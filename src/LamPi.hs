{-# LANGUAGE OverloadedStrings, DeriveDataTypeable, FlexibleContexts, 
PatternSynonyms, DeriveFunctor, DeriveGeneric, DeriveAnyClass, 
ScopedTypeVariables, TypeApplications, FlexibleInstances, IncoherentInstances, 
StandaloneDeriving, RecordWildCards, DefaultSignatures #-}


module LamPi where

-- import UnicodeEnc

import Data.Aeson(ToJSON, encode)
import GHC.Generics

import Data.Text(Text)
import qualified Data.Text as T
import Control.Monad(unless)
import Data.String.Conv(toS)

import Data.Data(Data, Typeable)
import Data.Has
import Data.Bifunctor

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative

import Data.Map(Map)
import qualified Data.Map as M

import Data.Set(Set)

import qualified Data.Set as S

import Debug.Trace(trace)
import Data.List(intercalate, unfoldr, sortBy)

import qualified SimpleSMT as SMT
import qualified Control.Exception as X
import System.Process(runInteractiveProcess, waitForProcess)
import Control.Concurrent(forkIO)
import System.IO (hFlush, hGetLine, hGetContents, hPutStrLn, stdout, hClose)
import Data.IORef(newIORef, atomicModifyIORef, modifyIORef', readIORef,
                  writeIORef)

import           Text.Earley.Mixfix(Associativity(..))

import Data.Bits(xor)

infixl 7 :@:

debugMode = False
-- smtLogMode = True

showImpl = False

debug = if debugMode then flip trace else (\a _ -> a)

data ExplImpl a = I a | E a deriving (Show, Eq, Ord, Data, Functor, Generic, ToJSON)

unExplImpl :: ExplImpl a -> a
unExplImpl (I a) = a
unExplImpl (E a) = a

instance PPrint a => PPrint (ExplImpl a) where
    pprint i (E a) = pprint i a
    pprint i (I a) = "{" ++ pprint i a ++ "}"

data Name = Global Text
          | Local Int
          | Quote Int
          | Meta Int
          | InferMeta
          | UserHole Int
          deriving (Show, Eq, Ord, Data, Generic, ToJSON)

instance PPrint Name where
    pprint _ (Global t) = toS t 
    pprint _ (Local i) = "L" ++ show i
    pprint _ (Quote i) = "Q" ++ show i
    pprint _ (Meta i) = "M" ++ show i
    pprint _ (UserHole i) = "?" ++ show i
    pprint _ InferMeta = "_"

data Infix = Infix {
    assoc :: Text.Earley.Mixfix.Associativity
  , precedence :: Int
  , symb :: Text
} deriving (Show, Eq)

data Term = StarT
          | PropT
          | NameT
          | MkName Text
          | SetT Term
          | MkSet Term [Term]
          | IntT
          | MkInt Int
          -- | RealT
          -- | MkReal Int
          | Π (Maybe Text) Term Term
          | IΠ Term Term
          | Term :⇒: Term
          | Bound Int
          | Free Name
          | Term :@: [ExplImpl Term]
          -- | Λ [ExplImpl Term] Term
          deriving (Show, Ord, Data, Generic, ToJSON)

instance Eq Term where
    StarT == StarT = True
    PropT == PropT = True
    NameT == NameT = True
    MkName x == MkName y = x == y
    SetT x == SetT y = x == y
    MkSet a x == MkSet b y = a == b && S.fromList x == S.fromList y
    IntT == IntT = True
    MkInt x == MkInt y = x == y
    Π _ a b == Π _ c d = a == c && b == d
    IΠ a b == IΠ c d = a == c && b == d
    a :⇒: b == c :⇒: d = a == c && b == d
    Bound x == Bound y = x == y
    Free x == Free y = x == y
    x :@: xs == y :@: ys = x == y && xs == ys
    _ == _ = False



class PPrint a where
    pprint :: Map Text Infix -> a -> String
    pprintE :: a -> String
    pprintE = pprint M.empty

instance PPrint Term where
    pprint _ StarT = "*"
    pprint _ PropT = "Prop"
    pprint _ NameT = "Name"
    pprint _ (MkName s) = "\'" ++ toS s
    pprint iFix (SetT a) = "Set " ++ pprint iFix a
    pprint iFix (MkSet a s) = "(⦃" ++ (intercalate "," (S.toList (S.fromList (map (pprint iFix) s)))) ++ "⦄ : " ++ "Set " ++ pprint iFix a ++ ")"
    pprint _ IntT = "Int"
    pprint _ (MkInt i) = toS $ show i
    pprint iFix (Π Nothing t t') = "Π " ++ pprint iFix t ++ " . " ++ pprint iFix t'
    pprint iFix (Π (Just n) t t') = "Π (" ++ toS n ++ ") " ++ pprint iFix t ++ " . " ++ pprint iFix t'
    pprint iFix (IΠ t t') = "Π {" ++ pprint iFix t ++ "} . " ++ pprint iFix t'
    pprint iFix (t :⇒: t') = "[" ++ pprint iFix t ++ "] -> " ++ pprint iFix t'
    pprint _ (Bound n) = "B" ++ show n
    pprint iFix (Free n) = pprint iFix n
    pprint iFix ((C n) :@: xs) = case (M.lookup n iFix, filterI xs) of
        (Just _, [x,y]) -> showApp iFix [x, E (C n), y]
        (Nothing, []) -> pprint iFix (C n)
        _ -> pprint iFix (C n) ++ " " ++ showApp iFix xs
            
    pprint iFix (x :@: xs) = pprint iFix x ++ " " ++ showApp iFix xs
    -- pprint iFix (Λ xs x) = printLamList xs ++ pprint iFix x
    --     where
    --         printLamList [] = ""
    --         printLamList (I x:xs) = "λ {" ++ pprint iFix x ++ "}. " ++ printLamList xs
    --         printLamList (E x:xs) = "λ " ++ pprint iFix x ++ ". " ++ printLamList xs
   

showApp _ [] = ""
showApp iFix [I x] = if showImpl then "{" ++ pprint iFix x ++ "}" else ""
showApp iFix [E x@(_ :@:xs)] = case filterI xs of
    [] -> pprint iFix x 
    _ -> "(" ++ pprint iFix x ++ ")"
showApp iFix [E x] = pprint iFix x
showApp iFix (I x:xs) = (if showImpl then "{" ++ pprint iFix x ++ "} " else "") ++ showApp iFix xs
showApp iFix ((E x@(_ :@:_)):xs) = "(" ++ pprint iFix x ++ ") " ++ showApp iFix xs
showApp iFix ((E x):xs) = pprint iFix x ++ " " ++ showApp iFix xs


filterI [] = []
filterI (I _:xs) = filterI xs
filterI (x:xs) = x : filterI xs

pattern C x = Free (Global x)
pattern M x = Free (Meta x)
pattern L x = Free (Local x)
pattern H x = Free (UserHole x)
pattern InferM = Free InferMeta

data Value = VStarT
           | VPropT
           | VNameT
           | VMkName Text
           | VSetT Value
           | VMkSet Value [Value]
           | VIntT
           | VMkInt Int
           | VΠ (Maybe Text) Value (Value -> Value)
           | VIΠ Value (Value -> Value)
           | VSArr Value Value
           -- | VLam (Value -> Value)
           | VNeutral Neutral

instance PPrint Value where
    pprint i = pprint i . quote0


data Neutral = NFree Name
             -- | NConst Text
             | NApp Neutral [ExplImpl Value]
             -- | NIApp Neutral Value
             -- | NHole Value

type Type = Value

data Γ = Γ { 
    types :: Map Name Type
  , constrs :: Map Name (Set Name)
  , defs :: Map Name (Term, Type)
  , props :: Map Text (SExpr Text Int)
  , unLiftMap :: Map Text Text
  , infixM :: Map Text Infix
  , langs :: Set Text
  , translations :: Map (Text, Name) ([ExplImpl Term], Maybe [ExplImpl Term], Text)
  , smtOpts :: [SMT.SExpr]
  , smtRaw :: [SMT.SExpr]
  , smtLogLevel :: Int
  , smtLogEnabled :: Bool
 }

emptyΓ = Γ M.empty M.empty M.empty M.empty M.empty M.empty (S.fromList ["JSON"]) M.empty [] [] 0 False

hash = T.foldl' (\h c -> 33*h `xor` fromEnum c) 5381

instance PPrint a => PPrint [a] where
    pprint i xs = "[" ++ (intercalate "," $ map (pprint i) xs) ++ "]"

instance Show Γ where
    show Γ{..} = "\n\n\n\nTypes:\n" ++ 
        (intercalate "\n" $ map (\(n,t) -> pprint infixM n ++ " -> " ++ pprint infixM t) $ M.toList types) ++
        "\n\n--------------------------------------------------------\n\nConstructors:\n" ++
        (intercalate "\n" $ map (\(n,e) -> pprint infixM n ++ " : " ++ (pprint infixM $ S.toList e)) $ M.toList constrs) ++
        "\n\n--------------------------------------------------------\n\nDefs:\n" ++
        (intercalate "\n" $ map (\(n,(e,t)) -> pprint infixM n ++ " : " ++ pprint infixM t ++ " = " ++ pprint infixM e) $ M.toList defs) ++
        "\n\n--------------------------------------------------------\n\nDefined Props:\n" ++
        (intercalate "\n" $ map (\(n,e) -> toS n ++ " -> " ++ show e) $ M.toList props) ++
        "\n\n--------------------------------------------------------\n\nUnlift Map:\n" ++
        (intercalate "\n" $ map (\(n,e) -> toS n ++ " -> " ++ toS e) $ M.toList unLiftMap) ++
        "\n\n--------------------------------------------------------\n\nDefined Languages:\n" ++
        (intercalate "," $ map show $ S.toList langs) ++
        "\n\n--------------------------------------------------------\n\nTranslations:\n" ++
        (intercalate "\n" $ map (\((l,n),e) -> pprint infixM n ++ "[" ++ toS l ++ "] : " ++ pprint infixM e) $ M.toList translations) ++
        "\n\n--------------------------------------------------------\n\nSMT opts:\n" ++
        (intercalate "," $ map (\e -> SMT.showsSExpr e "") $ smtOpts) ++
        "\n\n--------------------------------------------------------\n\nSMT raw:\n" ++
        (intercalate "\n" $ map (\e -> SMT.showsSExpr e "") $ smtRaw) ++
        "\n\n--------------------------------------------------------\n\nSMT Log level: " ++ show smtLogLevel ++ 
        "\n\n--------------------------------------------------------\n\nSMT Log enabled: " ++ show smtLogEnabled

type Env = [Value]


vfree :: Name -> Value
vfree n = VNeutral (NFree n)


vapp :: Value -> [ExplImpl Value] -> Value 
vapp (VΠ _ n f) [E v] = f v
vapp (VIΠ n f) [I v] = f v
vapp (VNeutral n) vs = VNeutral (NApp n vs)


eval :: Term -> Env -> Value
eval StarT d = VStarT
eval PropT d = VPropT
eval NameT d = VNameT
eval (MkName s) d = VMkName s
eval (SetT a) d = VSetT (eval a d)
eval (MkSet a s) d = VMkSet (eval a d) (map (flip eval d) s)
eval IntT d = VIntT
eval (MkInt i) d = VMkInt i
eval (Π n τ τ') d = VΠ n (eval τ d) (\x -> eval τ' (x:d))
eval (IΠ τ τ') d = VIΠ (eval τ d) (\x -> eval τ' (x:d))
eval (τ :⇒: τ') d = VSArr (eval τ d) (eval τ' d)
eval (Free x) d = vfree x
eval (Bound i) d = d !! i
eval (e :@: es) d = vapp (eval e d) (fmap (fmap (flip eval d)) es)

subst :: Int -> Term -> Term -> Term
subst i r (Π n τ τ') = Π n (subst i r τ) (subst (i+1) r τ')
subst i r (IΠ τ τ') = IΠ (subst i r τ) (subst (i+1) r τ')
subst i r (τ :⇒: τ') = (subst i r τ) :⇒: (subst i r τ')
subst i r (Bound j) = if i == j then r else Bound j 
subst i r (e :@: es) = subst i r e :@: (fmap (fmap (subst i r)) es)
subst i r (SetT a) = SetT (subst i r a)
subst i r (MkSet a s) = MkSet (subst i r a) (map (subst i r) s)
subst i r x = x


bind :: Int -> Int -> Term -> Term
bind i r (Π n τ τ') = Π n (bind i r τ) (bind (i+1) r τ')
bind i r (IΠ τ τ') = IΠ (bind i r τ) (bind (i+1) r τ')
bind i r (τ :⇒: τ') = (bind i r τ) :⇒: (bind i r τ')
bind i r e@(Free (Local j)) = if r == j then Bound i else e
bind i r (e :@: es) = bind i r e :@: (fmap (fmap (bind i r)) es)
bind i r (SetT a) = SetT (bind i r a)
bind i r (MkSet a s) = MkSet (bind i r a) (map (bind i r) s)
bind i r x = x


substMeta :: Int -> Term -> Term -> Term
substMeta i r (Π n τ τ') = Π n (substMeta i r τ) (substMeta i r τ')
substMeta i r (IΠ τ τ') = IΠ (substMeta i r τ) (substMeta i r τ')
substMeta i r (Bound j) = Bound j 
substMeta i r (Free (Meta j)) = if i == j then r else Free (Meta j)
substMeta i r (e :@: es) = substMeta i r e :@: (fmap (fmap (substMeta i r)) es)
substMeta i r (SetT a) = SetT (substMeta i r a)
substMeta i r (MkSet a s) = MkSet (substMeta i r a) (map (substMeta i r) s)
substMeta i r x = x



quote0 :: Value -> Term 
quote0 = quote 0

quote :: Int -> Value -> Term
quote i VStarT = StarT
quote i VPropT = PropT
quote i VNameT = NameT
quote i (VMkName s) = MkName s
quote i (VSetT a) = SetT (quote i a)
quote i (VMkSet a s) = MkSet (quote i a) (map (quote i) s)
quote i VIntT = IntT
quote i (VMkInt j) = MkInt j

quote i (VΠ n v f) = Π n (quote i v) (quote (i + 1) (f (vfree (Quote i))))
quote i (VIΠ v f) = IΠ (quote i v) (quote (i + 1) (f (vfree (Quote i))))
quote i (VSArr v v') = (quote i v) :⇒: (quote i v')
quote i (VNeutral n) = neutralQuote i n

neutralQuote :: Int -> Neutral -> Term
neutralQuote i (NFree x) = boundFree i x
neutralQuote i (NApp n vs) = neutralQuote i n :@: (fmap (fmap (quote i)) vs)
-- neutralQuote i (NIApp n v) = neutralQuote i n :|@|: quote i v
-- neutralQuote i (NConst x) = Const x
-- neutralQuote i (NHole v) = Hole $ quote i v

boundFree :: Int -> Name -> Term
boundFree i (Quote k) = Bound (i - k - 1) 
boundFree i x = Free x



newtype MetaCounter = MetaCounter { unMetaCounter :: Int } -- deriving (Eq, Show)


newtype BVCounter = BVCounter { unBVCounter :: Int }


newtype ConstrList = ConstrList { unConstrList :: [(Term,Term)] } deriving (Eq) --, Show)

instance (PPrint a, PPrint b) => PPrint (a,b) where
    pprint i (a,b) = "(" ++ pprint i a ++ "," ++ pprint i b ++ ")"

instance (PPrint a, PPrint b, PPrint c) => PPrint (a,b,c) where
    pprint i (a,b, c) = "(" ++ pprint i a ++ "," ++ pprint i b ++ "," ++ pprint i c ++ ")"

instance (PPrint a) => PPrint (Maybe a) where
    pprint i Nothing = "Nothing"
    pprint i (Just x) = "Just " ++ pprint i x

instance PPrint Text where
    pprint _ s = toS s


instance PPrint Int where
    pprint _ i = show i


instance (PPrint a, PPrint b) => PPrint (Map a b) where
    pprint i m = "(" ++ 
        (intercalate "," $ map (\(k,v) -> pprint i k ++ " -> " ++ pprint i v) $ M.toList m)
        ++ ")"



getFreshAndIncrementMeta :: (Has MetaCounter s, MonadState s m) => m Int
getFreshAndIncrementMeta = do
    s <- get
    modify (\s -> modifier (\(MetaCounter m) -> MetaCounter $ m+1) s)
    return $ unMetaCounter $ getter s


getFreshAndIncrementBV :: (Has BVCounter s, MonadState s m) => m Int
getFreshAndIncrementBV = do
    s <- get
    modify (\s -> modifier (\(BVCounter m) -> BVCounter $ m+1) s)
    return $ unBVCounter $ getter s

addToΓ :: (Has Γ s, MonadState s m) => Name -> Type -> m ()
addToΓ n τ = modify (\s -> modifier (\env@Γ{..} -> env{types = M.insert n τ types}) s)


getInfM :: (Has Γ s, MonadState s m) => m (Map Text Infix)
getInfM = do
    s <- get
    return $ infixM $ getter s


lookupInΓ :: (Has Γ s, MonadState s m , MonadError String m) => Name -> m Type
lookupInΓ n = do
    s <- get
    case M.lookup n (types $ getter s) of
        Just τ -> return τ
        Nothing -> throwError ("unknown identifier: " ++ pprint (infixM $ getter s) n)

getSExprMap :: (Has Γ s, MonadState s m) => m (Map Text (SExpr Text Int))
getSExprMap = do
    Γ{..} <- getter <$> get
    return props

getConstrList :: (Has ConstrList s, MonadState s m) => m ConstrList
getConstrList = getter <$> get


addToConstrList :: (Has ConstrList s, MonadState s m) => ConstrList -> m ()
addToConstrList (ConstrList xs) = modify (\s -> modifier (\(ConstrList ys) -> ConstrList $ xs ++ ys) s)


putConstrList :: (Has ConstrList s, MonadState s m) => ConstrList -> m ()
putConstrList xs = modify (\s -> modifier (\_ -> xs) s)

checkDoesNotContainMetas here t = unless (doesNotContainMetas t) $ throwError "" `debug` (pprintE t ++ " contains metas!" ++ here)




newtype SATConstrList = SATConstrList { unSATConstrList :: [Term] } deriving (Eq) --, Show)

addToSATConstrList :: (Has SATConstrList s, MonadState s m) => SATConstrList -> m ()
addToSATConstrList (SATConstrList xs) = modify (\s -> modifier (\(SATConstrList ys) -> SATConstrList $ xs ++ ys) s)

getSATConstrList :: (Has SATConstrList s, MonadState s m) => m SATConstrList
getSATConstrList = getter <$> get


elabType :: (Has BVCounter s, Has MetaCounter s, Has Γ s, Has ConstrList s, Has SATConstrList s, Has SATDefs s,
    MonadState s m , Has SMTSolver s, MonadIO m, MonadError String m) => 
    Term -> m (Term, Type)
elabType StarT = return (StarT, VStarT)
elabType PropT = return (PropT, VStarT)
elabType NameT = return (NameT, VStarT)
elabType (MkName s) = return (MkName s, VNameT)
elabType IntT = return (IntT, VStarT)
elabType (MkInt i) = return (MkInt i, VIntT)
elabType (SetT α) = do
    α' <- typeOf α VStarT
    return (SetT α', VStarT)
elabType (MkSet α []) = do
    α' <- typeOf α VStarT
    infM <- getInfM
    let α'' = eval α' [] `debug` ("{| |} : " ++ (pprint infM $ eval α' []))
    return $ (MkSet α' [], VSetT α'')
elabType (MkSet α xs) = do
    α' <- typeOf α VStarT
    let α'' = eval α' []
    xs' <- mapM (flip typeOf α'') xs
    infM <- getInfM
    pure ()  `debug` (pprint infM xs' ++ " : " ++ pprint infM α'')
    return (MkSet α' xs', VSetT α'')
elabType (Π n ρ ρ') = do
    τ <- typeOf ρ VStarT
    i <- getFreshAndIncrementBV
    addToΓ (Local i) $ eval ρ []
    
    smap <- getSExprMap
    infM <- getInfM
    (SATDefs setDefs) <- getHas
    -- we only define bound vars that have a SAT representation
    case toSExprMaybe smap setDefs ρ of
        Just sexpr -> do
            (SMTSolver proc) <- getHas `debug` ("found bound " ++ show i ++ " : " ++ pprint infM ρ)
            liftIO $ SMT.declare proc ("L" ++ show i) sexpr
            return ()
        Nothing ->
            return () `debug` ("Could not convert " ++ pprint infM  ρ ++ " to SExpr.")
            

    τ' <- typeOf (subst 0 (Free (Local i)) ρ') VStarT
    (ConstrList cs) <- getConstrList
    σ <- unifyConstraintsFull cs [] False M.empty -- `debug` ("\n\ncs1 (elabType Π): " ++ show cs)
    let τ'' = substMetas σ τ'
    checkDoesNotContainMetas "here??" τ''

    return (Π n τ (bind 0 i τ''), VStarT) -- `debug` ("i after: " ++ show i') -- 
        -- `debug` ("\n\ngot: " ++ show (Π ρ ρ') ++ " with fresh L" ++ show i ++ ", after subst: " ++ show (subst 0 (Free (Local i)) ρ') ++ " returning: " ++ show (Π τ (bind 0 i τ')))
elabType (IΠ ρ ρ') = do
    (Π _ τ τ', τ'') <- elabType (Π Nothing ρ ρ')
    return (IΠ τ τ', τ'')
elabType (x :⇒: y) = do
    x' <- typeOf x VPropT 
    y' <- typeOf y VStarT 
    (ConstrList cs) <- getConstrList
    σ <- unifyConstraintsFull cs [] False M.empty -- `debug` ("\n\nconstraints: " ++ show cs)
    let x'' = substMetas σ x'
    let y'' = substMetas σ y'
    infM <- getInfM
    checkDoesNotContainMetas "here1" y'' `debug` ("\n\n:⇒: " ++ pprint infM x'')
    return (x'' :⇒: y'', VStarT)
elabType (H n) = do
    -- mi <- getFreshAndIncrementMeta
    -- let mvar = Free (Meta mi)
    -- addToΓ (Meta mi) τ
    return (H n, eval (H n) [])
elabType InferM = do
    mi <- getFreshAndIncrementMeta
    let mvar = Free (Meta mi)

    mj <- getFreshAndIncrementMeta
    let mvarTy = eval (Free (Meta mj)) [] `debug` ("InferM -> added " ++ show mi ++ "," ++ show mj)
    addToΓ (Meta mi) mvarTy
    return (mvar, mvarTy)
elabType (Free n) = do
    τ <- lookupInΓ n
    return (Free n, τ)
elabType (e :@: es) = do  -- D :@: xs
    (e',τ) <- elabType e       -- D : σ
    infM <- getInfM
    (es',τ') <- elabTypeApp τ es `debug` ("App head: " ++ pprint infM e' ++ " : " ++ pprint infM τ)
    return (e' :@: es', τ')
    -- typeOfApp i g σ es
-- elabType (Λ [] body) = do  -- D :@: xs
--     (body' , τ) <- elabType body
--     return (Λ [] body', τ)
-- elabType (Λ (I ρ:ts) body) = do  -- D :@: xs
--     infM <- getInfM
--     i <- getFreshAndIncrementBV `debug` ("\n\n\n\n\n\ngetting here\n\n\n\n\n\n")
--     addToΓ (Local i) $ eval ρ [] 
--     let tsSubst = map (\(n,t) -> fmap (subst n (Free (Local i))) t) (zip [0..length ts] ts)  
--         bodySubst = subst (length ts) (Free (Local i)) body

--     (bodyElab , τ) <- elabType (Λ tsSubst bodySubst) `debug` ("ts': " ++ pprint infM tsSubst ++ ", body' : " ++ pprint infM bodySubst)
--     return (Λ ts (bind 0 i bodyElab), VIΠ (eval ρ []) (\t -> flip eval [] $ subst 0 (quote0 t) $ bind 0 i $ quote0 τ))
-- elabType (Λ (E ρ:ts) body) = do  -- D :@: xs
--     infM <- getInfM
--     i <- getFreshAndIncrementBV
--     addToΓ (Local i) $ eval ρ []
--     let tsSubst = map (\(n,t) -> fmap (subst n (Free (Local i))) t) (zip [0..length ts] ts)  
--         bodySubst = subst (length ts) (Free (Local i)) body

--     (bodyElab , τ) <- elabType (Λ tsSubst bodySubst) `debug` ("ts': " ++ pprint infM tsSubst ++ ", body' : " ++ pprint infM bodySubst)
--     return (Λ ts (bind 0 i bodyElab), VΠ Nothing (eval ρ []) (\t -> flip eval [] $ subst 0 (quote0 t) $ bind 0 i $ quote0 τ))
elabType e = do
    infM <- getInfM
    error $ "can't handle " ++ pprint infM e


elabTypeApp :: (Has BVCounter s, Has MetaCounter s, Has Γ s, Has ConstrList s, Has SATConstrList s, Has SATDefs s,
    MonadState s m , Has SMTSolver s, MonadIO m, MonadError String m) => 
    Type -> [ExplImpl Term] -> m ([ExplImpl Term], Type)
elabTypeApp ty [] = case ty of
    (VIΠ τ τ') -> do
        mi <- getFreshAndIncrementMeta
        let mvar = Free (Meta mi)
        addToΓ (Meta mi) τ
        (xs',τ'') <- elabTypeApp (τ' (eval mvar [])) []
        return $ (I mvar:xs',τ'')
    (VΠ _ _ _) -> do
        infM <- getInfM
        throwError $ "illegal application at " <> (toS $ pprint infM ty)
    (VSArr cnstr τ') -> do
        cnstr' <- typeOf (quote0 cnstr) VPropT
        (ConstrList cs) <- getConstrList
        infM <- getInfM
        pure () `debug` ("\n\nConstrList is: "++ pprint infM cs)
        -- σ <- unifyConstraints cs [] False M.empty
        let cnstr'' = substMetas (mkMap cs) cnstr'
        addToSATConstrList $ SATConstrList [cnstr''] -- `debug` ("\nmap is: " ++ show σ)
        infM <- getInfM
        elabTypeApp τ' [] `debug` ("\n\nconstraint is: "++ pprint infM cnstr'')
    _ -> return ([], ty)
elabTypeApp ty (x:xs) = case (x,ty) of
    (E x', VΠ _ τ τ') -> do
        x'' <- typeOf x' τ
        (ConstrList cs) <- getConstrList
        (xs',τ'') <- elabTypeApp (τ' (eval x'' [])) (fmap (fmap $ substMetas $ mkMap cs) xs) -- `debug` ("sbustmetas: " ++ show cs)
        return $ (E x'':xs',τ'')
    (I x', VIΠ τ τ') -> do
        x'' <- typeOf x' τ
        (ConstrList cs) <- getConstrList
        (xs',τ'') <- elabTypeApp (τ' (eval x'' [])) (fmap (fmap $ substMetas $ mkMap cs) xs) -- `debug` ("sbustmetas: " ++ show cs)
        return $ (I x'':xs',τ'')
    (E _, VIΠ τ τ') -> do
        mi <- getFreshAndIncrementMeta
        let mvar = Free (Meta mi)
        addToΓ (Meta mi) τ
        (xs',τ'') <- elabTypeApp (τ' (eval mvar [])) (x:xs) -- `debug` ("adding meta: " ++ show (VIΠ τ τ') ++ " -> " ++ show (τ' (eval (Free (Global "aaa")) [])))
        return $ (I mvar:xs',τ'')
    (_, VSArr cnstr τ') -> do
        cnstr' <- typeOf (quote0 cnstr) VPropT
        (ConstrList cs) <- getConstrList
        infM <- getInfM
        pure () `debug` ("\n\nConstrList is: "++ pprint infM cs)
        -- σ <- unifyConstraints cs [] False M.empty
        let cnstr'' = substMetas (mkMap cs) cnstr' -- substMetas σ cnstr'
        addToSATConstrList $ SATConstrList [cnstr''] -- `debug` ("\nmap is: " ++ show σ)
        elabTypeApp τ' (x:xs) `debug` ("\n\nconstraint is: "++ pprint infM cnstr'')
    _ -> do
        infM <- getInfM
        throwError $ "illegal application at " <> (toS $ pprint infM x) <> " : " <> (toS $ pprint infM ty)



typeOf :: (Has BVCounter s, Has MetaCounter s, Has Γ s, Has ConstrList s, Has SATConstrList s, Has SATDefs s,
    MonadState s m , Has SMTSolver s, MonadIO m, MonadError String m) => 
    Term -> Type -> m Term
typeOf e τ = do
    infM <- getInfM
    cs <- getConstrList `debug` ("calling tyOf on " ++ pprint infM e ++ " : " ++ pprint infM τ)
    (e',τ') <- elabType e
    pure () `debug` ("elaborated " ++ pprint infM e ++ " : " ++ pprint infM τ ++ " to " ++ pprint infM e' ++ " : " ++ pprint infM τ')
    case τ' of -- `debug` (show e' ++ " : orig= " ++ show τ ++ ", elab= " ++ show τ') --of
        -- in case of C "Cons" :@: [E $ C "Z", E $ C "Nil"]
        -- we want to make C "Nil" into a C "Nil" :@: [] to add hidden params
        VIΠ _ _ -> do
            putConstrList cs
            (e'',τ'') <- elabType (e :@: [])
            addToConstrList $ ConstrList $ unifyType (quote0 τ) (quote0 τ'')
            return e'' -- `debug` ("\n\nfound : " ++ show cs')
        _ -> do
            addToConstrList $ ConstrList $ unifyType (quote0 τ) (quote0 τ')
            infM <- getInfM
            return e' `debug` ("\n\nadding -> " ++ pprint infM e ++ " .... " ++ (pprint infM $ unifyType (quote0 τ) (quote0 τ')))

unifyType :: Term -> Term -> [(Term,Term)]
unifyType τ τ' | τ == τ' = []
unifyType (Free (Meta i)) τ' = [(Free (Meta i),τ')]
unifyType τ (Free (Meta i)) = [(Free (Meta i),τ)]
unifyType (x :@: xs) (y :@: ys) 
    | length xs == length ys = unifyType x y ++ (concat $ map unifyTypeApp $ zip xs ys)
    | otherwise = error $ "length of xs and ys is different: " ++ pprintE (xs,ys)
    where

        unifyTypeApp :: (ExplImpl Term, ExplImpl Term) -> [(Term,Term)]
        unifyTypeApp (E x,E y) = unifyType x y
        unifyTypeApp (I x,I y) = unifyType x y
        unifyTypeApp _ = error "trying to unify E with I"
unifyType (SetT x) (SetT y) = unifyType x y
unifyType (MkSet a _) (MkSet b _) = unifyType a b

unifyType (H n) x = [(H n, x)]
unifyType x (H n) = [(H n, x)]
unifyType InferM InferM = error $ "\n\nfailed on : " ++ pprintE InferM ++ " and " ++ pprintE InferM ++ "\n\n"

unifyType x InferM = [] `debug` ("unifying " ++ pprintE x ++ " with InferM")
unifyType InferM x = [] `debug` ("unifying " ++ pprintE x ++ " with InferM")
unifyType τ τ' = error $ "\n\nfailed to unify on : " ++ pprintE τ ++ " and " ++ pprintE τ' ++ "\n\n"


data UnificationSettings = Full | Partial

unifyConstraints :: (MonadReader UnificationSettings m, MonadError String m) => [(Term,Term)] -> [(Term,Term)] -> Bool -> Map Int Term -> m (Map Int Term)
unifyConstraints []                                  []  _     m = return m
unifyConstraints []                                  acc False m = do
    s <- ask
    case s of
        Full -> throwError $ "cannot unify rest (acc): " ++ pprintE acc ++ "; m contains: " ++ pprintE m
        Partial -> return m `debug` ("cannot unify rest (acc): " ++ pprintE acc ++ "; m contains: " ++ pprintE m)
unifyConstraints []                                  acc True  m = 
    unifyConstraints (map (\(x,y) -> (substMetas m x, substMetas m y)) acc) [] False m
unifyConstraints ((M x, M y):xs) acc flag m = case (M.lookup x m, M.lookup y m) of 
    (Just (L _), Just _) -> unifyConstraints xs acc flag m
    (Just _, Just (L _)) -> unifyConstraints xs acc flag m
    (Just tx, Just ty) -> do
        unless (tx == ty) $ throwError $ "cannot unify (2): " ++ pprintE [tx,ty]
        unifyConstraints xs acc flag m
    (Just tx, Nothing) -> unifyConstraints xs acc flag $ M.insert y tx m
    (Nothing, Just ty) -> unifyConstraints xs acc flag $ M.insert x ty m
    (Nothing, Nothing) -> unifyConstraints xs ((M x, M y):acc) flag m
unifyConstraints ((M x, y):xs)                       acc flag  m 
    | doesNotContainMetas y = unifyConstraints xs acc True $ M.insert x y m `debug` ("unify : " ++ pprintE (M x, y))
    | otherwise = case M.lookup x m of
        Just tx -> unifyConstraints xs ((tx, y):acc) flag m `debug` ("unify oterwise : " ++ pprintE (M x, y))
        Nothing -> unifyConstraints xs ((M x, y):acc) flag m 
unifyConstraints ((x, M y):xs)                       acc flag  m = unifyConstraints ((M y,x):xs) acc flag m
unifyConstraints ((StarT, StarT):xs)                   acc flag  m = unifyConstraints xs acc flag m
unifyConstraints ((NameT, NameT):xs)                   acc flag  m = unifyConstraints xs acc flag m
unifyConstraints ((MkName x, MkName y):xs)           acc flag  m | x == y = unifyConstraints xs acc flag m
unifyConstraints ((SetT x, SetT y):xs)                 acc flag  m = unifyConstraints ((x,y):xs) acc flag m
unifyConstraints ((x@(MkSet _ _), y@(MkSet _ _)):xs) acc flag  m | x == y = unifyConstraints xs acc flag m

unifyConstraints ((Π _ σ σ', Π _ τ τ'):xs)           acc flag  m = throwError "not sure how to unify yet"
unifyConstraints ((IΠ σ σ', IΠ τ τ'):xs)             acc flag  m = throwError "not sure how to unify yet"
unifyConstraints ((Free x, Free y):xs)               acc flag  m | x == y = unifyConstraints xs acc flag m
unifyConstraints ((Bound x, Bound y):xs)             acc flag  m | x == y = unifyConstraints xs acc flag m
unifyConstraints ((e :@: es, e' :@: es'):xs)         acc flag  m = do
    eses' <- mapM matchApp $ zip es es'
    unifyConstraints ((e,e'):eses'++xs) acc flag m
    where
        matchApp :: MonadError String m => (ExplImpl Term , ExplImpl Term) -> m (Term, Term)
        matchApp (E t , E t') = return (t,t')
        matchApp (I t , I t') = return (t,t')
        matchApp (t , t') = throwError $ "cannot unify (in matchApp): " ++ pprintE [t,t']

unifyConstraints ((H _, _):xs)                       acc flag  m = unifyConstraints xs acc flag m 
    -- `debug` ("\n================================\n" ++ show (H x) ++ " : " ++ show y ++ "\n================================")
unifyConstraints ((_, H _):xs)                       acc flag  m = unifyConstraints xs acc flag m
    -- `debug` ("\n================================\n" ++ show (H y) ++ " : " ++ show x ++ "\n================================")
unifyConstraints ((L _, _):xs)                       acc flag  m = unifyConstraints xs acc flag m 
unifyConstraints ((_, L _):xs)                       acc flag  m = unifyConstraints xs acc flag m 
unifyConstraints (x:_)                               _   _     _ = throwError $ "bad constraint " ++ pprintE x


unifyConstraintsFull ts1 ts2 f m = flip runReaderT Full $ unifyConstraints ts1 ts2 f m
unifyConstraintsPart ts1 ts2 f m = flip runReaderT Partial $ unifyConstraints ts1 ts2 f m

doesNotContainMetas :: Term -> Bool
-- doesNotContainMetas InferM = False
doesNotContainMetas (M _) = False
doesNotContainMetas (SetT a) = doesNotContainMetas a
doesNotContainMetas (MkSet a xs) = doesNotContainMetas a && foldr (\t b -> doesNotContainMetas t && b) True xs
doesNotContainMetas (Π _ τ τ') = doesNotContainMetas τ && doesNotContainMetas τ'
doesNotContainMetas (IΠ τ τ') = doesNotContainMetas (Π Nothing τ τ')
doesNotContainMetas (e :@: es) = doesNotContainMetas e && foldr doesNotContainMetasApp True es
    where
        doesNotContainMetasApp _ False = False
        doesNotContainMetasApp (E x) b = doesNotContainMetas x && b
        doesNotContainMetasApp (I x) b = doesNotContainMetas x && b
doesNotContainMetas (τ :⇒: τ') = doesNotContainMetas τ && doesNotContainMetas τ'
doesNotContainMetas _ = True


substMetas :: Map Int Term -> Term -> Term
substMetas m t = foldr (\(i,v) t' -> substMeta i v t') t (M.toList m)



mkMap :: [(Term,Term)] -> Map Int Term
mkMap [] = M.empty
mkMap ((M x, M y):xs) = let xs' = mkMap xs in
    case (M.lookup x xs', M.lookup y xs') of
        (Just xm, Nothing) -> M.insert y xm xs'
        (Nothing, Just ym) -> M.insert x ym xs'
        (Just xm, Just ym) -> 
            if xm == ym then xs' 
            else M.insert x ym $ M.insert y xm xs'
            -- error $ "this shouldn't happen: " ++ show (x, xm, y, ym)
        (Nothing, Nothing) -> M.insert x (M y) xs'
mkMap ((M x, y):xs) = M.insert x y $ mkMap xs
mkMap ((x, M y):xs) = mkMap $ (M y, x):xs
mkMap (_:xs) = mkMap xs


newtype SATDefs = SATDefs { unSATDefs :: Set Int } deriving (Eq, Show)

newtype SMTSolver = SMTSolver { unSMTSolver :: SMT.Solver }

getHas :: (Has a s, MonadState s m) => m a
getHas = getter <$> get


addToSATDefs :: (Has SATDefs s, MonadState s m) => Int -> m ()
addToSATDefs i = modify (\s -> modifier (\(SATDefs ys) -> SATDefs $ S.insert i ys) s)



-- using this to only define bound vars that have a SAT representation
toSExprMaybe :: Map Text (SExpr Text Int) -> Set Int -> Term -> Maybe SMT.SExpr
toSExprMaybe _ _ PropT = pure $ SMT.tBool
toSExprMaybe _ _ NameT = pure $ SMT.const "String"
toSExprMaybe _ _ (MkName s) = pure $ SMT.const $ "\"" ++ toS s ++ "\""
toSExprMaybe smap defMetas (SetT a) = (\x -> SMT.fun "Set" [x]) <$> toSExprMaybe smap defMetas a
toSExprMaybe smap defMetas (MkSet a []) = 
    (\x -> SMT.fun "as" [SMT.const "emptyset", x]) <$> toSExprMaybe smap defMetas (SetT a)
toSExprMaybe smap defMetas (MkSet _ [x]) = do
    x' <- toSExprMaybe smap defMetas x
    return $ SMT.fun "singleton" [x']
toSExprMaybe smap defMetas (MkSet _ (x:xs)) = do
    x' <- toSExprMaybe smap defMetas x
    xs' <- mapM (toSExprMaybe smap defMetas) xs
    return $ SMT.fun "insert" $ xs' ++ [SMT.fun "singleton" [x']]
toSExprMaybe _ defMetas (M x) = 
    if x `S.member` defMetas 
    then pure $ SMT.const $ "M" ++ show x
    else Nothing
toSExprMaybe smap defMetas t@(C op :@: args) = 
    case M.lookup op smap of
        Just sexp -> substSExprMaybe smap defMetas t (map unExplImpl args) sexp
        Nothing -> Nothing
-- toSExprMaybe _ (L i) = return $ SMT.const $ "L"++ show i
toSExprMaybe smap defMetas t@(C op) = 
    case M.lookup op smap of
        Just sexp -> substSExprMaybe smap defMetas t [] sexp
        Nothing -> Nothing
toSExprMaybe _ _ _ = Nothing


substSExprMaybe :: Map Text (SExpr Text Int) -> Set Int -> Term -> [Term] -> SExpr Text Int -> Maybe SMT.SExpr
substSExprMaybe _ _ _ _ (NAtom x) = return $ SMT.Atom (toS x)
substSExprMaybe smap defMetas trm ts (VAtom i)
    | 0 <= i && i < length ts = toSExprMaybe smap defMetas (ts !! i)
    | otherwise = Nothing
substSExprMaybe smap defMetas trm ts (List xs) = SMT.List <$> 
    mapM (substSExprMaybe smap defMetas trm ts) xs


fromSExprMaybe :: Map Text Text -> SMT.SExpr -> Type -> Maybe Term
fromSExprMaybe _ (SMT.Atom xs) VNameT = return $ MkName $ toS $ filter (/= '"') xs
fromSExprMaybe _ (SMT.Atom i) VIntT = return $ MkInt $ read i
fromSExprMaybe _ (SMT.List [SMT.Atom "as",SMT.Atom "emptyset",_]) (VSetT a) = return $ MkSet (quote0 a) []
fromSExprMaybe unLiftMap (SMT.List [SMT.Atom "singleton",n])          (VSetT a) = (\e -> MkSet (quote0 a) [e]) <$> fromSExprMaybe unLiftMap n a
fromSExprMaybe unLiftMap (SMT.List [SMT.Atom "union", xs, ys])        (VSetT a) = do
    (MkSet a' xs') <- fromSExprMaybe unLiftMap xs (VSetT a)
    (MkSet _ ys') <- fromSExprMaybe unLiftMap ys (VSetT a)
    return $ MkSet a' $ xs' ++ ys'
fromSExprMaybe unLiftMap trm τ = unlift unLiftMap trm
    where
        unlift :: Map Text Text -> SMT.SExpr -> Maybe Term
        unlift unLiftMap (SMT.List [SMT.Atom "as",trm,_]) = unlift unLiftMap trm
        unlift unLiftMap (SMT.Atom n) = C <$> M.lookup (toS n) unLiftMap
        unlift unLiftMap (SMT.List (x:xs)) = do
            x' <- unlift unLiftMap x
            xs' <- mapM (unlift unLiftMap) xs
            return $ x' :@: map E xs'
        unlift _ t = error $ "unsupported operation " ++ SMT.showsSExpr t ""

defineMetas :: (MonadIO m, Has SMTSolver s, Has Γ s, Has SATDefs s, MonadState s m, MonadError String m) => 
    Term -> m ()
defineMetas (M n) = do
    (SATDefs defined) <- getHas
    if not (n `S.member` defined) then do
        τ <- lookupInΓ (Meta n)
        smap <- getSExprMap
        infM <- getInfM
        (SMTSolver proc) <- getHas `debug` ("found meta " ++ show n ++ " : " ++ pprint infM τ)

        -- we only define bound vars that have a SAT representation
        (SATDefs satDefs) <- getHas
        case toSExprMaybe smap (S.insert n satDefs) $ quote0 τ of
            Just sexpr -> do
                (SMTSolver proc) <- getHas `debug` ("found meta " ++ show n ++ " : " ++ pprint infM τ)
                liftIO $ SMT.declare proc ("M" ++ show n) sexpr
                addToSATDefs n
            Nothing ->
                return () `debug` ("Could not convert " ++ show (quote0 τ) ++ " to SExpr.")
                
    else pure ()
defineMetas (e :@: es) = mapM_ (\x -> case x of
    E y -> defineMetas y
    I y -> defineMetas y) es
defineMetas _ = return ()



checkSMT :: (Has Γ s, Has ConstrList s, Has SATConstrList s, Has SATDefs s, Has BVCounter s, Has MetaCounter s, 
    MonadState s m , Has SMTSolver s, MonadIO m, MonadError String m) => Term -> m ()
checkSMT trm = do
    (ConstrList cs) <- getConstrList
    -- get collected sat constraints and replace all equal metas, collected in ConstrList
    (SATConstrList satcs) <- getSATConstrList
    let satcs' = map (substMetas $ mkMap cs) satcs

    -- translate to sat, first defining all meta variables
    mapM_ defineMetas satcs'
    infM <- getInfM
    (SMTSolver proc) <- getHas `debug` ("produced following sat goals: " ++ pprint infM satcs')
    smap <- getSExprMap
    -- mapM_ (\s -> liftIO $ SMT.assert proc $ toSExpr smap s) satcs'
    mapM_ (\(s,i) -> do
        (SATDefs setDefs) <- getHas
        -- let sexpr = eliminateBrackets $ 
        case toSExprMaybe smap setDefs s of
            Just sexpr -> 
                liftIO $ SMT.assert proc $ SMT.named ('_':show i) sexpr
            Nothing -> 
                return () `debug` (pprint infM s ++ " could not be added as it contains undefined metas.")
        ) (zip satcs' [0..])
        

    -- check sat
    (SMTSolver proc) <- getHas
    r <- liftIO $ SMT.check proc
    case r of
        SMT.Sat -> do
            (SATDefs defined) <- getHas
            forM_ (S.toList defined) (\d -> do
                (SMT.Other v) <- liftIO $ SMT.getExpr proc (SMT.const $ "M" ++ pprint infM d)
                τ <- lookupInΓ (Meta d) `debug` ("\n\nSMT returned: " ++ show v)

                Γ{..} <- getter <$> get
                case fromSExprMaybe unLiftMap v τ of
                    Just vt -> do
                        -- Because vt was translated back from SMT, it's not fully typed,
                        -- namely it does not contain any of the implicit arguments.
                        -- Calling typeOf will elaborate vt and add these, so that we get
                        -- a well formed/typed term.
                        vt' <- typeOf vt τ
                        addToConstrList $ ConstrList [(M d,vt')] `debug` ("\n\nadding const: " ++ pprint infM (M d,vt))
                    Nothing -> pure () `debug` ("\n\ncould not translate: " ++ SMT.showsSExpr v "" ++ " back."))
        SMT.Unsat -> do 
            (SMT.List res) <- liftIO $ SMT.command proc (SMT.List [ SMT.Atom "get-unsat-core" ])
            let unsat_core = map (\(SMT.Atom (_:num)) -> (read num :: Int)) res
            σ <- unifyConstraintsPart cs [] False M.empty -- `debug` ("\n\nelabType0 constraints: " ++ show cs' ++ "\nmkMap cs = " ++ show (mkMap cs) ++ "\n sat constraints: " ++ show satcs' )
            
            throwError $ "The following constraints are unsatisfiable:\n" ++
                (intercalate "\n" $ map (\i -> "- " ++ (pprint infM $ substMetas σ $ satcs' !! i)) unsat_core) ++
                "\nin the term:\n" ++ pprint infM trm

        _ -> throwError $ "unknown result"




getHoles [] = []
getHoles ((H n, x):xs) = (n,x) : getHoles xs
getHoles ((x, H n):xs) = (n,x) : getHoles xs
getHoles (_:xs) = getHoles xs


-- | Start a new solver process.
newSolver :: String       {- ^ Executable -}            ->
             [String]     {- ^ Arguments -}             ->
             Maybe SMT.Logger {- ^ SMTOptional logging here -} ->
             IO SMT.Solver
newSolver exe opts mbLog =
  do (hIn, hOut, hErr, h) <- runInteractiveProcess exe opts Nothing Nothing

     let info lvl a = case mbLog of
                    Nothing -> return ()
                    Just log  -> case lvl of
                        Just i -> SMT.logMessageAt log i a
                        Nothing -> SMT.logMessage log a

     _ <- forkIO $ forever (do errs <- hGetLine hErr
                               info (Just 1) ("[stderr] " ++ errs))
                    `X.catch` \X.SomeException {} -> return ()

     getResponse <-
       do txt <- hGetContents hOut                  -- Read *all* output
          ref <- newIORef (unfoldr SMT.readSExpr txt)  -- Parse, and store result
          return $ atomicModifyIORef ref $ \xs ->
                      case xs of
                        []     -> (xs, Nothing)
                        y : ys -> (ys, Just y)

     let cmd c = do let txt = SMT.showsSExpr c ""
                    info Nothing ("[send->] " ++ txt)
                    hPutStrLn hIn txt
                    hFlush hIn

         command c =
           do cmd c
              mb <- getResponse
              case mb of
                Just res -> do case res of
                                 SMT.List (SMT.Atom "error":_) -> 
                                    info (Just 1) ("[<-recv] " ++ SMT.showsSExpr res "")
                                 _ -> 
                                    info Nothing ("[<-recv] " ++ SMT.showsSExpr res "")
                               return res
                Nothing  -> fail "Missing response from solver"

         stop =
           do cmd (SMT.List [SMT.Atom "exit"])
              ec <- waitForProcess h
              X.catch (do hClose hIn
                          hClose hOut
                          hClose hErr)
                      (\ex -> info (Just 1) (show (ex::X.IOException)))
              return ec

         solver = SMT.Solver { .. }

     SMT.setOption solver ":print-success" "true"
     SMT.setOption solver ":produce-models" "true"

     return solver

smtSMTOptIsDefined :: (Has Γ s, MonadReader s m) => Text -> m Bool
smtSMTOptIsDefined opt = do
    Γ{..} <- getter <$> ask

    return $ findSMTOpt opt smtOpts

    where
        findSMTOpt :: Text -> [SMT.SExpr] -> Bool
        findSMTOpt _ [] = False
        findSMTOpt opt (SMT.List (SMT.Atom "set-option":SMT.Atom opt':_):xs)
            | opt == toS opt' = True
            | otherwise = findSMTOpt opt xs
        findSMTOpt "set-logic" (SMT.List (SMT.Atom "set-logic":_):xs) = True
        findSMTOpt opt (_:xs) = findSMTOpt opt xs



initSMT :: (MonadIO m , Has Γ s, MonadReader s m, MonadError String m) => m SMT.Solver
initSMT = do
    Γ{..} <- getter <$> ask
    log <- liftIO $ SMT.newLogger smtLogLevel
    smt <- liftIO $ newSolver "cvc4" ["--fmf-fun", "--incremental", "--lang" , "smt2.6"] (if smtLogEnabled then Just log else Nothing)
    setLogic <- smtSMTOptIsDefined "set-logic"
    unless setLogic $ 
        liftIO $ SMT.setLogic smt "ALL" -- QF_UFSLIAFS" -- "QF_UFLIAFS"
    
    produceUnsatCores <- smtSMTOptIsDefined ":produce-unsat-cores"
    unless produceUnsatCores $ 
        liftIO $ SMT.setOption smt ":produce-unsat-cores" "true"
    
    forM_ smtOpts (\x -> liftIO $ SMT.ackCommand smt x)

    forM_ smtRaw (\x -> liftIO $ SMT.ackCommand smt $ x)
    return smt


elabType0 ::  (Has BVCounter s, Has MetaCounter s, Has Γ s, Has ConstrList s, Has SATConstrList s, Has SATDefs s,
    MonadState s m , Has SMTSolver s, MonadIO m, MonadError String m) => Bool -> 
    Term -> m (Term, Type)
elabType0 canContainMetas t = do 
    (trm,typ) <- elabType t

    checkSMT trm

    (ConstrList cs') <- getConstrList -- `debug` "stopped SMT"
    σ <- unifyConstraintsFull cs' [] False M.empty -- `debug` ("\n\nelabType0 constraints: " ++ show cs' ++ "\nmkMap cs = " ++ show (mkMap cs) ++ "\n sat constraints: " ++ show satcs' )
    let trm' = substMetas σ trm
        typ' = substMetas σ $ quote0 typ
        holes = map (\(n,x) -> (n,substMetas σ x)) $ getHoles cs'
    infM <- getInfM
    liftIO $ mapM_ (\(n,x) -> putStrLn $ ("\n================================\n" ++ pprint infM (H n) ++ " : " ++ pprint infM x ++ "\n================================")) holes
    unless (canContainMetas || doesNotContainMetas trm')$ throwError $ pprint infM trm' ++ " contains metas! (elabType0)"
    unless (doesNotContainMetas typ')$ throwError $ pprint infM typ' ++ " contains metas! (elabType0)"
    return $ (trm', eval typ' []) `debug` ("cs now contains: " ++ pprint infM cs')


runElabType0 :: (MonadIO m, MonadError String m) => Bool -> Γ -> Term -> m (Term, Type)
runElabType0 canContainMetas g t = do
    smt <- runReaderT initSMT g

    res <- (flip evalStateT (BVCounter 0,MetaCounter 0,g,ConstrList [],SATConstrList [], SATDefs S.empty, SMTSolver smt)) $ elabType0 canContainMetas t
    liftIO $ SMT.stop smt
    return res



typeOf0 :: (Has BVCounter s, Has MetaCounter s, Has Γ s, Has ConstrList s, Has SATConstrList s, Has SATDefs s,
    MonadState s m , Has SMTSolver s, MonadError String m, MonadIO m) =>
    Term -> Type -> m Term
typeOf0 t τ = do
    trm <- typeOf t τ
    (ConstrList cs) <- getConstrList

    checkSMT trm
    -- get model and add to cs

    -- liftIO $ SMT.stop proc
    (ConstrList cs') <- getConstrList -- `debug` "stopped SMT in typeOf0"
    σ <- unifyConstraintsFull cs' [] False M.empty --`debug` ("\n\nelabType0 constraints: " ++ show cs' ++ "\nmkMap cs = " ++ show (mkMap cs) ++ "\n sat constraints: " ++ show satcs' )
    let trm' = substMetas σ trm
        holes = map (\(n,x) -> (n,substMetas σ x)) $ getHoles cs'
    infM <- getInfM


    unless (doesNotContainMetas trm')$ do
        liftIO $ mapM_ (\(n,x) -> putStrLn $ ("\n================================\n" ++ pprint infM (H n) ++ " : " ++ pprint infM x ++ "\n================================")) holes
        throwError $ pprint infM trm' ++ " contains metas! (typeOf0)"
    return $ trm'



evalTypeOf0 :: (MonadError String m, MonadIO m) => Γ -> Term -> Type -> m Term
evalTypeOf0 g t τ = do
    smt <- runReaderT initSMT g

    res <- flip evalStateT (BVCounter 0,MetaCounter 0,g,ConstrList [],SATConstrList [], SATDefs S.empty, SMTSolver smt) $ typeOf0 t τ

    liftIO $ SMT.stop smt
    return res


data SExpr n v = NAtom n
             | VAtom v
             | List [SExpr n v]
    deriving (Eq, Data)

instance {-# OVERLAPPING #-} (Show v) => Show (SExpr Text v) where
    show (NAtom n) = "'" ++ toS n
    show (VAtom i) =  show i
    show (List xs) = "(" ++ (intercalate " " $ map show xs) ++ ")" 

instance (Show n, Show v) => Show (SExpr n v) where
    show (NAtom n) = show n
    show (VAtom i) =  show i
    show (List xs) = "(" ++ (intercalate " " $ map show xs) ++ ")" 

instance Bifunctor SExpr where
    bimap f g (NAtom n) = NAtom $ f n
    bimap f g (VAtom v) = VAtom $ g v
    bimap f g (List xs) = List $ map (bimap f g) xs

toSMTSExp :: (a -> String) -> (b -> String) -> SExpr a b -> SMT.SExpr
toSMTSExp f _ (NAtom x) = SMT.Atom $ f x
toSMTSExp _ g (VAtom x) = SMT.Atom $ g x
toSMTSExp f g (List xs) = SMT.List $ map (toSMTSExp f g) xs


replace :: Eq a => a -> a -> SExpr a b -> SExpr a b
replace a b (NAtom c) | a == c = NAtom b
                      | otherwise = NAtom c
replace _ _ x@(VAtom _) = x
replace a b (List xs) = List $ map (replace a b) xs

deriving instance Data SMT.SExpr

data SMTOpt name = 
    SMTCmd (LamPi.SExpr name name)
  | SMTLogLevel Int
  | SMTLogEnabled Bool
    deriving (Show, Eq, Data, Typeable)

data DataOpt = None | LiftToSMT
     deriving (Show, Eq, Data, Typeable)



instance Functor SMTOpt where
    fmap f (SMTCmd sexp) = SMTCmd (bimap f f sexp)
    fmap f (SMTLogLevel i) = SMTLogLevel i
    fmap f (SMTLogEnabled i) = SMTLogEnabled i

data Decl = 
    Data DataOpt [(Text, Term, [(Text, Term)])]
  | Def Text (Maybe Text) (Maybe Term) (Either Term (Maybe (SExpr Text Int)))
  -- | PropDef Text Term (SExpr Text Int)
  | SMTOptDef (SMTOpt Text)
  | Lang Text
  -- | RawSMT Text
  | TranslateDef Text Text [(Term, Maybe Term, Text)]
  | TranslateApp Text Text Text
    deriving (Eq, Data)

codom :: Term -> Term
codom (Π _ _ ρ) = codom ρ
codom (IΠ _ ρ) = codom ρ
codom (_ :⇒: ρ) = codom ρ
codom x = x


-- doesNotOccurIn :: MonadError String m => Text -> Term -> m ()
-- doesNotOccurIn c (Π ρ ρ') = do
--     doesNotOccurIn c ρ
--     doesNotOccurIn c ρ'
-- doesNotOccurIn c (e :@: es) =  do
--     doesNotOccurIn c e
-- --     mapM_ (liftM fmap (doesNotOccurIn c)) es
-- doesNotOccurIn c (Free (Global c')) = 
--     unless (c /= c') $ throwError "positivity check failed"
-- doesNotOccurIn _ _ = return ()


-- strictPositivityCheck' :: MonadError String m => Bool -> Text -> Term -> m ()
-- strictPositivityCheck' True c (Π ρ ρ') = do
--     strictPositivityCheck False c ρ
--     strictPositivityCheck True c ρ'
-- strictPositivityCheck' False c (Π ρ ρ') = do      --- (x : (ρ -> ρ')) -> ...
--     c `doesNotOccurIn` ρ
--     strictPositivityCheck' False c ρ'
-- strictPositivityCheck mustBeAppC c (e :@: es) = do
--     strictPositivityCheck' mustBeAppC c e
-- --     mapM_ (liftM fmap (doesNotOccurIn c)) es
-- strictPositivityCheck mustBeAppC c (Free (Global c')) = 
--     unless (not mustBeAppC || c == c') $ throwError "type constructor for type D x1 ... xn should have type ... -> D x1' ... xn'"
-- strictPositivityCheck mustBeAppC c _ = return ()

chooseNm nm Nothing = nm
chooseNm _ (Just nm) = nm


-- lifts simple types with type params like Tuple, List, Either, etc. to SMT
liftToSMT :: (MonadIO m, MonadError String m) =>  Γ -> [(Text, Term, [(Text, Term)])] -> m Γ
liftToSMT env ds = do -- [nm ty tyConns
    noOfParams <- mapM (\(_,ty,_) -> params ty) ds

    conns <- mapM (\(_,ty,tyConns) -> mapM (mkSMTCon ty) tyConns) ds


    -- here we declare the dataype with syntax:
    -- (declare-datatypes ((T n)) ((par (t0 ..tn) ((C0 ...) ... (Cn ...)))))
    -- we add these to smtRaw
    let pars n = [VAtom i | i <- upto n]
        def = List [NAtom "declare-datatypes", 
                List [List [NAtom $ nHash nm, NAtom (toS $ show nOp) ] | ((nm,_,_), nOp) <- zip ds noOfParams] ,
                List [List [NAtom "par", List (pars nOp), List cns ] | (nOp, cns) <- zip noOfParams conns]
            ]

        -- we map the constructors in our language to the lifted SMT term constructors
        -- e.g. ∷ : [cons] : {a : Type} -> (hd : Trm) -> (tl : List a) -> List a 
        -- gets mapped to {∷ -> ('cons 1 2)}
    let env' = foldr (\(_,_,tyConns) e -> addLiftedConToProps e tyConns) env ds
        -- we map a type signature in our language to the lifted SMT type constructor
        -- e.g data Either : Type -> Type -> * becomes {Either -> ('Either 0 1)}
        sexp nm nOp = case nOp of
            0 -> NAtom nm
            _ -> List $ NAtom nm : (reverse [VAtom i | i <- upto nOp])
        sexps = M.fromList $ map (\((nm,_,_),nOp) -> (nm, sexp (nHash nm) nOp)) $ zip ds noOfParams

        -- creates a map of SMT constructor names back to Term names:
        -- e.g. ∅ [nil] : ... becomes {nil -> ∅}
        unL = M.fromList $ concat $ 
            map (\(n,_, tys) ->
                (nHash n, n) : 
                (map (\(nm,_) -> (nHash nm, nm))) tys) ds


    return env'{
        props = sexps `M.union` (props env'),
        unLiftMap = unL `M.union` (unLiftMap env'),
        smtRaw = (smtRaw env') ++ [ toSMTSExp toS (\i -> "t" ++ show i) def ]}
    where
        upto :: Int -> [Int]
        upto 0 = []
        upto k = upto (k-1) ++ [k-1]

        nHash n = toS $ 'n' : (show $ hash n)

        -- counts the number of explicit parameters in a give type, ignoring implicit ones
        params :: MonadError String m => Term -> m Int
        params (Π _ _ trm) = (+1) <$> params trm
        params (IΠ _ _) = throwError "Implicit parameters not allowed in lifted SMT defintions."
        params (_ :⇒: _) = throwError "Synthesised parameters not allowed in lifted SMT defintions."
        params (_) = return 0

        -- encodes a term constructor into SMT-lib
        -- e.g. (∷) [cons] : {a : Type} -> (hd : a) -> (tl : List a) -> List a
        -- becomes (cons (hd t0) (tl (List t0)))

        -- nm' is the optional SMT name for the constructor, e.g. cons in (∷) [cons] : ...
        -- because CVC4 does not support unicode, the user needs to provide ASCII syntax
        -- when lifting datatypes to SMT
        mkSMTCon ty (nm, tyC) = do

            tyC' <- mkSMTConAux 0 ty tyC
            return $ List (NAtom (nHash nm) : tyC')

        mkSMTConAux i (Π _ ty trm) (IΠ ty' trmC)
            | ty == ty' = mkSMTConAux (i+1) trm trmC
            | otherwise = throwError "the order of implicit parameters must be the same as the declared type signature when lifting to SMT"
        mkSMTConAux _ StarT (C _) = return []
        mkSMTConAux _ StarT (_ :@: _) = return []
        mkSMTConAux i StarT (Π (Just n) ty tys) = 
            ((List [NAtom n, termToSExpr i ty]):) <$> mkSMTConAux (i+1) StarT tys
        mkSMTConAux _ _ _ = throwError "Lifting of this type is not supported"

        addLiftedConToProps env [] = env
        addLiftedConToProps env@Γ{..} ((nm, tyC):tys) = 
            addLiftedConToProps env{props = M.insert nm trm props} tys            
            where
                (tyP, tyTyP) = (init $ mkConProp 0 tyC, last $ mkConProp 0 tyC)

                -- if the type has no aruments like nil or none, we dont want to 
                -- return (nil)
                trmAux = case tyP of
                    [] -> NAtom $ nHash nm
                    _ -> List $ NAtom (nHash nm):tyP

                -- make sure that for something like nil : List a
                -- or left : a -> Either a b, we fully annotate the types to
                --  (as nil (List a)) and (as (left x) (Either a b))
                -- a constructor Cons : {a : Type} -> (hd:a) -> (tl : List a) -> List a
                -- becomes ('Cons 1 2) because all the typese are implicitly known from the
                -- arguments.
                trm = if ambiguous $ eraseLastType tyC 
                    then List [NAtom "as" ,trmAux, tyTyP]
                    else trmAux


        -- turn Π t1. ... Π tn. tk to
        -- Π t_1. ... Π t_n. _
        eraseLastType (IΠ ty tys) = IΠ ty $ eraseLastType tys
        eraseLastType (Π n ty tys) = Π n ty $ eraseLastType tys
        eraseLastType x = Free (UserHole (-1))

        isNotInTerm t = t == subst 0 (Free (UserHole (-2))) t
        
        ambiguous (IΠ _ tys) = isNotInTerm tys || ambiguous tys
        ambiguous (Π _ _ tys) = ambiguous tys
        ambiguous _ = False

termToSExpr :: Int -> Term -> SExpr Text Int
termToSExpr _ PropT = NAtom "Bool"
termToSExpr _ NameT = NAtom "String"
termToSExpr i (SetT a) = List [NAtom "Set", termToSExpr i a]
termToSExpr _ IntT = NAtom "Int"

termToSExpr i (x :@: args) = List (termToSExpr i x:mapApp args)
    where
        mapApp [] = []
        mapApp (I _:xs) = mapApp xs
        mapApp (E x:xs) = termToSExpr i x:mapApp xs
termToSExpr _ (C n) = NAtom $ toS $ 'n' : (show $ hash n)
termToSExpr j (Bound i) = VAtom $ j - i - 1
termToSExpr _ x = error $ pprintE x ++ " unsupported"


-- adds a VAtom i for each explicit parameter it encouters
-- and returns the final type as the last term,
-- e.g. Cons : {a : Type} -> (hd:a) -> (tl : List a) -> List a
-- becomes [1,2,(List 0)]
mkConProp :: Int -> Term -> [SExpr Text Int]
mkConProp i (IΠ _ tys) = mkConProp (i+1) tys
mkConProp i (Π _ ty tys) = VAtom i : mkConProp (i+1) tys 
mkConProp i x = [termToSExpr i x]

defineDecl :: (MonadIO m, MonadError String m) => Bool -> Γ -> Decl -> m Γ 
defineDecl ignoreCodom env (Data opt ds) = do
    -- first check to make sure none of the types are already defined
    forM_ ds (\(n,_,_) -> case M.lookup (Global n) (types env) of
        Just _ -> throwError $ "constant " ++ toS n ++ " already defined"
        Nothing -> pure ())

    -- eval the type signatures so we have all the mutually defined type signatures in scope for the next part
    tySigs <- forM ds (\(n,t,_) -> do
        unless (codom t == StarT) $ throwError $ toS n ++ " data declaration should have type ... -> */Prop"
        t' <- evalTypeOf0 env t VStarT
        return (Global n, eval t' []))

    env' <- foldM (\e ((n,_,xs),(_,τ)) -> do
        (Γ tys' _ _ _ _ _ _ _ _ _ _ _) <- defineTyCon e n xs
        return $ e{
            types = M.insert (Global n) τ $ tys' `M.union` (types e), 
            constrs = M.insert (Global n) (S.fromList $ map (\(n,_) -> Global n) xs) (constrs e) }
        ) env{types = (types env) `M.union` (M.fromList tySigs)} (zip ds tySigs)

    if opt == LiftToSMT then liftToSMT env' ds else pure env'


defineDecl _ env (SMTOptDef o) = defineSMTOpt env o
defineDecl _ env@Γ{..} (Lang l) = 
    if l `S.member` langs then throwError $ "language " ++ toS l ++ " already defined"
        else return $ env{langs = S.insert l langs}
defineDecl _ env@Γ{..} (TranslateDef n l cs) = do -- [(Term, Maybe Term, Text)]
    unless (l `S.member` langs) $ throwError $ "language " ++ toS l ++ " has not been defined"
    case M.lookup (Global n) constrs of
        Just cs' -> do
            env' <- defineTranslation env l cs
            unless (S.fromList (map (\(trm,_,_) -> 
                case trm of
                    C n :@: _ -> Global n
                    C n ->  Global n) cs) == cs') $ 
                liftIO $ putStrLn $ "\n\n-------------------------------------------\n" ++
                    "Warning: Patterns of " ++ toS n ++ " : " ++ toS l ++ " are incomplete." ++
                    "\n-------------------------------------------\n\n"
            return env'
        Nothing -> throwError $ "Type " ++ toS n ++ " has not been defined."
defineDecl _ env@Γ{..} (TranslateApp d l fp) = do
    case M.lookup (Global d) defs of
        Just (trm, ty) -> do
            str <- translate env l trm (quote0 ty)
            liftIO $ putStrLn $ "\n\n-------------------------------------------\n" ++ "output:\n" ++
                toS str ++ "\n-------------------------------------------\n\n"

        Nothing -> throwError $ "Def " ++ toS d ++ " does not exist."
    return env
-- def x = e case
defineDecl _ env@Γ{..} (Def n _ Nothing (Left trm)) = do
    case (M.lookup (Global n) types, M.lookup (Global n) defs) of
        (Just _, Just _) -> throwError $ "constant " ++ toS n ++ " already defined"
        (Just _, Nothing) -> throwError $ "constant " ++ toS n ++ " already defined"
        (Nothing, Just _) -> throwError $ "constant " ++ toS n ++ " already defined"
        (Nothing, Nothing) -> do
            (t', τ) <- runElabType0 False env trm
            liftIO $ putStrLn $ "\n\n-------------------------------------------\n" ++
                                "Successfully elaborated\n" ++ pprint infixM t' ++ " : " ++ pprint infixM τ ++
                                "\n-------------------------------------------\n\n"
            return $ env{defs = M.insert (Global n) (t', τ) defs}

-- smt-builtin x : t ... case
defineDecl ignoreCodom env@Γ{..} (Def n (Just nSMT) (Just ty) (Right Nothing)) = do
    case M.lookup (Global n) types of
        Just _ -> throwError $ "constant " ++ toS n ++ " already defined"
        Nothing -> do
            ty' <- evalTypeOf0 env ty VStarT
            let τ = eval ty' []
                sexp = List $ (NAtom $ nSMT) : (init $ mkConProp 0 ty')

            return $ env{types = M.insert (Global n) τ $ types, props = M.insert n sexp props}
-- smt-def x : T where ... case
defineDecl ignoreCodom env@Γ{..} (Def n _ (Just t) (Right (Just sexp))) = do
    case M.lookup (Global n) types of
        Just _ -> throwError $ "constant " ++ toS n ++ " already defined"
        Nothing -> do
            t' <- evalTypeOf0 env t VStarT
            let τ = eval t' []
            if sexp `contains` n
            then do
                let defFunRec = SMT.List [
                        SMT.Atom "define-fun-rec", 
                        SMT.Atom nHash, 
                        toSMTSExp toS (\i -> "v" ++ show i) $ List $ mkTySig 0 t',
                        toSMTSExp toS (\i -> "v" ++ show i) $ last $ mkConProp 0 t', 
                        toSMTSExp toS (\i -> "v" ++ show i) $ replaceWithHashed types' sexp]
                    types' = M.insert (Global n) τ $ types
                    nHash = 'n' : (show $ hash n)
                    tySig = List $ (NAtom $ toS $ nHash) : (init $ mkConProp 0 t')
                return $ env{
                    types = types',
                    props = M.insert n tySig props,
                    smtRaw = smtRaw ++ [ defFunRec ]}
            else return $ env{types = M.insert (Global n) τ $ types, props = M.insert n sexp props}
    where
        contains :: SExpr Text a -> Text -> Bool
        contains (NAtom n) m = n == m
        contains (VAtom _) _ = False
        contains (List xs) m = foldr ((||).(flip contains m)) False xs

        mkTySig :: Int -> Term -> [SExpr Text Int]
        mkTySig i (IΠ _ tys) = mkTySig (i+1) tys
        mkTySig i (Π _ ty tys) = (List [VAtom i, termToSExpr i ty]) : mkTySig (i+1) tys 
        mkTySig i x = []

        replaceWithHashed tys (NAtom n) = case 
            M.lookup (Global n) tys of
                Just _ -> NAtom $ toS $ 'n' : (show $ hash n)
                Nothing -> NAtom n
        replaceWithHashed tys (List xs) = List $ map (replaceWithHashed tys) xs 
        replaceWithHashed _ x = x

-- defineDecl ignoreCodom env@Γ{..} (PropDef n t sexp) = do
--     case M.lookup (Global n) types of
--         Just _ -> throwError $ "constant " ++ toS n ++ " already defined"
--         Nothing -> do
--             t' <- evalTypeOf0 env t VStarT
--             let τ = eval t' []
--             -- if ignoreCodom then pure () else unless (codom t == Prop) $ throwError $ toS n ++ " data declaration should have type ... -> */Prop"
--             return $ env{types = M.insert (Global n) τ $ types, props = M.insert n sexp props}
-- def x : T where ... case
defineDecl _ env@Γ{..} (Def n _ (Just ty) (Left trm)) = do
    case (M.lookup (Global n) types, M.lookup (Global n) defs) of
        (Just _, Just _) -> throwError $ "constant " ++ toS n ++ " already defined"
        (Just _, Nothing) -> throwError $ "constant " ++ toS n ++ " already defined"
        (Nothing, Just _) -> throwError $ "constant " ++ toS n ++ " already defined"
        (Nothing, Nothing) -> do
            (ty',_) <- runElabType0 True env ty
            pure ()  `debug` ("\nran elabType0 on ty and got: " ++ pprint infixM ty')
            -- let trm = Λ (mkLam ty') trmBody
            trm' <- evalTypeOf0 env trm (eval ty' [])
            pure () `debug` ("\nran evalTypeOf0 on trm and got: " ++ pprint infixM trm')
 
            -- -- if the elab term is a hole, we dont want to try to elab its type again...
            -- ty'' <- case trm' of
            --     (H _) -> pure $ eval ty' []
            --     _ -> do

            --         -- this is complete hackery... use case is:
            --         -- def test2 : Trm _ where
            --         --     test2 = var 'y
            --         -- end
            --         -- here we first elaborate the type, namely Trm _ becomes Trm M0
            --         -- then we type-check the body (var 'y) against Trm M0 getting the elaborated (var {{|'y|}} 'y)
            --         -- finally we ask for the full type of var {{|'y|}} 'y
            --         -- not sure this actually does anything...
            --         (_, ty''') <- runElabType0 False env trm'
            --         return ty'''
            liftIO $ putStrLn $ "\n\n-------------------------------------------\n" ++
                                "Successfully elaborated\n" ++ pprint infixM trm' ++ " : " ++ pprint infixM ty' ++
                                "\n-------------------------------------------\n\n"
            return $ env{defs = M.insert (Global n) (trm', eval ty' []) defs}
    where
        mkLam (IΠ t tys) = I t : mkLam tys
        mkLam (Π _ t tys) = E t : mkLam tys
        mkLam _ = []


defineTyCon :: (MonadIO m, MonadError String m) =>  Γ -> Text -> [(Text, Term)] -> m Γ 
defineTyCon env@Γ{..} _ [] = return $ env{types = M.empty}
defineTyCon env@Γ{..} n ((c, t):xs) = do
    (Γ tys' _ _ _ _ _ _ _ _ _ _ _) <- defineTyCon env n xs
    case M.lookup (Global c) (types `M.union` tys') of
        Just _ -> throwError $ "constant " ++ toS c ++ " already defined"
        Nothing -> do
            case codom t of
                (C c') -> unless (c' == n) $ throwError $ "The constructor for type " ++ toS n ++ ", must be of the shape ... -> " ++ toS n ++ "\n instead found: " ++ pprint infixM (codom t)
                (C c' :@: _) -> unless (c' == n) $ throwError $ "The constructor for type " ++ toS n ++ " ... , must be of the shape ... -> " ++ toS n ++ " ...\n instead found: " ++ pprint infixM (codom t)
                _ -> throwError $ "constructor " ++ pprint infixM c ++ " : " ++ pprint infixM t ++ " of incorrect shape"
            -- (t', τ) <- evalElabType0 g t
            t' <- evalTypeOf0 env t VStarT
            -- strictPositivityCheck True n t
            return $ env{types = M.insert (Global c) (eval t' []) tys'} -- `debug` ("have " ++ show t ++ " found " ++ show t') 


defineSMTOpt env@Γ{..} (SMTCmd sexp) = return env{smtOpts = toSMTSExp toS toS sexp : smtOpts}
defineSMTOpt env@Γ{..} (SMTLogLevel i) = return env{smtLogLevel = i}
defineSMTOpt env@Γ{..} (SMTLogEnabled b) = return env{smtLogEnabled = b}


defineTranslation :: MonadError String m => Γ -> Text -> [(Term, Maybe Term, Text)] -> m Γ
defineTranslation env _ [] = return env
defineTranslation env@Γ{..} l ((x@(C n :@: args),typ,str):xs) =
    case M.lookup (Global n) types of
        Just trmTy -> do
            unless (checkPattern (quote0 trmTy) args) $ throwError $ "The pattern " ++ pprint infixM x ++ " is malformed."
            argsT <- case typ of
                Just (C nT :@: argsT) -> do
                    case M.lookup (Global n) types of
                        Just tyTy -> unless (checkPattern (quote0 tyTy) argsT) $ throwError $ "The pattern " ++ pprint infixM x ++ " is malformed."
                        Nothing -> throwError $ "The type " ++ show nT ++ " is not defined."
                    return $ Just argsT
                Just p -> throwError $ "The term " ++ pprint infixM p ++ " is not a valid pattern."
                Nothing -> return Nothing
            defineTranslation env{translations = M.insert (l, Global n) (args, argsT, (T.replace "\\n" "\n" str)) translations} l xs
        Nothing -> throwError $ "The constructor " ++ show n ++ " is not defined."
defineTranslation env@Γ{..} l ((x@(C n),typ,str):xs) =
    case M.lookup (Global n) types of
        Just trmTy -> do
            unless (checkPattern (quote0 trmTy) []) $ throwError $ "The pattern " ++ pprint infixM x ++ " is malformed."
            argsT <- case typ of
                Just (C nT :@: argsT) -> do
                    case M.lookup (Global n) types of
                        Just tyTy -> unless (checkPattern (quote0 tyTy) argsT) $ throwError $ "The pattern " ++ pprint infixM x ++ " is malformed."
                        Nothing -> throwError $ "The type " ++ show nT ++ " is not defined."
                    return $ Just argsT
                Just p -> throwError $ "The term " ++ pprint infixM p ++ " is not a valid pattern."
                Nothing -> return Nothing
            defineTranslation env{translations = M.insert (l, Global n) ([], argsT, (T.replace "\\n" "\n" str)) translations} l xs
        Nothing -> throwError $ "The constructor " ++ show n ++ " is not defined."
defineTranslation env@Γ{..} l (p:xs) = throwError $ "The term " ++ pprint infixM p ++ " is not a valid pattern."



checkPattern :: Term -> [ExplImpl Term] -> Bool
checkPattern (Π _ _ _) [] = False
checkPattern (IΠ _ trm) [] = checkPattern trm []
checkPattern (_ :⇒: trm) xs = checkPattern trm xs
checkPattern (Π _ _ trm) (E (C x):xs) = checkPattern trm xs
checkPattern (IΠ _ trm) (E (C x):xs) = checkPattern trm (E (C x):xs)
checkPattern trm@(Π _ _ _) (I (C x):xs) = checkPattern trm xs
checkPattern (IΠ _ trm) (I (C x):xs) = checkPattern trm xs
checkPattern _ _ = True
      

translate :: (MonadIO m, MonadError String m) => Γ -> Text -> Term -> Term -> m Text
-- this might need to be modified, if we want to return a JSON tree where every term is fully typed.
-- this would probably involve writing the toJSON function my hand....
translate _ l trm ty | l == "JSON" = return $ toS $ encode (trm, ty)
translate env@Γ{..} _ (C n) StarT = return $ toS $ n
translate _ _ (MkName n) NameT = return n
translate env l (MkSet ty xs) (SetT _) = do
    xs' <- mapM (\t -> translate env l t ty) xs
    return $ "{" <> T.intercalate "," xs' <> "}"
translate env@Γ{..} _ trm (Π _ _ _) = return $ toS $ pprint infixM trm
translate env@Γ{..} _ trm (IΠ _ _) = return $ toS $ pprint infixM trm
translate env@Γ{..} _ trm (_ :⇒: _) = return $ toS $ pprint infixM trm
translate env@Γ{..} l trm ty = do
    (n, args, nTy, argsTy) <- case (trm, ty) of
        (C n, C nTy) -> return (n, [], nTy, [])
        (C n, C nTy :@: argsTy) -> return (n, [], nTy, argsTy)
        (C n :@: args, C nTy) -> return (n, args, nTy, [])
        (C n :@: args, C nTy :@: argsTy) -> return (n, args, nTy, argsTy)
        _ -> throwError $ "Expected app in " ++ pprint infixM (trm, ty)
    case M.lookup (l, (Global n)) translations of
        Just (trmPat, Just tyPat, str) -> do
            args' <- translateExpImpApp env l args
            argsTy' <- translateExpImpApp env l argsTy
            let mapTrm = unifyPattern trmPat args' 
            -- sortBy (\(a,_) (b,_) -> compare (T.length b) (T.length a)) $ unify trmPat args' 
            let mapTy = unifyPattern tyPat argsTy' 
            return $ foldr (\(pn, trm) s -> T.replace ("#{" <> pn <> "}") trm s) str $ mapTrm ++ mapTy
        Just (trmPat, Nothing, str) -> do
            args' <- translateExpImpApp env l args
            let mapTrm = unifyPattern trmPat args' 
            return $ foldr (\(pn, trm) s -> T.replace ("#{" <> pn <> "}") trm s) str $ mapTrm
        Nothing -> do
            -- args' <- translateExpImpApp env l args
            return $ toS $ pprint infixM trm

    where
        translateExpImpApp :: (MonadIO m, MonadError String m) => 
            Γ -> Text -> [ExplImpl Term] -> m [ExplImpl Text]
        translateExpImpApp _ _ [] = return []
        translateExpImpApp env l (E t:xs) = do
            (_, ty) <- runElabType0 False env t `debug` ("Elab: " ++ pprint infixM t)
            t' <- translate env l t (quote0 ty)
            xs' <- translateExpImpApp env l xs
            return $ E t':xs'
        translateExpImpApp env l (I t:xs) = do
            (_, ty) <- runElabType0 False env t `debug` ("Elab: " ++ pprint infixM t)
            t' <- translate env l t (quote0 ty)
            xs' <- translateExpImpApp env l xs
            return $ I t':xs'

unifyPattern :: [ExplImpl Term] -> [ExplImpl a] -> [(Text,a)]
unifyPattern [] [] = []
unifyPattern (I _:xs) [] = unifyPattern xs []
unifyPattern [] (I _:xs) = unifyPattern [] xs
unifyPattern (I (C pn):ps) (I trm:ts) = (pn, trm): unifyPattern ps ts
unifyPattern (E (C pn):ps) (E trm:ts) = (pn, trm): unifyPattern ps ts
unifyPattern (I _:ps) ts@(E _:_) = unifyPattern ps ts
unifyPattern ps@(E _:_) (I _:ts) = unifyPattern ps ts



