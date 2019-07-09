{-# LANGUAGE OverloadedStrings, DeriveDataTypeable, FlexibleContexts, 
PatternSynonyms, DeriveFunctor, DeriveGeneric, DeriveAnyClass, 
ScopedTypeVariables, TypeApplications, FlexibleInstances, IncoherentInstances, 
StandaloneDeriving, RecordWildCards #-}


module LamPi where

import UnicodeEnc

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
infixl 7 :@:

debugMode = False
-- smtLogMode = True

showImpl = False

debug = if debugMode then flip trace else (\a _ -> a)

data ExplImpl a = I a | E a deriving (Show, Eq, Ord, Data, Functor, Generic, ToJSON)

data Name = Global Text
          | Local Int
          | Quote Int
          | Meta Int
          | InferMeta
          | UserHole Int
          deriving (Eq, Ord, Data, Generic, ToJSON)

instance Show Name where
    show (Global t) = toS t 
    show (Local i) = "L" ++ show i
    show (Quote i) = "Q" ++ show i
    show (Meta i) = "M" ++ show i
    show (UserHole i) = "?" ++ show i
    show InferMeta = "_"

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
          deriving (Ord, Data, Generic, ToJSON)

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




instance Show Term where
    show StarT = "*"
    show PropT = "Prop"
    show NameT = "Name"
    show (MkName s) = "\'" ++ toS s
    show (SetT a) = "Set " ++ show a
    show (MkSet a s) = "(⦃" ++ (intercalate "," (S.toList (S.fromList (map show s)))) ++ "⦄ : " ++ "Set " ++ show a ++ ")"
    show IntT = "Int"
    show (MkInt i) = toS $ show i
    show (Π Nothing t t') = "Π " ++ show t ++ " . " ++ show t'
    show (Π (Just n) t t') = "Π (" ++ toS n ++ ") " ++ show t ++ " . " ++ show t'
    show (IΠ t t') = "Π {" ++ show t ++ "} . " ++ show t'
    show (t :⇒: t') = "[" ++ show t ++ "] -> " ++ show t'
    show (Bound n) = "B" ++ show n
    show (Free n) = show n
    show (x :@: xs) = show x ++ " " ++ showApp xs
        where
            showApp [] = ""
            showApp [I x] = if showImpl then "{" ++ show x ++ "}" else ""
            showApp [E x@(_ :@:_)] = "(" ++ show x ++ ")"
            showApp [E x] = show x
            showApp (I x:xs) = (if showImpl then "{" ++ show x ++ "} " else "") ++ showApp xs
            showApp ((E x@(_ :@:_)):xs) = "(" ++ show x ++ ") " ++ showApp xs
            showApp ((E x):xs) = show x ++ " " ++ showApp xs


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
           | VNeutral Neutral

instance Show Value where
    show = show . quote0


data Neutral = NFree Name
             -- | NConst Text
             | NApp Neutral [ExplImpl Value]
             -- | NIApp Neutral Value
             -- | NHole Value

type Type = Value
-- newtype Γ = Γ { unΓ :: [(Name, Type)] } deriving Show

data Γ = Γ { 
    types :: Map Name Type
  , constrs :: Map Name (Set Name)
  , defs :: Map Name (Term, Type)
  , props :: Map Text (SExpr Text Int)
  , langs :: Set Text
  , translations :: Map (Text, Name) ([ExplImpl Term], Maybe [ExplImpl Term], Text)
  , smtOpts :: [SMT.SExpr]
  , smtRaw :: [SMT.SExpr]
  , smtLogLevel :: Int
  , smtLogEnabled :: Bool
 }

emptyΓ = Γ M.empty M.empty M.empty M.empty (S.fromList ["JSON"]) M.empty [] [] 0 False

instance Show Γ where
    show Γ{..} = "\n\n\n\nTypes:\n" ++ 
        (intercalate "\n" $ map (\(n,t) -> show n ++ " -> " ++ show t) $ M.toList types) ++
        "\n\n--------------------------------------------------------\n\nConstructors:\n" ++
        (intercalate "\n" $ map (\(n,e) -> show n ++ " : " ++ (show $ S.toList e)) $ M.toList constrs) ++
        "\n\n--------------------------------------------------------\n\nDefs:\n" ++
        (intercalate "\n" $ map (\(n,(e,t)) -> show n ++ " : " ++ show t ++ " = " ++ show e) $ M.toList defs) ++
        "\n\n--------------------------------------------------------\n\nDefined Props:\n" ++
        (intercalate "\n" $ map (\(n,e) -> show n ++ " : " ++ show e) $ M.toList props) ++
        "\n\n--------------------------------------------------------\n\nDefined Languages:\n" ++
        (intercalate "," $ map show $ S.toList langs) ++
        "\n\n--------------------------------------------------------\n\nTranslations:\n" ++
        (intercalate "\n" $ map (\(n,e) -> show n ++ " : " ++ show e) $ M.toList translations) ++
        "\n\n--------------------------------------------------------\n\nSMT opts:\n" ++
        (intercalate "," $ map (\e -> SMT.showsSExpr e "") $ smtOpts) ++
        "\n\n--------------------------------------------------------\n\nSMT opts:\n" ++
        (intercalate "," $ map (\e -> SMT.showsSExpr e "") $ smtRaw) ++
        "\n\n--------------------------------------------------------\n\nSMT Log level: " ++ show smtLogLevel ++ 
        "\n\n--------------------------------------------------------\n\nSMT Log enabled: " ++ show smtLogEnabled

type Env = [Value]


vfree :: Name -> Value
vfree n = VNeutral (NFree n)


vapp :: Value -> [ExplImpl Value] -> Value 
-- vapp (VLam f) v =f v
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


newtype ConstrList = ConstrList { unConstrList :: [(Term,Term)] } deriving (Eq, Show)

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

lookupInΓ :: (Has Γ s, MonadState s m , MonadError String m) => Name -> m Type
lookupInΓ n = do
    s <- get
    case M.lookup n (types $ getter s) of
        Just τ -> return τ
        Nothing -> throwError ("unknown identifier: " ++ show n)

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

checkDoesNotContainMetas here t = unless (doesNotContainMetas t) $ throwError "" `debug` (show t ++ " contains metas!" ++ here)




newtype SATConstrList = SATConstrList { unSATConstrList :: [Term] } deriving (Eq, Show)

addToSATConstrList :: (Has SATConstrList s, MonadState s m) => SATConstrList -> m ()
addToSATConstrList (SATConstrList xs) = modify (\s -> modifier (\(SATConstrList ys) -> SATConstrList $ xs ++ ys) s)

getSATConstrList :: (Has SATConstrList s, MonadState s m) => m SATConstrList
getSATConstrList = getter <$> get


elabType :: (Has BVCounter s, Has MetaCounter s, Has Γ s, Has ConstrList s, Has SATConstrList s,
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
    let α'' = eval α' [] `debug` ("{| |} : " ++ (show $ eval α' []))
    return $ (MkSet α' [], VSetT α'')
elabType (MkSet α xs) = do
    -- let α' = eval α [ ]
    α' <- typeOf α VStarT
    let α'' = eval α' []
    xs' <- mapM (flip typeOf α'') xs
    pure ()  `debug` (show xs' ++ " : " ++ show α'')
    return (MkSet α' xs', VSetT α'')
elabType (Π n ρ ρ') = do
    τ <- typeOf ρ VStarT
    i <- getFreshAndIncrementBV
    addToΓ (Local i) $ eval ρ []
    
    smap <- getSExprMap
    -- using this to only define bound vars that have a SAT representation
    case toSExprMaybe smap ρ of
        Just ty -> do
            (SMTSolver proc) <- getHas `debug` ("found bound " ++ show i ++ " : " ++ show ρ)
            liftIO $ SMT.declare proc ("L" ++ show i) ty
            return ()
        Nothing -> return ()

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
    checkDoesNotContainMetas "here1" y'' `debug` ("\n\n:⇒: " ++ show x')
    return (x :⇒: y'', VStarT)
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
    (es',τ') <- elabTypeApp τ es `debug` ("App head: " ++ show e' ++ " : " ++ show τ)
    return (e' :@: es', τ')
    -- typeOfApp i g σ es
elabType e = error $ "can't handle " ++ show e


elabTypeApp :: (Has BVCounter s, Has MetaCounter s, Has Γ s, Has ConstrList s, Has SATConstrList s,
    MonadState s m , Has SMTSolver s, MonadIO m, MonadError String m) => 
    Type -> [ExplImpl Term] -> m ([ExplImpl Term], Type)
elabTypeApp ty [] = case ty of
    (VIΠ τ τ') -> do
        mi <- getFreshAndIncrementMeta
        let mvar = Free (Meta mi)
        addToΓ (Meta mi) τ
        (xs',τ'') <- elabTypeApp (τ' (eval mvar [])) []
        return $ (I mvar:xs',τ'')
    (VΠ _ _ _) -> throwError $ "illegal application at " <> (toS $ show ty)
    (VSArr cnstr τ') -> do
        cnstr' <- typeOf (quote0 cnstr) VPropT
        (ConstrList cs) <- getConstrList 
        pure () `debug` ("\n\nConstrList is: "++ show cs)
        -- σ <- unifyConstraints cs [] False M.empty
        let cnstr'' = substMetas (mkMap cs) cnstr'
        addToSATConstrList $ SATConstrList [cnstr''] -- `debug` ("\nmap is: " ++ show σ)
        elabTypeApp τ' [] `debug` ("\n\nconstraint is: "++ show cnstr'')
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
        pure () `debug` ("\n\nConstrList is: "++ show cs)
        -- σ <- unifyConstraints cs [] False M.empty
        let cnstr'' = substMetas (mkMap cs) cnstr' -- substMetas σ cnstr'
        addToSATConstrList $ SATConstrList [cnstr''] -- `debug` ("\nmap is: " ++ show σ)
        elabTypeApp τ' (x:xs) `debug` ("\n\nconstraint is: "++ show cnstr'')
    _ -> throwError $ "illegal application at " <> (toS $ show x) <> " : " <> (toS $ show ty)



typeOf :: (Has BVCounter s, Has MetaCounter s, Has Γ s, Has ConstrList s, Has SATConstrList s,
    MonadState s m , Has SMTSolver s, MonadIO m, MonadError String m) => 
    Term -> Type -> m Term
typeOf e τ = do
    cs <- getConstrList `debug` ("calling tyOf on " ++ show e ++ " : " ++ show τ)
    (e',τ') <- elabType e
    pure () `debug` ("elaborated " ++ show e ++ " : " ++ show τ ++ " to " ++ show e' ++ " : " ++ show τ')
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
            return e' `debug` ("\n\nadding -> " ++ show e ++ " .... " ++ (show $ unifyType (quote0 τ) (quote0 τ')))

unifyType :: Term -> Term -> [(Term,Term)]
unifyType τ τ' | τ == τ' = []
unifyType (Free (Meta i)) τ' = [(Free (Meta i),τ')]
unifyType τ (Free (Meta i)) = [(Free (Meta i),τ)]
unifyType (x :@: xs) (y :@: ys) 
    | length xs == length ys = unifyType x y ++ (concat $ map unifyTypeApp $ zip xs ys)
    | otherwise = error $ "length of xs and ys is different: " ++ show (xs,ys)
    where

        unifyTypeApp :: (ExplImpl Term, ExplImpl Term) -> [(Term,Term)]
        unifyTypeApp (E x,E y) = unifyType x y
        unifyTypeApp (I x,I y) = unifyType x y
        unifyTypeApp _ = error "trying to unify E with I"
unifyType (SetT x) (SetT y) = unifyType x y
unifyType (MkSet a _) (MkSet b _) = unifyType a b

unifyType (H n) x = [(H n, x)]
unifyType x (H n) = [(H n, x)]
unifyType InferM InferM = error $ "\n\nfailed on : " ++ show InferM ++ " and " ++ show InferM ++ "\n\n"

unifyType x InferM = [] `debug` ("unifying " ++ show x ++ " with InferM")
unifyType InferM x = [] `debug` ("unifying " ++ show x ++ " with InferM")
unifyType τ τ' = error $ "\n\nfailed to unify on : " ++ show τ ++ " and " ++ show τ' ++ "\n\n"


data UnificationSettings = Full | Partial

unifyConstraints :: (MonadReader UnificationSettings m, MonadError String m) => [(Term,Term)] -> [(Term,Term)] -> Bool -> Map Int Term -> m (Map Int Term)
unifyConstraints []                                  []  _     m = return m
unifyConstraints []                                  acc False m = do
    s <- ask
    case s of
        Full -> throwError $ "cannot unify rest (acc): " ++ show acc ++ "; m contains: " ++ show m
        Partial -> return m `debug` ("cannot unify rest (acc): " ++ show acc ++ "; m contains: " ++ show m)
unifyConstraints []                                  acc True  m = 
    unifyConstraints (map (\(x,y) -> (substMetas m x, substMetas m y)) acc) [] False m
unifyConstraints ((M x, M y):xs) acc flag m = case (M.lookup x m, M.lookup y m) of 
    (Just (L _), Just _) -> unifyConstraints xs acc flag m
    (Just _, Just (L _)) -> unifyConstraints xs acc flag m
    (Just tx, Just ty) -> do
        unless (tx == ty) $ throwError $ "cannot unify (2): " ++ show [tx,ty]
        unifyConstraints xs acc flag m
    (Just tx, Nothing) -> unifyConstraints xs acc flag $ M.insert y tx m
    (Nothing, Just ty) -> unifyConstraints xs acc flag $ M.insert x ty m
    (Nothing, Nothing) -> unifyConstraints xs ((M x, M y):acc) flag m
unifyConstraints ((M x, y):xs)                       acc flag  m 
    | doesNotContainMetas y = unifyConstraints xs acc True $ M.insert x y m `debug` ("unify : " ++ show (M x, y))
    | otherwise = case M.lookup x m of
        Just tx -> unifyConstraints xs ((tx, y):acc) flag m `debug` ("unify oterwise : " ++ show (M x, y))
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
        matchApp (t , t') = throwError $ "cannot unify (in matchApp): " ++ show [t,t']

unifyConstraints ((H _, _):xs)                       acc flag  m = unifyConstraints xs acc flag m 
    -- `debug` ("\n================================\n" ++ show (H x) ++ " : " ++ show y ++ "\n================================")
unifyConstraints ((_, H _):xs)                       acc flag  m = unifyConstraints xs acc flag m
    -- `debug` ("\n================================\n" ++ show (H y) ++ " : " ++ show x ++ "\n================================")
unifyConstraints ((L _, _):xs)                       acc flag  m = unifyConstraints xs acc flag m 
unifyConstraints ((_, L _):xs)                       acc flag  m = unifyConstraints xs acc flag m 

unifyConstraints (x:_)                               _   _     _ = throwError $ "bad constraint " ++ show x


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


-- runElabType0' :: Γ -> Term -> Either String (Term, Type, [(Term,Term)])
-- runElabType0' g t = runExcept (flip evalStateT (MetaCounter 0,g,ConstrList []) $ elabType 0 t)



-- evalElabType0 :: MonadError String m => Γ -> Term -> m (Term, Type)
-- evalElabType0 g t = flip evalStateT (MetaCounter 0,g,ConstrList []) (elabType0 t)



-- toSExprT :: Term -> SExprT Term
-- toSExprT = undefined

newtype SATDefs = SATDefs { unSATDefs :: Set Int } deriving (Eq, Show)

newtype SMTSolver = SMTSolver { unSMTSolver :: SMT.Solver }

getHas :: (Has a s, MonadState s m) => m a
getHas = getter <$> get


addToSATDefs :: (Has SATDefs s, MonadState s m) => Int -> m ()
addToSATDefs i = modify (\s -> modifier (\(SATDefs ys) -> SATDefs $ S.insert i ys) s)


-- using this to only define bound vars that have a SAT representation
toSExprMaybe :: Map Text (SExpr Text Int) -> Term -> Maybe SMT.SExpr
toSExprMaybe _ PropT = pure $ SMT.tBool
toSExprMaybe _ NameT = pure $ SMT.const "String"
toSExprMaybe _ (MkName s) = pure $ SMT.const $ "\"" ++ toS s ++ "\""
toSExprMaybe smap (SetT a) = (\x -> SMT.fun "Set" [x]) <$> toSExprMaybe smap a
toSExprMaybe smap (MkSet a []) = 
    (\x -> SMT.fun "as" [SMT.const "emptyset", x]) <$> toSExprMaybe smap (SetT a)
toSExprMaybe smap (MkSet _ [x]) = do
    x' <- toSExprMaybe smap x
    return $ SMT.fun "singleton" [x']
toSExprMaybe smap (MkSet _ (x:xs)) = do
    x' <- toSExprMaybe smap x
    xs' <- mapM (toSExprMaybe smap) xs
    return $ SMT.fun "insert" $ xs' ++ [SMT.fun "singleton" [x']]
toSExprMaybe _ (M x) = pure $ SMT.const $ "M" ++ show x
toSExprMaybe smap t@(C op :@: args) = 
    case M.lookup op smap of
        Just sexp -> substSExpr smap t (map unExplImpl args) sexp
        Nothing -> Nothing
    
    where
        substSExpr :: Map Text (SExpr Text Int) -> Term -> [Term] -> SExpr Text Int -> Maybe SMT.SExpr
        substSExpr _ _ _ (NAtom x) = return $ SMT.Atom (toS x)
        substSExpr smap trm ts (VAtom i)
            | 0 <= i && i < length ts = toSExprMaybe smap (ts !! i)
            | otherwise = Nothing
        substSExpr smap trm ts (List xs) = SMT.List <$> 
            mapM (substSExpr smap trm ts) xs
        
        unExplImpl :: ExplImpl a -> a
        unExplImpl (I a) = a
        unExplImpl (E a) = a

-- toSExprMaybe _ (L i) = return $ SMT.const $ "L"++ show i

toSExprMaybe _ _ = Nothing


-- TODO replace this with toSExprMaybe + a suitable error message??

toSExpr :: Map Text (SExpr Text Int) -> Term -> SMT.SExpr
toSExpr _ PropT = SMT.tBool
toSExpr _ NameT = SMT.const "String"
toSExpr smap (MkName s) = SMT.const $ "\"" ++ toS s ++ "\""
toSExpr _ IntT = SMT.const "Int"
toSExpr smap (MkInt i) = SMT.const $ show i
toSExpr smap (SetT a) = SMT.fun "Set" [toSExpr smap a]
toSExpr smap (MkSet a []) = 
    SMT.fun "as" [SMT.const "emptyset", toSExpr smap (SetT a)]
toSExpr smap (MkSet _ [x]) = SMT.fun "singleton" [toSExpr smap x]
toSExpr smap (MkSet _ (x:xs)) = 
    SMT.fun "insert" $ map (toSExpr smap) xs ++ [SMT.fun "singleton" [toSExpr smap x]]
toSExpr _ (M x) = SMT.const $ "M" ++ show x

toSExpr smap t@(C op :@: args) = 
    case M.lookup op smap of
        Just sexp -> substSExpr smap t (map unExplImpl args) sexp
        Nothing -> error $ "operation not found " ++ toS op
    
    where
        substSExpr :: Map Text (SExpr Text Int) -> Term -> [Term] -> SExpr Text Int -> SMT.SExpr
        substSExpr _ _ _ (NAtom x) = SMT.Atom (toS x)
        substSExpr smap trm ts (VAtom i)
            | 0 <= i && i < length ts = toSExpr smap (ts !! i)
            | otherwise = error  $ "index out of range in " ++ show trm
        substSExpr smap trm ts (List xs) = SMT.List $ 
            map (substSExpr smap trm ts) xs
        
        unExplImpl :: ExplImpl a -> a
        unExplImpl (I a) = a
        unExplImpl (E a) = a

toSExpr _ (L i) = SMT.const $ "L"++ show i

toSExpr _ e = error $ "unsupported operation " ++ show e

 

fromSExpr :: SMT.SExpr -> Type -> Term
fromSExpr (SMT.Atom xs) VNameT = MkName $ toS $ filter (/= '"') xs
fromSExpr (SMT.Atom i) VIntT = MkInt $ read i
fromSExpr (SMT.List [SMT.Atom "as",SMT.Atom "emptyset",_]) (VSetT a) = MkSet (quote0 a) []
fromSExpr (SMT.List [SMT.Atom "singleton",n])          (VSetT a) = MkSet (quote0 a) [fromSExpr n a]
fromSExpr (SMT.List [SMT.Atom "union", xs, ys])        (VSetT a) = 
    let (MkSet a' xs') = fromSExpr xs (VSetT a)
        (MkSet _ ys') = fromSExpr ys (VSetT a) in
        MkSet a' $ xs' ++ ys'



defineMetas :: (MonadIO m, Has SMTSolver s, Has Γ s, Has SATDefs s, MonadState s m, MonadError String m) => 
    Term -> m ()
defineMetas (M n) = do
    (SATDefs defined) <- getHas
    if not (n `S.member` defined) then do
        τ <- lookupInΓ (Meta n)
        smap <- getSExprMap
        (SMTSolver proc) <- getHas `debug` ("found meta " ++ show n ++ " : " ++ show τ)


        -- liftIO $ SMT.declare proc ("M" ++ show n) (toSExpr smap $ quote0 τ)

        -- using this to only define bound vars that have a SAT representation
        case toSExprMaybe smap $ quote0 τ of
            Just ty -> do
                (SMTSolver proc) <- getHas `debug` ("found meta " ++ show n ++ " : " ++ show τ)
                liftIO $ SMT.declare proc ("M" ++ show n) ty
                return ()
            Nothing -> return ()

        addToSATDefs n
    else pure ()
defineMetas (e :@: es) = mapM_ (\x -> case x of
    E y -> defineMetas y
    I y -> defineMetas y) es
defineMetas _ = return ()

checkSMT :: (Has Γ s, Has ConstrList s, Has SATConstrList s, Has SATDefs s,
    MonadState s m , Has SMTSolver s, MonadIO m, MonadError String m) => Term -> m ()
checkSMT trm = do
    (ConstrList cs) <- getConstrList
    -- get collected sat constraints and replace all equal metas, collected in ConstrList
    (SATConstrList satcs) <- getSATConstrList
    let satcs' = map (substMetas $ mkMap cs) satcs

    -- translate to sat, first defining all meta variables
    mapM_ defineMetas satcs'
    (SMTSolver proc) <- getHas `debug` ("produced following sat goals: " ++ show satcs')
    smap <- getSExprMap
    -- mapM_ (\s -> liftIO $ SMT.assert proc $ toSExpr smap s) satcs'
    mapM_ (\(s,i) -> liftIO $ SMT.assert proc $ SMT.named ('_':show i) $ toSExpr smap s) (zip satcs' [0..])

    -- check sat

    (SMTSolver proc) <- getHas
    r <- liftIO $ SMT.check proc
    case r of
        SMT.Sat -> do
            (SATDefs defined) <- getHas
            forM_ (S.toList defined) (\d -> do
                (SMT.Other v) <- liftIO $ SMT.getExpr proc (SMT.const $ "M" ++ show d)
                τ <- lookupInΓ (Meta d) `debug` ("\n\nSMT returned: " ++ show v)
                let vt = fromSExpr v τ 
                addToConstrList $ ConstrList [(M d,vt)] `debug` ("\n\nadding const: " ++ show (M d,vt)))
        SMT.Unsat -> do 
            (SMT.List res) <- liftIO $ SMT.command proc (SMT.List [ SMT.Atom "get-unsat-core" ])
            let unsat_core = map (\(SMT.Atom (_:num)) -> (read num :: Int)) res
            σ <- unifyConstraintsPart cs [] False M.empty -- `debug` ("\n\nelabType0 constraints: " ++ show cs' ++ "\nmkMap cs = " ++ show (mkMap cs) ++ "\n sat constraints: " ++ show satcs' )
            
            throwError $ "The following constraints are unsatisfiable:\n" ++
                (intercalate "\n" $ map (\i -> "- " ++ (show $ substMetas σ $ satcs' !! i)) unsat_core) ++
                "\nin the term:\n" ++ show trm

        _ -> throwError $ "unknown result"


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
    liftIO $ mapM_ (\(n,x) -> putStrLn $ ("\n================================\n" ++ show (H n) ++ " : " ++ show x ++ "\n================================")) holes
    unless (canContainMetas || doesNotContainMetas trm')$ throwError $ show trm' ++ " contains metas! (elabType0)"
    unless (doesNotContainMetas typ')$ throwError $ show typ' ++ " contains metas! (elabType0)"
    return $ (trm', eval typ' []) `debug` ("cs now contains: " ++ show cs')



elabType0' ::  (Has BVCounter s, Has MetaCounter s, Has Γ s, Has ConstrList s, Has SATConstrList s, Has SATDefs s,
    MonadState s m , Has SMTSolver s, MonadIO m, MonadError String m) => 
    Term -> Term -> m (Term, Type)
elabType0' trm ty = do 
    (ty',_) <- elabType ty
    trm' <- typeOf trm (eval ty' [])

    checkSMT trm
    -- get model and add to cs

    -- liftIO $ SMT.stop proc
    (ConstrList cs') <- getConstrList -- `debug` "stopped SMT"
    σ <- unifyConstraintsFull cs' [] False M.empty -- `debug` ("\n\nelabType0 constraints: " ++ show cs' ++ "\nmkMap cs = " ++ show (mkMap cs) ++ "\n sat constraints: " ++ show satcs' )
    let trm'' = substMetas σ trm'
        ty' = substMetas σ ty
        holes = map (\(n,x) -> (n,substMetas σ x)) $ getHoles cs'
    liftIO $ mapM_ (\(n,x) -> putStrLn $ ("\n================================\n" ++ show (H n) ++ " : " ++ show x ++ "\n================================")) holes
    unless (doesNotContainMetas trm'')$ throwError $ show trm'' ++ " contains metas! (elabType0')"
    unless (doesNotContainMetas ty')$ throwError $ show ty' ++ " contains metas! (elabType0')"
    return $ (trm'', eval ty' []) `debug` ("cs now contains: " ++ show cs')




getHoles [] = []
getHoles ((H n, x):xs) = (n,x) : getHoles xs
getHoles ((x, H n):xs) = (n,x) : getHoles xs
getHoles (_:xs) = getHoles xs

-- runElabType0 :: Bool -> Γ -> Term -> IO (Either String (Term, Type))
-- runElabType0 canContainMetas g t = do
--     smt <- initSMT

--     res <- runExceptT $ (flip (evalStateT @(ExceptT String IO)) (BVCounter 0,MetaCounter 0,g,ConstrList [],SATConstrList [], SATDefs S.empty, SMTSolver smt)) $ elabType0 canContainMetas t
--     liftIO $ SMT.stop smt
--     return res


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
    smt <- liftIO $ newSolver "cvc4" ["--incremental", "--lang" , "smt2.0"] (if smtLogEnabled then Just log else Nothing)
    setLogic <- smtSMTOptIsDefined "set-logic"
    unless setLogic $ 
        liftIO $ SMT.setLogic smt "QF_UFSLIAFS" -- "QF_UFLIAFS"
    
    produceUnsatCores <- smtSMTOptIsDefined ":produce-unsat-cores"
    unless produceUnsatCores $ 
        liftIO $ SMT.setOption smt ":produce-unsat-cores" "true"
    
    forM_ smtOpts (\x -> liftIO $ SMT.ackCommand smt x)

    return smt


runElabType0' :: (MonadIO m, MonadError String m) => Bool -> Γ -> Term -> m (Term, Type)
runElabType0' canContainMetas g t = do
    smt <- runReaderT initSMT g

    res <- (flip evalStateT (BVCounter 0,MetaCounter 0,g,ConstrList [],SATConstrList [], SATDefs S.empty, SMTSolver smt)) $ elabType0 canContainMetas t
    liftIO $ SMT.stop smt
    return res

runElabType0List :: (MonadIO m, MonadError String m) => Γ -> Term -> Term -> m (Term, Type)
runElabType0List g trm ty = do
    smt <- runReaderT initSMT g

    res <- (flip (evalStateT ) (BVCounter 0,MetaCounter 0,g,ConstrList [],SATConstrList [], SATDefs S.empty, SMTSolver smt)) $ elabType0' trm ty
    liftIO $ SMT.stop smt
    return res




typeOf0 ::  (Has BVCounter s, Has MetaCounter s, Has Γ s, Has ConstrList s, Has SATConstrList s, Has SATDefs s,
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
    liftIO $ mapM_ (\(n,x) -> putStrLn $ ("\n================================\n" ++ show (H n) ++ " : " ++ show x ++ "\n================================")) holes

    unless (doesNotContainMetas trm')$ throwError $ show trm' ++ " contains metas! (typeOf0)"
    return $ trm'



-- elabType0 ::  (Has BVCounter s, Has MetaCounter s, Has Γ s, Has ConstrList s, Has SATConstrList s, Has SATDefs s,
--     MonadState s m , Has SMTSolver s, MonadIO m, MonadError String m) => 
--     Term -> m (Term, Type)


-- evalTypeOf0 :: MonadError String m => Γ -> Term -> Type -> m Term
-- evalTypeOf0 g t τ = flip evalStateT (BVCounter 0,MetaCounter 0,g,ConstrList [],SATConstrList []) (typeOf0 t τ) `debug` ("evalTypeOf0 ... " ++ show t ++ " : " ++ show τ)


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
    Data DataOpt Text Term [(Text, Maybe Text, Term)]  
  | Def Text (Maybe Term) Term
  | PropDef Text Term (SExpr Text Int)
  | SMTOptDef (SMTOpt Text)
  | Lang Text
  | TranslateDef Text Text [(Term, Maybe Term, Text)]
  | TranslateApp Text Text Text
    deriving (Show, Eq, Data)

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

upto :: Int -> [Int]
upto 0 = []
upto k = upto (k-1) ++ [k-1]

liftToSMT :: (MonadIO m, MonadError String m) =>  Γ -> Text -> Term -> [(Text, Maybe Text, Term)] -> m Γ
liftToSMT env nm ty tyConns = do
    noOfParams <- params ty
    conns <- mapM (mkCon ty) tyConns
    let pars = [SMT.Atom ("t" ++ show i) | i <- upto noOfParams]
        def = SMT.List [SMT.Atom "declare-datatypes", 
                SMT.List [SMT.List [SMT.Atom (toS nm), SMT.Atom (show noOfParams) ]] ,
                SMT.List [SMT.List [SMT.Atom "par", SMT.List pars, SMT.List conns ]]
            ]
    -- liftIO $ putStrLn $ SMT.showsSExpr def ""
    -- liftIO $ putStrLn $ show nm ++ " : " ++ show ty

    let env' = mkEnv env tyConns

        sexp = List $ NAtom nm : (reverse [VAtom i | i <- upto noOfParams])
    return env'{props = M.insert nm sexp (props env')}
    where
        params :: MonadError String m => Term -> m Int
        params (Π _ _ trm) = (+1) <$> params trm
        params (IΠ _ _) = throwError "Implicit parameters not allowed in lifted SMT defintions."
        params (_ :⇒: _) = throwError "Synthesised parameters not allowed in lifted SMT defintions."
        params (_) = return 0

        mkCon ty (nm, nm', tyC) = do
            -- liftIO $ putStrLn $ show tyC
            -- liftIO $ putStrLn $ show $ mkConProp 0 tyC

            tyC' <- mkConAux 0 ty tyC
            case nm' of
                Just nm'' -> return $ SMT.List (SMT.Atom (toS nm'') : tyC')
                Nothing -> return $ SMT.List (SMT.Atom (toS nm) : tyC')

        mkConAux i (Π _ ty trm) (IΠ ty' trmC)
            | ty == ty' = mkConAux (i+1) trm trmC
            | otherwise = throwError "the order of implicit parameters must be the same as the declared type signature when lifting to SMT"
        mkConAux _ StarT (C _) = return []
        mkConAux _ StarT (_ :@: _) = return []
        mkConAux i StarT (Π (Just n) ty tys) = 
            ((SMT.List [SMT.Atom (toS n), mkTy i ty]):) <$> mkConAux (i+1) StarT tys
        mkConAux _ _ _ = throwError "Lifting of this type is not supported"

        mkTy _ PropT = SMT.Atom "Bool"
        mkTy _ NameT = SMT.Atom "String"
        mkTy i (SetT a) = SMT.List [SMT.Atom "Set", mkTy i a]
        mkTy _ IntT = SMT.Atom "Int"
        mkTy i (x :@: args) = SMT.List (mkTy i x:mapApp args)
            where
                mapApp [] = []
                mapApp (I _:xs) = mapApp xs
                mapApp (E x:xs) = mkTy i x:mapApp xs
        mkTy _ (C n) = SMT.Atom $ toS n
        mkTy j (Bound i) = SMT.Atom $ ("t" ++ show (j - i - 1))
        mkTy _ x = error $ show x ++ " unsupported"

        mkTyProp :: Int -> Term -> SExpr Text Int
        mkTyProp _ PropT = NAtom "Bool"
        mkTyProp _ NameT = NAtom "String"
        mkTyProp i (SetT a) = List [NAtom "Set", mkTyProp i a]
        mkTyProp _ IntT = NAtom "Int"
        
        mkTyProp i (x :@: args) = List (mkTyProp i x:mapApp args)
            where
                mapApp [] = []
                mapApp (I _:xs) = mapApp xs
                mapApp (E x:xs) = mkTyProp i x:mapApp xs
        mkTyProp _ (C n) = NAtom $ toS n
        mkTyProp j (Bound i) = VAtom $ j - i - 1
        mkTyProp _ x = error $ show x ++ " unsupported"

        mkConProp :: Int -> Term -> [SExpr Text Int]
        mkConProp i (IΠ _ tys) = mkConProp (i+1) tys
        mkConProp i (Π _ ty tys) = List [NAtom "as", VAtom i, mkTyProp i ty] : mkConProp (i+1) tys 
        mkConProp i x = [mkTyProp i x]

        mkEnv env [] = env
        mkEnv env@Γ{..} ((nm, nm', tyC):tys) = 
            mkEnv env{props = M.insert nm (List [NAtom "as" ,List (NAtom (toS n):tyP), tyTyP]) props} tys            
            where
                (tyP, tyTyP) = (init $ mkConProp 0 tyC, last $ mkConProp 0 tyC)

                n = case nm' of 
                    Just nm'' -> nm''
                    Nothing -> nm
        -- data Term = StarT
        --   | PropT
        --   | NameT
        --   | MkName Text
        --   | SetT Term
        --   | MkSet Term [Term]
        --   | IntT
        --   | MkInt Int
        --   -- | RealT
        --   -- | MkReal Int
        --   | Π (Maybe Text) Term Term
        --   | IΠ Term Term
        --   | Term :⇒: Term
        --   | Bound Int
        --   | Free Name
        --   | Term :@: [ExplImpl Term]
        --   deriving (Ord, Data, Generic, ToJSON)


defineDecl :: (MonadIO m, MonadError String m) => Bool -> Γ -> Decl -> m Γ 
defineDecl ignoreCodom env@Γ{..} (Data opt n t xs) = do
    case M.lookup (Global n) types of
        Just _ -> throwError $ "constant " ++ toS n ++ " already defined"
        Nothing -> do
            t' <- evalTypeOf0 env t VStarT
            let τ = eval t' []
            if ignoreCodom then pure () else unless (codom t == StarT) $ throwError $ toS n ++ " data declaration should have type ... -> */Prop"
            (Γ tys' _ _ _ _ _ _ _ _ _) <- defineTyCon env{types = M.insert (Global n) τ types} n xs
            
            env' <- if opt == LiftToSMT then do
                liftToSMT env n t xs
            else pure env



            return $ env'{
                types = M.insert (Global n) τ $ tys' `M.union` types, 
                constrs = M.insert (Global n) (S.fromList $ map (\(n,_,_) -> Global n) xs) constrs }

defineDecl ignoreCodom env@Γ{..} (PropDef n t sexp) = do
    case M.lookup (Global n) types of
        Just _ -> throwError $ "constant " ++ toS n ++ " already defined"
        Nothing -> do
            t' <- evalTypeOf0 env t VStarT
            let τ = eval t' []
            -- if ignoreCodom then pure () else unless (codom t == Prop) $ throwError $ toS n ++ " data declaration should have type ... -> */Prop"
            return $ env{types = M.insert (Global n) τ $ types, props = M.insert n sexp props}
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

defineDecl _ env@Γ{..} (Def n Nothing trm) = do
    case (M.lookup (Global n) types, M.lookup (Global n) defs) of
        (Just _, Just _) -> throwError $ "constant " ++ toS n ++ " already defined"
        (Just _, Nothing) -> throwError $ "constant " ++ toS n ++ " already defined"
        (Nothing, Just _) -> throwError $ "constant " ++ toS n ++ " already defined"
        (Nothing, Nothing) -> do
            (t', τ) <- runElabType0' False env trm
            liftIO $ putStrLn $ "\n\n-------------------------------------------\n" ++
                                "Successfully elaborated\n" ++ show t' ++ " : " ++ show τ ++
                                "\n-------------------------------------------\n\n"
            return $ env{defs = M.insert (Global n) (t', τ) defs}
defineDecl _ env@Γ{..} (Def n (Just ty) trm) = do
    case (M.lookup (Global n) types, M.lookup (Global n) defs) of
        (Just _, Just _) -> throwError $ "constant " ++ toS n ++ " already defined"
        (Just _, Nothing) -> throwError $ "constant " ++ toS n ++ " already defined"
        (Nothing, Just _) -> throwError $ "constant " ++ toS n ++ " already defined"
        (Nothing, Nothing) -> do
            (ty',_) <- runElabType0' True env ty
            pure ()  `debug` ("\nran elabType0 on ty and got: " ++ show ty')
            trm' <- evalTypeOf0 env trm (eval ty' [])
            pure () `debug` ("\nran evalTypeOf0 on trm and got: " ++ show trm')
 
            -- if the elab term is a hole, we dont want to try to elab its type again...
            ty'' <- case trm' of
                (H _) -> pure $ eval ty' []
                _ -> do

                    -- this is complete hackery... use case is:
                    -- def test2 : Trm _ where
                    --     test2 = var 'y
                    -- end
                    -- here we first elaborate the type, namely Trm _ becomes Trm M0
                    -- then we type-check the body (var 'y) against Trm M0 getting the elaborated (var {{|'y|}} 'y)
                    -- finally we ask for the full type of var {{|'y|}} 'y
                    -- not sure this actually does anything...

                    (_, ty''') <- runElabType0' False env trm'
                    return ty'''


            -- (ConstrList cs) <- getConstrList -- `debug` "stopped SMT in typeOf0"
            -- σ <- unifyConstraints cs [] False M.empty
            -- let trm'' = substMetas σ trm'
            --     ty'' = substMetas σ ty'

            liftIO $ putStrLn $ "\n\n-------------------------------------------\n" ++
                                "Successfully elaborated\n" ++ show trm' ++ " : " ++ show ty'' ++
                                "\n-------------------------------------------\n\n"
            return $ env{defs = M.insert (Global n) (trm', ty'') defs}



defineSMTOpt env@Γ{..} (SMTCmd sexp) = return env{smtOpts = toSMTSExp sexp : smtOpts}
    where
        toSMTSExp :: SExpr Text Text -> SMT.SExpr
        toSMTSExp (NAtom x) = SMT.Atom (toS x)
        toSMTSExp (VAtom x) = SMT.Atom (toS x)
        toSMTSExp (List xs) = SMT.List $ map toSMTSExp xs
defineSMTOpt env@Γ{..} (SMTLogLevel i) = return env{smtLogLevel = i}
defineSMTOpt env@Γ{..} (SMTLogEnabled b) = return env{smtLogEnabled = b}


defineTranslation :: MonadError String m => Γ -> Text -> [(Term, Maybe Term, Text)] -> m Γ
defineTranslation env _ [] = return env
defineTranslation env@Γ{..} l ((x@(C n :@: args),typ,str):xs) =
    case M.lookup (Global n) types of
        Just trmTy -> do
            unless (checkPattern (quote0 trmTy) args) $ throwError $ "The pattern " ++ show x ++ " is malformed."
            argsT <- case typ of
                Just (C nT :@: argsT) -> do
                    case M.lookup (Global n) types of
                        Just tyTy -> unless (checkPattern (quote0 tyTy) argsT) $ throwError $ "The pattern " ++ show x ++ " is malformed."
                        Nothing -> throwError $ "The type " ++ show nT ++ " is not defined."
                    return $ Just argsT
                Just p -> throwError $ "The term " ++ show p ++ " is not a valid pattern."
                Nothing -> return Nothing
            defineTranslation env{translations = M.insert (l, Global n) (args, argsT, (T.replace "\\n" "\n" str)) translations} l xs
        Nothing -> throwError $ "The constructor " ++ show n ++ " is not defined."
defineTranslation env@Γ{..} l ((x@(C n),typ,str):xs) =
    case M.lookup (Global n) types of
        Just trmTy -> do
            unless (checkPattern (quote0 trmTy) []) $ throwError $ "The pattern " ++ show x ++ " is malformed."
            argsT <- case typ of
                Just (C nT :@: argsT) -> do
                    case M.lookup (Global n) types of
                        Just tyTy -> unless (checkPattern (quote0 tyTy) argsT) $ throwError $ "The pattern " ++ show x ++ " is malformed."
                        Nothing -> throwError $ "The type " ++ show nT ++ " is not defined."
                    return $ Just argsT
                Just p -> throwError $ "The term " ++ show p ++ " is not a valid pattern."
                Nothing -> return Nothing
            defineTranslation env{translations = M.insert (l, Global n) ([], argsT, (T.replace "\\n" "\n" str)) translations} l xs
        Nothing -> throwError $ "The constructor " ++ show n ++ " is not defined."
defineTranslation env@Γ{..} l (p:xs) = throwError $ "The term " ++ show p ++ " is not a valid pattern."


defineTyCon :: (MonadIO m, MonadError String m) =>  Γ -> Text -> [(Text, Maybe Text, Term)] -> m Γ 
defineTyCon env@Γ{..} _ [] = return $ env{types = M.empty}
defineTyCon env@Γ{..} n ((c, _, t):xs) = do
    (Γ tys' _ _ _ _ _ _ _ _ _) <- defineTyCon env n xs
    case M.lookup (Global c) (types `M.union` tys') of
        Just _ -> throwError $ "constant " ++ toS c ++ " already defined"
        Nothing -> do
            case codom t of
                (C c') -> unless (c' == n) $ throwError $ "The constructor for type " ++ toS n ++ ", must be of the shape ... -> " ++ toS n ++ "\n instead found: " ++ show (codom t)
                (C c' :@: _) -> unless (c' == n) $ throwError $ "The constructor for type " ++ toS n ++ " ... , must be of the shape ... -> " ++ toS n ++ " ...\n instead found: " ++ show (codom t)
                _ -> throwError $ "constructor " ++ show c ++ " : " ++ show t ++ " of incorrect shape"
            -- (t', τ) <- evalElabType0 g t
            t' <- evalTypeOf0 env t VStarT
            -- strictPositivityCheck True n t
            return $ env{types = M.insert (Global c) (eval t' []) tys'} -- `debug` ("have " ++ show t ++ " found " ++ show t') 


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
translate _ l trm ty | l == "JSON" = return $ toS $ encode (trm, ty)
translate _ _ (MkName n) NameT = return n
translate env l (MkSet ty xs) (SetT _) = do
    xs' <- mapM (\t -> translate env l t ty) xs
    return $ "{" <> T.intercalate "," xs' <> "}"
translate _ _ trm (Π _ _ _) = return $ toS $ show trm
translate _ _ trm (IΠ _ _) = return $ toS $ show trm
translate _ _ trm (_ :⇒: _) = return $ toS $ show trm
translate env@Γ{..} l trm ty = do
    (n, args, nTy, argsTy) <- case (trm, ty) of
        (C n, C nTy) -> return (n, [], nTy, [])
        (C n, C nTy :@: argsTy) -> return (n, [], nTy, argsTy)
        (C n :@: args, C nTy) -> return (n, args, nTy, [])
        (C n :@: args, C nTy :@: argsTy) -> return (n, args, nTy, argsTy)
        _ -> throwError $ "Expected app in " ++ show (trm, ty)
    case M.lookup (l, (Global n)) translations of
        Just (trmPat, Just tyPat, str) -> do
            args' <- translateExpImpApp env l args
            argsTy' <- translateExpImpApp env l argsTy
            let mapTrm = unify trmPat args' 
                -- sortBy (\(a,_) (b,_) -> compare (T.length b) (T.length a)) $ unify trmPat args' 
            let mapTy = unify tyPat argsTy' 
            return $ foldr (\(pn, trm) s -> T.replace ("#{" <> pn <> "}") trm s) str $ mapTrm ++ mapTy
        Just (trmPat, nothing, str) -> do
            args' <- translateExpImpApp env l args
            let mapTrm = unify trmPat args' 
            return $ foldr (\(pn, trm) s -> T.replace ("#{" <> pn <> "}") trm s) str $ mapTrm
        Nothing -> do
            -- args' <- translateExpImpApp env l args
            return $ toS $ show trm

    where
        translateExpImpApp :: (MonadIO m, MonadError String m) => 
            Γ -> Text -> [ExplImpl Term] -> m [ExplImpl Text]
        translateExpImpApp _ _ [] = return []
        translateExpImpApp env l (E t:xs) = do
            (_, ty) <- runElabType0' False env t `debug` ("Elab: " ++ show t)
            t' <- translate env l t (quote0 ty)
            xs' <- translateExpImpApp env l xs
            return $ E t':xs'
        translateExpImpApp env l (I t:xs) = do
            (_, ty) <- runElabType0' False env t `debug` ("Elab: " ++ show t)
            t' <- translate env l t (quote0 ty)
            xs' <- translateExpImpApp env l xs
            return $ I t':xs'

unify [] [] = []
unify (I _:xs) [] = unify xs []
unify [] (I _:xs) = unify [] xs
unify (I (C pn):ps) (I trm:ts) = (pn, trm): unify ps ts
unify (E (C pn):ps) (E trm:ts) = (pn, trm): unify ps ts
unify (I _:ps) ts@(E _:_) = unify ps ts
unify ps@(E _:_) (I _:ts) = unify ps ts



