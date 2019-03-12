{-# LANGUAGE OverloadedStrings, DeriveDataTypeable, FlexibleContexts, 
PatternSynonyms, DeriveFunctor, ScopedTypeVariables, TypeApplications #-}


module LamPi where

import Data.Text(Text)
import qualified Data.Text as T
import Control.Monad(unless)
import Data.String.Conv(toS)

import Data.Data(Data)
import Data.Has

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative

import Data.Map(Map)
import qualified Data.Map as M

import Data.Set(Set)

import qualified Data.Set as S

import Debug.Trace(trace)
import Data.List(intercalate)

import qualified SimpleSMT
-- import SMT
infixl 7 :@:

debugMode = False

showImpl = False

debug = if debugMode then flip trace else (\a _ -> a)

data ExplImpl a = I a | E a deriving (Show, Eq, Ord, Data, Functor)

data Name = Global Text
          | Local Int
          | Quote Int
          | Meta Int
          | InferMeta
          | UserHole Int
          deriving (Eq, Ord, Data)

instance Show Name where
    show (Global t) = toS t 
    show (Local i) = "L" ++ show i
    show (Quote i) = "Q" ++ show i
    show (Meta i) = "M" ++ show i
    show (UserHole i) = "?" ++ show i
    show InferMeta = "_"

data Term = Star
          | Prop
          | Name
          | MkName Text
          | Set Term
          | MkSet Term [Term]
          | Π Term Term
          | IΠ Term Term
          | Term :⇒: Term
          | Bound Int
          | Free Name
          | Term :@: [ExplImpl Term]
          deriving (Ord, Data)

instance Eq Term where
    Star == Star = True
    Prop == Prop = True
    Name == Name = True
    MkName x == MkName y = x == y
    Set x == Set y = x == y
    MkSet a x == MkSet b y = a == b && S.fromList x == S.fromList y
    Π a b == Π c d = a == c && b == d
    IΠ a b == IΠ c d = a == c && b == d
    a :⇒: b == c :⇒: d = a == c && b == d
    Bound x == Bound y = x == y
    Free x == Free y = x == y
    x :@: xs == y :@: ys = x == y && xs == ys
    _ == _ = False




instance Show Term where
    show Star = "*"
    show Prop = "Prop"
    show Name = "Name"
    show (MkName s) = "\'" ++ toS s
    show (Set a) = "Set " ++ show a
    show (MkSet _ s) = "⦃" ++ (intercalate "," (S.toList (S.fromList (map show s)))) ++ "⦄"
    show (Π t t') = "Π " ++ show t ++ " . " ++ show t'
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

data Value = VStar
           | VProp
           | VName
           | VMkName Text
           | VSet Value
           | VMkSet Value [Value]
           | VΠ Value (Value -> Value)
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
newtype Γ = Γ { unΓ :: [(Name, Type)] } deriving Show


type Env = [Value]


vfree :: Name -> Value
vfree n = VNeutral (NFree n)


vapp :: Value -> [ExplImpl Value] -> Value 
-- vapp (VLam f) v =f v
vapp (VΠ n f) [E v] = f v
vapp (VIΠ n f) [I v] = f v
vapp (VNeutral n) vs = VNeutral (NApp n vs)


eval :: Term -> Env -> Value
eval Star d = VStar
eval Prop d = VProp
eval Name d = VName
eval (MkName s) d = VMkName s
eval (Set a) d = VSet (eval a d)
eval (MkSet a s) d = VMkSet (eval a d) (map (flip eval d) s)
eval (Π τ τ') d = VΠ (eval τ d) (\x -> eval τ' (x:d))
eval (IΠ τ τ') d = VIΠ (eval τ d) (\x -> eval τ' (x:d))
eval (τ :⇒: τ') d = VSArr (eval τ d) (eval τ' d)
eval (Free x) d = vfree x
eval (Bound i) d = d !! i
eval (e :@: es) d = vapp (eval e d) (fmap (fmap (flip eval d)) es)

subst :: Int -> Term -> Term -> Term
subst i r (Π τ τ') = Π (subst i r τ) (subst (i+1) r τ')
subst i r (IΠ τ τ') = IΠ (subst i r τ) (subst (i+1) r τ')
subst i r (τ :⇒: τ') = (subst i r τ) :⇒: (subst i r τ')
subst i r (Bound j) = if i == j then r else Bound j 
subst i r (e :@: es) = subst i r e :@: (fmap (fmap (subst i r)) es)
subst i r (Set a) = Set (subst i r a)
subst i r (MkSet a s) = MkSet (subst i r a) (map (subst i r) s)
subst i r x = x


bind :: Int -> Int -> Term -> Term
bind i r (Π τ τ') = Π (bind i r τ) (bind (i+1) r τ')
bind i r (IΠ τ τ') = IΠ (bind i r τ) (bind (i+1) r τ')
bind i r (τ :⇒: τ') = (bind i r τ) :⇒: (bind i r τ')
bind i r e@(Free (Local j)) = if r == j then Bound i else e
bind i r (e :@: es) = bind i r e :@: (fmap (fmap (bind i r)) es)
bind i r (Set a) = Set (bind i r a)
bind i r (MkSet a s) = MkSet (bind i r a) (map (bind i r) s)
bind i r x = x


substMeta :: Int -> Term -> Term -> Term
substMeta i r (Π τ τ') = Π (substMeta i r τ) (substMeta i r τ')
substMeta i r (IΠ τ τ') = IΠ (substMeta i r τ) (substMeta i r τ')
substMeta i r (Bound j) = Bound j 
substMeta i r (Free (Meta j)) = if i == j then r else Free (Meta j)
substMeta i r (e :@: es) = substMeta i r e :@: (fmap (fmap (substMeta i r)) es)
substMeta i r (Set a) = Set (substMeta i r a)
substMeta i r (MkSet a s) = MkSet (substMeta i r a) (map (substMeta i r) s)
substMeta i r x = x



quote0 :: Value -> Term 
quote0 = quote 0

quote :: Int -> Value -> Term
quote i VStar = Star
quote i VProp = Prop
quote i VName = Name
quote i (VMkName s) = MkName s
quote i (VSet a) = Set (quote i a)
quote i (VMkSet a s) = MkSet (quote i a) (map (quote i) s)

quote i (VΠ v f) = Π (quote i v) (quote (i + 1) (f (vfree (Quote i))))
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
addToΓ n τ = modify (\s -> modifier (\(Γ g) -> Γ $ (n, τ):g) s)

lookupInΓ :: (Has Γ s, MonadState s m , MonadError String m) => Name -> m Type
lookupInΓ n = do
    s <- get
    case lookup n (unΓ $ getter s) of
        Just τ -> return τ
        Nothing -> throwError ("unknown identifier: " ++ show n)

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
elabType Star = return (Star, VStar)
elabType Prop = return (Prop, VStar)
elabType Name = return (Name, VStar)
elabType (MkName s) = return (MkName s, VName)

elabType (Set α) = do
    α' <- typeOf α VStar
    return (Set α', VStar)
elabType (MkSet α []) = do
    let α' = eval α []
    return $ (MkSet α [], VSet α')
elabType (MkSet α xs) = do
    let α' = eval α [ ]
    xs' <- mapM (flip typeOf α') xs
    return (MkSet α xs', VSet α')
elabType (Π ρ ρ') = do
    τ <- typeOf ρ VStar
    i <- getFreshAndIncrementBV
    addToΓ (Local i) $ eval ρ []
    

    -- using this to only define bound vars that have a SAT representation
    case toSExprMaybe ρ of
        Just ty -> do
            (SMTSolver proc) <- getHas `debug` ("found bound " ++ show i ++ " : " ++ show ρ)
            liftIO $ SimpleSMT.declare proc ("L" ++ show i) ty
            return ()
        Nothing -> return ()

    τ' <- typeOf (subst 0 (Free (Local i)) ρ') VStar
    (ConstrList cs) <- getConstrList
    σ <- unifyConstraints cs [] False M.empty -- `debug` ("\n\ncs1 (elabType Π): " ++ show cs)
    let τ'' = substMetas σ τ'
    checkDoesNotContainMetas "here??" τ''

    return (Π τ (bind 0 i τ''), VStar) -- `debug` ("i after: " ++ show i') -- 
        -- `debug` ("\n\ngot: " ++ show (Π ρ ρ') ++ " with fresh L" ++ show i ++ ", after subst: " ++ show (subst 0 (Free (Local i)) ρ') ++ " returning: " ++ show (Π τ (bind 0 i τ')))
elabType (IΠ ρ ρ') = do
    (Π τ τ', τ'') <- elabType (Π ρ ρ')
    return (IΠ τ τ', τ'')
elabType (x :⇒: y) = do
    x' <- typeOf x VProp 
    y' <- typeOf y VStar 
    (ConstrList cs) <- getConstrList
    σ <- unifyConstraints cs [] False M.empty -- `debug` ("\n\nconstraints: " ++ show cs)
    let x'' = substMetas σ x'
    let y'' = substMetas σ y'
    checkDoesNotContainMetas "here1" y'' `debug` ("\n\n:⇒: " ++ show x')
    return (x :⇒: y'', VStar)
elabType (H n) = do
    -- mi <- getFreshAndIncrementMeta
    -- let mvar = Free (Meta mi)
    -- addToΓ (Meta mi) τ
    return (H n, eval (H n) [])
elabType InferM = do
    mi <- getFreshAndIncrementMeta
    let mvar = Free (Meta mi)

    mj <- getFreshAndIncrementMeta
    let mvarTy = eval (Free (Meta mj)) [] `debug` ("added " ++ show mi ++ "," ++ show mj)
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
    (VΠ _ _) -> throwError $ "illegal application at " <> (toS $ show ty)
    (VSArr cnstr τ') -> do
        cnstr' <- typeOf (quote0 cnstr) VProp
        (ConstrList cs) <- getConstrList
        let cnstr'' = substMetas (mkMap cs) cnstr'
        addToSATConstrList $ SATConstrList [cnstr''] `debug` ("\n\nConstrList is: "++ show cs)
        elabTypeApp τ' [] `debug` ("\n\nconstraint is: "++ show cnstr'')
    _ -> return ([], ty)
elabTypeApp ty (x:xs) = case (x,ty) of
    (E x', VΠ τ τ') -> do
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
        cnstr' <- typeOf (quote0 cnstr) VProp
        (ConstrList cs) <- getConstrList
        let cnstr'' = substMetas (mkMap cs) cnstr'
        addToSATConstrList $ SATConstrList [cnstr'']
        elabTypeApp τ' (x:xs) `debug` ("\n\nconstraint is: "++ show cnstr'')
    _ -> throwError $ "illegal application at " <> (toS $ show x) <> " : " <> (toS $ show ty)



typeOf :: (Has BVCounter s, Has MetaCounter s, Has Γ s, Has ConstrList s, Has SATConstrList s,
    MonadState s m , Has SMTSolver s, MonadIO m, MonadError String m) => 
    Term -> Type -> m Term
typeOf e τ = do
    cs <- getConstrList -- `debug` ("calling tyOf on " ++ show e ++ " : " ++ show τ)
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
            return e' -- `debug` ("\n\nadding : " ++ show e ++ " .... " ++ (show $ unifyType (unConstrList cs) (quote0 τ) (quote0 τ')))

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
unifyType (Set x) (Set y) = unifyType x y

unifyType (H n) x = [(H n, x)]
unifyType x (H n) = [(H n, x)]
unifyType InferM InferM = error $ "\n\nfailed on : " ++ show InferM ++ " and " ++ show InferM ++ "\n\n"

unifyType x InferM = []
unifyType InferM x = []
unifyType τ τ' = error $ "\n\nfailed to unify on : " ++ show τ ++ " and " ++ show τ' ++ "\n\n"


unifyConstraints :: MonadError String m => [(Term,Term)] -> [(Term,Term)] -> Bool -> Map Int Term -> m (Map Int Term)
unifyConstraints []                                  []  _     m = return m
unifyConstraints []                                  acc False m = 
    throwError $ "cannot unify rest (acc): " ++ show acc ++ "; m contains: " ++ show m
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
    | doesNotContainMetas y = unifyConstraints xs acc True $ M.insert x y m
    | otherwise = unifyConstraints xs ((M x, y):acc) flag m 
unifyConstraints ((x, M y):xs)                       acc flag  m = unifyConstraints ((M y,x):xs) acc flag m
unifyConstraints ((Star, Star):xs)                   acc flag  m = unifyConstraints xs acc flag m
unifyConstraints ((Name, Name):xs)                   acc flag  m = unifyConstraints xs acc flag m
unifyConstraints ((MkName x, MkName y):xs)           acc flag  m | x == y = unifyConstraints xs acc flag m
unifyConstraints ((Set x, Set y):xs)                 acc flag  m = unifyConstraints ((x,y):xs) acc flag m
unifyConstraints ((x@(MkSet _ _), y@(MkSet _ _)):xs) acc flag  m | x == y = unifyConstraints xs acc flag m

unifyConstraints ((Π σ σ', Π τ τ'):xs)               acc flag  m = throwError "not sure how to unify yet"
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


doesNotContainMetas :: Term -> Bool
doesNotContainMetas (M _) = False
doesNotContainMetas (Π τ τ') = doesNotContainMetas τ && doesNotContainMetas τ'
doesNotContainMetas (IΠ τ τ') = doesNotContainMetas (Π τ τ')
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

newtype SMTSolver = SMTSolver { unSMTSolver :: SimpleSMT.Solver }

getHas :: (Has a s, MonadState s m) => m a
getHas = getter <$> get


addToSATDefs :: (Has SATDefs s, MonadState s m) => Int -> m ()
addToSATDefs i = modify (\s -> modifier (\(SATDefs ys) -> SATDefs $ S.insert i ys) s)


-- using this to only define bound vars that have a SAT representation
toSExprMaybe :: Term -> Maybe SimpleSMT.SExpr
toSExprMaybe Prop = pure $ SimpleSMT.tBool
toSExprMaybe Name = pure $ SimpleSMT.const "String"
toSExprMaybe (MkName s) = pure $ SimpleSMT.const $ "\"" ++ toS s ++ "\""
toSExprMaybe (Set a) = (\x -> SimpleSMT.fun "Set" [x]) <$> toSExprMaybe a
toSExprMaybe (MkSet a []) = 
    (\x -> SimpleSMT.fun "as" [SimpleSMT.const "emptyset", x]) <$> toSExprMaybe (Set a)
toSExprMaybe (MkSet _ [x]) = do
    x' <- toSExprMaybe x
    return $ SimpleSMT.fun "singleton" [x']
toSExprMaybe (MkSet _ (x:xs)) = do
    x' <- toSExprMaybe x
    xs' <- mapM toSExprMaybe xs
    return $ SimpleSMT.fun "insert" $ xs' ++ [SimpleSMT.fun "singleton" [x']]
toSExprMaybe (M x) = pure $ SimpleSMT.const $ "M" ++ show x
-- toSExprMaybe (L i) = pure $ SimpleSMT.const $ "L"++ show i
-- toSExprMaybe (C "¬" :@: [E x]) = SimpleSMT.not <$> toSExprMaybe x
-- toSExprMaybe (C "&&" :@: [E x, E y]) = SimpleSMT.and <$> toSExprMaybe x <*> toSExprMaybe y
-- toSExprMaybe (C "∈" :@: [_, E x, E s]) = (\a b -> SimpleSMT.fun "member" [a,b]) <$> toSExprMaybe x <*> toSExprMaybe s
-- toSExprMaybe (C "∉" :@: [_, E x, E s]) = (\a b -> SimpleSMT.not $ SimpleSMT.fun "member" [a,b]) <$> toSExprMaybe x <*> toSExprMaybe s
-- toSExprMaybe (C "\\\\" :@: [_, E s, E x]) = (\a b -> SimpleSMT.fun "setminus" [a, SimpleSMT.fun "singleton" [b]]) <$> toSExprMaybe s <*> toSExprMaybe x
-- toSExprMaybe (C "≡" :@: [_, E x, E y]) = SimpleSMT.eq <$> toSExprMaybe x <*> toSExprMaybe y
-- toSExprMaybe (C "∪" :@: [_, E x, E y]) = (\a b -> SimpleSMT.fun "union" [a,b]) <$> toSExprMaybe x <*> toSExprMaybe y
-- toSExprMaybe (C "∩" :@: [_, E x, E y]) = (\a b -> SimpleSMT.fun "intersection" [a,b]) <$> toSExprMaybe x <*> toSExprMaybe y
-- toSExprMaybe (C "\\" :@: [_, E x, E y]) = (\a b -> SimpleSMT.fun "setminus" [a,b]) <$> toSExprMaybe x <*> toSExprMaybe y
-- toSExprMaybe (C "singleton" :@: [_, E x]) = (\a -> SimpleSMT.fun "singleton" [a]) <$> toSExprMaybe x
-- toSExprMaybe (C "infer" :@: [_, E x]) = SimpleSMT.eq <$> toSExprMaybe x <*> toSExprMaybe x -- vacuous, but forces x to be declared, if it is a meta var
toSExprMaybe _ = Nothing


-- TODO replace this with toSExprMaybe + a suitable error message??

toSExpr :: Term -> SimpleSMT.SExpr
toSExpr Prop = SimpleSMT.tBool
toSExpr Name = SimpleSMT.const "String"
toSExpr (MkName s) = SimpleSMT.const $ "\"" ++ toS s ++ "\""
toSExpr (Set a) = SimpleSMT.fun "Set" [toSExpr a]
toSExpr (MkSet a []) = 
    SimpleSMT.fun "as" [SimpleSMT.const "emptyset", toSExpr (Set a)]
toSExpr (MkSet _ [x]) = SimpleSMT.fun "singleton" [toSExpr x]
toSExpr (MkSet _ (x:xs)) = 
    SimpleSMT.fun "insert" $ map toSExpr xs ++ [SimpleSMT.fun "singleton" [toSExpr x]]
toSExpr (M x) = SimpleSMT.const $ "M" ++ show x
toSExpr (C "¬" :@: [E x]) = SimpleSMT.not $ toSExpr x
toSExpr (C "&&" :@: [E x, E y]) = SimpleSMT.and (toSExpr x) (toSExpr y)
toSExpr (C "∈" :@: [_, E x, E s]) = SimpleSMT.fun "member" [toSExpr x, toSExpr s]
toSExpr (C "∉" :@: [_, E x, E s]) = SimpleSMT.not $ SimpleSMT.fun "member" [toSExpr x, toSExpr s]
toSExpr (C "\\\\" :@: [_, E s, E x]) = SimpleSMT.fun "setminus" [toSExpr s, SimpleSMT.fun "singleton" [toSExpr x]]
toSExpr (C "≡" :@: [_, E x, E y]) = SimpleSMT.eq (toSExpr x) (toSExpr y)
toSExpr (C "∪" :@: [_, E x, E y]) = SimpleSMT.fun "union" [toSExpr x, toSExpr y]
toSExpr (C "∩" :@: [_, E x, E y]) = SimpleSMT.fun "intersection" [toSExpr x, toSExpr y]
toSExpr (C "\\" :@: [_, E x, E y]) = SimpleSMT.fun "setminus" [toSExpr x, toSExpr y]
toSExpr (C "singleton" :@: [_, E x]) = SimpleSMT.fun "singleton" [toSExpr x]
toSExpr (C "infer" :@: [_, E x]) = SimpleSMT.eq (toSExpr x) (toSExpr x) -- vacuous, but forces x to be declared, if it is a meta var
toSExpr (L i) = SimpleSMT.const $ "L"++ show i

toSExpr e = error $ "unsupported operation " ++ show e

 

fromSExpr :: SimpleSMT.SExpr -> Type -> Term
fromSExpr (SimpleSMT.Atom xs) VName = MkName $ toS $ filter (/= '"') xs
fromSExpr (SimpleSMT.List [SimpleSMT.Atom "as",SimpleSMT.Atom "emptyset",_]) (VSet a) = MkSet (quote0 a) []
fromSExpr (SimpleSMT.List [SimpleSMT.Atom "singleton",n])          (VSet a) = MkSet (quote0 a) [fromSExpr n a]
fromSExpr (SimpleSMT.List [SimpleSMT.Atom "union", xs, ys])        (VSet a) = 
    let (MkSet a' xs') = fromSExpr xs (VSet a)
        (MkSet _ ys') = fromSExpr ys (VSet a) in
        MkSet a' $ xs' ++ ys'


-- toSExpr (Set a) = SimpleSMT.fun "Set" [toSExpr a]
-- toSExpr (MkSet a []) = 
--     SimpleSMT.fun "as" [SimpleSMT.const "emptyset", toSExpr (Set a)]
-- toSExpr (MkSet _ (x:xs)) = 
--     SimpleSMT.fun "insert" $ map toSExpr xs ++ [SimpleSMT.fun "singleton" [toSExpr x]]
-- toSExpr (M x) = SimpleSMT.const $ "M" ++ show x
-- toSExpr (C "∈" :@: [_, E x, E s]) = SimpleSMT.fun "member" [toSExpr x, toSExpr s]
-- toSExpr (C "\\\\" :@: [_, E s, E x]) = SimpleSMT.fun "setminus" [toSExpr s, SimpleSMT.fun "singleton" [toSExpr x]]
-- toSExpr (C "≡" :@: [_, E x, E y]) = SimpleSMT.eq (toSExpr x) (toSExpr y)
-- toSExpr _ = error "unsupported operation"



defineMetas :: (MonadIO m, Has SMTSolver s, Has Γ s, Has SATDefs s, MonadState s m, MonadError String m) => 
    Term -> m ()
defineMetas (M n) = do
    (SATDefs defined) <- getHas
    if not (n `S.member` defined) then do
        τ <- lookupInΓ (Meta n)
        (SMTSolver proc) <- getHas `debug` ("found meta " ++ show n ++ " : " ++ show τ)
        liftIO $ SimpleSMT.declare proc ("M" ++ show n) (toSExpr $ quote0 τ)
        addToSATDefs n
    else pure ()
defineMetas (e :@: es) = mapM_ (\x -> case x of
    E y -> defineMetas y
    I y -> defineMetas y) es
defineMetas _ = return ()



elabType0 ::  (Has BVCounter s, Has MetaCounter s, Has Γ s, Has ConstrList s, Has SATConstrList s, Has SATDefs s,
    MonadState s m , Has SMTSolver s, MonadIO m, MonadError String m) => Bool -> 
    Term -> m (Term, Type)
elabType0 canContainMetas t = do 
    (trm,typ) <- elabType t
    (ConstrList cs) <- getConstrList

    -- get collected sat constraints and replace all equal metas, collected in ConstrList
    (SATConstrList satcs) <- getSATConstrList
    let satcs' = map (substMetas $ mkMap cs) satcs

    -- translate to sat, first defining all meta variables
    mapM_ defineMetas satcs'
    (SMTSolver proc) <- getHas
    mapM_ (\s -> liftIO $ SimpleSMT.assert proc $ toSExpr s) satcs'
    -- check sat

    r <- liftIO $ SimpleSMT.check proc

    case r of
        SimpleSMT.Sat -> do
            (SATDefs defined) <- getHas
            forM_ (S.toList defined) (\d -> do
                (SimpleSMT.Other v) <- liftIO $ SimpleSMT.getExpr proc (SimpleSMT.const $ "M" ++ show d)
                τ <- lookupInΓ (Meta d) `debug` ("\n\nSMT returned: " ++ show v)
                let vt = fromSExpr v τ 
                addToConstrList $ ConstrList [(M d,vt)] `debug` ("\n\nadding const: " ++ show (M d,vt)))
        _ -> throwError $ "collected constraints: " ++ show satcs' ++ " are not satisfiable!"
    -- get model and add to cs

    -- liftIO $ SimpleSMT.stop proc
    (ConstrList cs') <- getConstrList -- `debug` "stopped SMT"
    σ <- unifyConstraints cs' [] False M.empty `debug` ("\n\nelabType0 constraints: " ++ show cs' ++ "\nmkMap cs = " ++ show (mkMap cs) ++ "\n sat constraints: " ++ show satcs' )
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
    (ConstrList cs) <- getConstrList

    -- get collected sat constraints and replace all equal metas, collected in ConstrList
    (SATConstrList satcs) <- getSATConstrList
    let satcs' = map (substMetas $ mkMap cs) satcs

    -- translate to sat, first defining all meta variables
    mapM_ defineMetas satcs'
    (SMTSolver proc) <- getHas
    mapM_ (\s -> liftIO $ SimpleSMT.assert proc $ toSExpr s) satcs'
    -- check sat

    r <- liftIO $ SimpleSMT.check proc

    case r of
        SimpleSMT.Sat -> do
            (SATDefs defined) <- getHas
            forM_ (S.toList defined) (\d -> do
                (SimpleSMT.Other v) <- liftIO $ SimpleSMT.getExpr proc (SimpleSMT.const $ "M" ++ show d)
                τ <- lookupInΓ (Meta d) `debug` ("\n\nSMT returned: " ++ show v)
                let vt = fromSExpr v τ 
                addToConstrList $ ConstrList [(M d,vt)] `debug` ("\n\nadding const: " ++ show (M d,vt)))
        _ -> throwError $ "collected constraints: " ++ show satcs' ++ " are not satisfiable!"
    -- get model and add to cs

    -- liftIO $ SimpleSMT.stop proc
    (ConstrList cs') <- getConstrList -- `debug` "stopped SMT"
    σ <- unifyConstraints cs' [] False M.empty `debug` ("\n\nelabType0 constraints: " ++ show cs' ++ "\nmkMap cs = " ++ show (mkMap cs) ++ "\n sat constraints: " ++ show satcs' )
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
--     log <- SimpleSMT.newLogger 0
--     smt <- SimpleSMT.newSolver "cvc4" ["--incremental", "--lang" , "smt2.0"] (if debugMode then Just log else Nothing)
--     SimpleSMT.setLogic smt "QF_UFSLIAFS" -- "QF_UFLIAFS"

--     res <- runExceptT $ (flip (evalStateT @(ExceptT String IO)) (BVCounter 0,MetaCounter 0,g,ConstrList [],SATConstrList [], SATDefs S.empty, SMTSolver smt)) $ elabType0 canContainMetas t
--     liftIO $ SimpleSMT.stop smt
--     return res

runElabType0' :: (MonadIO m, MonadError String m) => Bool -> Γ -> Term -> m (Term, Type)
runElabType0' canContainMetas g t = do
    log <- liftIO $ SimpleSMT.newLogger 0
    smt <- liftIO $ SimpleSMT.newSolver "cvc4" ["--incremental", "--lang" , "smt2.0"] (if debugMode then Just log else Nothing)
    liftIO $ SimpleSMT.setLogic smt "QF_UFSLIAFS" -- "QF_UFLIAFS"

    res <- (flip evalStateT (BVCounter 0,MetaCounter 0,g,ConstrList [],SATConstrList [], SATDefs S.empty, SMTSolver smt)) $ elabType0 canContainMetas t
    liftIO $ SimpleSMT.stop smt
    return res

runElabType0List :: (MonadIO m, MonadError String m) => Γ -> Term -> Term -> m (Term, Type)
runElabType0List g trm ty = do
    log <- liftIO $ SimpleSMT.newLogger 0
    smt <- liftIO $ SimpleSMT.newSolver "cvc4" ["--incremental", "--lang" , "smt2.0"] (if debugMode then Just log else Nothing)
    liftIO $ SimpleSMT.setLogic smt "QF_UFSLIAFS" -- "QF_UFLIAFS"

    res <- (flip (evalStateT ) (BVCounter 0,MetaCounter 0,g,ConstrList [],SATConstrList [], SATDefs S.empty, SMTSolver smt)) $ elabType0' trm ty
    liftIO $ SimpleSMT.stop smt
    return res




typeOf0 ::  (Has BVCounter s, Has MetaCounter s, Has Γ s, Has ConstrList s, Has SATConstrList s, Has SATDefs s,
    MonadState s m , Has SMTSolver s, MonadError String m, MonadIO m) =>
    Term -> Type -> m Term
typeOf0 t τ = do
    trm <- typeOf t τ
    (ConstrList cs) <- getConstrList

    -- get collected sat constraints and replace all equal metas, collected in ConstrList
    (SATConstrList satcs) <- getSATConstrList
    let satcs' = map (substMetas $ mkMap cs) satcs

    -- translate to sat, first defining all meta variables
    mapM_ defineMetas satcs'
    (SMTSolver proc) <- getHas
    mapM_ (\s -> liftIO $ SimpleSMT.assert proc $ toSExpr s) satcs'
    -- check sat

    r <- liftIO $ SimpleSMT.check proc

    case r of
        SimpleSMT.Sat -> do
            (SATDefs defined) <- getHas
            forM_ (S.toList defined) (\d -> do
                (SimpleSMT.Other v) <- liftIO $ SimpleSMT.getExpr proc (SimpleSMT.const $ "M" ++ show d)
                τ <- lookupInΓ (Meta d) `debug` ("\n\nSMT returned: " ++ show v)
                let vt = fromSExpr v τ 
                addToConstrList $ ConstrList [(M d,vt)] `debug` ("\n\nadding const: " ++ show (M d,vt)))
        _ -> throwError $ "collected constraints: " ++ show satcs' ++ " are not satisfiable!"
    -- get model and add to cs

    -- liftIO $ SimpleSMT.stop proc
    (ConstrList cs') <- getConstrList -- `debug` "stopped SMT in typeOf0"
    σ <- unifyConstraints cs' [] False M.empty --`debug` ("\n\nelabType0 constraints: " ++ show cs' ++ "\nmkMap cs = " ++ show (mkMap cs) ++ "\n sat constraints: " ++ show satcs' )
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
    -- log <- liftIO $ SimpleSMT.newLogger 0
    -- smt <- liftIO $ SimpleSMT.newSolver "cvc4" ["--incremental", "--lang" , "smt2.0"] (if debugMode then Just log else Nothing)
    -- liftIO $ SimpleSMT.setLogic smt "QF_UFSLIAFS" -- "QF_UFLIAFS"

    log <- liftIO $ SimpleSMT.newLogger 0
    smt <- liftIO $ SimpleSMT.newSolver "cvc4" ["--incremental", "--lang" , "smt2.0"] (if debugMode then Just log else Nothing)
    liftIO $ SimpleSMT.setLogic smt "QF_UFSLIAFS" -- "QF_UFLIAFS"

    res <- flip evalStateT (BVCounter 0,MetaCounter 0,g,ConstrList [],SATConstrList [], SATDefs S.empty, SMTSolver smt) $ typeOf0 t τ

    liftIO $ SimpleSMT.stop smt
    return res




data Decl = 
    Data Text Term [(Text, Term)]  
  | Def Text (Maybe Term) Term
    deriving (Show, Eq, Data)

codom :: Term -> Term
codom (Π _ ρ) = codom ρ
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


defineDecl :: (MonadIO m, MonadError String m) => Bool -> Γ -> Decl -> m Γ 
defineDecl ignoreCodom env@(Γ g) (Data n t xs) = do
    case lookup (Global n) g of
        Just _ -> throwError $ "constant " ++ toS n ++ " already defined"
        Nothing -> do
            t' <- evalTypeOf0 env t VStar
            let τ = eval t' []
            if ignoreCodom then pure () else unless (codom t == Star || codom t == Prop) $ throwError $ toS n ++ " data declaration should have type ... -> */Prop"
            (Γ g') <- defineTyCon (Γ $ (Global n,τ):g) n xs
            return $ Γ $ g' ++ ((Global n,τ):g)

defineDecl _ env@(Γ g) (Def n Nothing trm) = do
    case lookup (Global n) g of
        Just _ -> throwError $ "constant " ++ toS n ++ " already defined"
        Nothing -> do
            (t', τ) <- runElabType0' False env trm
            liftIO $ putStrLn $ "-------------------------------------------\n" ++
                                "Successfully elaborated\n" ++ show t' ++ " : " ++ show τ ++
                                "\n-------------------------------------------"
            return $ env
defineDecl _ env@(Γ g) (Def n (Just ty) trm) = do
    case lookup (Global n) g of
        Just _ -> throwError $ "constant " ++ toS n ++ " already defined"
        Nothing -> do
            (ty',_) <- runElabType0' True env ty

            trm' <- evalTypeOf0 env trm (eval ty' []) `debug` ("\nran elabType0 on ty and got: " ++ show ty')
            
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

            liftIO $ putStrLn $ "-------------------------------------------\n" ++
                                "Successfully elaborated\n" ++ show trm' ++ " : " ++ show ty'' ++
                                "\n-------------------------------------------"
            return $ env


defineTyCon :: (MonadIO m, MonadError String m) =>  Γ -> Text -> [(Text, Term)] -> m Γ 
defineTyCon _ _ [] = return $ Γ []
defineTyCon env@(Γ g) n ((c, t):xs) = do
    (Γ g') <- defineTyCon env n xs
    case lookup (Global c) (g ++ g') of
        Just _ -> throwError $ "constant " ++ toS c ++ " already defined"
        Nothing -> do
            case codom t of
                (C c') -> unless (c' == n) $ throwError $ "The constructor for type " ++ toS n ++ ", must be of the shape ... -> " ++ toS n ++ "\n instead found: " ++ show (codom t)
                (C c' :@: _) -> unless (c' == n) $ throwError $ "The constructor for type " ++ toS n ++ " ... , must be of the shape ... -> " ++ toS n ++ " ...\n instead found: " ++ show (codom t)
                _ -> throwError $ "constructor " ++ show c ++ " : " ++ show t ++ " of incorrect shape"
            -- (t', τ) <- evalElabType0 g t
            t' <- evalTypeOf0 env t VStar 
            -- strictPositivityCheck True n t
            return $ Γ $ (Global c,eval t' []):g' -- `debug` ("have " ++ show t ++ " found " ++ show t') 

