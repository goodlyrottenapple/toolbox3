{-# LANGUAGE OverloadedStrings, DeriveDataTypeable, FlexibleContexts, 
PatternSynonyms, DeriveFunctor, ScopedTypeVariables #-}


module LamPi where

import Data.Text(Text)
import qualified Data.Text as T
import Control.Monad(unless)
import Data.String.Conv(toS)

import Data.Data(Data)
import Data.Has

import Control.Monad.Except
import Control.Monad.State
import Control.Applicative

import Data.Map(Map)
import qualified Data.Map as M

import Data.Set(Set)

import qualified Data.Set as S

import Debug.Trace(trace)

import qualified SimpleSMT
import SMT
infixl 7 :@:


debug = flip trace

data ExplImpl a = I a | E a deriving (Show, Eq, Ord, Data, Functor)

data Name = Global Text
          | Local Int
          | Quote Int
          | Meta Int
          deriving (Eq, Ord, Data)

instance Show Name where
    show (Global t) = toS t 
    show (Local i) = "L" ++ show i
    show (Quote i) = "Q" ++ show i
    show (Meta i) = "M" ++ show i

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
    -- show Set = "Set"
    -- show (MkSet s) = "\'" ++ toS s
    show (Π t t') = "Π " ++ show t ++ " . " ++ show t'
    show (IΠ t t') = "Π {" ++ show t ++ "} . " ++ show t'
    show (t :⇒: t') = "[" ++ show t ++ "] -> " ++ show t'
    show (Bound n) = "B" ++ show n
    show (Free n) = show n
    show (x :@: xs) = show x ++ " " ++ showApp xs
        where
            showApp [] = ""
            showApp [I x] = "{" ++ show x ++ "}"
            showApp [E x@(_ :@:_)] = "(" ++ show x ++ ")"
            showApp [E x] = show x
            showApp (I x:xs) = "{" ++ show x ++ "} " ++ showApp xs
            showApp ((E x@(_ :@:_)):xs) = "(" ++ show x ++ ") " ++ showApp xs
            showApp ((E x):xs) = show x ++ " " ++ showApp xs


pattern C x = Free (Global x)
pattern M x = Free (Meta x)

data Value = VStar
           | VProp
           | VName
           | VMkName Text
           | VSet Value
           | VMkSet Value (Set Value)
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
subst i r x = x


bind :: Int -> Int -> Term -> Term
bind i r (Π τ τ') = Π (bind i r τ) (bind (i+1) r τ')
bind i r (IΠ τ τ') = IΠ (bind i r τ) (bind (i+1) r τ')
bind i r (τ :⇒: τ') = (bind i r τ) :⇒: (bind i r τ')
bind i r e@(Free (Local j)) = if r == j then Bound i else e
bind i r (e :@: es) = bind i r e :@: (fmap (fmap (bind i r)) es)
bind i r x = x


substMeta :: Int -> Term -> Term -> Term
substMeta i r (Π τ τ') = Π (substMeta i r τ) (substMeta i r τ')
substMeta i r (IΠ τ τ') = IΠ (substMeta i r τ) (substMeta i r τ')
substMeta i r (Bound j) = Bound j 
substMeta i r (Free (Meta j)) = if i == j then r else Free (Meta j)
substMeta i r (e :@: es) = substMeta i r e :@: (fmap (fmap (substMeta i r)) es)
substMeta i r x = x



quote0 :: Value -> Term 
quote0 = quote 0

quote :: Int -> Value -> Term
quote i VStar = Star
quote i VProp = Prop
quote i VName = Name
quote i (VMkName s) = MkName s
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


elabType :: (Has BVCounter s, Has MetaCounter s, Has Γ s, Has ConstrList s, MonadState s m , MonadError String m) => 
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
-- elabType i m (MkSet α xs) = do
    -- let α' = eval α [ ]
    -- return $ (MkSet α [], VSet α', m)

--     let slist = S.toList s
--     foldM (\m selem -> ) m slist

--     σ <- unifyConstraints cs [] False M.empty -- `debug` ("\n\nconstraints: " ++ show cs)
--     let τ'' = substMetas σ τ'
--     checkDoesNotContainMetas τ''

--     return (Set, VΠ VStar (\_ -> VStar) , m)
elabType (Π ρ ρ') = do
    τ <- typeOf ρ VStar
    i <- getFreshAndIncrementBV
    addToΓ (Local i) $ eval ρ []
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
elabType (ρ :⇒: ρ') = do
    τ <- typeOf ρ VProp `debug` ("\n\ntype: " ++ show (ρ :⇒: ρ'))
    τ' <- typeOf ρ' VStar
    (ConstrList cs) <- getConstrList
    σ <- unifyConstraints cs [] False M.empty -- `debug` ("\n\nconstraints: " ++ show cs)
    let τ'' = substMetas σ τ'
    checkDoesNotContainMetas "here1" τ''
    return (τ :⇒: τ'', VStar)
elabType (Free n) = do
    τ <- lookupInΓ n
    return (Free n, τ)
elabType (e :@: es) = do  -- D :@: xs
    (e',τ) <- elabType e       -- D : σ
    (es',τ') <- elabTypeApp τ es
    return (e' :@: es', τ')
    -- typeOfApp i g σ es
elabType e = error $ "can't handle " ++ show e


elabTypeApp :: (Has BVCounter s, Has MetaCounter s, Has Γ s, Has ConstrList s, MonadState s m , MonadError String m) => 
    Type -> [ExplImpl Term] -> m ([ExplImpl Term], Type)
elabTypeApp ty [] = case ty of
    (VIΠ τ τ') -> do
        mi <- getFreshAndIncrementMeta
        let mvar = Free (Meta mi)
        addToΓ (Meta mi) τ
        (xs',τ'') <- elabTypeApp (τ' (eval mvar [])) []
        return $ (I mvar:xs',τ'')
    (VΠ _ _) -> throwError $ "illegal application at " <> (toS $ show ty)
    (VSArr _  τ') -> elabTypeApp τ' []
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

        elabTypeApp τ' (x:xs) `debug` ("\n\nconstraint is: "++ show cnstr)
    _ -> throwError $ "illegal application at " <> (toS $ show x) <> " : " <> (toS $ show ty)



typeOf :: (Has BVCounter s, Has MetaCounter s, Has Γ s, Has ConstrList s, MonadState s m , MonadError String m) => 
    Term -> Type -> m Term
typeOf e τ = do
    cs <- getConstrList
    (e',τ') <- elabType e 
    case τ' of --`debug` (show e' ++ " : orig= " ++ show τ ++ ", elab= " ++ show τ') of
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
    | otherwise = error "length of xs and ys is different"
    where

        unifyTypeApp :: (ExplImpl Term, ExplImpl Term) -> [(Term,Term)]
        unifyTypeApp (E x,E y) = unifyType x y
        unifyTypeApp (I x,I y) = unifyType x y
        unifyTypeApp _ = error "trying to unify E with I"

unifyType τ τ' = error $ "\n\nfailed on : " ++ show τ ++ " and " ++ show τ' ++ "\n\n"


unifyConstraints :: MonadError String m => [(Term,Term)] -> [(Term,Term)] -> Bool -> Map Int Term -> m (Map Int Term)
unifyConstraints []                          []  _     m = return m
unifyConstraints []                          acc False m = 
    throwError $ "cannot unify rest (acc): " ++ show acc ++ "; m contains: " ++ show m
unifyConstraints []                          acc True  m = 
    unifyConstraints (map (\(x,y) -> (substMetas m x, substMetas m y)) acc) [] False m
unifyConstraints ((M x, M y):xs) acc flag m = case (M.lookup x m, M.lookup y m) of 
    (Just tx, Just ty) -> do
        unless (tx == ty) $ throwError $ "cannot unify: " ++ show [tx,ty]
        unifyConstraints xs acc flag m
    (Just tx, Nothing) -> unifyConstraints xs acc flag $ M.insert y tx m
    (Nothing, Just ty) -> unifyConstraints xs acc flag $ M.insert x ty m
    (Nothing, Nothing) -> unifyConstraints xs ((M x, M y):acc) flag m
unifyConstraints ((M x, y):xs)               acc flag  m 
    | doesNotContainMetas y = unifyConstraints xs acc True $ M.insert x y m
    | otherwise = unifyConstraints xs ((M x, y):acc) flag m 
unifyConstraints ((x, M y):xs)               acc flag  m = unifyConstraints ((M y,x):xs) acc flag m
unifyConstraints ((Star, Star):xs)           acc flag  m = unifyConstraints xs acc flag m
unifyConstraints ((Name, Name):xs)           acc flag  m = unifyConstraints xs acc flag m
unifyConstraints ((MkName x, MkName y):xs)   acc flag  m | x == y = unifyConstraints xs acc flag m
unifyConstraints ((Π σ σ', Π τ τ'):xs)       acc flag  m = throwError "not sure how to unify yet"
unifyConstraints ((IΠ σ σ', IΠ τ τ'):xs)     acc flag  m = throwError "not sure how to unify yet"
unifyConstraints ((Free x, Free y):xs)       acc flag  m | x == y = unifyConstraints xs acc flag m
unifyConstraints ((Bound x, Bound y):xs)     acc flag  m | x == y = unifyConstraints xs acc flag m
unifyConstraints ((e :@: es, e' :@: es'):xs) acc flag  m = do
    eses' <- mapM matchApp $ zip es es'
    unifyConstraints ((e,e'):eses'++xs) acc flag m
    where
        matchApp :: MonadError String m => (ExplImpl Term , ExplImpl Term) -> m (Term, Term)
        matchApp (E t , E t') = return (t,t')
        matchApp (I t , I t') = return (t,t')
        matchApp (t , t') = throwError $ "cannot unify: " ++ show [t,t']
unifyConstraints (x:_)                       _   _     _ = throwError $ "bad constraint " ++ show x


doesNotContainMetas :: Term -> Bool
doesNotContainMetas (M _) = False
doesNotContainMetas (Π τ τ') = doesNotContainMetas τ && doesNotContainMetas τ'
doesNotContainMetas (IΠ τ τ') = doesNotContainMetas (Π τ τ')
doesNotContainMetas (e :@: es) = doesNotContainMetas e && foldr doesNotContainMetasApp True es
    where
        doesNotContainMetasApp _ False = False
        doesNotContainMetasApp (E x) b = doesNotContainMetas x && b
        doesNotContainMetasApp (I x) b = doesNotContainMetas x && b
doesNotContainMetas _ = True


substMetas :: Map Int Term -> Term -> Term
substMetas m t = foldr (\(i,v) t' -> substMeta i v t') t (M.toList m)



mkMap :: [(Term,Term)] -> Map Int Term
mkMap [] = M.empty
mkMap ((M x, y):xs) = M.insert x y $ mkMap xs
mkMap ((x, M y):xs) = M.insert y x $ mkMap xs
mkMap (_:xs) = mkMap xs


-- runElabType0' :: Γ -> Term -> Either String (Term, Type, [(Term,Term)])
-- runElabType0' g t = runExcept (flip evalStateT (MetaCounter 0,g,ConstrList []) $ elabType 0 t)

runElabType0 :: Γ -> Term -> Either String (Term, Type)
runElabType0 g t = runExcept (flip evalStateT (BVCounter 0,MetaCounter 0,g,ConstrList []) (elabType0 t))


-- evalElabType0 :: MonadError String m => Γ -> Term -> m (Term, Type)
-- evalElabType0 g t = flip evalStateT (MetaCounter 0,g,ConstrList []) (elabType0 t)


elabType0 ::  (Has BVCounter s, Has MetaCounter s, Has Γ s, Has ConstrList s, MonadState s m , MonadError String m) => 
    Term -> m (Term, Type)
elabType0 t = do 
    (trm,typ) <- elabType t
    (ConstrList cs) <- getConstrList
    σ <- unifyConstraints cs [] False M.empty `debug` ("\n\nelabType0 constraints: " ++ show cs)
    let trm' = substMetas σ trm
        typ' = substMetas σ $ quote0 typ
    unless (doesNotContainMetas trm')$ throwError $ show trm' ++ " contains metas! (elabType0)"
    unless (doesNotContainMetas typ')$ throwError $ show typ' ++ " contains metas! (elabType0)"
    return $ (trm', eval typ' [])



typeOf0 ::  (Has BVCounter s, Has MetaCounter s, Has Γ s, Has ConstrList s, MonadState s m , MonadError String m) => 
    Term -> Type -> m Term
typeOf0 t τ = do
    trm <- typeOf t τ
    (ConstrList cs) <- getConstrList
    σ <- unifyConstraints cs [] False M.empty `debug` ("\n\ntypeOf0 constraints: " ++ show cs)
    let trm' = substMetas σ trm
    unless (doesNotContainMetas trm')$ throwError $ show trm' ++ " contains metas! (typeOf0)"
    return trm'


evalTypeOf0 :: MonadError String m => Γ -> Term -> Type -> m Term
evalTypeOf0 g t τ = flip evalStateT (BVCounter 0,MetaCounter 0,g,ConstrList []) (typeOf0 t τ) `debug` ("evalTypeOf0 ... " ++ show t ++ " : " ++ show τ)




data Decl = 
    Data Text Term [(Text, Term)]  deriving (Show, Eq, Data)
  -- | Def name (Type name) [PClause name]


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


defineDecl :: MonadError String m => Γ -> Decl -> m Γ 
defineDecl env@(Γ g) (Data n t xs) = do
    case lookup (Global n) g of
        Just _ -> throwError $ "constant " ++ toS n ++ " already defined"
        Nothing -> do
            t' <- evalTypeOf0 env t VStar
            let τ = eval t' []
            unless (codom t == Star || codom t == Prop) $ throwError $ toS n ++ " data declaration should have type ... -> */Prop"
            (Γ g') <- defineTyCon (Γ $ (Global n,τ):g) n xs
            return $ Γ $ g' ++ ((Global n,τ):g)

defineTyCon :: MonadError String m => Γ -> Text -> [(Text, Term)] -> m Γ 
defineTyCon _ _ [] = return $ Γ []
defineTyCon env@(Γ g) n ((c, t):xs) = do
    (Γ g') <- defineTyCon env n xs
    case lookup (Global c) (g ++ g') of
        Just _ -> throwError $ "constant " ++ toS c ++ " already defined"
        Nothing -> do
            -- (t', τ) <- evalElabType0 g t
            t' <- evalTypeOf0 env t VStar 
            -- strictPositivityCheck True n t
            return $ Γ $ (Global c,eval t' []):g' -- `debug` ("have " ++ show t ++ " found " ++ show t') 




testSMT :: IO ()
testSMT = runCVC4 "QF_UFSLIAFS" $ do
    a <- declare "a" (Just "a")
    b <- declare "b" (Just "b")
    c <- declare "c" (Just "c")
    (x :: SExprT (Set String)) <- declare "X" Nothing
    (y :: SExprT (Set String)) <- declare "Y" Nothing

    assert (a `member` x)
    assert (b `member` x)
    assert (c `member` y)
    assert (distinct [a, b, c])
    assert (y `eq` (x `elemMinus` a))
    assert (card y `geq` defineSExpr 3)
    r <- check

    case r of
        SimpleSMT.Sat -> do
            aval <- getExpr a
            xval <- getExpr x
            yval <- getExpr y
            liftIO $ putStrLn $ show aval
            liftIO $ putStrLn $ show xval
            liftIO $ putStrLn $ show yval
        _ -> return () 

