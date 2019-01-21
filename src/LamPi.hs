{-# LANGUAGE OverloadedStrings, DeriveDataTypeable, FlexibleContexts, 
PatternSynonyms, DeriveFunctor, ScopedTypeVariables #-}


module LamPi where

import Data.Text(Text)
import qualified Data.Text as T
import Control.Monad(unless)
import Data.String.Conv(toS)

import Data.Data(Data)
import Control.Monad.Except
import Control.Monad.State
import Control.Applicative

import Data.Map(Map)
import qualified Data.Map as M

import Data.Set(Set)


import Debug.Trace(trace)

import qualified SimpleSMT
import SMT
infixl 7 :@:


debug = flip trace

data ExplImpl a = I a | E a deriving (Show, Eq, Data, Functor)

data Name = Global Text
          | Local Int
          | Quote Int
          | Meta Int
          deriving (Eq, Data)

instance Show Name where
    show (Global t) = toS t 
    show (Local i) = "L" ++ show i
    show (Quote i) = "Q" ++ show i
    show (Meta i) = "M" ++ show i

data Term = Star
          | Prop
          | Name
          | MkName Text
          | Π Term Term
          | IΠ Term Term
          | Term :⇒: Term
          | Bound Int
          | Free Name
          | Term :@: [ExplImpl Term]
          deriving (Eq, Data)
instance Show Term where
    show Star = "*"
    show Prop = "Prop"
    show Name = "Name"
    show (MkName s) = "\'" ++ toS s
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
type Γ = [(Name, Type)]


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



getFreshAndIncrementMeta :: MonadState (Int,Γ) m => m Int
getFreshAndIncrementMeta = do
    (m,_) <- get
    modify (\(m,g) -> (m+1,g))
    return m

addToΓ :: MonadState (Int,Γ) m => Name -> Type -> m ()
addToΓ n τ = modify (\(m,g) -> (m,(n, τ):g))

lookupInΓ :: (MonadState (Int,Γ) m , MonadError String m) => Name -> m Type
lookupInΓ n = do
    (_,g) <- get
    case lookup n g of
        Just τ -> return τ
        Nothing -> throwError "unknown identifier"


checkDoesNotContainMetas t = unless (doesNotContainMetas t) $ throwError $ show t ++ " contains metas!"


elabType :: (MonadState (Int,Γ) m , MonadError String m) => Int -> [(Term,Term)] -> Term -> m (Term, Type, [(Term,Term)])
elabType i m Star = return (Star, VStar, m)
elabType i m Prop = return (Prop, VStar, m)
elabType i m Name = return (Name, VStar, m)
elabType i m (MkName s) = return (MkName s, VName, m)
elabType i m (Π ρ ρ') = do
    (τ, m') <- typeOf i m ρ VStar
    addToΓ (Local i) $ eval ρ [ ]
    (τ',cs) <- typeOf (i+1) m' (subst 0 (Free (Local i)) ρ') VStar

    σ <- unifyConstraints cs [] False M.empty -- `debug` ("\n\nconstraints: " ++ show cs)
    let τ'' = substMetas σ τ'
    checkDoesNotContainMetas τ''

    return (Π τ (bind 0 i τ''), VStar, cs) -- `debug` ("i after: " ++ show i') -- 
        -- `debug` ("\n\ngot: " ++ show (Π ρ ρ') ++ " with fresh L" ++ show i ++ ", after subst: " ++ show (subst 0 (Free (Local i)) ρ') ++ " returning: " ++ show (Π τ (bind 0 i τ')))
elabType i m (IΠ ρ ρ') = do
    (Π τ τ', τ'', m') <- elabType i m (Π ρ ρ')
    return (IΠ τ τ', τ'', m')
elabType i m (ρ :⇒: ρ') = do
    (τ, m') <- typeOf i m ρ VProp `debug` ("\n\ntype: " ++ show (ρ :⇒: ρ'))
    (τ', cs) <- typeOf i m' ρ' VStar
    σ <- unifyConstraints cs [] False M.empty -- `debug` ("\n\nconstraints: " ++ show cs)
    let τ'' = substMetas σ τ'
    checkDoesNotContainMetas τ''
    return (τ :⇒: τ'', VStar, cs)
elabType i m (Free n) = do
    τ <- lookupInΓ n
    return (Free n, τ, m)
elabType i m (e :@: es) = do  -- D :@: xs
    (e',τ,m') <- elabType i m e       -- D : σ
    (es',τ',m'') <- elabTypeApp i m' τ es
    return (e' :@: es', τ', m'')
    -- typeOfApp i g σ es
elabType i m e = error $ "can't handle " ++ show e


elabTypeApp :: (MonadState (Int,Γ) m , MonadError String m) => Int -> [(Term,Term)] -> Type -> [ExplImpl Term] -> m ([ExplImpl Term], Type, [(Term,Term)])
elabTypeApp i m ty [] = case ty of
        (VIΠ τ τ') -> do
            mi <- getFreshAndIncrementMeta
            let mvar = Free (Meta mi)
            addToΓ (Meta mi) τ
            (xs',τ'',σ) <- elabTypeApp i m (τ' (eval mvar [])) []
            return $ (I mvar:xs',τ'',σ)
        (VΠ _ _) -> throwError $ "illegal application at " <> (toS $ show ty)
        (VSArr _  τ') -> elabTypeApp i m τ' []
        _ -> return ([], ty , m)
elabTypeApp i m ty (x:xs) = do
    case (x,ty) of
        (E x', VΠ τ τ') -> do
            (x'', m') <- typeOf i m x' τ
            (xs',τ'',σ) <- elabTypeApp i m' (τ' (eval x'' [])) (fmap (fmap $ substMetas $ mkMap m') xs)
            return $ (E x'':xs',τ'',σ)
        (I x', VIΠ τ τ') -> do
            (x'', m') <- typeOf i m x' τ
            (xs',τ'',σ) <- elabTypeApp i m' (τ' (eval x'' [])) (fmap (fmap $ substMetas $ mkMap m') xs) --(fmap (fmap $ substMetas m') xs)
            return $ (I x'':xs',τ'',σ)
        (E _, VIΠ τ τ') -> do
            mi <- getFreshAndIncrementMeta
            let mvar = Free (Meta mi)
            addToΓ (Meta mi) τ
            (xs',τ'',m) <- elabTypeApp i m (τ' (eval mvar [])) (x:xs) -- `debug` ("adding meta: " ++ show (VIΠ τ τ') ++ " -> " ++ show (τ' (eval (Free (Global "aaa")) [])))
            return $ (I mvar:xs',τ'',m)
        (_, VSArr _ τ') -> elabTypeApp i m τ' (x:xs)
        _ -> throwError $ "illegal application at " <> (toS $ show x) <> " : " <> (toS $ show ty)


mkMap :: [(Term,Term)] -> Map Int Term
mkMap [] = M.empty
mkMap ((M x, y):xs) = M.insert x y $ mkMap xs
mkMap ((x, M y):xs) = M.insert y x $ mkMap xs
mkMap (_:xs) = mkMap xs


typeOf :: (MonadState (Int,Γ) m , MonadError String m) => Int -> [(Term,Term)] -> Term -> Type -> m (Term, [(Term,Term)]) 
typeOf i m e τ = do 
    (e',τ',m') <- elabType i m e 
    case τ' of --`debug` (show e' ++ " : orig= " ++ show τ ++ ", elab= " ++ show τ') of
        -- in case of C "Cons" :@: [E $ C "Z", E $ C "Nil"]
        -- we want to make C "Nil" into a C "Nil" :@: [] to add hidden params
        VIΠ _ _ -> do
            (e'',τ'',m'') <- elabType i m (e :@: [])
            return $ (e'' , unifyType m'' (quote0 τ) (quote0 τ''))
        _ -> return $ (e' , unifyType m' (quote0 τ) (quote0 τ'))


unifyType :: [(Term,Term)] -> Term -> Term -> [(Term,Term)]
unifyType m τ τ' | τ == τ' = m
unifyType m (Free (Meta i)) τ' = (Free (Meta i),τ'):m
unifyType m τ (Free (Meta i)) = (Free (Meta i),τ):m
unifyType m (x :@: xs) (y :@: ys) 
    | length xs == length ys = foldl unifyTypeApp m' $ zip xs ys
    | otherwise = error "length of xs and ys is different"
    where
        m' = unifyType m x y

        unifyTypeApp :: [(Term,Term)] -> (ExplImpl Term, ExplImpl Term) -> [(Term,Term)]
        unifyTypeApp m (E x,E y) = unifyType m x y
        unifyTypeApp m (I x,I y) = unifyType m x y
        unifyTypeApp m _ = error "trying to unify E with I"

unifyType m τ τ' = error $ "\n\nfailed on : " ++ show τ ++ " and " ++ show τ' ++ "\n\n"


unifyConstraints :: MonadError String m => [(Term,Term)] -> [(Term,Term)] -> Bool -> Map Int Term -> m (Map Int Term)
unifyConstraints [] [] _ m = return m
unifyConstraints [] acc False m = throwError $ "cannot unify rest (acc): " ++ show acc ++ "; m contains: " ++ show m
unifyConstraints [] acc True m = unifyConstraints (map (\(x,y) -> (substMetas m x, substMetas m y)) acc) [] False m
unifyConstraints ((M x, M y):xs) acc flag m = case (M.lookup x m, M.lookup y m) of 
    (Just tx, Just ty) -> do
        unless (tx == ty) $ throwError $ "cannot unify: " ++ show [tx,ty]
        unifyConstraints xs acc flag m
    (Just tx, Nothing) -> unifyConstraints xs acc flag $ M.insert y tx m
    (Nothing, Just ty) -> unifyConstraints xs acc flag $ M.insert x ty m
    (Nothing, Nothing) -> unifyConstraints xs ((M x, M y):acc) flag m
unifyConstraints ((M x, y):xs) acc flag m 
    | doesNotContainMetas y = unifyConstraints xs acc True $ M.insert x y m
    | otherwise = unifyConstraints xs ((M x, y):acc) flag m 
unifyConstraints ((x, M y):xs) acc flag m = unifyConstraints ((M y,x):xs) acc flag m
unifyConstraints ((Star, Star):xs) acc flag m = unifyConstraints xs acc flag m
unifyConstraints ((Name, Name):xs) acc flag m = unifyConstraints xs acc flag m
unifyConstraints ((MkName x, MkName y):xs) acc flag m | x == y = unifyConstraints xs acc flag m
unifyConstraints ((Π σ σ', Π τ τ'):xs) acc flag m = throwError "not sure how to unify yet"
unifyConstraints ((IΠ σ σ', IΠ τ τ'):xs) acc flag m = throwError "not sure how to unify yet"
unifyConstraints ((Free x, Free y):xs) acc flag m | x == y = unifyConstraints xs acc flag m
unifyConstraints ((Bound x, Bound y):xs) acc flag m | x == y = unifyConstraints xs acc flag m
unifyConstraints ((e :@: es, e' :@: es'):xs) acc flag m = do
    eses' <- mapM matchApp $ zip es es'
    unifyConstraints ((e,e'):eses'++xs) acc flag m
    where
        matchApp :: MonadError String m => (ExplImpl Term , ExplImpl Term) -> m (Term, Term)
        matchApp (E t , E t') = return (t,t')
        matchApp (I t , I t') = return (t,t')
        matchApp (t , t') = throwError $ "cannot unify: " ++ show [t,t']

unifyConstraints (x:_) _ _ _ = throwError $ "bad constraint " ++ show x


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

runElabType0' :: Γ -> Term -> Either String (Term, Type, [(Term,Term)])
runElabType0' g t = runExcept (flip evalStateT (0,g) $ elabType 0 [] t)

runElabType0 :: Γ -> Term -> Either String (Term, Type)
runElabType0 g t = runExcept (flip evalStateT (0,g) (elabType0 t))


evalElabType0 :: MonadError String m => Γ -> Term -> m (Term, Type)
evalElabType0 g t = flip evalStateT (0,g) (elabType0 t)


elabType0 :: (MonadState (Int,Γ) m , MonadError String m) => Term -> m (Term, Type)
elabType0 t = do 
    (trm,typ,cs) <- elabType 0 [] t
    σ <- unifyConstraints cs [] False M.empty `debug` ("\n\nconstraints: " ++ show cs)
    let trm' = substMetas σ trm
        typ' = substMetas σ $ quote0 typ
    unless (doesNotContainMetas trm')$ throwError $ show trm' ++ " contains metas!"
    unless (doesNotContainMetas typ')$ throwError $ show typ' ++ " contains metas!"
    return $ (trm', eval typ' [])



typeOf0 :: (MonadState (Int,Γ) m , MonadError String m) => Term -> Type -> m Term
typeOf0 t τ = do
    (trm, cs) <- typeOf 0 [] t τ
    σ <- unifyConstraints cs [] False M.empty `debug` ("\n\nconstraints: " ++ show cs)
    let trm' = substMetas σ trm
    unless (doesNotContainMetas trm')$ throwError $ show trm' ++ " contains metas!"
    return trm'


evalTypeOf0 :: MonadError String m => Γ -> Term -> Type -> m Term
evalTypeOf0 g t τ = flip evalStateT (0,g) (typeOf0 t τ)




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
defineDecl g (Data n t xs) = do
    case lookup (Global n) g of
        Just _ -> throwError $ "constant " ++ toS n ++ " already defined"
        Nothing -> do
            t' <- evalTypeOf0 g t VStar
            let τ = eval t' []
            unless (codom t == Star || codom t == Prop) $ throwError $ toS n ++ " data declaration should have type ... -> */Prop"
            g' <- defineTyCon ((Global n,τ):g) n xs
            return $ g' ++ ((Global n,τ):g)

defineTyCon :: MonadError String m => Γ -> Text -> [(Text, Term)] -> m Γ 
defineTyCon _ _ [] = return []
defineTyCon g n ((c, t):xs) = do
    g' <- defineTyCon g n xs
    case lookup (Global c) (g ++ g') of
        Just _ -> throwError $ "constant " ++ toS c ++ " already defined"
        Nothing -> do
            -- (t', τ) <- evalElabType0 g t
            t' <- evalTypeOf0 g t VStar 
            -- strictPositivityCheck True n t
            return ((Global c,eval t' []):g') -- `debug` ("have " ++ show t ++ " found " ++ show t') 





testSMT :: IO ()

testSMT = runCVC4 $ do
        (a :: SExprT Integer) <- declare "a"
        (b :: SExprT Integer) <- declare "b"
        (c :: SExprT Integer) <- declare "c"
        (x :: SExprT (Set Integer)) <- declare "X"
        (y :: SExprT (Set Integer)) <- declare "Y"
        -- define a 6


        assert (a `member` x)
        assert (b `member` x)
        assert (c `member` y)

        assert (distinct [a, b, c])

        assert (y `eq` (x `elemMinus` a))

        -- assert (card y `geq` defineSExpr 3)

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

-- testSMT = do
--     log <- SMT.newLogger 0
--     smt <- SMT.newSolver "cvc4" ["--incremental", "--lang" , "smt2.0"] (Just log)
--     SMT.setLogic smt "QF_UFLIAFS"

    -- r <- SMT.check smt
        -- case r of
        --     SMT.Sat -> do
        --         vals <- SMT.getExprs smt [SMT.Atom "a", SMT.Atom "X"]
        --         putStrLn $ show vals
        --     _ -> return () 
    -- SMT.stop smt


