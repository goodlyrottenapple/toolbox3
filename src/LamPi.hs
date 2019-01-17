{-# LANGUAGE OverloadedStrings, DeriveDataTypeable, FlexibleContexts, PatternSynonyms, DeriveFunctor #-}


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

infixl 7 :@: -- , :|@|:


data ExplImpl a = I a | E a deriving (Show, Eq, Data, Functor)

data Name = Global Text
          | Local Int
          | Quote Int
          | Meta Int
          deriving (Eq, Data)

instance Show Name where
    show (Global t) = toS t 
    show (Local i) = show i
    show (Quote i) = "Q" ++ show i
    show (Meta i) = "M" ++ show i

data Term = Star
          | String
          | MkString Text
          | Π Term Term
          | IΠ Term Term
          | Bound Int
          | Free Name
          | Term :@: [ExplImpl Term]
          -- | Term :|@|: Term
          -- | Const Text 
          -- | Hole Term 
          deriving (Eq, Data)
instance Show Term where
    show Star = "*"
    show String = "String"
    show (MkString s) = "\"" ++ toS s ++ "\""
    show (Π t t') = "Π " ++ show t ++ " . " ++ show t'
    show (IΠ t t') = "Π {" ++ show t ++ "} . " ++ show t'
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
           | VString
           | VMkString Text
           | VΠ Value (Value -> Value)
           | VIΠ Value (Value -> Value)
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


-- viapp :: Value -> Value -> Value 
-- -- vapp (VLam f) v =f v
-- viapp (VΠ n f) v = f v
-- viapp (VIΠ n f) v = f v
-- viapp (VNeutral n) v = VNeutral (NIApp n v)


eval :: Term -> Env -> Value
eval Star d = VStar
eval String d = VString
eval (MkString s) d = VMkString s
eval (Π τ τ') d = VΠ (eval τ d) (\x -> eval τ' (x:d))
eval (IΠ τ τ') d = VIΠ (eval τ d) (\x -> eval τ' (x:d))
eval (Free x) d = vfree x
eval (Bound i) d = d !! i
eval (e :@: es) d = vapp (eval e d) (fmap (fmap (flip eval d)) es)
-- eval (e :|@|: e') d = viapp (eval e d) (eval e' d)
-- eval (Const x) d = VNeutral (NConst x)
-- eval (Hole e) d = VNeutral $ NHole $ (eval e d)


subst :: Int -> Term -> Term -> Term
subst i r (Π τ τ') = Π (subst i r τ) (subst (i+1) r τ')
subst i r (IΠ τ τ') = IΠ (subst i r τ) (subst (i+1) r τ')
subst i r (Bound j) = if i == j then r else Bound j 
subst i r (e :@: es) = subst i r e :@: (fmap (fmap (subst i r)) es)
subst i r x = x


substMeta :: Int -> Term -> Term -> Term

substMeta i r (Π τ τ') = Π (substMeta i r τ) (substMeta i r τ')
substMeta i r (IΠ τ τ') = IΠ (substMeta i r τ) (substMeta i r τ')
substMeta i r (Bound j) = Bound j 
substMeta i r (Free (Meta j)) = if i == j then r else Free (Meta j)
substMeta i r (e :@: es) = substMeta i r e :@: (fmap (fmap (substMeta i r)) es)
substMeta i r x = x

-- subst i r (e :|@|: e') = subst i r e :|@|: subst i r e'
-- subst i r (Const x) = Const x
-- subst i r (Meta x) = Meta x



quote0 :: Value -> Term 
quote0 = quote 0

quote :: Int -> Value -> Term
quote i VStar = Star
quote i VString = String
quote i (VMkString s) = MkString s
quote i (VΠ v f) = Π (quote i v) (quote (i + 1) (f (vfree (Quote i))))
quote i (VIΠ v f) = IΠ (quote i v) (quote (i + 1) (f (vfree (Quote i))))
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


-- type Result α = Either String α

inferType :: MonadError String m => Int -> Γ -> Term -> m Type 
inferType i g Star = return VStar
inferType i g String = return VStar
inferType i g (MkString _) = return VString
inferType i g (Π ρ ρ') = do
    typeOf i g ρ VStar
    let τ = eval ρ [ ]
    typeOf (i+1) ((Local i,τ):g) (subst 0 (Free (Local i)) ρ') VStar
    return VStar
inferType i g (IΠ ρ ρ') = do
    typeOf i g ρ VStar
    let τ = eval ρ [ ]
    typeOf (i+1) ((Local i,τ):g) (subst 0 (Free (Local i)) ρ') VStar
    return VStar
inferType i g (Free x) = case lookup x g of
    Just τ -> return τ
    Nothing -> throwError "unknown identifier"
inferType i g (e :@: es) = do  -- D :@: xs
    σ <- inferType i g e       -- D : σ
    typeOfApp i g σ es

typeOfApp :: MonadError String m => Int -> Γ -> Type -> [ExplImpl Term] -> m Type
typeOfApp i g σ [] = return σ
typeOfApp i g σ (x:xs) = do
    case (x,σ) of
        (E x', VΠ τ τ') -> do
            typeOf i g x' τ
            typeOfApp i g (τ' (eval x' [])) xs
        (I x', VIΠ τ τ') -> do
            typeOf i g x' τ
            typeOfApp i g (τ' (eval x' [])) xs
        _ ->  throwError $ "illegal application at " <> (toS $ show x) <> " - " <> (toS $ show $ quote0 σ)



getFreshAndIncrement :: MonadState (Int,Int,Γ) m => m Int
getFreshAndIncrement = do
    (i,_,_) <- get
    modify (\(i,m,g) -> (i+1,m,g))
    return i

getFreshAndIncrementMeta :: MonadState (Int,Int,Γ) m => m Int
getFreshAndIncrementMeta = do
    (_,m,_) <- get
    modify (\(i,m,g) -> (i,m+1,g))
    return m

addToΓ :: MonadState (Int,Int,Γ) m => Name -> Type -> m ()
addToΓ n τ = modify (\(i,m,g) -> (i,m,(n, τ):g))

lookupInΓ :: (MonadState (Int,Int,Γ) m , MonadError String m) => Name -> m Type
lookupInΓ n = do
    (_,_,g) <- get
    case lookup n g of
        Just τ -> return τ
        Nothing -> throwError "unknown identifier"




elabType :: (MonadState (Int,Int,Γ) m , MonadError String m) => [(Term,Term)] -> Term -> m (Term, Type, [(Term,Term)])
elabType m Star = return (Star, VStar, m)
elabType m String = return (String, VStar, m)
elabType m (MkString s) = return (MkString s, VString, m)
elabType m (Π ρ τ) = do
    (ρ', m') <- typeOf' m ρ VStar
    i <- getFreshAndIncrement
    let ρ'' = eval ρ' [ ]
    addToΓ (Local i) ρ''
    (τ' ,m'') <- typeOf' m' (subst 0 (Free (Local i)) τ) VStar
    return (Π ρ' τ', VStar, m'')
elabType m (IΠ ρ ρ') = do
    (Π τ τ', τ'', m') <- elabType m (Π ρ ρ')
    return (IΠ τ τ', τ'', m')
elabType m (Free n) = do
    τ <- lookupInΓ n
    return (Free n, τ, m)
elabType m (e :@: es) = do  -- D :@: xs
    (e',τ,m') <- elabType m e       -- D : σ

    (es',τ',m'') <- elabTypeApp m' τ es
    return (e' :@: es', τ', m'')
    -- typeOfApp i g σ es


elabTypeApp :: (MonadState (Int,Int,Γ) m , MonadError String m) => [(Term,Term)] -> Type -> [ExplImpl Term] -> m ([ExplImpl Term], Type, [(Term,Term)])
elabTypeApp m ty [] = case ty of
        (VIΠ τ τ') -> do
            -- typeOf' x' τ
            mi <- getFreshAndIncrementMeta
            let mvar = Free (Meta mi)
            addToΓ (Meta mi) τ
            (xs',τ'',σ) <- elabTypeApp m (τ' (eval mvar [])) []
            return $ (I mvar:xs',τ'',σ)
        _ -> return ([], ty , m)
elabTypeApp m ty (x:xs) = do
    case (x,ty) of
        (E x', VΠ τ τ') -> do
            (x'', m') <- typeOf' m x' τ
            (xs',τ'',σ) <- elabTypeApp m' (τ' (eval x'' [])) (fmap (fmap $ substMetas $ mkMap m') xs)
            return $ (E x'':xs',τ'',σ)
        (I x', VIΠ τ τ') -> do
            (x'', m') <- typeOf' m x' τ
            (xs',τ'',σ) <- elabTypeApp m' (τ' (eval x'' [])) (fmap (fmap $ substMetas $ mkMap m') xs) --(fmap (fmap $ substMetas m') xs)
            return $ (I x'':xs',τ'',σ)
        (E _, VIΠ τ τ') -> do
            -- typeOf' x' τ
            mi <- getFreshAndIncrementMeta
            let mvar = Free (Meta mi)
            addToΓ (Meta mi) τ
            (xs',τ'',m) <- elabTypeApp m (τ' (eval mvar [])) (x:xs)
            return $ (I mvar:xs',τ'',m)
        _ ->  throwError $ "illegal application at " <> (toS $ show x)


mkMap :: [(Term,Term)] -> Map Int Term
mkMap [] = M.empty
mkMap ((M x, y):xs) = M.insert x y $ mkMap xs
mkMap ((x, M y):xs) = M.insert y x $ mkMap xs
mkMap (_:xs) = mkMap xs


typeOf' :: (MonadState (Int,Int,Γ) m , MonadError String m) => [(Term,Term)] -> Term -> Type -> m (Term, [(Term,Term)]) 
typeOf' m e τ = do 
    (e',τ',_) <- elabType m e
    if (quote0 τ /= quote0 τ') then return $ (e' , unifyType m (quote0 τ) (quote0 τ'))
    else return (e', m)

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
unifyConstraints [] acc False m = throwError $ "cannot unify rest: " ++ show acc ++ "m contains: " ++ show m
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
unifyConstraints (x:_) _ _ _ = throwError $ "bad constraint" ++ show x


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

-- unifyType m (Π ρ ρ')


-- Star
--           | Π Term Term
--           | IΠ Term Term
--           | Bound Int
--           | Free Name
--           | Term :@: [ExplImpl Term]
--           τ τ' = 





-- typeOf' :: (MonadState (Int,Int,Γ) m , MonadError String m) => [(Term,Term)] -> Term -> Type -> m ([(Term,Term)]) 
-- typeOf' m e τ = do 
--     (_,τ',_) <- elabType m e

--     case e of
--         Free (Meta i) -> do
--             case M.lookup i m of
--                 Just e' -> do
--                     unless (e' == e) $ throwError $ "inconsistent meta... tried unifying" <> (toS $ show $ e') <> " with " <> (toS $ show $ e')
--                     return m
--                 Nothing -> return $ M.insert i e m
--         _ -> do
--             unless (quote0 τ == quote0 τ') $ throwError $ 
--                 "Type mismatch in " <> (toS $ show $ e) <> 
--                 " where the type mismatch is\n\n" <> (toS $ show $ quote0 τ) 
--                 <> "\n\nand\n" <> (toS $ show $ quote0 τ')
--             return m

substMetas :: Map Int Term -> Term -> Term
substMetas m t = foldr (\(i,v) t' -> substMeta i v t') t (M.toList m)

elabType0' :: Γ -> Term -> Either String (Term, Type, [(Term,Term)])
elabType0' g t = runExcept (flip evalStateT (0,0,g) $ elabType [] t)

elabType0 :: Γ -> Term -> Either String (Term, Type)
elabType0 g t = runExcept (flip evalStateT (0,0,g) $ do 
        (trm,typ,cs) <- elabType [] t
        σ <- unifyConstraints cs [] False M.empty
        let trm' = substMetas σ trm
            typ' = substMetas σ $ quote0 typ
        unless (doesNotContainMetas trm')$ throwError $ show trm' ++ " contains metas!"
        unless (doesNotContainMetas typ')$ throwError $ show typ' ++ " contains metas!"
        return $ (trm', eval typ' [])
    )

-- inferType i g (e :|@|: es) = do
--     σ <- inferType i g e
--     case σ of
--         VIΠ τ τ' -> do
--             typeOf i g es τ
--             return $ τ' (eval e' [])
--         _ ->  throwError $ "illegal application at " <> (toS $ show e) 
-- inferType i g (Const x) = case lookup (Constant x) g of
--     Just τ -> return τ
--     Nothing -> throwError $ "unknown constant " <> toS x


inferType0 :: MonadError String m => Γ -> Term -> m Type 
inferType0 = inferType 0



-- addHoles :: MonadError String m => Γ -> Term -> m Term
-- addHoles g (Π ρ ρ') = do
--     τ <- addHoles g ρ
--     τ' <- addHoles g ρ'
--     return $ Π τ τ'
-- addHoles g (IΠ ρ ρ') = do
--     τ <- addHoles g ρ
--     τ' <- addHoles g ρ'
--     return $ IΠ τ τ'
-- addHoles g (e :@: f) = do
--     σ <- inferType0 g e
--     case σ of
--         VΠ _ _ -> do
--             e' <- addHoles g e
--             f' <- addHoles g f
--             return $ e' :@: f'
--         VIΠ τ _ -> do
--             e' <- addHoles g (e :|@|: Hole (quote0 τ))
--             f' <- addHoles g f
--             return $ e' :@: f' 


-- throwError :: String -> Result a
-- throwError e = Left e

typeOf :: MonadError String m => Int -> Γ -> Term -> Type -> m () 
typeOf i g e v = do 
    v' <- inferType i g e
    unless (quote0 v == quote0 v') $ throwError $ "type mismatch in " <> (toS $ show $ e) <> " where the type mismatch is " <> (toS $ show $ quote0 v) <> "\n\nand\n" <> (toS $ show $ quote0 v')





data Decl = 
    Data Text Term [(Text, Term)]  deriving (Show, Eq, Data)
  -- | Def name (Type name) [PClause name]


codom :: Term -> Term
codom (Π _ ρ) = codom ρ
codom (IΠ _ ρ) = codom ρ
codom x = x


doesNotOccurIn :: MonadError String m => Text -> Term -> m ()
doesNotOccurIn c (Π ρ ρ') = do
    doesNotOccurIn c ρ
    doesNotOccurIn c ρ'
doesNotOccurIn c (e :@: es) =  do
    doesNotOccurIn c e
--     mapM_ (liftM fmap (doesNotOccurIn c)) es
doesNotOccurIn c (Free (Global c')) = 
    unless (c /= c') $ throwError "positivity check failed"
doesNotOccurIn _ _ = return ()


strictPositivityCheck' :: MonadError String m => Bool -> Text -> Term -> m ()
strictPositivityCheck' True c (Π ρ ρ') = do
    strictPositivityCheck False c ρ
    strictPositivityCheck True c ρ'
strictPositivityCheck' False c (Π ρ ρ') = do      --- (x : (ρ -> ρ')) -> ...
    c `doesNotOccurIn` ρ
    strictPositivityCheck' False c ρ'
strictPositivityCheck mustBeAppC c (e :@: es) = do
    strictPositivityCheck' mustBeAppC c e
--     mapM_ (liftM fmap (doesNotOccurIn c)) es
strictPositivityCheck mustBeAppC c (Free (Global c')) = 
    unless (not mustBeAppC || c == c') $ throwError "type constructor for type D x1 ... xn should have type ... -> D x1' ... xn'"
strictPositivityCheck mustBeAppC c _ = return ()


defineDecl :: MonadError String m => Int -> Γ -> Decl -> m Γ 
defineDecl i g (Data n t xs) = do
    case lookup (Global n) g of
        Just _ -> throwError $ "constant " ++ toS n ++ " already defined"
        Nothing -> do
            typeOf i g t VStar
            unless (codom t == Star) $ throwError $ toS n ++ " data declaration should have type ... -> *"
            let τ = eval t []
            g' <- defineTyCon i ((Global n,τ):g) n xs
            return $ g' ++ ((Global n,τ):g)

defineTyCon :: MonadError String m => Int -> Γ -> Text -> [(Text, Term)] -> m Γ 
defineTyCon _ _ _ [] = return []
defineTyCon i g n ((c, t):xs) = do
    g' <- defineTyCon i g n xs
    case lookup (Global c) (g ++ g') of
        Just _ -> throwError $ "constant " ++ toS c ++ " already defined"
        Nothing -> do
            typeOf i g t VStar
            strictPositivityCheck True n t
            return ((Global c,eval t []):g')

defineDecl0 :: MonadError String m => Γ -> Decl -> m Γ 
defineDecl0 = defineDecl 0


defineDecls :: MonadError String m => Γ -> [Decl] -> m Γ 
defineDecls g ds = foldM defineDecl0 g ds


-- natDecl :: Decl
-- natDecl = Data "Nat" Star [("Z", Const "Nat") , ("S", (Π (Const "Nat") (Const "Nat")))]



-- vecDecl :: Decl
-- vecDecl = Data "Vec" (Π Star (Π (Const "Nat") Star)) [
--     -- ("Nil", (Π Star ( ((Const "Vec") :@: (Bound 0)) :@: (Const "Z") ))),
--     ("Cons", 
--         (Π Star 
--             (Π (Const "Nat")
--                 (Π (Bound 1)
--                     (Π ( ((Const "Vec") :@: (Bound 2)) :@: (Bound 1) )
--                         ( (((Const "Vec") :@: (Bound 3)) :@: (  (Const "S") :@: (Bound 2)  )) )))))) ]


-- defineVec :: MonadError String m => m Γ 
-- defineVec = do
--     g <- defineDecl0 [] natDecl
--     defineDecl0 g vecDecl


-- inferNat :: MonadError String m => m Value
-- inferNat = do
--     g <- defineDecl0 [] natDecl
--     g' <- defineDecl0 g vecDecl

--     -- t <- inferType0 g (Const "S" :@: Const "Z") 
--     t <- inferType0 g' $ ((((Const "Cons") :@: (Const "Nat")) :@: Const "Z") :@: (Const "S" :@: Const "Z")) :@: (Const "Nil" :@: Const "Nat")

--     return t
--     -- inferType0 g' (quote0 t)
