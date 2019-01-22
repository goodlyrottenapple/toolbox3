{-# LANGUAGE InstanceSigs, ScopedTypeVariables, TypeApplications, DefaultSignatures, FlexibleContexts, FlexibleInstances #-}

module SMT where

import SimpleSMT(SExpr(..), Value(..), Solver, fun, int, ackCommand)
import qualified SimpleSMT

import Data.Set(Set)
import qualified Data.Set as S
import Safe(readMay)
import Control.Monad.IO.Class
import Control.Monad.Reader

newtype SExprT a = SExprT {unwrap :: SExpr} deriving (Eq, Show)

class SMTTypeable a where
    ty :: SExprT a
    declareSExpr :: String -> SExprT a
    defineSExpr :: a -> SExprT a
    fromValue :: Value -> Maybe a
    fromSExpr :: SExpr -> Maybe a

instance SMTTypeable Integer where
    ty = SExprT $ SimpleSMT.const "Int"
    declareSExpr n = SExprT $ fun "declare-const" [ Atom n, Atom "Int" ]
    defineSExpr a = SExprT $ int a

    fromValue (Int i) = return i
    fromValue _ = Nothing


    fromSExpr (Atom i) = readMay i
    fromSExpr (List [Atom "-", Atom i]) = do
        ival <- readMay i
        return $ -ival
    fromSExpr _ = Nothing


instance SMTTypeable String where
    ty = SExprT $ SimpleSMT.const "String"

    declareSExpr n = SExprT $ fun "declare-fun" [ Atom n, List [], Atom "String" ]
    defineSExpr s = SExprT $ Atom ('"':s ++ "\"")

    fromValue (Other s) = fromSExpr s
    fromValue _ = Nothing

    fromSExpr (Atom s) = Just $ removeQuotes s
        where
            removeQuotes [] = []
            removeQuotes ('"':xs) = removeQuotes xs
            removeQuotes (x:xs) = x:removeQuotes xs
    fromSExpr _ = Nothing



instance (Ord a , SMTTypeable a) => SMTTypeable (Set a) where
    ty :: forall a. (Ord a, SMTTypeable a) => SExprT (Set a)
    ty = SExprT $ fun "Set" [unwrap $ ty @a]

    declareSExpr :: forall a. (Ord a, SMTTypeable a) => String -> SExprT (Set a)
    declareSExpr n = SExprT $ fun "declare-fun" [ Atom n, List [], unwrap $ ty @(Set a) ]


    defineSExpr :: forall a. (Ord a, SMTTypeable a) => Set a -> SExprT (Set a)
    defineSExpr s | S.null s = SExprT $ 
        fun "as" [SimpleSMT.const "emptyset", unwrap $ ty @(Set a)]
    defineSExpr s = let (x:xs) = S.toList s in
        SExprT $ fun "insert" (
            (map (unwrap . SMT.defineSExpr) xs) ++ 
            [fun "singleton" [unwrap $ SMT.defineSExpr x]])

    fromValue (Other x) = fromSExpr x
    fromValue _ = Nothing

    fromSExpr (List [Atom "as",Atom "emptyset",_]) = return $ S.empty
    fromSExpr (List [Atom "singleton",n]) = do
        nval <- fromSExpr n
        return $ S.fromList [nval]
    fromSExpr (List [Atom "union", xs, ys]) = do
        xs' <- fromSExpr xs
        ys' <- fromSExpr ys
        return $ S.union xs' ys'
    fromSExpr _ = Nothing

not :: SExprT Bool -> SExprT Bool
not p = SExprT $ fun "not" [unwrap p]

-- | Conjunction.
and :: SExprT Bool -> SExprT Bool -> SExprT Bool
and p q = SExprT $ fun "and" [unwrap p, unwrap q]

andMany :: [SExprT Bool] -> SExprT Bool
andMany xs = if null xs then SExprT $ SimpleSMT.bool True else SExprT $ fun "and" (map unwrap xs)

-- | Disjunction.
or :: SExprT Bool -> SExprT Bool -> SExprT Bool
or p q = SExprT $ fun "or" [unwrap p, unwrap q]

orMany :: [SExprT Bool] -> SExprT Bool
orMany xs = if null xs then SExprT $ SimpleSMT.bool False else SExprT $ fun "or" (map unwrap xs)

-- | Exclusive-or.
xor :: SExprT Bool -> SExprT Bool -> SExprT Bool
xor p q = SExprT $ fun "xor" [unwrap p, unwrap q]

-- | Implication.
implies :: SExprT Bool -> SExprT Bool -> SExprT Bool
implies p q = SExprT $ fun "=>" [unwrap p, unwrap q]


eq :: SExprT a -> SExprT a -> SExprT Bool
eq x y = SExprT $ SimpleSMT.eq (unwrap x) (unwrap y)


neq :: SExprT a -> SExprT a -> SExprT Bool
neq x y = SMT.not $ eq x y

-- for [a_1,...a_n] produces 
-- a_1 /= a_2 /\ ... a_1 /= a_n /\ a_2 /= a_3 /\ ... a_n-1 /= a_n
distinct :: [SExprT a] -> SExprT Bool
distinct [] = SExprT $ SimpleSMT.bool True
distinct [_] = SExprT $ SimpleSMT.bool True
distinct [a,b] = neq a b
distinct (x:xs) = andMany (distinct xs : map (neq x) xs)


-- | Greater-then
gt :: SExprT Integer -> SExprT Integer -> SExprT Bool
gt x y = SExprT $ fun ">" [unwrap x, unwrap y]

-- | Less-then.
lt :: SExprT Integer -> SExprT Integer -> SExprT Bool
lt x y = SExprT $ fun "<" [unwrap x, unwrap y]

-- | Greater-than-or-equal-to.
geq :: SExprT Integer -> SExprT Integer -> SExprT Bool
geq x y = SExprT $ fun ">=" [unwrap x, unwrap y]

-- | Less-than-or-equal-to.
leq :: SExprT Integer -> SExprT Integer -> SExprT Bool
leq x y = SExprT $ fun "<=" [unwrap x, unwrap y]


member :: SExprT a -> SExprT (Set a) -> SExprT Bool
member x y = SExprT $ fun "member" [unwrap x, unwrap y]


union :: SExprT (Set a) -> SExprT (Set a) -> SExprT (Set a)
union x y = SExprT $ fun "union" [unwrap x, unwrap y]


intersection :: SExprT (Set a) -> SExprT (Set a) -> SExprT (Set a)
intersection x y = SExprT $ fun "intersection" [unwrap x, unwrap y]


setMinus :: SExprT (Set a) -> SExprT (Set a) -> SExprT (Set a)
setMinus x y = SExprT $ fun "setminus" [unwrap x, unwrap y]


elemMinus :: SExprT (Set a) -> SExprT a -> SExprT (Set a)
elemMinus x y = SExprT $ fun "setminus" [unwrap x, fun "singleton" [unwrap y]]


complement :: SExprT (Set a) -> SExprT (Set a)
complement x = SExprT $ fun "complement" [unwrap x]


card :: SExprT (Set a) -> SExprT Integer
card x = SExprT $ fun "card" [unwrap x]


subset :: SExprT (Set a) -> SExprT (Set a) -> SExprT Bool
subset x y = SExprT $ fun "subset" [unwrap x, unwrap y]


assert :: (MonadIO m, MonadReader Solver m) => SExprT Bool -> m ()
assert e = do 
    proc <- ask
    liftIO $ SimpleSMT.assert proc (unwrap e)


define :: forall a m. (SMTTypeable a, MonadIO m, MonadReader Solver m) => SExprT a -> a -> m ()
define var a = assert (eq var (defineSExpr a))


declare :: forall a m. (SMTTypeable a, MonadIO m, MonadReader Solver m) => String -> Maybe a -> m (SExprT a)
declare n v = do
    proc <- ask
    liftIO $ ackCommand proc $ unwrap $ declareSExpr @a n
    let nexp = SExprT $ SimpleSMT.const n
    case v of 
        Just val -> define nexp val
        Nothing -> return ()
    return (SExprT $ SimpleSMT.const n)



check :: (MonadIO m, MonadReader Solver m) => m SimpleSMT.Result
check = do
    proc <- ask
    liftIO $ SimpleSMT.check proc


getExpr :: (SMTTypeable a, MonadIO m, MonadReader Solver m) => SExprT a -> m (Maybe a)
getExpr a = do
    proc <- ask
    v <- liftIO $ SimpleSMT.getExpr proc (unwrap a)
    return $ fromValue v


runCVC4 :: String -> ReaderT Solver IO a -> IO ()
runCVC4 logic m = do
    log <- SimpleSMT.newLogger 0
    smt <- SimpleSMT.newSolver "cvc4" ["--incremental", "--lang" , "smt2.0"] (Just log)
    SimpleSMT.setLogic smt logic -- "QF_UFLIAFS"

    runReaderT m smt

    SimpleSMT.stop smt
    return ()
