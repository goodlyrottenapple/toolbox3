{-# LANGUAGE InstanceSigs, ScopedTypeVariables, TypeApplications, DefaultSignatures, FlexibleContexts, FlexibleInstances #-}

module SMT where

import Control.Applicative
import Control.Monad ( join )
import Data.Maybe
import qualified Data.Traversable as T

-- import Z3.Monad


-- run :: IO ()
-- run = evalZ3 script >>= \mbSol ->
--         case mbSol of
--              Nothing  -> error "No solution found."
--              Just sol -> putStr "Solution: " >> putStrLn sol

-- script :: Z3 (Maybe String) --(Maybe [Integer])
-- script = do
--   intSet <- mkSetSort =<< mkIntSort
--   xS <- mkFreshVar "X" intSet


--   x <- mkFreshIntVar "x"
--   assert =<< mkSetMember x xS
--   yS <- mkFreshVar "Y" intSet

--   e <- mkEmptySet =<< mkIntSort
--   xsingle <- mkSetAdd e x

--   xsingleY <- mkSetUnion [xsingle, yS]
--   assert =<< mkEq xS xsingleY

--   fmap snd $ withModel $ \m -> modelToString m -- do