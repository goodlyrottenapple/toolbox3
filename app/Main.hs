{-# LANGUAGE 
  RecordWildCards #-}

module Main (main) where

import Lib
import Test
import LamPi(debugMode)

import Options.Applicative
import Data.Semigroup ((<>))
import Data.IORef(writeIORef)

data T3 = T3 { file :: String
             , debug :: Bool
             , printSummary :: Bool
             , smtLog :: Bool
             }

runWithOptions :: T3 -> IO ()
runWithOptions T3{..} = do
  if debug then writeIORef debugMode True else return ()
  elab printSummary smtLog file


 
main :: IO ()
main = execParser opts >>= runWithOptions
  where
    parser = T3 <$> argument str (metavar "FILE")
                <*> switch (short 'v' <>
                            long "verbose" <>
                            help "Run in verbose debug mode")
                <*> switch (short 's' <>
                            long "summary" <>
                            help "Print a summary of parsed file")
                <*> switch (short 'l' <>
                            long "smt-log" <>
                            help "Print logs from the SMT solver")
    opts = info parser mempty