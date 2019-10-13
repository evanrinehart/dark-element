{-# LANGUAGE OverloadedStrings #-}
module Driver where

import Control.Monad.State
import Data.Text.IO
import Text.Megaparsec
import Parser
import Core4
import Combination
import Compiler

drive :: FilePath -> IO ()
drive path = do
  raw <- Data.Text.IO.readFile path
  case runParser parser path raw of
    Left errorBundle -> print errorBundle
    Right e -> do
      print e
      let e' = convert 0 e
      print e'
      let asm = compileFn [] [] (Compiler.Lam (-1) e')
      print asm
      let table = execState (thinFn asm) []
      print table
      dumpAsm "outdir" table
