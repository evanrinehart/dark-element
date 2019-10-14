module Combination where

import Core4 (E(Ctor,Dtor))
import qualified Core4 as X
import qualified Compiler as Y

-- convert Core4 code to Compiler code so it can be compiled

-- in X all variables are bound and are either arguments or letvars
-- in Y all variables are named and unique, and only 1 kind.
-- traverse X.E with a counter to get an equivalent Y.E

convert :: Int -> X.E -> Y.E
-- next two lines probably wrong, if you want all variables to be unique
-- then when converting each subexpression you need to know how many variables
-- were used and started from there, don't start over. This means a stateful
-- mapM. Or maybe it doesn't matter.
convert m (Ctor ch es) = Y.Node (convCH ch) (map (convert m) es)
convert m (Dtor dh es) = Y.Node (convDH dh) (map (convert m) es)
convert m (X.Lam body) = Y.Lam m (convert (m+1) (X.subst (X.FV (show m)) body))
convert m (X.LetRec n es e) = Y.LetRec defs (convert (m+n) e') where
  vars = [m..m+n-1]
  strVars = map (X.FV . show) vars
  rename e = X.letsubst strVars e
  e' = rename e
  es' = map rename es
  defs = zipWith (\v e -> (v, convert (m+n) e)) vars es'
convert m (X.FV x) = case reads x of
  (i,_):_ -> Y.Var i
  [] -> error ("can't read variable " ++ x)
  
convert m (X.LamV _) = error "bug 1"
convert m (X.LetV _) = error "bug 2"

convCH ch = case ch of
  X.Star -> Y.Unit
  X.T -> Y.TT
  X.F -> Y.FF
  X.Z -> Y.Z
  X.S -> Y.S
  X.P -> Y.P
  X.Nil -> Y.Nil
  X.Cons -> Y.Cons

convDH dh = case dh of
  X.App -> Y.At
  X.Ifte -> Y.Ifte
  X.Iter -> Y.Iter
  X.Pr1 -> Y.Pr1
  X.Pr2 -> Y.Pr2
  X.Fold -> Y.Fold
