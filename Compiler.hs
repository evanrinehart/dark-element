{-# LANGUAGE RecursiveDo, BangPatterns, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Compiler where

import Data.List
import Control.Monad.State

unions xxs = foldr union [] xxs

-- source language with all variables unique
data E =
  Unit | TT | FF | Z | S E | P E E | Nil | Cons E E |
  At E E | Ifte E E E | Iter E E E | Pr1 E | Pr2 E |
  Fold E E E | Var Int | Lam Int E | LetRec [(Int,E)] E |
  Bind E E | Do String E | Bomb | Seq E E | Pack E | MInt Int
    deriving Show

-- target language
data A a =
  AP Com Com | AS Com | ACons Com Com | AAt Com Com | APr1 Com |
  APr2 Com | AIfte Com Com Com | AIter Com Com Com | AFold Com Com Com |
  ABind Com Com | ADo Com Com | APack Com | ASeq Com Com |
  AX | AClo Int | ALam Int a Com | AInd Com | AAtom CAtom
    deriving (Show,Functor,Foldable,Traversable)

data Com = Imm Int | RPlus Int | FFI String | Atom CAtom | CClo Int | X
  deriving Show

data CAtom = CUnit | CTT | CFF | CZ | CNil | CBomb
  deriving Show

newtype Fat = Fat [A Fat] deriving Show -- nested assembly
type Thin = [A Int]                     -- flat assembly

-- the Legend tells you generally where a variable is
type Legend = [(V,Loc)]
data Loc = Arg | Clo | Local Int deriving Show
type V = Int


-- atom symbols that can appear directly in an instruction
toAtom :: E -> Maybe CAtom
toAtom Z    = Just CZ
toAtom Nil  = Just CNil
toAtom Bomb = Just CBomb
toAtom TT   = Just CTT
toAtom FF   = Just CFF
toAtom Unit = Just CUnit
toAtom _    = Nothing


-- compile a lambda give a closure signature it will use
compileFn :: Legend -> [V] -> E -> [A Fat]
compileFn leg0 sig body = go 0 leg0 body where
  go' there leg e0 = case toAtom e0 of
    Just atom -> (Atom atom, [])
    Nothing   -> case e0 of
      Var i -> case lookup i leg of
        Just Clo -> let Just j = elemIndex i sig in (CClo j, [])
        Just Arg -> (X, [])
        Just (Local l) -> (RPlus l, [])
        Nothing -> error "variable not found (1)"
      _ -> (RPlus there, go there leg e0)
  go here leg e0 = case toAtom e0 of
    Just atom -> [AInd (Atom atom)]
    _ -> case e0 of
      S e -> (AS c):smoke where
        (c,smoke) = go' (here+1) leg e
      Pr1 e -> (APr1 c):smoke where
        (c,smoke) = go' (here+1) leg e
      Pr2 e -> (APr2 c):smoke where
        (c,smoke) = go' (here+1) leg e
      Pack e -> (APack c):smoke where
        (c,smoke) = go' (here+1) leg e
      P e1 e2 -> (AP c1 c2):smoke1 ++ smoke2 where
        (c1,smoke1) = go' (here+1) leg e1
        (c2,smoke2) = go' (here+length smoke1+1) leg e2
      Cons e1 e2 -> (ACons c1 c2):smoke1 ++ smoke2 where
        (c1,smoke1) = go' (here+1) leg e1
        (c2,smoke2) = go' (here+length smoke1+1) leg e2
      At e1 e2 -> (AAt c1 c2):smoke1 ++ smoke2 where
        (c1,smoke1) = go' (here+1) leg e1
        (c2,smoke2) = go' (here+length smoke1+1) leg e2
      Bind e1 e2 -> (ABind c1 c2):smoke1 ++ smoke2 where
        (c1,smoke1) = go' (here+1) leg e1
        (c2,smoke2) = go' (here+length smoke1+1) leg e2
      Seq e1 e2 -> (ASeq c1 c2):smoke1 ++ smoke2 where
        (c1,smoke1) = go' (here+1) leg e1
        (c2,smoke2) = go' (here+length smoke1+1) leg e2
      Fold e1 e2 e3 -> (AFold c1 c2 c3):smoke1 ++ smoke2 ++ smoke3 where
        (c1,smoke1) = go' (here+1) leg e1
        (c2,smoke2) = go' (here+length smoke1+1) leg e2
        (c3,smoke3) = go' (here+length smoke1+length smoke2+1) leg e3
      Iter e1 e2 e3 -> (AIter c1 c2 c3):smoke1 ++ smoke2 ++ smoke3 where
        (c1,smoke1) = go' (here+1) leg e1
        (c2,smoke2) = go' (here+length smoke1+1) leg e2
        (c3,smoke3) = go' (here+length smoke1+length smoke2+1) leg e3
      Ifte e1 e2 e3 -> (AIfte c1 c2 c3):smoke1 ++ smoke2 ++ smoke3 where
        (c1,smoke1) = go' (here+1) leg e1
        (c2,smoke2) = go' (here+length smoke1+1) leg e2
        (c3,smoke3) = go' (here+length smoke1+length smoke2+1) leg e3
      Do name e -> (ADo (FFI name) c):smoke where
        (c,smoke) = go' (here+1) leg e
      Lam x e -> (ALam n (Fat smoke) clAddr):closure where
        sig' = closigFn x (map fst leg) e
        n = length sig'
        clAddr = if n > 0 then RPlus (here+1) else Atom CBomb
        smoke = compileFn leg' sig' e
        leg' = (x,Arg) : map (fmap (const Clo)) leg
        closure = map f sig'
        f i = case lookup i leg of
          Just Clo -> let Just j = elemIndex i sig in AClo j
          Just Arg -> AX
          Just (Local l) -> AInd (RPlus l)
          Nothing -> error "variable not found (1)"
      Var i -> case lookup i leg of
        Just Clo -> let Just j = elemIndex i sig in [AClo j]
        Just Arg -> [AX]
        Just (Local l) -> [AInd (RPlus l)]
        Nothing -> error "variable not found (2)"
      LetRec defs e -> concat (smoke:smokes) where
        smoke = go here leg' e
        es = map snd defs
        vars = map fst defs
        start = length smoke --magic
        layout = scanl (+) start (map length smokes) --magic
        smokes = zipWith (\n e -> go (here+n) leg' e) layout es
        leg' = leg ++ zipWith (\v n -> (v,Local (here+n))) vars layout



-- determine a closure signature for a lambda in an environment
closigFn :: Int -> [Int] -> E -> [V]
closigFn x env body = closig ((x,Arg):map (\i->(i,Clo)) env) body \\ [x]

-- we use a legend with wrong local locations but the locations aren't used
closig :: Legend -> E -> [V]
closig leg e0 = case e0 of
  S e -> closig leg e
  Pr1 e -> closig leg e
  Pr2 e -> closig leg e
  Do _ e -> closig leg e
  Pack e -> closig leg e
  P e1 e2 -> closig leg e1 `union` closig leg e2
  Cons e1 e2 -> closig leg e1 `union` closig leg e2
  At e1 e2 -> closig leg e1 `union` closig leg e2
  Bind e1 e2 -> closig leg e1 `union` closig leg e2
  Seq e1 e2 -> closig leg e1 `union` closig leg e2
  Fold e1 e2 e3 -> unions (map (closig leg) [e1,e2,e3])
  Iter e1 e2 e3 -> unions (map (closig leg) [e1,e2,e3])
  Ifte e1 e2 e3 -> unions (map (closig leg) [e1,e2,e3])
  Var i -> case lookup i leg of
    Just Clo -> [i]
    _        -> []
  Lam x body -> closigFn x (map fst leg) body
  LetRec es e -> us \\ map fst es where
    us = closig leg' e `union` unions (map (closig leg' . snd) es)
    leg' = leg ++ map (fmap (const (Local (error "don't look!")))) es
  _ -> []
  
  
-- thinning out the compiled code
thinFn :: [A Fat] -> State [(Int,Thin)] (Int, Thin)
thinFn as = do
  myId <- gets length
  rec
    modify ((myId,bs):)
    bs <- mapM thin as
  return (myId,bs)

thin :: A Fat -> State [(Int,Thin)] (A Int)
thin a = sequence (fmap f a) where
  f (Fat as) = do
    (i,_) <- thinFn as
    return i  

-- pretty print the assembly code
ppasm :: A Int -> String
ppasm a = case a of
  AS c -> unwords ["S", ppcom c]
  APr1 c -> unwords ["PR1", ppcom c]
  APr2 c -> unwords ["PR2", ppcom c]
  AInd c -> unwords ["IND", ppcom c]
  APack c -> unwords ["PACK", ppcom c]
  AP c1 c2 -> unwords ["P", ppcom c1, ppcom c2]
  ACons c1 c2 -> unwords ["CONS", ppcom c1, ppcom c2]
  AAt c1 c2 -> unwords ["AT", ppcom c1, ppcom c2]
  ABind c1 c2 -> unwords ["BIND", ppcom c1, ppcom c2]
  ADo c1 c2 -> unwords ["DO", ppcom c1, ppcom c2]
  ASeq c1 c2 -> unwords ["SEQ", ppcom c1, ppcom c2]
  AIfte c1 c2 c3 -> unwords ("IF":map ppcom [c1,c2,c3])
  AIter c1 c2 c3 -> unwords ("ITER":map ppcom [c1,c2,c3])
  AFold c1 c2 c3 -> unwords ("FOLD":map ppcom [c1,c2,c3])
  AX -> "x"
  AClo i -> "clo[" ++ show i ++ "]"
  ALam x i addr -> unwords ["LAM", show x, show i, ppcom addr]
  AAtom atom -> ppatom atom

ppatom :: CAtom -> String
ppatom CUnit = "UNIT"
ppatom CTT = "T"
ppatom CFF = "F"
ppatom CZ = "Z"
ppatom CNil = "NIL"
ppatom CBomb = "BOMB"

ppcom :: Com -> String
ppcom (Imm i) = show i
ppcom (RPlus i) = "r+" ++ show i
ppcom (FFI name) = name
ppcom (Atom atom) = ppatom atom
ppcom (CClo i) = "clo[" ++ show i ++ "]"
ppcom X = "x"
