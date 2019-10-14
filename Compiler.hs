{-# LANGUAGE RecursiveDo, BangPatterns, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Compiler where

import Data.List
import Control.Monad.State
import System.IO

data H = Unit | TT | FF | Z | Nil | S | P | Cons |
         At | Ifte | Iter | Pr1 | Pr2 | Fold | Bind |
         Pack | Seq | Bomb
            deriving Show

-- source language with all variables unique
data E =
    Node H [E]
  | Lam Int E
  | LetRec [(Int,E)] E
  | Var Int
  | Do String E
  | MInt Int
      deriving Show

-- target language
data A a =
    ANode H [Com]
  | AX
  | AClo Int
  | AClam a Int Com
  | ALam a
  | AInd Com
  | ADo String Com
  | AInt Int
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
toAtom :: H -> Maybe CAtom
toAtom Z    = Just CZ
toAtom Nil  = Just CNil
toAtom Bomb = Just CBomb
toAtom TT   = Just CTT
toAtom FF   = Just CFF
toAtom Unit = Just CUnit
toAtom _    = Nothing


-- compile a lambda given a closure signature it will use
compileFn :: Legend -> [V] -> E -> [A Fat]
compileFn leg0 sig body = go 0 leg0 body where
  go' :: Int -> Legend -> E -> (Com, [A Fat])
  go' there leg (Var i) = case lookup i leg of
    Just Clo -> let Just j = elemIndex i sig in (CClo j, [])
    Just Arg -> (X, [])
    Just (Local l) -> (RPlus l, [])
    Nothing -> error "variable not found (1)"
  go' there leg me@(Node h coms) = case toAtom h of
    Just atom -> (Atom atom, [])
    Nothing   -> (RPlus there, go there leg me)
  go' there leg other = (RPlus there, go there leg other)
  go :: Int -> Legend -> E -> [A Fat]
  go here leg (MInt i) = [AInt i]
  go here leg (Do name e) = (ADo name c):smoke where
    (c,smoke) = go' (here+1) leg e
  go here leg (Node h es) = case toAtom h of
    Just atom -> [AInd (Atom atom)]
    Nothing -> case es of
      [e] -> (ANode h [c]):smoke where
        (c,smoke) = go' (here+1) leg e
      [e1,e2] -> (ANode h [c1,c2]):smoke1 ++ smoke2 where
        (c1,smoke1) = go' (here+1) leg e1
        (c2,smoke2) = go' (here+length smoke1+1) leg e2
      [e1,e2,e3] -> (ANode h [c1,c2,c3]):smoke1 ++ smoke2 ++ smoke3 where
        (c1,smoke1) = go' (here+1) leg e1
        (c2,smoke2) = go' (here+length smoke1+1) leg e2
        (c3,smoke3) = go' (here+length smoke1+length smoke2+1) leg e3
  go here leg (Lam x e) = asm where
    asm = if n > 0 
      then (AClam (Fat smoke) n (RPlus (here+1))):closure
      else [ALam (Fat smoke)]
    sig' = closigFn x (map fst leg) e
    n = length sig'
    smoke = compileFn leg' sig' e
    leg' = (x,Arg) : map (fmap (const Clo)) leg
    closure = map f sig'
    f i = case lookup i leg of
      Just Clo -> let Just j = elemIndex i sig in AClo j
      Just Arg -> AX
      Just (Local l) -> AInd (RPlus l)
      Nothing -> error "variable not found (1)"
  go here leg (Var i) = case lookup i leg of
    Just Clo -> let Just j = elemIndex i sig in [AClo j]
    Just Arg -> [AX]
    Just (Local l) -> [AInd (RPlus l)]
    Nothing -> error "variable not found (2)"
  go here leg (LetRec defs e) = concat (smoke:smokes) where
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
  Node h es -> unions (map (closig leg) es)
  Var i -> case lookup i leg of
    Just Clo -> [i]
    _        -> []
  Lam x body -> closigFn x (map fst leg) body
  LetRec es e -> us \\ map fst es where
    us = closig leg' e `union` unions (map (closig leg' . snd) es)
    leg' = leg ++ map (fmap (const (Local (error "don't look!")))) es
  Do name e -> closig leg e
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

pph :: H -> String
pph h = case h of
  Unit -> "UNIT"
  TT -> "TT"
  FF -> "FF"
  Z -> "Z"
  Nil -> "NIL"
  S -> "S"
  P -> "P"
  Cons -> "CONS"
  At -> "AT"
  Ifte -> "IF"
  Iter -> "ITER"
  Pr1 -> "PR1"
  Pr2 -> "PR2"
  Fold -> "FOLD"
  Bind -> "BIND"
  Pack -> "PACK"
  Seq -> "SEQ"
  Bomb -> "BOMB"

-- pretty print the assembly code
ppasm :: A Int -> String
ppasm a = case a of
  ANode h cs -> unwords (pph h : map ppcom cs)
  AX -> "x"
  AClo i -> "clo[" ++ show i ++ "]"
  AClam i n addr -> unwords ["CLAM", show i, show n, ppcom addr]
  ALam i -> unwords ["LAM", show i]
  ADo name c -> unwords ["DO", name, ppcom c]
  AInt i -> unwords ["INT", show i]
  AInd c -> unwords ["IND", ppcom c]

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

unions xxs = foldr union [] xxs


dumpAsm :: FilePath -> [(Int,Thin)] -> IO ()
dumpAsm dirPath things = mapM_ f things where
  f (i,as) = writeFile (dirPath++"/"++show i) (unlines (map ppasm as))
  
