module Core4 where

import Data.List (find,findIndex)
import Data.Maybe (fromJust)

-- Toy functional language. Lazy evaluation and recursive
-- bindings. Small step evaluator. Bools, Numbers, Pairs, Unit.
--
-- Type system pending.

data H = Star | T | F | Z | S | P | Nil | Cons | Inl | Inr
  deriving Show

data D = App | Ifte | Iter | Pr1 | Pr2 | Fold | Case
  deriving Show

data E =
    FV String
  | Ctor H [E] 
  | Dtor D [E]
  | Lam HoleE
  | LetRec Int [NLinkE] NLinkE
  | LamV Int
  | LetV Int
      deriving Show

eval :: E -> [E]
eval = iterate (step [])

-- do only 1 step of evaluation, guaranteed to terminate
step :: [E] -> E -> E
step env (LetV i)                    = env !! i
step env (Dtor d es)                 = destruct env d es
step env (LetRec n env' (Ctor h es)) = Ctor h (map (LetRec n env') es)
step env (LetRec n env' (Lam body))  = Lam (LetRec n env' body)
step env (LetRec n env' (FV x))      = FV x
step env (LetRec n env' e)           = LetRec n env' (step (env'++env) e)
step env e@(Ctor _ _)                = e
step env e@(Lam _)                   = e
step env e@(FV _)                    = e
step env e@(LamV _)                  = e -- impossible

-- step and destruct are mutually recursive
-- but they both recurse on structurally smaller E.
destruct :: [E] -> D -> [E] -> E

-- scrutinee has correct form, reduce!
destruct env Pr1  [Ctor P [x,_]]        = x -- pr1 (x,y) = x
destruct env Pr2  [Ctor P [_,y]]        = y -- pr2 (x,y) = y
                                            -- iter(base,f,Z)   = base
destruct env Iter [base, _, Ctor Z []]  = base 
                                            -- iter(base,f,S n) = f iter(base,f,n)
destruct env Iter [base, f, Ctor S [e]] = f @@ (Dtor Iter [base, f, e])
destruct env Ifte [x, _, Ctor F []]     = x -- ifte(x,y,F) = x
destruct env Ifte [_, y, Ctor T []]     = y -- ifte(x,y,T) = y
                                            -- (\x -> body) @ arg = body[x\arg]
destruct env App  [Lam body, arg]       = subst arg body 
destruct env Fold [base, f, Ctor Nil []]      = base
destruct env Fold [base, f, Ctor Cons [x,xs]] = f @@ x @@ (Dtor Fold [base,f,xs])
destruct env Case [f,g,Ctor Inl [e]] = f @@ e -- case(f,g,inl(e)) = f e
destruct env Case [f,g,Ctor Inr [e]] = g @@ e -- case(f,g,inr(e)) = g e

-- otherwise crunch scrutinee
destruct env Pr1  [e]                   = Dtor Pr1  [step env e]
destruct env Pr2  [e]                   = Dtor Pr2  [step env e]
destruct env Iter [base, f, e]          = Dtor Iter [base, f, step env e]
destruct env Ifte [x, y, e]             = Dtor Ifte [x, y, step env e]
destruct env App  [e1, e2]              = Dtor App  [step env e1, e2]
destruct env Fold [base, f, e]          = Dtor Fold [base, f, step env e]
destruct env Case [f,g,e]               = Dtor Case [f, g, step env e]


type HoleE = E
type NLinkE = E

-- fill a lambda-bound variable
subst :: E -> HoleE -> E
subst v e = go 0 e where
  go i e@(LamV j) | i == j    = v
                  | otherwise = e
  go i (Ctor h es)            = Ctor h (map (go i) es)
  go i (Dtor d es)            = Dtor d (map (go i) es)
  go i (Lam body)             = Lam (go (i+1) body)
  go i (LetRec n env e)       = LetRec n (map (go i) env) (go i e)
  go i e@(FV _)               = e
  go i e@(LetV _)             = e

-- replace free variable x at lambda-level i with LamV i
abstr :: String -> E -> HoleE
abstr x e = go 0 e where
  go i e@(FV y) | x == y    = LamV i
                | otherwise = e
  go i (Ctor h es)          = Ctor h (map (go i) es)
  go i (Dtor d es)          = Dtor d (map (go i) es)
  go i (Lam body)           = Lam (go (i+1) body)
  go i (LetRec n es e)      = LetRec n (map (go i) es) (go i e)
  go i e@(LetV _)           = e
  go i e@(LamV _)           = e

letsubst :: [E] -> NLinkE -> E
letsubst vars e = go 0 e where
  go j e@(LetV i)
    | i >= j    = vars !! (i - j)
    | otherwise = e
  go j (Ctor h es)        = Ctor h (map (go j) es)
  go j (Dtor d es)        = Dtor d (map (go j) es)
  go j (Lam body)         = Lam (go j body)
  go j (LetRec n es e)    = LetRec n (map (go (j+n)) es) (go (j+n) e)
  go j e@(LamV _)         = e
  go j e@(FV _)           = e

-- replace free variable x_i at let-level j with LetV (i+j)
links :: [String] -> E -> NLinkE
links xs e = go 0 e where
  go j e@(FV y) = case findIndex (== y) xs of
    Just i  -> LetV (i + j)
    Nothing -> e
  go j (Ctor h es)        = Ctor h (map (go j) es)
  go j (Dtor d es)        = Dtor d (map (go j) es)
  go j (Lam body)         = Lam (go j body)
  go j (LetRec n es e)    = LetRec n (map (go (j+n)) es) (go (j+n) e)
  go j e@(LetV _)         = e
  go j e@(LamV _)         = e

isVal :: E -> Bool
isVal (Ctor _ _)     = True
isVal (Lam _)        = True
isVal (FV _)         = True
isVal (LetRec _ _ e) = False
isVal _              = False

force :: E -> E
force = fromJust . find isVal . eval




-- code builder
star = Ctor Star []
tt = Ctor T []
ff = Ctor F []
zero = Ctor Z []
succ x = Ctor S [x]
pair x y = Ctor P [x,y]
inl x = Ctor Inl [x]
inr x = Ctor Inr [x]
nil = Ctor Nil []
cons x xs = Ctor Cons [x,xs]
x @@ y = Dtor App [x,y]
ifte x y z = Dtor Ifte [x,y,z]
pr1 x = Dtor Pr1 [x]
pr2 y = Dtor Pr2 [y]
kase f g e = Dtor Case [f,g,e]
fv x = FV x
lam x body = Lam (abstr x body)
letrec eqs e = LetRec n env e' where
  n = length eqs
  vars = map fst eqs
  defs = map snd eqs
  env = map (links vars) defs
  e' = links vars e

-- core syntax
-- * T F Z (S _) (P _ _) (\x -> _)  Nil  _:_
-- (f x y z) if(_, _, _) iter(_, _, _) pr1(_) pr2(_) fold(_,_,_)
-- let[x=_, y=_] _
