----------------------------------------------------------------
-- Computer Science 320 (Fall, 2012)
-- Concepts of Programming Languages
--
-- Assignment 7
--   Exp.hs

----------------------------------------------------------------
-- Abstract Syntax for the mini-Haskell Interpreter

module Exp (Oper(..), Exp(..), subst, fv, fixExp, unique,
                     opsWithStrings, opsWithStrings2) 
  where
  
import Env

data Oper = Plus | Times 
          | Equal 
          | And | Or | Not 
          | Head | Tail | Cons
  deriving Eq

data Exp = Unit | Nil
         | N Int | B Bool | Var String | Op Oper
         | App Exp Exp
         | LamUnit Exp
         | Lam String Exp
         | If Exp Exp Exp
         | Let [(String, Exp)] Exp

----------------------------------------------------------------
-- Helper function to check whether a variable is free
-- in an expression.

fv :: String -> Exp -> Bool
fv x (Var x')      = x == x'
fv x (Lam x' e)    = if (x == x') then False else fv x e
fv x (LamUnit e)   = fv x e
fv x (App e1 e2)   = (fv x e1) || (fv x e2)
fv x (If e1 e2 e3) = (fv x e1) || (fv x e2) || (fv x e3)
fv x (Let [] be)   = fv x be
fv x (Let ((x',e):nes) be) =
  if (x == x') then 
    False 
  else
    (fv x e) || (fv x (Let nes be))
fv x _        = False ---- no free variables in primitives

----------------------------------------------------------------
-- Helper values, these are the lambda expression which are
-- equivalent to the 'fix' operator, and can be used with
-- call-by-value evaluation (the first is known as the "Z"
-- combinator, as opposed to the "Y" combinator).

fixExp = Lam "f" 
         (App (Lam "x" (App (Var "f") (Lam "y" 
                  (App (App (Var "x") (Var "x")) (Var "y")))))
              (Lam "x" (App (Var "f") (Lam "y" 
                  (App (App (Var "x") (Var "x")) (Var "y"))))))

----------------------------------------------------------------
-- Functions for Substitution

-- Assignment 7, Problem 1, Part A
noLets :: Exp -> Exp
noLets (App e1 e2)   = App (noLets e1) (noLets e2)
noLets (LamUnit e)   = LamUnit (noLets e)
noLets (Lam x e)     = Lam x (noLets e)
noLets (If e1 e2 e3) = If (noLets e1) (noLets e2) (noLets e3)

-- Note that if 'x' occurs inside its own definition, we
-- abstract it away and apply the fix operator to it. Other
-- than that, the two cases are the same.
noLets (Let ((x,e):xes) be) = 
  if fv x e then
    App (Lam x (noLets (Let xes be))) (App fixExp (Lam x e))
  else
    App (Lam x (noLets (Let xes be))) e
noLets (Let [] be) = noLets be

-- This is a catch-all for primitives ([] () int bool op var)
noLets e = e

-- Assignment 7, Problem 1, Part B
subst :: String -> Exp -> Exp -> Exp
subst x e' (Var x')     = if (x == x') then e' else Var x'
subst x e' (App e1 e2)  = App (subst x e' e1) (subst x e' e2)
subst x e' (LamUnit e)  = LamUnit (subst x e' e)
subst x e' (Lam x' e) =
  Lam x' (if (x == x') then e else (subst x e' e))
  
subst x e' (If e1 e2 e3) =
  If (subst x e' e1) (subst x e' e2) (subst x e' e3)
  
-- We avoid performing the substitution on any subexpression
-- in which an alphanumerically equivalent variable is
-- bound and obstructs the original variable we're trying to
-- substitute. This includes the current binding body, any
-- subsequent binding bodies, and the body of the entire
-- 'let' expression.
subst x e' (Let ((x',e):xes) be) =
  if (x == x') then
    Let ((x',e):xes) be
  else
    let e'' = subst x e' e
        (Let xes' be') = subst x e' (Let xes be)
    in
       Let ((x',e''):xes') be'
subst x e' (Let [] be) = Let [] (subst x e' be)

-- This is a catch-all for primitives ([] () int bool op var)
subst x  e' pe = pe

-- Assignment 7, Problem 4, Part A
unique :: [String] -> Env String -> Exp -> (Exp, [String])
unique fvs env (Var x) =
  case (findEnv x env) of
    Nothing -> (Var x, fvs)
    Just x' -> (Var x', fvs)

unique fvs env (App e1 e2) =
  let (e1', fvs') = unique fvs env e1
      (e2', fvs'') = unique fvs' env e2
  in 
     (App e1' e2', fvs'')

unique fvs env (LamUnit e)     =
  let (e', fvs') = unique fvs env e
  in
     (LamUnit e', fvs')

unique (fv:fvs') env (Lam x e) =
  let (e', fvs'') = unique fvs' (updEnv x fv env) e
  in
     (Lam fv e', fvs'')

unique fvs env (If e1 e2 e3) =
  let (e1', fvs') = unique fvs env e1
      (e2', fvs'') = unique fvs' env e2
      (e3', fvs''') = unique fvs'' env e3
  in 
     (If e1' e2' e3', fvs''')

unique (fv:fvs') env (Let ((x,e):xes) be) =
  let env' = (updEnv x fv env)
      (e', fvs'') = unique fvs' env' e
      (Let xes' be', fvs''') = unique fvs'' env' (Let xes be)
  in
     (Let ((fv,e'):xes') be', fvs''')

unique fvs env (Let [] be) =
  let (be', fvs') = unique fvs env be
  in
     (Let [] be', fvs')

-- This is a catch-all for primitives ([] () int bool op var)
unique fvs env e = (e, fvs)

----------------------------------------------------------------
-- Printing functions for Abstract Syntax

ops       = [Not, Head, Tail,
             Plus, Times, Equal, And, Or, Cons]
opStrings = ["not", "head", "tail",
             "(+)", "(*)", "(==)", "(&&)", "(||)", "(:)"]
opsWithStrings = zip ops opStrings

showOper op = fOp op opsWithStrings
  where
    fOp op ((o,n):ons) = if (o == op) then n else (fOp op ons)
    fOp op []           = "impossible"

-- Convenient list for the parser.
ops2       = [Plus, Times, Equal, And, Or, Cons]
opStrings2 = ["+)", "*)", "==)", "&&)", "||)", ":)"]
opsWithStrings2 = zip ops2 opStrings2

showExp wh Unit  = wh ++ "()"
showExp wh Nil   = wh ++ "[]"
showExp wh (N n) = wh ++ (show n)
showExp wh (B b) = wh ++ (show b)
showExp wh (Var x) = wh ++ x
showExp wh (Op o) = wh ++ (show o)
showExp wh (App e1 e2) = "(" ++ (showExp wh e1) ++ 
                         " " ++ (showExp wh e2) ++ ")"
showExp wh (LamUnit e) = "\\() -> " ++ (showExp wh e)
showExp wh (Lam x e) = "\\" ++ x ++ " -> " ++ (showExp wh e)
showExp wh (If e1 e2 e3) = "if " ++ (showExp wh e1) ++ 
                           " then " ++ (showExp wh e2) ++ 
                           " else " ++ (showExp wh e3)
showExp wh (Let xses e) = "let\n" ++ (showBinds wh xses) ++ 
                          "in \n  " ++ (showExp wh e)

showBinds wh [] = "impossible"
showBinds wh [(n, e)] = "  " ++ n ++ " = " ++ (showExp wh e) ++ "\n"
showBinds wh ((n, e):xns) = "  " ++ n ++ " = " ++ (showExp wh e) ++ 
                                 ";\n" ++ (showBinds wh xns)

instance Show Oper where
  show = showOper

instance Show Exp where
  show = showExp []
