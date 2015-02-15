----------------------------------------------------------------
-- Computer Science 320 (Fall, 2012)
-- Concepts of Programming Languages
--
-- Assignment 7
--   Eval.hs

----------------------------------------------------------------
-- Evaluation for mini-Haskell

module Eval (evalExp) where

import Env
import Err
import Exp
import Val

----------------------------------------------------------------
-- This function is exported to the Main module.

-- Assignment 6, Problem 3, Part C
-- Assignment 7, Problem 4, Part B
evalExp :: Exp -> Error Val
evalExp e =
  let freshvars n = ("v"++(show n)):(freshvars (n+1))
      (e', _) = unique (freshvars 0) emptyEnv e
  in
     -- One of two evaluation functions can be called
     -- below.
     ev0 e
     --ev e emptyEnv

----------------------------------------------------------------
-- Functions for evaluating operations applied to values.

-- Assignment 6, Problem 1, Part A
appOp :: Oper -> Val -> Error Val
appOp Not  (VB b) = S (VB (not b))
appOp Head (VListBool (b:bs)) = S (VB b)
appOp Head (VListInt  (n:ns)) = S (VN n)
appOp Tail (VListBool (b:bs)) = S (VListBool bs)
appOp Tail (VListInt  (n:ns)) = S (VListInt  ns)
appOp Head _ = Error "head applied to an empty list"
appOp Tail _ = Error "tail applied to an empty list"
appOp Not  _ = Error "not applied to non-boolean"
appOp op v2 = S (Partial op v2)

-- Assignment 6, Problem 1, Part B
appBinOp :: Oper -> Val -> Val -> Error Val
appBinOp Plus  (VN n) (VN n') = S $ VN (n + n')
appBinOp Times (VN n) (VN n') = S $ VN (n * n')
appBinOp Equal (VN n) (VN n') = S $ VB (n == n')
appBinOp Equal (VB b) (VB b') = S $ VB (b == b')
appBinOp And   (VB b) (VB b') = S $ VB (b && b')
appBinOp Or    (VB b) (VB b') = S $ VB (b || b')
appBinOp Cons  (VB b) (VListBool bs) = S $ VListBool (b:bs)
appBinOp Cons  (VN n) (VListInt ns)  = S $ VListInt (n:ns)
appBinOp Cons  (VB b) VNil           = S $ VListBool (b:[])
appBinOp Cons  (VN n) VNil           = S $ VListInt (n:[])
appBinOp op v v' =
  Error $ "binary operator " 
           ++ (show op) 
           ++ "not defined on arguments " 
           ++ (show v) ++ " and " ++ (show v')

----------------------------------------------------------------
-- Function for applying one value to another.

-- Assignment 6, Problem 1, Part C; Problem 3, Part A
appVals :: Val -> Val -> Error Val
appVals (VOp op)         v2     = appOp op v2
appVals (Partial op v1 ) v2     = appBinOp op v1 v2
appVals (VLamUnit e env) VUnit  = ev e env
appVals (VLam x e env)   v2     = ev e (updEnv x v2 env)
appVals v1 v2 = Error $ (show v1)
                        ++ " cannot be applied to " ++ (show v2)

-- Assignment 7, Problem 2, Part A
-- We are careful to avoid evaluating the second argument
-- wherever it is unnecessary to do so (as specified by the
-- call-by-name evaluation rules).
appValExp :: Val -> Exp -> Error Val
appValExp (VOp op) e2 =
  case ev0 e2 of
    S v2      -> appVals (VOp op) v2
    Error msg -> Error msg

appValExp (Partial Or  (VB True )) e2 = S (VB True)
appValExp (Partial And (VB False)) e2 = S (VB False)
appValExp (Partial op  v1)         e2 =
  case ev0 e2 of
    S v2      -> appVals (Partial op v1) v2
    Error msg -> Error msg

-- Here, for unit lambda abstractions, we don't evaluate
-- the second argument; for variable lambda abstractions,
-- we perform the substitution, then evaluate the result
-- of the substitution.
appValExp (VLamUnit e env) e2 = ev0 e
appValExp (VLam x   e env) e2 = ev0 (subst x e2 e)
appValExp v1 e2 = Error $ (show v1)
                          ++ " cannot be applied to an argument"

----------------------------------------------------------------
-- Function for evaluating an expression with no bindings or
-- variables to a value.

-- Assignment 7, Problem 2, Part B
ev0 :: Exp -> Error Val
ev0 Unit    = S VUnit
ev0 Nil     = S VNil
ev0 (N n)   = S (VN n)
ev0 (B b)   = S (VB b)
ev0 (Op op) = S (VOp op)
ev0 (Var x) = Error $ "ev0 should not encounter a variable," 
                    ++ "substitution has not been performed"
                    ++ "properly"

ev0 (App e1 e2) =
  case (ev0 e1) of
    Error err -> Error err
    S v1      -> appValExp v1 e2

ev0 (LamUnit e) = S $ VLamUnit e emptyEnv
ev0 (Lam x e)   = S $ VLam x e emptyEnv

ev0 (If e1 e2 e3) =
  case (ev0 e1) of
    S (VB c)  -> if c then ev0 e2 else ev0 e3
    S _       -> Error "'if' condition not a boolean"
    Error err -> Error err

-- Once again, a simple recursive definition is handled by
-- checking whether the variable being bound is found inside
-- the body of its definition, and if it is, the definition
-- is wrapped so that the variable is abstracted out, and
-- 'fix' is applied to this new lambda abstraction.
ev0 (Let ((x,e):xes) be) =
  if fv x e then
    ev0 (subst x (App fixExp (Lam x e)) (Let xes be)) 
  else
    ev0 (subst x e (Let xes be))
ev0 (Let [] be) = ev0 be

----------------------------------------------------------------
-- Function for evaluating an expression to a value. Note the
-- need for an environment to keep track of variables.

-- Assignment 7, Problem 3, Part A
-- Because the original version of appValExp ignores
-- environments, we provide an alternative version which calls
-- 'ev' instead of 'ev0' and keeps track of environments.
appValExp' :: Val -> Exp -> Env Val -> Error Val
appValExp' (VOp op) e2 env =
  case ev e2 env of
    S v2      -> appVals (VOp op) v2
    Error msg -> Error msg

appValExp' (Partial Or  (VB True )) e2 env = S (VB True)
appValExp' (Partial And (VB False)) e2 env = S (VB False)
appValExp' (Partial op  v1)         e2 env =
  case ev e2 env of
    S v2      -> appVals (Partial op v1) v2
    Error msg -> Error msg

-- Here, for unit lambda abstractions, we don't evaluate
-- the second argument; for variable lambda abstractions,
-- we evaluate as usual. Note that we ignore the environment
-- which is supplied as an argument to appValExp', and use
-- only the environments inside the lambda closures.
appValExp' (VLamUnit e env) e2 env' = ev e env
appValExp' (VLam x   e env) e2 env' = 
  ev (subst x (App (Var x) Unit) e) (updEnv x (VLamUnit e2 env') env)
appValExp' v1 e2 env = Error $ (show v1)
                          ++ " cannot be applied to an argument"

-- In the definition of ev, we are careful to call
-- appValExp' instead of appValExp.
ev :: Exp -> Env Val -> Error Val
ev Unit    env = S VUnit
ev Nil     env = S VNil
ev (N n)   env = S (VN n)
ev (B b)   env = S (VB b)
ev (Op op) env = S (VOp op)

ev (Var x) env =
  case (findEnv x env) of
    Just x' -> S x'
    Nothing -> Error $ "unbound variable: " ++ x

ev (App e1 e2) env =
  case (ev e1 env) of
    Error err -> Error err
    S v1 -> appValExp' v1 e2 env

-- Notice in these cases how we store the current
-- environment inside the closure. If the closure is
-- applied to an argument at any other point, this
-- environment can then be used to evaluate
-- the body of the lambda abstraction.
ev (Lam x e)   env = S (VLam x e env)
ev (LamUnit e) env = S (VLamUnit e env)

ev (If e1 e2 e3) env =
  case (ev e1 env) of
    S (VB c)  -> if c then ev e2 env else ev e3 env
    S _       -> Error "'if' condition not a boolean"
    Error err -> Error err

-- There are two cases here, the first occurs if the
-- variable being bound does not occur in its own
-- definition. In the second case, we must abstract
-- over the variable and apply 'fix' to this abstraction,
-- as specified in the evaluation rules.

-- Note again that we bind 'x' to a thunk, substitute all
-- occurrences of x with (x ()), and evaluate under the
-- newly extended environment. In the second case, the
-- substitution must also be applied to the body of the
-- binding definition, but not before 'fix' has been
-- applied. The reasoning here is that the recursive
-- definition implies an instance of 'fix', and this is
-- independent of our creation of a thunk (which is merely
-- the result of restricting our environment to Val and not
-- Exp).
ev (Let ((x,e):nes) be) env =
  if not (fv x e) then
    ev (subst x (App (Var x) Unit) (Let nes be)) 
       (updEnv x (VLamUnit e env) env)
  else
    let thunk = VLamUnit (App fixExp (Lam x e)) env
    in 
       ev (subst x (App (Var x) Unit) (Let nes be)) 
          (updEnv x thunk env)
ev (Let [] be) env = ev be env
