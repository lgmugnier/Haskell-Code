----------------------------------------------------------------
-- Computer Science 320 (Fall, 2012)
-- Concepts of Programming Languages
--
-- Assignment 8
--   Ty.hs

----------------------------------------------------------------
-- Syntax for Types for the mini-Haskell Interpreter

module Ty (typeCheck, AnnotVal(AnnotVal)) 
  where

import Exp (Exp(..), Oper(..))
import Err
import Env
import Val
import Data.Char

data Ty = TyUnit
        | TyVar String
        | TyBool
        | TyInt
        | TyBoolList
        | TyIntList
        | Arrow Ty Ty
  deriving Eq

-- Annotated values, for printing in Main
data AnnotVal = AnnotVal Val Ty
instance Show AnnotVal where
  show (AnnotVal v t) = (show v) ++ " :: " ++ (show t)

-- Useful function for transforming environment (used for
-- applying substitutions to environment).
--mapEnv :: (a -> b) -> Env a -> Env a
--mapEnv s (V ((x, t):xts)) = V ((x, (s t)) : mapEnv s xts)
--mapEnv s emptyEnv = emptyEnv

mapEnv :: (a -> b) -> Env a -> Env b
mapEnv s (V ((x, t):xts)) = case (mapEnv s (V xts)) of
								V (list) -> V ((x, (s t)) : list)
mapEnv s (V []) = (V [])

----------------------------------------------------------------
-- Canonical form

data PolyTy = ForAll [String] Ty
showVars (v:vs) = v ++ " "
showVars [v] = v
showVars [] = ""
instance Show PolyTy where
  show (ForAll [] t) = show t
  show (ForAll vs t) = "forall " ++ (showVars vs) ++ "." ++ (show t)

--canon :: Ty -> PolyTy
--Assignment 8, Problem #4 (b) Not Yet Implemented

--freevars :: Ty -> [String]
--Assignment 8, Problem #4 (a) Not Yet Implemented"]

----------------------------------------------------------------
-- This function is exported to the Main module.

-- For testing purposes, you may want to replace the
-- body of typeCheck with a call (ty0 e)

typeCheck :: Exp -> Error Ty
typeCheck e =
  case (ty emptyEnv freshTyVars e) of
    Error msg -> Error msg
    S (t, s, fv) -> S $ s t -- We apply the substitution before
                            -- returning the type.

----------------------------------------------------------------
-- Type-checking Algorithm

tyOp :: Oper -> Ty
tyOp Plus = Arrow (Arrow TyInt TyInt) TyInt
tyOp Times = Arrow (Arrow TyInt TyInt) TyInt
tyOp Equal = Arrow (Arrow TyInt TyInt) TyInt
tyOp And = Arrow (Arrow TyBool TyBool) TyBool 
tyOp Or = Arrow (Arrow TyBool TyBool) TyBool
tyOp Not = Arrow TyBool TyBool
tyOp Head = Arrow TyIntList TyInt
tyOp Tail = Arrow TyIntList TyIntList
tyOp Cons = Arrow (Arrow TyInt TyIntList) TyIntList
tyOp _ = TyVar "Error"

----------------------------------------------------------------

ty0 :: Exp -> Error Ty
ty0 Unit = S (TyUnit)
ty0 Nil = S (TyInt)
ty0 (Var s) = S (TyVar s)
ty0 (B b) = S (TyBool)
ty0 (N i) = S (TyInt)
ty0 (Op op) = S (tyOp op)
ty0 (If e1 e2 e3) = case (ty0 e1) of
						Error a -> Error "Incorrectly formated If statement"
						S (x) -> case (ty0 e2) of
									Error a -> Error "Incorrectly formated If statement"
									S (x) -> case (ty0 e3) of
												Error a -> Error "Incorrectly formated If statement"
												S(y) -> case (x == y) of
															True -> S (y)
															False -> Error "Incorrectly formated if statement"
ty0 (App e1 e2) = case (ty0 e1) of
					S (Arrow t1 t2) -> case (ty0 e2) of
										S(t3) -> case (t1 == t3) of
													True -> S (t2)
													False -> Error "Incorrectly formated App statement"
ty0 (LamUnit e) = case (ty0 e) of
					Error a -> Error "Incorrectly formated Lambda Unit statement"
					S (x)   -> S (Arrow TyUnit x)
ty0 _ = Error "ty0 Error"

----------------------------------------------------------------

ty :: Env Ty -> FreshVars -> Exp -> Error (Ty, Subst, FreshVars)

ty gamma fvs (Unit) = S (TyUnit, idsubst, fvs)
ty gamma fvs (B b) = S (TyBool, idsubst, fvs)
ty gamma fvs (N n) = S (TyInt, idsubst, fvs)
ty gamma fvs (Nil) = S (TyIntList, idsubst, fvs)
ty gamma fvs (Op p) = S ((tyOp p), idsubst, fvs)

ty gamma fvs (Var x) =
  case (findEnv x gamma) of
    Nothing -> Error $ "unbound variable " ++ x
    Just t  -> S (t, idsubst, fvs)

ty gamma fvs (If e1 e2 e3) =
  case (tys gamma fvs [e1, e2, e3]) of
    Error msg -> Error msg
    S ([t1, t2, t3], s, fvs') -> Error "Assignment 8, Problem #4 (b) Not Yet Implemented"

ty gamma fvs (App e1 e2) =
  case (tys gamma fvs [e1, e2]) of
    Error msg -> Error msg
    S ([t1, t2], s, (fv:fvs'')) ->
      case (unify (s t1) (Arrow (s t2) fv)) of
        Error msg -> Error msg
        S s'' -> S (s(s'' fv), s `o` s'', fvs'')

ty gamma (fv:fvs') (Lam x e) =
  Error "Assignment 8, Problem #4 (d) Not Yet Implemented"

ty gamma fvs (LamUnit e) =
  Error "Assignment 8, Problem #4 (c) Not Yet Implemented"

ty gamma (fv:fvs') (Let ((x,e):xes) be) =
  case (ty (updEnv x fv gamma) fvs' e) of
    Error msg       -> Error msg
    S (t, s, fvs'') -> ty (updEnv x (s t) gamma) fvs'' (Let xes be)
ty gamma fvs (Let [] be) = ty gamma fvs be

ty gamma fvs e = Error "cannot infer type"

-- This function infers the types of a list of expressions,
-- accumulating the substitutions and returning their
-- composition along with the list of types.
tys :: Env Ty -> FreshVars -> [Exp] -> Error ([Ty], Subst, FreshVars)
tys gamma fvs (e:es) =
  case (tys gamma fvs es) of
    Error msg -> Error msg
    S (ts, s, fvs') ->
      case (ty (mapEnv s gamma) fvs' e) of
        Error msg -> Error msg
        S (t, s', fvs'') -> S (t:ts, \x -> s (s' x), fvs'')
tys gamma fvs [] = S ([], idsubst, fvs)

----------------------------------------------------------------
-- Type Unification
unify :: Ty -> Ty -> Error Subst
unify (Arrow t1 t2) (Arrow t3 t4) = case (unify (s1 t1) (s1 t2)) of
										S (z) -> S (z `o` s1)
	where s1 = case (unify t2 t4) of
				S (x) -> x

----------------------------------------------------------------
-- Type Variable Substitutions

type Subst = Ty -> Ty

placeHolder :: String -> Subst
placeHolder s = \t->TyVar s

idsubst :: Subst
idsubst t0 = t0

o :: Subst -> Subst -> Subst
o s1 s2 = s1.s2

subst :: String -> Ty -> Subst
subst v t (Arrow t1 t2) = Arrow (subst v t t1) (subst v t t2)
subst v t (TyVar v2) = case (v == v2) of
						True -> t
						False -> TyVar v2

----------------------------------------------------------------
-- Infinite List of Fresh Type Variables

type FreshVars = [Ty]

freshTyVars :: FreshVars
freshTyVars = [TyVar ["x"]++[chr x] | x <- [1..]]

----------------------------------------------------------------
-- Printing functions for Syntax of Types

showTy TyUnit      = "()"
showTy (TyVar s)   = s
showTy TyBool      = "Bool"
showTy TyInt       = "Int"
showTy TyBoolList  = "[Bool]"
showTy TyIntList   = "[Int]"
-- If the left argument of an arrow is an arrow, we need to
-- add parentheses to make sure the type is not ambiguous.
showTy (Arrow (Arrow t1 t2) t3) =
   "(" ++ (showTy (Arrow t1 t2)) ++ ") -> " ++ (showTy t3)
showTy (Arrow t1 t2) =
   (showTy t1) ++ " -> " ++ (showTy t2)

instance Show Ty where
  show = showTy
