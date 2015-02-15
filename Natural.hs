module Natural where

import Data.Maybe
import Unify

--Problem 2
--Part a

data Natural = Zero | Succ Natural | Var String
	deriving (Eq) -- required to be of type a in Unifiable class

instance Substitutable Natural where
	subst s (Zero)	 	= Zero
	subst s (Var x) 	= fromJust (get x s)
	subst s (Succ z)	= subst s z

instance Unifiable Natural where
	unify Zero     Zero		= Just (emp)
	unify (Var x)  n 		= Just (sub x n)
	unify n        (Var x)	= Just (sub x n)
	unify (Succ y) (Succ z)	= unify y z
	unify  _       _		= Nothing

















			


