module Equation where

import Unify
import Natural
import Data.Maybe

data Equation a = a `Equals` a

--Problem 4
--Part a

solveEqn :: (Unifiable a) => Equation a -> Maybe (Subst a)
solveEqn (Equals x y) = unify x y

--Part b

solveSystem :: (Unifiable a) => [Equation a] -> Maybe (Subst a)
solveSystem list = foldr1 cmb [solveEqn r| r <- list, solveEqn r /= Nothing]
