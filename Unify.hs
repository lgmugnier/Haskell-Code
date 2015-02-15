module Unify (Subst (S), sub, emp, get, Substitutable, Unifiable, subst, unify, cmb) 
	where

import Data.Maybe
import Data.List

--Part f

--Problem 1
--Part a

data Subst a = S [(String, a)]
	deriving (Show, Eq)

--Part b

emp = S []

sub :: String -> a -> Subst a
sub str x = S [(str, x)]

--Part c

get :: String -> Subst a -> Maybe a
get str (emp) = Nothing
get str (S ((str1, x):xs))
	|str == str1	= Just x
	|otherwise	= get str (S xs)

--Part d

class Substitutable a where
	subst :: Subst a -> a -> a

--Part e

class (Eq a, Substitutable a) => Unifiable a where
	unify :: a -> a -> Maybe (Subst a)

--Problem 3
--Part a
--added qualifyer "Eq a"
unresolved :: Eq a => [(String, a)] -> Maybe (String, a, a)
unresolved [] = Nothing
unresolved list 
	|length l1 == 0			= unresolved (tail list)
	|(head l2) == (last l2)	= Nothing
	|otherwise 				= Just ((fst (head list), head l2, last l2))
		where 	
			l1 = [x| x <- (tail list), (fst x) == (fst (head list))]
			l2 = snd (head list) : [snd y| y <- l1, snd y /= snd (head list)]

--Part b
resolve :: Unifiable a => Subst a -> Maybe (Subst a)
resolve (S subList)
	|unresolved subList == Nothing	= Just (S subList)
	|unify b c == Nothing			= Nothing
	|otherwise						= resolve newList
		where 
			(a, b, c) = fromJust (unresolved subList)
			S (r) = fromJust (unify b c)
			temp = delete (a, b) subList
			newList = S (r ++ subList)

--Part c
cmb:: Unifiable a => Maybe (Subst a) -> Maybe (Subst a) -> Maybe (Subst a) 
cmb  _        (Nothing) = Nothing
cmb (Nothing)  _ 		= Nothing
cmb (Nothing) (Nothing) = Nothing
cmb x y = resolve (S (sub1 ++ sub2))
	where 
		(S sub1) = fromJust x
		(S sub2) = fromJust y





