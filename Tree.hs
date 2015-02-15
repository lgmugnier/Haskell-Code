module Tree where

import Unify
import Maybe

data Tree = Leaf | Node Tree Tree | Var String
	deriving (Eq)

instance Substitutable Tree where
	subst s (Leaf) 		= Leaf
	subst s (Var x)		= fromJust (get s x)
	subst s (Node t1 t2)	= subst s t1
