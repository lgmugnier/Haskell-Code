----------------------------------------------------------------
-- Computer Science 320 (Fall, 2012)
-- Concepts of Programming Languages
--
-- Assignment 6
--   Env.hs

----------------------------------------------------------------
-- Environments

module Env (Env (..), emptyEnv, updEnv, findEnv)
  where

data Env a = V [(String, a)]
	deriving (Show)

emptyEnv = V []

updEnv :: String -> a -> Env a -> Env a
updEnv str x (V xs)     = V ((str, x) : xs)
updEnv str x (emptyEnv) = V [(str, x)]

findEnv :: String -> Env a -> Maybe a
findEnv str (V xs)
	|null list == True	= Nothing
	|otherwise	        = Just (head list)
		where list = [ y | (x, y) <- xs, x == str]
findEnv str (emptyEnv) = Nothing

