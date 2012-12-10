module Main where

import Data.Map
import Test.HUnit.Base(assertEqual)

-- This is the Reader monad, abstracting the passing of
-- environments.
--
-- In most cases of this example, `r` is the environment type
-- `Map String Int`, `a` is the value type `Int`, and the field
-- `runReader` computes a value from an initial environment.

newtype Reader r a = Reader { runReader :: r -> a }

instance Monad (Reader r) where
  return a = Reader (const a)
  m >>= k  = Reader (\r -> runReader (k (runReader m r)) r)


-- Useful for getting the current environment.
askR :: Reader a a
askR = Reader id

-- Useful for changing the environment in a subcomputation.
localR :: (r -> b) -> Reader b a -> Reader r a
localR f m = Reader (runReader m . f)


-- Environment-based WAE interpreter using the Reader monad

data Exp = Num Int
         | Add Exp Exp
         | Mul Exp Exp
         | Id String
         | With String Exp Exp deriving Show

type Env = Map String Int

-- What `eval` computes is an instance of the monad Reader[Env, Int].
-- It has one field, `runReader`, whose meaning should be clear from
-- its type `Env => Int`.

eval :: Exp -> Reader Env Int
eval (Num n)            = return n
eval (Add lhs rhs)      = do v1 <- eval lhs
                             v2 <- eval rhs
                             return (v1 + v2)
eval (Mul lhs rhs)      = do v1 <- eval lhs
                             v2 <- eval rhs
                             return (v1 * v2)
eval (Id x)             = do env <- askR
                             return (env ! x)
eval (With x xdef body) = do xv <- eval xdef
                             localR (\env -> insert x xv env) (eval body)

-- Tests from notes on WAE.

test1 = With "x" (Num 5) (Add (Id "x") (Id "x"))
test2 = With "x" (Num 5) (Add (Id "x") (With "x" (Num 3) (Num 10)))
test3 = With "x" (Num 5) (Add (Id "x") (With "x" (Num 3) (Id "x")))
test4 = With "x" (Num 5) (Add (Id "x") (With "y" (Num 3) (Id "x")))

runTest :: Exp -> Int
runTest test = runReader (eval test) empty

main = do
  assertEqual "test1 failed" (runTest test1) 10
  assertEqual "test2 failed" (runTest test2) 15
  assertEqual "test3 failed" (runTest test3)  8
  assertEqual "test4 failed" (runTest test4) 10
  putStrLn "All tests passed."
