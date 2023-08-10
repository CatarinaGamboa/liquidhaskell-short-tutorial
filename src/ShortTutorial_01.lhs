Introduction {#intro}
============

\begin{comment}
\begin{code}
{-# LANGUAGE CPP #-}

module ShortTutorial_01 where
main = putStrLn "Intro"

-- {-@ ignore average @-}

\end{code}
\end{comment}

One of the amazing things about Haskell is its brainy type system that
allows one to enforce a variety of invariants at compile time, thereby
nipping in the bud a large swathe of run-time [errors](#getting-started).

Well-Typed Programs Do Go Wrong! {#gowrong}
------------------------------------------

Alas, well-typed programs *do* go quite wrong, in a variety of ways.

\newthought{Division by Zero} This innocuous function computes the average
of a list of integers:

\begin{code}
average    :: [Int] -> Int
average xs = sum xs `div` 10
\end{code}

We get the desired result on a non-empty list of numbers:

~~~~~{.ghci}
ghci> average [10, 20, 30, 40]
25
~~~~~


-- \begin{code}
-- module Demo.Lib where

-- {-@ type Pos = {v:Int | 0 < v} @-}
-- {-@ incr :: Pos -> Pos @-}
-- incr :: Int -> Int
-- incr x = x - 1
-- \end{code}