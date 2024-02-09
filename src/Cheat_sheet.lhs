Introduction {#intro}
============


\begin{comment}
\begin{code}
{-# LANGUAGE CPP #-}

module Cheat_sheet where
main = putStrLn "Intro"

-- {-@ ignore average @-}
-- {-@ ignore mySize @-}

\end{code}
\end{comment}

Welcome to the LiquidHaskell Short Tutorial  Cheat Sheet!

Here are the main concepts and examples you can use to complete the exercises.


Adding Specifications 
------------------------------------------
LiquidHaskell specifications in functions are written between `{-@ spec @-}`.

For example:
\begin{code}
{-@ calcPer    ::  {a:Int | a > 0} -> {b:Int | 0 <= b && b <= a} -> c:Int @-}
calcPer       :: Int -> Int -> Int
calcPer a b    = (b * 100) `div` a
\end{code}


Alias
------------------------------------------
To reuse a specification we can use aliases.

For example:
\begin{code}
{-@ type Nat      = {v:Int | 0 <= v}        @-}
{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-} 
\end{code}


Liquid types in Datatypes
------------------------------------------
To add a specification to the datatypes, first create the datatype in Haskell and 
then add the specification inside `{-@ @-}`.

For example:

1) In Haskell
\begin{code}
data Sparse a = SP { spDim   :: Int
                   , spElems :: [(Int, a)] }
\end{code}

2) Adding the LiquidHaskell specifiaction
\begin{code}
{-@ data Sparse a = SP { spDim   :: Nat
                       , spElems :: [(Btwn 0 spDim, a)]} @-}
\end{code}



Measures
------------------------------------------
Measures lift an Haskell function to the refinements logic.
It is first created as a Haskell function, sinalizing that it is 
a measure and adding liquid types to the signature. Then, it can be used
inside other refinements.

For example:

\begin{code}
{-@ measure mySize @-}
{-@ mySize :: [a] -> Nat @-}
mySize :: [a] -> Int
mySize []     = 0
mySize (_:rs) = 1 + mySize rs
\end{code}

And then, `size` can be used in:

\begin{code}
{-@ type ListN a N = {v:[a] | size v == N} @-}
\end{code}

