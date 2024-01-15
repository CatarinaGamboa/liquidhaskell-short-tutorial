Introduction {#intro}
============

\begin{comment}
\begin{code}
{-# LANGUAGE CPP #-}

module Tutorial_01_Introduction where
main = putStrLn "Intro"

-- {-@ ignore average @-}

\end{code}
\end{comment}

Welcome to the LiquidHaskell Short Tutorial, where you will learn the basic workings 
of LiquidHaskell and complete some exercises.
The full version of the tutorial can be found in the [project's website](https://ucsd-progsys.github.io/liquidhaskell-tutorial/Tutorial_01_Introduction.html).

One of the great things about Haskell is its brainy type system that
allows one to enforce a variety of invariants at compile time, thereby
nipping in the bud a large swathe of run-time [errors](#getting-started).

Well-Typed Programs Do Go Wrong {#gowrong}
------------------------------------------

Alas, well-typed programs *do* go quite wrong, in a variety of ways.

\newthought{Division by Zero} This innocuous function computes the average
of a list of integers:

\begin{code}
average    :: [Int] -> Int
average xs = sum xs `div` length xs
\end{code}

We get the desired result on a non-empty list of numbers:

~~~~~{.ghci}
ghci> average [10, 20, 30, 40]
25
~~~~~


a. Yes, e.g., the list [1]
b. Yes, e.g., the list []
c. No, it should not crash




-- html_quizzes/intro_1.html


^[If we call it with an empty list, we get a rather unpleasant crash: *** Exception: divide by zero. We could write `average` more *defensively*, returning
a `Maybe` or `Either` value. However, this merely kicks
the can down the road. Ultimately, we will want to extract
the `Int` from the `Maybe` and if the inputs were invalid
to start with, then at that point we'd be stuck.]



\newthought{Heart Bleeds}
For certain kinds of programs, there is a fate worse than death.
`text` is a high-performance string processing library for Haskell, that
is used, for example, to build web services.

~~~~~{.ghci}
ghci> :m +Data.Text Data.Text.Unsafe
ghci> let t = pack "Voltage"
ghci> takeWord16 5 t
"Volta"
~~~~~

A cunning adversary can use invalid, or rather,
*well-crafted*, inputs that go well outside the size of
the given `text` to read extra bytes and thus *extract secrets*
without anyone being any the wiser.

~~~~~{.ghci}
ghci> takeWord16 20 t
"Voltage\1912\3148\SOH\NUL\15928\2486\SOH\NUL"
~~~~~

The above call returns the bytes residing in memory
*immediately after* the string `Voltage`. These bytes
could be junk, or could be either the name of your
favorite TV show, or, more worryingly, your bank
account password.

Refinement Types
----------------

Refinement types allow us to enrich Haskell's type system with
*predicates* that precisely describe the sets of *valid* inputs
and outputs of functions, values held inside containers, and
so on. These predicates are drawn from special *logics* for which
there are fast *decision procedures* called SMT solvers.

\newthought{By combining types with predicates} you can specify *contracts*
which describe valid inputs and outputs of functions. The refinement
type system *guarantees at compile-time* that functions adhere to
their contracts. That is, you can rest assured that
the above calamities *cannot occur at run-time*.

\newthought{LiquidHaskell} is a Refinement Type Checker for Haskell, and in
this tutorial we'll describe how you can use it to make programs
better and programming even more fun. 

As a glimpse of what LiquidHaskell can do, the average example can be specified to inform that return needs to be different than zero, and LiquidHaskell will check if the implementation complies with it.
Run the example and read the error message.

\begin{code}
{-@ average' :: [Int] -> {v: Int | v /= 0} @-}
average'    :: [Int] -> Int
average' xs = sum xs `div` length xs
\end{code}


In this tutorial you will learn how to add and reason about
refinement types in Haskell, and how it can increase the realiability
of Haskell problems.

To get started, open the [Web Demo](http://goto.ucsd.edu:8090/index.html#?demo=blank.hs)
and see what is the result when you `Check` the code from the first example.


