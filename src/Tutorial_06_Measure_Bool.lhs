
Boolean Measures {#boolmeasures}
================


In the last two chapters, we saw how refinements could be used to
reason about the properties of basic `Int` values like vector
indices, or the elements of a list. Next, let's see how we can
describe properties of aggregate structures like lists and trees,
and use these properties to improve the APIs for operating over
such structures.

\begin{comment}
\begin{code}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}


module Tutorial_06_Measure_Bool where

import Prelude hiding(foldl, foldl1, map, sum, head, tail, null)

main = putStrLn "Hello"

-- | Old Definitions

{-@ type Nat     = {v:Int | 0 <= v} @-}
{-@ type Pos     = {v:Int | 0 <  v} @-}
{-@ type NonZero = {v:Int | 0 /= v} @-}

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg

-- Type Definitions
divide     :: Int -> Int -> Int
size1, size2 :: [a] -> Int

-- {-@ ignore avgMany  @-}
-- {-@ ignore average' @-}
-- {-@ ignore size1    @-}
-- {-@ ignore size2    @-}
-- {-@ ignore safeHead @-}
-- {-@ ignore sumBad   @-}
-- {-@ ignore wtAverage @-}
-- {-@ ignore risers    @-}

\end{code}
\end{comment}


Partial Functions
------------------

As a motivating example, let us return to the problem of ensuring
the safety of division. Recall that we wrote:

\begin{code}
{-@ divide :: Int -> NonZero -> Int @-}
divide _ 0 = die "divide-by-zero"
divide x n = x `div` n
\end{code}

\newthought{The Precondition} asserted by the input type `NonZero`
allows LiquidHaskell to prove that the `die` is *never* executed at
run-time, but consequently, requires us to establish that wherever
`divide` is *used*, the second parameter be provably non-zero.
This requirement is not onerous when we know what the
divisor is *statically*

\begin{code}
avg2 x y   = divide (x + y)     2

avg3 x y z = divide (x + y + z) 3
\end{code}

\noindent However, it can be more of a challenge when the divisor
is obtained *dynamically*. For example, let's write a function to
find the number of elements in a list

\begin{code}
size        :: [a] -> Int
size []     =  0
size (_:xs) =  1 + size xs
\end{code}

\noindent and use it to compute the average value of a list:

\begin{code}
avgMany xs = divide total elems
  where
    total  = sum  xs
    elems  = size xs
\end{code}

Uh oh. LiquidHaskell wags its finger at us!

~~~~~{.liquiderror}
     src/04-measure.lhs:77:27-31: Error: Liquid Type Mismatch
       Inferred type
         VV : Int | VV == elems

       not a subtype of Required type
         VV : Int | 0 /= VV

       In Context
         VV    : Int | VV == elems
         elems : Int
~~~~~

\newthought{We cannot prove} that the divisor is `NonZero`,
because it *can be* `0` -- when the list is *empty*. Thus, we
need a way of specifying that the input to `avgMany` is indeed
non-empty!

Lifting Functions to Measures {#usingmeasures}
-----------------------------

\newthought{How} shall we tell LiquidHaskell that a list is *non-empty*?
Recall the notion of `measure` previously [introduced](#vectorbounds)
to describe the size of a `Data.Vector`. In that spirit, let's write
a function that computes whether a list is not empty:

\begin{code}
notEmpty       :: [a] -> Bool
notEmpty []    = False
notEmpty (_:_) = True
\end{code}

\newthought{A measure} is a *total* Haskell function,

1. With a *single* equation per data constructor, and
2. Guaranteed to *terminate*, typically via structural recursion.

\noindent
We can tell LiquidHaskell to *lift* a function meeting
the above requirements into the refinement logic by declaring:

\begin{code}
{-@ measure notEmpty @-}
\end{code}


\newthought{Non-Empty Lists} can now be described as
the *subset* of plain old Haskell lists `[a]` for which
the predicate `notEmpty` holds

\begin{code}
{-@ type NEList a = {v:[a] | notEmpty v} @-}
\end{code}

We can now refine various signatures to establish the safety of
the list-average function.

\newthought{Size} returns a non-zero value *if* the input list is
not-empty. We capture this condition with an [implication](#semantics)
in the output refinement.

\begin{code}
{-@ size :: xs:[a] -> {v:Nat | notEmpty xs => v > 0} @-}
\end{code}

\newthought{Average} is only sensible for non-empty lists.
Add a specification to average using the type NEList.

\begin{code}
{-@ average :: NEList Int -> Int @-}
average xs = divide total elems
  where
    total  = sum xs
    elems  = size xs
\end{code}



<div>
   <button class="btn-answer" onclick="toggleCollapsible(6)"> Answer</button>
    <div id="collapsibleDiv6">
`{-@ average :: NEList Int -> Int @-}`
</div>

<div class="hwex" id="Debugging Specifications">
An important aspect of formal verifiers like LiquidHaskell
is that they help establish properties not just of your *implementations*
but equally, or more importantly, of your *specifications*. In that spirit,
can you explain why the following two variants of `size` are *rejected*
by LiquidHaskell?
</div>

\begin{code}
{-@ size1    :: xs:NEList a -> Pos @-}
size1 []     =  0
size1 (_:xs) =  1 + size1 xs

{-@ size2    :: xs:[a] -> {v:Int | notEmpty xs => v > 0} @-}
size2 []     =  0
size2 (_:xs) =  1 + size2 xs
\end{code}


\noindent
Of course, we can do a lot more with measures, so let's press on!



