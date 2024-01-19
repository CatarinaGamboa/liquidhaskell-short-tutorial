
Refinement Types
================

\begin{comment}
\begin{code}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
module Tutorial_03_Basic where

import Prelude hiding (abs)
divide  :: Int -> Int -> Int
die     :: String -> a

-- {-@ fail nonsense  @-}
-- {-@ fail canDie    @-}
-- {-@ fail divide'   @-}
-- {-@ fail avg       @-}
-- {-@ ignore lAssert @-}

\end{code}
\end{comment}

\newthought{What is a Refinement Type?} In a nutshell,

 > *Refinement Types* = *Types* + *Predicates*


\noindent
That is, refinement types allow us to decorate types with
*logical predicates*, which you can think of as *boolean-valued*
Haskell expressions, that constrain the set of values described
by the type. This lets us specify sophisticated invariants of
the underlying values.

Defining Types {#definetype}
--------------

Let us define some refinement types:^[You can read the type of `Zero` as:
"`v` is an `Int` *such that* `v` equals `0`" and `NonZero` as : "`v` is
an `Int` *such that* `v` does not equal `0`"]

\begin{code}
{-@ type Zero    = {v:Int | v == 0} @-}
{-@ type NonZero = {v:Int | v /= 0} @-}
\end{code}

\newthought{The Value Variable} `v` denotes the set of valid inhabitants
of each refinement type. Hence, `Zero` describes the *set of* `Int` values
that are equal to `0`, that is, the singleton set containing just `0`, and
`NonZero` describes the set of `Int` values that are *not* equal to `0`,
that is, the set `{1, -1, 2, -2, ...}` and so on.
^[We will use `@`-marked comments to write refinement
type annotations in the Haskell source file, making these
types, quite literally, machine-checked comments!]

\newthought{To use} these types we can write:

\begin{code}
{-@ zero :: Zero @-}
zero  = 0 :: Int

{-@ one, two, three :: NonZero @-}
one   = 1 :: Int
two   = 2 :: Int
three = 3 :: Int
\end{code}

Errors
------

If we try to say nonsensical things like:

\begin{code}
nonsense :: Int
nonsense = one'
  where
  {-@ one' :: Zero @-}
  one' = 1 
\end{code}

\noindent
LiquidHaskell will complain with an error message:

~~~~~{.sh}
../liquidhaskell-tutorial/src/03-basic.lhs:72:3-6: Error: Liquid Type Mismatch

72 |   one' = 1 :: Int
       ^^^^

  Inferred type
    VV : {VV : Int | VV == (1 : int)}

  not a subtype of Required type
    VV : {VV : Int | VV == 0}
~~~~~

\noindent
The message says that the expression `1 :: Int` has the type

~~~~~{.sh}
    {v:Int | v == 1}
~~~~~

\noindent
which is *not* (a subtype of) the *required* type

~~~~~{.sh}
    {v:Int | v == 0}
~~~~~

\noindent
as `1` is not equal to `0`.

Subtyping
---------

What is this business of *subtyping*? Suppose we have some more refinements of `Int`

\begin{code}
{-@ type Nat   = {v:Int | 0 <= v}        @-}
{-@ type Even  = {v:Int | v mod 2 == 0 } @-}
{-@ type Lt100 = {v:Int | v < 100}       @-}
\end{code}

\newthought{What is the type of} `zero`? `Zero` of course, but also `Nat`:

\begin{code}
{-@ zero' :: Nat @-}
zero'     = zero
\end{code}

\noindent
and also `Even`:

\begin{code}
{-@ zero'' :: Even @-}
zero''     = zero
\end{code}

\noindent
and also any other satisfactory refinement,
such as ^[We use a different names `zero'`,
`zero''` etc. as (currently) LiquidHaskell
supports *at most* one refinement type
for each top-level name.]


\begin{code}
{-@ zero''' :: Lt100  @-}
zero'''     = zero
\end{code}

\newthought{Subtyping and Implication}
`Zero` is the most precise type for `0::Int`, as it is a *subtype* of `Nat`,
`Even` and `Lt100`. This is because the set of values defined by `Zero`
is a *subset* of the values defined by `Nat`, `Even` and `Lt100`, as
the following *logical implications* are valid:

+ $v = 0 \Rightarrow 0 \leq v$
+ $v = 0 \Rightarrow v \ \mbox{mod}\ 2 = 0$
+ $v = 0 \Rightarrow v < 100$


Now let us try a new predicate.
Write a type for the numbers that represent a percentage (between 0 and 100) 
by replacing the TRUE predicate.
Then run the code, and the first example should be correct and the second should not.

\begin{code}
{-@ type Percentage = TRUE  @-}

{-@ percentT  :: Percentage  @-}
percentT    = 10 :: Int
{-@ percentF  :: Percentage  @-}
percentF :: Int
percentF    = 10 + 99 :: Int
\end{code}


\newthought{In Summary} the key points about refinement types are:

1. A refinement type is just a type *decorated* with logical predicates.
2. A term can have *different* refinements for different properties.
3. When we *erase* the predicates we get the standard Haskell types.^[Dually, a
standard Haskell type has the trivial refinement `true`. For example, `Int` is
equivalent to `{v:Int|true}`.]

Writing Specifications
----------------------

Let's write some more interesting specifications.

\newthought{Typing Dead Code} We can wrap the usual `error`
function in a function `die` with the type:

\begin{code}
{-@ die :: {v:String | false} -> a  @-}
die msg = error msg
\end{code}

The interesting thing about `die` is that the input type has the
refinement `false`, meaning the function must only be called with
`String`s that satisfy the predicate `false`.
This seems bizarre; isn't it *impossible* to satisfy `false`?
Indeed! Thus, a program containing `die` typechecks *only* when
LiquidHaskell can prove that `die` is *never called*. For example, LiquidHaskell will *accept*

\begin{code}
cannotDie = if 1 + 1 == 3
              then die "horrible death"
              else ()
\end{code}

\noindent
by inferring that the branch condition is always `False` and so `die`
cannot be called. However, LiquidHaskell will *reject*

\begin{code}
canDie = if 1 + 1 == 2
           then die "horrible death"
           else ()
\end{code}

\noindent
as the branch may (will!) be `True` and so `die` can be called.


Refining Function Types: Pre-conditions
--------------------------------------

Let's use `die` to write a *safe division* function that
*only accepts* non-zero denominators.

\begin{code}
divide'     :: Int -> Int -> Int
divide' n 0 = die "divide by zero"
divide' n d = n `div` d
\end{code}

From the above, it is clear to *us* that `div` is only
called with non-zero divisors. However, LiquidHaskell reports an
error at the call to `"die"` because, what if `divide'`
is actually invoked with a `0` divisor?

We can specify that will not happen, with a *pre-condition*
that says that the second argument is non-zero:

\begin{code}
{-@ divide :: Int -> NonZero -> Int @-}
divide _ 0 = die "divide by zero"
divide n d = n `div` d
\end{code}

\newthought{To Verify} that `divide` never calls `die`, LiquidHaskell infers
that `"divide by zero"` is not merely of type `String`, but in fact
has the the refined type `{v:String | false}` *in the context* in
which the call to `die` occurs. LiquidHaskell arrives at this conclusion by
using the fact that in the first equation for `divide` the
*denominator* is in fact

~~~~~{.sh}
    0 :: {v: Int | v == 0}
~~~~~

\noindent
which *contradicts* the pre-condition (i.e. input) type.
Thus, by contradiction, LiquidHaskell deduces that the first equation is
*dead code* and hence `die` will not be called at run-time.

\newthought{Establishing Pre-conditions}
The above signature forces us to ensure that that when we
*use* `divide`, we only supply provably `NonZero` arguments.
Hence, these two uses of `divide` are fine:

\begin{code}
avg2 x y   = divide (x + y) 2
avg3 x y z = divide (x + y + z) 3
\end{code}

<div class="hwex" id="List Average">
Consider the function `avg`:

1. Why does LiquidHaskell flag an error at `n` ?
2. How can you change the code so LiquidHaskell verifies it?

</div>

\begin{code}
avg       :: [Int] -> Int
avg xs    = divide total n
  where
    total = sum xs
    n     = length xs
\end{code}

<div>
   <button class="btn-answer" onclick="toggleCollapsible(4)"> Answer</button>
    <div id="collapsibleDiv4">
Add a case for the empty list that does not call upon divide.
    </div>
</div>



Refining Function Types: Post-conditions
---------------------------------------

Next, let's see how we can use refinements to describe the *outputs* of a
function. Consider the following simple *absolute value* function

\begin{code}
abs           :: Int -> Int
abs n
  | 0 < n     = n
  | otherwise = 0 - n
\end{code}

We can use a refinement on the output type to specify that the function
returns non-negative values

\begin{code}
{-@ abs :: Int -> Nat @-}
\end{code}

LiquidHaskell *verifies* that `abs` indeed enjoys the
above type by deducing that `n` is trivially non-negative
when `0 < n` and that in the `otherwise` case,
the value `0 - n` is indeed non-negative. ^[LiquidHaskell
is able to automatically make these arithmetic deductions
by using an [SMT solver][smt-wiki] which has built-in
decision procedures for arithmetic, to reason about the
logical refinements.]


