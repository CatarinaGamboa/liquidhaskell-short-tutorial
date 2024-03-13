
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
{-@ die :: {v:String | false} -> a  @-}
die msg = error msg


-- {-@ fail nonsense  @-}
-- {-@ fail canDie    @-}
-- {-@ fail divide'   @-}
-- {-@ fail avg       @-}
-- {-@ fail percentT  @-}
-- {-@ fail percentF  @-}
-- {-@ fail cpc  @-}
-- {-@ fail cpi  @-}
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

Let us define some refinement types:

\begin{code}
{-@ type Zero    = {v:Int | v == 0} @-}
{-@ type NonZero = {v:Int | v /= 0} @-}
\end{code}

\newthought{The Value Variable} `v` denotes the set of valid inhabitants
of each refinement type. Hence, `Zero` describes the *set of* `Int` values
that are equal to `0`, that is, the singleton set containing just `0`, and
`NonZero` describes the set of `Int` values that are *not* equal to `0`,
that is, the set `{1, -1, 2, -2, ...}` and so on.

To indicate that these specifications are for LiquidHaskell we write them like `{-@ spec @-}`.

\newthought{Now, to use} these types we can write:

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
{-@ type Nat      = {v:Int | 0 <= v}        @-}
{-@ type Positive = {v:Int | 0 < v}         @-}
{-@ type Even     = {v:Int | v mod 2 == 0 } @-}
{-@ type TensToHundred = {v:Int | v mod 10 == 0 && v <= 100}         @-}

\end{code}

\newthought{Subtyping and Implication}
`Zero` is the most precise type for `0::Int`, as it is a *subtype* of `Nat`,
`Even`. However, it is not a subtype of `Positive`.
The alias `TensToHundred` represents the multiples of 10 smaller than 100,
meaning that `Even` is a *subtype* of it but all the other ones are not. 

<div class = "interact">
<b>Exercise:</b>
Now let us try a new predicate.

Write a type `Percentage` for the numbers that represent a percentage (between 0 and 100).

Then, remove the comment the liquid type signatures and run the code. 
The first example should be correct and the second should not.

\begin{code}
-- write the alias here

-- {-@ percentT  :: Percentage  @-}
percentT    = 10 :: Int
-- {-@ percentF  :: Percentage  @-}
percentF :: Int
percentF    = 10 + 99 :: Int
\end{code}

<div>
   <button class="btn-answer" onclick="toggleCollapsible(1)"> Answer</button>
    <div id="collapsibleDiv1">
`{-@ type Percentage = {v:Int | 0 <= v && v <= 100}  @-}`
    </div>
</div>



</div>

\newthought{In Summary} the key points about refinement types are:

1. A refinement type is just a type *decorated* with logical predicates.
2. A term can have *different* refinements for different properties.
3. When we *erase* the predicates we get the standard Haskell types.

Writing Specifications
----------------------

We can also add specifications as pre- and post-conditions of functions.

Remember the divide function from before? We can add the case of dividing by zero
with this `die "message"` to indicate that this case should be handled before
running the code.

\begin{code}
divide'     :: Int -> Int -> Int
divide' n 0 = die "divide by zero"
divide' n d = n `div` d
\end{code}

So, now we can specify that the first case will never with a *pre-condition*
that says that the second argument is non-zero:

\begin{code}
{-@ divide :: Int -> NonZero -> Int @-}
divide _ 0 = die "divide by zero"
divide n d = n `div` d
\end{code}

You can run the both pieces of code and check that the first one
throws an error while the second one does not since it can infer that
the first case will not be called.

\newthought{Establishing Pre-conditions}
The above signature forces us to ensure that that when we
*use* `divide`, we only supply provably `NonZero` arguments.


<div class="interact" id="question1" style="width=640px;border= 2px solid #3498db; border-radius= 10px;">
   <b> Exercise:</b>
   <p>Select which of the following functions that call divide would <b>raise an error:</b> </p>
   <label class="container"> foo x y   = divide (x + y) 2 <input type="radio" name="q3" value="1"> <span class="checkmark"></span> </label><br>
   <label class="container"> foo' x y z = divide (divide (x + y) 3) 10 <input type="radio" name="q3" value="2"><span class="checkmark"></span> </label><br>
   <label class="container"> foo'' x y z = divide (x + y) z  <input type="radio" name="q3" value="3"><span class="checkmark"></span> </label><br>
   <button class="btn-select" onclick="checkAnswer(3)">Submit</button> <p id="result3"></p> <input type="hidden" id="correctAnswer3" value="3">

   <button class="btn-answer" onclick="toggleCollapsible(3)"> Answer</button>
    <div id="collapsibleDiv3">
    foo'' is the invocation that could trigger a crash since we have no guarantees that z is a `NonZero` value. 
    </div>
</div>
<br/>


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
the value `0 - n` is indeed non-negative. 


Dependent Refinements
---------------------------------------

The predicates in pre- and post- conditions can also refer to previous arguments
of the function.

For example, including that the output is greater than the input.

\begin{code}
{-@ plus1 :: a:Int -> {b:Int |b > a}@-}
plus1 :: Int -> Int 
plus1 a = a + 1
\end{code}

And the same could be done between input values.

<div class="interact">
<b>Exercise:</b>

Let's put everything together now.

Write a specification for the method `calcPer` that:

1) first receives a positive int;

2) then an int with a value between zero and the first int;

3) returns a percentage;

Use the aliases created in the exercises you have completed before.

\begin{code}
calcPer       :: Int -> Int -> Int
calcPer a b    = (b * 100) `div` a


cpc = calcPer 10 5 :: Int  -- should be correct
cpi = calcPer 10 11 :: Int -- should be incorrect

\end{code}

<div>
   <button class="btn-answer" onclick="toggleCollapsible(1)"> Answer</button>
    <div id="collapsibleDiv5">
`{-@ calcPer :: a:Positive -> {b:Int | 0 <= b && b <= a} -> c:Percentage @-}`
    </div>
</div>

</div>

You finished the first part of the Tutorial!
Tell the interviewers you got to the end of the page, and answer some questions from our team before moving to the next section.

<a href="Tutorial_05_Datatypes.html" >
    <button class="btn-next">Next</button>
</a> 
