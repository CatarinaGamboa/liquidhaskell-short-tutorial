
Polymorphism {#polymorphism}
============

\begin{comment}
\begin{code}
{-@ LIQUID "--short-names"         @-}
{-@ LIQUID "--no-termination"      @-}
{-@ LIQUID "--scrape-used-imports" @-}

module Tutorial_04_Polymorphism
   ( safeLookup
   , unsafeLookup
   , vectorSum, vectorSum'
   , absoluteSum, absoluteSum'
   , dotProduct
   , sparseProduct, sparseProduct'
   , eeks
   , head, head', head''
   ) where

import Prelude      hiding (head, abs, length)
import Data.List    (foldl')
import Data.Vector  hiding (head, foldl')

absoluteSum'     :: Vector Int -> Int
dotProduct     :: Vector Int -> Vector Int -> Int
absoluteSum     :: Vector Int -> Int
sparseProduct, sparseProduct'  :: Vector Int -> [(Int, Int)] -> Int

-- {-@ fail eeks @-}
-- {-@ fail head @-}
-- {-@ fail unsafeLookup @-}
-- {-@ fail dotProduct @-}

\end{code}
\end{comment}

Refinement types shine when we want to establish
properties of *polymorphic* datatypes and higher-order
functions. Rather than be abstract, let's illustrate this
with a [classic][dmlarray] use-case.

\newthought{Array Bounds Verification} aims to ensure
that the indices used to retrieve values from an array are indeed
*valid* for the array, i.e. are between `0` and the
*size* of the array. For example, suppose we create
an `array` with two elements:

~~~~~{.spec}
twoLangs  = fromList ["haskell", "javascript"]
~~~~~

Lets attempt to look it up at various indices:

\begin{code}
eeks      = [ok, yup, nono]
  where
    ok    = twoLangs ! 0
    yup   = twoLangs ! 1
    nono  = twoLangs ! 3
\end{code}

If we try to *run* the above, we get a nasty shock: an
exception that says we're trying to look up `twoLangs`
at index `3` whereas the size of `twoLangs` is just `2`.

~~~~~{.sh}
Prelude> :l 03-poly.lhs
[1 of 1] Compiling VectorBounds     ( 03-poly.lhs, interpreted )
Ok, modules loaded: VectorBounds.
*VectorBounds> eeks
Loading package ... done.
"*** Exception: ./Data/Vector/Generic.hs:249 ((!)): index out of bounds (3,2)
~~~~~

Specification: Vector Bounds {#vectorbounds}
--------------------------------------------

First, let's see how to *specify* array bounds safety by *refining*
the types for the [key functions][vecspec] exported by `Data.Vector`,
i.e. how to

1. *define* the size of a `Vector`
2. *compute* the size of a `Vector`
3. *restrict* the indices to those that are valid for a given size.

<div class="toolinfo">

\newthought{Imports}
We can write specifications for imported modules -- for which we
*lack* the code -- either directly in the client's source file or
better, in `.spec` files which can be reused across multiple client
modules.

~~~~~{.spec}
-- | Define the size
measure vlen :: Vector a -> Int

-- | Compute the size
assume length :: x:Vector a -> {v:Int | v = vlen x}

-- | Lookup at an index
assume (!) :: x:Vector a -> {v:Nat | v < vlen x} -> a
~~~~~
</div>


\newthought{Measures} are used to define *properties* of
Haskell data values that are useful for specification and
verification. Think of `vlen` as the *actual*
size of a `Vector` regardless of how the size was computed.

\newthought{Assumes} are used to *specify* types describing the semantics of
functions that we cannot verify e.g. because we don't have the code
for them. Here, we are assuming that the library function `Data.Vector.length`
indeed computes the size of the input vector. Furthermore, we are stipulating
that the lookup function `(!)` requires an index that is between `0` and the real
size of the input vector `x`.

\newthought{Dependent Refinements} are used to describe relationships
*between* the elements of a specification. For example, notice how the
signature for `length` names the input with the binder `x` that then
appears in the output type to constrain the output `Int`. Similarly,
the signature for `(!)` names the input vector `x` so that the index
can be constrained to be valid for `x`.  Thus, dependency lets us
write properties that connect *multiple* program values.

\newthought{Aliases} are extremely useful for defining
*abbreviations* for commonly occurring types. Just as we
enjoy abstractions when programming, we will find it
handy to have abstractions in the specification mechanism.
To this end, LiquidHaskell supports *type aliases*.
For example, we can define `Vector`s of a given size `N` as:

\begin{code}
{-@ type VectorN a N = {v:Vector a | vlen v == N} @-}
\end{code}

\noindent and now use this to type `twoLangs` above as:

\begin{code}
{-@ twoLangs :: VectorN String 2 @-}
twoLangs     = fromList ["haskell", "javascript"]
\end{code}

Similarly, we can define an alias for `Int` values
between `Lo` and `Hi`:

\begin{code}
{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}
\end{code}

\noindent after which we can specify `(!)` as:

~~~~~{.spec}
(!) :: x:Vector a -> Btwn 0 (vlen x) -> a
~~~~~

Verification: Vector Lookup
---------------------------

Let's try to write some functions to sanity check the specifications.
First, find the starting element -- or `head` of a `Vector`

\begin{code}
head     :: Vector a -> a
head vec = vec ! 0
\end{code}

When we check the above, we get an error:

~~~~~{.liquiderror}
     src/03-poly.lhs:127:23: Error: Liquid Type Mismatch
       Inferred type
         VV : Int | VV == ?a && VV == 0

       not a subtype of Required type
         VV : Int | VV >= 0 && VV < vlen vec

       In Context
         VV  : Int | VV == ?a && VV == 0
         vec : Vector a | 0 <= vlen vec
         ?a  : Int | ?a == (0  :  int)
~~~~~

\noindent 


 <div id="question1" style="width=640px;border= 2px solid #3498db; border-radius= 10px;">
   <p>What is the problem that the message is describing?</p>
   <label class="container"> It does not know what is the `!` operator <input type="radio" name="q1" value="1"> <span class="checkmark"></span> </label><br>
   <label class="container"> The index should be greater than 0 because the head is not accessible <input type="radio" name="q1" value="2"><span class="checkmark"></span> </label><br>
   <label class="container"> Zero is not a valid index if the list is empty.   <input type="radio" name="q1" value="3"><span class="checkmark"></span> </label><br>
   <button class="btn-select" onclick="checkAnswer(1)">Submit</button> <p id="result1"></p><input type="hidden" id="correctAnswer1" value="3">

   <button class="btn-answer" onclick="toggleCollapsible(5)"> Answer</button>
    <div id="collapsibleDiv5">
LiquidHaskell is saying that `0` is *not* a valid index
as it is not between `0` and `vlen vec`. Say what? Well, what if
`vec` had *no* elements! A formal verifier doesn't
make *off by one* errors.
    </div>
</div>




\newthought{To Fix} the problem we can do one of two things.

1. *Require* that the input `vec` be non-empty, or
2. *Return* an output if `vec` is non-empty, or

Here's an implementation of the first approach, where we define
and use an alias `NEVector` for non-empty `Vector`s

\begin{code}
{-@ type NEVector a = {v:Vector a | 0 < vlen v} @-}

{-@ head' :: NEVector a -> a @-}
head' vec = vec ! 0
\end{code}

<div class="hwex" id="Vector Head">
Replace the `undefined` with an *implementation* of `head''`
which accepts *all* `Vector`s but returns a value only when
the input `vec` is not empty.
</div>

\begin{code}
head''     :: Vector a -> Maybe a
head'' vec = undefined
\end{code}

<div class="hwex" id="Unsafe Lookup"> The function `unsafeLookup` is
a wrapper around the `(!)` with the arguments flipped. Modify the
specification for `unsafeLookup` so that the *implementation* is
accepted by LiquidHaskell.
</div>

\begin{code}
{-@ unsafeLookup :: Int -> Vector a -> a @-}
unsafeLookup index vec = vec ! index
\end{code}

<div class="hwex" id="Safe Lookup">
Complete the implementation of `safeLookup` by filling
in the implementation of `ok` so that it performs a bounds
check before the access.
</div>

\begin{code}
{-@ safeLookup :: Vector a -> Int -> Maybe a @-}
safeLookup x i
  | ok        = Just (x ! i)
  | otherwise = Nothing
  where
    ok        = undefined
\end{code}

Inference: Our First Recursive Function
---------------------------------------

Ok, let's write some code! Let's start with a recursive
function that adds up the values of the elements of an
`Int` vector.

\begin{code}
-- >>> vectorSum (fromList [1, -2, 3])
-- 2
vectorSum         :: Vector Int -> Int
vectorSum vec     = go 0 0
  where
    go acc i
      | i < sz    = go (acc + (vec ! i)) (i + 1)
      | otherwise = acc
    sz            = length vec
\end{code}


\newthought{Inference}
LiquidHaskell verifies `vectorSum` -- or, to be precise,
the safety of the vector accesses `vec ! i`. 
The verification works out because LiquidHaskell is able to
*automatically infer* 

~~~~~{.spec}
go :: Int -> {v:Int | 0 <= v && v <= sz} -> Int
~~~~~

\noindent which states that the second parameter `i` is
between `0` and the length of `vec` (inclusive). LiquidHaskell
uses this and the test that `i < sz` to establish that `i` is
between `0` and `(vlen vec)` to prove safety.