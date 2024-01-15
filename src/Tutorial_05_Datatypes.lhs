
Refined Datatypes {#refineddatatypes}
=================


\begin{comment}
\begin{code}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module Tutorial_05_Datatypes
       (
         -- * Sparse: Data
         Sparse (..)

         -- * Sparse: Functions
       , dotProd, dotProd', plus, fromList

         -- * Sparse: Examples
       , okSP, badSP, test1, test2

          -- * OrdList: Data
       , IncList  (..)

          -- * OrdList: Examples
       , okList, badList

          -- * OrdList: Functions
       ,  insertSort, insertSort', mergeSort, quickSort

          -- * BST: Data
       , BST (..)

          -- * BST: Functions
       , mem, add, delMin, del, bstSort, toBST, toIncList

          -- * BST: Examples
       , okBST, badBST

       )
      where

import Prelude      hiding (abs, length, min)
import Data.List    (foldl')
import Data.Vector  hiding (singleton, foldl', foldr, fromList, (++))
import Data.Maybe   (fromJust)

dotProd, dotProd' :: Vector Int -> Sparse Int -> Int
test1 :: Sparse String
test2 :: Sparse Int

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg

-- {-@ fail badSP @-}
-- {-@ fail test1 @-}
-- {-@ fail test2 @-}
-- {-@ fail badList @-}
-- {-@ ignore append @-}
-- {-@ fail badBST @-}
-- {-@ ignore delMin @-}


\end{code}
\end{comment}


So far, we have seen how to refine the types of *functions*, to
specify, for example, pre-conditions on the inputs, or post-conditions
on the outputs. Very often, we wish to define *datatypes* that satisfy
certain invariants. In these cases, it is handy to be able to directly
refine the `data` definition, making it impossible to create
illegal inhabitants.

Sparse Vectors Revisited {#autosmart}
-------------------------------------

As our first example of a refined datatype, let's revisit the
sparse vector representation that we [saw earlier](#sparsetype).
The `SparseN` type alias we used got the job done, but is not
pleasant to work with because we have no way of determining
the *dimension* of the sparse vector. Instead, let's create a new
datatype to represent such vectors:

\begin{code}
data Sparse a = SP { spDim   :: Int
                   , spElems :: [(Int, a)] }
\end{code}

\noindent
Thus, a sparse vector is a pair of a dimension and a list of
index-value tuples. Implicitly, all indices *other* than those
in the list have the value `0` or the equivalent value type `a`.

\newthought{Legal}
`Sparse` vectors satisfy two crucial properties.
First, the dimension stored in `spDim` is non-negative.
Second, every index in `spElems` must be valid, i.e.
between `0` and the dimension. Unfortunately, Haskell's
type system does not make it easy to ensure that
*illegal vectors are not representable*.^[The standard
approach is to use abstract types and
[smart constructors][smart-ctr-wiki] but even
then there is only the informal guarantee that the
smart constructor establishes the right invariants.]

\newthought{Data Invariants} LiquidHaskell lets us enforce
these invariants with a refined data definition:

\begin{code}
{-@ data Sparse a = SP { spDim   :: Nat
                       , spElems :: [(Btwn 0 spDim, a)]} @-}
\end{code}

\noindent Where, as before, we use the aliases:

\begin{code}
{-@ type Nat        = {v:Int | 0 <= v}            @-}
{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}
\end{code}

\newthought{Refined Data Constructors} The refined data
definition is internally converted into refined types
for the data constructor `SP`:

~~~~~{.spec}
-- Generated Internal representation
data Sparse a where
  SP :: spDim:Nat
     -> spElems:[(Btwn 0 spDim, a)]
     -> Sparse a
~~~~~

\noindent In other words, by using refined input types for `SP`
we have automatically converted it into a *smart* constructor that
ensures that *every* instance of a `Sparse` is legal.
Consequently, LiquidHaskell verifies:

\begin{code}
okSP :: Sparse String
okSP = SP 5 [ (0, "cat")
            , (3, "dog") ]
\end{code}

\noindent but rejects, due to the invalid index:

\begin{code}
badSP :: Sparse String
badSP = SP 5 [ (0, "cat")
             , (6, "dog") ]
\end{code}

\newthought{Field Measures} It is convenient to write an alias
for sparse vectors of a given size `N`. We can use the field name
`spDim` as a *measure*, like `vlen`. That is, we can use `spDim`
inside refinements^[Note that *inside* a refined `data` definition,
a field name like `spDim` refers to the value of the field, but *outside*
it refers to the field selector measure or function.]

\begin{code}
{-@ type SparseN a N = {v:Sparse a | spDim v == N} @-}
\end{code}

\newthought{Sparse Products}
Let's write a function to compute a sparse product

\begin{code}
{-@ dotProd :: x:Vector Int -> SparseN Int (vlen x) -> Int @-}
dotProd x (SP _ y) = go 0 y
  where
    go sum ((i, v) : y') = go (sum + (x ! i) * v) y'
    go sum []            = sum
\end{code}

\noindent
LiquidHaskell verifies the above by using the specification
to conclude that for each tuple `(i, v)` in the list `y`, the
value of `i` is within the bounds of the vector `x`, thereby
proving `x ! i` safe.

\newthought{Folded Product} We can port the `fold`-based product
to our new representation:

\begin{code}
{-@ dotProd' :: x:Vector Int -> SparseN Int (vlen x) -> Int @-}
dotProd' x (SP _ y) = foldl' body 0 y
  where
    body sum (i, v) = sum + (x ! i)  * v
\end{code}

\noindent As before, LiquidHaskell checks the above by
[automatically instantiating refinements](#sparsetype)
for the type parameters of `foldl'`, saving us a fair
bit of typing and enabling the use of the elegant
polymorphic, higher-order combinators we know and love.

<div class="hwex" id="Sanitization"> \singlestar
Invariants are all well and good for data computed
*inside* our programs. The only way to ensure the
legality of data coming from *outside*, i.e. from
the "real world", is to write a sanitizer that will
check the appropriate invariants before constructing
a `Sparse` vector. Write the specification and
implementation of a sanitizer `fromList`, so that
the following typechecks:
</div>

\hint You need to check that *all* the indices in
`elts` are less than `dim`; the easiest way is to
compute a new `Maybe [(Int, a)]` which is `Just`
the original pairs if they are valid, and `Nothing`
otherwise.

\begin{code}
fromList          :: Int   -> [(Int, a)] -> Maybe (Sparse a)
fromList dim elts = undefined

{-@ test1 :: SparseN String 3 @-}
test1     = fromJust $ fromList 3 [(0, "cat"), (2, "mouse")]
\end{code}

<div class="hwex" id="Addition">
Write the specification and implementation
of a function `plus` that performs the addition of two `Sparse`
vectors of the *same* dimension, yielding an output of that dimension.
When you are done, the following code should typecheck:
</div>

\begin{code}
plus     :: (Num a) => Sparse a -> Sparse a -> Sparse a
plus x y = undefined

{-@ test2 :: SparseN Int 3 @-}
test2    = plus vec1 vec2
  where
    vec1 = SP 3 [(0, 12), (2, 9)]
    vec2 = SP 3 [(0, 8),  (1, 100)]
\end{code}


Recap
-----

In this chapter we saw how LiquidHaskell lets you refine data
type definitions to capture sophisticated invariants. These
definitions are internally represented by refining the types
of the data constructors, automatically making them "smart"  in
that they preclude the creation of illegal values that violate
the invariants. We will see much more of this handy technique
in future chapters.

One recurring theme in this chapter was that we had to create new
versions of standard datatypes, just in order to specify certain
invariants.  For example, we had to write a special list type, with
its own *copies* of nil and cons. Similarly, to implement `delMin` we
had to create our own pair type.

\newthought{This duplication} of types is quite tedious.
There should be a way to just slap the desired invariants
on to *existing* types, thereby facilitating their reuse.
In a few chapters, we will see how to achieve this reuse
by [abstracting refinements][vazou13] from the definitions of
datatypes or functions in the same way we abstract
the element type `a` from containers like `[a]` or `BST a`.
