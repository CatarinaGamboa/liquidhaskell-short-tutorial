
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

Sparse Vectors {#autosmart}
-------------------------------------

As our first example of a refined datatype, let's see 
Sparse Vectors.
While the standard Vector is great for dense arrays, often we have to 
manipulate sparse vectors where most elements are just 0. We might represent 
such vectors as a list of index-value tuples `[(Int, a)]`.

Let's create a new datatype to represent such vectors:

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
1) the dimension stored in `spDim` is non-negative;
2) every index in `spElems` must be valid, i.e.
between `0` and the dimension. 

Unfortunately, Haskell's
type system does not make it easy to ensure that
*illegal vectors are not representable*.

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
for the data constructor `SP`.
So, by using refined input types for `SP`
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


<div class="interact">
Write another example of a Sparse data type that is invalid.
\begin{code}
badSP' :: Sparse String
\end{code}

<div>
   <button class="btn-answer" onclick="toggleCollapsible(1)"> Answer</button>
    <div id="collapsibleDiv1">
e.g., `badSP' = SP -1 [(0, "cat")]`
    </div>
</div>

</div>




\newthought{Field Measures} It is convenient to write an alias
for sparse vectors of a given size `N`. So that we can easily say in
a refinement that we have a sparse vector of a certain size.

For this we can use *measures*.

\newthought{Measures} are used to define *properties* of
Haskell data values that are useful for specification and
verification. 

\newthought{A measure} is a *total* Haskell function,
1. With a *single* equation per data constructor, and
2. Guaranteed to *terminate*, typically via structural recursion.

\noindent
We can tell LiquidHaskell to *lift* a function meeting
the above requirements into the refinement logic by declaring:

\begin{code}
{-@ measure nameOfMeasure @-}
\end{code}

For example, for a list we can define a way to *measure* its size with 
the following function.

\begin{code}
{-@ measure size @-}
{-@ size :: [a] -> Nat @-}
size []     = 0
size (_:rs) = 1 + size rs
\end{code}

Then, we can use this measure to define aliases.

<div class = "interact">
But first, create another measure named `notEmpty` that takes a list as input
and returns a `Bool` with the information if it is empty or not.

\begin{code}
{-@ measure notEmpty @-}
\end{code}


<div>
   <button class="btn-answer" onclick="toggleCollapsible(2)"> Answer</button>
    <div id="collapsibleDiv2">
`{-@ measure notEmpty @-}`<br/>
`notEmpty       :: [a] -> Bool`
`notEmpty []    = False`
`notEmpty (_:_) = True`
    </div>
</div>

</div>



And now, we can use this `size` to create an alias that defines
lists of a certain size `N` and another that defines 

\begin{code}
type List a = [a]

{-@ type ListN a N = {v:List a | size v = N} @-}
\end{code}

\newthought{A ListN} is a list with exactly `N` elements. 
We can also create a list of and a
`ListX` is a list whose size is the same as another list `X`.  Note
that when defining refinement type aliases, we use uppercase variables
like `N` and `X` to distinguish *value* parameters from the lowercase
*type* parameters like `a`.





Similarly, the sparse vector can also have a *measure* for its dimension.
In this case we can create `spDim` as the *actual*
dimension of the `Sparse` vector inside the refinement, and therefore create 
an alias of a sparse vector of size N.

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


<a href="Tutorial_06_Measure_Bool.html" >
    <button class="btn-next">Next</button>
</a> 