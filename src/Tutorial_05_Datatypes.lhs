
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
-- {-@ fail badSP' @-}
-- {-@ fail test1 @-}
-- {-@ fail test2 @-}
-- {-@ fail badList @-}
-- {-@ ignore append @-}
-- {-@ fail badBST @-}
-- {-@ fail ne1 @-}
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
But first, let's create another measure named `notEmpty` that takes a list as input
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

We can now define a couple of useful aliases
for describing lists of a given dimension.

And now, we can define that a list has exactly `N` elements. 

\begin{code}
{-@ type ListN a N = {v:[a] | size v == N} @-}
\end{code}

Note that when defining refinement type aliases, we use uppercase variables
like `N` to distinguish *value* parameters from the lowercase
*type* parameters like `a`.


<div class="interact">
Now, try to create an alias for an empty list, using the measure 
`notEmpty` created before. The first example should raise an error while the
second should not.

\begin{code}
{-@ type NEList a = {true} @-}

{-@ ne1 :: NEList Int@-}
ne1 = [] ::  [Int]
{-@ ne1 :: NEList Int@-}
ne2 = [1,2,3,4] :: [Int]
\end{code}

<div>
   <button class="btn-answer" onclick="toggleCollapsible(40)"> Answer</button>
   
   <div id="collapsibleDiv40">
`{-@ type NEList a = {v:[a] | notEmpty v} @-}`
   </div>
</div>

</div>


\newthought{Measures with Sparse Vectors}

Similarly, the sparse vector also has a *measure* for its dimension, but in this
case it is already defined by `spDim`, so we can use it to create the new alias 
of sparse vectors of size N.

<div class="interact">
Now, following what we did with the lists, write the alias for sparse vector,
using `spDim` instead of `size`.

\begin{code}
{-@ type SparseN a N = {true} @-}
\end{code}

<div>
<button class="btn-answer" onclick="toggleCollapsible(5)"> Answer</button>

    <div id="collapsibleDiv5">
`{-@ type SparseN a N = {v:Sparse a | spDim v == N} @-}`
   </div>
</div>
</div>


`Vector`s are similar to Sparse Vectors, and therefore, have a
*measure* of size named `vlen`.


\newthought{Sparse Products}
So, now, we can see that LiquidHaskell is able to compute a sparse product,
making the product of all the same indexes and returning its sum.
Run the code ahead.

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


\newthought{You finished the second part of the Tutorial!}
Before moving to the next part, answer some questions from our team.


\newthought{Next Exercise!}
Now that you have learned the main blocks of LiquidHaskell, lets complete
an exercise using all the concepts.

You can open a <a href="cheat_sheet.html" >Cheat Sheet</a> with examples of the main concepts on the side.


<a href="Tutorial_09_Case_Study_Lazy_Queues.html" >
    <button class="btn-next">Next</button>
</a> 