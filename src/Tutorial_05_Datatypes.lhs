
Refined Datatypes
=================


\begin{comment}
\begin{code}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module Tutorial_05_Datatypes
       (
       )
      where


{-@ die :: {v:_ | false} -> a @-}
die msg = error msg

-- {-@ fail badSP @-}
-- {-@ fail badSP' @-}
-- {-@ fail badList @-}
-- {-@ ignore append @-}
-- {-@ fail badBST @-}
-- {-@ fail ne1 @-}
-- {-@ ignore delMin @-}


\end{code}
\end{comment}

So far, we have seen how to refine the types of *functions*, to
specify, for example, pre-conditions on the inputs, or post-conditions
on the outputs. 
In this section we will see how to apply these in datatypes.
First, by defining properties of data values, and then by defining *datatypes* that satisfy
certain invariants. In the latter, it is handy to be able to directly
refine the `data` definition, making it impossible to create
illegal inhabitants.


\newthought{Measures} are used to define *properties* of
Haskell data values that are useful for specification and
verification. 

\newthought{A measure} is a *total* Haskell function,
1. With a *single* equation per data constructor, and
2. Guaranteed to *terminate*, typically via structural recursion.

\noindent
We can tell LiquidHaskell to *lift* a function meeting
the above requirements into the refinement logic by declaring:

`{-@ measure nameOfMeasure @-}`

For example, for a list we can define a way to *measure* its size with 
the following function.

\begin{code}
{-@ measure size @-}
{-@ size :: [a] -> Nat @-}
size :: [a] -> Int
size []     = 0
size (_:rs) = 1 + size rs
\end{code}


Then, we can use this measure to define aliases.

<div class = "interact">
Let's create another measure named `notEmpty` that takes a list as input
and returns a `Bool` with the information if it is empty or not.

\begin{code}
-- write notEmpty measure
\end{code}

<div>
   <button class="btn-answer" onclick="toggleCollapsible(2)"> Answer</button>
    <div id="collapsibleDiv2">
`{-@ measure notEmpty @-}`<br/>
`notEmpty       :: [a] -> Bool`<br/>
`notEmpty []    = False`<br/>
`notEmpty (_:_) = True`
    </div>
</div>

</div>

We can now define a couple of useful aliases
for describing lists of a given dimension.

For example, we can define that a list has exactly `N` elements. 

\begin{code}
{-@ type ListN a N = {v:[a] | size v == N} @-}
\end{code}

Note that when defining refinement type aliases, we use uppercase variables
like `N` to distinguish *value* parameters from the lowercase
*type* parameters like `a`.


<div class="interact">
Now, try to create an alias `NEList` for an empty list, using the measure 
`notEmpty` created before. When removed from comment, the first example should raise an error while the
second should not.

\begin{code}
-- write the alias here

-- Remove the comments below to test the alias
-- {-@ ne1 :: NEList Int@-}
-- ne1 = [] ::  [Int]       -- should fail
-- {-@ ne2 :: NEList Int@-} -- should be correct 
-- ne2 = [1,2,3,4] :: [Int]
\end{code}

<div>
   <button class="btn-answer" onclick="toggleCollapsible(40)"> Answer</button>
   
   <div id="collapsibleDiv40">
`{-@ type NEList a = {v:[a] | notEmpty v} @-}`
   </div>
</div>

</div>

Sparse Vectors
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
1. the dimension stored in `spDim` is non-negative;

2. every index in `spElems` must be valid, i.e.
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
Remove the comment from the type signature below and complete the implementation with the example.
\begin{code}
-- badSP' :: Sparse String
\end{code}

<div>
   <button class="btn-answer" onclick="toggleCollapsible(1)"> Answer</button>
    <div id="collapsibleDiv1">
e.g., `badSP' = SP (-1) [(0, "cat")]`
    </div>
</div>

</div>


\newthought{Field Measures} It is convenient to write an alias
for sparse vectors of a given size `N`. So that we can easily say in
a refinement that we have a sparse vector of a certain size.

For this we can use *measures*.


\newthought{Measures with Sparse Vectors}
Similarly, the sparse vector also has a *measure* for its dimension, and it
is already defined by `spDim`, so we can use it to create the new alias 
of sparse vectors of size N.


<div class="think-aloud">
<b><span class="think-aloud-text">Think Aloud:</span></b>

For the following exercise, we will use a technique called Think Aloud, where you
should try to say everything that comes to your mind while you engage with the exercise.

In specific, aim:

a) to speak all thoughts, even if they are unrelated to the task;

b) to refrain from  explaining the  thoughts; 

c) to not try to plan out what to say; 

d) to imagine that you are alone and speaking to yourself; and  

e) to speak continuously. 

For the following exercise, read the question aloud and remeber to voice your thoughts while 
solving the exercise.
</div>

<div class="interact">
Following what we did with the lists, write the alias `SparseN` for sparse vector of
length N, using `spDim` instead of `size`.

\begin{code}
-- write the alias here
\end{code}

<div>
<button class="btn-answer" onclick="toggleCollapsible(5)"> Answer</button>
   <div id="collapsibleDiv5">
e.g., `{-@ type SparseN a N = {v:Sparse a | spDim v == N} @-}`
   </div>
</div>

</div>



\newthought{You finished the Tutorial!}
You finished the Tutorial!
Tell the interviewers you got to the end of the page, and answer some questions from our team before moving to the next section.

\newthought{Next Exercise!}
Now that you have learned the main blocks of LiquidHaskell, let's complete
an exercise using all the concepts.

You can open a <a href="Tutorial_Cheat_sheet.html" >Cheat Sheet</a> with examples of the main concepts on another tab on the side.


<a href="Tutorial_09_Case_Study_Lazy_Queues.html" >
    <button class="btn-next">Next</button>
</a> 