Numeric Measures {#numericmeasure}
================

\begin{comment}
\begin{code}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module Tutorial_07_Measure_Int where
import Prelude  hiding  (map, zipWith, zip, take, drop, reverse)

{-@ type TRUE = {v:Bool | v} @-}

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg
take, drop, take' :: Int -> [a] -> [a]
txgo              :: Int -> Int -> Vector (Vector a) -> Vector (Vector a)
quickSort         :: (Ord a) => [a] -> [a]
size              :: [a] -> Int
flatten :: Int -> Int -> Vector (Vector a) -> Vector a
test4 :: [String]

-- {-@ ignore dotProd @-}
-- {-@ ignore matProd @-}
-- {-@ ignore prop_map @-}
-- {-@ ignore reverse @-}
-- {-@ fail test1 @-}
-- {-@ fail test2 @-}
-- {-@ fail test3 @-}
-- {-@ fail test4 @-}
-- {-@ fail test5 @-}
-- {-@ fail test6 @-}
-- {-@ fail test10 @-}
-- {-@ ignore drop @-}
-- {-@ ignore zipOrNull @-}
-- {-@ fail badVec @-}
-- {-@ fail product @-}
-- {-@ fail bad1 @-}
-- {-@ fail bad2 @-}
-- {-@ fail mat23 @-}
-- {-@ fail matProduct @-}

-- {-@ ignore for @-}
\end{code}
\end{comment}


Many of the programs we have seen so far, for example those in
[here](#vectorbounds), suffer from *indexitis*. This is a term
coined by [Richard Bird][bird-pearls] which describes a tendency
to perform low-level manipulations to iterate over the indices
into a collection, opening the door to various off-by-one
errors. Such errors can be eliminated by instead programming
at a higher level, using a [wholemeal approach][hinze-icfp09]
where the emphasis is on using aggregate operations, like `map`,
`fold` and `reduce`.

\newthought{Wholemeal programming is no panacea} as it still
requires us to take care when operating on *different* collections;
if these collections are *incompatible*, e.g. have the wrong dimensions,
then we end up with a fate worse than a crash, a possibly meaningless
result. Fortunately, LiquidHaskell can help. Lets see how we can use
measures to specify dimensions and create a dimension-aware API for
lists which can be used to implement wholemeal
dimension-safe APIs.^[In a [later chapter](#kmeans-case-study)
we will use this API to implement K-means clustering.]

Wholemeal Programming
---------------------

Indexitis begone! As an example of wholemeal programming, let's
write a small library that represents vectors as lists and
matrices as nested vectors:

\begin{code}
data Vector a = V { vDim  :: Int
                  , vElts :: [a]
                  }
              deriving (Eq)

data Matrix a = M { mRow  :: Int
                  , mCol  :: Int
                  , mElts :: Vector (Vector a)
                  }
              deriving (Eq)
\end{code}

\newthought{The Dot Product} of two `Vector`s can be easily computed using a fold:

\begin{code}
dotProd       :: (Num a) => Vector a -> Vector a -> a
dotProd vx vy = sum (prod xs ys)
  where
    prod      = zipWith (\x y -> x * y)
    xs        = vElts vx
    ys        = vElts vy
\end{code}


\newthought{The Iteration} embodied by the `for` combinator, is simply
a `map` over the elements of the vector.

~~~~~{.spec}
for            :: Vector a -> (a -> b) -> Vector b
for (V n xs) f = V n (map f xs)
~~~~~

\newthought{Wholemeal programming frees} us from having to fret
about low-level index range manipulation, but is hardly a panacea.
Instead, we must now think carefully about the *compatibility*
of the various aggregates. For example,

+ `dotProd` is only sensible on vectors of the same dimension;
  if one vector is shorter than another (i.e. has fewer elements)
  then we will won't get a run-time crash but instead will get
  some gibberish result that will be dreadfully hard to debug.

+ `matProd` is only well defined on matrices of compatible
  dimensions; the number of columns of `mx` must equal the
  number of rows  of `my`. Otherwise, again, rather than an
  error, we will get the wrong output.^[In fact, while the
  implementation of `matProd` breezes past GHC it is quite
  wrong!]

Specifying List Dimensions
--------------------------

In order to start reasoning about dimensions, we need a way
to represent the *dimension* of a list inside the refinement
logic. ^[We could just use `vDim`, but that is a cheat as
there is no guarantee that the field's value actually equals
the size of the list!]

\newthought{Measures} are ideal for this
task. [Previously](#boolmeasures) we saw how we could lift
Haskell functions up to the refinement logic. Lets write a
measure to describe the length of a list: ^[[Recall](#usingmeasures)
that these must be inductively defined functions, with a single
equation per data-constructor]

\begin{code}
{-@ measure size @-}
{-@ size :: [a] -> Nat @-}
size []     = 0
size (_:rs) = 1 + size rs
\end{code}

\newthought{Measures Refine Constructors}
As with [refined data definitions](#autosmart), the
measures are translated into strengthened types for
the type's constructors. For example, the `size`
measure is translated into:

~~~~~{.spec}
data [a] where
  []  :: {v: [a] | size v = 0}
  (:) :: a -> xs:[a] -> {v:[a]|size v = 1 + size xs}
~~~~~

\newthought{Multiple Measures} may be defined for the same data
type. For example, in addition to the `size` measure, we can define a
`notEmpty` measure for the list type:

\begin{code}
{-@ measure notEmpty @-}
notEmpty       :: [a] -> Bool
notEmpty []    = False
notEmpty (_:_) = True
\end{code}


\newthought{We Compose Different Measures}
simply by *conjoining* the refinements in the strengthened
constructors. For example, the two measures for lists end
up yielding the constructors:

~~~~~{.spec}
data [a] where
  []  :: {v: [a] | not (notEmpty v) && size v = 0}
  (:) :: a
      -> xs:[a]
      -> {v:[a]| notEmpty v && size v = 1 + size xs}
~~~~~

\noindent
We are almost ready to begin creating a dimension aware API
for lists; one last thing that is useful is a couple of aliases
for describing lists of a given dimension.

\newthought{To make signatures symmetric} let's define an alias for
plain old (unrefined) lists:

\begin{code}
type List a = [a]
\end{code}

<div class="toolinfo">
\newthought{A ListN} is a list with exactly `N` elements, and a
`ListX` is a list whose size is the same as another list `X`.  Note
that when defining refinement type aliases, we use uppercase variables
like `N` and `X` to distinguish *value* parameters from the lowercase
*type* parameters like `a`.
</div>

\begin{code}
{-@ type ListN a N = {v:List a | size v = N} @-}
{-@ type ListX a X = ListN a {size X}        @-}
\end{code}


Lists: Size Preserving API
--------------------------

With the types and aliases firmly in our pockets, let us
write dimension-aware variants of the usual list functions.
The implementations are the same as in the standard library
i.e. [`Data.List`][data-list], but the specifications are
enriched with dimension information.

<div class="hwex" id="Map">
\newthought{map} yields a list with the same size as the input.
Fix the specification of `map` so that the `prop_map` is verified.
</div>

\begin{code}
{-@ map      :: (a -> b) -> xs:List a -> List b @-}
map _ []     = []
map f (x:xs) = f x : map f xs

{-@ prop_map :: List a -> TRUE @-}
prop_map xs = size ys == size xs
  where
    ys      = map id xs
\end{code}




<div>
   <button style="padding: 10px; background-color: green; color: white; border: none; border-radius: 5px;" onclick="toggleCollapsible(1)"> Answer</button>
    <div id="collapsibleDiv1">
`{-@ map      :: (a -> b) -> xs: List a -> ListX b xs @-}``
    </div>
</div>


Now that we have seen the basics of LiquidHaskell, let us try a more complex exercise.
