
Case Study: Okasaki's Lazy Queues 
=================================

Lets test what we learned so far in a case study that is simple enough to explain without
pages of code, yet complex enough to show off whats cool about
dependency: Chris Okasaki's beautiful [Lazy Queues][okasaki95].
This structure leans heavily on an invariant to provide fast
*insertion* and *deletion*. Let's see how to enforce that
invariant with LiquidHaskell.

\begin{comment}
\begin{code}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--maxparams=3"    @-}

module Tutorial_09_Case_Study_Lazy_Queues 
  (Queue, insert, remove, emp) 
  where

import Prelude hiding (replicate, take, length)

-- | Size function actually returns the size: (Duh!)

{-@ size :: q:SList a -> {v:Nat | v = size q} @-}

{-@ die :: {v:String | false} -> a @-}
die x = error x

{-@ invariant {v:SList a | size v >= 0} @-}

-- Source: Okasaki, JFP 1995
-- http://www.westpoint.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/jfp95queue.pdf

replicate :: Int -> a -> Queue a




-- {-@ fail okList   @-}
-- {-@ fail badList   @-}
-- {-@ fail nil   @-}
-- {-@ fail cons   @-}
-- {-@ fail tl   @-}
-- {-@ fail hd   @-}
-- {-@ fail okHd   @-}
-- {-@ fail badHd   @-}
-- {-@ fail okQ   @-}
-- {-@ fail badQ   @-}
-- {-@ fail emp   @-}
-- {-@ fail example2Q   @-}
-- {-@ fail example0Q   @-}
-- {-@ fail remove   @-}
-- {-@ fail okRemove   @-}
-- {-@ fail badRemove   @-}
-- {-@ fail insert   @-}
-- {-@ fail replicate   @-}
-- {-@ fail okReplicate   @-}
-- {-@ fail badReplicate   @-}
-- {-@ fail makeq   @-}
-- {-@ fail rot   @-}



\end{code}
\end{comment}

Queues
------

A [queue][queue-wiki] is a structure into which we can `insert` and `remove` data
such that the order in which the data is removed is the same as the order in which
it was inserted.

<div class="figure"
  id="fig:queue"
  caption="A Queue is a structure into which we can insert
           and remove elements. The order in which the elements are
           removed is the same as the order in which they were inserted."
  height="200px"
  file="img/queue.png">
</div>

\newthought{To efficiently implement} a queue we need to have rapid
access to both the front as well as the back because we `remove`
elements from former and `insert` elements into the latter. This is
quite straightforward with explicit pointers and mutation -- one uses
an old school linked list and maintains pointers to the head and the
tail. But can we implement the structure efficiently without having
stoop so low?

\newthought{Chris Okasaki} came up with a very cunning way to
implement queues using a *pair* of lists -- let's call them `front`
and `back` which represent the corresponding parts of the Queue.

+ To `insert` elements, we just *cons* them onto the `back` list,
+ To `remove` elements, we just *un-cons* them from the `front` list.

<div class="figure"
     id="fig:queue-pair"
     height="200px"
     file="img/queue-lists.png"
     caption="We can implement a Queue with a pair of lists;
              respectively representing the front and back.">
</div>

\newthought{The catch} is that we need to shunt elements from the back
to the front every so often, e.g. we can transfer the elements from
the `back` to the `front`, when:

1. a `remove` call is triggered, and
2. the `front` list is empty.

<div class="figure"
     id="fig:queue-transfer"
     height="200px"
     file="img/queue-rotate.png"
     caption="Transferring Elements from back to front.">
</div>

\newthought{Okasaki's first insight} was to note that every element is only moved
*once* from the back to the front; hence, the time for `insert` and
`remove` could be `O(1)` when *amortized* over all the
operations. This is perfect, *except* that some set of unlucky
`remove` calls (which occur when the `front` is empty) are stuck
paying the bill. They have a rather high latency up to `O(n)` where
`n` is the total number of operations.

\newthought{Okasaki's second insight} saves the day: he observed that
all we need to do is to enforce a simple *balance invariant*:

$$\mbox{Size of front} \geq \mbox{Size of back}$$


\newthought{This is a good moment to see if you understood the idea of these Queues, 
we will start implement them now.}


\newthought{Lets implement Queues} and ensure the crucial invariant(s)
with LiquidHaskell. What we need are the following ingredients:

1. A type for `List`s, and a way to track their `size`,

2. A type for `Queue`s which encodes the balance invariant

3. A way to implement the `insert`, `remove` and `transfer` operations.

Sized Lists
------------

The first part is super easy. Let's define a type:

\begin{code}
data SList a = SL { size :: Int, elems :: [a] }
\end{code}

We have a special field that saves the `size` because otherwise, we
have a linear time computation that wrecks Okasaki's careful
analysis. (Actually, he presents a variant which does *not*
require saving the size as well, but that's for another day.)



<div class = "think-aloud">
<b><span class="think-aloud-text">Think Aloud:</span></b>

Read the question aloud and voice your thoughts while solving the exercise.
</div>
<div class = "interact">
How can we be sure that `size` is indeed the *real size* of `elems`?
Write a measure `realSize` to get the number of elements in any list:

\begin{code}
-- write measure realSize in here
\end{code}


\hint When you are done, uncomment `data SList`, that specifies a *refined* type for `SList` that ensures that the *real* size is saved in the `size` field.

\begin{code}
-- {-@ data SList a = SL {
--      size  :: Nat
--    , elems :: {v:[a] | realSize v = size}
--    }
-- @-}
\end{code}

<div>
   <button class="btn-answer" onclick="toggleCollapsible(1)"> Answer</button>
    <div id="collapsibleDiv1">
`{-@ measure realSize @-}`<br/>
`realSize      :: [a] -> Int`<br/>
`realSize []     = 0`<br/>
`realSize (_:xs) = 1 + realSize xs`
    </div>
</div>
</div>


Now, as a sanity check, consider this:

\begin{code}
okList  = SL 1 ["cat"]    -- accepted

badList = SL 1 []         -- rejected
\end{code}

\newthought{Lets define an alias} for lists of a given size `N`:

\begin{code}
{-@ type SListN a N = {v:SList a | size v = N} @-}
\end{code}

<div class = "think-aloud">
<b><span class="think-aloud-text">Think Aloud:</span></b>
Read the question aloud and voice your thoughts while solving the exercise.
</div>

<div class = "interact">
\newthought{Now define an alias} `NEList` for lists that are not empty by replacing `{true}` by the correct signature.

\begin{code}
{-@ type NEList a = {true} @-}
\end{code}

<div>
   <button class="btn-answer" onclick="toggleCollapsible(3)"> Answer</button>
    <div id="collapsibleDiv3">
`{-@ type NEList a = {v:SList a | size v > 0} @-}`
    </div>
</div>
</div>

\noindent
Finally, we can define a basic API for `SList`.

\newthought{To Construct lists}, we use `nil` and `cons`:

\begin{code}
{-@ nil :: SListN a 0 @-}
nil = SL 0 []

{-@ cons :: a -> xs:SList a -> SListN a {size xs + 1} @-}
cons x (SL n xs) = SL (n+1) (x:xs)
\end{code}


<div class = "think-aloud">
<b><span class="think-aloud-text">Think Aloud:</span></b>
Read the question aloud and voice your thoughts while solving the exercise.
</div>

<div class = "interact">

<div class="hwex" id="Destructing Lists">
We can destruct lists by writing a `hd` (head) and `tl` (tail)
function as shown below. 

For `tl`, fix the signature such that it receives
a non-empty list and returns another without the first element.

For `hd`, do the opposite. From the presented signature, remove the comment from the signature and write the implementation.
This function returns just the element at the front of the list.
</div>

\begin{code}
{-@ tl           :: {xs:NEList a| size xs < 0}
                    -> SListN a {size xs}  @-}
tl (SL n (_:xs)) = SL (n-1) xs
tl _             = die "empty SList"

{-@ hd           :: xs:NEList a -> a @-}
hd (SL _ (x:_))  = x
hd _             = die "empty SList"
\end{code}

\hint When you are done, `okHd` should be verified, but `badHd` should be rejected.

\begin{code}
{-@ okList :: SListN String 1 @-}

okHd  = hd okList       -- accepted

badHd = hd (tl okList)  -- rejected
\end{code}

<div>
   <button class="btn-answer" onclick="toggleCollapsible(9)"> Answer</button>
    <div id="collapsibleDiv9">
`{-@ tl           :: xs:NEList a -> SListN a {size xs - 1}  @-}`<br/>
<br/>
`hd (SL _ (x:_))  = x`<br/>
`hd _             = die "empty SList"`
    </div>
</div>

</div>

Queue Type
-----------

It is quite straightforward to define the `Queue` type, as a pair of lists,
`front` and `back`, such that the latter is always smaller than the former:

\begin{code}
{-@ data Queue a = Q {
      front :: SList a
    , back  :: SListLE a (size front)
    }
@-}
data Queue a = Q
  { front :: SList a
  , back  :: SList a
  }
\end{code}

\newthought{The alias} `SListLE a L` corresponds to lists with at most `N` elements:

\begin{code}
{-@ type SListLE a N = {v:SList a | size v <= N} @-}
\end{code}

\noindent
As a quick check, notice that we *cannot represent illegal Queues*:

\begin{code}
okQ  = Q okList nil  -- accepted, |front| > |back|

badQ = Q nil okList  -- rejected, |front| < |back|
\end{code}



Queue Operations
----------------

Almost there! Now all that remains is to define the `Queue` API. The
code below is more or less identical to Okasaki's (I prefer `front`
and `back` to his `left` and `right`.)

\newthought{The Empty Queue} is simply one where both `front` and
`back` are both empty:

\begin{code}
emp = Q nil nil
\end{code}


<div class = "think-aloud">
<b><span class="think-aloud-text">Think Aloud:</span></b>
Read the question aloud and voice your thoughts while solving the exercise.
</div>
<div class = "interact">
<div class="hwex" id="Queue Sizes">
For the remaining operations we need some more information.
Do the following steps:

1. Write a *measure* qsize to describe the queue size,
2. Use it to complete the definition of `QueueN` below, and
3. In the next step use QueueN.
</div>

\begin{code}
-- | create measuere qsize here

-- | Queues of size `N`
{-@ type QueueN a N = {v:Queue a | true} @-}

{-@ emp :: QueueN _ 0 @-}

{-@ example2Q :: QueueN _ 2 @-}
example2Q = Q (1 `cons` (2 `cons` nil)) nil

{-@ example0Q :: QueueN _ 0 @-}
example0Q = Q nil nil
\end{code}

<div>
   <button class="btn-answer" onclick="toggleCollapsible(71)"> Answer</button>
    <div id="collapsibleDiv71">
`{-@ measure qsize @-}`<br/>
`qsize         :: Queue a -> Int`<br/>
`qsize (Q l r) = size l + size r`<br/>
<br/>
`{-@ type QueueN a N = {v:Queue a | qsize v = N} @-}`
    </div>

</div>

</div>

\newthought{To Remove} an element we pop it off the `front` by using
`hd` and `tl`.  Notice that the `remove` is only called on non-empty
`Queue`s, which together with the key balance invariant (`makeq` that we will see later), ensures that
the calls to `hd` and `tl` are safe.


<div class = "think-aloud">
<b><span class="think-aloud-text">Think Aloud:</span></b>
Read the question aloud and voice your thoughts while solving the exercise.
</div>
<div class="interact">
Add a LiquidHaskell signature to remove using QueueN. When you are done, `okRemove` should be accepted, `badRemove`
should be rejected.

\begin{code}
remove (Q f b)   = (hd f, makeq (tl f) b)


okRemove  = remove example2Q   -- accept
badRemove = remove example0Q   -- reject
\end{code}


<div>
   <button class="btn-answer" onclick="toggleCollapsible(4)"> Answer</button>
    <div id="collapsibleDiv4">
`{-@ remove       :: {q:Queue a | qsize q > 0} a -> (a, QueueN a {qsize q - 1}) @-}`
    </div>
</div>

</div>



\newthought{To Insert} an element we just `cons` it to the `back` list, and call
the *smart constructor* `makeq` to ensure that the balance invariant holds.

<div class = "think-aloud">
<b><span class="think-aloud-text">Think Aloud:</span></b>
Read the question aloud and voice your thoughts while solving the exercise.
</div>
<div class="interact">
<div class="hwex" id="Insert">Write down a liquid type signature for `replicate` (that uses `insert`),
so that it adds the same element n times to the queue, and `okReplicate` is accepted by LiquidHaskell, but `badReplicate`
is rejected.
</div>

\begin{code}
{-@ insert :: a -> q:Queue a -> QueueN a {qsize q + 1}   @-}
insert e (Q f b) = makeq f (e `cons` b)

-- write liquid type signature
replicate 0 _ = emp
replicate n x = insert x (replicate (n-1) x)

{-@ okReplicate :: QueueN _ 3 @-}
okReplicate = replicate 3 "Yeah!"  -- accept

{-@ badReplicate :: QueueN _ 3 @-}
badReplicate = replicate 1 "No!"   -- reject
\end{code}

<div>
   <button class="btn-answer" onclick="toggleCollapsible(5)"> Answer</button>
    <div id="collapsibleDiv5">
`{-@ replicate :: n:Nat -> a -> QueueN a n @-}`
    </div>
</div>

</div>


\newthought{To Ensure the Invariant} we use the smart constructor
`makeq`, which is where the heavy lifting happens.  The constructor
takes two lists, the front `f` and back `b` and if they are balanced,
directly returns the `Queue`, and otherwise transfers the elements
from `b` over using the rotate function `rot` described next.

\begin{code}
{-@ makeq :: f:SList a -> 
             b:SListLE a {size f + 1 } -> 
             QueueN a {size f + size b} @-}
makeq f b
  | size b <= size f = Q f b
  | otherwise        = Q (rot f b nil) nil
\end{code}


\newthought{The rotate function} will ensure that the two lists are balanced, as introduced at the start.
It is arranged so that it the `hd` is built up fast, before the entire
computation finishes; which, combined with laziness provides the
efficient worst-case guarantee. 
<div class="figure"
     id="fig:queue-transfer"
     height="100px"
     file="img/queue-rotate.png"
     caption="Transferring Elements from back to front.">
</div>


<div class = "think-aloud">
<b><span class="think-aloud-text">Think Aloud:</span></b>
Read the question aloud and voice your thoughts while solving the exercise.
</div>

<div class = "interact">

<div class="hwex" id="Rotate"> \doublestar
Read and fix the liquid type added to `rot`, following the next properties.

The Rotate function `rot`:  
1. is only called when `back` is one larger than the `front` (we never let things drift beyond that). 

2. And the return size is the sum of the size in front, back and the additional to be rotated.

</div>


\begin{code}
{-@ rot :: f:SList a
          -> b:SListN a {1 - size f}
          -> acc:SList a
          -> SListN a {size acc}
@-}
rot f b acc
  | size f == 0 = hd b `cons` acc
  | otherwise = hd f `cons` rot (tl f) (tl b) (hd b `cons` acc)
\end{code}


<div>
   <button class="btn-answer" onclick="toggleCollapsible(6)"> Answer</button>
    <div id="collapsibleDiv6">
`{-@ rot :: f:SList a`<br/>
`         -> b:SListN a {1 + size f}`<br/>
`         -> acc:SList a`<br/>
`         -> SListN a {size f + size b + size acc}`<br/>
`@-}`
    </div>


</div>

Recap of everyting!
-----

Well there you have it; Okasaki's beautiful lazy Queue, with the
invariants easily expressed and checked with LiquidHaskell.
This example is particularly interesting because

1. The refinements express invariants that are critical for efficiency,
2. The code introspects on the `size` to guarantee the invariants, and
3. The code is quite simple and we hope, easy to follow!

This exercise concludes the Short Tutorial of LiquidHaskell. 
Thank you for tagging along!

