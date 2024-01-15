
Logic & SMT
===========

\begin{comment}
\begin{code}
{-@ LIQUID "--short-names"         @-}
{-@ LIQUID "--no-termination"      @-}
{-@ LIQUID "--reflection"          @-}

module Tutorial_02_Logic where

{- size  :: xs:[a] -> {v:Int | v = size xs} @-}

ax1 :: Int -> Bool
ax2 :: Int -> Bool
ax3 :: Int -> Int -> Bool
ax4 :: Int -> Int -> Bool
ax5 :: Int -> Int -> Int -> Bool
ax6 :: Int -> Int -> Bool

congruence :: (Int -> Int) -> Int -> Int -> Bool
fx1 :: (Int -> Int) -> Int -> Bool

ex1, ex2 :: Bool -> Bool
ex3, ex3', ex4, ex6, ex7, exDeMorgan1, exDeMorgan2 :: Bool -> Bool -> Bool

infixr 9 ==>

{-@ invariant {v:[a] | size v >= 0} @-}

-- {-@ fail ex0' @-}
-- {-@ fail ex3' @-}
-- {-@ fail exDeMorgan2 @-}
-- {-@ fail ax0' @-}
-- {-@ fail ax6 @-}

\end{code}
\end{comment}

As we shall see shortly, a refinement type is:

 > *Refinement Types* = *Types* + *Logical Predicates*

Let us begin by quickly recalling what we mean by "logical predicates"
in the remainder of this tutorial. ^[If you are comfortable with this material,
e.g. if you know what the "S", "M" and "T" stand for in SMT, and what QF-UFLIA
stands for (i.e. the quantifier free theory of linear arithmetic and
uninterpreted functions), then feel free skip to the next chapter.]
To this end, we will describe *syntax*, that is, what predicates *look*
like, and *semantics*, which is a fancy word for what predicates *mean*.

Syntax
------

A *logical predicate* is, informally speaking, a Boolean valued term drawn
from a *restricted* subset of Haskell. In particular, the expressions are
drawn from the following grammar comprising *constants*, *expressions* and
*predicates*.

\newthought{A Constant}^[When you see := you should read it as "is defined
to be"] `c` is simply one of the numeric values:

~~~~~{.spec}
    c := 0, 1, 2, ...
~~~~~

\newthought{A Variable} `v` is one of `x`, `y`, `z`, etc., these will refer
to (the values of) binders in our source programs.

~~~~~{.spec}
    v := x, y, z, ...
~~~~~

\newthought{An Expression} `e` is one of the following forms;
that is, an expression is built up as linear arithmetic expressions
over variables and constants and uninterpreted function applications.

~~~~~{.spec}
    e := v                      -- variable
       | c                      -- constant
       | (e + e)                -- addition
       | (e - e)                -- subtraction
       | (c * e)                -- multiplication by constant
       | (v e1 e2 ... en)       -- uninterpreted function application
       | (if p then e else e)   -- if-then-else
~~~~~

\newthought{Examples of Expressions} include the following:

+ `x + y - z`
+ `2 * x`
+ `1 + size x`

\newthought{A Relation} is one of the usual (arithmetic)
comparison operators:

~~~~~{.spec}
    r := ==               -- equality
       | /=               -- disequality
       | >=               -- greater than or equal
       | <=               -- less than or equal
       | >                -- greater than
       | <                -- less than
~~~~~

\newthought{A Predicate} is either an atomic predicate, obtained by comparing
two expressions, or, an application of a predicate function to a list of arguments,
or the Boolean combination of the above predicates with the operators `&&` (and),
`||` (or), `==>` (implies ^[Read `p ==> q` as "if `p` then `q`"]), `<=>` (if and only
if ^[Read `p <=> q` as "if `p` then `q` **and** if `q` then `p`"]), and `not`.

~~~~~{.spec}
    p := (e r e)                -- binary relation
       | (v e1 e2 ... en)       -- predicate (or alias) application
       | (p && p)               -- and
       | (p || p)               -- or
       | (p => p) | (p ==> p)   -- implies
       | (p <=> p)              -- iff
       | (not p)                -- negation
       | true | True
       | false | False
~~~~~


\newthought{Examples of Predicates} include the following:



Can you select which of the following ones is not a valid predicate?
!!Exercise
 <div id="question2" style="width=640px;border= 2px solid #3498db; border-radius= 10px;">
   <p>What should be the predicate of div to make it impossible to divide by zero?</p>
   <label class="container"> `x /= 3`                               <input type="radio" name="q2" value="1"> <span class="checkmark"></span> </label><br>
   <label class="container"> `x + y <= 3 && y < 1`                  <input type="radio" name="q2" value="2"> </label><br>
   <label class="container"> `x < 10 ==> y < 10 ==> x + y < 20`     <input type="radio" name="q2" value="3"></label><br>
   <label class="container"> `x ** y > 0 `                          <input type="radio" name="q2" value="4"></label><br>
   <label class="container"> `0 < x + y <=> 0 < y + x`              <input type="radio" name="q2" value="5"></label><br>
   
   <button style="padding: 10px; background-color: #3498db; color: white; border: none; border-radius: 5px;" onclick="checkAnswer(2)">Submit</button>
   <p id="result2"></p>
   <input type="hidden" id="correctAnswer2" value="4">

   <button style="padding: 10px; background-color: green; color: white; border: none; border-radius: 5px;" onclick="toggleCollapsibleDiv()"> Answer</button>
    <div class="collapsibleDiv">
All of them are valid syntatic expressions, except for `x ** y > 0 ` since 
the operator ** is not part of the language.   
    </div>
</div>



+ `x /= 3`
+ `x + y <= 3 && y < 1`
+ `x < 10 ==> y < 10 ==> x + y < 20`
+ `x ** y > 0 ` <----  
+ `0 < x + y <=> 0 < y + x`






Semantics {#semantics}
----------------------

The syntax of predicates tells us what they *look* like, that is, what we
can *write down* as valid predicates. Next, let us turn our attention to
what a predicate *means*. Intuitively, a predicate is just a Boolean valued
Haskell function with `&&`, `||`, `not` being the usual operators and `==>` and
`<=>` being two special operators.

\newthought{A Predicate is Satisfiable} if *there exists*
an assignment that makes the predicate evaluate to `True`.
For example, with the following assignments of x, y and z, the predicate bellow
is satisfiable.

~~~~~{.spec}
    x := 1
    y := 2
    z := 3

    x + y == z
~~~~~

\noindent
as the above assignment makes the predicate
evaluate to `True`.

\newthought{A Predicate is Valid} in an environment if *every*
assignment in that environment makes the predicate evaluate to
`True`. For example, the predicate

~~~~~{.spec}
    x < 10 || x == 10 || x > 10
~~~~~

\noindent
is valid no matter what value we assign to `x`, the
above predicate will evaluate to `True`.


Verification Conditions
-----------------------

LiquidHaskell works without actually *executing* your
programs. Instead, it checks that your program meets the given
specifications in roughly two steps.

1. First, LH combines the code and types down to a set of
   *Verification Conditions* (VC) which are predicates that
   are valid *only if* your program satisfies a given
   property. 

2. Next, LH *queries* an [SMT solver] to determine
   whether these VCs are valid. If so, it says your program
   is *safe* and otherwise it *rejects* your program.

\newthought{The SMT Solver decides} whether a predicate (VC) is valid
*without enumerating* and evaluating all assignments. The SMT solver 
uses a variety of sophisticated *symbolic algorithms*
to deduce whether a predicate is valid or not.

\newthought{We Restrict the Logic} to ensure that all our VC queries
fall within the *decidable fragment*. This makes LiquidHaskell
extremely automatic -- there is *no* explicit manipulation of proofs,
just the specification of properties via types and of course, the
implementation via Haskell code!  This automation comes at a price:
all our refinements *must* belong to the logic above. Fortunately,
with a bit of creativity, we can say a *lot* in this logic. ^[In
particular, we will use the uninterpreted functions to create many
sophisticated abstractions.]

Examples: Propositions
----------------------

Finally, let's conclude this quick overview with some
examples of predicates, in order to build up our own
intuition about logic and validity.
Each of the below is a predicate from our refinement
logic. However, we write them as raw Haskell expressions
that you may be more familiar with right now, and so that
we can start to use LiquidHaskell to determine whether a
predicate is indeed valid or not.

\newthought{Let `TRUE` be a refined type} for `Bool`
valued expressions that *always* evaluate to `True`.
Similarly, we can define `FALSE` for `Bool` valued
expressions that *always* evaluate to `False`:^[This syntax will be discussed in
greater detail [soon](#propositions)]

\begin{code}
{-@ type TRUE  = {v:Bool | v    } @-}
{-@ type FALSE = {v:Bool | not v} @-}
\end{code}

\noindent
Thus, a *valid predicate* is one that has the type
`TRUE`. The simplest example of a valid predicate
is just `True`:

\begin{code}
{-@ ex0 :: TRUE @-}
ex0 = True
\end{code}

\noindent of course, `False` is *not valid*

\begin{code}
{-@ ex0' :: FALSE @-}
ex0' = False
\end{code}

We can get more interesting predicates if we use variables.
For example, the following is valid predicate says that a
`Bool` variable is either `True` or `False`.

\begin{code}
{-@ ex1 :: Bool -> TRUE @-}
ex1 b = b || not b
\end{code}

\noindent Of course, a variable cannot be both `True`
and `False`. Write a predicate for ex2 with that meaning:

\begin{code}
ex2 b = b && not b
\end{code}
!!Exercise
<div>
 <button style="padding: 10px; background-color: green; color: white; border: none; border-radius: 5px;" onclick="toggleCollapsibleDiv()"> Answer</button>
    <div class="collapsibleDiv">
The correct answer would be: {-@ ex2 :: Bool -> FALSE @-}
    </div>
</div>




Examples: Arithmetic
--------------------

Next, let's look at some predicates involving arithmetic.
The simplest ones don't have any variables, for example:

\begin{code}
{-@ ax0 :: TRUE @-}
ax0 = 1 + 1 == 2
\end{code}

\noindent Again, a predicate that evaluates to `False`
is *not* valid. Run the example and change it to be correct:

\begin{code}
{-@ ax0' :: TRUE @-}
ax0' = 1 + 1 == 3
\end{code}

\newthought{SMT Solvers determine Validity} *without*
enumerating assignments. For example, consider the
predicate:

\begin{code}
{-@ ax1 :: Int -> TRUE @-}
ax1 x = x < x + 1
\end{code}

\noindent It is trivially valid; as via the usual
laws of arithmetic, it is equivalent to `0 < 1`
which is `True` independent of the value of `x`.
The SMT solver is able to determine this validity
without enumerating the infinitely many possible
values for `x`. This kind of validity checking
lies at the heart of LiquidHaskell.


Examples: Uninterpreted Function
--------------------------------

We say that function symbols are *uninterpreted* in the refinement logic,
because the SMT solver does not "know" how functions are defined. Instead,
the only thing that the solver knows is the *axiom of congruence* which
states that any function `f`, returns equal outputs when invoked on equal
inputs.

To get a taste of why uninterpreted functions will prove useful,
let's write a function to compute the `size` of a list:

\begin{code}
{-@ measure size @-}
{-@ size :: [a] -> Nat @-}
size        :: [a] -> Int
size []     = 0
size (x:xs) = 1 + size xs
\end{code}

We can now verify that the following predicates are *valid*:

\begin{code}
{-@ fx0 :: [a] -> [a] -> TRUE @-}
fx0 xs ys = (xs == ys) ==> (size xs == size ys)
\end{code}

\noindent Note that to determine that the above is valid, the SMT
solver does not need to know the *meaning* or *interpretation* of
`size` -- merely that it is a function. When we need some information
about the definition, of `size` we will put it inside the predicate.
For example, in order to prove that the following is valid:

\begin{code}
{-@ fx2 :: a -> [a] -> TRUE @-}
fx2 x xs = 0 < size ys
  where
    ys   = x : xs
\end{code}

\noindent LiquidHaskell actually asks the SMT solver to
prove the validity of a VC predicate which states that
sizes are non-negative and that since `ys` equals `x:xs`,
the size of `ys` is one more than `xs`. ^[Fear not! We
will describe how this works [soon](#autosmart)]

\begin{code}
{-@ fx2VC :: _ -> _ -> _ -> TRUE @-}
fx2VC x xs ys =   (0 <= size xs)
              ==> (size ys == 1 + size xs)
              ==> (0 < size ys)
\end{code}

Next, let's see how we can use logical predicates to *specify* and
*verify* properties of real programs.
