Introduction {#intro}
============

<style>
/* Add some basic styling */
.collapsibleDiv {
  display: none;
  padding: 20px;
  border: 1px solid #ddd;
  margin-top: 10px;
}
/* The container */
.container {
display: block;
position: relative;
padding-left: 35px;
margin-bottom: 12px;
cursor: pointer;
font-size: 22px;
-webkit-user-select: none;
-moz-user-select: none;
-ms-user-select: none;
user-select: none;
}

/* Hide the browser's default radio button */
.container input {
position: absolute;
opacity: 0;
cursor: pointer;
}

/* Create a custom radio button */
.checkmark {
position: absolute;
top: 0;
left: 0;
height: 25px;
width: 25px;
background-color: #eee;
border-radius: 50%;
}

/* On mouse-over, add a grey background color */
.container:hover input ~ .checkmark {
background-color: #ccc;
}

/* When the radio button is checked, add a blue background */
.container input:checked ~ .checkmark {
background-color: #2196F3;
}

/* Create the indicator (the dot/circle - hidden when not checked) */
.checkmark:after {
content: "";
position: absolute;
display: none;
}

/* Show the indicator (dot/circle) when checked */
.container input:checked ~ .checkmark:after {
display: block;
}

/* Style the indicator (dot/circle) */
.container .checkmark:after {
 top: 9px;
left: 9px;
width: 8px;
height: 8px;
border-radius: 50%;
background: white;
}
</style>
  
<script>
function checkAnswer(questionNumber) {
    const selectedAnswer = document.querySelector(`input[name=q${questionNumber}]:checked`).value;
    const correctAnswer = document.getElementById(`correctAnswer${questionNumber}`).value;
    const resultElement = document.getElementById(`result${questionNumber}`);

    if (selectedAnswer === correctAnswer) {
       resultElement.textContent = 'Correct!';
    } else {
       resultElement.textContent = 'Incorrect. Please try again.';
    }
}

function toggleCollapsibleDiv() {
    var div = document.getElementById('collapsibleDiv');
    div.style.display = (div.style.display === 'none') ? 'block' : 'none';
}
</script>



\begin{comment}
\begin{code}
{-# LANGUAGE CPP #-}

module Tutorial_01_Introduction where
main = putStrLn "Intro"

-- {-@ ignore average @-}

\end{code}
\end{comment}

Welcome to the LiquidHaskell Short Tutorial, where you will learn the basic workings 
of LiquidHaskell and complete some exercises.
The full version of the tutorial can be found in the [project's website](https://ucsd-progsys.github.io/liquidhaskell-tutorial/Tutorial_01_Introduction.html).

One of the great things about Haskell is its brainy type system that
allows one to enforce a variety of invariants at compile time, thereby
nipping in the bud a large swathe of run-time [errors](#getting-started).

Well-Typed Programs Do Go Wrong {#gowrong}
------------------------------------------

Alas, well-typed programs *do* go quite wrong, in a variety of ways.

\newthought{Division by Zero} This innocuous function computes the average
of a list of integers:

\begin{code}
average    :: [Int] -> Int
average xs = sum xs `div` length xs
\end{code}

We get the desired result on a non-empty list of numbers:

~~~~~{.ghci}
ghci> average [10, 20, 30, 40]
25
~~~~~

 <div id="question1" style="width=640px;border= 2px solid #3498db; border-radius= 10px;">
   <p>What should be the predicate of div to make it impossible to divide by zero?</p>
   <label class="container"> Yes, e.g., the list [1] <input type="radio" name="q1" value="1"> <span class="checkmark"></span> </label><br>
   <label class="container"> Yes, e.g., the list []   <input type="radio" name="q1" value="2"> </label><br>
   <label class="container"> No, it should not crash. <input type="radio" name="q1" value="3"></label><br>
   <button style="padding: 10px; background-color: #3498db; color: white; border: none; border-radius: 5px;" onclick="checkAnswer(1)">Submit</button>
   <p id="result1"></p>
   <input type="hidden" id="correctAnswer1" value="2">

   <button style="padding: 10px; background-color: green; color: white; border: none; border-radius: 5px;" onclick="toggleCollapsibleDiv()"> Answer</button>
    <div class="collapsibleDiv">
If we call it with an empty list, we get a rather unpleasant crash: 
*** Exception: divide by zero. We could write `average` more *defensively*, 
returning a `Maybe` or `Either` value. However, this merely kicks
the can down the road. Ultimately, we will want to extract
the `Int` from the `Maybe` and if the inputs were invalid
to start with, then at that point we'd be stuck.    
    </div>
</div>



\newthought{Heart Bleeds}
For certain kinds of programs, there is a fate worse than death.
`text` is a high-performance string processing library for Haskell, that
is used, for example, to build web services.

~~~~~{.ghci}
ghci> :m +Data.Text Data.Text.Unsafe
ghci> let t = pack "Voltage"
ghci> takeWord16 5 t
"Volta"
~~~~~

A cunning adversary can use invalid, or rather,
*well-crafted*, inputs that go well outside the size of
the given `text` to read extra bytes and thus *extract secrets*
without anyone being any the wiser.

~~~~~{.ghci}
ghci> takeWord16 20 t
"Voltage\1912\3148\SOH\NUL\15928\2486\SOH\NUL"
~~~~~

The above call returns the bytes residing in memory
*immediately after* the string `Voltage`. These bytes
could be junk, or could be either the name of your
favorite TV show, or, more worryingly, your bank
account password.

Refinement Types
----------------

Refinement types allow us to enrich Haskell's type system with
*predicates* that precisely describe the sets of *valid* inputs
and outputs of functions, values held inside containers, and
so on. These predicates are drawn from special *logics* for which
there are fast *decision procedures* called SMT solvers.

\newthought{By combining types with predicates} you can specify *contracts*
which describe valid inputs and outputs of functions. The refinement
type system *guarantees at compile-time* that functions adhere to
their contracts. That is, you can rest assured that
the above calamities *cannot occur at run-time*.

\newthought{LiquidHaskell} is a Refinement Type Checker for Haskell, and in
this tutorial we'll describe how you can use it to make programs
better and programming even more fun. 

As a glimpse of what LiquidHaskell can do, run the average example below and 
read the error message.
Since div cannot take a zero value as the second argument, and LiquidHaskell
sees that it is a possibility in this function, an error will be raised.
\begin{code}
average'    :: [Int] -> Int
average' xs =  sum xs `div` length xs
\end{code}


In this tutorial you will learn how to add and reason about
refinement types in Haskell, and how it can increase the realiability
of Haskell problems.

To get started, open the [Web Demo](http://goto.ucsd.edu:8090/index.html#?demo=blank.hs)
and see what is the result when you `Check` the code from the first example.

