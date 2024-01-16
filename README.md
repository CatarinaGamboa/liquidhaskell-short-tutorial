# LiquidHaskell - Short - Tutorial

This is a short version of the full LiquidHaskell Tutorial.

To access the tutorial, follow the following steps:
1. Clone the repo
2. On the command line change to the "publishing branch" `git checkout gh-pages`
3. Open the html files in the folder `docs`, starting with `Tutorial_01_Introduction.html`

<!-- 

## How to _Do_ The Tutorial

LH is available as a GHC plugin from version 0.8.10.

Thus, **the best way** to do this tutorial is to 

**Step 1** Clone this repository,

```bash
$ git clone https://github.com/ucsd-progsys/liquidhaskell-tutorial.git
```

**Step 2:** Iteratively edit-compile until it _builds_ without any liquid type errors

```bash
$ cabal v2-build
```

or 

```
$ stack build --fast --file-watch
```

The above workflow will let you use whatever Haskell tooling you use for your 
favorite editor, to automatically display LH errors as well.

## Contents

### Part I: Refinement Types

1. [Introduction](src/Tutorial_01_Introduction.lhs)
2. [Logic & SMT](src/Tutorial_02_Logic.lhs)
3. [Refinement Types](src/Tutorial_03_Basic.lhs)
4. [Polymorphism](src/Tutorial_04_Polymorphism.lhs)
5. [Refined Datatypes](src/Tutorial_05_Datatypes.lhs)

### Part II: Measures

6. [Boolean Measures](src/Tutorial_06_Measure_Bool.lhs)
7. [Numeric Measures](src/Tutorial_07_Measure_Int.lhs)
8. [Set Measures](src/Tutorial_08_Measure_Sets.lhs)

### Part III : Case Studies

9. [Case Study: Okasaki's Lazy Queues](src/Tutorial_09_Case_Study_Lazy_Queues.lhs)

### Update

```bash
$ git pull origin master
$ git submodule update --recursive
```

## Building

### Deploy on Github

```
$ cp package.yaml.pandoc package.yaml
$ mkdir _site dist
$ stack install pandoc
$ make html
$ make pdf
$ cp dist/pbook.pdf _site/book.pdf
$ git add _site
$ git commit -a -m "updating GH-PAGES"
$ git push --force-with-lease origin HEAD:gh-pages
```

#### Prerequisites

* Install LaTeX dependencies:
  * [Texlive](https://www.tug.org/texlive/)
  * texlive-latex-extra
  * texlive-fonts-extra

#### Producing .pdf Book

```bash
$ make pdf
$ evince dist/pbook.pdf
```

## Solutions to Exercises

Solutions are in *separate* [private repo](https://github.com/ucsd-progsys/liquidhaskell-tutorial-solutions)



## TODO

A work list of TODO items can be found in the [bug tracker](https://github.com/ucsd-progsys/liquidhaskell-tutorial/issues/19)

## Feedback and Gotchas

Editing feedback and various gotchas can be found in [feedback.md](feedback.md) -->

## Solutions
Solution to Lazy Queues https://ucsd-progsys.github.io/liquidhaskell/blogposts/2015-01-30-okasakis-lazy-queue.lhs/