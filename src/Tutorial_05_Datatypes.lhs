
Refined Datatypes
=================


\begin{comment}
\begin{code}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module Tutorial_05_Datatypes
      where

import Prelude      hiding (abs, length, min)
import Data.List    (foldl')
import Data.Vector  hiding (singleton, foldl', foldr, fromList, (++))
import Data.Maybe   (fromJust)
 

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

\begin{code}
{-@ measure size @-}
{-@ size :: [a] -> Nat @-}
size :: [a]->Int
size []     = 0
size (_:rs) = 1 + size rs
\end{code}
