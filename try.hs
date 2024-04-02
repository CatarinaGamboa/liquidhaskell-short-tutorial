{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module Tutorial_05_Datatypes
       (
       )
      where

import Data.Vector  hiding (singleton, foldl', foldr, fromList, (++))

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg

-- {-@ fail badSP @-}
-- {-@ fail badSP' @-}
-- {-@ fail badList @-}
-- {-@ ignore append @-}
-- {-@ fail badBST @-}
-- {-@ fail ne1 @-}
-- {-@ ignore delMin @-}



{-@ measure size @-}
{-@ size :: [a] -> Nat @-}
size :: [a] -> Int
size []     = 0
size (_:rs) = 1 + size rs
-- write notEmpty measure
{-@ type ListN a N = {v:[a] | size v == N} @-}
-- write the alias here

-- Remove the comments below to test the alias
-- {-@ ne1 :: NEList Int@-}
-- ne1 = [] ::  [Int]
-- {-@ ne1 :: NEList Int@-}
-- ne2 = [1,2,3,4] :: [Int]
data Sparse a = SP { spDim   :: Int
                   , spElems :: [(Int, a)] }
{-@ data Sparse a = SP { spDim   :: Nat
                       , spElems :: [(Btwn 0 spDim, a)]} @-}
{-@ type Nat        = {v:Int | 0 <= v}            @-}
{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-} 
okSP :: Sparse String
okSP = SP 5 [ (0, "cat")
            , (3, "dog") ]
badSP :: Sparse String
badSP = SP 5 [ (0, "cat")
             , (6, "dog") ]
-- badSP' :: Sparse String
-- write the alias here
-- dotProd :: Vector Int -> Sparse Int -> Int
-- {-@ dotProd :: x:Vector Int -> SparseN Int (vlen x) -> Int @-}
-- dotProd x (SP _ y) = go 0 y
--  where
--    go sum ((i, v) : y') = go (sum + (x ! i) * v) y'
--    go sum []            = sum
