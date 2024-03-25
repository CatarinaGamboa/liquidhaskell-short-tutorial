{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module Test
      where

import Prelude      hiding (abs, length, min)


{-@ measure sizeH @-}
{-@ sizeH :: [a] -> Nat @-}
sizeH :: [a] -> Int
sizeH []     = 0
sizeH (_:rs) = 1 + sizeH rs

