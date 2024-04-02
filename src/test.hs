{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
module Tutorial_03_Basic where

import Prelude hiding (abs)
divide  :: Int -> Int -> Int

die     :: String -> a
{-@ die :: {v:String | false} -> a  @-}
die msg = error msg


-- {-@ fail nonsense  @-}
-- {-@ fail canDie    @-}
-- {-@ fail divide'   @-}
-- {-@ fail avg       @-}
-- {-@ fail percentT  @-}
-- {-@ fail percentF  @-}
-- {-@ fail cpc  @-}
-- {-@ fail cpi  @-}
-- {-@ ignore lAssert @-}


{-@ type Zero    = {v:Int | v == 0} @-}
{-@ type NonZero = {v:Int | v /= 0} @-}
{-@ zero :: Zero @-}
zero  = 0 :: Int

{-@ one, two, three :: NonZero @-}
one   = 1 :: Int
two   = 2 :: Int
three = 3 :: Int
nonsense :: Int
nonsense = one'
  where
  {-@ one' :: Zero @-}
  one' = 1 
{-@ type Nat      = {v:Int | 0 <= v}        @-}

{-@ type Positive = {v:Int | 0 < v}         @-}

{-@ type Even     = {v:Int | v mod 2 == 0 } @-}

{-@ type TensToHundred = {v:Int | v mod 10 == 0 && v <= 100} @-}
-- write the alias here

-- {-@ percentT  :: Percentage  @-}
percentT    = 10 :: Int
-- {-@ percentF  :: Percentage  @-}
percentF :: Int
percentF    = 10 + 99 :: Int
divide'     :: Int -> Int -> Int
divide' n 0 = die "divide by zero"
divide' n d = n `div` d
{-@ divide :: Int -> NonZero -> Int @-}
divide _ 0 = die "divide by zero"
divide n d = n `div` d
abs           :: Int -> Int
abs n
  | 0 < n     = n
  | otherwise = 0 - n
{-@ abs :: Int -> Nat @-}
{-@ plus1 :: a:Int -> {b:Int |b > a}@-}
plus1 :: Int -> Int 
plus1 a = a + 1
calcPer       :: Int -> Int -> Int
calcPer a b    = (b * 100) `div` a



cpc = calcPer 10 5 :: Int  -- should be correct
cpi = calcPer 10 11 :: Int -- should be incorrect
