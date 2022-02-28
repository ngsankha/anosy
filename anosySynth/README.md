# GHC Plugin

### Setup

The following command will download dependencies, build and install the plugin
in the package environment called `qif`.

```
cabal v2-install --lib --package-env=qif
```

### Example

Given a Haskell input:

```hs
{-@ LIQUID "--reflection" @-}

module ShipLocLiquid where

import Prelude hiding (abs)
import Point

{-@ reflect abs @-}
abs :: Int -> Int
{-@ abs :: Int -> Nat @-}
abs i | i < 0 = -1 * i
abs i         = i

{-@ reflect nearby @-}
nearby :: Point -> Bool
nearby z = abs (x z - x l) + abs (y z - y l) <= d
    where
        l = Point 200 200
        d = 100

{-# ANN module ("sound", "nearby", "Rectangle") #-}
```

The `ANN` annotation tells the plugin to generate soundness theorem for `nearby`
function with the `Rectangle` abstract domain.

To run the plugin use the command: `ghc -package-env qif -fplugin=HsToSMT ShipLocLiquid.hs`

It will output the following file. The generated file imports the user
definition and verifies through LiquidHaskell.

```hs
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module ShipLocLiquidGen where

import Point
import Range
import Rectangle
import ShipLocLiquid

{-@ sound :: secret: Point
       -> {prior: Rectangle | betweenPoint secret prior}
       -> {response: Bool | response <=> nearby secret}
       -> {post:Rectangle<{l:Point | nearby secret <=> nearby l}, {\_ -> True}> | subsetRect post prior  }
@-}
sound :: Point -> Rectangle -> Bool -> Rectangle
sound secret prior response 
  = prior `intersect` soundHelper secret prior response

{-@ soundHelper :: secret: Point
       -> {prior: Rectangle | betweenPoint secret prior}
       -> {response: Bool | response <=> nearby secret}
       -> Rectangle<{l:Point | nearby secret <=> nearby l}, {\_ -> True}> 
@-}
soundHelper :: Point -> Rectangle -> Bool -> Rectangle
soundHelper _secret _prior True 
  = Rectangle (Range 150 250) (Range 150 250) propNearby memptyNeg
soundHelper _secret _prior False 
  = Rectangle (Range 301 500) (Range 0 500) propNotNearby memptyNeg

{-@ propNearby :: xx:{Int | 150 <= xx && xx <= 250} 
               -> yy:{Int | 150 <= yy && yy <= 250}
               -> {l:Point <{v:Point | True <=> nearby v}> | x l = xx && y l = yy} @-}
propNearby :: Int -> Int -> Point 
propNearby x y = Point x y 

{-@ propNotNearby :: xx:{Int | 301 <= xx && xx <= 500} 
               -> yy:{Int | 0 <= yy && yy <= 500}
               -> {l:Point<{v:Point | False <=> nearby v}> | x l == xx && y l == yy }  @-}
propNotNearby :: Int -> Int -> Point 
propNotNearby x y = Point x y  

{-@ memptyNeg :: xx:Int -> yy:Int -> {l:Point | x l = xx && y l = yy } @-}
memptyNeg :: Int -> Int -> Point 
memptyNeg x y = Point x y 
```
