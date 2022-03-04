{-# LANGUAGE RecordWildCards #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module PowerSet where

import Interval
import SecretDefn
import Prelude hiding (max, min, length)

{-@
data PowerSet <p :: Secret -> Bool, n :: Secret -> Bool> = PowerSet {
      pos :: [Range]
    , neg :: [Range]
    , pD  :: lp:{Secret | (inPowerSet lp pos) && not (inPowerSet lp neg)} -> {ll: Secret<p> | lp = ll }
    , nD  :: ln:{Secret | not (inPowerSet ln pos) || (inPowerSet ln neg)} -> {ll: Secret<n> | ln = ll }
} | PowerSetEmpty { negD :: ln: Secret -> {ll: Secret<n> | ln == ll }}
  | PowerSetFull  { posD :: lp: Secret -> {ll: Secret<p> | lp == ll }}
@-}
data PowerSet = PowerSet {
      pos :: [Range]
    , neg :: [Range]
    , pD  :: Secret -> Secret
    , nD  :: Secret -> Secret
} | PowerSetEmpty { negD :: Secret -> Secret }
  | PowerSetFull  { posD :: Secret -> Secret }

instance Show PowerSet where
  show (PowerSet pos neg _ _) = "PowerSet (" ++ (show pos) ++ ") - (" ++ (show neg) ++ ")"

{-@ reflect secretInPowerset @-}
secretInPowerset :: Secret -> PowerSet -> Bool
secretInPowerset s (PowerSet pos neg _ _) = (inPowerSet s pos) && not (inPowerSet s neg)
secretInPowerset _ (PowerSetFull _) = True
secretInPowerset _ (PowerSetEmpty _) = False

{-@ reflect inPowerSet @-}
inPowerSet :: Secret -> [Range] -> Bool
inPowerSet s (hd:tl) = (betweenSecret s hd) || (inPowerSet s tl)
inPowerSet s [] = False

{-@ reflect subsetPowerSet @-}
subsetPowerSet :: PowerSet -> PowerSet -> Bool
subsetPowerSet (PowerSet poslist1 neglist1 _ _) (PowerSet poslist2 neglist2 _ _) = subsetList poslist1 neglist1 poslist2 neglist2
subsetPowerSet (PowerSetEmpty _) _ = True
subsetPowerSet _ (PowerSetFull _) = True
subsetPowerSet _ _ = False

{-@ reflect subsetList @-}
subsetList :: [Range] -> [Range] -> [Range] -> [Range] -> Bool
subsetList (poshd1:postl1) neglist1 poslist2 (neghd2:negtl2) = (subsetOne poshd1 poslist2) && (subsetList postl1 neglist1 poslist2 negtl2)
subsetList [] neglist1 poslist2 (neghd2:negtl2) = (subsetOne neghd2 neglist1) && (subsetList [] neglist1 poslist2 negtl2)
subsetList _ _ _ _ = True

{-@ reflect subsetOne @-}
subsetOne :: Range -> [Range] -> Bool
subsetOne range (hd:tl) = (subsetRange range hd) || (subsetOne range tl)
subsetOne _ [] = False


{-@ ignore intersectPowerSet @-}
intersectPowerSet :: PowerSet -> PowerSet -> PowerSet
{-@ assume intersectPowerSet :: forall <p1::Secret -> Bool, p2::Secret -> Bool, p::Secret -> Bool, n1::Secret -> Bool, n2::Secret -> Bool, n::Secret -> Bool>.
                  { Secret<n1> <: Secret<n> }
                  { Secret<n2> <: Secret<n> }
                  { l1::Secret<p1> |- {l:Secret<p2> | l == l1} <: {l:Secret<p> | l == l1}}
                  l1:PowerSet<p1,n1> -> l2:PowerSet<p2,n2>
                  -> {l:PowerSet<p,n> | subset l l1 && subset l l2} @-}
intersectPowerSet l1@(PowerSet pos1 neg1 p1 n1) l2@(PowerSet pos2 neg2 p2 n2) = PowerSet (intersectPowerSetElem pos1 pos2) (neg1 ++ neg2) (intersectPowerSetP l1 l2 p1 p2) (intersectPowerSetN l1 l2 p1 p2)

intersectPowerSetElem :: [Range] -> [Range] -> [Range]
intersectPowerSetElem (hd:tl) l2 = (intersectPowerSetOne hd l2) ++ (intersectPowerSetElem tl l2)
intersectPowerSetElem [] l2 = []

intersectPowerSetOne :: Range -> [Range] -> [Range]
intersectPowerSetOne dom l = map (intersect dom) l

{-@ intersectPowerSetP :: forall <p1::Secret -> Bool, p2::Secret -> Bool, p::Secret -> Bool, n1::Secret -> Bool, n2::Secret -> Bool, n::Secret -> Bool>. 
                 { l1::Secret <p1> |- {l:Secret<p2> | l == l1 } <: {l:Secret<p> | l == l1 } }
                 l1:PowerSet<p1, n1> -> l2:PowerSet<p2, n2> 
              -> (xl1:{Secret| secretInPowerset xl1 l1 } ->  {l:Secret<p1> | l == xl1 })
              -> (xl2:{Secret| secretInPowerset xl2 l2 } ->  {l:Secret<p2> | l == xl2 })
              -> xl:{Secret | secretInPowerset xl l1 && secretInPowerset xl l2 } 
              -> {l:Secret<p> | l == xl }  @-}
intersectPowerSetP :: PowerSet -> PowerSet 
           -> (Secret -> Secret)
           -> (Secret -> Secret)
           -> Secret
           -> Secret   
intersectPowerSetP  l1 l2  p1 p2 x =  p2 x `interloc` p1 x

{-@ ignore intersectPowerSetN @-}
{-@ intersectPowerSetN :: forall <p1::Secret -> Bool, p2::Secret -> Bool, p::Secret -> Bool, n1::Secret -> Bool, n2::Secret -> Bool, n::Secret -> Bool>. 
                 { Secret<n1>  <: Secret<n>  }
                 { Secret<n2>  <: Secret<n>  }
                 l1:PowerSet<p1, n1> -> l2:PowerSet<p2, n2> 
              -> (xl1:{Secret | not ( secretInPowerset xl1 l1) } ->  {ll:Secret<n1> | ll = xl1 }) 
              -> (xl2:{Secret | not ( secretInPowerset xl2 l2) } ->  {ll:Secret<n2> | ll = xl2 })
              -> xl:{Secret | not (secretInPowerset xl l1) || not (secretInPowerset xl l2) }
              -> {l:Secret<n> | l == xl}  @-}
intersectPowerSetN :: PowerSet -> PowerSet 
           -> (Secret -> Secret)
           -> (Secret -> Secret)
           -> Secret
           -> Secret   
intersectPowerSetN l1 l2 p1 p2 x
  | not (secretInPowerset x l1)
  = p1 x
  | not (secretInPowerset x l2)
  = p2 x

refine :: PowerSet -> PowerSet
{-@ assume refine :: lr:PowerSet -> {v:PowerSet<{l:Secret | secretInPowerset l lr}, {l:Secret |  not (secretInPowerset l lr)}>  | v == lr } @-}
refine lr = lr 

{-@ propEmpty :: li:Secret -> {lr:Secret | li = lr } @-}
propEmpty :: Secret -> Secret 
propEmpty li = li

{-@ reflect sizePowerset @-}
sizePowerset :: PowerSet -> Int
sizePowerset (PowerSet pos neg _ _) = (sizeRange pos) - (sizeRange neg)
sizePowerset (PowerSetEmpty _)  = 0
sizePowerset (PowerSetFull _) = -1

{-@ reflect sizeRange @-}
sizeRange :: [Range] -> Int
sizeRange [] = 0
sizeRange (hd:tl) = (size hd) + (sizeRange tl)
