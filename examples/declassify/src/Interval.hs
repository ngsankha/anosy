

{-# LANGUAGE RecordWildCards #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Interval where

import SecretDefn
import Prelude hiding (max, min, length)

{-@
data IntRange = IntRange {
      lower :: Int
    , upper :: {v:Int | lower <= v }
    }
@-}
data IntRange = IntRange {
      lower :: Int
    , upper :: Int
    }
    deriving (Show)

{-@ data Range <p:: Secret -> Bool, n :: Secret -> Bool> = Range {
      bounds :: [IntRange]
    , pD     :: lp:{Secret | betweenSecretRec (secretToLst lp) bounds} -> {ll: Secret<p> | lp = ll }
    , nD     :: ln:{Secret | not(betweenSecretRec (secretToLst ln) bounds)} -> {ll: Secret<n> | ln = ll }
    } | RangeEmpty { negD :: ln: Secret -> {ll: Secret<n> | ln == ll }}
      | RangeFull  { posD :: lp: Secret -> {ll: Secret<p> | lp == ll }}
    @-}
data Range = Range {
      bounds :: [IntRange]
    , pD     :: Secret -> Secret
    , nD     :: Secret -> Secret
    } | RangeEmpty { negD :: Secret -> Secret }
      | RangeFull  { posD :: Secret -> Secret }

instance Show Range where
  show (RangeEmpty _) = "RangeEmpty"
  show (RangeFull _) = "RangeFull"
  show (Range b _ _) = "Range " ++ show b

{-@ reflect betweenSecret @-}
betweenSecret :: Secret -> Range -> Bool
betweenSecret l (Range bounds _ _) = betweenSecretRec (secretToLst l) bounds
betweenSecret _ (RangeEmpty _) = False
betweenSecret _ (RangeFull _) = True

{-@ reflect betweenSecretRec @-}
betweenSecretRec :: [Int] -> [IntRange] -> Bool
betweenSecretRec (i:rest) (r:restbounds) = (betweenInt i r) && (betweenSecretRec rest restbounds)
betweenSecretRec [] _ = True
betweenSecretRec _ [] = True
betweenSecretRec [] [] = True

{-@ reflect betweenInt @-}
betweenInt :: Int -> IntRange -> Bool
betweenInt x IntRange{..} = lower <= x && x <= upper

{-@ reflect subsetInt @-}
subsetInt :: IntRange -> IntRange -> Bool
subsetInt (IntRange l1 u1) (IntRange l2 u2) = l1 >= l2 && u1 <= u2

{-@ subsetIntProof :: i : Int
                      -> r1 : IntRange
                      -> {r2 : IntRange | subsetInt r1 r2}
                      -> {betweenInt i r1 => betweenInt i r2} @-}
subsetIntProof :: Int -> IntRange -> IntRange -> ()
subsetIntProof i r1 r2 = ()

{-@ length :: [a] -> Nat @-} 
length :: [a] -> Int 
length []     = 0 
length (_:xs) = 1 + length xs

{-@ measure length @-}

(?) :: a -> () -> a
x ? _ = x

{-@ (==.) :: x:a -> y:{a | x == y} ->
      {o:a | o == y && o == x} @-}

(==.) :: a -> a -> a
_ ==. x = x

{-@ subsetRangeRecProof :: i : [Int]
                      -> r1 : [IntRange]
                      -> {r2 : [IntRange] | (subsetRangeRec r1 r2) && (length i == length r1) && (length i == length r2)}
                      -> {betweenSecretRec i r1 => betweenSecretRec i r2} @-}
subsetRangeRecProof :: [Int] -> [IntRange] -> [IntRange] -> ()
subsetRangeRecProof [] [] [] = ()
subsetRangeRecProof (x:xs) (y:ys) (z:zs) = (subsetIntProof x y z) ? subsetRangeRecProof xs ys zs

{-@ subsetRangeProof :: i : Secret
                      -> r1 : Range
                      -> {r2 : Range | (subsetRange r1 r2) && (length (secretToLst i) == length (bounds r1)) && (length (secretToLst i) == length (bounds r2))}
                      -> {betweenSecret i r1 => betweenSecret i r2} @-}
subsetRangeProof :: Secret -> Range -> Range -> ()
subsetRangeProof i (Range r1 _ _) (Range r2 _ _) = subsetRangeRecProof (secretToLst i) r1 r2
subsetRangeProof i (RangeEmpty _) _ = ()
subsetRangeProof i _ (RangeFull _) = ()
subsetRangeProof i _ _ = ()

{-@ reflect sizeInterval @-}
sizeInterval :: IntRange -> Int
sizeInterval (IntRange lower upper) = upper - lower + 1

{-@ reflect validIntRange @-}
validIntRange :: IntRange -> Bool
validIntRange r = lower r <= upper r

{-@ reflect validIntRanges @-}
validIntRanges :: [IntRange] -> Bool
validIntRanges [] = True
validIntRanges (x:xs) = validIntRange x && validIntRanges xs

{-@ reflect sizeLst @-}
sizeLst :: [IntRange] -> Int
sizeLst [] = 1
sizeLst (hd:tl) = (sizeInterval hd) * (sizeLst tl)

{-@ sizeIntervalProof :: r1 : IntRange 
                  -> {r2 : IntRange | subsetInt r1 r2 && validIntRange r1 && validIntRange r2}
                  -> {sizeInterval r1 <= sizeInterval r2 && sizeInterval r1 >= 0 } @-}
sizeIntervalProof :: IntRange -> IntRange -> ()
sizeIntervalProof r1 r2 = ()

{-@ sizeListProof ::  r1 : [IntRange]
                  -> {r2 : [IntRange] | (subsetRangeRec r1 r2) && (length r1 == length r2) && validIntRanges r1 && validIntRanges r2}
                  -> {sizeLst r1 <= sizeLst r2 && sizeLst r1 >= 0} @-}
sizeListProof :: [IntRange] -> [IntRange] -> ()
sizeListProof [] [] = ()
sizeListProof (x:xs) (y:ys) = (sizeIntervalProof x y) ? sizeListProof xs ys

{-@ reflect size @-}
size :: Range -> Int
size (Range lst _ _) = sizeLst lst
size (RangeEmpty _)  = 0
size (RangeFull _) = -1

{-@ reflect sizeCheck @-}
sizeCheck :: Range -> Range -> Bool
sizeCheck r1@(Range _ _ _) r2@(Range _ _ _) = size r1 <= size r2 && size r1 >= 0
sizeCheck r1@(RangeEmpty _) _ = True
sizeCheck _ r2@(RangeFull _) = True
sizeCheck _ _ = False

{-@ sizeLaw :: r1 : Range
            -> {r2: Range | subsetRange r1 r2 && validIntRanges (bounds r1) && validIntRanges (bounds r2) && length (bounds r1) == length (bounds r2)}
            -> { sizeCheck r1 r2 } @-}
sizeLaw :: Range -> Range -> ()
sizeLaw r1@(Range b1 _ _) r2@(Range b2 _ _) = sizeListProof b1 b2
sizeLaw r1@(RangeEmpty _) _ = ()
sizeLaw _ r2@(RangeFull _) = ()
sizeLaw _ _ = ()

{-@ reflect subsetRange @-}
subsetRange :: Range -> Range -> Bool
subsetRange (Range b1 _ _) (Range b2 _ _) = subsetRangeRec b1 b2
subsetRange (RangeEmpty _) _ = True
subsetRange _ (RangeFull _)  = True
subsetRange _ _              = False

{-@ reflect subsetRangeRec @-}
subsetRangeRec :: [IntRange] -> [IntRange] -> Bool
subsetRangeRec (hd1:tl1) (hd2:tl2) = (subsetInt hd1 hd2) && (subsetRangeRec tl1 tl2)
subsetRangeRec [] _ = True
subsetRangeRec _ [] = True
subsetRangeRec [] [] = True

-- {-@ intersectLaw :: i: Secret
--              -> r1: Range
--              -> r2: Range
--              -> {r3: Range | r3 == intersect r1 r2}
--              -> {betweenSecret i r3 => (betweenSecret i r1 || betweenSecret i r2) } @-}
-- intersectLaw :: Secret -> Range -> Range -> Range -> ()
-- intersectLaw i r1 r2 r3 = ()

{-@ ignore intersect @-}
{-@ assume intersect :: forall <p1::Secret -> Bool, p2::Secret -> Bool, p::Secret -> Bool, n1::Secret -> Bool, n2::Secret -> Bool, n :: Secret -> Bool>. 
                 { Secret<n1>  <: Secret<n>  }
                 { Secret<n2>  <: Secret<n>  }
                 { l1::Secret <p1> |- {l:Secret<p2> | l == l1 } <: {l:Secret<p> | l == l1 } }
                 l1:Range<p1,n1> -> l2:Range<p2,n2> 
              -> {l:Range<p,n> | subsetRange l l1 && subsetRange l l2  } @-}
intersect :: Range -> Range -> Range
intersect (RangeEmpty p) _ = RangeEmpty p
intersect (RangeFull p1) l2 = case l2 of 
     RangeEmpty p2 -> RangeEmpty p2 
     RangeFull  p2 -> RangeFull (\l -> p1 l `interloc` p2 l)
     Range b p2 n2 -> Range b (intersectPFull l2 p2 p1) n2
intersect l1@(Range b1 p1 n1) l2 = case l2 of 
     RangeEmpty p2 -> RangeEmpty p2 
     RangeFull  p  -> Range b1 p1 n1
     Range b2 p2 n2 
            -> if validIntersectionRanges b1 b2
                 then Range (intersectIntRanges b1 b2) (intersectP l1 l2 p1 p2) (intersectN l1 l2 n1 n2)
                 else RangeEmpty (intersectN l1 l2 n1 n2)

{-@ reflect intersectIntRanges @-}
{-@ intersectIntRanges :: b1:[IntRange]
                       -> {b2:[IntRange] | validIntersectionRanges b1 b2}
                       -> [IntRange] @-}
intersectIntRanges :: [IntRange] -> [IntRange] -> [IntRange]
intersectIntRanges ((IntRange l1 u1):tl1) ((IntRange l2 u2):tl2) = (IntRange l u):(intersectIntRanges tl1 tl2) where
  l = max l1 l2
  u = min u1 u2
intersectIntRanges [] _ = []
intersectIntRanges _  _ = []

{-@ reflect validIntersectionRanges @-}
validIntersectionRanges :: [IntRange] -> [IntRange] -> Bool
validIntersectionRanges ((IntRange l1 u1):tl1) ((IntRange l2 u2):tl2) = ((max l1 l2) <= (min u1 u2)) && (validIntersectionRanges tl1 tl2)
validIntersectionRanges [] _ = True
validIntersectionRanges _ _ = True

{-@ intersectPFull :: forall <p1::Secret -> Bool, p2::Secret -> Bool, p::Secret -> Bool, n1::Secret -> Bool, n2::Secret -> Bool, n::Secret -> Bool>. 
                 { l1::Secret <p1> |- {l:Secret<p2> | l == l1 } <: {l:Secret<p> | l == l1 } }
                 l1:Range<p1, n1>
              -> (xl1:{Secret| betweenSecret xl1 l1 } -> {l:Secret<p1> | xl1 == l})
              -> (xl2:Secret -> {l:Secret<p2> | xl2 == l})
              -> xl:{Secret | betweenSecret xl l1 }
              -> {l:Secret<p> | l == xl}  @-}
intersectPFull :: Range 
           -> (Secret -> Secret)
           -> (Secret -> Secret)
           -> Secret
           -> Secret   
intersectPFull  l1  p1 p2 x =  p2 x `interloc` p1 x


{-@ intersectP :: forall <p1::Secret -> Bool, p2::Secret -> Bool, p::Secret -> Bool, n1::Secret -> Bool, n2::Secret -> Bool, n::Secret -> Bool>. 
                 { l1::Secret <p1> |- {l:Secret<p2> | l == l1 } <: {l:Secret<p> | l == l1 } }
                 l1:Range<p1, n1> -> l2:Range<p2, n2> 
              -> (xl1:{Secret| betweenSecret xl1 l1 } ->  {l:Secret<p1> | l == xl1 })
              -> (xl2:{Secret| betweenSecret xl2 l2 } ->  {l:Secret<p2> | l == xl2 })
              -> xl:{Secret | betweenSecret xl l1 && betweenSecret xl l2 } 
              -> {l:Secret<p> | l == xl }  @-}
intersectP :: Range -> Range 
           -> (Secret -> Secret)
           -> (Secret -> Secret)
           -> Secret
           -> Secret   
intersectP  l1 l2  p1 p2 x =  p2 x `interloc` p1 x



{-@ intersectN :: forall <p1::Secret -> Bool, p2::Secret -> Bool, p::Secret -> Bool, n1::Secret -> Bool, n2::Secret -> Bool, n::Secret -> Bool>. 
                 { Secret<n1>  <: Secret<n>  }
                 { Secret<n2>  <: Secret<n>  }
                 l1:Range<p1, n1> -> l2:Range<p2, n2> 
              -> (xl1:{Secret | not ( betweenSecret xl1 l1) } ->  {ll:Secret<n1> | ll = xl1 }) 
              -> (xl2:{Secret | not ( betweenSecret xl2 l2) } ->  {ll:Secret<n2> | ll = xl2 })
              -> xl:{Secret | not (betweenSecret xl l1) || not (betweenSecret xl l2) }
              -> {l:Secret<n> | l == xl}  @-}
intersectN :: Range -> Range 
           -> (Secret -> Secret)
           -> (Secret -> Secret)
           -> Secret
           -> Secret   
intersectN l1 l2 p1 p2 x
  | not (betweenSecret x l1)
  = p1 x
  | not (betweenSecret x l2)
  = p2 x



{-@ reflect max @-}
max :: Int -> Int -> Int
max x y = if x >= y then x else y

{-@ reflect min @-}
min :: Int -> Int -> Int
min x y = if x <= y then x else y


{-@ interloc :: forall <p1::Secret -> Bool, p2::Secret -> Bool, p::Secret -> Bool>. 
                 { l1::Secret <p1> |- {l:Secret<p2> | l == l1 } <: {l:Secret<p> | l == l1 } }
                 l1:Secret<p1> -> l2:{Secret<p2> | l1 == l2} -> {l:Secret<p> | l == l1 && l == l2}  @-}
interloc :: Secret -> Secret -> Secret 
interloc _ l = l

refine :: Range -> Range
{-@ assume refine :: lr:Range -> {v:Range<{l:Secret | betweenSecret l lr}, {l:Secret |  not (betweenSecret l lr)}>  | v == lr } @-}
refine lr = lr 


{-@ propEmpty :: li:Secret -> {lr:Secret | li = lr } @-}
propEmpty :: Secret -> Secret 
propEmpty li = li
