{-# LANGUAGE QuasiQuotes #-}

module Language.SMT.Constraints where

import Data.String.Interpolate (i)
import Annotations (Annotation)
import Unique (Unique)
import Language.SMT.ToSMT (sepBy)
import Utils (first, second, annName)

intRangeSMT :: String
intRangeSMT = [i|
(declare-datatypes () ((IntRange (IntRange (lower Int) (upper Int))))) 

(define-fun betweenInt ((x Int) (r IntRange)) Bool
   (and (<= (lower r) x) (<= x (upper r)))) 
|]

absDataFields :: [(String, (Int, Int))] -> [String]
absDataFields items = map (\x -> [i|(#{first x}R IntRange)|]) items

absSMT :: Annotation -> (Unique, [[(String, (Int, Int))]]) -> String
absSMT ann bounds = [i|
(declare-datatypes () ((#{name}Range
  (#{name}Range
#{sepBy "\n" (absDataFields (head (second bounds)))}
  ))))|]
  where
    name = annName ann

betweeenSMT :: Annotation -> (Unique, [[(String, (Int, Int))]]) -> String
betweeenSMT ann bounds = [i|
(define-fun between ((p #{name}) (r #{name}Range)) Bool 
  (and #{sepBy " " (map betweenAxis (head (second bounds)))})) 
|]
  where
    name = annName ann

betweenAxis :: (String, (Int, Int)) -> String
betweenAxis bound = [i|(betweenInt (#{axis} p) (#{axis}R r))|]
  where
    axis = first bound

boundsSMT :: (String, (Int, Int)) -> String
boundsSMT b = [i|
(declare-fun #{axis}min () Int)
(declare-fun #{axis}max () Int)
(assert (<= #{axis}min #{axis}max)) 
(assert (<= #{lower} #{axis}min))
(assert (<= #{axis}max #{upper}))
|]
  where
    axis = first b
    lower = first (second b)
    upper = second (second b)

searchBounds :: [(String, (Int, Int))] -> String
searchBounds bounds = sepBy "\n" (map boundsSMT bounds)

forallBounds :: [(String, (Int, Int))] -> String
forallBounds bounds = sepBy " " (map (\x -> let label = (first x) in
  let bound = (second x) in
    [i|(<= #{label} #{second bound}) (<= #{first bound} #{label})|]) bounds)

solverQuery :: Annotation -> (String, String) -> [(String, (Int, Int))] -> Bool -> String
solverQuery ann ("underapprox", func) dataFields True = [i|
(assert
  (forall (#{forallParams dataFields})
    (=> (between #{secretConstructor (annName ann) dataFields} #{absConstructor (annName ann) dataFields})
      (#{func} #{secretConstructor (annName ann) dataFields}))))
|]
solverQuery ann ("underapprox", func) dataFields False = [i|
(assert
  (forall (#{forallParams dataFields})
    (=> (between #{secretConstructor (annName ann) dataFields} #{absConstructor (annName ann) dataFields})
      (not (#{func} #{secretConstructor (annName ann) dataFields})))))
|]
solverQuery ann ("overapprox", func) dataFields True = [i|
(assert
  (forall (#{forallParams dataFields})
    (=> (and (#{func} #{secretConstructor (annName ann) dataFields}) #{forallBounds dataFields})
      (between #{secretConstructor (annName ann) dataFields} #{absConstructor (annName ann) dataFields}))))
|]
solverQuery ann ("overapprox", func) dataFields False = [i|
(assert
  (forall (#{forallParams dataFields})
    (=> (and (not (#{func} #{secretConstructor (annName ann) dataFields})) #{forallBounds dataFields})
    (between #{secretConstructor (annName ann) dataFields} #{absConstructor (annName ann) dataFields}))))
|]
solverQuery _ _ _ _ = error "unexpected module annotation"

absConstructor :: String -> [(String, (Int, Int))] -> String
absConstructor name dataFields = [i|(#{name}Range #{(sepBy " " (map rangeConstructor (map first dataFields)))})|]

rangeConstructor :: String -> String
rangeConstructor field = [i|(IntRange #{field}min #{field}max)|]

forallParams :: [(String, (Int, Int))] -> String
forallParams dataFields = sepBy " " (map (\x -> [i|(#{first x} Int)|]) dataFields)

optQuery :: (String, String) -> [(String, (Int, Int))] -> String
optQuery ("underapprox"   , _) dataFields = sepBy "\n" (map (\x -> [i|(maximize (- #{x}max #{x}min))|]) (map first dataFields))
optQuery ("overapprox", _) dataFields = sepBy "\n" (map (\x -> [i|(minimize (- #{x}max #{x}min))|]) (map first dataFields))
optQuery _ _ = error "unexpected optimization directive"

secretConstructor :: String -> [(String, (Int, Int))] -> String
secretConstructor name dataFields = [i|(#{name} #{sepBy " " (map first dataFields)})|]
