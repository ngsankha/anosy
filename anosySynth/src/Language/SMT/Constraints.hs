{-# LANGUAGE QuasiQuotes #-}

module Language.SMT.Constraints where

import Data.String.Interpolate (i)
import Annotations (Annotation)
import Unique (Unique)
import Language.SMT.ToSMT (sepBy)
import Utils (first, second, annName)
import Domains.PowerSet (PowerSet(..), Range(..), IntRange(..))

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

betweeenSMT :: Annotation -> (Unique, [[(String, (Int, Int))]]) -> PowerSet -> String
betweeenSMT ann boundMap pset = [i|
(define-fun between ((p #{name}) (r #{name}Range)) Bool 
  (and #{sepBy " " (map betweenAxis bounds)}))
|]
  where
    name = annName ann
    bounds = head (second boundMap)

betweenAxis :: (String, (Int, Int)) -> String
betweenAxis bound = [i|(betweenInt (#{axis} p) (#{axis}R r))|]
  where
    axis = first bound

psetPosContains :: [(String, (Int, Int))] -> PowerSet -> String
psetPosContains bounds (PowerSet [] _) = ""
psetPosContains bounds (PowerSet pos []) = [i|
(and #{sepBy " " (map (betweenRangeConc bounds) pos)})
|]
psetPosContains bounds (PowerSet pos neg) = [i|
(and #{sepBy " " (map (betweenRangeConc bounds) pos)}
     (not (or #{sepBy " " (map (betweenRangeConc bounds) neg)})))
|]

betweenRangeConc :: [(String, (Int, Int))] -> Range -> String
betweenRangeConc bounds (Range boundConc) = [i|
(and #{sepBy " " (map betweenRangeConcInd pairedBounds)})
|]
  where
    pairedBounds = zip bounds boundConc

betweenRangeConcInd :: ((String, (Int, Int)), IntRange) -> String
betweenRangeConcInd ((axis, _), (IntRange l u)) = [i|
(betweenInt #{axis} (IntRange #{l} #{u}))
|]

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

underapproxAux :: String -> String
underapproxAux "" = ""
underapproxAux smt  = "(not " ++ smt ++ ")"
solverQuery :: Annotation -> (String, String, Int) -> [(String, (Int, Int))]
            -> (Unique, [[(String, (Int, Int))]])
            -> PowerSet -> Bool -> String
solverQuery ann ("underapprox", func, _) dataFields boundMap pset True = [i|
(assert
  (forall (#{forallParams dataFields})
    (=> (between #{secretConstructor (annName ann) dataFields} #{absConstructor (annName ann) dataFields})
      (and (#{func} #{secretConstructor (annName ann) dataFields})
            #{underapproxAux (psetPosContains bounds pset)}))))
|]
  where
    bounds = head (second boundMap)
solverQuery ann ("underapprox", func, _) dataFields boundMap pset False = [i|
(assert
  (forall (#{forallParams dataFields})
    (=> (between #{secretConstructor (annName ann) dataFields} #{absConstructor (annName ann) dataFields})
      (and (not (#{func} #{secretConstructor (annName ann) dataFields}))
           #{underapproxAux (psetPosContains bounds pset)}))))
|]
  where
    bounds = head (second boundMap)
solverQuery ann ("overapprox", func, 1) dataFields boundMap pset True = [i|
(assert
  (forall (#{forallParams dataFields})
    (=> (and (#{func} #{secretConstructor (annName ann) dataFields})
             #{forallBounds dataFields})
    (between #{secretConstructor (annName ann) dataFields} #{absConstructor (annName ann) dataFields}))))
|]
  where
    bounds = head (second boundMap)
solverQuery ann ("overapprox", func, _) dataFields boundMap pset True = [i|
(assert
  (forall (#{forallParams dataFields})
    (=> (between #{secretConstructor (annName ann) dataFields} #{absConstructor (annName ann) dataFields})
      (and (not (#{func} #{secretConstructor (annName ann) dataFields}))
            #{psetPosContains bounds pset}))))
|]
  where
    bounds = head (second boundMap)
solverQuery ann ("overapprox", func, 1) dataFields boundMap pset False = [i|
(assert
  (forall (#{forallParams dataFields})
    (=> (and (not (#{func} #{secretConstructor (annName ann) dataFields}))
            #{forallBounds dataFields})
    (between #{secretConstructor (annName ann) dataFields} #{absConstructor (annName ann) dataFields}))))
|]
  where
    bounds = head (second boundMap)
solverQuery ann ("overapprox", func, _) dataFields boundMap pset False = [i|
(assert
  (forall (#{forallParams dataFields})
    (=> (between #{secretConstructor (annName ann) dataFields} #{absConstructor (annName ann) dataFields})
      (and (#{func} #{secretConstructor (annName ann) dataFields})
            #{psetPosContains bounds pset}))))
|]
  where
    bounds = head (second boundMap)
solverQuery _ _ _ _ _ _ = error "unexpected module annotation"

absConstructor :: String -> [(String, (Int, Int))] -> String
absConstructor name dataFields = [i|(#{name}Range #{(sepBy " " (map rangeConstructor (map first dataFields)))})|]

rangeConstructor :: String -> String
rangeConstructor field = [i|(IntRange #{field}min #{field}max)|]

forallParams :: [(String, (Int, Int))] -> String
forallParams dataFields = sepBy " " (map (\x -> [i|(#{first x} Int)|]) dataFields)

optQuery :: (String, String, Int) -> [(String, (Int, Int))] -> String
optQuery ("underapprox", _, _) dataFields = sepBy "\n" (map (\x -> [i|(maximize (- #{x}max #{x}min))|]) (map first dataFields))
optQuery ("overapprox",  _, 1) dataFields = sepBy "\n" (map (\x -> [i|(minimize (- #{x}max #{x}min))|]) (map first dataFields))
optQuery ("overapprox",  _, _) dataFields = sepBy "\n" (map (\x -> [i|(maximize (- #{x}max #{x}min))|]) (map first dataFields))
optQuery _ _ = error "unexpected optimization directive"

secretConstructor :: String -> [(String, (Int, Int))] -> String
secretConstructor name dataFields = [i|(#{name} #{sepBy " " (map first dataFields)})|]
