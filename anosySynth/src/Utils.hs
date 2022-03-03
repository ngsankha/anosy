module Utils where

import Annotations (Annotation, AnnTarget(..), ann_target)
import Language.Ghc.Misc ()
import Data.List (find)

first :: (a, b) -> a
first (x, _) = x

second :: (a, b) -> b
second (_, x) = x

annName :: Annotation -> String
annName ann = case (ann_target ann) of
  NamedTarget name -> show name
  _ -> error "unexpected annotation"

modAnnot :: Annotation -> Bool
modAnnot ann = case (ann_target ann) of
  NamedTarget _ -> False
  ModuleTarget _ -> True

dataAnnot :: Annotation -> Bool
dataAnnot ann = not (modAnnot ann)

findNum :: (Foldable t, Eq a) => a -> t (a, c) -> Either String c
findNum label y = case (find (\x -> (fst x == label)) y) of
  Just t -> Right (snd t)
  Nothing -> Left "model not found"
