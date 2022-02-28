{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}

module Language.SMT.ToSMT where 

import TyCon
import DataCon
import Name 
import Var 
import TyCoRep 
import CoreSyn 
import Id 
import Literal
-- import TysWiredIn

import FastString

import Language.Ghc.Misc ()
import qualified Data.List  as L 
import qualified Data.Maybe as M
import           Data.Char (toUpper)

-- import Debug.Trace



class ToSMT a where 
  toSMT :: a -> String 

instance ToSMT Name where
  toSMT = show  

instance ToSMT Var where
  toSMT x = (if isTyVar x then mapHead toUpper else id) $ show x 
    where mapHead f (y:ys) = (f y:ys)
          mapHead _ []     = [] 

instance ToSMT FieldLabel where
  toSMT = unpackFS . flLabel


instance ToSMT [TyCon] where 
  toSMT tcs = sepBy "\n" (toSMT <$> reverse tcs) -- hack: find proper order 

instance ToSMT TyCon where 
  toSMT tc | isAlgTyCon tc 
    = paren ("declare-datatypes" <+>
                paren (sepBy " " (toSMT <$> tyConTyVars tc)) <+> 
                paren (paren ((toSMT $ tyConName tc) <+> 
                       sepBy " " (paren . toSMT <$> tyConDataCons tc))
                )
            ) <+> "\n"
  toSMT _ = error "toSMT: TypCon non AlgTypCon"

instance ToSMT DataCon where  
  toSMT dc 
    = toSMT (dataConName dc) <+> sepBy " " [paren (toSMT x <+> toSMT t) | (x,t) <- dataconFields dc]

instance ToSMT CoreProgram where 
    toSMT cbs = sepBy "\n" (toSMT <$> cbs')
      where cbs' = filter (not . isRecordSelectorBind) $ 
                   filter (not . isGhcInternalBind)    $ 
                   cbs

isRecordSelectorBind :: CoreBind -> Bool 
isRecordSelectorBind x = any isRecordSelector (binds x)
      

isGhcInternalBind :: CoreBind -> Bool 
isGhcInternalBind x = any isGhcInternalVar (binds x)

isGhcInternalVar :: Var -> Bool 
isGhcInternalVar x = "$" `L.isPrefixOf` show x

binds :: CoreBind -> [Var]
binds (NonRec x _) = [x]
binds (Rec xes)    = fst <$> xes 

instance ToSMT CoreBind where 
    toSMT (NonRec x e) 
      = paren ("define-fun" <+> toSMT x <+> paren (declareArgs xs) <+> declareRes <++> declareBody bd) <+> "\n"
      where declareArgs ys = sepBy " " [ paren (toSMT y <+> toSMT (varType y)) | y <- ys]
            declareBody    = paren . toSMT 
            declareRes     = toSMT $ resType $ varType x 
            (xs, bd)       = grabArgs $ simplify e 
    toSMT (Rec _)      = error "todo: Rec Functions"

resType :: Type -> Type 
resType (ForAllTy _ t) = resType t 
resType (FunTy _ _ t)    = resType t 
resType t              = t 

grabArgs :: CoreExpr -> ([Id], CoreExpr)
grabArgs = go [] 
  where go acc (Tick _ e) = go acc e 
        go acc (Lam x e) | isTyVar x = go acc e 
        go acc (Lam x e) = go (x:acc) e 
        go acc e         = (reverse acc, e)


grabApps :: CoreExpr -> (CoreExpr, [CoreExpr])
grabApps = go [] 
  where go acc (Tick _ e) = go acc e 
        go acc (App f e) = go (e:acc) f 
        go acc e         = (e, acc)        


instance ToSMT CoreExpr where
    toSMT (Lit l) = toSMT l 
    toSMT (Var x) = toSMT x 
    toSMT e@(App _ _) = let (f, es) = grabApps e in smtApp f es -- toSMTFun f <+> (sepBy " " (toSMTArg <$> es)) 
    toSMT e@(Let _ _)  = error ("toSMT CoreExpr on let " ++ show e)
    toSMT (Case c x _ [(_,_,ef), (_,_,et)]) | show (varType x) == "Bool"
        = "ite" <+> toSMTArg c <+> toSMTArg et <+> toSMTArg ef
    toSMT e@(Case _ x _ _) = error ("toSMT Case " ++ show (varType x) ++ "Expr = " ++ show e)
    toSMT e          = error ("toSMT CoreExpr on " ++ show e)

smtApp :: CoreExpr -> [CoreExpr] -> String  
smtApp (Var x) [e]
  | show x == "negate" = "- 0" <+> toSMTArg e
smtApp f es = case (show f) of
  "==" -> "=" <+> (sepBy " " (toSMTArg <$> es))
  "&&" -> "and" <+> (sepBy " " (toSMTArg <$> es))
  "||" -> "or" <+> (sepBy " " (toSMTArg <$> es))
  _    -> toSMT f <+> (sepBy " " (toSMTArg <$> es))

toSMTArg :: CoreExpr -> String 
toSMTArg l@(Lit _) = toSMT l 
toSMTArg v@(Var _) = toSMT v 
toSMTArg e         = paren $ toSMT e 

instance ToSMT Literal where
    toSMT (LitNumber _ i _) = show i 
    toSMT _ = error ("toSMt Literal on ... ")


subst :: (Var, CoreExpr) -> CoreExpr -> CoreExpr 
subst (x, ex) (Var y) 
  | x == y 
  = ex 
  | otherwise 
  = Var y  
subst su (App e1 e2)
  = App (subst su e1) (subst su e2)
subst su (Lam x e)
  = Lam x (subst su e)
subst _ (Case _ _ _ _) = error "todo: make subst into a type class..."
subst _ e 
  = e 

instance ToSMT Type where
  toSMT (TyVarTy x)    = toSMT x 
  toSMT t              = show t 


class Simplify a where 
  simplify :: a -> a 

instance Simplify CoreExpr where 
  simplify (App e (Type _)) = simplify e
  simplify (App e (Var x)) | isGhcInternalVar x = simplify e
  simplify (App (Var x) e) | show x == "I#" || show x == "D#" = simplify e 
  simplify (App e1 e2) = App (simplify e1) (simplify e2)
  simplify (Tick _ e) = simplify e 
  simplify (Lam x e) = Lam x (simplify e)
  simplify (Case e b t alts) = Case (simplify e) b t (simplify <$> alts)
  simplify (Let (NonRec x ex) e) = subst (x, simplify ex) $ simplify e  
  simplify e = e  

instance Simplify a => Simplify [a] where 
  simplify xs = simplify <$> xs 

instance Simplify (Expr a) => Simplify (Alt a) where 
  simplify (a,l,e) = (a, l, simplify e)

dataconFields :: DataCon -> [(FieldLabel, Type)]    
dataconFields dc =  M.catMaybes [ dataConFieldType_maybe dc (flLabel fl) | fl <- dataConFieldLabels dc ]

sepBy :: String -> [String] -> String 
sepBy sep xs = concat $ L.intersperse sep xs 

paren :: String -> String 
paren x = "(" ++ x ++ ")"

(<+>) :: String -> String -> String 
x <+> y = x ++ " " ++ y 

(<++>) :: String -> String -> String 
x <++> y = x ++ "\n" ++ y 


