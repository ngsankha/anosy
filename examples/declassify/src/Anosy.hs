{-# LANGUAGE MultiParamTypeClasses #-}

module Anosy where 

import Control.Monad.Trans.State.Lazy
import Control.Monad.Trans.Class
import Control.Exception
import LIO 
import LIO.DCLabel
import LIO.TCB (ioTCB, Labeled(..))

import Data.HashMap.Strict 
import Data.Maybe 
import Data.Hashable
import Prelude hiding (lookup)
import SecretDefn (Secret)

-- The State of Anosy is the abstract domain, 
-- defined as data in case we want to expans it 
data AnosyST dom secret = AnosyST {
    policy   :: (dom, dom) -> (Bool, Bool),
    secrets  :: HashMap secret dom,
    initKnow :: dom, 
    queries  :: HashMap String (QInfo secret dom) 
    }

data QInfo secret dom 
  = QInfo { quer  :: secret -> Bool
          , sound_approx :: dom -> (dom,dom) 
          , complete_approx :: dom -> (dom,dom)  }

data Check = UnderApprox | OverApprox 

type AnosyT dom secret m = StateT (AnosyST dom secret) m

class Unprotectable p where 
  unprotect :: p a -> a 


downgrade :: (Monad m, Eq secret, Hashable secret, Unprotectable p)
              => Check
              -> p secret 
              -> String 
              -> AnosyT dom secret m Bool
downgrade approx secret' queryName = do
        st <- get
        let secret = unprotect secret' 
        let prior = findWithDefault (initKnow st) secret (secrets st)
        let qinfo = lookup queryName (queries st)
        if isJust qinfo then do
          let (postTrue, postFalse) = pickCheck approx (fromJust qinfo) prior
          let (trueSafe, falseSafe) = (policy st) (postTrue, postFalse)
          if trueSafe && falseSafe then do
            let response = quer (fromJust qinfo) secret
            let posterior = if response then postTrue else postFalse
            modify $ \st -> st {secrets = insert secret posterior (secrets st)}
            return $ response
          else return $ throw $ userError "unsafe"
        else return $ throw $ userError ("cannot downgrade query " ++ queryName)

class AbsDom dom where 
    contains  :: Secret -> dom -> Bool
    subset    :: dom -> dom -> Bool
    intersect :: dom -> dom -> dom


pickCheck :: Check -> QInfo secret dom  -> (dom -> (dom, dom))
pickCheck UnderApprox q = sound_approx q 
pickCheck OverApprox  q = complete_approx q 
