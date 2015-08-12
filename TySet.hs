-- {-# OPTIONS_GHC -package=ghc-7.10.1 #-}
{-# LANGUAGE TypeFamilies, DataKinds, PolyKinds, StandaloneDeriving #-}

module TySet(plugin, Set, Union) where

import TypeRep
import Type
import Kind
import TcEvidence 
import CoAxiom   
import Name      
import OccName   
import Var       
import TyCon     
import BasicTypes

-- friends:
import Var
import VarEnv
import VarSet
import Name
import BasicTypes
import TyCon
import Class
import CoAxiom

-- others
import PrelNames
import Outputable
import FastString
import Util
import DynFlags

import TcPluginM ( TcPluginM, tcPluginIO, tcPluginTrace )
import TcRnMonad ( TcPlugin(..), TcPluginResult(..)
                 , Ct(..), CtEvidence(..), CtLoc, ctLoc, ctPred
                 , mkNonCanonical, isTouchableTcM, unsafeTcPluginTcM)
import Plugins    ( CommandLineOption, defaultPlugin, Plugin(..) )

import Debug.Trace
import Outputable
import DynFlags

import Control.Monad
import qualified Data.Typeable as DT

{- Set constructor -}
data Set (a :: [k])
{- Union operation -}
type family Union (a :: [k]) (b :: [k]) :: [k]

{- Plugin setup -}
plugin :: Plugin
plugin = defaultPlugin { tcPlugin = Just . thePlugin }

thePlugin :: [CommandLineOption] -> TcPlugin
thePlugin opts = TcPlugin
  { tcPluginInit  = pluginInit opts
  , tcPluginSolve = pluginSolve
  , tcPluginStop  = pluginStop
  }

pluginInit :: [CommandLineOption] -> TcPluginM ()
pluginInit _ = return ()

pluginSolve :: () -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
pluginSolve () given derived wanted = 
    do -- For debugging, show the constraints
       tcPluginTrace "SET" $ ppCts wanted
       tcPluginTrace "SET" $ ppr $ head $ wanted
       solved <- findSetEquality wanted
       -- For the sake of debugging
       tcPluginIO $ putStrLn "Running Set equality plugin"
       return $ TcPluginOk solved []
       
-- Possible eqations for the solver
-- Union a b ~ a  =>  b ~ '[]
-- Union a b ~ b  =>  a ~ '[]

-- Union (Union a b) c ~ d  => Union a (Union b c) ~ d
-- Union '[] a ~ b  => a ~ b
-- Union a '[] ~ b  => a ~ b
-- Union a a   ~ b  => a ~ b   (can do in a reduce phases that looks through a tree of union terms..)

-- Reqires an `ordering'
-- Union a b   ~ c  => Union b a ~ c  [for the purpose of normalisation]

-- Pretty print constraints
ppCts [] = text "(empty)"
ppCts cs = vcat (map ppr cs)

{- Some debugging Show instances to help me understand what is coming in and out of GHC -}
deriving instance Show TyLit
deriving instance Show Type
instance Show Var where
    show v = showSDocUnsafe $ ppr v
instance Show TyCon where
    show tycon = showSDocUnsafe $ ppr tycon

-- Prediacate one whether a type is = Set '[]
isEmptySetType t = do (x, tcs) <- splitTyConApp_maybe t
                      guard $ length tcs == 2
                      guard $ getOccString (tyConName x) == "Set"
                      case tcs of [TyVarTy k, TyConApp con [TyVarTy k']] -> 
                                        do guard $ k == k' 
                                           guard $ (getOccString . tyConName $ con) == "[]"
                                  _ -> Nothing

{- Experimenting, finds Set '[] ~ Set '[] and returns a refl coercion 
   This was set up before when 'Set' was a type family, but is now redundant
-}
findSetEquality :: [Ct] -> TcPluginM [(EvTerm, Ct)]
findSetEquality [] = return []
findSetEquality (ct : xs) = let x = (do (Nominal,t1,t2) <- getEqPredTys_maybe (ctPred ct)
                                        isEmptySetType t1
                                        isEmptySetType t2
                                        return ((EvCoercion $ TcRefl Nominal t1, ct), t1))
                            in
                               case x of 
                                 Just (ct, tcsA) -> do xs' <- (findSetEquality xs)
                                                       tcPluginTrace "SET" $ ppr $ tcsA
                                                       tcPluginTrace "SET" $ text $ show tcsA
                                                       return $ ct : xs'
                                 Nothing -> findSetEquality xs

pluginStop :: () -> TcPluginM ()
pluginStop _ = return ()
