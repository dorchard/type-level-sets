-- {-# OPTIONS_GHC -package=ghc-7.10.1 #-}
{-# LANGUAGE TypeFamilies, DataKinds, PolyKinds, StandaloneDeriving, TypeOperators, FlexibleInstances, ScopedTypeVariables #-}

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
import Control.Applicative
import qualified Data.Typeable as DT
import Data.List

import Test.QuickCheck
import Test.QuickCheck.Property

{- Set constructor -}
data Set (a :: [k])
{- Union operation -}
type family Union (a :: [k]) (b :: [k]) :: [k]

type family Member (a :: k) (b :: [k]) :: Bool where
            Member x '[]       = False
            Member x (x ': xs) = True
            Member x (y ': xs) = Member x xs           

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

getNameStr = getOccString . tyConName

isUnion :: Type -> Bool
isUnion t = case splitTyConApp_maybe t of
               Just (x, tcs) -> (getOccString . tyConName $ x) == "Union"
               _             -> False
               
-- splitUnion :: Type -> ([Type], [Type])
splitUnion t = do (x, tcs) <- splitTyConApp_maybe t
                  guard $ (getOccString . tyConName $ x) == "Union"
                   
splitList t = do (tcon, args) <- splitTyConApp_maybe t
                 case getNameStr tcon of 
                   ":" -> do guard $ (length args >= 2)
                             (t1 : (t2 : ts)) <- return args 
                             (kind, emptyArgs) <- splitTyConApp_maybe $ t1
                             guard $ emptyArgs == []
                              -- maybe be unnecessary and even restrictive
                             guard $ getNameStr kind == "*"
                             ts' <- splitList $ head ts -- possible bug here
                             return $ (t2 : ts')
                   "[]" -> do guard $ (length args == 1) 
                              [t] <- return args
                              (kind, emptyArgs) <- splitTyConApp_maybe $ t
                              -- maybe be unnecessary and even restrictive
                              guard $ getNameStr kind == "*"
                              guard $ emptyArgs == []
                              return $ []
                   _    -> return $ []

unionSingle t = do (x, tcs) <- splitTyConApp_maybe t
                   guard $ length tcs == 2
                   guard $ getNameStr x == "Set"
                   return ()

{- Experimenting, finds Set '[] ~ Set '[] and returns a refl coercion 
   This was set up before when 'Set' was a type family, but is now redundant
-}
findSetEquality :: [Ct] -> TcPluginM [(EvTerm, Ct)]
findSetEquality [] = return []
findSetEquality (ct : xs) = let x = (do (Nominal,t1,t2) <- getEqPredTys_maybe (ctPred ct)
                                        isEmptySetType t1
                                        isEmptySetType t2
                                        return ((EvCoercion $ TcRefl Nominal t1, ct), t1))
                                y = do (Nominal,t1,t2) <- getEqPredTys_maybe (ctPred ct)
                                       return t1
                            in
                               case x of 
                                 Just (ct, tcsA) -> do xs' <- (findSetEquality xs)
                                                       tcPluginTrace "SET" $ ppr $ tcsA
                                                       tcPluginTrace "SET" $ text $ show tcsA
                                                       return $ ct : xs'
                                 Nothing -> case y of 
                                              Just t -> do tcPluginTrace "SET" $ text $ show t
                                                           return []

                                              Nothing -> findSetEquality xs

pluginStop :: () -> TcPluginM ()
pluginStop _ = return ()

data TermTree a = Union (TermTree a) (TermTree a) | Empty | Var String | Data [a] deriving Show

equal :: Eq a => TermTree a -> TermTree a -> Bool
equal t1 t2 = let (vs1, ds1) = normalisedRep t1
                  (vs2, ds2) = normalisedRep t2
              in (vs1 == vs2) && (all (flip elem $ ds2) ds1) && (all (flip elem $ ds1) ds2)
               where        
                normalisedRep :: Eq a => TermTree a -> ([String], [a])
                normalisedRep t = let (vs, ds) = separate t
                                  in (nub . sort $ vs, nub ds)

separate :: TermTree a -> ([String], [a])
separate Empty = ([], [])
separate (Var s) = ([s], [])
separate (Data xs) = ([], xs)
separate (Union a b) = let (vs1, ds1) = separate a
                           (vs2, ds2) = separate b
                       in (vs1++vs2, ds1++ds2)

{-- Unit testing of normaliser and set equality --}
testSetTermEquality :: IO ()
testSetTermEquality = quickCheck (\((n, m) :: (TermTree Int, TermTree Int)) -> equal n m)

instance Arbitrary (TermTree Int, TermTree Int) where
    arbitrary = sized $ \vars -> 
                  sized $ \datums -> 
                           do v    <- (vector vars)::(Gen [String])
                              dat  <- (vector datums)::(Gen [Int])
                              v'   <- shuffle v
                              dat' <- shuffle dat
                              g1   <- gen v dat
                              g2   <- gen v' dat'

                              -- Soundness check on generated tree
                              let (v0, dat0) = separate g1
                                  (v1, dat1) = separate g2
                                  norm :: (Ord a) => [a] -> [a]
                                  norm = nub . sort

                              if and [(norm v0) == (norm v), (norm v1) == (norm v), 
                                      (norm dat) == (norm dat0), (norm dat) == (norm dat1)]
                                then return ()
                                else error $ "Generated trees failed soundness check: " ++ (show g1) ++ " " ++ (show g2)
                              return (g1, g2)

-- Arbitrarily permute a union of two generators
unionPerm x y = do x' <- x
                   y' <- y
                   elements [Union x' y', Union y' x']

-- Generates arbitrary terms from a list of variables and list of Int adtums
gen :: [String] -> [Int] -> Gen (TermTree Int)
gen []     []   = return $ Empty
gen vs     ds   = do -- Choose between 0 and 1 if 'vs' is empty, or 0-2 if 'vs' has elements
                     choose <- suchThat arbitrary (\x -> x<=(2 - if vs == [] then 1 else 0) && x>=0)
                     case choose::Int of 
                       -- Union with Empty
                       0 -> unionPerm (gen vs ds) (return $ Empty)

                       -- Pick some number of elements (maybe none) and create a data leaf
                       1 -> do i <- suchThat arbitrary (<= (length ds)) 
                               unionPerm (gen vs (drop i ds)) (return $ Data (take i ds))

                       -- Case where vs is non-empty, create a variable node, and either remove that
                       -- variable, or keep it around as a possibility again to test idempotency
                       2 -> oneof [unionPerm (gen (tail vs) ds) (return $ Var (head vs)), 
                                   unionPerm (gen vs ds) (return $ Var (head vs))]
                       _ -> error "unpossible"
                                                     
                                                     
                                           
                                           
                                         
                                         
                                             
                                       