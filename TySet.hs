-- {-# OPTIONS_GHC -package=ghc-7.10.1 #-}
{-# LANGUAGE TypeFamilies, DataKinds, PolyKinds, StandaloneDeriving, TypeOperators, FlexibleInstances, ScopedTypeVariables, ImplicitParams, MultiParamTypeClasses #-}

module TySet(plugin, Set, Union, dropPrefix) where

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
import GHC.TcPluginM.Extra

import Debug.Trace
import Outputable
import DynFlags

import Control.Monad
import Control.Monad.Trans.Maybe
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

class Debug t m where
    debug :: (?ifDebug :: Bool) => t -> m ()
instance Debug SDoc TcPluginM where
    debug x = tcPluginTrace "TySet" x
instance Debug String IO where
    debug x = putStrLn x

pluginInit :: [CommandLineOption] -> TcPluginM ()
pluginInit _ = return ()

pluginSolve :: () -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
pluginSolve () given derived wanted = 
    let ?ifDebug = True in

    do 
       tcPluginIO $ debug "Running TySet equality plugin"
       debug $ ppCts wanted 
       -- debug $ ppr $ head $ wanted

       --solved <- findEmptySetEquality wanted
       (solved, generated) <- findSetEquality wanted
       return $ TcPluginOk solved generated
       
pluginStop :: () -> TcPluginM ()
pluginStop _ = return ()

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
instance Show Ct where
    show ct = showSDocUnsafe $ ppr ct

{-
-- Prediacate one whether a type is = Set '[]
isEmptySetType t = do (x, tcs) <- splitTyConApp_maybe t
                      guard $ length tcs == 2
                      guard $ getOccString (tyConName x) == "Set"
                      case tcs of [TyVarTy k, TyConApp con [TyVarTy k']] -> 
                                        do guard $ k == k' 
                                           guard $ (getOccString . tyConName $ con) == "[]"
                                  _ -> Nothing
-}

getNameStr = getOccString . tyConName

liftTc :: Maybe a -> MaybeT TcPluginM a
liftTc = MaybeT . return

liftMt :: TcPluginM a -> MaybeT TcPluginM a
liftMt x = MaybeT (fmap Just x)

findSetEquality :: [Ct] -> TcPluginM ([(EvTerm, Ct)], [Ct])
findSetEquality [] = return ([], [])
findSetEquality (ct : xs) = 
    do x <- runMaybeT $ 
        do (Nominal, t1, t2) <- liftTc $ getEqPredTys_maybe (ctPred ct)
           a <- liftTc $ listTypeToTerm t1
           b <- "sofar sogood" `trace` liftTc $ listTypeToTerm t2
           (show (t1, a, t2, b)) `trace` 
                if (a == b) then
                    "are equal" `trace` return $ Left (EvCoercion $ TcRefl Nominal t1, ct)
                else -- not equal, try to find an mgu and generate conditions on that
                    let ?ctLoc = ctLoc ct in
                    do unifiers <- "not equal" `trace` mgu a b 
                       case unifiers of
                         Left unifiers -> ("L unifiers: \n" ++ show unifiers) `trace` return $ Right []
                         Right (dataUnifiers, unsolvedExtra) -> ("data unifiers:" ++ (show $ dataUnifiers)) `trace` return $ Right $ (EvCoercion $ TcRefl Nominal t1, ct) : map (\c -> (EvCoercion $ TcRefl Nominal undefined, c)) dataUnifiers
                                            
       (solved, generated) <- findSetEquality xs
       case x of 
         Just y -> case y of
             Left (ev, ct) -> return $ ((ev, ct) : solved, generated)
             Right cts     -> return $ (solved ++ cts, generated)
         Nothing -> return (solved, generated)

listTypeToTerm :: Type -> Maybe (TermTree Type)
listTypeToTerm t = case (splitTyConApp_maybe t) of 
             Just (tcon, args) -> 
                 case getNameStr tcon of 
                   "Union" -> do guard $ (length args) >= 3
                                 (_ : (t1 : (t2 : ts))) <- return args
                                 t1' <- listTypeToTerm t1
                                 t2' <- listTypeToTerm t2
                                 return $ Union t1' t2'
                   -- this case is probably temporary [see SessionListE.hs]
                   ":++" -> do guard $ (length args) >= 3
                               (_ : (t1 : (t2 : ts))) <- return args
                               t1' <- listTypeToTerm t1
                               t2' <- listTypeToTerm t2
                               return $ Union t1' t2'
                   ":" -> do guard $ (length args >= 2)
                             (t1 : (t2 : ts)) <- return args 
                             (kind, args) <- splitTyConApp_maybe $ t1
                             ts' <- listTypeToTerm $ head ts -- possible bug here
                             return $ Union (Data [t2]) ts'
                   "[]" -> do guard $ (length args == 1) 
                              [t] <- return args
                              (kind, args) <- splitTyConApp_maybe $ t
                              return $ Empty

                   _    -> return $ Empty -- Data [t]
             _ -> case t of
                    TyVarTy v -> return $ Var $ v

-- Representation for solving equalities on terms comprising union, data, and variables

data TermTree a = Union (TermTree a) (TermTree a) | Empty | Var Var | Data [a] deriving Show

-- if the second argument is a prefix of the first argument, then return Just of the suffix, else Nothing
dropPrefix :: Eq a => [a] -> [a] -> Maybe [a]
dropPrefix [] xs = Just []
dropPrefix xs [] = Just xs
dropPrefix (x:xs) (y:ys) | x == y = dropPrefix xs ys
                         | otherwise = Nothing

mguDataVars :: [a] -> [Var] -> Maybe [(Var, TermTree a)]
mguDataVars suffix [] = Nothing -- No variables to unify with
mguDataVars suffix (v:vs) = Just $ [(v, Data suffix)] ++ map (\v' -> (v', Var v)) vs

mgu :: (?ctLoc :: CtLoc) => TermTree Type -> TermTree Type -> MaybeT TcPluginM (Either [(Var, TermTree Type)] ([Ct], ([Type], [Type]))) -- last component should be some equalities
mgu t1 t2 = let (vs1, ds1) = normalisedRep t1
                (vs2, ds2) = normalisedRep t2
            in ("----> " ++ show (ds1, ds2)) `trace`
               (show $ dropPrefix ds1 ds2) `trace`
               case (dropPrefix ds1 ds2) of 
                 Nothing -> case (dropPrefix ds2 ds1) of
                              Nothing -> "el zilcho primo" `trace` do x <- liftMt (zipMatch ds1 ds2)
                                                                      return $ Right x -- ([], ([], []))
                              Just suffix_ds2 -> "suffix_ds2" `trace`
                                                  do x <- liftTc $ mguDataVars suffix_ds2 vs1
                                                     return $ Left x
                 Just suffix_ds1 -> ("suffix_ds1 " ++ (show suffix_ds1))
                                     `trace`
                                      if (suffix_ds1 == []) then
                                         do x <- liftMt (zipMatch ds1 ds2)
                                            ("zipm: ds1 = " ++ (show ds1) ++ " ds2 = " ++ (show ds2) ++ ": " ++ (show x)) `trace` return $ Right x -- ([], ([], []))
                                      else
                                          do x <- liftTc $ mguDataVars suffix_ds1 vs2
                                             return $ Left x

mkEqualities :: (?ctLoc :: CtLoc) => [(Type, Type)] -> TcPluginM [Ct]
mkEqualities xs = (mapM (\(x, y) -> mkCt x y) xs) -- >>= (return . concat)

mkCt t t' = fmap mkNonCanonical (newDerived ?ctLoc (uncurry mkPrimEqPred (t,t')))

mkEqualities' (AppTy t1 t2) (AppTy t1' t2') = do ct <- mkCt t1 t1' 
                                                 ct' <- mkCt t2 t2'
                                                 return [ct, ct']
mkEqualities' (TyConApp con kt) (TyConApp con' kt') | con == con' = mapM (uncurry mkCt) (zip kt kt')
mkEqualities' (FunTy t1 t2) (FunTy t1' t2') = do ct <- mkCt t1 t1'
                                                 ct' <- mkCt t2 t2'
                                                 return [ct, ct']
mkEqualities' (ForAllTy v t) (ForAllTy v' t') | v == v' = do ct <- mkCt t t'
                                                             return [ct]
mkEqualities' t t' = do ct <- mkCt t t'
                        return [ct]




zipMatch :: (?ctLoc :: CtLoc) => [Type] -> [Type] -> TcPluginM ([Ct], ([Type], [Type]))
zipMatch xs ys = let (unifiers, restL, restR) = zipMatch' xs ys
                 in do unifiers' <- mkEqualities unifiers
                       return $ (unifiers', (restL, restR))

zipMatch' :: [a] -> [a] -> ([(a, a)], [a], [a])
zipMatch' [] xs = ([], [], xs)
zipMatch' xs [] = ([], xs, [])
zipMatch' (x:xs) (y:ys) = let (zips, l, r) = zipMatch' xs ys
                          in ((x, y) : zips, l, r)
                                        
                             




subst :: TermTree a -> [(Var, TermTree a)] -> TermTree a
subst (Union s t) theta = Union (subst s theta) (subst t theta)
subst (Var a)     theta = case (lookup a theta) of
                            Just t -> t
                            Nothing -> Var a
subst t           theta = t

instance Eq a => Eq (TermTree a) where
    t1 == t2 = let (vs1, ds1) = normalisedRep t1
                   (vs2, ds2) = normalisedRep t2
               in ("vars = " ++ (show (vs1, vs2)) ++ " eq = " ++ (show (vs1 == vs2))) 
                      `trace` (vs1 == vs2) && (all (flip elem $ ds2) ds1) && (all (flip elem $ ds1) ds2)

normalisedRep :: Eq a => TermTree a -> ([Var], [a])
normalisedRep t = let (vs, ds) = separate t
                  in (nub . sort $ vs, nub ds)

separate :: TermTree a -> ([Var], [a])
separate Empty = ([], [])
separate (Var s) = ([s], [])
separate (Data xs) = ([], xs)
separate (Union a b) = let (vs1, ds1) = separate a
                           (vs2, ds2) = separate b
                       in (vs1++vs2, ds1++ds2)

{-- Unit testing of normaliser and set equality --}
testSetTermEquality :: IO ()
testSetTermEquality = quickCheck (\((n, m) :: (TermTree Int, TermTree Int)) -> n == m)

mkVar :: String -> Var
mkVar = undefined

instance Arbitrary (TermTree Int, TermTree Int) where
    arbitrary = sized $ \vars -> 
                  sized $ \datums -> 
                           do v0    <- (vector vars)::(Gen [String])
                              v    <- return $ map mkVar v0
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
gen :: [Var] -> [Int] -> Gen (TermTree Int)
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
                                                     
                                                     
                                           
                                           
                                         
                                         
                                             
                                       