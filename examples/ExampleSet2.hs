{-# LANGUAGE DataKinds, TypeOperators, TypeFamilies, GADTs, StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}

module ExampleSet2 where

import GHC.TypeLits ( Nat, CmpNat, type (+) )
import Data.Type.Set

type instance Cmp (Natural n) (Natural m) = CmpNat n m
type instance Cmp String String      = 'EQ
type instance Cmp String (Natural _) = 'LT
type instance Cmp (Natural _) String = 'GT

data Natural (a :: Nat) where
    Z :: Natural 0
    S :: Natural n -> Natural (n + 1)

deriving instance Show (Natural n)

instance Eq (Natural n) where
    _ == _ = True

foo :: Set '[String, Natural 1]
foo = asSet $ Ext "str1" $ Ext (S Z) Empty

bar :: Set '[String]
bar = asSet $ Ext "str2" Empty

foobar :: Set '[String, Natural 1]
foobar = foo `union` bar

barfoo :: Set '[String, Natural 1]
barfoo = bar `union` foo

fooStr :: String
fooStr = project Proxy foo

foobarStr :: String
foobarStr = project Proxy foobar

barfooStr :: String
barfooStr = project Proxy barfoo

fooHasNat1 :: Bool
fooHasNat1 = member (Proxy :: Proxy (Natural 1)) foo

barHasNat1 :: Bool
barHasNat1 = member (Proxy :: Proxy (Natural 1)) bar

r0_9 :: Set '[Natural 0, Natural 1, Natural 2, Natural 3, Natural 4, Natural 5, Natural 6, Natural 7, Natural 8, Natural 9]
r0_9 =
  Ext Z $
  Ext (S Z) $
  Ext (S (S Z)) $
  Ext (S (S (S Z))) $
  Ext (S (S (S (S Z)))) $
  Ext (S (S (S (S (S Z))))) $
  Ext (S (S (S (S (S (S Z)))))) $
  Ext (S (S (S (S (S (S (S Z))))))) $
  Ext (S (S (S (S (S (S (S (S Z)))))))) $
  Ext (S (S (S (S (S (S (S (S (S Z))))))))) Empty

r10_19 :: Set '[Natural 10, Natural 11, Natural 12, Natural 13, Natural 14, Natural 15, Natural 16, Natural 17, Natural 18, Natural 19]
r10_19 =
  Ext ((S . S . S . S . S . S . S . S . S . S) Z) $
  Ext ((S . S . S . S . S . S . S . S . S . S . S) Z) $
  Ext ((S . S . S . S . S . S . S . S . S . S . S . S) Z) $
  Ext ((S . S . S . S . S . S . S . S . S . S . S . S . S) Z) $
  Ext ((S . S . S . S . S . S . S . S . S . S . S . S . S . S) Z) $
  Ext ((S . S . S . S . S . S . S . S . S . S . S . S . S . S . S) Z) $
  Ext ((S . S . S . S . S . S . S . S . S . S . S . S . S . S . S . S) Z) $
  Ext ((S . S . S . S . S . S . S . S . S . S . S . S . S . S . S . S . S) Z) $
  Ext ((S . S . S . S . S . S . S . S . S . S . S . S . S . S . S . S . S . S) Z) $
  Ext ((S . S . S . S . S . S . S . S . S . S . S . S . S . S . S . S . S . S . S) Z) Empty
