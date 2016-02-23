{-# LANGUAGE DataKinds, KindSignatures, GADTs, TypeOperators, TypeFamilies, PolyKinds, EmptyDataDecls #-}
{-# OPTIONS_GHC -fplugin=TySet #-}

import GHC.TypeLits
import TySet

data Container (a :: *)  where
    Empty :: Container (Set '[])
    Ext   :: a -> Container (Set s) -> Container (Set (Union '[a] s))

data Natural (a :: Nat) where
    Z :: Natural 0
    S :: Natural n -> Natural (n + 1)

-- Should be typeable with the plugin
{-
foo :: Container (Set '[Natural 1, Natural 2, Natural 3])
foo = Ext (S $ S Z) (Ext (S Z) (Ext (S $ S $ S Z) Empty))
-}

dup :: Container (Set s) -> Container (Set (Union s s))
dup Empty = Empty
dup (Ext x xs) = Ext x (Ext x (dup xs))