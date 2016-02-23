{-# LANGUAGE DataKinds, KindSignatures, GADTs, TypeOperators, TypeFamilies, PolyKinds, EmptyDataDecls, StandaloneDeriving #-}
{-# OPTIONS_GHC -fplugin=TySet #-}

import GHC.TypeLits
import TySet

data Container (a :: *)  where
    Empty :: Container (Set '[])
    Ext   :: Show a => a -> Container (Set s) -> Container (Set (Union '[a] s))

instance Show (Container a) where
     show Empty = "Empty"
     show (Ext x xs) = "Ext " ++ show x ++ " " ++ show xs 

data Natural (a :: Nat) where
    Z :: Natural 0
    S :: Natural n -> Natural (n + 1)

instance Show (Natural a) where
     show Z = "Z"
     show (S n) = "S " ++ (show n)

-- Should be typeable with the plugin

foo :: Container (Set '[Natural 3, Natural 2, Natural 1])
foo = Ext (S $ S Z) (Ext (S Z) (Ext (S $ S $ S Z) Empty))

foo2 :: Container (Set '[Natural 2, Natural 1])
foo2 = Ext (S $ S Z) (Ext (S Z) Empty)

bar :: (Container (Set '[Natural 2, Natural 1])) -> Container (Set '[Natural 1])
bar (Ext (S (S Z)) (Ext (S Z) Empty)) = Ext (S Z) Empty
bar (Ext (S Z) (Ext (S (S Z)) Empty)) = Ext (S Z) Empty

{-
dup :: Container (Set s) -> Container (Set (Union s s))
dup Empty = Empty
dup (Ext x xs) = Ext x (Ext x (dup xs))
-}