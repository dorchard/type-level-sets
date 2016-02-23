{-# LANGUAGE DataKinds, KindSignatures, GADTs, TypeOperators, TypeFamilies, PolyKinds, EmptyDataDecls #-}

{-# OPTIONS_GHC -fplugin=TyMap #-}
import TyMap

import GHC.TypeLits


data Proxy (s :: Map * (Session *)) = Proxy

data Container (a :: *)  where
    Empty :: Container (Set '[])
    Ext   :: a -> Container (Set s) -> Container (Set (Union '[a] s))
    ExtP  :: Proxy a -> Container (Set s) -> Container (Set (Union '[a] s))

data Natural (a :: Nat) where
    Z :: Natural 0
    S :: Natural n -> Natural (n + 1)

-- Should be typeable with the plugin
foo :: Container (Set '[Natural 1, Natural 2, Natural 3])
foo = Ext (S $ S Z) (Ext (S Z) (Ext (S $ S $ S Z) Empty))























infixr 4 :-> 
data Map a b = a :-> b

data X
data Y

mkA :: Proxy (Y :-> A)
mkA = Proxy

mkB :: Proxy (X :-> B)
mkB = Proxy

data Session a = A | B | C a

bar :: Container (Set '[Y :-> A, X :-> B])
bar = ExtP mkB (ExtP mkA Empty)