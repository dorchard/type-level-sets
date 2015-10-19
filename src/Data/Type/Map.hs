{- This module provides type-level finite maps.
The implementation is similar to that shown in the paper.
 "Embedding effect systems in Haskell" Orchard, Petricek 2014  -}

{-# LANGUAGE TypeOperators, PolyKinds, DataKinds, KindSignatures, 
             TypeFamilies, UndecidableInstances, MultiParamTypeClasses, 
             FlexibleInstances, GADTs, FlexibleContexts, ScopedTypeVariables, ConstraintKinds #-}

module Data.Type.Map (Mapping(..), Union, Unionable, union, Var(..), Map(..), 
                      Combine, Combinable(..), Cmp, 
                      Lookup, Member, (:\)) where

import GHC.TypeLits
import Data.Type.Bool
import Data.Type.Equality
import Data.Type.Set hiding (Set(..), Nub,Union,Nubable,Sortable,Unionable,append,union,quicksort,nub)

{- Throughout, type variables
   'k' ranges over "keys"
   'v'  ranges over "values"
   'kvp' ranges over "key-value-pairs"
   'm', 'n' range over "maps" -}

-- Mappings
infixr 4 :-> 
{-| A key-value pair -}
data Mapping k v = k :-> v

{-| Union of two finite maps -}
type Union m n = Nub (Sort (m :++ n))

{-| Apply 'Combine' to values with matching key (removes duplicate keys) -}
type family Nub t where
   Nub '[]                             = '[]
   Nub '[kvp]                          = '[kvp]
   Nub ((k :-> v1) ': (k :-> v2) ': m) = Nub ((k :-> Combine v1 v2) ': m)
   Nub (kvp1 ': kvp2 ': s)             = kvp1 ': Nub (kvp2 ': s)

{-| Open type family for combining values in a map (that have the same key) -}
type family Combine (a :: v) (b :: v) :: v

{-| Delete elements from a map by key -}
type family (m :: [Mapping k v]) :\ (c :: k) :: [Mapping k v] where
     '[]               :\ k = '[]
     ((k :-> v) ': m)  :\ k = m :\ k
     (kvp ': m)        :\ k = kvp ': (m :\ k)

{-| Lookup elements from a map -}
type family Lookup (m :: [Mapping k v]) (c :: k) :: Maybe v where
            Lookup '[]              k = Nothing
            Lookup ((k :-> v) ': m) k = Just v
            Lookup (kvp ': m)       k = Lookup m k

{-| Membership test -}
type family Member (c :: k) (m :: [Mapping k v]) :: Bool where
            Member k '[]              = False
            Member k ((k :-> v) ': m) = True
            Member k (kvp ': m)       = Member k m

-----------------------------------------------------------------
-- Value-level map with a type-level representation

{-| Pair a symbol (representing a variable) with a type -}
data Var (k :: Symbol) = Var 

instance KnownSymbol k => Show (Var k) where
    show = symbolVal

{-| A value-level heterogenously-typed Map (with type-level representation in terms of lists) -}
data Map (n :: [Mapping Symbol *]) where
    Empty :: Map '[]
    Ext :: Var k -> v -> Map m -> Map ((k :-> v) ': m)

instance Show (Map '[]) where
    show Empty = "{}"

instance (KnownSymbol k, Show v, Show' (Map s)) => Show (Map ((k :-> v) ': s)) where
    show (Ext k v s) = "{" ++ show k ++ " :-> " ++ show v ++ (show' s) ++ "}" 

class Show' t where
    show' :: t -> String
instance Show' (Map '[]) where
    show' Empty = ""
instance (KnownSymbol k, Show v, Show' (Map s)) => Show' (Map ((k :-> v) ': s)) where
    show' (Ext k v s) = ", " ++ show k ++ " :-> " ++ show v ++ (show' s)

{-| Union of two finite maps -}
union :: (Unionable s t) => Map s -> Map t -> Map (Union s t)
union s t = nub (quicksort (append s t))

type Unionable s t = (Nubable (Sort (s :++ t)), Sortable (s :++ t))

append :: Map s -> Map t -> Map (s :++ t)
append Empty x = x
append (Ext k v xs) ys = Ext k v (append xs ys)

type instance Cmp (k :: Symbol) (k' :: Symbol) = CmpSymbol k k'
type instance Cmp (k :-> v) (k' :-> v) = CmpSymbol k k'

{-| Value-level quick sort that respects the type-level ordering -}
class Sortable xs where
    quicksort :: Map xs -> Map (Sort xs)

instance Sortable '[] where
    quicksort Empty = Empty

instance (Sortable (Filter FMin (k :-> v) xs),
          Sortable (Filter FMax (k :-> v) xs), FilterV FMin k v xs, FilterV FMax k v xs) => Sortable ((k :-> v) ': xs) where
    quicksort (Ext k v xs) = ((quicksort (less k v xs)) `append` (Ext k v Empty)) `append` (quicksort (more k v xs))
                              where less = filterV (Proxy::(Proxy FMin))
                                    more = filterV (Proxy::(Proxy FMax))

{- Filter out the elements less-than or greater-than-or-equal to the pivot -}
class FilterV (f::Flag) k v xs where
    filterV :: Proxy f -> Var k -> v -> Map xs -> Map (Filter f (k :-> v) xs)

instance FilterV f k v '[] where
    filterV _ k v Empty      = Empty

instance (Conder ((Cmp x (k :-> v)) == LT), FilterV FMin k v xs) => FilterV FMin k v (x ': xs) where
    filterV f@Proxy k v (Ext k' v' xs) = cond (Proxy::(Proxy ((Cmp x (k :-> v)) == LT)))
                                        (Ext k' v' (filterV f k v xs)) (filterV f k v xs) 

instance (Conder (((Cmp x (k :-> v)) == GT) || ((Cmp x (k :-> v)) == EQ)), FilterV FMax k v xs) => FilterV FMax k v (x ': xs) where
    filterV f@Proxy k v (Ext k' v' xs) = cond (Proxy::(Proxy (((Cmp x (k :-> v)) == GT) || ((Cmp x (k :-> v)) == EQ))))
                                        (Ext k' v' (filterV f k v xs)) (filterV f k v xs)  

class Combinable t t' where
    combine :: t -> t' -> Combine t t'

class Nubable t where
    nub :: Map t -> Map (Nub t)

instance Nubable '[] where
    nub Empty = Empty

instance Nubable '[e] where
    nub (Ext k v Empty) = Ext k v Empty

instance {-# OVERLAPPING #-}
    (Combinable v v', Nubable ((k :-> Combine v v') ': s)) => Nubable ((k :-> v) ': (k :-> v') ': s) where
    nub (Ext k v (Ext k' v' s)) = nub (Ext k (combine v v') s)

instance {-# OVERLAPPING #-}
     (Nub (e ': f ': s) ~ (e ': Nub (f ': s)), 
              Nubable (f ': s)) => Nubable (e ': f ': s) where
    nub (Ext k v (Ext k' v' s)) = Ext k v (nub (Ext k' v' s))

class Conder g where
    cond :: Proxy g -> Map s -> Map t -> Map (If g s t)

instance Conder True where
    cond _ s t = s

instance Conder False where
    cond _ s t = t

