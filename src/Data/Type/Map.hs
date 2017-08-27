{- This module provides type-level finite maps.
The implementation is similar to that shown in the paper.
 "Embedding effect systems in Haskell" Orchard, Petricek 2014  -}

{-# LANGUAGE TypeOperators, PolyKinds, DataKinds, KindSignatures,
             TypeFamilies, UndecidableInstances, MultiParamTypeClasses,
             FlexibleInstances, GADTs, FlexibleContexts, ScopedTypeVariables,
             ConstraintKinds #-}

module Data.Type.Map (Mapping(..), Union, Unionable, union, Var(..), Map(..),
                      Combine, Combinable(..), Cmp,
                      Nubable, nub,
                      Lookup, Member, (:\), Split, split,
                      IsMap, AsMap, asMap,
                      Submap, submap) where

import GHC.TypeLits
import Data.Type.Bool
import Data.Type.Equality
import Data.Type.Set (Cmp, Proxy(..), Flag(..), Sort, Filter, (:++))
import Data.Type.Map.Internal (IsMap, AsMap, Var(..), Map(..), Mapping(..),
                               Combine, Nub, Show'(..), Union, (:\), Lookup,
                               Member)

{- Throughout, type variables
   'k' ranges over "keys"
   'v'  ranges over "values"
   'kvp' ranges over "key-value-pairs"
   'm', 'n' range over "maps" -}

{-| At the value level, noramlise the list form to the map form -}
asMap :: (Sortable s, Nubable (Sort s)) => Map s -> Map (AsMap s)
asMap x = nub (quicksort x)

instance Show (Map '[]) where
    show Empty = "{}"

instance (KnownSymbol k, Show v, Show' (Map s)) => Show (Map ((k :-> v) ': s)) where
    show (Ext k v s) = "{" ++ show k ++ " :-> " ++ show v ++ (show' s) ++ "}"

instance Show' (Map '[]) where
    show' Empty = ""
instance (KnownSymbol k, Show v, Show' (Map s)) => Show' (Map ((k :-> v) ': s)) where
    show' (Ext k v s) = ", " ++ show k ++ " :-> " ++ show v ++ (show' s)

instance Eq (Map '[]) where
    Empty == Empty = True

instance (KnownSymbol k, Eq (Var k), Eq v, Eq (Map s)) => Eq (Map ((k :-> v) ': s)) where
    (Ext k v m) == (Ext k' v' m') = k == k' && v == v' && m == m'

{-| Union of two finite maps -}
union :: (Unionable s t) => Map s -> Map t -> Map (Union s t)
union s t = nub (quicksort (append s t))

type Unionable s t = (Nubable (Sort (s :++ t)), Sortable (s :++ t))

append :: Map s -> Map t -> Map (s :++ t)
append Empty x = x
append (Ext k v xs) ys = Ext k v (append xs ys)

type instance Cmp (k :: Symbol) (k' :: Symbol) = CmpSymbol k k'
type instance Cmp (k :-> v) (k' :-> v') = CmpSymbol k k'

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

instance {-# OVERLAPPABLE #-}
     (Nub (e ': f ': s) ~ (e ': Nub (f ': s)),
              Nubable (f ': s)) => Nubable (e ': f ': s) where
    nub (Ext k v (Ext k' v' s)) = Ext k v (nub (Ext k' v' s))

instance {-# OVERLAPS #-}
    (Combinable v v', Nubable ((k :-> Combine v v') ': s)) => Nubable ((k :-> v) ': (k :-> v') ': s) where
    nub (Ext k v (Ext k' v' s)) = nub (Ext k (combine v v') s)


class Conder g where
    cond :: Proxy g -> Map s -> Map t -> Map (If g s t)

instance Conder True where
    cond _ s t = s

instance Conder False where
    cond _ s t = t


{-| Splitting a union of maps, given the maps we want to split it into -}
class Split s t st where
   -- where st ~ Union s t
   split :: Map st -> (Map s, Map t)

instance Split '[] '[] '[] where
   split Empty = (Empty, Empty)

instance {-# OVERLAPPABLE #-} Split s t st => Split (x ': s) (x ': t) (x ': st) where
   split (Ext k v st) = let (s, t) = split st
                        in (Ext k v s, Ext k v t)

instance {-# OVERLAPS #-} Split s t st => Split (x ': s) t (x ': st) where
   split (Ext k v st) = let (s, t) = split st
                        in  (Ext k v s, t)

instance {-# OVERLAPS #-} (Split s t st) => Split s (x ': t) (x ': st) where
   split (Ext k v st) = let (s, t) = split st
                        in  (s, Ext k v t)

{-| Construct a submap 's' from a supermap 't' -}
class Submap s t where
   submap :: Map t -> Map s

instance Submap '[] '[] where
   submap xs = Empty

instance {-# OVERLAPPABLE #-} Submap s t => Submap s (x ': t) where
   submap (Ext _ _ xs) = submap xs

instance {-# OVERLAPS #-} Submap s t => Submap  (x ': s) (x ': t) where
   submap (Ext k v xs) = Ext k v (submap xs)
