{- This module provides type-level finite maps.
The implementation is similar to that shown in the paper.
 "Embedding effect systems in Haskell" Orchard, Petricek 2014  -}

{-# LANGUAGE TypeOperators, PolyKinds, DataKinds, KindSignatures,
             TypeFamilies, UndecidableInstances, MultiParamTypeClasses,
             FlexibleInstances, GADTs, FlexibleContexts, ScopedTypeVariables,
             ConstraintKinds, FunctionalDependencies #-}

module Data.Type.Map (Mapping(..), Union, Unionable, union, append, Var(..), Map(..),
                        ext, empty, mapLength,
                        Combine, Combinable(..), Cmp,
                        Nubable, nub,
                        Lookup, Member, (:\), Split, split,
                        IsMember, lookp, Updatable, update,
                        IsMap, AsMap, asMap,
                        Sortable, quicksort,
                        Submap, submap) where

import GHC.TypeLits
import Data.Type.Bool
import Data.Type.Equality
import Data.Type.Set (Cmp, Proxy(..), Flag(..), Sort, Filter, Filter', (:++))
import Data.Kind (Type)
import Rearrange.Rearrangeable
import Rearrange.Typeclass

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
     '[]              :\ k = '[]
     ((k :-> v) ': m) :\ k = m :\ k
     (kvp ': m)       :\ k = kvp ': (m :\ k)

{-| Type-level lookup of elements from a map -}
type family Lookup (m :: [Mapping k v]) (c :: k) :: Maybe v where
            Lookup '[]              k = Nothing
            Lookup ((k :-> v) ': m) k = Just v
            Lookup (kvp ': m)       k = Lookup m k

{-| Membership test as type function -}
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
data Map (n :: [Mapping Symbol Type]) where
    Empty :: Map '[]
    Ext :: Var k -> v -> Map m -> Map ((k :-> v) ': m)

instance Rearrangeable Map where
    rConsToHead (Ext x v _) = Ext x v
    rTail (Ext _ _ xs) = xs
    rEmpty = Empty

{-| Smart constructor which normalises the representation -}
ext :: (Sortable ((k :-> v) ': m), Nubable (Sort ((k :-> v) ': m))) => Var k -> v -> Map m -> Map (AsMap ((k :-> v) ': m))
ext k v m = asMap $ Ext k v m

{-| Smart constructor to match `ext` (but doesn't do anything other than wrap Empty) -}
empty :: Map '[]
empty = Empty

{-| Length function -}
mapLength :: Map n -> Int
mapLength Empty = 0
mapLength (Ext _ _ xs) = 1 + mapLength xs

{-| Membership test a type class (predicate) -}
class IsMember v t m | m v -> t where
  {-| Value-level lookup of elements from a map, via type class predicate -}
  lookp :: Var v -> Map m -> t

instance {-# OVERLAPS #-} IsMember v t ((v ':-> t) ': m) where
  lookp _ (Ext _ x _) = x

instance {-# OVERLAPPABLE #-} IsMember v t m => IsMember v t (x ': m) where
  lookp v (Ext _ _ m) = lookp v m


{-| Updatability as a type class -}
class Updatable v t m n where
  {-| Update a map with `m` at variable `v` with a value of type `t`
      to produce a map of type `n` -}
  update :: Map m -> Var v -> t -> Map n

instance {-# OVERLAPS #-} Updatable v t ((v ':-> s) ': m) ((v ':-> t) ': m) where
  update (Ext v _ m) _ x = Ext v x m

instance Updatable v t m n => Updatable v t ((w ':-> y) ': m) ((w ':-> y) ': n) where
  update (Ext w y m) v x = Ext w y (update m v x)

-- instance Updatable v t '[] '[v ':-> t] where
--   update Empty v x = Ext v x Empty

instance Updatable v t s ((v ':-> t) ': s) where
  update xs v x = Ext v x xs


{-| Predicate to check if in normalised map form -}
type IsMap s = (s ~ Nub (Sort s))

{-| At the type level, normalise the list form to the map form -}
type AsMap s = Nub (Sort s)

{-| At the value level, normalise the list form to the map form.
    Note: in theory, this could be replaced with a call to rDel
          mapping from a Map s to a Map (AsMap s).
          However, nub must be used due to note [NubOrdering]
          (in `Data.Type.Set`). -}
asMap :: (Sortable s, Nubable (Sort s)) => Map s -> Map (AsMap s)
asMap x = nub (quicksort x)

instance Show (Map '[]) where
    show Empty = "{}"

instance (KnownSymbol k, Show v, Show' (Map s)) => Show (Map ((k :-> v) ': s)) where
    show (Ext k v s) = "{" ++ show k ++ " :-> " ++ show v ++ show' s ++ "}"

class Show' t where
    show' :: t -> String
instance Show' (Map '[]) where
    show' Empty = ""
instance (KnownSymbol k, Show v, Show' (Map s)) => Show' (Map ((k :-> v) ': s)) where
    show' (Ext k v s) = ", " ++ show k ++ " :-> " ++ show v ++ (show' s)

instance Eq (Map '[]) where
    Empty == Empty = True

instance (Eq v, Eq (Map s)) => Eq (Map ((k :-> v) ': s)) where
    (Ext Var v m) == (Ext Var v' m') = v == v' && m == m'

instance Ord (Map '[]) where
    compare Empty Empty = EQ

instance (Ord v, Ord (Map s)) => Ord (Map ((k :-> v) ': s)) where
    compare (Ext Var v m) (Ext Var v' m') = compare v v' `mappend` compare m m'

{-| Union of two finite maps (normalising) -}
union :: (Unionable s t) => Map s -> Map t -> Map (Union s t)
union s t = nub (quicksort (append s t))

type Unionable s t = (Nubable (Sort (s :++ t)), Sortable (s :++ t))

{-| Append of two finite maps (non normalising) -}
append :: Map s -> Map t -> Map (s :++ t)
append Empty x = x
append (Ext k v xs) ys = Ext k v (append xs ys)

type instance Cmp (k :: Symbol) (k' :: Symbol) = CmpSymbol k k'
type instance Cmp (k :-> v) (k' :-> v') = CmpSymbol k k'

{-| Value-level quick sort that respects the type-level ordering -}
type Sortable xs = Permute Map xs (Sort xs)

quicksort :: Sortable xs => Map xs -> Map (Sort xs)
quicksort = permute

class Combinable t t' where
    combine :: t -> t' -> Combine t t'

{-| Value-level counterpart to the type-level 'Nub'
    See the notes on `nub` in `Data.Type.Set`. -}
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
       (Combinable v v', Nubable ((k :-> Combine v v') ': s))
    => Nubable ((k :-> v) ': (k :-> v') ': s) where
    nub (Ext k v (Ext k' v' s)) = nub (Ext k (combine v v') s)

{-| Splitting a union of maps, given the maps we want to split it into -}
type Split s t st = (RDel Map st s, RDel Map st t)

split :: (Split s t st) => Map st -> (Map s, Map t)
split inp = (rDel inp, rDel inp)

{-| Construct a submap 's' from a supermap 't' -}
type Submap s t = RDel Map t s

submap :: (Submap s t) => Map t -> Map s
submap = rDel