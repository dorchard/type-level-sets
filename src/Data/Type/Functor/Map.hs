{- This module provides type-level finite maps.
The implementation is similar to that shown in the paper.
 "Embedding effect systems in Haskell" Orchard, Petricek 2014  -}

{-# LANGUAGE TypeOperators, PolyKinds, DataKinds, KindSignatures,
             TypeFamilies, UndecidableInstances, MultiParamTypeClasses,
             FlexibleInstances, GADTs, FlexibleContexts, ScopedTypeVariables,
             ConstraintKinds, RankNTypes #-}

module Data.Type.Functor.Map
  (Mapping(..), Union, Unionable, union, Var(..), Map(..), fromSimple, toSimple,
   traverseValues, mapValues, Combine, Combinable(..), Cmp, Nubable, nub,
   Lookup, Member, (:\), Split, split, IsMap, AsMap, asMap, Submap, submap)
   where

import GHC.TypeLits
import Data.Functor.Identity (Identity(..))

import Data.Type.Bool
import Data.Type.Equality
import Data.Type.Set (Cmp, Proxy(..), Flag(..), Sort, Filter, (:++))

import Data.Type.Map.Internal (IsMap, AsMap, Mapping(..), Combine, Nub,
                               Show'(..), Var(..), Union, (:\), Lookup, Member)
import qualified Data.Type.Map.Internal as Simple

-- import qualified Data.Type.M

{- Throughout, type variables
   'k' ranges over "keys"
   'v'  ranges over "values"
   'kvp' ranges over "key-value-pairs"
   'm', 'n' range over "maps" -}

-----------------------------------------------------------------
-- Value-level map with a type-level representation

{-|
A value-level heterogenously-typed Map (with type-level representation in terms
of lists).

The map is parameterised by a functor @f@ from the universe @u@ to concrete
types. For example, use 'Identity' for a normal heterogeneous map, or
'Data.Functor.Const.Const a' for a homogeneous map with values of type @a@.
-}
data Map (f :: u -> *) (n :: [Mapping Symbol u]) where
    Empty :: Map f '[]
    Ext :: Var k -> f v -> Map f m -> Map f ((k :-> v) ': m)

{-| At the value level, noramlise the list form to the map form -}
asMap :: (Sortable s, Nubable f (Sort s)) => Map f s -> Map f (AsMap s)
asMap x = nub (quicksort x)

-- | Convert from a simple 'Simple.Map' to a 'Map' in 'Identity'.
fromSimple :: Simple.Map m -> Map Identity m
fromSimple Simple.Empty = Empty
fromSimple (Simple.Ext k v s) = Ext k (Identity v) (fromSimple s)

-- | Convert from a 'Map' in 'Identity' to a simple 'Simple.Map'.
toSimple :: Map Identity m -> Simple.Map m
toSimple Empty = Simple.Empty
toSimple (Ext k (Identity v) s) = Simple.Ext k v (toSimple s)

-- | Analogous to 'traverse', but the given function is a natural transformation
-- from @f@ to @t . g@.
traverseValues
  :: (Applicative t)
  => (forall a. f a -> t (g a)) -> Map f m -> t (Map g m)
traverseValues f Empty = pure Empty
traverseValues f (Ext k v s) =
  Ext k <$> f v <*> traverseValues f s

-- | Analogous to 'fmap', but the given function is a natural transformation
-- from @f@ to @g@.
mapValues :: (forall a. f a -> g a) -> Map f m -> Map g m
mapValues f = runIdentity . traverseValues (Identity . f)

instance Show (Map f '[]) where
    show Empty = "{}"

instance (KnownSymbol k, Show (f v), Show' (Map f s)) => Show (Map f ((k :-> v) ': s)) where
    show (Ext k v s) = "{" ++ show k ++ " :-> " ++ show v ++ (show' s) ++ "}"

instance Show' (Map f '[]) where
    show' Empty = ""
instance (KnownSymbol k, Show (f v), Show' (Map f s)) => Show' (Map f ((k :-> v) ': s)) where
    show' (Ext k v s) = ", " ++ show k ++ " :-> " ++ show v ++ (show' s)

instance Eq (Map f '[]) where
    Empty == Empty = True

instance (KnownSymbol k, Eq (Var k), Eq (f v), Eq (Map f s)) => Eq (Map f ((k :-> v) ': s)) where
    (Ext k v m) == (Ext k' v' m') = k == k' && v == v' && m == m'

{-| Union of two finite maps -}
union :: (Unionable f s t) => Map f s -> Map f t -> Map f (Union s t)
union s t = nub (quicksort (append s t))

type Unionable f s t = (Nubable f (Sort (s :++ t)), Sortable (s :++ t))

append :: Map f s -> Map f t -> Map f (s :++ t)
append Empty x = x
append (Ext k v xs) ys = Ext k v (append xs ys)

{-| Value-level quick sort that respects the type-level ordering -}
class Sortable xs where
    quicksort :: Map f xs -> Map f (Sort xs)

instance Sortable '[] where
    quicksort Empty = Empty

instance (Sortable (Filter FMin (k :-> v) xs),
          Sortable (Filter FMax (k :-> v) xs), FilterV FMin k v xs, FilterV FMax k v xs) => Sortable ((k :-> v) ': xs) where
    quicksort (Ext k v xs) = ((quicksort (less k v xs)) `append` (Ext k v Empty)) `append` (quicksort (more k v xs))
                              where less = filterV (Proxy::(Proxy FMin))
                                    more = filterV (Proxy::(Proxy FMax))

{- Filter out the elements less-than or greater-than-or-equal to the pivot -}
class FilterV (f::Flag) k v xs where
    filterV :: Proxy f -> Var k -> g v -> Map g xs -> Map g (Filter f (k :-> v) xs)

instance FilterV f k v '[] where
    filterV _ k v Empty      = Empty

instance (Conder ((Cmp x (k :-> v)) == LT), FilterV FMin k v xs) => FilterV FMin k v (x ': xs) where
    filterV f@Proxy k v (Ext k' v' xs) = cond (Proxy::(Proxy ((Cmp x (k :-> v)) == LT)))
                                        (Ext k' v' (filterV f k v xs)) (filterV f k v xs)

instance (Conder (((Cmp x (k :-> v)) == GT) || ((Cmp x (k :-> v)) == EQ)), FilterV FMax k v xs) => FilterV FMax k v (x ': xs) where
    filterV f@Proxy k v (Ext k' v' xs) = cond (Proxy::(Proxy (((Cmp x (k :-> v)) == GT) || ((Cmp x (k :-> v)) == EQ))))
                                        (Ext k' v' (filterV f k v xs)) (filterV f k v xs)

class Combinable f t t' where
  combine :: f t -> f t' -> f (Combine t t')

class Nubable f t where
    nub :: Map f t -> Map f (Nub t)

instance Nubable f '[] where
    nub Empty = Empty

instance Nubable f '[e] where
    nub (Ext k v Empty) = Ext k v Empty

instance {-# OVERLAPPABLE #-}
     (Nub (e ': f ': s) ~ (e ': Nub (f ': s)),
              Nubable g (f ': s)) => Nubable g (e ': f ': s) where
    nub (Ext k v (Ext k' v' s)) = Ext k v (nub (Ext k' v' s))

instance {-# OVERLAPS #-}
    (Combinable f v v', Nubable f ((k :-> Combine v v') ': s)) => Nubable f ((k :-> v) ': (k :-> v') ': s) where
    nub (Ext k v (Ext k' v' s)) = nub (Ext k (combine v v') s)


class Conder g where
    cond :: Proxy g -> Map f s -> Map f t -> Map f (If g s t)

instance Conder True where
    cond _ s t = s

instance Conder False where
    cond _ s t = t


{-| Splitting a union of maps, given the maps we want to split it into -}
class Split s t st where
   -- where st ~ Union s t
   split :: Map f st -> (Map f s, Map f t)

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
   submap :: Map f t -> Map f s

instance Submap '[] '[] where
   submap xs = Empty

instance {-# OVERLAPPABLE #-} Submap s t => Submap s (x ': t) where
   submap (Ext _ _ xs) = submap xs

instance {-# OVERLAPS #-} Submap s t => Submap  (x ': s) (x ': t) where
   submap (Ext k v xs) = Ext k v (submap xs)
