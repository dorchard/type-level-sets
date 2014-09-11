{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies, 
             MultiParamTypeClasses, FlexibleInstances, PolyKinds, FlexibleContexts,
             UndecidableInstances, ConstraintKinds, OverlappingInstances, ScopedTypeVariables #-}

module Data.Type.Set (Set(..), Union, Unionable, union, quicksort, append, 
                      Sort, Sortable, Append(..), Split(..), Cmp, 
                      Nub, Nubable(..), AsSet, asSet, IsSet, Subset(..),
                      (:->)(..), Var(..)) where

import GHC.TypeLits
import Data.Type.Bool
import Data.Type.Equality
import Data.Proxy

{-| Core Set definition, in terms of lists -}
data Set (n :: [*]) where
    Empty :: Set '[]
    Ext :: e -> Set s -> Set (e ': s)

instance Show (Set '[]) where
    show Empty = "{}"

instance (Show e, Show' (Set s)) => Show (Set (e ': s)) where
    show (Ext e s) = "{" ++ show e ++ (show' s) ++ "}" 

class Show' t where
    show' :: t -> String
instance Show' (Set '[]) where
    show' Empty = ""
instance (Show' (Set s), Show e) => Show' (Set (e ': s)) where
    show' (Ext e s) = ", " ++ show e ++ (show' s)

{-| At the type level, normalise the list form to the set form -}
type AsSet s = Nub (Sort s)

{-| At the value level, noramlise the list form to the set form -}
asSet :: (Sortable s, Nubable (Sort s)) => Set s -> Set (AsSet s)
asSet x = nub (quicksort x)

{-| Predicate to check if in the set form -}
type IsSet s = (s ~ Nub (Sort s))

{-| Useful properties to be able to refer to someties -}
type SetProperties f = (Union f '[] ~ f, Split f '[] f, 
                        Union '[] f ~ f, Split '[] f f, 
                        Union f f ~ f, Split f f f,
                        Unionable f '[], Unionable '[] f)

{-- Union --}

{-| Union of sets -}
type Union s t = Nub (Sort (Append s t))

union :: (Unionable s t) => Set s -> Set t -> Set (Union s t)
union s t = nub (quicksort (append s t))

type Unionable s t = (Sortable (Append s t), Nubable (Sort (Append s t)))

{-| List append (essentially set disjoint union) -}
type family Append (s :: [k]) (t :: [k]) :: [k] where
            Append '[] t = t
            Append (x ': xs) ys = x ': (Append xs ys)

append :: Set s -> Set t -> Set (Append s t)
append Empty x = x
append (Ext e xs) ys = Ext e (append xs ys)

{-| Useful alias for append -}
type (s :: [k]) :++ (t :: [k]) = Append s t

{-| Splitting a union a set, given the sets we want to split it into -}
class Split s t st where
   -- where st ~ Union s t
   split :: Set st -> (Set s, Set t) 

instance Split '[] '[] '[] where
   split Empty = (Empty, Empty)

instance Split s t st => Split (x ': s) (x ': t) (x ': st) where
   split (Ext x st) = let (s, t) = split st
                      in (Ext x s, Ext x t)

instance Split s t st => Split (x ': s) t (x ': st) where
   split (Ext x st) = let (s, t) = split st
                      in  (Ext x s, t) 

instance (Split s t st) => Split s (x ': t) (x ': st) where
   split (Ext x st) = let (s, t) = split st
                      in  (s, Ext x t) 



{-| Remove duplicates from a sorted list -}
type family Nub t where
    Nub '[]           = '[]
    Nub '[e]          = '[e]
    Nub (e ': e ': s) = Nub (e ': s)
    Nub (e ': f ': s) = e ': Nub (f ': s)

{-| Value-level counterpart to the type-level 'Nub'
    Note: the value-level case for equal types is not define here, 
          but should be given per-application, e.g., custom 'merging' behaviour may be required -}

class Nubable t where
    nub :: Set t -> Set (Nub t)

instance Nubable '[] where
    nub Empty = Empty

instance Nubable '[e] where
    nub (Ext x Empty) = Ext x Empty

instance Nubable (e ': s) => Nubable (e ': e ': s) where
    nub (Ext _ (Ext e s)) = nub (Ext e s)

instance (Nub (e ': f ': s) ~ (e ': Nub (f ': s)), 
              Nubable (f ': s)) => Nubable (e ': f ': s) where
    nub (Ext e (Ext f s)) = Ext e (nub (Ext f s))


{-| Construct a subsetset 's' from a superset 't' -}
class Subset s t where
   subset :: Set t -> Set s

instance Subset '[] '[] where 
   subset xs = Empty

instance Subset '[] (x ': t) where 
   subset xs = Empty

instance Subset s t => Subset (x ': s) (x ': t) where
   subset (Ext x xs) = Ext x (subset xs)


{-| Type-level quick sort for normalising the representation of sets -}
type family Sort (xs :: [k]) :: [k] where
            Sort '[]       = '[]
            Sort (x ': xs) = ((Sort (Filter FMin x xs)) :++ '[x]) :++ (Sort (Filter FMax x xs))

data Flag = FMin | FMax

type family Filter (f :: Flag) (p :: k) (xs :: [k]) :: [k] where
            Filter f p '[]       = '[]
            Filter FMin p (x ': xs) = If (Cmp x p == LT) (x ': (Filter FMin p xs)) (Filter FMin p xs) 
            Filter FMax p (x ': xs) = If (Cmp x p == GT || Cmp x p == EQ) (x ': (Filter FMax p xs)) (Filter FMax p xs) 

{-| Value-level quick sort that respects the type-level ordering -}
class Sortable xs where
    quicksort :: Set xs -> Set (Sort xs)

instance Sortable '[] where
    quicksort Empty = Empty

instance (Sortable (Filter FMin p xs),
          Sortable (Filter FMax p xs), FilterV FMin p xs, FilterV FMax p xs) => Sortable (p ': xs) where
    quicksort (Ext p xs) = ((quicksort (less p xs)) `append` (Ext p Empty)) `append` (quicksort (more p xs))
                           where less = filterV (Proxy::(Proxy FMin))
                                 more = filterV (Proxy::(Proxy FMax))

{- Filter out the elements less-than or greater-than-or-equal to the pivot -}
class FilterV (f::Flag) p xs where
    filterV :: Proxy f -> p -> Set xs -> Set (Filter f p xs)

instance FilterV f p '[] where
    filterV _ p Empty      = Empty

instance (Conder ((Cmp x p) == LT), FilterV FMin p xs) => FilterV FMin p (x ': xs) where
    filterV f@Proxy p (Ext x xs) = cond (Proxy::(Proxy ((Cmp x p) == LT)))
                                        (Ext x (filterV f p xs)) (filterV f p xs) 

instance (Conder (((Cmp x p) == GT) || ((Cmp x p) == EQ)), FilterV FMax p xs) => FilterV FMax p (x ': xs) where
    filterV f@Proxy p (Ext x xs) = cond (Proxy::(Proxy (((Cmp x p) == GT) || ((Cmp x p) == EQ))))
                                        (Ext x (filterV f p xs)) (filterV f p xs)  

class Conder g where
    cond :: Proxy g -> Set s -> Set t -> Set (If g s t)

instance Conder True where
    cond _ s t = s

instance Conder False where
    cond _ s t = t

{-| Open-family for the ordering operation in the sort -}

type family Cmp (a :: k) (b :: k) :: Ordering

{-| Pair a symbol (representing a variable) with a type -}
infixl 2 :->
data (k :: Symbol) :-> (v :: *) = (Var k) :-> v

data Var (k :: Symbol) where Var :: Var k 
                             {- Some special defaults for some common names -}
                             X   :: Var "x"
                             Y   :: Var "y"
                             Z   :: Var "z"


instance (Show (Var k), Show v) => Show (k :-> v) where
    show (k :-> v) = "(" ++ show k ++ " :-> " ++ show v ++ ")"
instance Show (Var "x") where
    show X   = "x"
    show Var = "Var"
instance Show (Var "y") where
    show Y   = "y"
    show Var = "Var"
instance Show (Var "z") where
    show Z   = "z"
    show Var = "Var"
instance Show (Var v) where
    show _ = "Var"

{-| Symbol comparison -}
type instance Cmp (v :-> a) (u :-> b) = CmpSymbol v u
