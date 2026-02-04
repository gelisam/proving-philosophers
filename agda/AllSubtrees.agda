{-# OPTIONS --guardedness #-}
module AllSubtrees where

open import Data.List.Relation.Unary.All using (All)

open import Tree using (StepFun)

-- We want to express the property that no philosopher will starve. That is, at
-- any point in any of the branching paths of the execution tree, that point is
-- a finite number of steps away from an EatRandomly statement.
--
-- The following datatype represents the "at any point in any of the branching
-- paths" part of that statement: a value of type AllSubtrees P is a proof that
-- P is true for every subtree.
record AllSubtrees {A : Set} (f : StepFun A) (P : A → Set) (a : A) : Set where
  coinductive
  field
    trueHere
      : P a
    trueThere
      : All (AllSubtrees f P) (f a)