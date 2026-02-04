module AllPaths where

open import Data.List.Base using (List)
open import Data.List.Relation.Unary.All using (All)

open import Tree using (Tree; StepFun; value; childValues)

-- We want to express the property that no philosopher will starve. That is, at
-- any point in any of the branching paths of the execution tree, that point is
-- a finite number of steps away from an EatRandomly statement.
--
-- The following datatype represents the "a finite number of steps away from X"
-- part of that statement: a value of type AllPaths P is finite and represents a
-- proof that along every path, a node satisfying P occurs after a finite number
-- of steps.
data AllPaths {A : Set} (f : StepFun A) (P : A → Set) (a : A) : Set where
  here
    : P a
    → AllPaths f P a
  there
    : All (AllPaths f P) (f a)
    → AllPaths f P a