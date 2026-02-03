{-# OPTIONS --guardedness #-}
module Tree where

open import Data.List.Base using (List)
open import Data.List.Relation.Unary.All using (All)

-- Possibly-infinite tree
record Tree (A : Set) : Set where
  coinductive
  field
    value
      : A
    children
      : List (Tree A)

-- P is true for every subtree
record AllSubtrees {A : Set} (P : Tree A → Set) (t : Tree A) : Set where
  coinductive
  field
    value
      : P t
    children
      : All (AllSubtrees P) (Tree.children t)

-- Along every path, P occurs after a finite number of steps
data AllPaths {A : Set} (P : Tree A → Set) (t : Tree A) : Set where
  here
    : P t
    → AllPaths P t
  there
    : All (AllPaths P) (Tree.children t)
    → AllPaths P t

-- Helper function for the common case where P is a predicate on values
ValueIs : {A : Set} → (A → Set) → (Tree A → Set)
ValueIs P t = P (Tree.value t)