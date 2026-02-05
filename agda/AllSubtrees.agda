{-# OPTIONS --guardedness #-}
module AllSubtrees where

open import Data.List.Base using (List)
open import Data.List.Relation.Unary.All using (All; []; _∷_)

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

mutual
  AllSubtrees-map
    : {A : Set}
    → {f : StepFun A}
    → {P Q : A → Set}
    → ((x : A) → P x → Q x)
    → (x : A)
    → AllSubtrees f P x
    → AllSubtrees f Q x
  AllSubtrees.trueHere (AllSubtrees-map p2q x ast)
    = p2q x (AllSubtrees.trueHere ast)
  AllSubtrees.trueThere (AllSubtrees-map {A} {f} p2q x ast)
    = All-AllSubtrees-map
        p2q
        (f x)
        (AllSubtrees.trueThere ast)

  All-AllSubtrees-map
    : {A : Set}
    → {f : StepFun A}
    → {P Q : A → Set}
    → ((x : A) → P x → Q x)
    → (xs : List A)
    → All (AllSubtrees f P) xs
    → All (AllSubtrees f Q) xs
  All-AllSubtrees-map p2q _ []
    = []
  All-AllSubtrees-map p2q _ (px ∷ pxs)
    = AllSubtrees-map p2q _ px
    ∷ All-AllSubtrees-map p2q _ pxs
