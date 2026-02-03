{-# OPTIONS --guardedness #-}
module Practice where

open import Data.Bool using (Bool; true; false; not; T)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (Tree; AllSubtrees; AllPaths; here; there; ValueIs)

-- An infinite tree of alternating booleans, a much simplified practice version
-- of an infinite tree of program states. As a simplified version of proving
-- that no philosopher starves, we want to prove that true occurs infinitely
-- often.
boolTree : Bool → Tree Bool
Tree.value (boolTree b)
  = b
Tree.children (boolTree b)
  = boolTree (not b) ∷ []

-- true occurs after a finite number of steps
eventuallyTrueFrom
  : (b : Bool)
  → AllPaths (ValueIs (_≡_ true)) (boolTree b)
eventuallyTrueFrom true
  = here refl
eventuallyTrueFrom false
  = there (here refl ∷ [])

-- from any node, true occurs after a finite number of steps
eventuallyTrueFromAnywhere
  : (b : Bool)
  → AllSubtrees (AllPaths (ValueIs (_≡_ true))) (boolTree b)
AllSubtrees.value (eventuallyTrueFromAnywhere b)
  = eventuallyTrueFrom b
AllSubtrees.children (eventuallyTrueFromAnywhere b)
  = eventuallyTrueFromAnywhere (not b) ∷ []
