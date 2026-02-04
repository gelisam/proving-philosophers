{-# OPTIONS --guardedness #-}
module Practice where

open import Data.Bool using (Bool; true; false; not; T)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (Tree; MkTree)
open import AllSubtrees using (AllSubtrees)
open import AllPaths using (AllPaths; here; there)

-- An infinite tree of alternating booleans, a much simplified practice version
-- of an infinite tree of program states. As a simplified version of proving
-- that no philosopher starves, we want to prove that true occurs infinitely
-- often.
 
boolTreeStep : Bool → List Bool
boolTreeStep b = not b ∷ []

boolTree : Bool → Tree Bool
boolTree b = MkTree boolTreeStep b

-- true occurs after a finite number of steps
eventuallyTrueFrom
  : (b : Bool)
  → AllPaths boolTreeStep (_≡_ true) b
eventuallyTrueFrom true
  = here refl
eventuallyTrueFrom false
  = there (here refl ∷ [])

-- from any node, true occurs after a finite number of steps
eventuallyTrueFromAnywhere
  : (b : Bool)
  → AllSubtrees boolTreeStep (AllPaths boolTreeStep (_≡_ true)) b
AllSubtrees.trueHere (eventuallyTrueFromAnywhere b)
  = eventuallyTrueFrom b
AllSubtrees.trueThere (eventuallyTrueFromAnywhere b)
  = eventuallyTrueFromAnywhere (not b) ∷ []
