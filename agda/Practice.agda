{-# OPTIONS --guardedness #-}
module Practice where

open import Data.Bool using (Bool; true; false; not; T)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (Tree; MkTree)
open import AllSubtrees using (AllSubtrees)
open import AllPaths using (AllPaths; here; there; bindAllPaths)

-- An infinite tree of alternating booleans, a much simplified practice version
-- of an infinite tree of program states. As a simplified version of proving
-- that no philosopher starves, we want to prove that true occurs infinitely
-- often.
 
boolTreeStep : Bool → List Bool
boolTreeStep b = not b ∷ []

boolTree : Bool → Tree Bool
boolTree b = MkTree boolTreeStep b

-- false occurs after a finite number of steps
eventuallyFalseFrom
  : (b : Bool)
  → AllPaths boolTreeStep (λ x → x ≡ false) b
eventuallyFalseFrom true
  = there (here refl ∷ [])
eventuallyFalseFrom false
  = here refl

-- true occurs exactly from false (in one step)
exactlyTrueFromFalse
  : (b : Bool)
  → b ≡ false
  → AllPaths boolTreeStep (λ x → x ≡ true) b
exactlyTrueFromFalse false refl
  = there (here refl ∷ [])

-- true occurs after a finite number of steps (using bindAllPaths)
eventuallyTrueFrom
  : (b : Bool)
  → AllPaths boolTreeStep (λ x → x ≡ true) b
eventuallyTrueFrom b
  = bindAllPaths (eventuallyFalseFrom b) exactlyTrueFromFalse

-- from any node, true occurs after a finite number of steps
eventuallyTrueFromAnywhere
  : (b : Bool)
  → AllSubtrees boolTreeStep (AllPaths boolTreeStep (λ x → x ≡ true)) b
AllSubtrees.trueHere (eventuallyTrueFromAnywhere b)
  = eventuallyTrueFrom b
AllSubtrees.trueThere (eventuallyTrueFromAnywhere b)
  = eventuallyTrueFromAnywhere (not b) ∷ []
