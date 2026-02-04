{-# OPTIONS --guardedness #-}
module Practice where

open import Data.Bool using (Bool; true; false; not; T)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (Tree; MkTree)
open import AllSubtrees using (AllSubtrees)
open import AllPaths using (AllPaths; here; there; bindAllPaths)

-- An infinite tree of alternating booleans, a much simplified practice version
-- of an infinite tree of program states. As a simplified version of proving
-- that no philosopher starves, we want to prove that true occurs infinitely
-- often.


boolTreeStep : Bool × Bool → List (Bool × Bool)
boolTreeStep (false , false)
  = (true , false)
  ∷ (false , true)
  ∷ []
boolTreeStep (false , true)
  = (true , true)
  ∷ []
boolTreeStep (true , false)
  = (true , true)
  ∷ []
boolTreeStep (true , true)
  = (false , false)
  ∷ []

boolTree : Bool × Bool → Tree (Bool × Bool)
boolTree bb = MkTree boolTreeStep bb

-- (true , _) occurs after a finite number of steps
eventuallyTrueAnyFrom
  : (bb : Bool × Bool)
  → AllPaths boolTreeStep (λ x → proj₁ x ≡ true) bb
eventuallyTrueAnyFrom (false , false)
  = there (here refl ∷ (eventuallyTrueAnyFrom (false , true)) ∷ [])
eventuallyTrueAnyFrom (false , true)
  = there (here refl ∷ [])
eventuallyTrueAnyFrom (true , false)
  = here refl
eventuallyTrueAnyFrom (true , true)
  = here refl

-- (true , _) occurs a finite number of steps after (true , _)
eventuallyTrueTrueFromTrueAny
  : (bb : Bool × Bool)
  → proj₁ bb ≡ true
  → AllPaths boolTreeStep (λ x → x ≡ (true , true)) bb
eventuallyTrueTrueFromTrueAny (.true , false) refl
  = there (here refl ∷ [])
eventuallyTrueTrueFromTrueAny (.true , true) refl
  = here refl

-- (true , true) occurs after a finite number of steps
eventuallyTrueFrom
  : (bb : Bool × Bool)
  → AllPaths boolTreeStep (λ x → x ≡ (true , true)) bb
eventuallyTrueFrom bb
  = bindAllPaths
      (eventuallyTrueAnyFrom bb)
      eventuallyTrueTrueFromTrueAny

---- from any node, true occurs after a finite number of steps
--eventuallyTrueFromAnywhere
--  : (b : Bool)
--  → AllSubtrees boolTreeStep (AllPaths boolTreeStep (λ x → x ≡ true)) b
--AllSubtrees.trueHere (eventuallyTrueFromAnywhere b)
--  = eventuallyTrueFrom b
--AllSubtrees.trueThere (eventuallyTrueFromAnywhere b)
--  = eventuallyTrueFromAnywhere (not b) ∷ []
--