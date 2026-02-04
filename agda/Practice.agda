{-# OPTIONS --guardedness #-}
module Practice where

open import Data.Bool using (Bool; true; false; not; T)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
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

-- Proof that a Bool × Bool has at most n falses
data CapFalses : ℕ → Bool × Bool → Set where
  or-fewer
    : ∀ {n bb}
    → CapFalses n bb
    → CapFalses (suc n) bb
  zero
    : CapFalses 0 (true , true)
  atMostOne1
    : ∀ {b₁}
    → CapFalses 1 (b₁ , true)
  atMostOne2
    : ∀ {b₂}
    → CapFalses 1 (true , b₂)
  two
    : CapFalses 2 (false , false)

eventuallyTwoFalsesFrom
  : (bb : Bool × Bool)
  → AllPaths boolTreeStep (CapFalses 2) bb
eventuallyTwoFalsesFrom (false , false)
  = here two
eventuallyTwoFalsesFrom (false , true)
  = here (or-fewer atMostOne1)
eventuallyTwoFalsesFrom (true , false)
  = here (or-fewer atMostOne2)
eventuallyTwoFalsesFrom (true , true)
  = here (or-fewer (or-fewer zero))

eventuallyOneFalseFromTwoFalses
  : (bb : Bool × Bool)
  → CapFalses 2 bb
  → AllPaths boolTreeStep (CapFalses 1) bb
eventuallyOneFalseFromTwoFalses bb (or-fewer cap)
  = here cap
eventuallyOneFalseFromTwoFalses (.false , .false) two
  = there
  ( here atMostOne2
  ∷ here atMostOne1
  ∷ []
  )

eventuallyZeroFalsesFromOneFalse
  : (bb : Bool × Bool)
  → CapFalses 1 bb
  → AllPaths boolTreeStep (CapFalses 0) bb
eventuallyZeroFalsesFromOneFalse bb (or-fewer cap)
  = here cap
eventuallyZeroFalsesFromOneFalse (false , .true) atMostOne1
  = there (here zero ∷ [])
eventuallyZeroFalsesFromOneFalse (true , .true) atMostOne1
  = here zero
eventuallyZeroFalsesFromOneFalse ( .true , false) atMostOne2
  = there (here zero ∷ [])
eventuallyZeroFalsesFromOneFalse ( .true , true) atMostOne2
  = here zero

-- (true , true) occurs after a finite number of steps
eventuallyZeroFalsesFrom
  : (bb : Bool × Bool)
  → AllPaths boolTreeStep (CapFalses 0) bb
eventuallyZeroFalsesFrom bb
  = bindAllPaths
      (bindAllPaths
        (eventuallyTwoFalsesFrom bb)
        eventuallyOneFalseFromTwoFalses)
      eventuallyZeroFalsesFromOneFalse