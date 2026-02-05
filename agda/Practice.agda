{-# OPTIONS --guardedness #-}
module Practice where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

open import Tree using (Tree; MkTree)
open import AllSubtrees using (AllSubtrees)
open import AllPaths using (AllPaths; here; there; _>>=_)

-- An infinite tree of alternating natural numbers (0 and 1), a much simplified
-- practice version of an infinite tree of program states. As a simplified
-- version of proving that no philosopher starves, we want to prove that 1
-- occurs infinitely often.

natTreeStep : ℕ × ℕ → List (ℕ × ℕ)
natTreeStep (zero , zero)
  = (suc zero , zero)
  ∷ (zero , suc zero)
  ∷ []
natTreeStep (zero , suc zero)
  = (suc zero , suc zero)
  ∷ []
natTreeStep (suc zero , zero)
  = (suc zero , suc zero)
  ∷ []
natTreeStep (suc zero , suc zero)
  = (zero , zero)
  ∷ []
natTreeStep _ = []  -- catch-all for invalid states (neither 0 nor 1)

natTree : ℕ × ℕ → Tree (ℕ × ℕ)
natTree nn = MkTree natTreeStep nn

-- Proof that a ℕ × ℕ has at most n zeros
data CapZeros : ℕ → ℕ × ℕ → Set where
  or-fewer
    : ∀ {n nn}
    → CapZeros n nn
    → CapZeros (suc n) nn
  zero-cap
    : ∀ {n₁ n₂}
    → n₁ ≢ zero
    → n₂ ≢ zero
    → CapZeros 0 (n₁ , n₂)
  atMostOne1
    : ∀ {n₁ n₂}
    → n₂ ≢ zero
    → CapZeros 1 (n₁ , n₂)
  atMostOne2
    : ∀ {n₁ n₂}
    → n₁ ≢ zero
    → CapZeros 1 (n₁ , n₂)
  two
    : CapZeros 2 (zero , zero)

-- Helper to show that suc n ≢ zero
suc≢zero : ∀ {n} → suc n ≢ zero
suc≢zero ()

eventuallyTwoZerosFrom
  : (nn : ℕ × ℕ)
  → AllPaths natTreeStep (CapZeros 2) nn
eventuallyTwoZerosFrom (zero , zero)
  = here two
eventuallyTwoZerosFrom (zero , suc n)
  = here (or-fewer (atMostOne1 suc≢zero))
eventuallyTwoZerosFrom (suc n , zero)
  = here (or-fewer (atMostOne2 suc≢zero))
eventuallyTwoZerosFrom (suc n , suc m)
  = here (or-fewer (or-fewer (zero-cap suc≢zero suc≢zero)))

eventuallyOneZeroFromTwoZeros
  : (nn : ℕ × ℕ)
  → CapZeros 2 nn
  → AllPaths natTreeStep (CapZeros 1) nn
eventuallyOneZeroFromTwoZeros nn (or-fewer cap)
  = here cap
eventuallyOneZeroFromTwoZeros (zero , zero) two
  = there
  ( here (atMostOne2 suc≢zero)
  ∷ here (atMostOne1 suc≢zero)
  ∷ []
  )

eventuallyZeroZerosFromOneZero
  : (nn : ℕ × ℕ)
  → CapZeros 1 nn
  → AllPaths natTreeStep (CapZeros 0) nn
eventuallyZeroZerosFromOneZero nn (or-fewer cap)
  = here cap
-- atMostOne1 cases: n₂ ≢ zero
eventuallyZeroZerosFromOneZero (zero , zero) (atMostOne1 prf)
  = ⊥-elim (prf refl)  -- contradiction: n₂ = zero but prf says n₂ ≢ zero
eventuallyZeroZerosFromOneZero (zero , suc zero) (atMostOne1 prf)
  = there (here (zero-cap suc≢zero suc≢zero) ∷ [])
eventuallyZeroZerosFromOneZero (zero , suc (suc n)) (atMostOne1 prf)
  = there []  -- natTreeStep (zero , suc (suc n)) = []
eventuallyZeroZerosFromOneZero (suc zero , zero) (atMostOne1 prf)
  = ⊥-elim (prf refl)  -- contradiction
eventuallyZeroZerosFromOneZero (suc zero , suc zero) (atMostOne1 prf)
  = here (zero-cap suc≢zero suc≢zero)
eventuallyZeroZerosFromOneZero (suc zero , suc (suc n)) (atMostOne1 prf)
  = there []  -- natTreeStep (suc zero , suc (suc n)) = []
eventuallyZeroZerosFromOneZero (suc (suc n) , zero) (atMostOne1 prf)
  = ⊥-elim (prf refl)  -- contradiction
eventuallyZeroZerosFromOneZero (suc (suc n) , suc zero) (atMostOne1 prf)
  = there []  -- natTreeStep (suc (suc n) , suc zero) = []
eventuallyZeroZerosFromOneZero (suc (suc n) , suc (suc m)) (atMostOne1 prf)
  = there []  -- natTreeStep (suc (suc n) , suc (suc m)) = []
-- atMostOne2 cases: n₁ ≢ zero
eventuallyZeroZerosFromOneZero (zero , zero) (atMostOne2 prf)
  = ⊥-elim (prf refl)  -- contradiction
eventuallyZeroZerosFromOneZero (zero , suc zero) (atMostOne2 prf)
  = ⊥-elim (prf refl)  -- contradiction
eventuallyZeroZerosFromOneZero (zero , suc (suc m)) (atMostOne2 prf)
  = ⊥-elim (prf refl)  -- contradiction
eventuallyZeroZerosFromOneZero (suc zero , zero) (atMostOne2 prf)
  = there (here (zero-cap suc≢zero suc≢zero) ∷ [])
eventuallyZeroZerosFromOneZero (suc (suc n) , zero) (atMostOne2 prf)
  = there []  -- natTreeStep (suc (suc n) , zero) = []
eventuallyZeroZerosFromOneZero (suc zero , suc zero) (atMostOne2 prf)
  = here (zero-cap suc≢zero suc≢zero)
eventuallyZeroZerosFromOneZero (suc zero , suc (suc m)) (atMostOne2 prf)
  = there []  -- natTreeStep (suc zero , suc (suc m)) = []
eventuallyZeroZerosFromOneZero (suc (suc n) , suc zero) (atMostOne2 prf)
  = there []  -- natTreeStep (suc (suc n) , suc zero) = []
eventuallyZeroZerosFromOneZero (suc (suc n) , suc (suc m)) (atMostOne2 prf)
  = there []  -- natTreeStep (suc (suc n) , suc (suc m)) = []

-- (1 , 1) occurs after a finite number of steps
eventuallyZeroZerosFrom
  : (nn : ℕ × ℕ)
  → AllPaths natTreeStep (CapZeros 0) nn
eventuallyZeroZerosFrom nn
    = eventuallyTwoZerosFrom nn
  >>= eventuallyOneZeroFromTwoZeros
  >>= eventuallyZeroZerosFromOneZero