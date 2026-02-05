{-# OPTIONS --guardedness #-}
module Practice where

open import Data.List.Base using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import All1 using (All1; [_]; _∷_)
open import AllPaths using (AllPaths; here; there; _>>=_)
open import AllSubtrees using (AllSubtrees)
open import Tree using (Tree; MkTree)

-- An infinite tree of alternating natural numbers (0 and 1), a much simplified
-- practice version of an infinite tree of program states. As a simplified
-- version of proving that no philosopher starves, we want to prove that 1
-- occurs infinitely often.

natTreeStep : ℕ × ℕ → List (ℕ × ℕ)
natTreeStep (0 , 0)
  = (1 , 0)
  ∷ (0 , 1)
  ∷ []
natTreeStep (0 , 1)
  = (1 , 1)
  ∷ []
natTreeStep (1 , 0)
  = (1 , 1)
  ∷ []
natTreeStep (1 , 1)
  = (0 , 0)
  ∷ []
natTreeStep _
  = (2 , 2)
  ∷ []

natTree : ℕ × ℕ → Tree (ℕ × ℕ)
natTree nn = MkTree natTreeStep nn

-- Proof that a ℕ × ℕ has at most n 0s and the rest are 1s.
data CapZeroes : ℕ → ℕ × ℕ → Set where
  or-fewer
    : ∀ {n nn}
    → CapZeroes n nn
    → CapZeroes (suc n) nn
  zero
    : CapZeroes 0 (1 , 1)
  atMostOne1
    : ∀ {n₁}
    → n₁ ≤ 1
    → CapZeroes 1 (n₁ , 1)
  atMostOne2
    : ∀ {n₂}
    → n₂ ≤ 1
    → CapZeroes 1 (1 , n₂)
  two
    : ∀ {n₁ n₂}
    → n₁ ≤ 1
    → n₂ ≤ 1
    → CapZeroes 2 (n₁ , n₂)

0≤1 : 0 ≤ 1
0≤1 = z≤n

1≤1 : 1 ≤ 1
1≤1 = s≤s z≤n

eventuallyOneZeroFromTwoZeroes
  : (nn : ℕ × ℕ)
  → CapZeroes 2 nn
  → AllPaths natTreeStep (CapZeroes 1) nn
eventuallyOneZeroFromTwoZeroes nn (or-fewer cap)
  = here cap
eventuallyOneZeroFromTwoZeroes (.0 , .0) (two z≤n z≤n)
  = there
  ( here (atMostOne2 0≤1)
  ∷ [ here (atMostOne1 0≤1) ]
  )
eventuallyOneZeroFromTwoZeroes (.0 , .1) (two z≤n (s≤s z≤n))
  = here (atMostOne1 0≤1)
eventuallyOneZeroFromTwoZeroes (.1 , .0) (two (s≤s z≤n) z≤n)
  = here (atMostOne2 0≤1)
eventuallyOneZeroFromTwoZeroes (1 , 1) (two (s≤s z≤n) (s≤s z≤n))
  = here (or-fewer zero)

eventuallyZeroZeroesFromOneZero
  : (nn : ℕ × ℕ)
  → CapZeroes 1 nn
  → AllPaths natTreeStep (CapZeroes 0) nn
eventuallyZeroZeroesFromOneZero nn (or-fewer cap)
  = here cap
eventuallyZeroZeroesFromOneZero (.0 , .1) (atMostOne1 z≤n)
  = there [ here zero ]
eventuallyZeroZeroesFromOneZero (.1 , .1) (atMostOne1 (s≤s z≤n))
  = here zero
eventuallyZeroZeroesFromOneZero (.1 , .0) (atMostOne2 z≤n)
  = there [ here zero ]
eventuallyZeroZeroesFromOneZero (.1 , .1) (atMostOne2 (s≤s z≤n))
  = here zero

-- (1 , 1) occurs after a finite number of steps
eventuallyZeroZeroesFromTwoZeroes
  : AllPaths natTreeStep (CapZeroes 0) (0 , 0)
eventuallyZeroZeroesFromTwoZeroes
    = eventuallyOneZeroFromTwoZeroes (0 , 0) (two z≤n z≤n)
  >>= eventuallyZeroZeroesFromOneZero