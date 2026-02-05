{-# OPTIONS --guardedness #-}
module Practice where

open import Data.List.Base using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import All1 using (All1; [_]; _∷_)
open import Tree using (Tree; MkTree)
import AllPaths using (AllPaths; here; there; _>>=_)
import AllSubtrees using (AllSubtrees)

-- A much simplified version of the infinite tree of program states which we
-- want to use for the Dining Philosophers problem. In this simplified version,
-- the state is a pair of natural numbers which can each be either 0 or 1. At
-- each step, either of the numbers can increment (0 → 1), and when both are 1,
-- they both reset to 0.
--
-- >      (0 , 0)
-- >       /   \
-- > (1 , 0)   (0 , 1)
-- >       \   /
-- >      (1 , 1)
--
-- As a practice for proving that no philosopher starves, we want to prove that
-- the (1 , 1) state occurs infinitely often.

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

open AllPaths natTreeStep
open AllSubtrees natTreeStep

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
  atMostTwo
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
  → AllPaths (CapZeroes 1) nn
eventuallyOneZeroFromTwoZeroes nn (or-fewer cap)
  = here cap
eventuallyOneZeroFromTwoZeroes (.0 , .0) (atMostTwo z≤n z≤n)
  = there
  ( here (atMostOne2 0≤1)
  ∷ [ here (atMostOne1 0≤1) ]
  )
eventuallyOneZeroFromTwoZeroes (.0 , .1) (atMostTwo z≤n (s≤s z≤n))
  = here (atMostOne1 0≤1)
eventuallyOneZeroFromTwoZeroes (.1 , .0) (atMostTwo (s≤s z≤n) z≤n)
  = here (atMostOne2 0≤1)
eventuallyOneZeroFromTwoZeroes (1 , 1) (atMostTwo (s≤s z≤n) (s≤s z≤n))
  = here (or-fewer zero)

eventuallyZeroZeroesFromOneZero
  : (nn : ℕ × ℕ)
  → CapZeroes 1 nn
  → AllPaths (CapZeroes 0) nn
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
  : AllPaths (CapZeroes 0) (0 , 0)
eventuallyZeroZeroesFromTwoZeroes
    = eventuallyOneZeroFromTwoZeroes (0 , 0) (atMostTwo z≤n z≤n)
  >>= eventuallyZeroZeroesFromOneZero