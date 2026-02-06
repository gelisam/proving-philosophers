{-# OPTIONS --guardedness #-}
module Practice where

open import Data.Fin using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; _≤_; z≤n; s≤s)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import All1 using (All1; [_]; _∷_)
open import Tree using (Tree; MkTree)
import AllPaths using (AllPaths; here; there; AllPaths-map; _>>=_)
import AllSubtrees using (AllSubtrees)
import InfinitelyOften using (InfinitelyOften; infinitelyOften)

-- A much simplified version of the infinite tree of program states which we
-- want to use for the Dining Philosophers problem. In this simplified version,
-- the state is a pair of Fin 2 values which can each be either 0 or 1. At
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

natTreeStep : Fin 2 × Fin 2 → List (Fin 2 × Fin 2)
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

natTree : Fin 2 × Fin 2 → Tree (Fin 2 × Fin 2)
natTree nn = MkTree natTreeStep nn

open AllPaths natTreeStep
open AllSubtrees natTreeStep
open InfinitelyOften natTreeStep

ProblemStatement : Set
ProblemStatement
  = InfinitelyOften (_≡_ (suc zero , suc zero)) (zero , zero)


-- We will first prove that starting from two zeroes (0 , 0), we eventually
-- reach a position with at most one zero, then finally, a position with no
-- zeroes (1 , 1).

-- Proof that a Fin 2 × Fin 2 has at most n 0s and the rest are 1s.
data CapZeroes : ℕ → Fin 2 × Fin 2 → Set where
  capZero
    : CapZeroes 0 (suc zero , suc zero)
  capOne1
    : ∀ {n₁}
    → CapZeroes 1 (n₁ , suc zero)
  capOne2
    : ∀ {n₂}
    → CapZeroes 1 (suc zero , n₂)
  capTwo
    : ∀ {n₁ n₂}
    → CapZeroes 2 (n₁ , n₂)

---------------------------------------
-- part 1: always at most two zeroes --
---------------------------------------

alwaysTwoZeroesFromTwoZeroes
  : (nn : Fin 2 × Fin 2)
  → CapZeroes 2 nn
  → AllSubtrees (CapZeroes 2) nn
AllSubtrees.trueHere (alwaysTwoZeroesFromTwoZeroes nn cap)
  = cap
AllSubtrees.trueThere (alwaysTwoZeroesFromTwoZeroes (zero , zero) capTwo)
  = alwaysTwoZeroesFromTwoZeroes (suc zero , zero) capTwo
  ∷ alwaysTwoZeroesFromTwoZeroes (zero , suc zero) capTwo
  ∷ []
AllSubtrees.trueThere (alwaysTwoZeroesFromTwoZeroes (zero , suc zero) capTwo)
  = alwaysTwoZeroesFromTwoZeroes (suc zero , suc zero) capTwo
  ∷ []
AllSubtrees.trueThere (alwaysTwoZeroesFromTwoZeroes (suc zero , zero) capTwo)
  = alwaysTwoZeroesFromTwoZeroes (suc zero , suc zero) capTwo
  ∷ []
AllSubtrees.trueThere (alwaysTwoZeroesFromTwoZeroes (suc zero , suc zero) capTwo)
  = alwaysTwoZeroesFromTwoZeroes (zero , zero) capTwo
  ∷ []

------------------------------------
-- part 2: eventually zero zeroes --
------------------------------------

eventuallyOneZeroFromTwoZeroes
  : (nn : Fin 2 × Fin 2)
  → CapZeroes 2 nn
  → AllPaths (CapZeroes 1) nn
eventuallyOneZeroFromTwoZeroes (zero , zero) capTwo
  = there
  ( here capOne2
  ∷ [ here capOne1 ]
  )
eventuallyOneZeroFromTwoZeroes (zero , suc zero) capTwo
  = here capOne1
eventuallyOneZeroFromTwoZeroes (suc zero , zero) capTwo
  = here capOne2
eventuallyOneZeroFromTwoZeroes (suc zero , suc zero) capTwo
  = here capOne2

eventuallyZeroZeroesFromOneZero
  : (nn : Fin 2 × Fin 2)
  → CapZeroes 1 nn
  → AllPaths (CapZeroes 0) nn
eventuallyZeroZeroesFromOneZero (zero , suc zero) capOne1
  = there [ here capZero ]
eventuallyZeroZeroesFromOneZero (suc zero , suc zero) capOne1
  = here capZero
eventuallyZeroZeroesFromOneZero (suc zero , zero) capOne2
  = there [ here capZero ]
eventuallyZeroZeroesFromOneZero (suc zero , suc zero) capOne2
  = here capZero

-- (1 , 1) occurs after a finite number of steps
eventuallyZeroZeroesFromTwoZeroes
  : (nn : Fin 2 × Fin 2)
  → CapZeroes 2 nn
  → AllPaths (CapZeroes 0) nn
eventuallyZeroZeroesFromTwoZeroes nn cap
    = eventuallyOneZeroFromTwoZeroes nn cap
  >>= eventuallyZeroZeroesFromOneZero

---------------------------------
-- combining part 1 and part 2 --
---------------------------------

zeroZeroes⇒OneOne
  : (nn : Fin 2 × Fin 2)
  → CapZeroes 0 nn
  → (suc zero , suc zero) ≡ nn
zeroZeroes⇒OneOne (suc zero , suc zero) capZero
  = refl

eventuallyOneOneFromTwoZeroes
  : (nn : Fin 2 × Fin 2)
  → CapZeroes 2 nn
  → AllPaths (_≡_ (suc zero , suc zero)) nn
eventuallyOneOneFromTwoZeroes nn cap
  = AllPaths-map
      zeroZeroes⇒OneOne
      nn
      (eventuallyZeroZeroesFromTwoZeroes nn cap)

-- (1 , 1) occurs infinitely-often
mainProof : ProblemStatement
mainProof
  = infinitelyOften
      eventuallyOneOneFromTwoZeroes
      (zero , zero)
      (alwaysTwoZeroesFromTwoZeroes
        (zero , zero)
        capTwo)