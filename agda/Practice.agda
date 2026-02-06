{-# OPTIONS --guardedness #-}
module Practice where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import All1 using (All1; [_]; _∷_)
open import Tree using (Tree; MkTree)
import AllPaths using (AllPaths; here; there; AllPaths-map; _>>=_)
import AllSubtrees using (AllSubtrees)
import InfinitelyOften using (InfinitelyOften; infinitelyOften)

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
open InfinitelyOften natTreeStep

ProblemStatement : Set
ProblemStatement
  = InfinitelyOften (_≡_ (1 , 1)) (0 , 0)


-- We will first prove that starting from two zeroes (0 , 0), we eventually
-- reach a position with at most one zero, then finally, a position with no
-- zeroes (1 , 1).

-- Proof that a ℕ × ℕ has at most n 0s and the rest are 1s.
data CapZeroes : ℕ → ℕ × ℕ → Set where
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

---------------------------------------
-- part 1: always at most two zeroes --
---------------------------------------

alwaysTwoZeroesFromTwoZeroes
  : (nn : ℕ × ℕ)
  → CapZeroes 2 nn
  → AllSubtrees (CapZeroes 2) nn
AllSubtrees.trueHere (alwaysTwoZeroesFromTwoZeroes nn cap)
  = cap
AllSubtrees.trueThere (alwaysTwoZeroesFromTwoZeroes (.0 , .0) (atMostTwo z≤n z≤n))
  = alwaysTwoZeroesFromTwoZeroes (1 , 0) (atMostTwo 1≤1 0≤1)
  ∷ alwaysTwoZeroesFromTwoZeroes (0 , 1) (atMostTwo 0≤1 1≤1)
  ∷ []
AllSubtrees.trueThere (alwaysTwoZeroesFromTwoZeroes (.0 , .1) (atMostTwo z≤n (s≤s z≤n)))
  = alwaysTwoZeroesFromTwoZeroes (1 , 1) (atMostTwo 1≤1 1≤1)
  ∷ []
AllSubtrees.trueThere (alwaysTwoZeroesFromTwoZeroes (.1 , .0) (atMostTwo (s≤s z≤n) z≤n))
  = alwaysTwoZeroesFromTwoZeroes (1 , 1) (atMostTwo 1≤1 1≤1)
  ∷ []
AllSubtrees.trueThere (alwaysTwoZeroesFromTwoZeroes (.1 , .1) (atMostTwo (s≤s z≤n) (s≤s z≤n)))
  = alwaysTwoZeroesFromTwoZeroes (0 , 0) (atMostTwo 0≤1 0≤1)
  ∷ []

------------------------------------
-- part 2: eventually zero zeroes --
------------------------------------

eventuallyOneZeroFromTwoZeroes
  : (nn : ℕ × ℕ)
  → CapZeroes 2 nn
  → AllPaths (CapZeroes 1) nn
eventuallyOneZeroFromTwoZeroes (.0 , .0) (atMostTwo z≤n z≤n)
  = there
  ( here (atMostOne2 0≤1)
  ∷ [ here (atMostOne1 0≤1) ]
  )
eventuallyOneZeroFromTwoZeroes (.0 , .1) (atMostTwo z≤n (s≤s z≤n))
  = here (atMostOne1 0≤1)
eventuallyOneZeroFromTwoZeroes (.1 , .0) (atMostTwo (s≤s z≤n) z≤n)
  = here (atMostOne2 0≤1)
eventuallyOneZeroFromTwoZeroes (.1 , .1) (atMostTwo (s≤s z≤n) (s≤s z≤n))
  = here (atMostOne2 1≤1)

eventuallyZeroZeroesFromOneZero
  : (nn : ℕ × ℕ)
  → CapZeroes 1 nn
  → AllPaths (CapZeroes 0) nn
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
  : (nn : ℕ × ℕ)
  → CapZeroes 2 nn
  → AllPaths (CapZeroes 0) nn
eventuallyZeroZeroesFromTwoZeroes nn cap
    = eventuallyOneZeroFromTwoZeroes nn cap
  >>= eventuallyZeroZeroesFromOneZero

---------------------------------
-- combining part 1 and part 2 --
---------------------------------

zeroZeroes⇒OneOne
  : (nn : ℕ × ℕ)
  → CapZeroes 0 nn
  → (1 , 1) ≡ nn
zeroZeroes⇒OneOne (.1 , .1) zero
  = refl

eventuallyOneOneFromTwoZeroes
  : (nn : ℕ × ℕ)
  → CapZeroes 2 nn
  → AllPaths (_≡_ (1 , 1)) nn
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
      (0 , 0)
      (alwaysTwoZeroesFromTwoZeroes
        (0 , 0)
        (atMostTwo 0≤1 0≤1))