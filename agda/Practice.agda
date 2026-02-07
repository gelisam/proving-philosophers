{-# OPTIONS --guardedness #-}
module Practice where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types.All1 using (All1; [_]; _∷_)
open import Types.Readability using (starting-at_knowing_apply)
open import Types.Tree using (Tree; MkTree)
import Types.AllPaths using (AllPaths; here; there; AllPaths-map; _>>=_)
import Types.AllSubtrees using (AllSubtrees; AllSubtrees-induction)
import Types.InfinitelyOften using (InfinitelyOften; infinitelyOften)

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

open Types.AllPaths natTreeStep
open Types.AllSubtrees natTreeStep
open Types.InfinitelyOften natTreeStep

IsOneOne
  : ℕ × ℕ → Set
IsOneOne nn
  = nn ≡ (1 , 1)

initialPosition
  : ℕ × ℕ
initialPosition
  = (0 , 0)

ProblemStatement : Set
ProblemStatement
  = InfinitelyOften IsOneOne initialPosition


-- We want to prove that from any position, we will reach (0 , 0) after a finite
-- number of steps. We will first calculate a finite StepsLeft value for every
-- position, and then show that for a position with @StepsLeft n@, we will reach
-- (0 , 0) after a finite number of steps, namely @n@.

data StepsLeft : ℕ → ℕ × ℕ → Set where
  zero
    : StepsLeft 0 (1 , 1)
  one01
    : StepsLeft 1 (0 , 1)
  one10
    : StepsLeft 1 (1 , 0)
  two
    : StepsLeft 2 (0 , 0)

SomeStepsLeft
  : ℕ × ℕ → Set
SomeStepsLeft nn
  = ∃[ n ] StepsLeft n nn

initiallySomeStepsLeft
  : ∃[ n ] StepsLeft n (0 , 0)
initiallySomeStepsLeft
  = (_ , two)

stepPreservesSomeStepsLeft
  : (parent : ℕ × ℕ)
  → SomeStepsLeft parent
  → All SomeStepsLeft (natTreeStep parent)
stepPreservesSomeStepsLeft .(0 , 0) (_ , two)
  = (_ , one10) ∷ (_ , one01) ∷ []
stepPreservesSomeStepsLeft .(0 , 1) (_ , one01)
  = (_ , zero) ∷ []
stepPreservesSomeStepsLeft .(1 , 0) (_ , one10)
  = (_ , zero) ∷ []
stepPreservesSomeStepsLeft .(1 , 1) (_ , zero)
  = (_ , two) ∷ []

alwaysSomeStepsLeft
  : AllSubtrees SomeStepsLeft initialPosition
alwaysSomeStepsLeft
  = starting-at
      initialPosition
    knowing
      initiallySomeStepsLeft
    apply
      (AllSubtrees-induction stepPreservesSomeStepsLeft)

eventuallyZeroStepsLeft
  : (n : ℕ)
  → (nn : ℕ × ℕ)
  → StepsLeft n nn
  → AllPaths (StepsLeft 0) nn
eventuallyZeroStepsLeft .0 .(1 , 1) zero
  = here zero
eventuallyZeroStepsLeft .1 .(0 , 1) one01
  = there
    [ eventuallyZeroStepsLeft 0 (1 , 1) zero ]
eventuallyZeroStepsLeft .1 .(1 , 0) one10
  = there
    [ eventuallyZeroStepsLeft 0 (1 , 1) zero ]
eventuallyZeroStepsLeft .2 .(0 , 0) two
  = there
    ( eventuallyZeroStepsLeft 1 (1 , 0) one10 ∷
    [ eventuallyZeroStepsLeft 1 (0 , 1) one01 ]
    )

zeroStepsMeansOneOne
  : (nn : ℕ × ℕ)
  → StepsLeft 0 nn
  → IsOneOne nn
zeroStepsMeansOneOne .(1 , 1) zero
  = refl

eventuallyOneOne
  : (nn : ℕ × ℕ)
  → SomeStepsLeft nn
  → AllPaths IsOneOne nn
eventuallyOneOne nn (n , stepsLeft)
  = starting-at
      nn
    knowing
      (eventuallyZeroStepsLeft n nn stepsLeft)
    apply
      (AllPaths-map zeroStepsMeansOneOne)

-- (1 , 1) occurs infinitely-often
mainProof : ProblemStatement
mainProof
  = starting-at
      initialPosition
    knowing
      alwaysSomeStepsLeft
    apply
      (infinitelyOften eventuallyOneOne)