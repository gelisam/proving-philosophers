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
-- the state is a pair of natural numbers which can each be either 0, 1, or 2.
-- At each step, either of the numbers can increment by 1, and when both are 2,
-- they both reset to 0.
--
-- >           (0 , 0)
-- >            /   \
-- >      (1 , 0)   (0 , 1)
-- >       /   \     /   \
-- >   (2 , 0) (1 , 1) (0 , 2)
-- >       \   /     \   /
-- >      (2 , 1)   (1 , 2)
-- >            \   /
-- >           (2 , 2)
--
-- As a practice for proving that no philosopher starves, we want to prove that
-- the (2 , 2) state occurs infinitely often.

natTreeStep : ℕ × ℕ → List (ℕ × ℕ)
natTreeStep (0 , 0)
  = (1 , 0)
  ∷ (0 , 1)
  ∷ []
natTreeStep (0 , 1)
  = (1 , 1)
  ∷ (0 , 2)
  ∷ []
natTreeStep (0 , 2)
  = (1 , 2)
  ∷ []
natTreeStep (1 , 0)
  = (2 , 0)
  ∷ (1 , 1)
  ∷ []
natTreeStep (1 , 1)
  = (2 , 1)
  ∷ (1 , 2)
  ∷ []
natTreeStep (1 , 2)
  = (2 , 2)
  ∷ []
natTreeStep (2 , 0)
  = (2 , 1)
  ∷ []
natTreeStep (2 , 1)
  = (2 , 2)
  ∷ []
natTreeStep (2 , 2)
  = (0 , 0)
  ∷ []
natTreeStep _
  = (3 , 3)
  ∷ []

natTree : ℕ × ℕ → Tree (ℕ × ℕ)
natTree nn = MkTree natTreeStep nn

open Types.AllPaths natTreeStep
open Types.AllSubtrees natTreeStep
open Types.InfinitelyOften natTreeStep

IsTwoTwo
  : ℕ × ℕ → Set
IsTwoTwo nn
  = nn ≡ (2 , 2)

initialPosition
  : ℕ × ℕ
initialPosition
  = (0 , 0)

-- (2 , 2) occurs infinitely-often
ProblemStatement : Set
ProblemStatement
  = InfinitelyOften IsTwoTwo initialPosition


-- We want to prove that from any position, we will reach (2 , 2) after a finite
-- number of steps. We will first calculate a finite StepsLeft value for every
-- position, and then show that for a position with @StepsLeft n@, we will reach
-- (2 , 2) after a finite number of steps, namely @n@.

data StepsLeft : ℕ → ℕ × ℕ → Set where
  four00
    : StepsLeft 4 (0 , 0)
  three01
    : StepsLeft 3 (0 , 1)
  two02
    : StepsLeft 2 (0 , 2)
  three10
    : StepsLeft 3 (1 , 0)
  two11
    : StepsLeft 2 (1 , 1)
  one12
    : StepsLeft 1 (1 , 2)
  two20
    : StepsLeft 2 (2 , 0)
  one21
    : StepsLeft 1 (2 , 1)
  zero22
    : StepsLeft 0 (2 , 2)

SomeStepsLeft
  : ℕ × ℕ → Set
SomeStepsLeft nn
  = ∃[ n ] StepsLeft n nn

initiallySomeStepsLeft
  : ∃[ n ] StepsLeft n (0 , 0)
initiallySomeStepsLeft
  = (_ , four00)

stepPreservesSomeStepsLeft
  : (parent : ℕ × ℕ)
  → SomeStepsLeft parent
  → All SomeStepsLeft (natTreeStep parent)
stepPreservesSomeStepsLeft .(0 , 0) (_ , four00)
  = (_ , three10) ∷ (_ , three01) ∷ []
stepPreservesSomeStepsLeft .(0 , 1) (_ , three01)
  = (_ , two11) ∷ (_ , two02) ∷ []
stepPreservesSomeStepsLeft .(0 , 2) (_ , two02)
  = (_ , one12) ∷ []
stepPreservesSomeStepsLeft .(1 , 0) (_ , three10)
  = (_ , two20) ∷ (_ , two11) ∷ []
stepPreservesSomeStepsLeft .(1 , 1) (_ , two11)
  = (_ , one21) ∷ (_ , one12) ∷ []
stepPreservesSomeStepsLeft .(1 , 2) (_ , one12)
  = (_ , zero22) ∷ []
stepPreservesSomeStepsLeft .(2 , 0) (_ , two20)
  = (_ , one21) ∷ []
stepPreservesSomeStepsLeft .(2 , 1) (_ , one21)
  = (_ , zero22) ∷ []
stepPreservesSomeStepsLeft .(2 , 2) (_ , zero22)
  = (_ , four00) ∷ []

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
eventuallyZeroStepsLeft .4 .(0 , 0) four00
  = there
    ( eventuallyZeroStepsLeft 3 (1 , 0) three10 ∷
    [ eventuallyZeroStepsLeft 3 (0 , 1) three01 ]
    )
eventuallyZeroStepsLeft .3 .(0 , 1) three01
  = there
    ( eventuallyZeroStepsLeft 2 (1 , 1) two11 ∷
    [ eventuallyZeroStepsLeft 2 (0 , 2) two02 ]
    )
eventuallyZeroStepsLeft .2 .(0 , 2) two02
  = there
    [ eventuallyZeroStepsLeft 1 (1 , 2) one12 ]
eventuallyZeroStepsLeft .3 .(1 , 0) three10
  = there
    ( eventuallyZeroStepsLeft 2 (2 , 0) two20 ∷
    [ eventuallyZeroStepsLeft 2 (1 , 1) two11 ]
    )
eventuallyZeroStepsLeft .2 .(1 , 1) two11
  = there
    ( eventuallyZeroStepsLeft 1 (2 , 1) one21 ∷
    [ eventuallyZeroStepsLeft 1 (1 , 2) one12 ]
    )
eventuallyZeroStepsLeft .1 .(1 , 2) one12
  = there
    [ eventuallyZeroStepsLeft 0 (2 , 2) zero22 ]
eventuallyZeroStepsLeft .2 .(2 , 0) two20
  = there
    [ eventuallyZeroStepsLeft 1 (2 , 1) one21 ]
eventuallyZeroStepsLeft .1 .(2 , 1) one21
  = there
    [ eventuallyZeroStepsLeft 0 (2 , 2) zero22 ]
eventuallyZeroStepsLeft .0 .(2 , 2) zero22
  = here zero22

zeroStepsMeansTwoTwo
  : (nn : ℕ × ℕ)
  → StepsLeft 0 nn
  → IsTwoTwo nn
zeroStepsMeansTwoTwo .(2 , 2) zero22
  = refl

eventuallyTwoTwo
  : (nn : ℕ × ℕ)
  → SomeStepsLeft nn
  → AllPaths IsTwoTwo nn
eventuallyTwoTwo nn (n , stepsLeft)
  = starting-at
      nn
    knowing
      (eventuallyZeroStepsLeft n nn stepsLeft)
    apply
      (AllPaths-map zeroStepsMeansTwoTwo)

mainProof : ProblemStatement
mainProof
  = starting-at
      initialPosition
    knowing
      alwaysSomeStepsLeft
    apply
      (infinitelyOften eventuallyTwoTwo)
