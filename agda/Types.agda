module Types where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; lookup)


----------------------------------------------
-- Datatypes for representing the evolution --
-- of non-deterministic systems             --
----------------------------------------------

data FiniteDeadlockable (S : Set) (A : Set) : Set where
  deadlocked
    : FiniteDeadlockable S A
  done
    : A
    → FiniteDeadlockable S A
  next
    : S
    → FiniteDeadlockable S A

data Finite (S : Set) (A : Set) : Set where
  done
    : A
    → Finite S A
  next
    : S
    → Finite S A

-- deadlocked is permanent
data Deadlockable (S : Set) : Set where
  deadlocked
    : Deadlockable S
  next
    : S
    → Deadlockable S

-- blocked could be temporary or permanent
data Blockable (S : Set) : Set where
  blocked
    : Blockable S
  next
    : S
    → Blockable S

data Magma (A : Set) : Set where
  atom
    : A
    → Magma A
  concat
    : Magma A
    → Magma A
    → Magma A

data Tree (S : Set) (FS : Set) : Set where
  mkTree
    : (S → Magma FS)
    → FS
    → Tree S FS

InfinitePossibilityTree : Set → Set
InfinitePossibilityTree S
  = Tree S S

InfiniteDeadlockablePossibilityTree : Set → Set
InfiniteDeadlockablePossibilityTree S
  = Tree S (Deadlockable S)

FinitePossibilityTree : Set → Set → Set
FinitePossibilityTree S A
  = Tree S (Finite S A)

FiniteDeadlockablePossibilityTree : Set → Set → Set
FiniteDeadlockablePossibilityTree S A
  = Tree S (FiniteDeadlockable S A)

PossibleAtomicSteps : Set → Set → Set
PossibleAtomicSteps S A = S → FiniteDeadlockable (Magma S) A

module timeStepImpl
         {S A}
         (possibleSteps : PossibleAtomicSteps S A)
         where
  mutual
    stepFuns
      : Magma S
      → Magma (FiniteDeadlockable S A)
    stepFuns (atom s)
      = atom (next s)
    stepFuns (concat m1 m2)
      = concat (stepFuns m1) (stepFuns m2)

    stepFun
      : S
      → Magma (FiniteDeadlockable S A)
    stepFun s with possibleSteps s
    ... | deadlocked
        = atom deadlocked
    ... | done a
        = atom (done a)
    ... | next ss
        = stepFuns ss

timeStep
  : ∀ {S A}
  → PossibleAtomicSteps S A
  → S
  → FiniteDeadlockablePossibilityTree S A
timeStep {S} {A} possibleSteps s0
  = mkTree
      (timeStepImpl.stepFun possibleSteps)
      (next s0)

module lifecycleImpl
         {S A}
         (possibleSteps : PossibleAtomicSteps S A)
         (advanceTime : A → S)
         where
  advanceTimes
    : Magma (FiniteDeadlockable S A)
    → Magma (Deadlockable S)
  advanceTimes (atom deadlocked)
    = atom deadlocked
  advanceTimes (atom (done a))
    = atom (next (advanceTime a))
  advanceTimes (atom (next s))
    = atom (next s)
  advanceTimes (concat m1 m2)
    = concat (advanceTimes m1) (advanceTimes m2)

  stepFun
    : S → Magma (Deadlockable S)
  stepFun s
    = advanceTimes (timeStepImpl.stepFun possibleSteps s)

lifecycle
  : ∀ {S A}
  → PossibleAtomicSteps S A
  → (advanceTime : A → S)
  → S
  → InfiniteDeadlockablePossibilityTree S
lifecycle {S} {A} possibleSteps advanceTime s0
  = mkTree
      (lifecycleImpl.stepFun possibleSteps advanceTime)
      (next s0)


-------------------
-- proof objects --
-------------------

data FiniteButNotDeadlockable
       {S : Set}
       {A : Set}
       : FiniteDeadlockable S A
       → Set where
  done
    : (a : A)
    → FiniteButNotDeadlockable (done a)
  next
    : (s : S)
    → FiniteButNotDeadlockable (next s)

data NotDeadlockable {S : Set} : Deadlockable S → Set where
  next
    : (s : S)
    → NotDeadlockable (next s)

data AllMagma {A : Set} (F : A → Set) : Magma A → Set where
  atom
    : ∀ {a}
    → F a
    → AllMagma F (atom a)
  concat
    : ∀ {m1 m2}
    → AllMagma F m1
    → AllMagma F m2
    → AllMagma F (concat m1 m2)

PossibleAtomicStepsAreNotDeadlockable
  : ∀ {S A}
  → PossibleAtomicSteps S A
  → Set
PossibleAtomicStepsAreNotDeadlockable {S} {A} possibleAtomicSteps
  = ∀ s → FiniteButNotDeadlockable (possibleAtomicSteps s)

data AllTree
       {S : Set}
       {FS : Set}
       (PredS : S → Set)
       (PredFS : FS → Set)
       : Tree S FS
       → Set where
  mkAllTree
    : ∀ {stepFun fs0}
    → ((s : S) → PredS s → AllMagma PredFS (stepFun s))
    → PredFS fs0
    → AllTree PredS PredFS (mkTree stepFun fs0)


---------------------------------------
-- Modelling the Dining Philosophers --
---------------------------------------

data PhilosopherState : Set where
  thinking
    : ℕ
    → PhilosopherState
  eating
    : ℕ
    → PhilosopherState
  grabbed-one-fork
    : PhilosopherState

data ForkState : Set where
  locked
    : ForkState
  unlocked
    : ForkState

PhilosopherStates : Set
PhilosopherStates = Vec PhilosopherState 5

ForkStates : Set
ForkStates = Vec ForkState 5

OverallState : Set
OverallState = PhilosopherStates × ForkStates

record Philosopher : Set where
  constructor mkPhilosopher
  field
    index
      : Fin 5

record Fork : Set where
  constructor mkFork
  field
    index
      : Fin 5

-- 5 philosophers and 5 forks, arranged in a circle.
--
--       P4 F0 P0
--     F4        F1
--    P3          P1
--       F3    F2
--          P2
--
-- Each philosopher grabs the fork with the lower index first.
philosopherForks
  : Philosopher
  → Fork × Fork
philosopherForks (mkPhilosopher zero)
  = mkFork zero
  , mkFork (suc (suc (suc (suc zero))))
philosopherForks (mkPhilosopher (suc zero))
  = mkFork zero
  , mkFork (suc zero)
philosopherForks (mkPhilosopher (suc (suc zero)))
  = mkFork (suc zero)
  , mkFork (suc (suc zero))
philosopherForks (mkPhilosopher (suc (suc (suc zero))))
  = mkFork (suc (suc zero))
  , mkFork (suc (suc (suc zero)))
philosopherForks (mkPhilosopher (suc (suc (suc (suc zero)))))
  = mkFork (suc (suc (suc zero)))
  , mkFork (suc (suc (suc (suc zero))))

firstFork
  : Philosopher
  → Fork
firstFork p
  = proj₁ (philosopherForks p)

secondFork
  : Philosopher
  → Fork
secondFork p
  = proj₂ (philosopherForks p)

canGrabFirstFork
  : ForkStates
  → Philosopher
  → Bool
canGrabFirstFork forks p
  with (lookup forks (Fork.index (firstFork p)))
... | locked
  = false
... | unlocked
  = true

canGrabSecondFork
  : ForkStates
  → Philosopher
  → Bool
canGrabSecondFork forks p
  with (lookup forks (Fork.index (secondFork p)))
... | locked
  = false
... | unlocked
  = true

philosopherNextAtomicStep
  : ForkStates
  → Philosopher
  → PhilosopherState
  → Blockable PhilosopherState
philosopherNextAtomicStep forks p (thinking (suc n))
  = next (thinking n)
philosopherNextAtomicStep forks p (thinking zero)
  with canGrabFirstFork forks p
... | false
  = blocked
... | true
  = next grabbed-one-fork
philosopherNextAtomicStep forks p grabbed-one-fork
  with canGrabSecondFork forks p
... | false
  = blocked
... | true
  = -- TODO: sleep for a RANDOM number of time steps
    next (eating (suc (suc (suc (suc (suc zero))))))
philosopherNextAtomicStep forks p (eating (suc n))
  = next (eating n)
philosopherNextAtomicStep forks p (eating zero)
  = -- TODO: think for a RANDOM number of time steps
    next (thinking (suc (suc (suc (suc (suc zero))))))