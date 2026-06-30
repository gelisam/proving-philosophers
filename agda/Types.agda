module Types where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; lookup; _[_]≔_)


----------------------------------------------
-- datatypes for representing the evolution --
-- of non-deterministic systems             --
----------------------------------------------

data FinitePausable (S : Set) (A : Set) : Set where
  paused
    : FinitePausable S A
  done
    : A
    → FinitePausable S A
  next
    : S
    → FinitePausable S A

data Finite (S : Set) (A : Set) : Set where
  done
    : A
    → Finite S A
  next
    : S
    → Finite S A

data Pausable (S : Set) : Set where
  -- Could represent that a single philosopher is waiting for a fork,
  -- or that the entire system is deadlocked.
  paused
    : Pausable S
  next
    : S
    → Pausable S

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

InfinitePausablePossibilityTree : Set → Set
InfinitePausablePossibilityTree S
  = Tree S (Pausable S)

FinitePossibilityTree : Set → Set → Set
FinitePossibilityTree S A
  = Tree S (Finite S A)

FinitePausablePossibilityTree : Set → Set → Set
FinitePausablePossibilityTree S A
  = Tree S (FinitePausable S A)


------------------------------------
-- constructing non-deterministic --
-- systems from simpler parts     --
------------------------------------

PossibleAtomicSteps : Set → Set → Set
PossibleAtomicSteps S A = S → FinitePausable (Magma S) A

module timeStepImpl
         {S A}
         (possibleSteps : PossibleAtomicSteps S A)
         where
  mutual
    stepFuns
      : Magma S
      → Magma (FinitePausable S A)
    stepFuns (atom s)
      = atom (next s)
    stepFuns (concat m1 m2)
      = concat (stepFuns m1) (stepFuns m2)

    stepFun
      : S
      → Magma (FinitePausable S A)
    stepFun s with possibleSteps s
    ... | paused
        = atom paused
    ... | done a
        = atom (done a)
    ... | next ss
        = stepFuns ss

timeStep
  : ∀ {S A}
  → PossibleAtomicSteps S A
  → S
  → FinitePausablePossibilityTree S A
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
    : Magma (FinitePausable S A)
    → Magma (Pausable S)
  advanceTimes (atom paused)
    = atom paused
  advanceTimes (atom (done a))
    = atom (next (advanceTime a))
  advanceTimes (atom (next s))
    = atom (next s)
  advanceTimes (concat m1 m2)
    = concat (advanceTimes m1) (advanceTimes m2)

  stepFun
    : S → Magma (Pausable S)
  stepFun s
    = advanceTimes (timeStepImpl.stepFun possibleSteps s)

lifecycle
  : ∀ {S A}
  → PossibleAtomicSteps S A
  → (advanceTime : A → S)
  → S
  → InfinitePausablePossibilityTree S
lifecycle {S} {A} possibleSteps advanceTime s0
  = mkTree
      (lifecycleImpl.stepFun possibleSteps advanceTime)
      (next s0)


-------------------
-- proof objects --
-------------------

data FiniteButNotPaused
       {S : Set}
       {A : Set}
       : FinitePausable S A
       → Set where
  done
    : (a : A)
    → FiniteButNotPaused (done a)
  next
    : (s : S)
    → FiniteButNotPaused (next s)

data NotPaused {S : Set} : Pausable S → Set where
  next
    : (s : S)
    → NotPaused (next s)

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

PossibleAtomicStepsAreNotPaused
  : ∀ {S A}
  → PossibleAtomicSteps S A
  → Set
PossibleAtomicStepsAreNotPaused {S} {A} possibleAtomicSteps
  = ∀ s → FiniteButNotPaused (possibleAtomicSteps s)

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


-------------------------
-- data model for the  --
-- Dining Philosophers --
-------------------------

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

record OverallState : Set where
  constructor mkOverallState
  field
    philosophers
      : Vec PhilosopherState 5
    forks
      : Vec ForkState 5

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

getPhilosopher
  : Philosopher
  → OverallState
  → PhilosopherState
getPhilosopher (mkPhilosopher i) s
  = lookup (OverallState.philosophers s) i

getFork
  : Fork
  → OverallState
  → ForkState
getFork (mkFork i) s
  = lookup (OverallState.forks s) i

setPhilosopher
  : Philosopher
  → PhilosopherState
  → OverallState
  → OverallState
setPhilosopher (mkPhilosopher i) ps' s
  = let pss = OverallState.philosophers s
 in let pss' = pss [ i ]≔ ps'
 in record s { philosophers = pss' }

setFork
  : Fork
  → ForkState
  → OverallState
  → OverallState
setFork (mkFork i) fs' s
  = let fss = OverallState.forks s
 in let fss' = fss [ i ]≔ fs'
 in record s { forks = fss' }

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
  : Philosopher
  → OverallState
  → Bool
canGrabFirstFork p s
  with (getFork (firstFork p) s)
... | locked
  = false
... | unlocked
  = true

canGrabSecondFork
  : Philosopher
  → OverallState
  → Bool
canGrabSecondFork p s
  with (getFork (secondFork p) s)
... | locked
  = false
... | unlocked
  = true


---------------------------------
-- possible execution tree for --
-- the Dining Philosophers     --
---------------------------------

tryGrabFirstFork
  : Philosopher
  → OverallState
  → Pausable OverallState
tryGrabFirstFork p s0 with (canGrabFirstFork p s0)
... | false
  = paused
... | true
  = let s1 = setPhilosopher p grabbed-one-fork s0
 in let s2 = setFork (firstFork p) locked s1
 in next s2

tryGrabSecondFork
  : Philosopher
  → OverallState
  → Pausable OverallState
tryGrabSecondFork p s0 with (canGrabSecondFork p s0)
... | false
  = paused
... | true
  = let n = -- TODO: sleep for a RANDOM number of time steps
            suc (suc (suc (suc (suc zero))))
 in let s1 = setPhilosopher p (thinking n) s0
 in let s2 = setFork (secondFork p) locked s1
 in next s2

releaseForks
  : Philosopher
  → OverallState
  → OverallState
releaseForks p s0
  = let n = -- TODO: think for a RANDOM number of time steps
            suc (suc (suc (suc (suc zero))))
 in let s1 = setPhilosopher p (thinking n) s0
 in let s2 = setFork (firstFork p) unlocked s1
 in let s3 = setFork (secondFork p) unlocked s2
 in s3

philosopherNextAtomicStep
  : Philosopher
  → OverallState
  → Pausable OverallState
philosopherNextAtomicStep p s with (getPhilosopher p s)
... | thinking (suc n)
  = next (setPhilosopher p (thinking n) s)
... | thinking zero
  = -- grabbed-one-fork
    tryGrabFirstFork p s
... | grabbed-one-fork
  = -- eating 5
    tryGrabSecondFork p s
... | eating (suc n)
  = next (setPhilosopher p (eating n) s)
... | eating zero
  = -- thinking 5
    next (releaseForks p s)

