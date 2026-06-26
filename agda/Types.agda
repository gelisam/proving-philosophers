module Types where

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

data Deadlockable (S : Set) : Set where
  deadlocked
    : Deadlockable S
  next
    : S
    → Deadlockable S

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
