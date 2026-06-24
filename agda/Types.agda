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

timeStep
  : ∀ {S A}
  → PossibleAtomicSteps S A
  → S
  → FiniteDeadlockablePossibilityTree S A
timeStep = _

lifecycle
  : ∀ {S A}
  → PossibleAtomicSteps S A
  → (advanceTime : A → S)
  → InfiniteDeadlockablePossibilityTree S
lifecycle = _

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
