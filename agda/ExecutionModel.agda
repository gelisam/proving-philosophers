module ExecutionModel (State : Set) where

open import Types.Magma using (Magma; AllMagma)

data Deadlockable : Set where
  deadlocked
    : Deadlockable
  live
    : State
    → Deadlockable

-- We want to represent every possible interleaving of the threads in the dining
-- philosophers problem. An infinite rose tree [1] with branching paths at each
-- decision point seems appropriate:
--
-- > record Tree : Set where
-- >   coinductive
-- >   field
-- >     value
-- >       : State
-- >     children
-- >       : List Tree
--
-- However, when proving properties about those interleavings, the fact that the
-- future decision points are entirely determined by the current state is
-- important. To reflect this, we use an alternate representation inspired by
-- the Nu fixed point [2].
--
-- Also, we use Magma instead of List because this reduces the number of lemmas
-- about normalizing lists, and because we want to represent the case in which
-- there are no possible next states specially: this is a deadlock.
--
-- [1] https://hackage-content.haskell.org/package/containers-0.8/docs/Data-Tree.html#t:Tree
-- [2] https://hackage.haskell.org/package/data-fix-0.3.4/docs/Data-Fix.html#t:Nu
data Tree : Set where
  MkTree : (State → Magma Deadlockable) → State → Tree

StepFun : Set
StepFun = State → Magma Deadlockable

state : Tree → State
state (MkTree _ s) = s

stepFun : Tree → StepFun
stepFun (MkTree f _) = f

childStates : Tree → Magma Deadlockable
childStates (MkTree f s) = f s

data LiveDeadlockable : Deadlockable → Set where
  live
    : ∀ s
    → LiveDeadlockable (live s)

LiveMagmaDeadlockable : Magma Deadlockable → Set
LiveMagmaDeadlockable
  = AllMagma LiveDeadlockable

LiveStepFun : StepFun → Set
LiveStepFun f
  = ∀ s
  → LiveMagmaDeadlockable (f s)

LiveTree : Tree → Set
LiveTree (MkTree f _s)
  = LiveStepFun f