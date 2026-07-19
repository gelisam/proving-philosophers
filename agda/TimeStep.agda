-- IdleState is the subset of State from which no actions can be performed.
module TimeStep (State : Set) (Idle : State → Set) where

open import Types.Magma using (Magma; atom; concat; mapMagma)
import ExecutionModel using (Deadlockable; deadlocked; live; Tree; MkTree; StepFun)

open ExecutionModel State

-- What to do next, either for a given philosopher or for the system as a whole.
data Next (s : State) : Set where
  -- The next state is to be non-deterministically chosen from a set of possible
  -- next states. Then continue within the same time step.
  choice
    : Magma State
    → Next s
  -- At least one action was performed during this time step, and we are ready
  -- to move on to the next one.
  ready-for-next-time-step
    : Idle s
    → Next s
  -- Nothing happened during this time step. If nothing changes, the system is
  -- deadlocked.
  blocked
    : Idle s
    → Next s

-- Combine what multiple philosophers want to do next into a single next state
-- for the system as a whole.
--
-- 'choice' takes precedence over 'ready-for-next-time-step', because if any
-- philosopher has remaining actions to perform this turn, we must allow them to
-- do so before moving on to the next time step.
--
-- 'ready-for-next-time-step' takes precedence over 'blocked', because if any
-- philosopher is able to perform more actions in the next time step, then the
-- system is not deadlocked yet. It might still be livelocked, which is why we
-- have to prove that every philosopher eats infinitely often, it does not
-- suffice to prove that the system never deadlocks.
_<>_
  : ∀ {s}
  → Next s
  → Next s
  → Next s
choice m1 <> choice m2
  = choice (concat m1 m2)
choice m <> _
  = choice m
_ <> choice m
  = choice m
ready-for-next-time-step p1 <> _
  = -- if _ also contains an (Idle s), it doesn't matter which proof we keep
    ready-for-next-time-step p1
_ <> ready-for-next-time-step p2
  = ready-for-next-time-step p2
blocked p1 <> blocked _p2
  = -- it doesn't matter which proof we keep
    blocked p1

-- We chain together a number of atomic within-time-step actions until the
-- system is ready to move on to the next time step, then we perform the
-- between-time-steps cleanup action, and continue with the next time step.
-- The result is a tree of all possible interleavings of actions.
--
-- Note that the tree is defined as an infinite number of calls to StepFun,
-- where each such "step" is either an atomic within-time-step action or a
-- between-time-steps cleanup action.
timeStepsToStepFun
  : (∀ s → Next s)
  → (∀ s → Idle s → State)
  → StepFun
timeStepsToStepFun withinTimeStep betweenTimeSteps s0
  with withinTimeStep s0
... | choice m
  = mapMagma live m
... | ready-for-next-time-step p
  = atom (live (betweenTimeSteps s0 p))
... | blocked p
  = atom deadlocked

timeStepsToTree
  : (∀ s → Next s)
  → (∀ s → Idle s → State)
  → State → Tree
timeStepsToTree withinTimeStep betweenTimeSteps
  = MkTree (timeStepsToStepFun withinTimeStep betweenTimeSteps)
