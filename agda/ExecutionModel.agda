module ExecutionModel where

open import Types.Magma using (Magma; concat)

-- What to do next, either for a given philosopher or for the system as a whole.
data Next (State : Set) : Set where
  -- The next state is to be non-deterministically chosen from a set of possible
  -- next states. Then continue within the same time step.
  choice
    : Magma State
    → Next State
  -- At least one action was performed during this time step, and we are ready
  -- to move on to the next one.
  ready-for-next-time-step
    : Next State
  -- Nothing happened during this time step. If nothing changes, the system is
  -- deadlocked.
  blocked
    : Next State

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
  : ∀ {State}
  → Next State
  → Next State
  → Next State
choice m1 <> choice m2
  = choice (concat m1 m2)
choice m <> _
  = choice m
_ <> choice m
  = choice m
ready-for-next-time-step <> _
  = ready-for-next-time-step
_ <> ready-for-next-time-step
  = ready-for-next-time-step
blocked <> blocked
  = blocked