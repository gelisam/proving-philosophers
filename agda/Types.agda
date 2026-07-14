module Types where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; lookup; _[_]≔_)

open import Types.Magma using (Magma; atom; concat; mapMagma; AllMagma)

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

-- Above is generic, below is specific to the dining philosophers problem.

data PhilosopherState : Set where
  ready-to-think
    : PhilosopherState
  ready-for-thinking-time-step
    : ℕ
    → PhilosopherState
  done-with-thinking-time-step
    : ℕ
    → PhilosopherState
  ready-to-grab-first-fork
    : PhilosopherState
  ready-to-grab-second-fork
    : PhilosopherState
  ready-to-eat
    : PhilosopherState
  ready-for-eating-time-step
    : ℕ
    → PhilosopherState
  done-with-eating-time-step
    : ℕ
    → PhilosopherState

data ForkState : Set where
  locked
    : ForkState
  unlocked
    : ForkState

record SystemState : Set where
  constructor mkSystemState
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

magma1to10
  : Magma ℕ
magma1to10
  = concat (atom 1)
  ( concat (atom 2)
  ( concat (atom 3)
  ( concat (atom 4)
  ( concat (atom 5)
  ( concat (atom 6)
  ( concat (atom 7)
  ( concat (atom 8)
  ( concat (atom 9)
           (atom 10)))))))))

singlePhilosopherNext
  : PhilosopherState
  → Next PhilosopherState
singlePhilosopherNext ready-to-think
  = choice (mapMagma ready-for-thinking-time-step magma1to10)
singlePhilosopherNext (ready-for-thinking-time-step n)
  = choice (atom (done-with-thinking-time-step n))
singlePhilosopherNext (done-with-thinking-time-step n)
  = ready-for-next-time-step
singlePhilosopherNext ready-to-grab-first-fork
  = -- TODO: check if fork is available
    choice (atom ready-to-grab-second-fork)
singlePhilosopherNext ready-to-grab-second-fork
  = -- TODO: check if fork is available
    choice (atom ready-to-eat)
singlePhilosopherNext ready-to-eat
  = choice (mapMagma ready-for-eating-time-step magma1to10)
singlePhilosopherNext (ready-for-eating-time-step n)
  = choice (atom (done-with-eating-time-step n))
singlePhilosopherNext (done-with-eating-time-step n)
  = ready-for-next-time-step
