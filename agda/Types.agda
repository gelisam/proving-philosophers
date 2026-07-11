module Types where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; lookup; _[_]≔_)

open import Types.Magma using (Magma; atom; concat; AllMagma)

data PhilosopherState : Set where
  beginning-of-eating-time-step
    : ℕ
    → PhilosopherState
  end-of-eating-time-step
    : ℕ
    → PhilosopherState
  beginning-of-thinking-time-step
    : ℕ
    → PhilosopherState
  end-of-thinking-time-step
    : ℕ
    → PhilosopherState
  grabbed-one-fork
    : PhilosopherState

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


data Next (State : Set) : Set where
  choice
    : Magma State
    → Next State
  ready
    : Next State
  blocked
    : Next State

-- 'choice' takes precedence over ready, because if any philosopher has
-- remaining actions to perform this turn, we must allow them to do so before
-- moving on to the next time step.
--
-- 'ready' takes precedence over 'blocked', because if any philosopher is able
-- to perform more actions in the next time step, then the system is not
-- deadlocked yet. It might still be livelocked, which is why we have to prove
-- that every philosopher eats infinitely often, it does not suffice to prove
-- that the system never deadlocks.
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
ready <> _
  = ready
_ <> ready
  = ready
blocked <> blocked
  = blocked
