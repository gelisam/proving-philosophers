module DiningPhilosophers.SystemState where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)

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