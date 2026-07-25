module DiningPhilosophers.SystemState where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; lookup; _[_]≔_)
open import Data.Vec.Relation.Unary.All using (All)

data PhilosopherState : Set where
  ready-to-think
    : PhilosopherState
  ready-for-thinking-time-step
    : ℕ  -- thinking steps _after_ this step, so 0 means
         -- think for one time step, this one.
    → PhilosopherState
  done-with-thinking-time-step
    : ℕ  -- thinking steps _after_ this step, so 0 means
         -- we are done thinking altogether.
    → PhilosopherState
  ready-to-grab-first-fork
    : PhilosopherState
  ready-to-grab-second-fork
    : PhilosopherState
  ready-to-eat
    : PhilosopherState
  ready-for-eating-time-step
    : ℕ  -- eating steps _after_ this step, so 0 means
         -- eat for one time step, this one.
    → PhilosopherState
  done-with-eating-time-step
    : ℕ  -- eating steps _after_ this step, so 0 means
         -- we are done eating altogether.
    → PhilosopherState

data IdlePhilosopher : PhilosopherState → Set where
  done-with-thinking-time-step
    : ∀ {n}
    → IdlePhilosopher (done-with-thinking-time-step n)
  blocked-from-grabbing-first-fork
    : IdlePhilosopher ready-to-grab-first-fork
  blocked-from-grabbing-second-fork
    : IdlePhilosopher ready-to-grab-second-fork
  done-with-eating-time-step
    : ∀ {n}
    → IdlePhilosopher (done-with-eating-time-step n)

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

data IdleSystemState : SystemState → Set where
  mkIdleSystemState
    : ∀ {philosophers forks}
    → All IdlePhilosopher philosophers
    → IdleSystemState (mkSystemState philosophers forks)

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

getPhilosopherState
  : Philosopher
  → SystemState
  → PhilosopherState
getPhilosopherState p (mkSystemState philosophers _)
  = lookup philosophers (Philosopher.index p)

setPhilosopherState
  : Philosopher
  → PhilosopherState
  → SystemState
  → SystemState
setPhilosopherState p ps' (mkSystemState philosophers forks)
  = mkSystemState
      (philosophers [ Philosopher.index p ]≔ ps')
      forks

getForkState
  : Fork
  → SystemState
  → ForkState
getForkState f (mkSystemState _ forks)
  = lookup forks (Fork.index f)

setForkState
  : Fork
  → ForkState
  → SystemState
  → SystemState
setForkState f fs' (mkSystemState philosophers forks)
  = mkSystemState
      philosophers
      (forks [ Fork.index f ]≔ fs')