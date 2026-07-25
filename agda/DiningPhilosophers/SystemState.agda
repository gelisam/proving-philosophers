module DiningPhilosophers.SystemState where

open import Data.Fin using (Fin; zero; suc; #_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; lookup; _[_]≔_)

open import Types.Magma using (Magma; atom; concat)

data PhilosopherState : Set where
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

allPhilosophers
  : Magma Philosopher
allPhilosophers
  = concat (atom (mkPhilosopher (# 0)))
  ( concat (atom (mkPhilosopher (# 1)))
  ( concat (atom (mkPhilosopher (# 2)))
  ( concat (atom (mkPhilosopher (# 3)))
           (atom (mkPhilosopher (# 4))))))

record Fork : Set where
  constructor mkFork
  field
    index
      : Fin 5

allForks
  : Magma Fork
allForks
  = concat (atom (mkFork (# 0)))
  ( concat (atom (mkFork (# 1)))
  ( concat (atom (mkFork (# 2)))
  ( concat (atom (mkFork (# 3)))
           (atom (mkFork (# 4))))))

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

firstAndSecondFork
  : Philosopher
  → Fork × Fork
firstAndSecondFork (mkPhilosopher zero)
  = mkFork (# 0) , mkFork (# 4)
firstAndSecondFork (mkPhilosopher (suc zero))
  = mkFork (# 0) , mkFork (# 1)
firstAndSecondFork (mkPhilosopher (suc (suc zero)))
  = mkFork (# 1) , mkFork (# 2)
firstAndSecondFork (mkPhilosopher (suc (suc (suc zero))))
  = mkFork (# 2) , mkFork (# 3)
firstAndSecondFork (mkPhilosopher (suc (suc (suc (suc zero)))))
  = mkFork (# 3) , mkFork (# 4)

firstFork
  : Philosopher
  → Fork
firstFork p
  = proj₁ (firstAndSecondFork p)

secondFork
  : Philosopher
  → Fork
secondFork p
  = proj₂ (firstAndSecondFork p)

getFirstForkState
  : Philosopher
  → SystemState
  → ForkState
getFirstForkState p
  = getForkState (firstFork p)

getSecondForkState
  : Philosopher
  → SystemState
  → ForkState
getSecondForkState p
  = getForkState (secondFork p)

setFirstForkState
  : Philosopher
  → ForkState
  → SystemState
  → SystemState
setFirstForkState p forkState
  = setForkState (firstFork p) forkState

setSecondForkState
  : Philosopher
  → ForkState
  → SystemState
  → SystemState
setSecondForkState p forkState
  = setForkState (secondFork p) forkState