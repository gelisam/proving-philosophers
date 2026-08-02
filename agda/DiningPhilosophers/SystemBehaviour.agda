module DiningPhilosophers.SystemBehaviour where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; map)
open import Data.Vec using (Vec; lookup; _[_]≔_)

import ExecutionModel using (Tree)
open import DiningPhilosophers.SystemState using
  ( PhilosopherState;
      ready-to-eat;
      ready-for-eating-time-step;
      done-with-eating-time-step;
      ready-to-think;
      ready-for-thinking-time-step;
      done-with-thinking-time-step;
      ready-to-grab-first-fork;
      ready-to-grab-second-fork;
    ForkState;
      locked;
      unlocked;
    SystemState;
      mkSystemState;
    Philosopher;
      mkPhilosopher;
      allPhilosophers;
      getPhilosopherState;
      setPhilosopherState;
    Fork;
      mkFork;
      allForks;
      getForkState;
      setForkState;
    firstFork;
      getFirstForkState;
      setFirstForkState;
    secondFork;
      getSecondForkState;
      setSecondForkState)
import TimeStep using (Next; choice; ready-for-next-time-step; blocked; mconcatNexts; timeStepsToTree)
open import Types.Endo using (composeList; composeMagma)
open import Types.Magma using (Magma; atom; concat; mapMagma)

open ExecutionModel SystemState
open TimeStep SystemState


-- Eat for n+1 seconds
setToSpecificEating
  : Philosopher
  → SystemState
  → ℕ
  → SystemState
setToSpecificEating p ss seconds
  = setPhilosopherState
      p
      (ready-for-eating-time-step seconds)
      ss

-- Think for n+1 seconds
setToSpecificThinking
  : Philosopher
  → SystemState
  → ℕ
  → SystemState
setToSpecificThinking p ss seconds
  = setPhilosopherState
      p
      (ready-for-thinking-time-step seconds)
      ss

magma0to9
  : Magma ℕ
magma0to9
  = composeList
      ( concat (atom 0)
      ∷ concat (atom 1)
      ∷ concat (atom 2)
      ∷ concat (atom 3)
      ∷ concat (atom 4)
      ∷ concat (atom 5)
      ∷ concat (atom 6)
      ∷ concat (atom 7)
      ∷ concat (atom 8)
      ∷ []
      )
      (atom 9)

-- Eat for 1 to 10 seconds
setToRandomEating
  : Philosopher
  → SystemState
  → Magma SystemState
setToRandomEating p ss
  = mapMagma (setToSpecificEating p ss) magma0to9

-- Think for 1 to 10 seconds
setToRandomThinking
  : Philosopher
  → SystemState
  → Magma SystemState
setToRandomThinking p ss
  = mapMagma (setToSpecificThinking p ss) magma0to9

grabFirstForkIfPossible
  : Philosopher
  → SystemState
  → Next
grabFirstForkIfPossible p ss with getFirstForkState p ss
... | unlocked
  = choice
      (atom
         (composeList
            ( setPhilosopherState
                p
                ready-to-grab-second-fork
            ∷ setFirstForkState
                p
                locked
            ∷ []
            )
            ss))
... | locked
  = blocked

grabSecondForkIfPossible
  : Philosopher
  → SystemState
  → Next
grabSecondForkIfPossible p ss with getSecondForkState p ss
... | unlocked
  = choice
      (atom
         (composeList
            ( setPhilosopherState
                p
                ready-to-eat
            ∷ setSecondForkState
                p
                locked
            ∷ []
            )
            ss))
... | locked
  = blocked

-- Update a single philosopher
philosopherNext
  : Philosopher
  → SystemState
  → Next
philosopherNext p ss with getPhilosopherState p ss
... | ready-to-eat
  = choice (setToRandomEating p ss)
... | ready-for-eating-time-step n
  = choice
      (atom
         (setPhilosopherState
            p
            (done-with-eating-time-step n)
            ss))
... | done-with-eating-time-step n
  = ready-for-next-time-step
... | ready-to-think
  = choice (setToRandomThinking p ss)
... | ready-for-thinking-time-step n
  = choice
      (atom
         (setPhilosopherState
            p
            (done-with-thinking-time-step n)
            ss))
... | done-with-thinking-time-step n
  = ready-for-next-time-step
... | ready-to-grab-first-fork
  = grabFirstForkIfPossible p ss
... | ready-to-grab-second-fork
  = grabSecondForkIfPossible p ss

philosopherBetweenTimeSteps
  : Philosopher
  → SystemState
  → SystemState
philosopherBetweenTimeSteps p ss with getPhilosopherState p ss
... | done-with-eating-time-step (suc n)
  = setPhilosopherState
      p
      (ready-for-eating-time-step n)
      ss
... | done-with-eating-time-step zero
  = composeList
      ( setPhilosopherState
          p
          ready-to-think
      ∷ setSecondForkState
          p
          unlocked
      ∷ setFirstForkState
          p
          unlocked
      ∷ []
      )
      ss
... | done-with-thinking-time-step (suc n)
  = setPhilosopherState
      p
      (ready-for-thinking-time-step n)
      ss
... | done-with-thinking-time-step zero
  = setPhilosopherState
      p
      ready-to-grab-first-fork
      ss
... | _
  = -- no changes, either because the philosopher is stuck (e.g. in the case of
    -- ready-to-grab-first-fork), or because this is a state meant for the
    -- within-time-step function rather than this between-time-steps function
    -- (e.g. ready-to-eat), a situation we did not bother to rule out using the
    -- type system.
    ss

systemNext
  : SystemState
  → Next
systemNext ss
  = mconcatNexts
      (mapMagma
         (λ p → philosopherNext p ss)
         allPhilosophers)

systemBetweenTimeSteps
  : SystemState
  → SystemState
systemBetweenTimeSteps
  = composeMagma
      (mapMagma
         philosopherBetweenTimeSteps
         allPhilosophers)

systemTree
  : SystemState
  → Tree
systemTree
  = timeStepsToTree
      systemNext
      systemBetweenTimeSteps