{-# OPTIONS --guardedness #-}
module TrustedBase.RuntimeModel where

open import Data.List.Base using (List)
open import Data.Maybe.Base using (Maybe)
open import Data.Vec using (Vec)

open import TrustedBase.Fork using (Fork)
open import TrustedBase.Stmt using (Stmt)

-- Represents what condition a thread is waiting for
data WaitingCondition : Set where
  ForkAvailable : Fork → WaitingCondition
  SleepElapsed : WaitingCondition

-- Represents the state of a single thread
record ThreadState : Set where
  field
    acquiredForks : List Fork
    waiting : Maybe WaitingCondition
    restOfLoop : List Stmt

-- Represents the state of the entire program with n threads
ProgramState : (n : _) → Set
ProgramState n = Vec ThreadState n

-- Tree representing all possible execution traces (infinite tree)
-- Using coinductive record to represent infinite branching
record Tree (A : Set) : Set where
  coinductive
  field
    value : A
    children : List (Tree A)

-- Represents all possible traces of program execution
PossibleTraces : (n : _) → Set
PossibleTraces n = Tree (ProgramState n)
