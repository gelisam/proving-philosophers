{-# OPTIONS --guardedness #-}
module TrustedBase.RuntimeModel where

open import Data.List.Base using (List)
open import Data.Maybe using (Maybe)
open import Data.Vec using (Vec)
open import Codata.Musical.Notation using (♯_; ∞)
open import Codata.Musical.Colist using (Colist; _∷_)

open import TrustedBase.Fork using (Fork)
open import TrustedBase.Stmt using (Stmt)

-- Represents the condition a thread is waiting for
data WaitingCondition : Set where
  ForkAvailable : Fork → WaitingCondition
  SleepElapsed : WaitingCondition

-- Represents the runtime state of a single thread
record ThreadState : Set where
  field
    acquiredForks : List Fork
    waiting : Maybe WaitingCondition
    restOfLoop : List Stmt

-- Represents the runtime state of n threads
ProgramState : ∀ {n} → Set
ProgramState {n} = Vec ThreadState n

-- An infinite tree structure for possible execution traces
-- Using Colist (coinductive list) to represent the infinite tree
data Tree (A : Set) : Set where
  Node : A → Colist (∞ (Tree A)) → Tree A

-- Represents all possible execution traces as an infinite tree
PossibleTraces : ∀ {n} → Set
PossibleTraces {n} = Tree (ProgramState {n})
