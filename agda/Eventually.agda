open import Data.Sum using (_⊎_; inj₁; inj₂)

import ExecutionModel using (Deadlockable; live; StepFun; Tree)
open import Types.Magma using (Magma; atom; concat)

module Eventually (State : Set) (stepFun : ExecutionModel.StepFun State) where

open ExecutionModel State

data AllMagmaDeadlockable (P : State → Set) : Magma Deadlockable → Set where
  atom
    : ∀ {s}
    → P s
    → AllMagmaDeadlockable P (atom (live s))
  concat
    : ∀ {m1 m2}
    → AllMagmaDeadlockable P m1
    → AllMagmaDeadlockable P m2
    → AllMagmaDeadlockable P (concat m1 m2)

data Eventually (P : State → Set) (s : State) : Set where
  now
    : P s
    → Eventually P s
  later
    : AllMagmaDeadlockable (Eventually P) (stepFun s)
    → Eventually P s