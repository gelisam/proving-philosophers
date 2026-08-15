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

_LeadsTo_
  : (State → Set)
  → (State → Set)
  → Set
P LeadsTo Q
  = ∀ s → P s → Eventually Q s

mutual
  eventuallyThen
    : ∀ {P Q s}
    → Eventually P s
    → P LeadsTo Q
    → Eventually Q s
  eventuallyThen {s = s} (now ps) pLeadsToQ
    = pLeadsToQ s ps
  eventuallyThen (later allEventuallyP) pLeadsToQ
    = later
        (allEventuallyThen allEventuallyP pLeadsToQ)

  allEventuallyThen
    : ∀ {P Q m}
    → AllMagmaDeadlockable (Eventually P) m
    → P LeadsTo Q
    → AllMagmaDeadlockable (Eventually Q) m
  allEventuallyThen (atom eventuallyP) pLeadsToQ
    = atom
        (eventuallyThen eventuallyP pLeadsToQ)
  allEventuallyThen (concat all1 all2) pLeadsToQ
    = concat
        (allEventuallyThen all1 pLeadsToQ)
        (allEventuallyThen all2 pLeadsToQ)

leadsToThen
  : ∀ {P Q R}
  → P LeadsTo Q
  → Q LeadsTo R
  → P LeadsTo R
leadsToThen pLeadsToQ qLeadsToR s ps
  = eventuallyThen (pLeadsToQ s ps) qLeadsToR