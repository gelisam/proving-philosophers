open import Data.Fin using (Fin; zero; fromℕ; _<_)
open import Data.Nat using (ℕ; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)

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

eventuallySoonerOrLater
  : ∀ {P Q s}
  → Eventually (λ s → P s ⊎ Q s) s
  → P LeadsTo Q
  → Eventually Q s
eventuallySoonerOrLater {P} {Q} eventuallyPOrQ pLeadsToQ
  = eventuallyThen eventuallyPOrQ pOrQLeadsToQ
  where
    pOrQLeadsToQ : (λ s → P s ⊎ Q s) LeadsTo Q
    pOrQLeadsToQ s (inj₁ ps) = pLeadsToQ s ps
    pOrQLeadsToQ s (inj₂ qs) = now qs

leadsToSoonerOrLater
  : ∀ {P Q R}
  → P LeadsTo (λ s → Q s ⊎ R s)
  → Q LeadsTo R
  → P LeadsTo R
leadsToSoonerOrLater pLeadsToQOrR qLeadsToR s ps
  = eventuallySoonerOrLater (pLeadsToQOrR s ps) qLeadsToR

leadsToALaterStep
  : (n : ℕ)
  → (P : Fin (suc n) → State → Set)
  → (∀ j → (P j) LeadsTo (λ s → ∃ λ i → i < j × P i s))
  → (P zero) LeadsTo (P (fromℕ n))
leadsToALaterStep = _