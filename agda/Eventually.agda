open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<′_; <′-base; <′-step; ≤′-reflexive; ≤′-refl; ≤′-step)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

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

alreadyHere
  : ∀ {P}
  → P LeadsTo P
alreadyHere s ps
  = now ps

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

ltThanOneIsZero
  : ∀ {i}
  → i <′ 1
  → i ≡ 0
ltThanOneIsZero {.zero} ≤′-refl
  = refl
ltThanOneIsZero {i} (≤′-step (≤′-reflexive ()))
  -- impossible case

module _
  (P : ℕ → State → Set)
  where
    -- BEGIN machinery for implementing 'leadsToLastStep'

    -- "Later" step means a smaller number, as we count downwards to zero in
    -- order to make termination-checking easier.
    LaterThan : ℕ → State → Set
    LaterThan j s
      = ∃ λ i
      → i <′ j
      × P i s

    laterThanOneToLast
      : ∀ {s}
      → LaterThan 1 s
      → P 0 s
    laterThanOneToLast {s} (i , (i≤1 , pi))
      = subst (λ i → P i s) (ltThanOneIsZero i≤1) pi

    laterThanOneLeadsToLast
      : (LaterThan 1) LeadsTo (P 0)
    laterThanOneLeadsToLast s laterThan1
      = now (laterThanOneToLast laterThan1)

    ThisOrLater : ℕ → State → Set
    ThisOrLater j s
      = P j s
      ⊎ LaterThan j s

    laterThanSucToNextOrLater
      : ∀ {j s}
      → LaterThan (suc j) s
      → ThisOrLater j s
    laterThanSucToNextOrLater {j} {s} (.j , (<′-base , pj))
      = inj₁ pj
    laterThanSucToNextOrLater {j} {s} (i , (<′-step i<′j , pi))
      = inj₂ (i , (i<′j , pi))

    laterThanSucLeadsToNextOrLater
      : ∀ j
      → LaterThan (suc j) LeadsTo (ThisOrLater j)
    laterThanSucLeadsToNextOrLater j s laterThanSuc
      = now (laterThanSucToNextOrLater laterThanSuc)

    module _
      (leadsToLaterStep : ∀ j → (P j) LeadsTo (LaterThan j))
      where
        laterThanSucLeadsToLater
          : ∀ j
          → LaterThan (suc j) LeadsTo LaterThan j
        laterThanSucLeadsToLater j
          = leadsToSoonerOrLater
              -- LaterThan (suc j) LeadsTo P j or LaterThan j
              (laterThanSucLeadsToNextOrLater j)
              -- P j LeadsTo LaterThan j
              (leadsToLaterStep j)

        laterThanSucLeadsToLastStep
          : ∀ j
          → LaterThan (suc j) LeadsTo (P 0)
        laterThanSucLeadsToLastStep zero
          = -- LaterThan (suc zero) LeadsTo P 0
            laterThanOneLeadsToLast
        laterThanSucLeadsToLastStep (suc j)
          = leadsToThen
              -- LaterThan (suc (suc j)) LeadsTo LaterThan (suc j)
              (laterThanSucLeadsToLater (suc j))
              -- LaterThan (suc j) LeadsTo P 0
              (laterThanSucLeadsToLastStep j)

        -- END machinery for implementing 'leadsToLastStep'

        -- A generalization of 'leadsToSoonerOrLater' with more than two steps.
        leadsToLastStep
          : ∀ j
          → (P j) LeadsTo (P 0)
        leadsToLastStep zero
          = alreadyHere
        leadsToLastStep (suc j)
          = leadsToThen
              -- P (suc j) LeadsTo LaterThan (suc j)
              (leadsToLaterStep (suc j))
              -- LaterThan (suc j) LeadsTo P 0
              (laterThanSucLeadsToLastStep j)
