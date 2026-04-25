{-# OPTIONS --guardedness #-}

open import Types.Tree using (StepFun)
import Types.Proof.AllPaths using (AllPaths)
import Types.Proof.AllSubtrees using (AllSubtrees; AllSubtrees-map)

module Types.Proof.InfinitelyOften {A : Set} (f : StepFun A) where

open Types.Proof.AllPaths f
open Types.Proof.AllSubtrees f

-- P is true infinitely often: that is, starting from any node (AllSubtrees),
-- all paths reach a node satisfying P after a finite number of steps
-- (AllPaths).
InfinitelyOften
  : (P : A → Set)
  → A
  → Set
InfinitelyOften P a
  = AllSubtrees (AllPaths P) a

infinitelyOften
  : {P Q : A → Set}
  → ((x : A) → P x → AllPaths Q x)
  → (x : A)
  → AllSubtrees P x
  → InfinitelyOften Q x
infinitelyOften p2q x allSubtrees
  = AllSubtrees-map p2q x allSubtrees