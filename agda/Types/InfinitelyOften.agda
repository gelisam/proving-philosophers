{-# OPTIONS --guardedness #-}

open import Types.Tree using (StepFun)
import Types.AllPaths using (AllPaths)
import Types.AllSubtrees using (AllSubtrees; AllSubtrees-map)

module Types.InfinitelyOften {A : Set} (f : StepFun A) where

open Types.AllPaths f
open Types.AllSubtrees f

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
  → (a : A)
  → AllSubtrees P a
  → InfinitelyOften Q a
infinitelyOften p2q a allSubtrees
  = AllSubtrees-map p2q a allSubtrees