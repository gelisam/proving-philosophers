{-# OPTIONS --guardedness #-}

open import Tree using (StepFun)
import AllPaths using (AllPaths)
import AllSubtrees using (AllSubtrees; AllSubtrees-map)

module InfinitelyOften {A : Set} (f : StepFun A) where

open AllPaths f
open AllSubtrees f

-- P is true infinitely often: that is, starting from any node (AllSubtrees),
-- all paths reach a node satisfying P after a finite number of steps
-- (AllPaths).
InfinitelyOften
  : (P : A → Set)
  → A
  → Set
InfinitelyOften P a
  = AllSubtrees (AllPaths P) a