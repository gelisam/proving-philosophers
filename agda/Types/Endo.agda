module Types.Endo where

open import Data.List using (List; []; _∷_)

open import Types.Magma using (Magma; atom; concat)

composeList
  : ∀ {A : Set}
  → List (A → A)
  → A → A
composeList [] x
  = x
composeList (f ∷ fs) x
  = composeList fs (f x)

composeMagma
  : ∀ {A : Set}
  → Magma (A → A)
  → A → A
composeMagma (atom f) x
  = f x
composeMagma (concat m1 m2) x
  = composeMagma m2 (composeMagma m1 x)