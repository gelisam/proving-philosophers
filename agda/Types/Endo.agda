module Types.Endo where

open import Data.List using (List; []; _∷_)

compose
  : ∀ {A : Set}
  → List (A → A)
  → A → A
compose [] x
  = x
compose (f ∷ fs) x
  = compose fs (f x)