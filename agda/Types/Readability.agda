module Types.Readability where

starting-at_knowing_apply
  : {A : Set} {P : A → Set} {R : (x : A) → P x → Set}
  → (a : A)
  → (pa : P a)
  → ((x : A) → (px : P x) → R x px)
  → R a pa
starting-at a knowing pa apply
  = λ f → f a pa