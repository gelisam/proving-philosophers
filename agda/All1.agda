module All1 where

open import Data.List.Base using (List; []; _∷_)

-- A variant of Data.List.Relation.Unary.All which also proves that the list is
-- non-empty.
data All1 {A : Set} (P : A → Set) : List A → Set where
  [_]
    : ∀ {x}
    → P x
    → All1 P (x ∷ [])
  _∷_
    : ∀ {x xs}
    → P x
    → All1 P xs
    → All1 P (x ∷ xs)

infixr 5 _∷_