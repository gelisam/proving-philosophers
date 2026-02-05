module Partition where

open import Data.Nat using (ℕ; _+_)
open import Data.Vec using (Vec; []; _∷_; _++_)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

-- A partition where:
-- - xs contains elements satisfying P
-- - ys contains elements satisfying Q  
-- - zs is the whole vector (xs ++ ys), with length i + j
data Partition {A : Set} (P Q : A → Set) : ∀ {i j} → Vec A i → Vec A j → Vec A (i + j) → Set where
  here
    : ∀ {j} {ys : Vec A j}
    → All Q ys
    → Partition P Q [] ys ys
  cons
    : ∀ {i j} {x : A} {xs : Vec A i} {ys : Vec A j} {zs : Vec A (i + j)}
    → P x
    → Partition P Q xs ys zs
    → Partition P Q (x ∷ xs) ys (x ∷ zs)

-- Property 1: i + j ≡ n (this is now trivial since n = i + j in the type)
partition-length
  : ∀ {A : Set} {P Q : A → Set} {i j}
  → {xs : Vec A i} {ys : Vec A j} {zs : Vec A (i + j)}
  → Partition P Q xs ys zs
  → i + j ≡ i + j
partition-length _ = refl

-- Property 2: xs ++ ys ≡ zs  
partition-concat
  : ∀ {A : Set} {P Q : A → Set} {i j}
  → {xs : Vec A i} {ys : Vec A j} {zs : Vec A (i + j)}
  → Partition P Q xs ys zs
  → xs ++ ys ≡ zs
partition-concat (here _) = refl
partition-concat (cons _ p) = cong (_ ∷_) (partition-concat p)

-- Property 3: All P xs
partition-all-p
  : ∀ {A : Set} {P Q : A → Set} {i j}
  → {xs : Vec A i} {ys : Vec A j} {zs : Vec A (i + j)}
  → Partition P Q xs ys zs
  → All P xs
partition-all-p (here _) = []
partition-all-p (cons px p) = px ∷ partition-all-p p

-- Property 4: All Q ys
partition-all-q
  : ∀ {A : Set} {P Q : A → Set} {i j}
  → {xs : Vec A i} {ys : Vec A j} {zs : Vec A (i + j)}
  → Partition P Q xs ys zs
  → All Q ys
partition-all-q (here qys) = qys
partition-all-q (cons _ p) = partition-all-q p
