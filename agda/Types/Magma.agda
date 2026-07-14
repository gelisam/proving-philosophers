module Types.Magma where

open import Data.Maybe using (Maybe; just; nothing)

data Magma (A : Set) : Set where
  atom
    : A
    → Magma A
  concat
    : Magma A
    → Magma A
    → Magma A

mapMagma
  : ∀ {A B}
  → (A → B)
  → Magma A
  → Magma B
mapMagma f (atom a)
  = atom (f a)
mapMagma f (concat m1 m2)
  = concat (mapMagma f m1) (mapMagma f m2)

mapMaybeMagma
  : ∀ {A B}
  → (A → Maybe B)
  → Magma A
  → Maybe (Magma B)
mapMaybeMagma f (atom a)
  with f a
... | just b
    = just (atom b)
... | nothing
    = nothing
mapMaybeMagma f (concat m1 m2)
  with mapMaybeMagma f m1 | mapMaybeMagma f m2
... | just m1' | just m2'
    = just (concat m1' m2')
... | _ | _
    = nothing

data AllMagma {A} (P : A → Set) : Magma A → Set where
  atom
    : ∀ {a}
    → P a
    → AllMagma P (atom a)
  concat
    : ∀ {m1 m2}
    → AllMagma P m1
    → AllMagma P m2
    → AllMagma P (concat m1 m2)

checkAllMagma
  : ∀ {A}
  → {P : A → Set}
  → ((a : A) → Maybe (P a))
  → (m : Magma A)
  → Maybe (AllMagma P m)
checkAllMagma f (atom a)
  with f a
... | just p
    = just (atom p)
... | nothing
    = nothing
checkAllMagma f (concat m1 m2)
  with checkAllMagma f m1 | checkAllMagma f m2
... | just all1 | just all2
    = just (concat all1 all2)
... | _ | _
    = nothing