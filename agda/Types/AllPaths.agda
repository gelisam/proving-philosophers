open import Data.List.Base using (List; []; _∷_)

open import Types.All1 using (All1; [_]; _∷_)
open import Types.Tree using (Tree; StepFun; value; childValues)

module Types.AllPaths {A : Set} (f : StepFun A) where

-- We want to express the property that no philosopher will starve. That is, at
-- any point in any of the branching paths of the execution tree, that point is
-- a finite number of steps away from an EatRandomly statement.
--
-- The following datatype represents the "a finite number of steps away from X"
-- part of that statement: a value of type AllPaths P is finite and represents a
-- proof that along every path, a node satisfying P occurs after a finite number
-- of steps. In particular, no path can end with `f a = []` before reaching a
-- node satisfying P.
data AllPaths (P : A → Set) (a : A) : Set where
  here
    : P a
    → AllPaths P a
  there
    : All1 (AllPaths P) (f a)
    → AllPaths P a

mutual
  AllPaths-map
    : {P Q : A → Set}
    → ((x : A) → P x → Q x)
    → (a : A)
    → AllPaths P a
    → AllPaths Q a
  AllPaths-map p2q a (here pa)
    = here (p2q a pa)
  AllPaths-map p2q a (there aps)
    = there (All-AllPaths-map p2q (f a) aps)

  All-AllPaths-map
    : {P Q : A → Set}
    → ((x : A) → P x → Q x)
    → (xs : List A)
    → All1 (AllPaths P) xs
    → All1 (AllPaths Q) xs
  All-AllPaths-map p2q _ [ ap ]
    = [ AllPaths-map p2q _ ap ]
  All-AllPaths-map p2q _ (ap ∷ aps)
    = AllPaths-map p2q _ ap
    ∷ All-AllPaths-map p2q _ aps

mutual
  AllPaths-bind
    : {P Q : A → Set} {a : A}
    → AllPaths P a
    → ((x : A) → P x → AllPaths Q x)
    → AllPaths Q a
  AllPaths-bind (here px) k
    = k _ px
  AllPaths-bind (there aps) k
    = there (All-AllPaths-bind aps k)

  -- Helper function for mapping bindAllPaths over All
  All-AllPaths-bind
    : {P Q : A → Set} {as : List A}
    → All1 (AllPaths P) as
    → ((x : A) → P x → AllPaths Q x)
    → All1 (AllPaths Q) as
  All-AllPaths-bind [ ap ] k
    = [ AllPaths-bind ap k ]
  All-AllPaths-bind (ap ∷ aps) k
    = AllPaths-bind ap k
    ∷ All-AllPaths-bind aps k

_>>=_
  : {P Q : A → Set} {a : A}
  → AllPaths P a
  → ((x : A) → P x → AllPaths Q x)
  → AllPaths Q a
_>>=_ = AllPaths-bind
infixl 5 _>>=_
