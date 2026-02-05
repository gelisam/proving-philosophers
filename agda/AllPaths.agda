module AllPaths where

open import Data.List.Base using (List; []; _∷_)

open import All1 using (All1; [_]; _∷_)
open import Tree using (Tree; StepFun; value; childValues)

-- We want to express the property that no philosopher will starve. That is, at
-- any point in any of the branching paths of the execution tree, that point is
-- a finite number of steps away from an EatRandomly statement.
--
-- The following datatype represents the "a finite number of steps away from X"
-- part of that statement: a value of type AllPaths P is finite and represents a
-- proof that along every path, a node satisfying P occurs after a finite number
-- of steps. In particular, no path can end with `f a = []` before reaching a
-- node satisfying P.
data AllPaths {A : Set} (f : StepFun A) (P : A → Set) (a : A) : Set where
  here
    : P a
    → AllPaths f P a
  there
    : All1 (AllPaths f P) (f a)
    → AllPaths f P a

-- Combinator for chaining AllPaths proofs (uses mutual recursion)
mutual
  AllPaths-bind
    : {A : Set} {f : StepFun A} {P Q : A → Set} {a : A}
    → AllPaths f P a
    → ((x : A) → P x → AllPaths f Q x)
    → AllPaths f Q a
  AllPaths-bind (here px) k
    = k _ px
  AllPaths-bind (there aps) k
    = there (All-AllPaths-bind aps k)

  -- Helper function for mapping bindAllPaths over All
  All-AllPaths-bind
    : {A : Set} {f : StepFun A} {P Q : A → Set} {as : List A}
    → All1 (AllPaths f P) as
    → ((x : A) → P x → AllPaths f Q x)
    → All1 (AllPaths f Q) as
  All-AllPaths-bind [ ap ] k
    = [ AllPaths-bind ap k ]
  All-AllPaths-bind (ap ∷ aps) k
    = AllPaths-bind ap k
    ∷ All-AllPaths-bind aps k

_>>=_
  : {A : Set} {f : StepFun A} {P Q : A → Set} {a : A}
  → AllPaths f P a
  → ((x : A) → P x → AllPaths f Q x)
  → AllPaths f Q a
_>>=_ = AllPaths-bind
infixl 5 _>>=_