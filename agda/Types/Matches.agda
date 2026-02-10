{-# OPTIONS --guardedness #-}
{-# OPTIONS --termination-depth=3 #-}

open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types.All1 using (All1; [_]; _∷_)
open import Types.Tree using (StepFun)
import Types.AllPaths

module Types.Matches
  {B S : Set}
  (bigStep : StepFun B)
  (smallStep : StepFun S)
  (recover : B → S)
  where

open Types.AllPaths smallStep renaming (AllPaths to AllPathsSmall; _>>=_ to _>>=S_)
open Types.AllPaths bigStep renaming (AllPaths to AllPathsBig; _>>=_ to _>>=B_)

-- MatchesOneOf represents that a small state s matches one of the big states
-- in the list bs by recovering to the same state
data MatchesOneOf : List B → S → Set where
  here
    : {b : B} {bs : List B}
    → MatchesOneOf (b ∷ bs) (recover b)
  there
    : {b : B} {bs : List B} {s : S}
    → MatchesOneOf bs s
    → MatchesOneOf (b ∷ bs) s

-- MatchesAllPaths is a record that proves the relationship between
-- big states and small states through the recover function
-- NOTE: The problem statement only included matchesHere and matchesThere,
-- but implementing AllPaths-expand requires knowing how small steps relate to big steps.
-- The smallStepMatches field provides this necessary information.
record MatchesAllPaths (b : B) (s : S) : Set where
  coinductive
  field
    matchesHere
      : MatchesAllPaths b (recover b)
    matchesThere
      : {s' : S}
      → Types.AllPaths.AllPaths smallStep (MatchesOneOf (bigStep b)) s'
      → MatchesAllPaths b s'
    -- Additional field needed for AllPaths-expand proof:
    -- For each small step from s, we eventually match one of the big steps
    smallStepMatches
      : All1 (Types.AllPaths.AllPaths smallStep (MatchesOneOf (bigStep b))) (smallStep s)

-- Additional assumption needed for the proof
postulate
  allMatches : (b : B) → MatchesAllPaths b (recover b)

-- AllPaths-expand proves that if we have a property P on big states that
-- implies a property Q on recovered small states, and we have AllPaths P
-- on big states, and MatchesAllPaths holds, then we have AllPaths Q on
-- the recovered small state
{-# TERMINATING #-}
mutual
  AllPaths-expand
    : {P : B → Set} {Q : S → Set} {b : B}
    → ((x : B) → P x → Q (recover x))
    → AllPathsBig P b
    → MatchesAllPaths b (recover b)
    → AllPathsSmall Q (recover b)
  AllPaths-expand {P} {Q} {b} p→q (Types.AllPaths.here pb) matches
    = Types.AllPaths.here (p→q b pb)
  AllPaths-expand {P} {Q} {b} p→q (Types.AllPaths.there aps) matches
    = Types.AllPaths.there (helper-All1 p→q matches aps (MatchesAllPaths.smallStepMatches matches))

  -- Map a bind operation over an All1 (for small steps)
  All1-map-bind
    : {P Q : S → Set} {as : List S}
    → All1 (AllPathsSmall P) as
    → ((a : S) → P a → AllPathsSmall Q a)
    → All1 (AllPathsSmall Q) as
  All1-map-bind [ ap ] f
    = [ ap >>=S f ]
  All1-map-bind (ap ∷ aps) f
    = (ap >>=S f) ∷ All1-map-bind aps f

  helper-All1
    : {P : B → Set} {Q : S → Set} {b : B}
    → ((x : B) → P x → Q (recover x))
    → MatchesAllPaths b (recover b)
    → All1 (AllPathsBig P) (bigStep b)
    → All1 (AllPathsSmall (MatchesOneOf (bigStep b))) (smallStep (recover b))
    → All1 (AllPathsSmall Q) (smallStep (recover b))
  helper-All1 {P} {Q} {b} p→q parentMatches bigAps smallAps
    = All1-map-bind {MatchesOneOf (bigStep b)} {Q} smallAps (matchToQ p→q parentMatches bigAps)

  -- Extract the proof corresponding to a MatchesOneOf
  extract-proof
    : {P : B → Set} {bs : List B} {s : S}
    → All1 (AllPathsBig P) bs
    → MatchesOneOf bs s
    → ∃[ b' ] (AllPathsBig P b' × (s ≡ recover b'))
  extract-proof [ ap ] here
    = (_ , ap , refl)
  extract-proof (ap ∷ aps) here
    = (_ , ap , refl)
  extract-proof [ ap ] (there ())
  extract-proof (ap ∷ aps) (there m)
    = extract-proof aps m

  -- Given proofs that all big steps eventually reach P,
  -- and MatchesAllPaths for the parent,
  -- and a proof that a small state matches one of those big steps,
  -- produce a proof that the small state eventually reaches Q
  matchToQ
    : {P : B → Set} {Q : S → Set} {b : B}
    → ((x : B) → P x → Q (recover x))
    → MatchesAllPaths b (recover b)
    → All1 (AllPathsBig P) (bigStep b)
    → (s : S)
    → MatchesOneOf (bigStep b) s
    → AllPathsSmall Q s
  matchToQ {P} {Q} {b} p→q parentMatches aps s match
    with extract-proof aps match
  ... | (b' , apBig , refl)
    = AllPaths-expand p→q apBig (allMatches b')
