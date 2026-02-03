{-# OPTIONS --guardedness #-}
module Program where

open import Data.Nat using (ℕ)
open import Data.List.Base using (List)

open import Thread using (Thread)

-- For representing Rust code like the entirety of rust/main.rs
data Program : Set where
  MkProgram
    : ℕ  -- number of forks
    → List Thread
    → Program
