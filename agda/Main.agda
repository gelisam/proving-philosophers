{-# OPTIONS --guardedness #-}
module Main where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.List.Base using (List; []; _∷_; reverse; map; concat; _++_)
open import Data.String.Base using (String)
open import Data.String.Base as Str using () renaming (_++_ to _+++_)
open import IO.Base using (Main; run)
open import IO.Finite using (putStr)

import Syntax
open import TrustedCore.Stmt using (ThinkRandomly; LockFork; EatRandomly)
open import TrustedCore.Thread using (Thread; MkThread)
open import TrustedCore.Program using (Program; MkProgram; render-program)

-- an Agda representation of rust/main.rs, so we can prove things about it.

threads : List Thread
threads =
  MkThread 1
    ( ThinkRandomly 1
    ∷ LockFork 1 1 2
    ∷ LockFork 2 5 1
    ∷ EatRandomly 1
    ∷ [] )
  ∷ MkThread 2
    ( ThinkRandomly 2
    ∷ LockFork 1 1 2
    ∷ LockFork 2 2 3
    ∷ EatRandomly 2
    ∷ [] )
  ∷ MkThread 3
    ( ThinkRandomly 3
    ∷ LockFork 1 2 3
    ∷ LockFork 2 3 4
    ∷ EatRandomly 3
    ∷ [] )
  ∷ MkThread 4
    ( ThinkRandomly 4
    ∷ LockFork 1 3 4
    ∷ LockFork 2 4 5
    ∷ EatRandomly 4
    ∷ [] )
  ∷ MkThread 5
    ( ThinkRandomly 5
    ∷ LockFork 1 4 5
    ∷ LockFork 2 5 1
    ∷ EatRandomly 5
    ∷ [] )
  ∷ []

program : Program
program = MkProgram 5 threads

-- Render the Agda representation of the Rust code to actual Rust code, so the
-- caller can verify that our proof is about the right program.
main : Main
main = run (putStr (Syntax.render (render-program program)))