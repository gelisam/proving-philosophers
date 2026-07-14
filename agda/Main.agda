{-# OPTIONS --guardedness #-}
module Main where

open import IO.Base using (Main; run)
open import IO.Finite using (putStr)

import Types.Syntax
open import TrustedBase.Render using (render-program)

open import RustProgram using (program)

-- Import Practice.agda etc. to ensure they are type-checked
import Practice
import ExecutionModel


-- Render the Agda representation of the Rust code to actual Rust code, so the
-- caller can verify that our proof is about the right program.
main : Main
main = run (putStr (Types.Syntax.render (render-program program)))
