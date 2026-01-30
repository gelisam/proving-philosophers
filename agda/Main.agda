{-# OPTIONS --guardedness #-}
module Main where

open import Data.Unit using (⊤; tt)
open import IO.Primitive using (IO; pure)

main : IO ⊤
main = pure tt
