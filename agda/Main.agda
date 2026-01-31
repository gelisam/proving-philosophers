{-# OPTIONS --guardedness #-}
module Main where

open import Data.Unit using (⊤; tt)
open import IO.Primitive.Core using (IO; pure)
open import IO.Primitive.Infinite using (putStrLn)
open import Codata.Musical.Costring using (Costring; toCostring)

main : IO ⊤
main = putStrLn (toCostring "Hello, world!")
