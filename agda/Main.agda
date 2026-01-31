{-# OPTIONS --guardedness #-}
module Main where

open import Data.String.Base using (String)
open import IO.Base using (Main; run)
open import IO.Finite using (putStrLn)

main : Main
main = run (putStrLn "Hello, world!")
