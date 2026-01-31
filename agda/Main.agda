module Main where

open import Data.String using (String)
open import IO using (IO; Main; run; putStrLn)

main : Main
main = run (putStrLn "Hello, world!")
