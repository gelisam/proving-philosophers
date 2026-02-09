module Types.Syntax where

open import Data.List.Base using (List; []; _∷_; concat; map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.String.Base using (String)
open import Data.String.Base as Str using (_++_)

-- Data type for representing syntax with automatic indentation and line breaks
data Syntax : Set where
  Line   : String → Syntax
  Block  : List Syntax → Syntax
  Indent : Syntax → Syntax

-- Helper to convert indentation level to string (4 spaces per level)
make-indent : ℕ → String
make-indent zero = ""
make-indent (suc n) = "    " ++ make-indent n

-- Helper function to concatenate strings
concat-strings : List String → String
concat-strings []       = ""
concat-strings (s ∷ ss) = s ++ concat-strings ss

-- Render a Syntax tree to a String, adding newlines and managing indentation
render : Syntax → String
render = go zero
  where
    go : ℕ → Syntax → String
    go level (Line s) = make-indent level ++ s ++ "\n"
    go level (Block []) = ""
    go level (Block (x ∷ xs)) = go level x ++ go level (Block xs)
    go level (Indent s) = go (suc level) s
