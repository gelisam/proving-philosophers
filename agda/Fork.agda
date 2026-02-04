module Fork where

open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.String.Base as Str using (String) renaming (_++_ to _+++_)

-- For representing a fork (mutex) between two philosophers
-- Fork i j represents the fork between philosopher i and philosopher j
data Fork : Set where
  MkFork : ℕ → ℕ → Fork

-- Generate the name of a fork, e.g., "FORK_1_2"
show-fork : Fork → String
show-fork (MkFork i j)
    = "FORK_" +++ show i
 +++ "_" +++ show j
