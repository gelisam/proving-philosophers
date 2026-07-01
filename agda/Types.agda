module Types (S : Set) where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; lookup; _[_]≔_)

open import Types.Magma using (Magma; atom; concat; AllMagma)


----------------------------------------------
-- datatypes for representing the evolution --
-- of non-deterministic systems             --
----------------------------------------------

-- The entire system's evolution is divided into a sequence of time steps.
--
-- Each time step is divided into a sequence of atomic steps.
--
-- When choosing the possible interleavings of atomic steps, we ask each thread
-- which atomic step they want to perform next.

data SingleThreadAtomicStep : Set where
  -- Ready for more atomic steps within the current time step.
  next
    : S
    → SingleThreadAtomicStep
  -- Ready for the next time step.
  done
    : SingleThreadAtomicStep
  -- Blocked until another thread hopefully unblocks this thread.
  -- If all threads are blocked, then the system is deadlocked.
  blocked
    : SingleThreadAtomicStep

data SystemAtomicStep : Set where
  -- Ready for more atomic steps within the current time step.
  next
    : S
    → SystemAtomicStep
  -- Ready for the next time step.
  done
    : SystemAtomicStep
  -- No more time steps are possible.
  deadlocked
    : SystemAtomicStep