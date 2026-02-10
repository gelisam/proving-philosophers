module TrustedBase.RuntimeModel where

open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Bool.ListAction using (all)
open import Data.List.Base using (List; []; _∷_; map; filter; any; _++_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Vec as Vec using (Vec; []; _∷_; toList; fromList)
open import Data.Vec using () renaming (map to mapVec)
open import Function.Base using (id)

open import Types.Fork using (Fork; MkFork)
open import Types.Program using (Program; MkProgram)
open import Types.Stmt using (Stmt; ThinkRandomly; EatRandomly; LockFork)
open import Types.Thread using (Thread; MkThread)
open import Types.Tree using (Tree; MkTree)

-- Represents what condition a thread is waiting for
data WaitingCondition : Set where
  ForkAvailable : Fork → WaitingCondition
  SleepTimer : ℕ → WaitingCondition  -- Tracks remaining sleep time

-- Represents the state of a single thread
record ThreadState : Set where
  constructor MkThreadState
  field
    acquiredForks : List Fork
    waiting : Maybe WaitingCondition
    restOfLoop : List Stmt
    fullLoop : List Stmt  -- Store the original loop for restarting
open ThreadState

-- Represents the state of the entire program with n threads
ProgramState : (n : _) → Set
ProgramState n = Vec ThreadState n

-- Represents all possible traces of program execution
PossibleTraces : (n : _) → Set
PossibleTraces n = Tree (ProgramState n)

-- Helper: Check if two forks are equal
_fork≡ᵇ_ : Fork → Fork → Bool
(MkFork i1 j1) fork≡ᵇ (MkFork i2 j2) = (i1 ≡ᵇ i2) ∧ (j1 ≡ᵇ j2)

-- Helper: Check if a fork is in a list of forks
fork-in-list : Fork → List Fork → Bool
fork-in-list f [] = false
fork-in-list f (x ∷ xs) = (f fork≡ᵇ x) ∨ fork-in-list f xs

-- Helper: Check if a fork is available (not acquired by any thread)
fork-is-available : {n : ℕ} → Fork → ProgramState n → Bool
fork-is-available fork state = not (any-thread-has-fork fork (toList state))
  where
    any-thread-has-fork : Fork → List ThreadState → Bool
    any-thread-has-fork fork [] = false
    any-thread-has-fork fork (ts ∷ tss) = fork-in-list fork (acquiredForks ts) ∨ any-thread-has-fork fork tss

-- Helper: Check if all threads are waiting
all-threads-waiting : {n : ℕ} → ProgramState n → Bool
all-threads-waiting state = all is-waiting (toList state)
  where
    is-waiting : ThreadState → Bool
    is-waiting ts with waiting ts
    ... | nothing = false
    ... | just _ = true

wait-for : WaitingCondition → ThreadState → ThreadState
wait-for condition ts
  = MkThreadState
      (acquiredForks ts)
      (just condition)
      (restOfLoop ts)
      (fullLoop ts)

-- Helper to generate all sleep timer states (1 to n seconds)
-- Generates in descending order [n, n-1, ..., 1] for efficiency
-- Order doesn't affect correctness as all states are explored
generate-timer-states : ℕ → ThreadState → List ThreadState
generate-timer-states zero ts = []
generate-timer-states (suc n) ts
  = wait-for (SleepTimer (suc n)) ts ∷ generate-timer-states n ts

-- Process a single statement for a thread, returning list of possible new thread states
process-stmt : Stmt → ThreadState → List ThreadState
process-stmt (ThinkRandomly _) ts
  = generate-timer-states 10 ts
process-stmt (EatRandomly _) ts
  = generate-timer-states 10 ts
process-stmt (LockFork _ fork) ts
  = wait-for (ForkAvailable fork) ts ∷ []

-- Helper: Decrement sleep timer by 1
-- Returns nothing for expired timers so thread can proceed
-- Preserves ForkAvailable conditions as they don't expire
decrement-timer : WaitingCondition → Maybe WaitingCondition
decrement-timer (ForkAvailable fork) = just (ForkAvailable fork)
decrement-timer (SleepTimer zero) = nothing  -- Timer expired
decrement-timer (SleepTimer (suc n)) = just (SleepTimer n)

-- Decrement timer for a thread state if all threads are waiting
decrement-thread-timer : ThreadState → ThreadState
decrement-thread-timer ts with waiting ts
... | nothing = ts
... | just condition =
  let new-waiting = decrement-timer condition
  in MkThreadState
       (acquiredForks ts)
       new-waiting
       (restOfLoop ts)
       (fullLoop ts)

-- Step a single thread forward if possible
step-thread : {n : ℕ} → ThreadState → ProgramState n → List ThreadState
step-thread ts state with waiting ts | restOfLoop ts
-- Thread is not waiting and has statements to execute
... | nothing | (stmt ∷ rest) with stmt
-- LockFork: Grab immediately if available, otherwise wait
... | LockFork _ fork =
  if fork-is-available fork state
  then (MkThreadState
         (fork ∷ acquiredForks ts)
         nothing
         rest
         (fullLoop ts)) ∷ []
  else (MkThreadState
         (acquiredForks ts)
         (just (ForkAvailable fork))
         rest
         (fullLoop ts)) ∷ []
-- ThinkRandomly/EatRandomly: Generate all possible timer states
... | _ =
  let new-ts-list = process-stmt stmt ts
  in map (λ new-ts → MkThreadState
                       (acquiredForks new-ts)
                       (waiting new-ts)
                       rest
                       (fullLoop ts)) new-ts-list
-- Thread is waiting for a fork
step-thread ts state | just (ForkAvailable fork) | _ =
  if fork-is-available fork state
  then (MkThreadState
         (fork ∷ acquiredForks ts)
         nothing
         (restOfLoop ts)
         (fullLoop ts)) ∷ []
  else []
-- Thread is waiting for sleep timer that has expired
step-thread ts state | just (SleepTimer zero) | _ =
  (MkThreadState
     (acquiredForks ts)
     nothing
     (restOfLoop ts)
     (fullLoop ts)) ∷ []
-- Thread is waiting for sleep timer (not yet expired)
step-thread ts state | just (SleepTimer (suc n)) | _ = []
-- Thread finished its loop, release forks and restart
step-thread ts state | nothing | [] =
  (MkThreadState
    []
    nothing
    (fullLoop ts)
    (fullLoop ts)) ∷ []

-- Generate all possible next states by trying to step each thread
generate-next-states : {n : ℕ} → ProgramState n → List (ProgramState n)
generate-next-states {zero} [] = []
generate-next-states {suc n} (ts ∷ rest) =
  let next-ts-list = step-thread ts (ts ∷ rest)
      rest-nexts = generate-next-states rest
      -- Thread at index 0 steps
      states-from-first = map (λ new-ts → new-ts ∷ rest) next-ts-list
      -- Other threads step
      states-from-rest = map (_∷_ ts) rest-nexts
      -- If all threads are waiting, also add state where all timers decrement
      -- Timer decrement is added last to prioritize individual thread progress
      timer-decrement-state =
        if all-threads-waiting (ts ∷ rest)
        then mapVec decrement-thread-timer (ts ∷ rest) ∷ []
        else []
  in states-from-first ++ states-from-rest ++ timer-decrement-state

-- Helper to extract threads from a Program
get-threads : Program → List Thread
get-threads (MkProgram _ threads) = threads

-- Main function: run a program to produce all possible traces
-- The type says: given a Program, produce a PossibleTraces with n threads
run-program : (p : Program) → PossibleTraces (length (get-threads p))
run-program (MkProgram num-forks threads)
  = MkTree generate-next-states initial-state
  where
    n : ℕ
    n = length threads

    -- Initialize thread state from Thread
    init-thread-state : Thread → ThreadState
    init-thread-state (MkThread _ stmts) = MkThreadState [] nothing stmts stmts

    -- Create initial program state
    initial-state : ProgramState n
    initial-state = mapVec init-thread-state (fromList threads)