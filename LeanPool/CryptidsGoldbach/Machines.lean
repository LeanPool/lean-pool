/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maxence Faldor, Moritz Firsching
-/
module

public import Mathlib.Computability.TuringMachine.Tape
public import Mathlib.Computability.StateTransition

/-!
# Finite-state Turing machines

A machine has a finite transition table and a tape from Mathlib. This module preserves
the execution definitions and the two Goldbach tables from google-deepmind/cryptids.
The tables are embedded as Lean literals so importing the project needs no external files.
-/

@[expose] public section
namespace ConjectureMachines
open Turing StateTransition

/-- A transition table: for a state and the symbol under the head, either the
symbol to write, the direction to move and the state to enter, or `none` to
halt. -/
structure Machine (states symbols : ℕ) where
  /-- The action for each state and scanned symbol. -/
  transition : Fin states → Fin symbols → Option (Fin symbols × Dir × Fin states)

variable {states symbols : ℕ} [NeZero states] [NeZero symbols]

/-- A configuration: the current state and the tape, whose `head` is the
symbol under the head. -/
structure Cfg (states symbols : ℕ) [NeZero symbols] where
  /-- The current control state. -/
  state : Fin states
  /-- The tape and head position. -/
  tape : Tape (Fin symbols)

/-- One step, or `none` when the transition is missing. -/
def step (M : Machine states symbols) : Cfg states symbols → Option (Cfg states symbols)
  | ⟨q, T⟩ => (M.transition q T.head).map fun ⟨a, d, q'⟩ => ⟨q', (T.write a).move d⟩

/-- The start state on the all-blank tape. -/
def init : Cfg states symbols := ⟨0, Tape.mk₁ []⟩

/-- `M` halts when started in state `0` on the all-blank tape. -/
def Halts (M : Machine states symbols) : Prop := (StateTransition.eval (step M) init).Dom

/-- Build a `Machine states symbols` from a list of per-state transition rows. -/
def Machine.ofRows (rows : List (List (Option (Fin symbols × Dir × Fin states)))) :
    Machine states symbols := ⟨fun q a => (rows.getD q.val []).getD a.val none⟩

/-- A Turing machine over `symbols` tape symbols bundled with its non-zero state count. -/
structure BundledMachine (symbols : ℕ) where
  /-- The number of control states. -/
  states : ℕ
  [neZeroStates : NeZero states]
  /-- The transition table with this state count. -/
  toMachine : Machine states symbols

attribute [instance] BundledMachine.neZeroStates

/-- Bundle a `Machine (states + 1) symbols` into a `BundledMachine symbols`. -/
abbrev Machine.bundle {states symbols : ℕ} (M : Machine (states + 1) symbols) :
    BundledMachine symbols := ⟨states + 1, M⟩

/-- `M` halts when started in state `0` on the all-blank tape. -/
abbrev BundledMachine.Halts {symbols : ℕ} [NeZero symbols] (M : BundledMachine symbols) : Prop :=
  ConjectureMachines.Halts M.toMachine

export BundledMachine (Halts)

namespace Machines

/-- Rows of the 25-state machine of Yijun Leng, from the upstream baseline table. -/
def goldbach25Rows : List (List (Option (Fin 2 × Dir × Fin 25))) := [
  [some (1, .right, 1), some (1, .right, 3)],
  [some (1, .left, 2), some (1, .right, 1)],
  [some (0, .right, 0), some (1, .left, 2)],
  [some (0, .left, 16), some (1, .right, 4)],
  [some (0, .left, 5), some (1, .right, 6)],
  [some (0, .left, 2), some (1, .left, 5)],
  [some (0, .left, 5), some (0, .left, 7)],
  [some (1, .left, 16), some (1, .left, 8)],
  [some (0, .right, 9), some (0, .left, 8)],
  [some (1, .right, 10), some (0, .left, 9)],
  [some (0, .right, 11), some (0, .right, 18)],
  [some (1, .right, 11), some (0, .right, 12)],
  [some (1, .right, 13), some (1, .right, 12)],
  [some (0, .left, 14), some (0, .left, 20)],
  [some (0, .left, 15), some (1, .left, 14)],
  [some (1, .right, 7), some (1, .left, 23)],
  [some (1, .left, 17), some (1, .left, 16)],
  [some (0, .right, 10), some (0, .left, 19)],
  [some (1, .left, 17), some (1, .right, 18)],
  [none, some (1, .right, 2)],
  [some (1, .left, 21), some (1, .left, 20)],
  [some (0, .left, 22), some (0, .left, 9)],
  [some (0, .right, 10), some (0, .left, 22)],
  [some (1, .right, 24), some (1, .left, 23)],
  [some (1, .right, 4), some (1, .right, 24)]
]

/-- The 25-state Goldbach baseline. -/
def goldbach25 : Machine 25 2 := Machine.ofRows goldbach25Rows

/-- Rows of the 21-state machine of Maxence Faldor and Moritz Firsching. -/
def goldbach21Rows : List (List (Option (Fin 2 × Dir × Fin 21))) := [
  [some (1, .left, 9), some (0, .right, 5)],
  [some (0, .right, 9), some (1, .right, 3)],
  [some (1, .right, 15), some (1, .left, 2)],
  [none, some (1, .right, 4)],
  [some (0, .left, 14), some (1, .right, 6)],
  [some (1, .left, 16), some (1, .right, 5)],
  [some (0, .right, 7), some (0, .left, 7)],
  [some (0, .left, 12), some (1, .left, 20)],
  [some (1, .right, 1), some (0, .left, 8)],
  [some (1, .right, 9), some (0, .right, 10)],
  [some (1, .right, 11), some (1, .right, 10)],
  [some (0, .left, 12), some (0, .left, 18)],
  [some (1, .left, 13), some (1, .left, 12)],
  [some (1, .left, 14), some (0, .left, 2)],
  [some (1, .left, 16), some (1, .left, 14)],
  [some (1, .right, 3), some (1, .right, 15)],
  [some (0, .right, 0), some (0, .left, 17)],
  [some (0, .right, 1), some (1, .left, 17)],
  [some (1, .left, 19), some (1, .left, 18)],
  [some (0, .left, 20), some (0, .left, 8)],
  [some (0, .right, 1), some (0, .left, 20)]
]

/-- The 21-state Goldbach machine. -/
def goldbach21 : Machine 21 2 := Machine.ofRows goldbach21Rows

end Machines

/-- The configuration `n` steps in from `init`, or `none` once `M` has halted. -/
def run (M : Machine states symbols) (n : ℕ) : Option (Cfg states symbols) :=
  (fun c => c.bind (step M))^[n] (some init)

/-- `M`, started in state `0` on the all-blank tape, has not halted within `n` steps. -/
def Runs (M : Machine states symbols) (n : ℕ) : Prop := (run M n).isSome

instance (M : Machine states symbols) (n : ℕ) : Decidable (Runs M n) :=
  inferInstanceAs (Decidable ((run M n).isSome = true))

end ConjectureMachines
