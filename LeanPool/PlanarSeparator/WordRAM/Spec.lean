/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import Mathlib.Basic.Real.Basic

/-!
# A random-access machine with a cost model

A unit-cost random-access machine with natural-number words, for algorithms on integer data:

* the input is a list of natural numbers (`Input.data`) together with a random tape
  (`Input.tape : ℕ → ℕ`); a deterministic algorithm ignores the tape, a randomized one reads it,
  and probabilities are taken over the tape;
* the output is a list of natural numbers;
* natural-number multiplication, division and remainder are unit-cost instructions (division and
  remainder by zero give `0`, as in Lean);
* `readIn` reads one input word, `rand` one word of the random tape, `outN` appends one word to
  the output.

Everything else is unchanged: natural registers and memory, exact real registers and memory, a
program counter, unit cost per executed instruction (`RunsWithin` charges one step per
instruction and one for the final `halt`), and a bound `W` on every natural word along the run
(`WordsBounded`), which a cost theorem states explicitly.
-/

@[expose] public section

namespace WordRAM

/-- The input of a run: a list of words and a random tape. -/
structure Input where
  /-- The input words. -/
  data : List ℕ
  /-- The random tape. -/
  tape : ℕ → ℕ

/-- The instruction set. `r`, `a`, `b` name registers; `k` is a literal natural; `z` a literal
integer; `l` a literal instruction address. -/
inductive Instr : Type
  /-- Stop; the run has succeeded. -/
  | halt
  /-- `nreg r := n`, the number of input words. -/
  | inputSize (r : ℕ)
  /-- `nreg r := k`. -/
  | constN (r k : ℕ)
  /-- `nreg r := nreg a`. -/
  | copyN (r a : ℕ)
  /-- `nreg r := nreg a + nreg b`. -/
  | addN (r a b : ℕ)
  /-- `nreg r := nreg a - nreg b` (truncated at zero). -/
  | subN (r a b : ℕ)
  /-- `nreg r := nreg a * nreg b`. -/
  | mulN (r a b : ℕ)
  /-- `nreg r := nreg a / nreg b` (`0` if `nreg b = 0`). -/
  | divN (r a b : ℕ)
  /-- `nreg r := nreg a % nreg b` (`nreg a` if `nreg b = 0`). -/
  | modN (r a b : ℕ)
  /-- `nreg r := nmem (nreg a)`. -/
  | loadN (r a : ℕ)
  /-- `nmem (nreg a) := nreg r`. -/
  | storeN (a r : ℕ)
  /-- `rreg r := z`. -/
  | constR (r : ℕ) (z : ℤ)
  /-- `rreg r := rreg a`. -/
  | copyR (r a : ℕ)
  /-- `rreg r := rreg a + rreg b`. -/
  | addR (r a b : ℕ)
  /-- `rreg r := rreg a - rreg b`. -/
  | subR (r a b : ℕ)
  /-- `rreg r := rreg a * rreg b`. -/
  | mulR (r a b : ℕ)
  /-- `rreg r := rreg a / rreg b`; faults if `rreg b = 0`. -/
  | divR (r a b : ℕ)
  /-- `rreg r := rmem (nreg a)`. -/
  | loadR (r a : ℕ)
  /-- `rmem (nreg a) := rreg r`. -/
  | storeR (a r : ℕ)
  /-- `nreg r :=` input word number `nreg a` (`0` past the end). -/
  | readIn (r a : ℕ)
  /-- `nreg r :=` word number `nreg a` of the random tape. -/
  | rand (r a : ℕ)
  /-- `pc := l`. -/
  | jump (l : ℕ)
  /-- If `nreg a < nreg b` then `pc := l` else continue. -/
  | brLtN (a b l : ℕ)
  /-- If `rreg a < rreg b` then `pc := l` else continue. -/
  | brLtR (a b l : ℕ)
  /-- Append `nreg a` to the output. -/
  | outN (a : ℕ)

/-- A program is a finite list of instructions; instruction addresses are list positions. -/
abbrev Program : Type := List Instr

/-- A machine configuration. -/
structure Config where
  /-- The program counter. -/
  pc : ℕ
  /-- Natural registers. -/
  nreg : ℕ → ℕ
  /-- Real registers. -/
  rreg : ℕ → ℝ
  /-- Natural memory. -/
  nmem : ℕ → ℕ
  /-- Real memory. -/
  rmem : ℕ → ℝ
  /-- The words output so far, in order. -/
  output : List ℕ

/-- The initial configuration: program counter `0`, all registers and memory cells zero,
nothing output. -/
def initConfig : Config :=
  { pc := 0, nreg := fun _ => 0, rreg := fun _ => 0, nmem := fun _ => 0, rmem := fun _ => 0,
    output := [] }

/-- Update one entry of a register file or memory. -/
def upd {α : Type} (f : ℕ → α) (i : ℕ) (v : α) : ℕ → α :=
  fun j => if j = i then v else f j

/-- Execute one instruction of `prog` on input `P` from configuration `c`. Returns `none` on a
fault (program counter out of range, or real division by zero) or when the current instruction
is `halt`; otherwise the next configuration. -/
noncomputable def step (prog : Program) (P : Input) (c : Config) : Option Config :=
  match prog[c.pc]? with
  | none => none
  | some ins =>
    match ins with
    | .halt => none
    | .inputSize r => some { c with pc := c.pc + 1, nreg := upd c.nreg r P.data.length }
    | .constN r k => some { c with pc := c.pc + 1, nreg := upd c.nreg r k }
    | .copyN r a => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a) }
    | .addN r a b => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a + c.nreg b) }
    | .subN r a b => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a - c.nreg b) }
    | .mulN r a b => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a * c.nreg b) }
    | .divN r a b => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a / c.nreg b) }
    | .modN r a b => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a % c.nreg b) }
    | .loadN r a => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nmem (c.nreg a)) }
    | .storeN a r => some { c with pc := c.pc + 1, nmem := upd c.nmem (c.nreg a) (c.nreg r) }
    | .constR r z => some { c with pc := c.pc + 1, rreg := upd c.rreg r (z : ℝ) }
    | .copyR r a => some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a) }
    | .addR r a b => some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a + c.rreg b) }
    | .subR r a b => some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a - c.rreg b) }
    | .mulR r a b => some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a * c.rreg b) }
    | .divR r a b =>
        if c.rreg b = 0 then none
        else some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a / c.rreg b) }
    | .loadR r a => some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rmem (c.nreg a)) }
    | .storeR a r => some { c with pc := c.pc + 1, rmem := upd c.rmem (c.nreg a) (c.rreg r) }
    | .readIn r a => some { c with pc := c.pc + 1, nreg := upd c.nreg r (P.data.getD (c.nreg a) 0) }
    | .rand r a => some { c with pc := c.pc + 1, nreg := upd c.nreg r (P.tape (c.nreg a)) }
    | .jump l => some { c with pc := l }
    | .brLtN a b l => some { c with pc := if c.nreg a < c.nreg b then l else c.pc + 1 }
    | .brLtR a b l => some { c with pc := if c.rreg a < c.rreg b then l else c.pc + 1 }
    | .outN a => some { c with pc := c.pc + 1, output := c.output ++ [c.nreg a] }

/-- Run `k` instructions, faulting if any step faults. -/
noncomputable def run (prog : Program) (P : Input) : ℕ → Config → Option Config
  | 0, c => some c
  | k + 1, c => (step prog P c).bind (run prog P k)

/-- The configuration is at a `halt` instruction. -/
def AtHalt (prog : Program) (c : Config) : Prop := prog[c.pc]? = some Instr.halt

/-- Every natural register and every natural memory cell of `c` is at most `W`. -/
def WordsBounded (W : ℕ) (c : Config) : Prop :=
  (∀ r, c.nreg r ≤ W) ∧ (∀ a, c.nmem a ≤ W)

/-- `prog`, started on input `P` in the initial configuration, executes exactly `k`
instructions without faulting and then sits at `halt`, every configuration along the way
(including the final one) has its natural words bounded by `W`, and the output at the end is
`out`. The run is charged `k + 1` steps: one for each executed instruction and one for the final
`halt`. -/
def RunsWithin (prog : Program) (P : Input) (W : ℕ) (steps : ℕ) (out : List ℕ) : Prop :=
  ∃ k : ℕ, k + 1 ≤ steps ∧
    (∀ i, i ≤ k → ∃ c, run prog P i initConfig = some c ∧ WordsBounded W c) ∧
    ∃ c, run prog P k initConfig = some c ∧ AtHalt prog c ∧ c.output = out

end WordRAM
