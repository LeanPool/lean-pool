/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.WordRAM.Machine.Structured

/-!
# Verification support for straight-line blocks

This file fixes the *style* in which programs for the RAM of `WordRAM/Spec.lean` are written and
verified.  Everything downstream (`MinVertex`, `EdgeHit`, and the larger programs to come)
follows the same pattern.

## The pattern

1. **Programs are `Stmt`s**, written with `Stmt.block [i₁, …, iₖ]` for straight-line pieces,
   `Stmt.seq`, `Stmt.ifLtN/ifLtR` and `Stmt.whileLtN/whileLtR` for control.  Register
   allocation is documented next to the definition (which registers are inputs, outputs,
   scratch).

2. **Every building block gets a *spec lemma* of the shape**
   ```
   theorem foo_exec (P : Input) (W : ℕ) (c : Config) (hc : WordsBounded W c) (side…) :
       ∃ c' k, Exec P W fooStmt c c' k ∧ k ≤ K ∧ ⟨postcondition on c, c'⟩ ∧ ⟨frame⟩
   ```
   with an explicit numeric cost `K`, a postcondition on the registers written, and a
   *frame*: which registers/memory/output are untouched.

3. **Goals are always of the form `∃ c' k, Exec P W s c c' k ∧ Q c' k`** ("spec goals") with
   `c` an explicit configuration and no metavariables.  The lemmas `spec_seq`,
   `spec_ifLtR_true/false`, `spec_ifLtN_true/false`, `spec_skip`, `spec_instr`, `spec_use`
   and `spec_imp` decompose a spec goal along the structure of `s`, threading the cost into
   `Q`; when `s` has been consumed the goal is `Q c_final k_final` with the final
   configuration written out as `{ c with nreg := upd (upd c.nreg …) …, rreg := … }` and
   the cost as a sum of literals (`0 + 1 + 1 + (1 + 2)`; `omega` and `config_simp` normalise
   it).  The postcondition is proved conjunct by conjunct:
   `refine ⟨by omega, by config_simp, fun r hr => by simp [hr], rfl, rfl⟩` — `rfl` closes
   the untouched-field conjuncts (`c'.nmem = c.nmem`), `config_simp` the register readings.

4. **Straight-line blocks are discharged by `exec_block`.**  On a spec goal for
   `Stmt.block [i₁, …, iₖ]` with `hc : WordsBounded W c` in context, it chains `spec_step`
   with the per-instruction rules of `WordRAM.Machine.Exec`, flattening the configuration
   after each step (so its size stays linear in `k`).  The remaining goals are the side
   conditions (`x ≤ W` for `constN`/`inputSize`/`addN`, `_ ≠ 0` for the divisor of `divR`),
   in program order, *followed by* the postcondition goal (`Q c_final k`, or the spec goal
   for the rest of the program when the block was sequenced with `spec_seq`).  The
   postcondition itself is never simplified by the tactic.  Typical use:
   ```
   refine spec_seq ?_
   -- Goal: ∃ c₁ k₁, Exec (block …) c c₁ k₁ ∧ ∃ c' k₂, Exec t c₁ c' k₂ ∧ Q c' (k₁ + k₂)
   exec_block
   · omega                        -- side condition `5 ≤ W`
   · config_simp; omega           -- side condition `{…}.nreg 0 + {…}.nreg 1 ≤ W`
   -- main goal: ∃ c' k₂, Exec t { c with … } c' k₂ ∧ Q c' (0 + 1 + 1 + 1 + k₂)
   ```
   `config_simp` (`simp only` with the projection and `upd` lemmas, never failing) reduces a
   configuration's fields; full `simp` does too.  The hypothesis names `‹WordsBounded _ _›`
   are found by `assumption`, so the word bound of the current configuration must be a
   hypothesis: after `spec_instr … fun hw₁ => ?_` or `spec_use …; intro c₁ k₁ hk hw₁ hpost`
   it is.

5. **Conditionals**: `by_cases h : (test in terms of the original registers)`, then
   `refine spec_ifLtR_true (by config_simp; exact h) ?_` or `_false` (`config_simp` reduces
   the test on the current configuration to the original registers).

5'. **Using a spec lemma of a sub-program** inside a spec goal:
   `refine spec_use (foo_exec _ ‹_›) ?_; intro c₁ k₁ hk hw₁ hpost` — the facts in `hpost`
   mention fields of the current (explicit) configuration; `config_simp at hpost` reduces
   them to the original registers.

6. **Loops** use `Exec.whileLtN_bounded` (body cost `B`, measure `μ`) or
   `Exec.whileLtN_potential`; the invariant includes `WordsBounded W`, the loop-variable
   facts, the mathematical invariant and the frame.  The body is proved as a spec lemma
   (pattern 2) and plugged into the invariant proof.

7. **Reading off facts**: `config_simp` or `simp`; the frame (`∀ r, r ∉ written → c'.nreg r
   = c.nreg r`) is proved by `intro r hr; simp [h₁, h₂]` with `hᵢ : r ≠ i` the register
   inequalities (they let `Machine.upd_other` fire); `Machine.upd_apply` turns a symbolic
   `upd f i v j` into an `if`.

8. **Top level**: `Machine.runsWithin_of_exec` turns an execution from `initConfig` into
   `RunsWithin (compile s 0 ++ [.halt]) P W (k + 1) out`.

## Contents

* `spec_nil`, `spec_step`: the chaining lemmas used by `exec_block`.
* `spec_seq`, `spec_skip`, `spec_instr`, `spec_ifLtN_true/false`, `spec_ifLtR_true/false`,
  `spec_use`, `spec_imp`, `spec_seq_of`: structural decomposition of spec goals.
* `exec_block`: the tactic (built from `exec_block_step`, `config_flatten_at`, `spec_flatten`).
* `config_simp`: the projection/`upd` simp set (also `config_simp at h`).
* `exec_block_example`: a worked example (also a regression test for the tactic).
-/

namespace WordRAM

namespace Programs

open Machine Machine.Stmt

@[expose] public section

/-! ### Spec goals and their decomposition -/

section spec
variable {P : Input} {W : ℕ}

/-- The empty block: the postcondition holds now, at cost `0`. -/
theorem spec_nil {c : Config} {Q : Config → ℕ → Prop} (hw : WordsBounded W c) (hQ : Q c 0) :
    ∃ c' k, Exec P W (block []) c c' k ∧ Q c' k :=
  ⟨c, 0, Exec.block_nil hw, hQ⟩

/-- One instruction of a block: run it (rule `h₁`, giving the explicit next configuration
`c₁`), then continue with the rest at cost `k + 1`. -/
theorem spec_step {i : Instr} {l : List Instr} {c c₁ : Config} {Q : Config → ℕ → Prop}
    (h₁ : Exec P W (.instr i) c c₁ 1)
    (h₂ : WordsBounded W c₁ → ∃ c' k, Exec P W (block l) c₁ c' k ∧ Q c' (k + 1)) :
    ∃ c' k, Exec P W (block (i :: l)) c c' k ∧ Q c' k := by
  obtain ⟨c', k, e, q⟩ := h₂ h₁.wb_right
  exact ⟨c', k + 1, Exec.block_cons h₁ e, q⟩

/-- A single instruction statement. -/
theorem spec_instr {i : Instr} {c c₁ : Config} {Q : Config → ℕ → Prop}
    (h₁ : Exec P W (.instr i) c c₁ 1) (hQ : WordsBounded W c₁ → Q c₁ 1) :
    ∃ c' k, Exec P W (.instr i) c c' k ∧ Q c' k :=
  ⟨c₁, 1, h₁, hQ h₁.wb_right⟩

/-- `skip`. -/
theorem spec_skip {c : Config} {Q : Config → ℕ → Prop} (hw : WordsBounded W c) (hQ : Q c 0) :
    ∃ c' k, Exec P W .skip c c' k ∧ Q c' k :=
  ⟨c, 0, .skip hw, hQ⟩

/-- Sequencing: run `s`, then `t` from where `s` stopped; costs add. -/
theorem spec_seq {s t : Stmt} {c : Config} {Q : Config → ℕ → Prop}
    (h : ∃ c₁ k₁, Exec P W s c c₁ k₁ ∧ ∃ c' k₂, Exec P W t c₁ c' k₂ ∧ Q c' (k₁ + k₂)) :
    ∃ c' k, Exec P W (.seq s t) c c' k ∧ Q c' k := by
  obtain ⟨c₁, k₁, e₁, c', k₂, e₂, q⟩ := h
  exact ⟨c', k₁ + k₂, .seq e₁ e₂, q⟩

/-- `ifLtN`, test true: cost `k + 1`. -/
theorem spec_ifLtN_true {a b : ℕ} {t e : Stmt} {c : Config} {Q : Config → ℕ → Prop}
    (ht : c.nreg a < c.nreg b) (h : ∃ c' k, Exec P W t c c' k ∧ Q c' (k + 1)) :
    ∃ c' k, Exec P W (.ifLtN a b t e) c c' k ∧ Q c' k := by
  obtain ⟨c', k, ex, q⟩ := h
  exact ⟨c', k + 1, .ifLtN_true ht ex, q⟩

/-- `ifLtN`, test false: cost `k + 2`. -/
theorem spec_ifLtN_false {a b : ℕ} {t e : Stmt} {c : Config} {Q : Config → ℕ → Prop}
    (ht : ¬ c.nreg a < c.nreg b) (h : ∃ c' k, Exec P W e c c' k ∧ Q c' (k + 2)) :
    ∃ c' k, Exec P W (.ifLtN a b t e) c c' k ∧ Q c' k := by
  obtain ⟨c', k, ex, q⟩ := h
  exact ⟨c', k + 2, .ifLtN_false ht ex, q⟩

/-- `ifLtR`, test true: cost `k + 1`. -/
theorem spec_ifLtR_true {a b : ℕ} {t e : Stmt} {c : Config} {Q : Config → ℕ → Prop}
    (ht : c.rreg a < c.rreg b) (h : ∃ c' k, Exec P W t c c' k ∧ Q c' (k + 1)) :
    ∃ c' k, Exec P W (.ifLtR a b t e) c c' k ∧ Q c' k := by
  obtain ⟨c', k, ex, q⟩ := h
  exact ⟨c', k + 1, .ifLtR_true ht ex, q⟩

/-- `ifLtR`, test false: cost `k + 2`. -/
theorem spec_ifLtR_false {a b : ℕ} {t e : Stmt} {c : Config} {Q : Config → ℕ → Prop}
    (ht : ¬ c.rreg a < c.rreg b) (h : ∃ c' k, Exec P W e c c' k ∧ Q c' (k + 2)) :
    ∃ c' k, Exec P W (.ifLtR a b t e) c c' k ∧ Q c' k := by
  obtain ⟨c', k, ex, q⟩ := h
  exact ⟨c', k + 2, .ifLtR_false ht ex, q⟩

/-- Plug in a spec lemma for a sub-statement: its cost bound and postcondition are all
that the continuation may use. -/
theorem spec_use {s : Stmt} {c : Config} {K : ℕ} {post : Config → Prop}
    {Q : Config → ℕ → Prop}
    (h : ∃ c' k, Exec P W s c c' k ∧ k ≤ K ∧ post c')
    (hQ : ∀ c' k, k ≤ K → WordsBounded W c' → post c' → Q c' k) :
    ∃ c' k, Exec P W s c c' k ∧ Q c' k := by
  obtain ⟨c', k, ex, hk, hp⟩ := h
  exact ⟨c', k, ex, hQ c' k hk ex.wb_right hp⟩

/-- Weaken the postcondition. -/
theorem spec_imp {s : Stmt} {c : Config} {Q Q' : Config → ℕ → Prop}
    (h : ∃ c' k, Exec P W s c c' k ∧ Q c' k) (hQ : ∀ c' k, Q c' k → Q' c' k) :
    ∃ c' k, Exec P W s c c' k ∧ Q' c' k := by
  obtain ⟨c', k, ex, q⟩ := h
  exact ⟨c', k, ex, hQ c' k q⟩

/-- Compose two spec lemmas of the standard shape (pattern 2 of the module docstring). -/
theorem spec_seq_of {s t : Stmt} {c : Config} {K₁ K₂ : ℕ} {Q₁ : Config → Prop}
    {Q₂ : Config → Config → Prop}
    (h₁ : ∃ c₁ k₁, Exec P W s c c₁ k₁ ∧ k₁ ≤ K₁ ∧ Q₁ c₁)
    (h₂ : ∀ c₁, WordsBounded W c₁ → Q₁ c₁ →
      ∃ c₂ k₂, Exec P W t c₁ c₂ k₂ ∧ k₂ ≤ K₂ ∧ Q₂ c₁ c₂) :
    ∃ c₂ k, Exec P W (.seq s t) c c₂ k ∧ k ≤ K₁ + K₂ ∧ ∃ c₁, Q₁ c₁ ∧ Q₂ c₁ c₂ := by
  obtain ⟨c₁, k₁, e₁, hk₁, q₁⟩ := h₁
  obtain ⟨c₂, k₂, e₂, hk₂, q₂⟩ := h₂ c₁ e₁.wb_right q₁
  exact ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, c₁, q₁, q₂⟩

end spec

/-! ### Simp support -/

/-- Reading a field of an explicitly built configuration. -/
@[simp] theorem Config.nreg_mk (pc : ℕ) (nreg : ℕ → ℕ) (rreg : ℕ → ℝ) (nmem : ℕ → ℕ)
    (rmem : ℕ → ℝ) (output : List ℕ) :
    (Config.mk pc nreg rreg nmem rmem output).nreg = nreg := rfl
@[simp] theorem Config.rreg_mk (pc : ℕ) (nreg : ℕ → ℕ) (rreg : ℕ → ℝ) (nmem : ℕ → ℕ)
    (rmem : ℕ → ℝ) (output : List ℕ) :
    (Config.mk pc nreg rreg nmem rmem output).rreg = rreg := rfl
@[simp] theorem Config.nmem_mk (pc : ℕ) (nreg : ℕ → ℕ) (rreg : ℕ → ℝ) (nmem : ℕ → ℕ)
    (rmem : ℕ → ℝ) (output : List ℕ) :
    (Config.mk pc nreg rreg nmem rmem output).nmem = nmem := rfl
@[simp] theorem Config.rmem_mk (pc : ℕ) (nreg : ℕ → ℕ) (rreg : ℕ → ℝ) (nmem : ℕ → ℕ)
    (rmem : ℕ → ℝ) (output : List ℕ) :
    (Config.mk pc nreg rreg nmem rmem output).rmem = rmem := rfl
@[simp] theorem Config.output_mk (pc : ℕ) (nreg : ℕ → ℕ) (rreg : ℕ → ℝ) (nmem : ℕ → ℕ)
    (rmem : ℕ → ℝ) (output : List ℕ) :
    (Config.mk pc nreg rreg nmem rmem output).output = output := rfl
@[simp] theorem Config.pc_mk (pc : ℕ) (nreg : ℕ → ℕ) (rreg : ℕ → ℝ) (nmem : ℕ → ℕ)
    (rmem : ℕ → ℝ) (output : List ℕ) :
    (Config.mk pc nreg rreg nmem rmem output).pc = pc := rfl

/-- The word bound of an explicitly built configuration. -/
theorem wordsBounded_mk {W : ℕ} (pc : ℕ) (nreg : ℕ → ℕ) (rreg : ℕ → ℝ) (nmem : ℕ → ℕ)
    (rmem : ℕ → ℝ) (output : List ℕ) :
    WordsBounded W (Config.mk pc nreg rreg nmem rmem output) ↔
      (∀ r, nreg r ≤ W) ∧ (∀ a, nmem a ≤ W) := Iff.rfl

open Lean.Parser.Tactic in
/-- `simp only` with the configuration-projection and `upd` lemmas.  Reduces
`({ c with nreg := upd c.nreg 0 5, … } : Config).nreg 0` to `5`, and `.nreg 1` to `c.nreg 1`
(the inequality `1 ≠ 0` between literals is decided by `simp`'s arithmetic simprocs).
An optional `at` clause selects the hypothesis to simplify. The tactic also normalises
costs such as `0 + 1 + 1` to `2`. -/
macro (name := simplifyConfiguration) "config_simp" loc:(location)? : tactic =>
  `(tactic| simp (config := { failIfUnchanged := false }) only [Config.nreg_mk, Config.rreg_mk,
      Config.nmem_mk, Config.rmem_mk, Config.output_mk, Config.pc_mk, Machine.upd_same,
      Machine.upd_other, Machine.upd_upd_same, Machine.upd_eq_self, ne_eq, Nat.succ_ne_zero,
      Nat.zero_ne_one, not_false_eq_true, Nat.reduceEqDiff, Nat.zero_add, Nat.reduceAdd,
      and_true, true_and] $[$loc]?)

/-- Flatten a nested configuration in a hypothesis to a single
`{ pc := …, nreg := upd (upd …) …, … }` (without this the term after `k` instructions would
have printed size exponential in `k`). -/
macro (name := flattenConfigurationAt) "config_flatten_at" h:ident : tactic =>
  `(tactic| simp (config := { failIfUnchanged := false }) only [Config.nreg_mk, Config.rreg_mk,
      Config.nmem_mk, Config.rmem_mk, Config.output_mk, Config.pc_mk, Machine.upd_same,
      Machine.upd_other, Machine.upd_upd_same, ne_eq, Nat.succ_ne_zero, Nat.zero_ne_one,
      not_false_eq_true, Nat.reduceEqDiff] at $h:ident)

/-- On a spec goal `∃ c' k, Exec P W s c c' k ∧ Q c' k`, flatten the starting configuration
`c` only (the postcondition `Q` is left untouched). -/
macro (name := flattenSpec) "spec_flatten" : tactic =>
  `(tactic| try (conv => enter [1, c', 1, k, 1, 4]; simp only [Config.nreg_mk, Config.rreg_mk,
      Config.nmem_mk, Config.rmem_mk, Config.output_mk, Config.pc_mk, Machine.upd_same,
      Machine.upd_other, Machine.upd_upd_same, ne_eq, Nat.succ_ne_zero, Nat.zero_ne_one,
      not_false_eq_true, Nat.reduceEqDiff]))

/-! ### The block tactic

`exec_block` discharges a spec goal `∃ c' k, Exec P W (block [i₁, …, iₖ]) c c' k ∧ Q c' k`.
It needs a hypothesis `WordsBounded W c` for the starting configuration in the local context
(found by `assumption`); the word bound of every later configuration is supplied by
`spec_step`.  Each step tries the per-instruction rules in turn, then flattens the new
configuration (in the goal and in the new word-bound hypothesis); rules with a side
condition (`constN`, `inputSize`, `addN`, `divR`) leave it as a goal, moved behind the main
goal by `rotate_left` so the chain continues.  After the block is exhausted the goals are
the side conditions in program order, then the postcondition `Q c_final k_final` (with
`c_final` flat and `k_final` a sum of literals). -/

/-- One step of `exec_block`: try every instruction rule on the head of the block. -/
macro (name := executeBlockStep) "exec_block_step" : tactic =>
  `(tactic| first
    | refine spec_nil ‹WordsBounded _ _› ?_
    | (refine spec_step (Machine.Exec.copyN ‹WordsBounded _ _› _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.subN ‹WordsBounded _ _› _ _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.loadN ‹WordsBounded _ _› _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.storeN ‹WordsBounded _ _› _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.constR ‹WordsBounded _ _› _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.copyR ‹WordsBounded _ _› _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.addR ‹WordsBounded _ _› _ _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.subR ‹WordsBounded _ _› _ _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.mulR ‹WordsBounded _ _› _ _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.loadR ‹WordsBounded _ _› _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.storeR ‹WordsBounded _ _› _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.outN ‹WordsBounded _ _› _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.divN ‹WordsBounded _ _› _ _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.modN ‹WordsBounded _ _› _ _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.constN ‹WordsBounded _ _› _ _ ?_) (fun _hw => ?_)
       rotate_left; config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.inputSize ‹WordsBounded _ _› _ ?_) (fun _hw => ?_)
       rotate_left; config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.addN ‹WordsBounded _ _› _ _ _ ?_) (fun _hw => ?_)
       rotate_left; config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.mulN ‹WordsBounded _ _› _ _ _ ?_) (fun _hw => ?_)
       rotate_left; config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.readIn ‹WordsBounded _ _› _ _ ?_) (fun _hw => ?_)
       rotate_left; config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.rand ‹WordsBounded _ _› _ _ ?_) (fun _hw => ?_)
       rotate_left; config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.divR ‹WordsBounded _ _› _ _ _ ?_) (fun _hw => ?_)
       rotate_left; config_flatten_at _hw; spec_flatten))

/-- Symbolic execution of a straight-line block on a spec goal; see the module docstring.
Leaves the side conditions (in program order) and then the postcondition goal. -/
macro (name := executeBlock) "exec_block" : tactic =>
  `(tactic| focus ((exec_block_step; repeat exec_block_step); rotate_left))

/-! ### Worked example

The block `nreg 0 := n; nreg 1 := 1; nreg 3 := input[nreg 1]; nreg 2 := nreg 0 + nreg 1`,
executed from any word-bounded `c` whose input words are at most `W`, with `n + 1 ≤ W`. -/

/-- Worked example of the recommended pattern (and a regression test of `exec_block`). -/
theorem exec_block_example (P : Input) (W : ℕ) (hW : P.data.length + 1 ≤ W)
    (hP : ∀ i, P.data.getD i 0 ≤ W) (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W
      (block [.inputSize 0, .constN 1 1, .readIn 3 1, .addN 2 0 1]) c c' k ∧
      k = 4 ∧ c'.nreg 0 = P.data.length ∧ c'.nreg 1 = 1 ∧ c'.nreg 2 = P.data.length + 1 ∧
      c'.nreg 3 = P.data.getD 1 0 ∧
      (∀ r, 4 ≤ r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  · omega
  · omega
  · config_simp; exact hP 1
  · config_simp; omega
  · refine ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp, ?_, rfl, rfl,
      rfl, rfl⟩
    intro r hr
    simp [show r ≠ 0 by omega, show r ≠ 1 by omega, show r ≠ 2 by omega, show r ≠ 3 by omega]

end

end Programs

end WordRAM
