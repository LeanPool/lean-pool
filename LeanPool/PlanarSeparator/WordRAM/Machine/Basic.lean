/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.WordRAM.Spec

/-!
# Machine basics

Elementary lemmas about the machine of `WordRAM/Spec.lean`:

* `upd` (register/memory update) lemmas;
* one lemma per instruction describing `step` when that instruction is at the
  program counter (`step_halt`, `step_constN`, …, `step_divR`, `step_divR_zero`);
* `run` lemmas (`run_zero`, `run_succ`, `run_add`, `run_succ_right`,
  `run_eq_some_of_le`, …);
* monotonicity of `WordsBounded` and `RunsWithin`;
* frame lemmas: what a `step` leaves unchanged;
* `BoundedRun` / `RunsTo`, the "every visited configuration is word-bounded"
  predicates used to build `RunsWithin` compositionally.
-/

namespace WordRAM

namespace Machine

@[expose] public section

/-! ### `upd` -/

@[simp] theorem upd_same {α : Type} (f : ℕ → α) (i : ℕ) (v : α) : upd f i v i = v := by
  simp [upd]

@[simp] theorem upd_other {α : Type} (f : ℕ → α) (i : ℕ) (v : α) {j : ℕ} (h : j ≠ i) :
    upd f i v j = f j := by
  simp [upd, h]

theorem upd_apply {α : Type} (f : ℕ → α) (i : ℕ) (v : α) (j : ℕ) :
    upd f i v j = if j = i then v else f j := rfl

@[simp] theorem upd_upd_same {α : Type} (f : ℕ → α) (i : ℕ) (v w : α) :
    upd (upd f i v) i w = upd f i w := by
  funext j; by_cases h : j = i <;> simp [upd, h]

theorem upd_upd_comm {α : Type} (f : ℕ → α) {i j : ℕ} (v w : α) (h : i ≠ j) :
    upd (upd f i v) j w = upd (upd f j w) i v := by
  funext k
  simp only [upd]
  by_cases hj : k = j
  · have hi : j ≠ i := Ne.symm h
    simp [hj, hi]
  · simp [hj]

@[simp] theorem upd_eq_self {α : Type} (f : ℕ → α) (i : ℕ) : upd f i (f i) = f := by
  funext j; by_cases h : j = i <;> simp [upd, h]

/-- Bound on all entries after an update. -/
theorem upd_le {f : ℕ → ℕ} {W : ℕ} (hf : ∀ j, f j ≤ W) {i v : ℕ} (hv : v ≤ W) (j : ℕ) :
    upd f i v j ≤ W := by
  by_cases h : j = i <;> simp [upd, h, hv, hf]

/-! ### One lemma per instruction -/

section step
variable {prog : Program} {P : Input} {c : Config}

theorem step_none_of_none (h : prog[c.pc]? = none) : step prog P c = none := by
  simp [step, h]

/-- A program counter outside the program faults. -/
theorem step_none_of_length_le (h : prog.length ≤ c.pc) : step prog P c = none :=
  step_none_of_none (List.getElem?_eq_none h)

theorem step_halt (h : prog[c.pc]? = some .halt) : step prog P c = none := by
  simp [step, h]

theorem step_inputSize {r : ℕ} (h : prog[c.pc]? = some (.inputSize r)) :
    step prog P c = some { c with pc := c.pc + 1, nreg := upd c.nreg r P.data.length } := by
  simp [step, h]

theorem step_constN {r k : ℕ} (h : prog[c.pc]? = some (.constN r k)) :
    step prog P c = some { c with pc := c.pc + 1, nreg := upd c.nreg r k } := by
  simp [step, h]

theorem step_copyN {r a : ℕ} (h : prog[c.pc]? = some (.copyN r a)) :
    step prog P c = some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a) } := by
  simp [step, h]

theorem step_addN {r a b : ℕ} (h : prog[c.pc]? = some (.addN r a b)) :
    step prog P c =
      some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a + c.nreg b) } := by
  simp [step, h]

theorem step_subN {r a b : ℕ} (h : prog[c.pc]? = some (.subN r a b)) :
    step prog P c =
      some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a - c.nreg b) } := by
  simp [step, h]

theorem step_mulN {r a b : ℕ} (h : prog[c.pc]? = some (.mulN r a b)) :
    step prog P c =
      some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a * c.nreg b) } := by
  simp [step, h]

theorem step_divN {r a b : ℕ} (h : prog[c.pc]? = some (.divN r a b)) :
    step prog P c =
      some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a / c.nreg b) } := by
  simp [step, h]

theorem step_modN {r a b : ℕ} (h : prog[c.pc]? = some (.modN r a b)) :
    step prog P c =
      some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a % c.nreg b) } := by
  simp [step, h]

theorem step_loadN {r a : ℕ} (h : prog[c.pc]? = some (.loadN r a)) :
    step prog P c =
      some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nmem (c.nreg a)) } := by
  simp [step, h]

theorem step_storeN {a r : ℕ} (h : prog[c.pc]? = some (.storeN a r)) :
    step prog P c =
      some { c with pc := c.pc + 1, nmem := upd c.nmem (c.nreg a) (c.nreg r) } := by
  simp [step, h]

theorem step_constR {r : ℕ} {z : ℤ} (h : prog[c.pc]? = some (.constR r z)) :
    step prog P c = some { c with pc := c.pc + 1, rreg := upd c.rreg r (z : ℝ) } := by
  simp [step, h]

theorem step_copyR {r a : ℕ} (h : prog[c.pc]? = some (.copyR r a)) :
    step prog P c = some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a) } := by
  simp [step, h]

theorem step_addR {r a b : ℕ} (h : prog[c.pc]? = some (.addR r a b)) :
    step prog P c =
      some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a + c.rreg b) } := by
  simp [step, h]

theorem step_subR {r a b : ℕ} (h : prog[c.pc]? = some (.subR r a b)) :
    step prog P c =
      some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a - c.rreg b) } := by
  simp [step, h]

theorem step_mulR {r a b : ℕ} (h : prog[c.pc]? = some (.mulR r a b)) :
    step prog P c =
      some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a * c.rreg b) } := by
  simp [step, h]

/-- Division with a nonzero divisor. -/
theorem step_divR {r a b : ℕ} (h : prog[c.pc]? = some (.divR r a b)) (hb : c.rreg b ≠ 0) :
    step prog P c =
      some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a / c.rreg b) } := by
  simp [step, h, hb]

/-- Division by zero faults. -/
theorem step_divR_zero {r a b : ℕ} (h : prog[c.pc]? = some (.divR r a b)) (hb : c.rreg b = 0) :
    step prog P c = none := by
  simp [step, h, hb]

theorem step_loadR {r a : ℕ} (h : prog[c.pc]? = some (.loadR r a)) :
    step prog P c =
      some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rmem (c.nreg a)) } := by
  simp [step, h]

theorem step_storeR {a r : ℕ} (h : prog[c.pc]? = some (.storeR a r)) :
    step prog P c =
      some { c with pc := c.pc + 1, rmem := upd c.rmem (c.nreg a) (c.rreg r) } := by
  simp [step, h]

theorem step_readIn {r a : ℕ} (h : prog[c.pc]? = some (.readIn r a)) :
    step prog P c =
      some { c with pc := c.pc + 1, nreg := upd c.nreg r (P.data.getD (c.nreg a) 0) } := by
  simp [step, h]

theorem step_rand {r a : ℕ} (h : prog[c.pc]? = some (.rand r a)) :
    step prog P c =
      some { c with pc := c.pc + 1, nreg := upd c.nreg r (P.tape (c.nreg a)) } := by
  simp [step, h]

theorem step_jump {l : ℕ} (h : prog[c.pc]? = some (.jump l)) :
    step prog P c = some { c with pc := l } := by
  simp [step, h]

theorem step_brLtN {a b l : ℕ} (h : prog[c.pc]? = some (.brLtN a b l)) :
    step prog P c = some { c with pc := if c.nreg a < c.nreg b then l else c.pc + 1 } := by
  simp [step, h]

theorem step_brLtN_true {a b l : ℕ} (h : prog[c.pc]? = some (.brLtN a b l))
    (ht : c.nreg a < c.nreg b) : step prog P c = some { c with pc := l } := by
  simp [step, h, ht]

theorem step_brLtN_false {a b l : ℕ} (h : prog[c.pc]? = some (.brLtN a b l))
    (ht : ¬ c.nreg a < c.nreg b) : step prog P c = some { c with pc := c.pc + 1 } := by
  simp [step, h, ht]

theorem step_brLtR {a b l : ℕ} (h : prog[c.pc]? = some (.brLtR a b l)) :
    step prog P c = some { c with pc := if c.rreg a < c.rreg b then l else c.pc + 1 } := by
  simp [step, h]

theorem step_brLtR_true {a b l : ℕ} (h : prog[c.pc]? = some (.brLtR a b l))
    (ht : c.rreg a < c.rreg b) : step prog P c = some { c with pc := l } := by
  simp [step, h, ht]

theorem step_brLtR_false {a b l : ℕ} (h : prog[c.pc]? = some (.brLtR a b l))
    (ht : ¬ c.rreg a < c.rreg b) : step prog P c = some { c with pc := c.pc + 1 } := by
  simp [step, h, ht]

theorem step_outN {a : ℕ} (h : prog[c.pc]? = some (.outN a)) :
    step prog P c =
      some { c with pc := c.pc + 1, output := c.output ++ [c.nreg a] } := by
  simp [step, h]

end step

/-! ### `run` -/

section run
variable {prog : Program} {P : Input}

@[simp] theorem run_zero (c : Config) : run prog P 0 c = some c := rfl

theorem run_succ (k : ℕ) (c : Config) :
    run prog P (k + 1) c = (step prog P c).bind (run prog P k) := rfl

theorem run_one : run prog P 1 = step prog P := by
  funext c; rw [run_succ]; cases step prog P c <;> rfl

theorem run_succ_of_step {k : ℕ} {c c₁ : Config} (h : step prog P c = some c₁) :
    run prog P (k + 1) c = run prog P k c₁ := by
  rw [run_succ, h, Option.bind_some]

theorem run_succ_of_step_none {k : ℕ} {c : Config} (h : step prog P c = none) :
    run prog P (k + 1) c = none := by
  rw [run_succ, h, Option.bind_none]

/-- Running `a + b` steps is running `a` steps and then `b` steps. -/
theorem run_add (a b : ℕ) (c : Config) :
    run prog P (a + b) c = (run prog P a c).bind (run prog P b) := by
  induction a generalizing c with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_add, run_succ, run_succ, Option.bind_assoc]
    cases step prog P c with
    | none => rfl
    | some c₁ => simp [ih]

/-- Peeling off the last step. -/
theorem run_succ_right (k : ℕ) (c : Config) :
    run prog P (k + 1) c = (run prog P k c).bind (step prog P) := by
  rw [run_add, run_one]

theorem run_add_of_run {a b : ℕ} {c c₁ : Config} (h : run prog P a c = some c₁) :
    run prog P (a + b) c = run prog P b c₁ := by
  rw [run_add, h, Option.bind_some]

/-- If a run of `k` steps succeeds, so does every shorter run from the same start. -/
theorem run_eq_some_of_le {k : ℕ} {c c' : Config} (h : run prog P k c = some c') {i : ℕ}
    (hi : i ≤ k) : ∃ c'', run prog P i c = some c'' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [run_add, Option.bind_eq_some_iff] at h
  obtain ⟨c'', h1, _⟩ := h
  exact ⟨c'', h1⟩

/-- The intermediate configuration after `i ≤ k` steps determines the rest of the run. -/
theorem run_eq_of_le {k : ℕ} {c c' : Config} (h : run prog P k c = some c') {i : ℕ}
    (hi : i ≤ k) : ∃ c'', run prog P i c = some c'' ∧ run prog P (k - i) c'' = some c' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [run_add, Option.bind_eq_some_iff] at h
  obtain ⟨c'', h1, h2⟩ := h
  exact ⟨c'', h1, by simpa using h2⟩

end run

/-! ### Word bounds and `RunsWithin` -/

theorem WordsBounded.mono {W W' : ℕ} {c : Config} (h : WordsBounded W c) (hW : W ≤ W') :
    WordsBounded W' c :=
  ⟨fun r => (h.1 r).trans hW, fun a => (h.2 a).trans hW⟩

theorem wordsBounded_initConfig (W : ℕ) : WordsBounded W initConfig :=
  ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩

/-- `WordsBounded` does not look at the program counter, the real registers, the real
memory or the output. -/
theorem wordsBounded_iff {W : ℕ} {c : Config} :
    WordsBounded W c ↔ (∀ r, c.nreg r ≤ W) ∧ (∀ a, c.nmem a ≤ W) := Iff.rfl

@[simp] theorem wordsBounded_setPc {W : ℕ} {c : Config} {p : ℕ} :
    WordsBounded W { c with pc := p } ↔ WordsBounded W c := Iff.rfl

theorem WordsBounded.nreg {W : ℕ} {c : Config} (h : WordsBounded W c) (r : ℕ) : c.nreg r ≤ W :=
  h.1 r

theorem WordsBounded.nmem {W : ℕ} {c : Config} (h : WordsBounded W c) (a : ℕ) : c.nmem a ≤ W :=
  h.2 a

/-- Updating a natural register with a value `≤ W` preserves the word bound. -/
theorem WordsBounded.upd_nreg {W : ℕ} {c : Config} (h : WordsBounded W c) {r v : ℕ}
    (hv : v ≤ W) (pc : ℕ) : WordsBounded W { c with pc := pc, nreg := upd c.nreg r v } :=
  ⟨upd_le h.1 hv, h.2⟩

/-- Updating a natural memory cell with a value `≤ W` preserves the word bound. -/
theorem WordsBounded.upd_nmem {W : ℕ} {c : Config} (h : WordsBounded W c) {a v : ℕ}
    (hv : v ≤ W) (pc : ℕ) : WordsBounded W { c with pc := pc, nmem := upd c.nmem a v } :=
  ⟨h.1, upd_le h.2 hv⟩

/-- Changing only the real registers preserves the word bound. -/
theorem WordsBounded.set_rreg {W : ℕ} {c : Config} (h : WordsBounded W c) (f : ℕ → ℝ) (pc : ℕ) :
    WordsBounded W { c with pc := pc, rreg := f } := h

/-- Changing only the real memory preserves the word bound. -/
theorem WordsBounded.set_rmem {W : ℕ} {c : Config} (h : WordsBounded W c) (f : ℕ → ℝ) (pc : ℕ) :
    WordsBounded W { c with pc := pc, rmem := f } := h

/-- Changing only the output preserves the word bound. -/
theorem WordsBounded.set_output {W : ℕ} {c : Config} (h : WordsBounded W c)
    (out : List ℕ) (pc : ℕ) : WordsBounded W { c with pc := pc, output := out } := h

theorem RunsWithin.mono_W {prog : Program} {P : Input} {W W' steps : ℕ}
    {out : List ℕ} (h : RunsWithin prog P W steps out) (hW : W ≤ W') :
    RunsWithin prog P W' steps out := by
  obtain ⟨k, hk, hb, hf⟩ := h
  refine ⟨k, hk, fun i hi => ?_, hf⟩
  obtain ⟨c, hc, hw⟩ := hb i hi
  exact ⟨c, hc, WordsBounded.mono hw hW⟩

theorem RunsWithin.mono_steps {prog : Program} {P : Input} {W steps steps' : ℕ}
    {out : List ℕ} (h : RunsWithin prog P W steps out) (hs : steps ≤ steps') :
    RunsWithin prog P W steps' out := by
  obtain ⟨k, hk, hb, hf⟩ := h
  exact ⟨k, hk.trans hs, hb, hf⟩

theorem RunsWithin.mono {prog : Program} {P : Input} {W W' steps steps' : ℕ}
    {out : List ℕ} (h : RunsWithin prog P W steps out) (hW : W ≤ W')
    (hs : steps ≤ steps') : RunsWithin prog P W' steps' out :=
  RunsWithin.mono_steps (RunsWithin.mono_W h hW) hs

/-! ### Bounded runs

`BoundedRun prog P W k c` says that the `k`-step run from `c` succeeds and every configuration
visited (including the first and the last) is `WordsBounded W`.  `RunsTo` adds the final
configuration.  These compose (`RunsTo.trans`) and give `RunsWithin` directly
(`runsWithin_of_runsTo`). -/

/-- The `k`-step run from `c` does not fault and every visited configuration is
`WordsBounded W`. -/
def BoundedRun (prog : Program) (P : Input) (W k : ℕ) (c : Config) : Prop :=
  ∀ i, i ≤ k → ∃ c', run prog P i c = some c' ∧ WordsBounded W c'

/-- The `k`-step run from `c` ends in `c'`, and every visited configuration is `WordsBounded W`. -/
def RunsTo (prog : Program) (P : Input) (W k : ℕ) (c c' : Config) : Prop :=
  run prog P k c = some c' ∧ BoundedRun prog P W k c

section runsTo
variable {prog : Program} {P : Input} {W : ℕ}

theorem BoundedRun.wb_start {k : ℕ} {c : Config} (h : BoundedRun prog P W k c) :
    WordsBounded W c := by
  obtain ⟨c', hc, hw⟩ := h 0 (Nat.zero_le _)
  simp only [run_zero, Option.some.injEq] at hc
  exact hc ▸ hw

theorem BoundedRun.mono_k {k k' : ℕ} {c : Config} (h : BoundedRun prog P W k c) (hk : k' ≤ k) :
    BoundedRun prog P W k' c :=
  fun i hi => h i (hi.trans hk)

theorem BoundedRun.mono_W {k W' : ℕ} {c : Config} (h : BoundedRun prog P W k c) (hW : W ≤ W') :
    BoundedRun prog P W' k c := by
  intro i hi
  obtain ⟨c', hc, hw⟩ := h i hi
  exact ⟨c', hc, WordsBounded.mono hw hW⟩

theorem BoundedRun.zero {c : Config} (h : WordsBounded W c) : BoundedRun prog P W 0 c := by
  intro i hi
  obtain rfl : i = 0 := Nat.le_zero.mp hi
  exact ⟨c, rfl, h⟩

theorem BoundedRun.cons {k : ℕ} {c c₁ : Config} (hw : WordsBounded W c)
    (hs : step prog P c = some c₁) (h : BoundedRun prog P W k c₁) :
    BoundedRun prog P W (k + 1) c := by
  intro i hi
  cases i with
  | zero => exact ⟨c, rfl, hw⟩
  | succ i =>
    obtain ⟨c', hc, hw'⟩ := h i (Nat.le_of_succ_le_succ hi)
    exact ⟨c', by rw [run_succ_of_step hs, hc], hw'⟩

theorem BoundedRun.add {a b : ℕ} {c c₁ : Config} (h₁ : BoundedRun prog P W a c)
    (hr : run prog P a c = some c₁) (h₂ : BoundedRun prog P W b c₁) :
    BoundedRun prog P W (a + b) c := by
  intro i hi
  by_cases hia : i ≤ a
  · exact h₁ i hia
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_le hia)
    obtain ⟨c', hc, hw⟩ := h₂ d (by omega)
    exact ⟨c', by rw [run_add_of_run hr, hc], hw⟩

theorem BoundedRun.run_eq_some {k : ℕ} {c : Config} (h : BoundedRun prog P W k c) :
    ∃ c', run prog P k c = some c' ∧ WordsBounded W c' :=
  h k le_rfl

theorem RunsTo.run_eq {k : ℕ} {c c' : Config} (h : RunsTo prog P W k c c') :
    run prog P k c = some c' := h.1

theorem RunsTo.bounded {k : ℕ} {c c' : Config} (h : RunsTo prog P W k c c') :
    BoundedRun prog P W k c := h.2

theorem RunsTo.wb_start {k : ℕ} {c c' : Config} (h : RunsTo prog P W k c c') :
    WordsBounded W c := h.2.wb_start

theorem RunsTo.wb_end {k : ℕ} {c c' : Config} (h : RunsTo prog P W k c c') :
    WordsBounded W c' := by
  obtain ⟨c'', hc, hw⟩ := h.2 k le_rfl
  rw [h.1, Option.some.injEq] at hc
  exact hc ▸ hw

theorem RunsTo.zero {c : Config} (h : WordsBounded W c) : RunsTo prog P W 0 c c :=
  ⟨rfl, BoundedRun.zero h⟩

/-- Prepend one step. -/
theorem RunsTo.cons {k : ℕ} {c c₁ c' : Config} (hw : WordsBounded W c)
    (hs : step prog P c = some c₁) (h : RunsTo prog P W k c₁ c') :
    RunsTo prog P W (k + 1) c c' :=
  ⟨by rw [run_succ_of_step hs, h.1], BoundedRun.cons hw hs h.2⟩

/-- A single step between two bounded configurations. -/
theorem RunsTo.single {c c₁ : Config} (hw : WordsBounded W c) (hw₁ : WordsBounded W c₁)
    (hs : step prog P c = some c₁) : RunsTo prog P W 1 c c₁ :=
  RunsTo.cons hw hs (RunsTo.zero hw₁)

theorem RunsTo.trans {a b : ℕ} {c c₁ c' : Config} (h₁ : RunsTo prog P W a c c₁)
    (h₂ : RunsTo prog P W b c₁ c') : RunsTo prog P W (a + b) c c' :=
  ⟨by rw [run_add_of_run h₁.1, h₂.1], BoundedRun.add h₁.2 h₁.1 h₂.2⟩

/-- Append one step. -/
theorem RunsTo.snoc {k : ℕ} {c c₁ c' : Config} (h : RunsTo prog P W k c c₁)
    (hs : step prog P c₁ = some c') (hw : WordsBounded W c') :
    RunsTo prog P W (k + 1) c c' :=
  h.trans (RunsTo.single h.wb_end hw hs)

/-- Replace the step count by an equal one (for arithmetic normalisation). -/
theorem RunsTo.cast {k k' : ℕ} {c c' : Config} (h : RunsTo prog P W k c c') (hk : k = k') :
    RunsTo prog P W k' c c' := hk ▸ h

theorem RunsTo.mono_W {k W' : ℕ} {c c' : Config} (h : RunsTo prog P W k c c') (hW : W ≤ W') :
    RunsTo prog P W' k c c' :=
  ⟨h.1, BoundedRun.mono_W h.2 hW⟩

/-- Steps are deterministic: two runs of the same length from the same start agree. -/
theorem RunsTo.unique {k : ℕ} {c c₁ c₂ : Config} (h₁ : RunsTo prog P W k c c₁)
    (h₂ : RunsTo prog P W k c c₂) : c₁ = c₂ := by
  have := h₁.1.symm.trans h₂.1
  exact Option.some.inj this

/-- `RunsWithin` from a bounded run of `initConfig` ending at a `halt`. -/
theorem runsWithin_of_runsTo {k : ℕ} {c : Config} (h : RunsTo prog P W k initConfig c)
    (hh : AtHalt prog c) : RunsWithin prog P W (k + 1) c.output :=
  ⟨k, le_rfl, h.2, c, h.1, hh, rfl⟩

/-- `RunsWithin` unfolded through `RunsTo`. -/
theorem runsWithin_iff {steps : ℕ} {out : List ℕ} :
    RunsWithin prog P W steps out ↔
      ∃ k c, k + 1 ≤ steps ∧ RunsTo prog P W k initConfig c ∧ AtHalt prog c ∧
        c.output = out := by
  constructor
  · rintro ⟨k, hk, hb, c, hc, hh, ho⟩
    exact ⟨k, c, hk, ⟨hc, hb⟩, hh, ho⟩
  · rintro ⟨k, c, hk, ⟨hc, hb⟩, hh, ho⟩
    exact ⟨k, hk, hb, c, hc, hh, ho⟩

end runsTo

end

end Machine

namespace Instr

@[expose] public section

/-- The natural register written by an instruction, if any. -/
def nDest : Instr → Option ℕ
  | .inputSize r => some r
  | .constN r _ => some r
  | .copyN r _ => some r
  | .addN r _ _ => some r
  | .subN r _ _ => some r
  | .mulN r _ _ => some r
  | .divN r _ _ => some r
  | .modN r _ _ => some r
  | .loadN r _ => some r
  | .readIn r _ => some r
  | .rand r _ => some r
  | _ => none

/-- The real register written by an instruction, if any. -/
def rDest : Instr → Option ℕ
  | .constR r _ => some r
  | .copyR r _ => some r
  | .addR r _ _ => some r
  | .subR r _ _ => some r
  | .mulR r _ _ => some r
  | .divR r _ _ => some r
  | .loadR r _ => some r
  | _ => none

/-- Does the instruction write natural memory? -/
def writesNMem : Instr → Bool
  | .storeN _ _ => true
  | _ => false

/-- Does the instruction write real memory? -/
def writesRMem : Instr → Bool
  | .storeR _ _ => true
  | _ => false

/-- Is the instruction an `outN`? -/
def isEmit : Instr → Bool
  | .outN _ => true
  | _ => false

/-- Is the instruction a control instruction (`halt`, `jump`, `brLtN`, `brLtR`)? -/
def isControl : Instr → Bool
  | .halt => true
  | .jump _ => true
  | .brLtN _ _ _ => true
  | .brLtR _ _ _ => true
  | _ => false

/-- A straight-line instruction: anything but `halt`, `jump`, `brLtN`, `brLtR`.  Straight-line
instructions always advance the program counter by one and never depend on it. -/
def IsStraight (ins : Instr) : Prop := ins.isControl = false

@[simp] theorem isStraight_halt : ¬ IsStraight .halt := by simp [IsStraight, isControl]
@[simp] theorem isStraight_jump (l : ℕ) : ¬ IsStraight (.jump l) := by simp [IsStraight, isControl]
@[simp] theorem isStraight_brLtN (a b l : ℕ) : ¬ IsStraight (.brLtN a b l) := by
  simp [IsStraight, isControl]
@[simp] theorem isStraight_brLtR (a b l : ℕ) : ¬ IsStraight (.brLtR a b l) := by
  simp [IsStraight, isControl]
theorem isStraight_inputSize (r : ℕ) : IsStraight (.inputSize r) := rfl
theorem isStraight_constN (r k : ℕ) : IsStraight (.constN r k) := rfl
theorem isStraight_copyN (r a : ℕ) : IsStraight (.copyN r a) := rfl
theorem isStraight_addN (r a b : ℕ) : IsStraight (.addN r a b) := rfl
theorem isStraight_subN (r a b : ℕ) : IsStraight (.subN r a b) := rfl
theorem isStraight_mulN (r a b : ℕ) : IsStraight (.mulN r a b) := rfl
theorem isStraight_divN (r a b : ℕ) : IsStraight (.divN r a b) := rfl
theorem isStraight_modN (r a b : ℕ) : IsStraight (.modN r a b) := rfl
theorem isStraight_loadN (r a : ℕ) : IsStraight (.loadN r a) := rfl
theorem isStraight_storeN (a r : ℕ) : IsStraight (.storeN a r) := rfl
theorem isStraight_constR (r : ℕ) (z : ℤ) : IsStraight (.constR r z) := rfl
theorem isStraight_copyR (r a : ℕ) : IsStraight (.copyR r a) := rfl
theorem isStraight_addR (r a b : ℕ) : IsStraight (.addR r a b) := rfl
theorem isStraight_subR (r a b : ℕ) : IsStraight (.subR r a b) := rfl
theorem isStraight_mulR (r a b : ℕ) : IsStraight (.mulR r a b) := rfl
theorem isStraight_divR (r a b : ℕ) : IsStraight (.divR r a b) := rfl
theorem isStraight_loadR (r a : ℕ) : IsStraight (.loadR r a) := rfl
theorem isStraight_storeR (a r : ℕ) : IsStraight (.storeR a r) := rfl
theorem isStraight_readIn (r a : ℕ) : IsStraight (.readIn r a) := rfl
theorem isStraight_rand (r a : ℕ) : IsStraight (.rand r a) := rfl
theorem isStraight_outN (a : ℕ) : IsStraight (.outN a) := rfl

end

end Instr

namespace Machine

@[expose] public section

/-! ### Frame lemmas

What a single step leaves unchanged, classified by the instruction executed. -/

section frame
variable {prog : Program} {P : Input} {c c' : Config} {ins : Instr}

/-- A straight-line instruction advances the program counter by exactly one. -/
theorem step_pc_of_isStraight (h : prog[c.pc]? = some ins) (hs : ins.IsStraight)
    (hst : step prog P c = some c') : c'.pc = c.pc + 1 := by
  cases ins <;> simp [Instr.IsStraight, Instr.isControl] at hs <;>
    simp only [step, h] at hst <;> first
    | (obtain rfl := Option.some.inj hst; rfl)
    | (split at hst
       · exact nomatch hst
       · obtain rfl := Option.some.inj hst; rfl)

/-- Natural registers other than the destination are unchanged. -/
theorem step_nreg_frame (h : prog[c.pc]? = some ins) (hst : step prog P c = some c') {j : ℕ}
    (hj : ins.nDest ≠ some j) : c'.nreg j = c.nreg j := by
  cases ins <;> simp only [step, h] at hst <;> first
    | (split at hst
       · cases hst
       · cases hst; rfl)
    | (obtain rfl := Option.some.inj hst; simp_all [Instr.nDest, upd, Ne.symm])
    | exact nomatch hst

/-- Real registers other than the destination are unchanged. -/
theorem step_rreg_frame (h : prog[c.pc]? = some ins) (hst : step prog P c = some c') {j : ℕ}
    (hj : ins.rDest ≠ some j) : c'.rreg j = c.rreg j := by
  cases ins <;> simp only [step, h] at hst <;> first
    | (split at hst
       · cases hst
       · cases hst; simp_all [Instr.rDest, upd, Ne.symm])
    | (obtain rfl := Option.some.inj hst; simp_all [Instr.rDest, upd, Ne.symm])
    | exact nomatch hst

/-- Natural memory is unchanged unless the instruction is `storeN`. -/
theorem step_nmem_frame (h : prog[c.pc]? = some ins) (hst : step prog P c = some c')
    (hw : ins.writesNMem = false) : c'.nmem = c.nmem := by
  cases ins <;> simp only [step, h] at hst <;> first
    | (split at hst
       · cases hst
       · cases hst; simp_all [Instr.writesNMem])
    | (obtain rfl := Option.some.inj hst; simp_all [Instr.writesNMem])
    | exact nomatch hst

/-- Real memory is unchanged unless the instruction is `storeR`. -/
theorem step_rmem_frame (h : prog[c.pc]? = some ins) (hst : step prog P c = some c')
    (hw : ins.writesRMem = false) : c'.rmem = c.rmem := by
  cases ins <;> simp only [step, h] at hst <;> first
    | (split at hst
       · cases hst
       · cases hst; simp_all [Instr.writesRMem])
    | (obtain rfl := Option.some.inj hst; simp_all [Instr.writesRMem])
    | exact nomatch hst

/-- The output is unchanged unless the instruction is `outN`. -/
theorem step_output_frame (h : prog[c.pc]? = some ins) (hst : step prog P c = some c')
    (hw : ins.isEmit = false) : c'.output = c.output := by
  cases ins <;> simp only [step, h] at hst <;> first
    | (split at hst
       · cases hst
       · cases hst; simp_all [Instr.isEmit])
    | (obtain rfl := Option.some.inj hst; simp_all [Instr.isEmit])
    | exact nomatch hst

/-- The output only ever grows: a step appends a (possibly empty) list. -/
theorem step_output_append (hst : step prog P c = some c') :
    ∃ l, c'.output = c.output ++ l := by
  rcases hins : prog[c.pc]? with _ | ins
  · rw [step_none_of_none hins] at hst; exact nomatch hst
  · cases ins <;> simp only [step, hins] at hst <;> first
      | (split at hst
         · cases hst
         · cases hst; exact ⟨[], (List.append_nil _).symm⟩)
      | (obtain rfl := Option.some.inj hst
         first | exact ⟨[], (List.append_nil _).symm⟩ | exact ⟨_, rfl⟩)
      | exact nomatch hst

/-- Over a whole run the output only grows. -/
theorem run_output_append {k : ℕ} (h : run prog P k c = some c') :
    ∃ l, c'.output = c.output ++ l := by
  induction k generalizing c with
  | zero => exact ⟨[], by simp_all⟩
  | succ k ih =>
    rw [run_succ, Option.bind_eq_some_iff] at h
    obtain ⟨c₁, hs, hr⟩ := h
    obtain ⟨l₁, hl₁⟩ := step_output_append hs
    obtain ⟨l₂, hl₂⟩ := ih hr
    exact ⟨l₁ ++ l₂, by rw [hl₂, hl₁, List.append_assoc]⟩

end frame

end

end Machine

end WordRAM
