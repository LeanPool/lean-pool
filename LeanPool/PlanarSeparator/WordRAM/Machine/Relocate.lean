/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.WordRAM.Machine.Basic

/-!
# Relocation and linking

* `Instr.relocate off` shifts every jump/branch target by `off`; `Program.relocate` maps it
  over a program.  Straight-line instructions are unchanged (`Instr.relocate_of_isStraight`).
* `SubAt p q base`: the program `p` sits verbatim at address `base` inside `q`
  (`∀ i ins, p[i]? = some ins → q[base + i]? = some ins`).  Lemmas for `[]`, `::`, `++`,
  transitivity, and the two halves of a concatenation.
* `shiftPc off c`: the configuration `c` with its program counter shifted by `off`.
* The relocation theorem `run_relocate`: if `p.relocate off` sits at `off` inside `q` and a
  `k`-step run of `p` from `c` never leaves `p`'s code (the program counter of every
  configuration *before* a step is `< p.length`), then
  `run q P k (shiftPc off c) = (run p P k c).map (shiftPc off)`.  Faults (`halt`, division
  by zero) are reproduced exactly.  `RunsTo.relocate` transfers bounded runs, and
  `AtHalt.relocate` transfers the final `halt`.
-/

namespace WordRAM

namespace Instr

@[expose] public section

/-- Shift every jump/branch target by `off`; other instructions are unchanged. -/
def relocate (off : ℕ) : Instr → Instr
  | .jump l => .jump (l + off)
  | .brLtN a b l => .brLtN a b (l + off)
  | .brLtR a b l => .brLtR a b (l + off)
  | ins => ins

@[simp] theorem relocate_halt (off : ℕ) : (Instr.halt).relocate off = .halt := rfl
@[simp] theorem relocate_jump (off l : ℕ) : (Instr.jump l).relocate off = .jump (l + off) := rfl
@[simp] theorem relocate_brLtN (off a b l : ℕ) :
    (Instr.brLtN a b l).relocate off = .brLtN a b (l + off) := rfl
@[simp] theorem relocate_brLtR (off a b l : ℕ) :
    (Instr.brLtR a b l).relocate off = .brLtR a b (l + off) := rfl

@[simp] theorem relocate_zero (ins : Instr) : ins.relocate 0 = ins := by
  cases ins <;> rfl

theorem relocate_relocate (ins : Instr) (a b : ℕ) :
    (ins.relocate a).relocate b = ins.relocate (a + b) := by
  cases ins <;> simp [relocate, Nat.add_assoc]

/-- Relocation does not touch straight-line instructions. -/
@[simp] theorem relocate_of_isStraight {ins : Instr} (h : ins.IsStraight) (off : ℕ) :
    ins.relocate off = ins := by
  cases ins <;> first | rfl | simp at h

@[simp] theorem isStraight_relocate {ins : Instr} {off : ℕ} :
    (ins.relocate off).IsStraight ↔ ins.IsStraight := by
  cases ins <;> simp [relocate]

end

end Instr

namespace Program

@[expose] public section

/-- Relocate every instruction of a program. -/
def relocate (off : ℕ) (p : Program) : Program := p.map (Instr.relocate off)

@[simp] theorem length_relocate (off : ℕ) (p : Program) : (p.relocate off).length = p.length :=
  List.length_map ..

@[simp] theorem getElem?_relocate (off : ℕ) (p : Program) (i : ℕ) :
    (p.relocate off)[i]? = p[i]?.map (Instr.relocate off) :=
  List.getElem?_map ..

@[simp] theorem relocate_zero (p : Program) : p.relocate 0 = p := by
  rw [relocate, show Instr.relocate 0 = id from funext Instr.relocate_zero, List.map_id]

@[simp] theorem relocate_nil (off : ℕ) : Program.relocate off [] = [] := rfl

@[simp] theorem relocate_cons (off : ℕ) (ins : Instr) (p : Program) :
    Program.relocate off (ins :: p) = ins.relocate off :: p.relocate off := rfl

@[simp] theorem relocate_append (off : ℕ) (p₁ p₂ : Program) :
    (p₁ ++ p₂).relocate off = p₁.relocate off ++ p₂.relocate off :=
  List.map_append ..

end

end Program

namespace Machine

@[expose] public section

/-! ### Placement of a program inside a larger one -/

/-- The program `p` sits verbatim at address `base` inside `q`. -/
def SubAt (p q : Program) (base : ℕ) : Prop :=
  ∀ i ins, p[i]? = some ins → q[base + i]? = some ins

/-- Lookup through a placement. -/
theorem SubAt.lookup {p q : Program} {base : ℕ} (h : SubAt p q base) {i : ℕ} (hi : i < p.length) :
    q[base + i]? = p[i]? := by
  rw [List.getElem?_eq_getElem hi]
  exact h i _ (List.getElem?_eq_getElem hi)

theorem subAt_iff {p q : Program} {base : ℕ} :
    SubAt p q base ↔ ∀ i, i < p.length → q[base + i]? = p[i]? := by
  constructor
  · intro h i hi; exact h.lookup hi
  · intro h i ins hins
    have hi : i < p.length := (List.getElem?_eq_some_iff.mp hins).1
    rw [h i hi, hins]

/-- A nonempty placed program fits inside the host. -/
theorem SubAt.length_le {p q : Program} {base : ℕ} (h : SubAt p q base) (hp : 0 < p.length) :
    base + p.length ≤ q.length := by
  have hl : p.length - 1 < p.length := by omega
  have := h.lookup hl
  rw [List.getElem?_eq_getElem hl] at this
  have := (List.getElem?_eq_some_iff.mp this).1
  omega

@[simp] theorem SubAt.nil (q : Program) (base : ℕ) : SubAt [] q base := by
  intro i ins h; simp at h

theorem SubAt.refl (p : Program) : SubAt p p 0 := by
  intro i ins h; simpa using h

theorem SubAt.cons_iff {ins : Instr} {p q : Program} {base : ℕ} :
    SubAt (ins :: p) q base ↔ q[base]? = some ins ∧ SubAt p q (base + 1) := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 ins rfl, fun i ins' hi => ?_⟩
    have := h (i + 1) ins' (by simpa using hi)
    rw [show base + 1 + i = base + (i + 1) by omega]; exact this
  · rintro ⟨h0, h⟩ i ins' hi
    cases i with
    | zero =>
      obtain rfl := Option.some.inj hi
      simpa using h0
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have := h i ins' hi
      rw [show base + (i + 1) = base + 1 + i by omega]; exact this

theorem SubAt.head {ins : Instr} {p q : Program} {base : ℕ} (h : SubAt (ins :: p) q base) :
    q[base]? = some ins :=
  (SubAt.cons_iff.mp h).1

theorem SubAt.tail {ins : Instr} {p q : Program} {base : ℕ} (h : SubAt (ins :: p) q base) :
    SubAt p q (base + 1) :=
  (SubAt.cons_iff.mp h).2

theorem SubAt.singleton_iff {ins : Instr} {q : Program} {base : ℕ} :
    SubAt [ins] q base ↔ q[base]? = some ins := by
  simp [SubAt.cons_iff]

theorem SubAt.append_iff {p₁ p₂ q : Program} {base : ℕ} :
    SubAt (p₁ ++ p₂) q base ↔ SubAt p₁ q base ∧ SubAt p₂ q (base + p₁.length) := by
  constructor
  · intro h
    refine ⟨fun i ins hi => h i ins ?_, fun i ins hi => ?_⟩
    · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1]; exact hi
    · have := h (p₁.length + i) ins (by
        rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]; exact hi)
      rwa [← Nat.add_assoc] at this
  · rintro ⟨h₁, h₂⟩ i ins hi
    by_cases hlt : i < p₁.length
    · rw [List.getElem?_append_left hlt] at hi; exact h₁ i ins hi
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hi
      have := h₂ _ ins hi
      rwa [Nat.add_assoc, Nat.add_sub_cancel' (Nat.le_of_not_lt hlt)] at this

theorem SubAt.of_append_left {p₁ p₂ q : Program} {base : ℕ} (h : SubAt (p₁ ++ p₂) q base) :
    SubAt p₁ q base :=
  (SubAt.append_iff.mp h).1

theorem SubAt.of_append_right {p₁ p₂ q : Program} {base : ℕ} (h : SubAt (p₁ ++ p₂) q base) :
    SubAt p₂ q (base + p₁.length) :=
  (SubAt.append_iff.mp h).2

/-- The lookup lemma for concatenation. -/
theorem getElem?_append_length_add (p₁ p₂ : Program) (i : ℕ) :
    (p₁ ++ p₂)[p₁.length + i]? = p₂[i]? := by
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- The first half of a concatenation sits at address `0`. -/
theorem SubAt.append_left (p₁ p₂ : Program) : SubAt p₁ (p₁ ++ p₂) 0 := by
  intro i ins hi
  rw [Nat.zero_add, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1]; exact hi

/-- The second half of a concatenation sits at address `p₁.length`. -/
theorem SubAt.append_right (p₁ p₂ : Program) : SubAt p₂ (p₁ ++ p₂) p₁.length := by
  intro i ins hi
  rw [getElem?_append_length_add]; exact hi

theorem SubAt.trans {p q r : Program} {a b : ℕ} (h₁ : SubAt p q a) (h₂ : SubAt q r b) :
    SubAt p r (b + a) := by
  intro i ins hi
  rw [Nat.add_assoc]; exact h₂ _ ins (h₁ i ins hi)

/-- Placement inside a longer program obtained by appending on the right. -/
theorem SubAt.append_right_of {p q r : Program} {base : ℕ} (h : SubAt p q base) :
    SubAt p (q ++ r) base := by
  intro i ins hi
  have := h i ins hi
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp this).1]; exact this

/-- Placement inside a longer program obtained by prepending on the left. -/
theorem SubAt.append_left_of {p q r : Program} {base : ℕ} (h : SubAt p q base) :
    SubAt p (r ++ q) (r.length + base) := by
  intro i ins hi
  rw [Nat.add_assoc, getElem?_append_length_add]; exact h i ins hi

/-! ### Shifting the program counter -/

/-- The configuration `c` with its program counter shifted by `off`. -/
def shiftPc (off : ℕ) (c : Config) : Config := { c with pc := c.pc + off }

@[simp] theorem shiftPc_pc (off : ℕ) (c : Config) : (shiftPc off c).pc = c.pc + off := rfl
@[simp] theorem shiftPc_nreg (off : ℕ) (c : Config) : (shiftPc off c).nreg = c.nreg := rfl
@[simp] theorem shiftPc_rreg (off : ℕ) (c : Config) : (shiftPc off c).rreg = c.rreg := rfl
@[simp] theorem shiftPc_nmem (off : ℕ) (c : Config) : (shiftPc off c).nmem = c.nmem := rfl
@[simp] theorem shiftPc_rmem (off : ℕ) (c : Config) : (shiftPc off c).rmem = c.rmem := rfl
@[simp] theorem shiftPc_output (off : ℕ) (c : Config) : (shiftPc off c).output = c.output := rfl
@[simp] theorem shiftPc_zero (c : Config) : shiftPc 0 c = c := rfl

theorem shiftPc_setPc (off : ℕ) (c : Config) (p : ℕ) :
    shiftPc off { c with pc := p } = { c with pc := p + off } := rfl

@[simp] theorem wordsBounded_shiftPc {W off : ℕ} {c : Config} :
    WordsBounded W (shiftPc off c) ↔ WordsBounded W c := Iff.rfl

theorem shiftPc_injective (off : ℕ) : Function.Injective (shiftPc off) := by
  intro c c' h
  cases c; cases c'
  simp only [shiftPc, Config.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp [Nat.add_right_cancel h1, h2, h3, h4, h5, h6]

/-! ### The relocation theorem -/

/-- One step of `p` at `c` is simulated by one step of `q` at `shiftPc off c`, provided the
relocated instruction sits at the shifted address.  Faults are reproduced. -/
theorem step_relocate {p q : Program} {off : ℕ} {P : Input} {c : Config} {ins : Instr}
    (hp : p[c.pc]? = some ins) (hq : q[c.pc + off]? = some (ins.relocate off)) :
    step q P (shiftPc off c) = (step p P c).map (shiftPc off) := by
  cases ins <;> simp only [step, hp, hq, Instr.relocate, Option.map_some, Option.map_none,
      shiftPc_pc, shiftPc_nreg, shiftPc_rreg, shiftPc_nmem, shiftPc_rmem, shiftPc_output]
  case brLtN a b l =>
    by_cases hab : c.nreg a < c.nreg b
    · simp only [hab, ite_true]; rfl
    · simp only [hab, ite_false, shiftPc]
      simp only [Option.some.injEq, Config.mk.injEq, and_true]
      omega
  case brLtR a b l =>
    by_cases hab : c.rreg a < c.rreg b
    · simp only [hab, ite_true]; rfl
    · simp only [hab, ite_false, shiftPc]
      simp only [Option.some.injEq, Config.mk.injEq, and_true]
      omega
  case divR r a b =>
    by_cases hb : c.rreg b = 0
    · simp only [hb, ite_true, Option.map_none]
    · simp only [hb, ite_false, Option.map_some, shiftPc, Option.some.injEq, Config.mk.injEq,
        and_true]
      omega
  all_goals first
    | rfl
    | (simp only [shiftPc, Option.some.injEq, Config.mk.injEq, and_true]; omega)

/-- Placing `p.relocate off` at address `off` of `q` is the "relocation placement". -/
theorem SubAt.relocate_lookup {p q : Program} {off : ℕ} (h : SubAt (p.relocate off) q off)
    {i : ℕ} {ins : Instr} (hi : p[i]? = some ins) : q[i + off]? = some (ins.relocate off) := by
  rw [Nat.add_comm]
  exact h i _ (by rw [Program.getElem?_relocate, hi]; rfl)

/-- **Relocation.**  If `p.relocate off` sits at `off` inside `q` and the `k`-step run of `p`
from `c` never leaves `p`'s code (the program counter of every configuration at which a step
is taken is `< p.length`), then the run of `q` from the shifted configuration is the shifted
run of `p`, faults included. -/
theorem run_relocate {p q : Program} {off : ℕ} {P : Input} {k : ℕ} {c : Config}
    (hq : SubAt (p.relocate off) q off)
    (hpc : ∀ i, i < k → ∀ c', run p P i c = some c' → c'.pc < p.length) :
    run q P k (shiftPc off c) = (run p P k c).map (shiftPc off) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    have h0 : c.pc < p.length := hpc 0 (Nat.succ_pos _) c rfl
    have hins : p[c.pc]? = some p[c.pc] := List.getElem?_eq_getElem h0
    have hstep := step_relocate (P := P) hins (hq.relocate_lookup hins)
    rw [run_succ, run_succ, hstep]
    cases hs : step p P c with
    | none => rfl
    | some c₁ =>
      simp only [Option.map_some, Option.bind_some]
      exact ih fun i hi c' hc' =>
        hpc (i + 1) (by omega) c' (by rw [run_succ_of_step hs]; exact hc')

/-- Relocation of a successful run. -/
theorem run_relocate_of_run {p q : Program} {off : ℕ} {P : Input} {k : ℕ} {c c' : Config}
    (hq : SubAt (p.relocate off) q off)
    (hpc : ∀ i, i < k → ∀ c'', run p P i c = some c'' → c''.pc < p.length)
    (h : run p P k c = some c') : run q P k (shiftPc off c) = some (shiftPc off c') := by
  rw [run_relocate hq hpc, h]; rfl

/-- Relocation of a bounded run (`RunsTo`). -/
theorem RunsTo.relocate {p q : Program} {off : ℕ} {P : Input} {W k : ℕ} {c c' : Config}
    (hq : SubAt (p.relocate off) q off)
    (hpc : ∀ i, i < k → ∀ c'', run p P i c = some c'' → c''.pc < p.length)
    (h : RunsTo p P W k c c') : RunsTo q P W k (shiftPc off c) (shiftPc off c') := by
  refine ⟨run_relocate_of_run hq hpc h.1, fun i hi => ?_⟩
  obtain ⟨c'', hc'', hw⟩ := h.2 i hi
  refine ⟨shiftPc off c'', ?_, hw⟩
  exact run_relocate_of_run hq (fun j hj => hpc j (by omega)) hc''

/-- A `halt` of `p` at `c` is a `halt` of `q` at the shifted configuration. -/
theorem AtHalt.relocate {p q : Program} {off : ℕ} {c : Config}
    (hq : SubAt (p.relocate off) q off) (h : AtHalt p c) : AtHalt q (shiftPc off c) := by
  unfold AtHalt at *
  rw [shiftPc_pc]
  exact hq.relocate_lookup h

/-- A program placed at `0` with no relocation. -/
theorem SubAt.relocate_zero_iff {p q : Program} : SubAt (p.relocate 0) q 0 ↔ SubAt p q 0 := by
  simp

end

end Machine

end WordRAM
