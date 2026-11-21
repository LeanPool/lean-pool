/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.WordRAM

/-!
# Syntactic frames of structured programs

For a statement `s` of the structured language of `WordRAM/Machine/Structured.lean`:

* `Stmt.wr s r`: some instruction of `s` writes the natural register `r`;
* `Stmt.st s`: some instruction of `s` stores into the natural memory;
* `Stmt.ou s`: some instruction of `s` prints.

An execution of `s` keeps every register that `s` does not write (`Exec.nreg_of_wr`), the memory
if `s` has no store (`Exec.nmem_of_st`), and the output if `s` does not print
(`Exec.output_of_ou`). These flags are computed by `decide` for a given program.
-/

@[expose] public section

namespace WordRAM

namespace Instr

/-- The instruction writes the natural register `r`. -/
def wr (r : ℕ) : Instr → Bool
  | .inputSize a | .constN a _ | .copyN a _ | .addN a _ _ | .subN a _ _ | .mulN a _ _
  | .divN a _ _ | .modN a _ _ | .loadN a _ | .readIn a _ | .rand a _ => a == r
  | _ => false

/-- The register the instruction writes (`0` if it writes none). -/
def wreg : Instr → ℕ
  | .inputSize a | .constN a _ | .copyN a _ | .addN a _ _ | .subN a _ _ | .mulN a _ _
  | .divN a _ _ | .modN a _ _ | .loadN a _ | .readIn a _ | .rand a _ => a
  | _ => 0

theorem wr_of_wreg {i : Instr} {r : ℕ} (h : i.wreg < r) : i.wr r = false := by
  cases i <;> simp [wreg, wr] at h ⊢ <;> omega

/-- The instruction stores into the natural memory. -/
def st : Instr → Bool
  | .storeN _ _ => true
  | _ => false

/-- The instruction prints. -/
def ou : Instr → Bool
  | .outN _ => true
  | _ => false

variable {P : Input} {c c' : Config}

theorem nreg_of_wr {i : Instr} {r : ℕ} (h : i.effect P c = some c') (hr : i.wr r = false) :
    c'.nreg r = c.nreg r := by
  cases i <;> simp only [effect, wr, Option.some.injEq, reduceCtorEq, beq_eq_false_iff_ne]
    at h hr <;> first
    | (subst c'; first | rfl | exact Machine.upd_other _ _ _ (Ne.symm hr))
    | (split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
       subst c'; rfl)

theorem nmem_of_st {i : Instr} (h : i.effect P c = some c') (hs : i.st = false) :
    c'.nmem = c.nmem := by
  cases i <;> simp only [effect, st, Option.some.injEq, reduceCtorEq] at h hs <;> first
    | (subst c'; rfl)
    | (split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
       subst c'; rfl)

theorem output_of_ou {i : Instr} (h : i.effect P c = some c') (hs : i.ou = false) :
    c'.output = c.output := by
  cases i <;> simp only [effect, ou, Option.some.injEq, reduceCtorEq] at h hs <;> first
    | (subst c'; rfl)
    | (split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
       subst c'; rfl)

end Instr

namespace Machine

namespace Stmt

/-- Some instruction of the statement writes the register `r`. -/
def wr (r : ℕ) : Stmt → Bool
  | .skip => false
  | .instr i => i.wr r
  | .seq s t => wr r s || wr r t
  | .ifLtN _ _ s t | .ifLtR _ _ s t => wr r s || wr r t
  | .whileLtN _ _ s | .whileLtR _ _ s => wr r s

/-- The largest register written by the statement (`0` if none). -/
def wmax : Stmt → ℕ
  | .skip => 0
  | .instr i => i.wreg
  | .seq s t => max (wmax s) (wmax t)
  | .ifLtN _ _ s t | .ifLtR _ _ s t => max (wmax s) (wmax t)
  | .whileLtN _ _ s | .whileLtR _ _ s => wmax s

theorem wr_of_wmax {s : Stmt} {r : ℕ} (h : s.wmax < r) : s.wr r = false := by
  induction s with
  | skip => rfl
  | instr i => exact Instr.wr_of_wreg h
  | seq s t ihs iht =>
    simp only [wmax, max_lt_iff] at h; simp [wr, ihs h.1, iht h.2]
  | ifLtN _ _ s t ihs iht =>
    simp only [wmax, max_lt_iff] at h; simp [wr, ihs h.1, iht h.2]
  | ifLtR _ _ s t ihs iht =>
    simp only [wmax, max_lt_iff] at h; simp [wr, ihs h.1, iht h.2]
  | whileLtN _ _ s ih => exact ih h
  | whileLtR _ _ s ih => exact ih h

/-- Some instruction of the statement stores into the memory. -/
def st : Stmt → Bool
  | .skip => false
  | .instr i => i.st
  | .seq s t => st s || st t
  | .ifLtN _ _ s t | .ifLtR _ _ s t => st s || st t
  | .whileLtN _ _ s | .whileLtR _ _ s => st s

/-- Some instruction of the statement prints. -/
def ou : Stmt → Bool
  | .skip => false
  | .instr i => i.ou
  | .seq s t => ou s || ou t
  | .ifLtN _ _ s t | .ifLtR _ _ s t => ou s || ou t
  | .whileLtN _ _ s | .whileLtR _ _ s => ou s

end Stmt

namespace Exec

variable {P : Input} {W : ℕ}

/-- **Register frame.** A register the statement never writes is kept. -/
theorem nreg_of_wr {s : Stmt} {c c' : Config} {k : ℕ} (h : Exec P W s c c' k) {r : ℕ}
    (hr : s.wr r = false) : c'.nreg r = c.nreg r := by
  induction h with
  | skip _ => rfl
  | instr _ he _ _ => exact Instr.nreg_of_wr he hr
  | seq _ _ ih₁ ih₂ =>
    simp only [Stmt.wr, Bool.or_eq_false_iff] at hr
    rw [ih₂ hr.2, ih₁ hr.1]
  | ifLtN_true _ _ ih => simp only [Stmt.wr, Bool.or_eq_false_iff] at hr; exact ih hr.1
  | ifLtN_false _ _ ih => simp only [Stmt.wr, Bool.or_eq_false_iff] at hr; exact ih hr.2
  | ifLtR_true _ _ ih => simp only [Stmt.wr, Bool.or_eq_false_iff] at hr; exact ih hr.1
  | ifLtR_false _ _ ih => simp only [Stmt.wr, Bool.or_eq_false_iff] at hr; exact ih hr.2
  | whileLtN_false _ _ => rfl
  | whileLtN_true _ _ _ ih₁ ih₂ => rw [ih₂ hr, ih₁ hr]
  | whileLtR_false _ _ => rfl
  | whileLtR_true _ _ _ ih₁ ih₂ => rw [ih₂ hr, ih₁ hr]

/-- **Memory frame.** A statement without stores keeps the memory. -/
theorem nmem_of_st {s : Stmt} {c c' : Config} {k : ℕ} (h : Exec P W s c c' k)
    (hs : s.st = false) : c'.nmem = c.nmem := by
  induction h with
  | skip _ => rfl
  | instr _ he _ _ => exact Instr.nmem_of_st he hs
  | seq _ _ ih₁ ih₂ =>
    simp only [Stmt.st, Bool.or_eq_false_iff] at hs
    rw [ih₂ hs.2, ih₁ hs.1]
  | ifLtN_true _ _ ih => simp only [Stmt.st, Bool.or_eq_false_iff] at hs; exact ih hs.1
  | ifLtN_false _ _ ih => simp only [Stmt.st, Bool.or_eq_false_iff] at hs; exact ih hs.2
  | ifLtR_true _ _ ih => simp only [Stmt.st, Bool.or_eq_false_iff] at hs; exact ih hs.1
  | ifLtR_false _ _ ih => simp only [Stmt.st, Bool.or_eq_false_iff] at hs; exact ih hs.2
  | whileLtN_false _ _ => rfl
  | whileLtN_true _ _ _ ih₁ ih₂ => rw [ih₂ hs, ih₁ hs]
  | whileLtR_false _ _ => rfl
  | whileLtR_true _ _ _ ih₁ ih₂ => rw [ih₂ hs, ih₁ hs]

/-- **Output frame.** A statement that does not print keeps the output. -/
theorem output_of_ou {s : Stmt} {c c' : Config} {k : ℕ} (h : Exec P W s c c' k)
    (hs : s.ou = false) : c'.output = c.output := by
  induction h with
  | skip _ => rfl
  | instr _ he _ _ => exact Instr.output_of_ou he hs
  | seq _ _ ih₁ ih₂ =>
    simp only [Stmt.ou, Bool.or_eq_false_iff] at hs
    rw [ih₂ hs.2, ih₁ hs.1]
  | ifLtN_true _ _ ih => simp only [Stmt.ou, Bool.or_eq_false_iff] at hs; exact ih hs.1
  | ifLtN_false _ _ ih => simp only [Stmt.ou, Bool.or_eq_false_iff] at hs; exact ih hs.2
  | ifLtR_true _ _ ih => simp only [Stmt.ou, Bool.or_eq_false_iff] at hs; exact ih hs.1
  | ifLtR_false _ _ ih => simp only [Stmt.ou, Bool.or_eq_false_iff] at hs; exact ih hs.2
  | whileLtN_false _ _ => rfl
  | whileLtN_true _ _ _ ih₁ ih₂ => rw [ih₂ hs, ih₁ hs]
  | whileLtR_false _ _ => rfl
  | whileLtR_true _ _ _ ih₁ ih₂ => rw [ih₂ hs, ih₁ hs]

end Exec

end Machine

end WordRAM
