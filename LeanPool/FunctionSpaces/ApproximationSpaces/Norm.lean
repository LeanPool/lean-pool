/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Error
public import LeanPool.FunctionSpaces.ApproximationSpaces.Sequences.Lq

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The approximation spaces `A^s_q`

For an approximation scheme `A` in `X`, a smoothness `s` and a fine index `1 ≤ q ≤ ∞`,
Pietsch's **approximation space** `A^s_q` consists of the `f ∈ X` with

`‖f‖_{A^s_q} = ‖ (n^(s - 1/q) E_{n-1}(f))_{n ≥ 1} ‖_{ℓ_q} < ∞`.

In Lean the sequence is indexed from `0` as `((n + 1)^(s - 1/q) E_n(f))_{n ≥ 0}`, the
quasi-norm is `A.approxNorm s q f`, and membership is `A.MemApprox s q f`.  For `q = ∞` the
exponent is `s` (in Lean `1 / ∞.toReal = 1 / 0 = 0`), so `‖f‖_{A^s_∞} = sup (n+1)^s E_n(f)`.
The same formula defines `A^s_q` for `0 < q < 1`, the range of nonlinear approximation; the
embedding `‖f‖ ≤ ‖f‖_{A^s_q}` holds for every `q ≠ 0`.

**Design.** The quasi-norm takes values in `ℝ≥0∞` and is defined for every `f`; membership is
finiteness, as for `MeasureTheory.eLpNorm` and `MeasureTheory.MemLp`.  The spaces are only
quasi-normed (the triangle inequality holds up to a constant), and Mathlib has no class for
quasi-normed spaces, so no new normed type is introduced.  The linear structure is recorded
separately as a `Submodule` (`ApproximationScheme.approxSpace`).

This file holds the definition and the facts that follow directly from the calculus of the
error `E_n(f) = A.approxError f n` of `ApproximationSpaces.Error`: homogeneity,
`‖f‖ ≤ ‖f‖_{A^s_q}` (because `E_0(f) = ‖f‖`), definiteness, and comparison of schemes.
Everything else is proved for the equivalent dyadic quasi-norm of
`ApproximationSpaces.Dyadic`.
-/

@[expose] public section

open scoped ENNReal

namespace ApproximationScheme

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

variable (A : ApproximationScheme X)

/-- **Pietsch's quasi-norm** of `A^s_q`: the `ℓ_q` norm of `((n + 1)^(s - 1/q) E_n(f))_n`. -/
noncomputable def approxNorm (s : ℝ) (q : ℝ≥0∞) (f : X) : ℝ≥0∞ :=
  ENNReal.lqNorm q (fun n => ((n + 1 : ℕ) : ℝ≥0∞) ^ (s - 1 / q.toReal) * A.approxError f n)

/-- `f` belongs to the **approximation space** `A^s_q`: its quasi-norm is finite. -/
def MemApprox (s : ℝ) (q : ℝ≥0∞) (f : X) : Prop := A.approxNorm s q f < ∞

variable {A} {s : ℝ} {q : ℝ≥0∞}

/-- `f ∈ A^s_q` iff its quasi-norm is finite. -/
theorem memApprox_iff {f : X} : A.MemApprox s q f ↔ A.approxNorm s q f < ∞ := Iff.rfl

/-- The quasi-norm of an element of `A^s_q` is finite. -/
theorem MemApprox.approxNorm_ne_top {f : X} (hf : A.MemApprox s q f) : A.approxNorm s q f ≠ ∞ :=
  hf.ne

/-- For `q = ∞` the quasi-norm is `sup_n (n + 1)^s E_n(f)`. -/
theorem approxNorm_top (s : ℝ) (f : X) :
    A.approxNorm s ∞ f = ⨆ n, ((n + 1 : ℕ) : ℝ≥0∞) ^ s * A.approxError f n := by
  simp [approxNorm, ENNReal.lqNorm_top]

/-- For `q < ∞` the `q`-th power of the quasi-norm is `∑ₙ (n + 1)^(sq - 1) E_n(f)^q`. -/
theorem approxNorm_rpow (hq0 : q ≠ 0) (hq : q ≠ ∞) (s : ℝ) (f : X) :
    A.approxNorm s q f ^ q.toReal =
      ∑' n, ((n + 1 : ℕ) : ℝ≥0∞) ^ (s * q.toReal - 1) * A.approxError f n ^ q.toReal := by
  have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [approxNorm, ENNReal.lqNorm_rpow hq0 hq]
  congr 1; funext n
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_mul]
  congr 2
  field_simp

/-- `‖0‖_{A^s_q} = 0`. -/
@[simp]
theorem approxNorm_zero (s : ℝ) (q : ℝ≥0∞) : A.approxNorm s q 0 = 0 := by
  simp [approxNorm]

/-- `0 ∈ A^s_q`. -/
theorem memApprox_zero (s : ℝ) (q : ℝ≥0∞) : A.MemApprox s q 0 := by
  simp [MemApprox]

/-- **Homogeneity**: `‖c f‖_{A^s_q} = |c| ‖f‖_{A^s_q}`. -/
theorem approxNorm_smul (c : ℝ) (f : X) :
    A.approxNorm s q (c • f) = ‖c‖ₑ * A.approxNorm s q f := by
  simp_rw [approxNorm, approxError_smul, mul_left_comm _ ‖c‖ₑ]
  exact ENNReal.lqNorm_const_mul _ _

/-- `A^s_q` is closed under real multiples. -/
theorem MemApprox.smul {f : X} (hf : A.MemApprox s q f) (c : ℝ) : A.MemApprox s q (c • f) := by
  rw [MemApprox, approxNorm_smul]
  exact ENNReal.mul_lt_top eNorm_lt_top hf

/-- `A^s_q` is closed under negation. -/
theorem MemApprox.neg {f : X} (hf : A.MemApprox s q f) : A.MemApprox s q (-f) := by
  simpa using hf.smul (-1)

/-- **The embedding `A^s_q ↪ X`**: `‖f‖ ≤ ‖f‖_{A^s_q}` for every `q ≠ 0`, also below `1`, from
the term `E_0(f) = ‖f‖`. -/
theorem enorm_le_approxNorm (hq0 : q ≠ 0) (f : X) : ‖f‖ₑ ≤ A.approxNorm s q f := by
  have := ENNReal.le_lqNorm (a := fun n => ((n + 1 : ℕ) : ℝ≥0∞) ^ (s - 1 / q.toReal) *
    A.approxError f n) hq0 0
  simp only [zero_add, Nat.cast_one, ENNReal.one_rpow, one_mul, approxError_zero_right] at this
  exact this

/-- For `q ≠ 0`, `‖f‖_{A^s_q} = 0` only for `f = 0`. -/
theorem approxNorm_eq_zero_iff (hq0 : q ≠ 0) {f : X} : A.approxNorm s q f = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ approxNorm_zero s q⟩
  have := enorm_le_approxNorm (A := A) (s := s) hq0 f
  rw [h, nonpos_iff_eq_zero, eNorm_eq_zero] at this
  exact this

/-- A scheme with larger sets has smaller quasi-norms, hence larger approximation spaces. -/
theorem approxNorm_anti_scheme {A' : ApproximationScheme X} (h : ∀ n, A n ⊆ A' n) (f : X) :
    A'.approxNorm s q f ≤ A.approxNorm s q f :=
  ENNReal.lqNorm_mono fun n => by gcongr; exact approxError_anti_scheme h f n

/-- A scheme with larger sets has larger approximation spaces. -/
theorem MemApprox.of_subset_scheme {A' : ApproximationScheme X} (h : ∀ n, A n ⊆ A' n) {f : X}
    (hf : A.MemApprox s q f) : A'.MemApprox s q f :=
  (approxNorm_anti_scheme h f).trans_lt hf

end ApproximationScheme
