/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Basic.Real.Basic

/-! The maximum absolute coefficient height of an integer polynomial, and the hypothesis
`CoefficientHeightLE f H` that it is at most a real bound `H`. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The height of an integer polynomial: the maximum absolute value of its coefficients, or `0` for
the zero polynomial. -/
def integerCoefficientHeight {σ : Type*} (f : MvPolynomial σ ℤ) : ℕ :=
  f.support.sup (fun m => (f.coeff m).natAbs)

/-- Every coefficient of `f` has absolute value at most the real bound `H`, that is, the
coefficient height of `f` is at most `H` (`coefficientHeightLE_iff`). -/
abbrev CoefficientHeightLE {σ : Type*} (f : MvPolynomial σ ℤ) (H : ℝ) : Prop :=
  ∀ m, |(f.coeff m : ℝ)| ≤ H

/-- Every coefficient of `f` has absolute value at most the coefficient height of `f`. -/
lemma coefficient_abs_le_integerCoefficientHeight {σ : Type*}
    (f : MvPolynomial σ ℤ) (m : σ →₀ ℕ) :
    |(f.coeff m : ℝ)| ≤ (integerCoefficientHeight f : ℝ) := by
  have hh : (f.coeff m).natAbs ≤ integerCoefficientHeight f := by
    by_cases hm : m ∈ f.support
    · exact Finset.le_sup (f := fun m => (f.coeff m).natAbs) hm
    · simp [notMem_support_iff.mp hm]
  simpa only [Nat.cast_natAbs, Int.cast_abs] using
    (show ((f.coeff m).natAbs : ℝ) ≤ integerCoefficientHeight f by exact_mod_cast hh)

/-- If every coefficient of `f` has absolute value at most a nonnegative real `H`, then the
coefficient height of `f` is at most `H`. -/
lemma integerCoefficientHeight_le {σ : Type*} (f : MvPolynomial σ ℤ)
    {H : ℝ} (hH : 0 ≤ H) (hc : CoefficientHeightLE f H) :
    (integerCoefficientHeight f : ℝ) ≤ H := by
  classical
  by_cases hf : f.support.Nonempty
  · obtain ⟨m, _, hm⟩ := Finset.exists_mem_eq_sup f.support hf (fun m => (f.coeff m).natAbs)
    unfold integerCoefficientHeight
    rw [hm]
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hc m
  · have he : f.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hf
    simpa [integerCoefficientHeight, he] using hH

/-- A real bound on all coefficients is the same as a bound on the coefficient height. -/
lemma coefficientHeightLE_iff {σ : Type*} {f : MvPolynomial σ ℤ} {H : ℝ} :
    CoefficientHeightLE f H ↔ (integerCoefficientHeight f : ℝ) ≤ H :=
  ⟨fun hc => integerCoefficientHeight_le f ((abs_nonneg _).trans (hc 0)) hc,
    fun hH m => (coefficient_abs_le_integerCoefficientHeight f m).trans hH⟩

/-- A nonzero integer polynomial has positive coefficient height. -/
lemma integerCoefficientHeight_pos {σ : Type*} (f : MvPolynomial σ ℤ) (hf : f ≠ 0) :
    0 < integerCoefficientHeight f := by
  obtain ⟨m, hne⟩ := MvPolynomial.exists_coeff_ne_zero hf
  exact (Int.natAbs_pos.mpr hne).trans_le
    (Finset.le_sup (f := fun m => (f.coeff m).natAbs) (mem_support_iff.mpr hne))

end
end CCDN
