/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.QuantumRealCovariance

/-!
# Positive real covariance from semidefinite nondegenerate uncertainty

A null real quadratic direction would also be a null direction of the
actual positive complex uncertainty matrix. Its imaginary part then puts
that real vector in the kernel of the commutation form. Invertibility of
the form excludes such a direction, proving actual real PosDef even when
the quantum uncertainty is only semidefinite.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quantumCovariance_im_apply (V Ω : Matrix ι ι ℝ) (i j : ι) :
    (quantumCovariance V Ω i j).im = Ω i j / 2 := by
  simp [quantumCovariance, Complex.mul_im]
  ring

omit [DecidableEq ι] in
theorem quantumCovariance_mulVec_real_im (V Ω : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) :
    ((quantumCovariance V Ω *ᵥ (fun j => (x j : ℂ))) i).im = (Ω *ᵥ x) i / 2 := by
  simp only [Matrix.mulVec, dotProduct, Complex.im_sum, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, quantumCovariance_im_apply]
  simp_rw [div_mul_eq_mul_div]
  exact (Finset.sum_div _ _ _).symm

theorem real_posDef_of_quantum_posSemidef {V Ω : Matrix ι ι ℝ}
    (hQ : (quantumCovariance V Ω).PosSemidef) (hΩ : IsUnit Ω) : V.PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨real_isHermitian_of_quantum_isHermitian hQ.isHermitian, ?_⟩
  intro x hx
  have hnn := hQ.dotProduct_mulVec_nonneg (fun i => (x i : ℂ))
  have hr : 0 ≤ x ⬝ᵥ (V *ᵥ x) := by
    simpa only [real_quantum_quadratic] using (Complex.nonneg_iff.mp hnn).1
  have hn : x ⬝ᵥ (V *ᵥ x) ≠ 0 := by
    intro hz
    have hzero : star (fun i => (x i : ℂ)) ⬝ᵥ
        (quantumCovariance V Ω *ᵥ (fun i => (x i : ℂ))) = 0 := by
      apply Complex.ext
      · simpa only [real_quantum_quadratic, Complex.zero_re] using hz
      · exact (Complex.nonneg_iff.mp hnn).2.symm
    have hmul := hQ.dotProduct_mulVec_zero_iff.mp hzero
    have hΩx : Ω *ᵥ x = 0 := by
      funext i
      have h := congrArg Complex.im (congrFun hmul i)
      rw [quantumCovariance_mulVec_real_im] at h
      change (Ω *ᵥ x) i / 2 = 0 at h
      change (Ω *ᵥ x) i = 0
      linarith
    apply hx
    apply Matrix.mulVec_injective_of_isUnit hΩ
    simpa only [Matrix.mulVec_zero] using hΩx
  simpa only [star_trivial] using lt_of_le_of_ne hr hn.symm

end VacuumBellSeparation.Gaussian
