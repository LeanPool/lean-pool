/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.QuantumModePositivity

/-!
# Real positive covariance from actual strict quantum uncertainty

The real part of V+iΩ/2 is literally V. Testing the actual complex
positive matrix on embedded real vectors proves positive definiteness of
V. This is an elementary direction of the uncertainty condition, not an
inference of uncertainty from an arbitrary state or formal kernel.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quantumCovariance_re_apply (V Ω : Matrix ι ι ℝ) (i j : ι) :
    (quantumCovariance V Ω i j).re = V i j := by
  simp [quantumCovariance, Complex.mul_re]

omit [Fintype ι] [DecidableEq ι] in
theorem real_isHermitian_of_quantum_isHermitian {V Ω : Matrix ι ι ℝ}
    (hQ : (quantumCovariance V Ω).IsHermitian) : V.IsHermitian := by
  change Vᵀ = V
  ext i j
  have h := congrArg Complex.re (congrFun (congrFun hQ.eq i) j)
  simpa only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_re,
    quantumCovariance_re_apply, Matrix.transpose_apply] using h

omit [DecidableEq ι] in
theorem real_quantum_quadratic (V Ω : Matrix ι ι ℝ) (x : ι → ℝ) :
    (star (fun i => (x i : ℂ)) ⬝ᵥ
      (quantumCovariance V Ω *ᵥ (fun i => (x i : ℂ)))).re = x ⬝ᵥ (V *ᵥ x) := by
  simp [dotProduct, Matrix.mulVec, Complex.mul_re, Complex.mul_im]

omit [Fintype ι] [DecidableEq ι] in
theorem real_posDef_of_quantum_posDef [Finite ι] {V Ω : Matrix ι ι ℝ}
    (hQ : (quantumCovariance V Ω).PosDef) : V.PosDef := by
  let _ : Fintype ι := Fintype.ofFinite ι
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨real_isHermitian_of_quantum_isHermitian hQ.isHermitian, ?_⟩
  intro x hx
  have hxc : (fun i => (x i : ℂ)) ≠ 0 := by
    intro he
    apply hx
    funext i
    have h := congrArg Complex.re (congrFun he i)
    simpa using h
  have h := (Complex.pos_iff.mp (hQ.dotProduct_mulVec_pos hxc)).1
  rw [real_quantum_quadratic] at h
  simpa only [star_trivial] using h

omit [Fintype ι] in
theorem quantum_covariance_shift_posDef [Finite ι] {V Ω : Matrix ι ι ℝ}
    (hQ : (quantumCovariance V Ω).PosDef) : (V + (1 / 2 : ℝ) • 1).PosDef :=
  (real_posDef_of_quantum_posDef hQ).add_posSemidef
    (Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1 / 2))

end VacuumBellSeparation.Gaussian
