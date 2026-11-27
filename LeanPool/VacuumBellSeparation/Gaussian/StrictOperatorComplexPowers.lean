/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.OperatorMeans
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Complex.Hadamard

/-!
# Actual complex powers of a strictly positive bounded operator

The entire family is the Banach-algebra exponential of the actual bounded
selfadjoint CFC logarithm. The auxiliary exponential is totalized for arbitrary
operators; identification with genuine real spectral powers requires the stated
strict positivity hypotheses. The reserve interpolation applies these identities
only to strictly positive regularizations and takes positive-power limits.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap Set
open scoped ComplexConjugate ContinuousFunctionalCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Complex powers of an operator computed by exponentiating a complex multiple of its
functional-calculus logarithm. -/
def operatorComplexPower (R : E →L[ℂ] E) (z : ℂ) : E →L[ℂ] E :=
  NormedSpace.exp (z • CFC.log R)

@[simp] theorem operatorComplexPower_zero (R : E →L[ℂ] E) :
    operatorComplexPower R 0 = 1 := by
  simp only [operatorComplexPower, zero_smul, NormedSpace.exp_zero]

theorem operatorComplexPower_add (R : E →L[ℂ] E) (z w : ℂ) :
    operatorComplexPower R (z + w) = operatorComplexPower R z * operatorComplexPower R w := by
  let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ (E →L[ℂ] E)
  unfold operatorComplexPower
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl (CFC.log R)).smul_left z).smul_right w)

theorem operatorComplexPower_commute (R : E →L[ℂ] E) (z w : ℂ) :
    Commute (operatorComplexPower R z) (operatorComplexPower R w) := by
  change _ * _ = _ * _
  rw [← operatorComplexPower_add, ← operatorComplexPower_add, add_comm]

theorem operatorComplexPower_star (R : E →L[ℂ] E) (z : ℂ) :
    star (operatorComplexPower R z) = operatorComplexPower R (conj z) := by
  simp only [operatorComplexPower, NormedSpace.star_exp, star_smul,
    (IsSelfAdjoint.log (a := R)).star_eq, starRingEnd_apply]

theorem differentiable_operatorComplexPower (R : E →L[ℂ] E) :
    Differentiable ℂ (operatorComplexPower R) := by
  change Differentiable ℂ (fun z : ℂ => NormedSpace.exp (z • CFC.log R))
  exact differentiable_exp_smul_const ℂ (CFC.log R)

theorem operatorComplexPower_real {R : E →L[ℂ] E}
    (hR : IsStrictlyPositive R) (t : ℝ) : operatorComplexPower R (t : ℂ) = R ^ t := by
  have hlog : ContinuousOn Real.log (spectrum ℝ R) := by
    apply Real.continuousOn_log.mono
    intro x hx
    exact ne_of_gt (hR.spectrum_pos hx)
  have hmul : ContinuousOn (fun x : ℝ => t * Real.log x) (spectrum ℝ R) :=
    continuousOn_const.mul hlog
  have hsmul : (t : ℂ) • CFC.log R = t • CFC.log R := by
    simpa only [RCLike.ofReal_eq_complex_ofReal] using
      (RCLike.real_smul_eq_coe_smul (K := ℂ) t (CFC.log R)).symm
  rw [operatorComplexPower, hsmul,
    ← CFC.real_exp_eq_normedSpace_exp ((IsSelfAdjoint.all t).smul (IsSelfAdjoint.log (a := R))),
    CFC.log, ← cfc_const_mul t Real.log R hlog,
    ← cfc_comp' Real.exp (fun x : ℝ => t * Real.log x) R
      Real.continuous_exp.continuousOn hmul hR.nonneg.isSelfAdjoint,
    CFC.rpow_eq_cfc_real hR.nonneg]
  apply cfc_congr
  intro x hx
  change Real.exp (t * Real.log x) = x ^ t
  rw [Real.rpow_def_of_pos (hR.spectrum_pos hx)]
  congr 1
  ring

@[simp] theorem operatorComplexPower_one {R : E →L[ℂ] E}
    (hR : IsStrictlyPositive R) : operatorComplexPower R 1 = R := by
  simpa only [Complex.ofReal_one, CFC.rpow_one R hR.nonneg] using operatorComplexPower_real hR 1

/-- Continuous linear map for the operator imaginary power, of type `unitary (E →L[ℂ] E)`. -/
def operatorImaginaryPower (R : E →L[ℂ] E) (t : ℝ) : unitary (E →L[ℂ] E) :=
  ⟨operatorComplexPower R ((t : ℂ) * Complex.I), by
    constructor
    · rw [operatorComplexPower_star, ← operatorComplexPower_add]
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
        neg_add_cancel, operatorComplexPower_zero]
    · rw [operatorComplexPower_star, ← operatorComplexPower_add]
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
        add_neg_cancel, operatorComplexPower_zero]⟩

@[simp] theorem operatorImaginaryPower_coe (R : E →L[ℂ] E) (t : ℝ) :
    (operatorImaginaryPower R t : E →L[ℂ] E) = operatorComplexPower R ((t : ℂ) * Complex.I) := rfl

theorem operatorComplexPower_split (R : E →L[ℂ] E) (z : ℂ) :
    operatorComplexPower R z = operatorComplexPower R (z.re : ℂ) *
      (operatorImaginaryPower R z.im : E →L[ℂ] E) := by
  conv_lhs => rw [← Complex.re_add_im z]
  exact operatorComplexPower_add R _ _

theorem norm_operatorComplexPower_eq_real (R : E →L[ℂ] E) (z : ℂ) :
    ‖operatorComplexPower R z‖ = ‖operatorComplexPower R (z.re : ℂ)‖ := by
  rw [operatorComplexPower_split, CStarRing.norm_mul_coe_unitary]

theorem exists_bound_operatorComplexPower_strip (R : E →L[ℂ] E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc (0 : ℝ) 1 →
      ‖operatorComplexPower R z‖ ≤ C := by
  have hc : Continuous (fun t : ℝ => operatorComplexPower R (t : ℂ)) :=
    (differentiable_operatorComplexPower R).continuous.comp Complex.continuous_ofReal
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun z hz => ?_⟩
  rw [norm_operatorComplexPower_eq_real]
  exact (hC z.re hz).trans (le_max_left _ _)

end VacuumBellSeparation.Gaussian
