/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.StrictOperatorComplexPowers
public import LeanPool.VacuumBellSeparation.Gaussian.FiniteSpectralTraceRecovery

/-!
# The actual signed reserve interpolation strip

The scalar functions are genuine finite trace tests of the bounded operator
family S(z) B S(z), with S(z)=exp((1-z)log(R)/2). Both vertical edges are
same-sided unitary sandwiches. Their nuclear bounds are proved by the
actual Jordan expectation rather than a unitary-conjugation assertion.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap Set
open scoped ENNReal ComplexConjugate

variable {ι κ E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Reserve strip half given by `operatorComplexPower R ((1 - z) / 2)`. -/
def reserveStripHalf (R : E →L[ℂ] E) (z : ℂ) : E →L[ℂ] E :=
  operatorComplexPower R ((1 - z) / 2)

/-- Reserve trace strip operator given by `reserveStripHalf R z * B * reserveStripHalf R z`. -/
def reserveTraceStripOperator (R B : E →L[ℂ] E) (z : ℂ) : E →L[ℂ] E :=
  reserveStripHalf R z * B * reserveStripHalf R z

theorem differentiable_reserveTraceStripOperator (R B : E →L[ℂ] E) :
    Differentiable ℂ (reserveTraceStripOperator R B) := by
  have hS : Differentiable ℂ (reserveStripHalf R) :=
    (differentiable_operatorComplexPower R).comp
      (((differentiable_const (1 : ℂ)).sub differentiable_id).div_const 2)
  exact (hS.mul_const B).mul hS

theorem reserveTraceStripOperator_real {R : E →L[ℂ] E}
    (hR : IsStrictlyPositive R) (B : E →L[ℂ] E) (t : ℝ) :
    reserveTraceStripOperator R B (t : ℂ) =
      R ^ ((1 - t) / 2) * B * R ^ ((1 - t) / 2) := by
  have he : (1 - (t : ℂ)) / 2 = (((1 - t) / 2 : ℝ) : ℂ) := by push_cast; rfl
  simp only [reserveTraceStripOperator, reserveStripHalf, he, operatorComplexPower_real hR]

theorem reserveTraceStripOperator_zero_edge {R : E →L[ℂ] E}
    (hR : IsStrictlyPositive R) (B : E →L[ℂ] E) {z : ℂ} (hz : z.re = 0) :
    reserveTraceStripOperator R B z =
      (operatorImaginaryPower R (((1 - z) / 2).im) : E →L[ℂ] E) *
        (R ^ (1 / 2 : ℝ) * B * R ^ (1 / 2 : ℝ)) *
          (operatorImaginaryPower R (((1 - z) / 2).im) : E →L[ℂ] E) := by
  let U := operatorImaginaryPower R (((1 - z) / 2).im)
  let H := R ^ (1 / 2 : ℝ)
  have hre : ((1 - z) / 2).re = (1 / 2 : ℝ) := by norm_num [Complex.div_re, hz]
  have hs : reserveStripHalf R z = H * (U : E →L[ℂ] E) := by
    rw [reserveStripHalf, operatorComplexPower_split, hre, operatorComplexPower_real hR]
  have hc : H * (U : E →L[ℂ] E) = (U : E →L[ℂ] E) * H := by
    change R ^ (1 / 2 : ℝ) * operatorComplexPower R _ =
      operatorComplexPower R _ * R ^ (1 / 2 : ℝ)
    rw [← operatorComplexPower_real hR]
    exact (operatorComplexPower_commute R _ _).eq
  change (reserveStripHalf R z * B * reserveStripHalf R z) =
    (U : E →L[ℂ] E) * (H * B * H) * U
  rw [hs]
  calc
    (H * U) * B * (H * U) = (U * H) * B * (H * U) := by rw [hc]
    _ = _ := by noncomm_ring

theorem reserveTraceStripOperator_one_edge {R : E →L[ℂ] E}
    (B : E →L[ℂ] E) {z : ℂ} (hz : z.re = 1) :
    reserveTraceStripOperator R B z =
      (operatorImaginaryPower R (((1 - z) / 2).im) : E →L[ℂ] E) * B *
        (operatorImaginaryPower R (((1 - z) / 2).im) : E →L[ℂ] E) := by
  have hre : ((1 - z) / 2).re = (0 : ℝ) := by norm_num [Complex.div_re, hz]
  have hs : reserveStripHalf R z =
      (operatorImaginaryPower R (((1 - z) / 2).im) : E →L[ℂ] E) := by
    rw [reserveStripHalf, operatorComplexPower_split, hre, Complex.ofReal_zero,
      operatorComplexPower_zero, one_mul]
  simp only [reserveTraceStripOperator, hs]

theorem reserveTraceStrip_test_bounded (R B : E →L[ℂ] E)
    (u : ι → E) (s : Finset ι) (w : ι → ℂ) :
    BddAbove ((norm ∘ fun z => finiteTraceTest u s w (reserveTraceStripOperator R B z)) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_operatorComplexPower_strip R
  refine ⟨‖finiteTraceTest u s w‖ * (C * ‖B‖ * C), ?_⟩
  rintro y ⟨z, hz, rfl⟩
  have hz' : z.re ∈ Icc (0 : ℝ) 1 := hz
  have hs : ‖reserveStripHalf R z‖ ≤ C := by
    apply hbound
    have hre : ((1 - z) / 2).re = (1 - z.re) / 2 := by simp []
    rw [hre]
    constructor <;> linarith [hz'.1, hz'.2]
  apply ((finiteTraceTest u s w).le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact norm_mul_le_of_le (norm_mul_le_of_le hs le_rfl) hs

theorem reserveTraceStrip_finite_test_interpolation (b : HilbertBasis κ ℂ E)
    {R B : E →L[ℂ] E} (hR : IsStrictlyPositive R)
    (hcB : IsCompactOperator B) (hB : IsSelfAdjoint B) (htB : operatorTraceNorm B < ∞)
    {u : ι → E} (hu : Orthonormal ℂ u) (s : Finset ι) (w : ι → ℂ)
    (hw : ∀ i ∈ s, ‖w i‖ ≤ 1) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    ‖finiteTraceTest u s w (R ^ ((1 - θ) / 2) * B * R ^ ((1 - θ) / 2))‖ ≤
      (operatorTraceNorm (R ^ (1 / 2 : ℝ) * B * R ^ (1 / 2 : ℝ))).toReal ^ (1 - θ) *
        (operatorTraceNorm B).toReal ^ θ := by
  have hhalf : IsSelfAdjoint (R ^ (1 / 2 : ℝ)) := CFC.rpow_nonneg.isSelfAdjoint
  have hG := selfAdjoint_sandwich_isSelfAdjoint hB hhalf
  have htG := operatorTraceNorm_selfAdjoint_sandwich_lt_top hcB hB htB hhalf
  let f : ℂ → ℂ := fun z => finiteTraceTest u s w (reserveTraceStripOperator R B z)
  have hf : Differentiable ℂ f :=
    (finiteTraceTest u s w).differentiable.comp (differentiable_reserveTraceStripOperator R B)
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' f
    (z := (θ : ℂ))
    (a := (operatorTraceNorm (R ^ (1 / 2 : ℝ) * B * R ^ (1 / 2 : ℝ))).toReal)
    (b := (operatorTraceNorm B).toReal)
    (by simpa only [Complex.HadamardThreeLines.verticalClosedStrip, mem_preimage,
      Complex.ofReal_re] using hθ) hf.diffContOnCl (reserveTraceStrip_test_bounded R B u s w)
    (fun z hz => by
      dsimp only [f]
      rw [reserveTraceStripOperator_zero_edge hR B (Set.mem_singleton_iff.mp hz)]
      exact norm_finiteTraceTest_unitary_sandwich_le b hu s w hw hG htG _)
    (fun z hz => by
      dsimp only [f]
      rw [reserveTraceStripOperator_one_edge B (Set.mem_singleton_iff.mp hz)]
      exact norm_finiteTraceTest_unitary_sandwich_le b hu s w hw hB htB _)
  simpa only [f, reserveTraceStripOperator_real hR, Complex.ofReal_re] using h

end VacuumBellSeparation.Gaussian
