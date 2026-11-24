/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CompactDdcCoordinateExpansion
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PositivityLeviLink
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.NormalDirectionVanishing
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.KahlerPotentialNormalization

/-!
# The Levi form of a positive smooth current

Recovers Levi semipositivity from positivity of the corresponding current.
-/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff InnerProductSpace
namespace SGPT.Foundations.Analysis.Pending.FullPositiveScalarCurrentLeviConverse

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts ScalarLeviPositiveCurrent CompactVariableCurrentTests
  CompactDdcCoordinateExpansion CompactDifferentialTests ScalarFullTestTranspose
  DirectionalLeviDensity PositivityLeviLink ConstantFormProducts TopDegreeDensity
  LocalCurrentLebesgue

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}

private theorem smoothDDC_perpQuadratic_constant (a z : ComplexModel (m + 1)) :
    smoothDDC (perpQuadratic a) z = smoothDDC (perpQuadratic a) 0 := by
  have hsplit : perpQuadratic a = (fun y : ComplexModel (m + 1) => ‖y‖ ^ 2) +
      (-1 : ℝ) • fun y : ComplexModel (m + 1) => ‖⟪a, y⟫_ℂ‖ ^ 2 := by
    funext y
    simp [perpQuadratic, sub_eq_add_neg]
  have hH (x v w : ComplexModel (m + 1)) :
      realHessian (perpQuadratic a) x v w = realHessian (perpQuadratic a) 0 v w := by
    have hformula (t : ComplexModel (m + 1)) :
        realHessian (perpQuadratic a) t v w =
          2 * ⟪v, w⟫_ℝ - 2 * (⟪a, w⟫_ℂ * (starRingEnd ℂ) ⟪a, v⟫_ℂ).re := by
      have h1 : ContDiffAt ℝ 2 (fun y : ComplexModel (m + 1) => ‖y‖ ^ 2) t :=
        (contDiff_norm_sq ℝ).contDiffAt
      have h2 : ContDiffAt ℝ 2 (fun y : ComplexModel (m + 1) => ‖⟪a, y⟫_ℂ‖ ^ 2) t :=
        (contDiff_normSq_inner a).contDiffAt
      rw [hsplit, realHessian_add (v := (-1 : ℝ) •
        fun y : ComplexModel (m + 1) => ‖⟪a, y⟫_ℂ‖ ^ 2)
        h1 (h2.const_smul (-1 : ℝ)), realHessian_smul h2,
        realHessian_norm_sq, realHessian_normSq_inner]
      ring
    rw [hformula x, hformula 0]
  ext w
  have hw : w = ![w 0, w 1] := by ext i; fin_cases i <;> rfl
  rw [hw, FirstPass.smoothDDC_apply_eq_realHessian
    (contDiff_perpQuadratic a).contDiffAt,
    FirstPass.smoothDDC_apply_eq_realHessian (contDiff_perpQuadratic a).contDiffAt,
    hH z, hH z]

/-- The full compact directional test and its exact distributional pairing are produced
    internally. -/
theorem exists_directional_full_test (T : 𝓓'(U, ℝ)) (φ : 𝓓(U, ℝ))
    (a : ComplexModel (m + 1)) (ha : ‖a‖ = 1) :
    ∃ α : 𝓓(U, RealForm (m + 1) (2 * m)),
      (∀ z, α z = φ z • formPower (smoothDDC (perpQuadratic a) 0) m) ∧
      (∀ z, α z ∈ formSpan (m + 1) m) ∧
      ((∀ z, 0 ≤ φ z) → ∀ z, α z ∈ spCone m) ∧
      (∑ i, ddc (scalarTopCurrent T) (formBasis (m + 1) m i) (coeffTest α i)) =
        ((m.factorial : ℝ) / Real.pi ^ (m + 1)) * distributionalLeviCLM a T φ := by
  have hβ : IsSemipositiveOneOne (smoothDDC (perpQuadratic a) 0) :=
    ⟨smoothDDC_isOneOne (contDiff_perpQuadratic a).contDiffAt,
      coefficientSemipositive_smoothDDC_perpQuadratic ha.le 0⟩
  let γ : formSpan (m + 1) m :=
    ⟨formPower (smoothDDC (perpQuadratic a) 0) m,
      mem_formSpan_of_mem_spCone (formPower_mem_spCone hβ m)⟩
  let α : 𝓓(U, RealForm (m + 1) (2 * m)) :=
    TestFunction.postcompCLM ((ContinuousLinearMap.id ℝ ℝ).smulRight
      (γ : RealForm (m + 1) (2 * m))) φ
  have hαval (z : ComplexModel (m + 1)) :
      α z = φ z • formPower (smoothDDC (perpQuadratic a) 0) m := rfl
  have hαspan (z : ComplexModel (m + 1)) : α z ∈ formSpan (m + 1) m :=
    (formSpan (m + 1) m).smul_mem (φ z) γ.property
  have hαadj : scalarAdjointTest α =
      ((m.factorial : ℝ) / Real.pi ^ (m + 1)) • leviScalarTest a φ := by
    refine scalarAdjointTest_constForm_eq_leviScalarTest γ φ a
      ((m.factorial : ℝ) / Real.pi ^ (m + 1)) ?_
    intro z
    change topDensity (coordinateWedge
      (formPower (smoothDDC (perpQuadratic a) 0) m) (smoothDDC φ z)) = _
    rw [formPower_eq_wedgeProd, ← wedgeProd_snoc,
      NormalDirectionVanishing.wedgeProd_snoc_eq_cons,
      ← smoothDDC_perpQuadratic_constant a z,
      topDensity_smoothDDC_perpQuadratic
        (φ.contDiff.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) a ha]
  refine ⟨α, hαval, hαspan, ?_, ?_⟩
  · intro hφ z
    rw [hαval]
    exact smul_mem_spCone (formPower_mem_spCone hβ m) (hφ z)
  · rw [ddc_scalarTopCurrent_full_test_transpose, hαadj, map_smul,
      smul_eq_mul, apply_leviScalarTest]

/-- Unit-direction tests suffice by the quadratic homogeneity of the Levi form. -/
theorem hasNonnegativeDistributionalLevi_of_unit (T : 𝓓'(U, ℝ))
    (hunit : ∀ a : ComplexModel (m + 1), ‖a‖ = 1 → ∀ φ : 𝓓(U, ℝ),
      (∀ z, 0 ≤ φ z) → 0 ≤ distributionalLeviCLM a T φ) :
    HasNonnegativeDistributionalLevi T := by
  intro v φ hφ
  by_cases hv : v = 0
  · subst v
    have hz : leviScalarTest (0 : ComplexModel (m + 1)) φ = 0 := by
      ext z
      simp only [leviScalarTest_apply, leviForm_zero, _root_.zero_apply]
    rw [← apply_leviScalarTest, hz, map_zero]
  · let a : ComplexModel (m + 1) := ‖v‖⁻¹ • v
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have ha : ‖a‖ = 1 := by
      change ‖‖v‖⁻¹ • v‖ = 1
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
    have hva : v = ‖v‖ • a := by
      change v = ‖v‖ • (‖v‖⁻¹ • v)
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have htest : leviScalarTest v φ = ‖v‖ ^ 2 • leviScalarTest a φ := by
      ext z
      simp only [_root_.smul_apply, smul_eq_mul, leviScalarTest_apply]
      conv_lhs => rw [hva, KahlerPotentialNormalization.leviForm_smul_right]
    rw [← apply_leviScalarTest, htest, map_smul, smul_eq_mul, apply_leviScalarTest]
    exact mul_nonneg (sq_nonneg _) (hunit a ha φ hφ)

/-- Genuine full positive pairings recover every actual constant-direction Levi inequality. -/
theorem hasNonnegativeDistributionalLevi_of_full_positive_pairings (T : 𝓓'(U, ℝ))
    (hT : ∀ α : 𝓓(U, RealForm (m + 1) (2 * m)),
      (∀ z, α z ∈ spCone m) →
        0 ≤ ∑ i, ddc (scalarTopCurrent T) (formBasis (m + 1) m i) (coeffTest α i)) :
    HasNonnegativeDistributionalLevi T := by
  have hunit (a : ComplexModel (m + 1)) (ha : ‖a‖ = 1)
      (φ : 𝓓(U, ℝ)) (hφ : ∀ z, 0 ≤ φ z) : 0 ≤ distributionalLeviCLM a T φ := by
    obtain ⟨α, _, _, hp, heq⟩ := exists_directional_full_test T φ a ha
    have h := hT α (hp hφ)
    rw [heq] at h
    exact (mul_nonneg_iff_of_pos_left
      (div_pos (by exact_mod_cast Nat.factorial_pos m)
        (pow_pos Real.pi_pos (m + 1)))).mp h
  exact hasNonnegativeDistributionalLevi_of_unit T hunit

/-- Full positivity of the actual scalar differential supplies the genuine Levi inequalities. -/
theorem hasNonnegativeDistributionalLevi_of_isPositive_ddc (T : 𝓓'(U, ℝ))
    (hT : IsPositive (ddc (scalarTopCurrent T))) : HasNonnegativeDistributionalLevi T :=
  hasNonnegativeDistributionalLevi_of_full_positive_pairings T
    (fun α hα => pairing_nonnegative _ hT α hα)

end SGPT.Foundations.Analysis.Pending.FullPositiveScalarCurrentLeviConverse
