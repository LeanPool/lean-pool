/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalPowers

/-!
# Domains of inverse thermal powers

Positive thermal powers have dense range and trivial kernel, but no bounded
left inverse. Their inverse powers are therefore defined as linear maps on
the actual dense range. This is a domain foundation for the Appendix A
sandwich; it does not by itself prove that the sandwich extends boundedly.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem injective_of_positive_basis_eigenvalues (b : HilbertBasis ℕ ℂ E)
    {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) {w : ℕ → ℝ}
    (hw : ∀ k, 0 < w k) (heig : ∀ k, A (b k) = w k • b k) :
    Function.Injective A := by
  have hcoord (x : E) (k : ℕ) :
      inner ℂ (b k) (A x) = (w k : ℂ) * inner ℂ (b k) x := by
    simpa only [hA.adjoint_eq, heig, inner_smul_left_eq_smul, Algebra.smul_def,
      Complex.coe_algebraMap] using
      (A.adjoint_inner_left x (b k)).symm
  intro x y hxy
  apply b.repr.injective
  ext k
  rw [b.repr_apply_apply, b.repr_apply_apply]
  have h := congrArg (fun z => inner ℂ (b k) z) hxy
  rw [hcoord, hcoord] at h
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (hw k))) h

omit [CompleteSpace E] in
theorem denseRange_of_nonzero_basis_eigenvalues (b : HilbertBasis ℕ ℂ E)
    {A : E →L[ℂ] E} {w : ℕ → ℝ} (hw : ∀ k, w k ≠ 0)
    (heig : ∀ k, A (b k) = w k • b k) : DenseRange A := by
  have hb : Submodule.span ℂ (Set.range b) ≤ A.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    refine ⟨(w k)⁻¹ • b k, ?_⟩
    change A ((w k)⁻¹ • b k) = b k
    rw [A.map_smul_of_tower, heig, inv_smul_smul₀ (hw k)]
  have hd : A.range.topologicalClosure = ⊤ := by
    apply top_unique
    rw [← b.dense_span]
    exact Submodule.topologicalClosure_mono hb
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hd

omit [CompleteSpace E] in
theorem no_bounded_leftInverse_of_vanishing_basis_eigenvalues
    (b : HilbertBasis ℕ ℂ E) {A : E →L[ℂ] E} {w : ℕ → ℝ}
    (hw : Tendsto w atTop (𝓝 0)) (heig : ∀ k, A (b k) = w k • b k) :
    ¬ ∃ S : E →L[ℂ] E, ∀ x, S (A x) = x := by
  rintro ⟨S, hS⟩
  have hbound (k : ℕ) : 1 ≤ ‖S‖ * ‖w k‖ := by
    calc
      1 = ‖S (A (b k))‖ := by rw [hS, b.orthonormal.norm_eq_one]
      _ ≤ ‖S‖ * ‖A (b k)‖ := S.le_opNorm _
      _ = ‖S‖ * ‖w k‖ := by rw [heig, norm_smul, b.orthonormal.norm_eq_one, mul_one]
  have hlim : Tendsto (fun k => ‖S‖ * ‖w k‖) atTop (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using hw.norm.const_mul ‖S‖
  have hfalse : (1 : ℝ) ≤ 0 := ge_of_tendsto' hlim hbound
  norm_num at hfalse

theorem thermalDensity_rpow_injective {q τ : ℝ}
    (hq₀ : 0 < q) (hq₁ : q < 1) (hτ : 0 < τ) :
    Function.Injective (thermalDensity q ^ τ) :=
  injective_of_positive_basis_eigenvalues numberBasis
    (CFC.rpow_nonneg (a := thermalDensity q) (y := τ)).isSelfAdjoint
    (fun k => Real.rpow_pos_of_pos (thermalWeight_pos hq₀ hq₁ k) τ)
    (thermalDensity_rpow_apply_numberBasis hq₀.le hq₁ hτ)

theorem thermalDensity_rpow_denseRange {q τ : ℝ}
    (hq₀ : 0 < q) (hq₁ : q < 1) (hτ : 0 < τ) :
    DenseRange (thermalDensity q ^ τ) :=
  denseRange_of_nonzero_basis_eigenvalues numberBasis
    (fun k => ne_of_gt (Real.rpow_pos_of_pos (thermalWeight_pos hq₀ hq₁ k) τ))
    (thermalDensity_rpow_apply_numberBasis hq₀.le hq₁ hτ)

theorem tendsto_thermalWeight_rpow {q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hτ : 0 < τ) :
    Tendsto (fun k => thermalWeight q k ^ τ) atTop (𝓝 0) := by
  have hw : Tendsto (thermalWeight q) atTop (𝓝 0) := by
    change Tendsto (fun k : ℕ => (1 - q) * q ^ k) atTop (𝓝 0)
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁).const_mul (1 - q)
  simpa only [Function.comp_def, Real.zero_rpow (ne_of_gt hτ)] using
    ((Real.continuous_rpow_const hτ.le).tendsto 0).comp hw

theorem thermalDensity_rpow_no_bounded_leftInverse {q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hτ : 0 < τ) :
    ¬ ∃ S : OscillatorSpace →L[ℂ] OscillatorSpace,
      ∀ x, S ((thermalDensity q ^ τ) x) = x :=
  no_bounded_leftInverse_of_vanishing_basis_eigenvalues numberBasis
    (tendsto_thermalWeight_rpow hq₀ hq₁ hτ)
    (thermalDensity_rpow_apply_numberBasis hq₀ hq₁ hτ)

theorem thermalDensity_rpow_not_isUnit {q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hτ : 0 < τ) :
    ¬ IsUnit (thermalDensity q ^ τ) := by
  rintro ⟨u, hu⟩
  apply thermalDensity_rpow_no_bounded_leftInverse hq₀ hq₁ hτ
  refine ⟨(↑(u⁻¹) : OscillatorSpace →L[ℂ] OscillatorSpace), fun x => ?_⟩
  rw [← hu, ← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self]

theorem thermalDensity_rpow_not_isStrictlyPositive {q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hτ : 0 < τ) :
    ¬ IsStrictlyPositive (thermalDensity q ^ τ) :=
  fun h => thermalDensity_rpow_not_isUnit hq₀ hq₁ hτ h.isUnit

/-- The natural dense domain of the inverse power, expressed as the actual
range of the bounded positive power. -/
noncomputable def thermalPowerDomain (q τ : ℝ) : Submodule ℂ OscillatorSpace :=
  (thermalDensity q ^ τ).range

/-- The inverse of the positive power, with its domain in the type.
This is a linear map, without an asserted continuity or boundedness. -/
noncomputable def thermalInversePower {q τ : ℝ}
    (hq₀ : 0 < q) (hq₁ : q < 1) (hτ : 0 < τ) :
    thermalPowerDomain q τ →ₗ[ℂ] OscillatorSpace :=
  (LinearEquiv.ofInjective (thermalDensity q ^ τ).toLinearMap
    (thermalDensity_rpow_injective hq₀ hq₁ hτ)).symm.toLinearMap

theorem thermalInversePower_apply_power {q τ : ℝ}
    (hq₀ : 0 < q) (hq₁ : q < 1) (hτ : 0 < τ) (x : OscillatorSpace) :
    thermalInversePower hq₀ hq₁ hτ ⟨(thermalDensity q ^ τ) x, ⟨x, rfl⟩⟩ = x :=
  (LinearEquiv.ofInjective (thermalDensity q ^ τ).toLinearMap
    (thermalDensity_rpow_injective hq₀ hq₁ hτ)).symm_apply_apply x

theorem thermalPower_apply_inversePower {q τ : ℝ}
    (hq₀ : 0 < q) (hq₁ : q < 1) (hτ : 0 < τ) (x : thermalPowerDomain q τ) :
    (thermalDensity q ^ τ) (thermalInversePower hq₀ hq₁ hτ x) = x :=
  congrArg Subtype.val ((LinearEquiv.ofInjective (thermalDensity q ^ τ).toLinearMap
    (thermalDensity_rpow_injective hq₀ hq₁ hτ)).apply_symm_apply x)

theorem thermalPowerDomain_dense {q τ : ℝ}
    (hq₀ : 0 < q) (hq₁ : q < 1) (hτ : 0 < τ) :
    Dense (thermalPowerDomain q τ : Set OscillatorSpace) :=
  thermalDensity_rpow_denseRange hq₀ hq₁ hτ

end VacuumBellSeparation.Gaussian
