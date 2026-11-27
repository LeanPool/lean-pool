/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeThermalPowers

/-!
# Actual dense inverse-power domains for faithful product densities

Strict positivity of all occupation weights gives injectivity and dense
range of positive CFC powers on the full multi-index Hilbert space. Their
inverse is a linear map on that actual range, with no boundedness claim.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem injective_of_positive_indexed_basis_eigenvalues (b : HilbertBasis ι ℂ E)
    {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) {w : ι → ℝ}
    (hw : ∀ k, 0 < w k) (heig : ∀ k, A (b k) = w k • b k) : Function.Injective A := by
  have hcoord (x : E) (k : ι) : inner ℂ (b k) (A x) = (w k : ℂ) * inner ℂ (b k) x := by
    simpa only [hA.adjoint_eq, heig, inner_smul_left_eq_smul, Algebra.smul_def,
      RCLike.algebraMap_eq_ofReal, RCLike.ofReal_eq_complex_ofReal] using
      (A.adjoint_inner_left x (b k)).symm
  intro x y hxy
  apply b.repr.injective
  ext k
  rw [b.repr_apply_apply, b.repr_apply_apply]
  have h := congrArg (fun z => inner ℂ (b k) z) hxy
  rw [hcoord, hcoord] at h
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (hw k))) h

omit [CompleteSpace E] in
theorem denseRange_of_nonzero_indexed_basis_eigenvalues (b : HilbertBasis ι ℂ E)
    {A : E →L[ℂ] E} {w : ι → ℝ} (hw : ∀ k, w k ≠ 0)
    (heig : ∀ k, A (b k) = w k • b k) : DenseRange A := by
  have hb : Submodule.span ℂ (Set.range b) ≤ A.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    refine ⟨(w k)⁻¹ • b k, ?_⟩
    change A ((w k)⁻¹ • b k) = b k
    calc
      A ((w k)⁻¹ • b k) = (w k)⁻¹ • A (b k) :=
        LinearMapClass.map_smul_of_tower A (w k)⁻¹ (b k)
      _ = (w k)⁻¹ • (w k • b k) :=
        congrArg (fun y : E => (w k)⁻¹ • y) (heig k)
      _ = b k := inv_smul_smul₀ (hw k) (b k)
  have hd : A.range.topologicalClosure = ⊤ := by
    apply top_unique
    rw [← b.dense_span]
    exact Submodule.topologicalClosure_mono hb
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hd

theorem multiModeThermalDensity_rpow_injective {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) :
    Function.Injective (multiModeThermalDensity q ^ τ) :=
  injective_of_positive_indexed_basis_eigenvalues (multiModeNumberBasis m)
    (CFC.rpow_nonneg (a := multiModeThermalDensity q) (y := τ)).isSelfAdjoint
    (fun k => Real.rpow_pos_of_pos (multiModeThermalWeight_pos hq₀ hq₁ k) τ)
    (multiModeThermalDensity_rpow_apply_numberBasis (fun j => (hq₀ j).le) hq₁ hτ)

theorem multiModeThermalDensity_rpow_denseRange {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) :
    DenseRange (multiModeThermalDensity q ^ τ) :=
  denseRange_of_nonzero_indexed_basis_eigenvalues (multiModeNumberBasis m)
    (fun k => ne_of_gt (Real.rpow_pos_of_pos (multiModeThermalWeight_pos hq₀ hq₁ k) τ))
    (multiModeThermalDensity_rpow_apply_numberBasis (fun j => (hq₀ j).le) hq₁ hτ)

/-- Multi thermal power domain. -/
def multiThermalPowerDomain {m : ℕ} (q : Fin m → ℝ) (τ : ℝ) :
    Submodule ℂ (MultiModeOscillatorSpace m) := (multiModeThermalDensity q ^ τ).range

/-- Linear map for the multi thermal inverse power, of type `multiThermalPowerDomain q τ →ₗ[ℂ]
MultiModeOscillatorSpace m`. -/
def multiThermalInversePower {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) :
    multiThermalPowerDomain q τ →ₗ[ℂ] MultiModeOscillatorSpace m :=
  (LinearEquiv.ofInjective (multiModeThermalDensity q ^ τ).toLinearMap
    (multiModeThermalDensity_rpow_injective hq₀ hq₁ hτ)).symm.toLinearMap

theorem multiThermalInversePower_apply_power {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) (x : MultiModeOscillatorSpace m) :
    multiThermalInversePower hq₀ hq₁ hτ ⟨(multiModeThermalDensity q ^ τ) x, ⟨x, rfl⟩⟩ = x :=
  (LinearEquiv.ofInjective (multiModeThermalDensity q ^ τ).toLinearMap
    (multiModeThermalDensity_rpow_injective hq₀ hq₁ hτ)).symm_apply_apply x

theorem multiThermalPower_apply_inversePower {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (x : multiThermalPowerDomain q τ) :
    (multiModeThermalDensity q ^ τ) (multiThermalInversePower hq₀ hq₁ hτ x) = x :=
  congrArg Subtype.val ((LinearEquiv.ofInjective (multiModeThermalDensity q ^ τ).toLinearMap
    (multiModeThermalDensity_rpow_injective hq₀ hq₁ hτ)).apply_symm_apply x)

theorem multiThermalPowerDomain_dense {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) :
    Dense (multiThermalPowerDomain q τ : Set (MultiModeOscillatorSpace m)) :=
  multiModeThermalDensity_rpow_denseRange hq₀ hq₁ hτ

end VacuumBellSeparation.Gaussian
