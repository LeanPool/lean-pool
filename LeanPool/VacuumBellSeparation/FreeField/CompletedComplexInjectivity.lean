/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.DistributionScalingMultiplier
public import LeanPool.VacuumBellSeparation.FreeField.ContinuousDistributionSeparation
public import LeanPool.VacuumBellSeparation.FreeField.ComplexTestInjectivity

/-!
# Complex injectivity for the actual bounded-region source completion

The completed position components are actual compactly supported distributions.
Their proved Fourier representations have entire affine slices. The physical
kernel relation becomes a literal relation between those functions, and the
odd-order zero of the massive polynomial forces both distributions to vanish.
-/

@[expose] public section

open scoped SchwartzMap FourierTransform InnerProductSpace

namespace VacuumBellSeparation

theorem complexSource_eq_zero_of_map_eq_zero
    {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))
    (hU : Bornology.IsBounded U) (z : ComplexSourceHilbert hm U)
    (hz : complexSourceMap hm U z = 0) : z = 0 := by
  obtain ⟨χ, hχ, hχone⟩ := exists_spatialSchwartz_cutoff hU.closure
  let T := complexSourceFirstDistribution hm U z
  let S := complexSourceSecondDistribution hm U z
  have hT : Distribution.IsVanishingOn T (closure U)ᶜ :=
    complexSourceFirstDistribution_isVanishingOn hm U z
  have hS : Distribution.IsVanishingOn S (closure U)ᶜ :=
    complexSourceSecondDistribution_isVanishingOn hm U z
  have hnorm := compactDistributionFourier_relation T S hT hS χ hχ hχone
    (normalizedSourceSecondMultiplier m) (hasTemperateGrowth_normalizedSourceSecondMultiplier hm)
    (complexSource_fourier_distribution_relation_of_kernel hm U z hz)
  let c : ℝ := 2 * Real.pi
  have hc : 0 < c := by dsimp [c]; positivity
  let F := fun p => compactDistributionFourier T χ (c⁻¹ • p)
  let G := fun p => compactDistributionFourier S χ (c⁻¹ • p)
  have hlinear (p : EuclideanSpace ℝ (Fin 3)) :
      F p = -(Complex.I * (dispersion m p : ℂ) * G p) := by
    have h := hnorm (c⁻¹ • p)
    change F p + sourceSecondInverseMultiplier m (c • (c⁻¹ • p)) * G p = 0 at h
    rw [smul_inv_smul₀ hc.ne'] at h
    exact eq_neg_of_add_eq_zero_left h
  have hparts (p : EuclideanSpace ℝ (Fin 3)) : F p = 0 ∧ G p = 0 := by
    let pperp := p - ⟪e₁, p⟫_ℝ • e₁
    have hpperp : ⟪e₁, pperp⟫_ℝ = 0 := by
      simp [pperp, inner_sub_right, real_inner_smul_right, norm_e₁]
    let M := dispersion m pperp
    have hM : 0 < M := hm.trans_le (le_dispersion hm.le pperp)
    let Fs := compactDistributionFourierSlice T χ hχ (c⁻¹ • pperp) (c⁻¹ • e₁)
    let Gs := compactDistributionFourierSlice S χ hχ (c⁻¹ • pperp) (c⁻¹ • e₁)
    have hFa : AnalyticOnNhd ℂ Fs Set.univ :=
      analyticOnNhd_compactDistributionFourierSlice T χ hχ _ _
    have hGa : AnalyticOnNhd ℂ Gs Set.univ :=
      analyticOnNhd_compactDistributionFourierSlice S χ hχ _ _
    have hFs (t : ℝ) : Fs (t : ℂ) = F (pperp + t • e₁) := by
      dsimp only [Fs, F]
      rw [compactDistributionFourierSlice_ofReal]
      congr 1
      module
    have hGs (t : ℝ) : Gs (t : ℂ) = G (pperp + t • e₁) := by
      dsimp only [Gs, G]
      rw [compactDistributionFourierSlice_ofReal]
      congr 1
      module
    have hrel (t : ℝ) : Fs (t : ℂ) ^ 2 =
        -((t : ℂ) ^ 2 + (M : ℂ) ^ 2) * Gs (t : ℂ) ^ 2 := by
      have hω : (dispersion m (pperp + t • e₁) : ℂ) ^ 2 =
          (t : ℂ) ^ 2 + (M : ℂ) ^ 2 := by
        exact_mod_cast dispersion_sq_transverse pperp hpperp t
      rw [hFs, hGs, hlinear, neg_sq, mul_pow, mul_pow, Complex.I_sq, hω]
      ring
    obtain ⟨hf0, hg0⟩ := entire_massive_square_zero_of_real hM hFa hGa hrel
    have hfp := congrFun hf0 (⟪e₁, p⟫_ℝ : ℂ)
    have hgp := congrFun hg0 (⟪e₁, p⟫_ℝ : ℂ)
    rw [hFs] at hfp
    rw [hGs] at hgp
    simpa [pperp] using And.intro hfp hgp
  have hFzero : ∀ p, compactDistributionFourier T χ p = 0 := by
    intro p
    have h := (hparts (c • p)).1
    simpa only [F, inv_smul_smul₀ hc.ne'] using h
  have hGzero : ∀ p, compactDistributionFourier S χ p = 0 := by
    intro p
    have h := (hparts (c • p)).2
    simpa only [G, inv_smul_smul₀ hc.ne'] using h
  exact complexSource_eq_zero_of_distributions_eq_zero hm U z
    (distribution_eq_zero_of_compactDistributionFourier_eq_zero T hT χ hχ hχone hFzero)
    (distribution_eq_zero_of_compactDistributionFourier_eq_zero S hS χ hχ hχone hGzero)

/-- The actual complex source map is injective for every bounded localization region. -/
theorem complexSourceMap_injective
    {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))
    (hU : Bornology.IsBounded U) : Function.Injective (complexSourceMap hm U) := by
  intro z w h
  apply sub_eq_zero.mp
  apply complexSource_eq_zero_of_map_eq_zero hm U hU (z - w)
  rw [map_sub, h, sub_self]

end VacuumBellSeparation
