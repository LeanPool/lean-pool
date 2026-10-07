/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLaplacian

/-!
# Sobolev promotion through the Laplacian

The second-order Bessel identity promotes a field by two Sobolev orders
when both the field and its distributional Laplacian have the lower order.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap Laplacian

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- A field and its distributional Laplacian in Hˢ give the field in Hˢ⁺². -/
theorem regularised_memSobolev_add_two_of_laplacian
    (s : ℝ) (D : 𝓢'(L2Vec3, ComplexVec3))
    (hD : TemperedDistribution.MemSobolev s 2 D)
    (hΔ : TemperedDistribution.MemSobolev s 2 (Laplacian.laplacian D)) :
    TemperedDistribution.MemSobolev (s + 2) 2 D := by
  let A : ℝ := (2 * Real.pi) ^ 2
  have hAne : A ≠ 0 := by dsimp [A]; positivity
  have hScaledD : TemperedDistribution.MemSobolev s 2 (A • D) := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) A D]
    exact hD.smul (A : ℂ)
  have hScaledDiff : TemperedDistribution.MemSobolev s 2
      (A • D - Laplacian.laplacian D) := hScaledD.sub hΔ
  have hBessel : TemperedDistribution.MemSobolev s 2
      (TemperedDistribution.besselPotential L2Vec3 ComplexVec3 2 D) := by
    have hScale : TemperedDistribution.MemSobolev s 2
        (A⁻¹ • (A • D - Laplacian.laplacian D)) := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ) A⁻¹
        (A • D - Laplacian.laplacian D)]
      exact hScaledDiff.smul ((A⁻¹ : ℝ) : ℂ)
    have hIdentity := regularised_besselPotential_two_laplacian_identity D
    change A • TemperedDistribution.besselPotential L2Vec3 ComplexVec3 2 D =
      A • D - Laplacian.laplacian D at hIdentity
    have hInv := congrArg
      (fun X : 𝓢'(L2Vec3, ComplexVec3) => A⁻¹ • X) hIdentity
    rw [smul_smul, inv_mul_cancel₀ hAne, one_smul] at hInv
    rw [hInv]
    exact hScale
  have hPromoted := TemperedDistribution.memSobolev_besselPotential_iff.mp hBessel
  convert hPromoted using 1
  ring

end CKN.Leray

end
