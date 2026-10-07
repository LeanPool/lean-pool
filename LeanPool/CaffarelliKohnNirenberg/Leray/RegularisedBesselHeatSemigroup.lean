/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLaplacian
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLaplacianStep
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildHeatContinuity

/-!
# Heat evolution in the complete Bessel space

The Fourier heat multiplier acts on the weighted L² coordinate of the
complete Sobolev carrier, preserving its order and contracting its norm.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Heat evolution transported through the Bessel/L² isometry. -/
@[expose]
def regularisedBesselHeat (s t : ℝ) (ht : 0 ≤ t)
    (v : BesselPotentialSpace L2Vec3 ComplexVec3 s 2) :
    BesselPotentialSpace L2Vec3 ComplexVec3 s 2 :=
  BesselPotentialSpace.ofLp s (heatSemigroup t ht v.toLp)

/-- The heat semigroup contracts every complete Bessel Hˢ norm. -/
theorem regularisedBesselHeat_norm_le (s t : ℝ) (ht : 0 ≤ t)
    (v : BesselPotentialSpace L2Vec3 ComplexVec3 s 2) :
    ‖regularisedBesselHeat s t ht v‖ ≤ ‖v‖ := by
  rw [← BesselPotentialSpace.norm_toLp_eq, ← BesselPotentialSpace.norm_toLp_eq (f := v),
    regularisedBesselHeat, BesselPotentialSpace.toLp_ofLp]
  exact heatSemigroup_norm_le t ht v.toLp

/-- Heat evolution is strongly continuous in the complete Bessel Hˢ
space at every nonnegative time, including time zero. -/
theorem regularisedBesselHeat_continuousAt
    (s : ℝ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (v : BesselPotentialSpace L2Vec3 ComplexVec3 s 2) :
    ContinuousAt
      (fun t : {t : ℝ // 0 ≤ t} => regularisedBesselHeat s t.1 t.2 v)
      ⟨t₀, ht₀⟩ := by
  have h := heatSemigroup_continuousAt ht₀ v.toLp
  have hfun : (fun t : {t : ℝ // 0 ≤ t} => regularisedBesselHeat s t.1 t.2 v) =
      fun t : {t : ℝ // 0 ≤ t} =>
        (BesselPotentialSpace.toLpₗᵢ L2Vec3 ComplexVec3 s 2).symm
          (heatSemigroup t.1 t.2 v.toLp) := by
    funext t
    apply BesselPotentialSpace.injective_toLp L2Vec3 ComplexVec3 s 2
    rw [regularisedBesselHeat, BesselPotentialSpace.toLp_ofLp,
      ← BesselPotentialSpace.toLpₗᵢ_apply
        (f := (BesselPotentialSpace.toLpₗᵢ L2Vec3 ComplexVec3 s 2).symm
        (heatSemigroup t.1 t.2 v.toLp)),
      LinearIsometryEquiv.apply_symm_apply]
  rw [hfun]
  exact (BesselPotentialSpace.toLpₗᵢ L2Vec3 ComplexVec3 s 2).symm.continuous.continuousAt.comp h

/-- Complete Sobolev heat evolution has the prescribed initial value. -/
theorem regularisedBesselHeat_zero (s : ℝ)
    (v : BesselPotentialSpace L2Vec3 ComplexVec3 s 2) :
    regularisedBesselHeat s 0 (le_refl (0 : ℝ)) v = v := by
  apply BesselPotentialSpace.injective_toLp L2Vec3 ComplexVec3 s 2
  rw [regularisedBesselHeat, BesselPotentialSpace.toLp_ofLp]
  let ℱ := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  change ℱ.symm (heatMultiplier 0 (le_refl _) • ℱ v.toLp) = v.toLp
  apply ℱ.injective
  rw [ℱ.apply_symm_apply]
  apply Lp.ext
  have hcoef : (heatMultiplier 0 (le_refl (0 : ℝ)) :
      Lp (α := L2Vec3) ℂ ∞) =ᵐ[volume] fun _ => 1 := by
    have hmem : MemLp (heatSymbol 0) ∞ volume := by
      apply memLp_top_of_bound (by fun_prop [heatSymbol]) 1
      filter_upwards [] with ξ
      exact heatSymbol_norm_le_one (le_refl 0) ξ
    have hcoe : (heatMultiplier 0 (le_refl (0 : ℝ)) :
        Lp (α := L2Vec3) ℂ ∞) =ᵐ[volume] heatSymbol 0 := by
      simpa [heatMultiplier] using hmem.coeFn_toLp
    filter_upwards [hcoe] with ξ hξ
    simpa [heatSymbol] using hξ
  filter_upwards [Lp.coeFn_lpSMul (r := 2)
    (heatMultiplier 0 (le_refl _)) (ℱ v.toLp), hcoef]
    with ξ hprod hone
  simpa [hone] using hprod

end CKN.Leray

end
