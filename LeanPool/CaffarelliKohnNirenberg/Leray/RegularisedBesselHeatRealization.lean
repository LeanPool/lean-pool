/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselHeatSemigroup

/-!
# Physical realization of Bessel heat evolution

The heat multiplier commutes with the inverse Bessel weight, so the
complete Sobolev heat evolution realizes the original physical L² heat flow.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Realization of the complete Bessel heat semigroup commutes with the
physical Fourier L² heat semigroup. -/
theorem regularisedBesselHeat_realization
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (v : BesselPotentialSpace L2Vec3 ComplexVec3 s 2) :
    regularisedBesselSobolevToL2 s hs
      (regularisedBesselHeat s t ht v) =
        heatSemigroup t ht (regularisedBesselSobolevToL2 s hs v) := by
  let ℱ := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  let vHeat := regularisedBesselHeat s t ht v
  have hHeat (F : ComplexVectorL2) :
      ℱ (heatSemigroup t ht F) =ᵐ[volume]
        fun ξ => heatSymbol t ξ • ℱ F ξ := by
    have hcoef : (heatMultiplier t ht : Lp (α := L2Vec3) ℂ ∞) =ᵐ[volume]
        heatSymbol t := by
      have hmem : MemLp (heatSymbol t) ∞ volume := by
        apply memLp_top_of_bound (by fun_prop [heatSymbol]) 1
        filter_upwards [] with ξ
        exact heatSymbol_norm_le_one ht ξ
      simpa [heatMultiplier] using hmem.coeFn_toLp
    have hsmul : (heatMultiplier t ht • ℱ F : ComplexVectorL2) =ᵐ[volume]
        fun ξ => heatMultiplier t ht ξ • ℱ F ξ :=
      Lp.coeFn_lpSMul (heatMultiplier t ht) (ℱ F)
    change ℱ (ℱ.symm (heatMultiplier t ht • ℱ F)) =ᵐ[volume] _
    rw [ℱ.apply_symm_apply]
    filter_upwards [hcoef, hsmul] with ξ hc hm
    rw [hm, hc]
  apply ℱ.injective
  apply Lp.ext
  have hLeft := regularisedBesselSobolevToL2_fourier_ae s hs vHeat
  have hRight := regularisedBesselSobolevToL2_fourier_ae s hs v
  have hWeighted : ℱ vHeat.toLp =ᵐ[volume]
      fun ξ => heatSymbol t ξ • ℱ v.toLp ξ := by
    have hv : vHeat.toLp = heatSemigroup t ht v.toLp := by
      simp only [vHeat, regularisedBesselHeat, BesselPotentialSpace.toLp_ofLp]
    rw [hv]
    exact hHeat v.toLp
  have hPhysical := hHeat (regularisedBesselSobolevToL2 s hs v)
  filter_upwards [hLeft, hRight, hWeighted, hPhysical]
    with ξ hL hR hW hP
  change ℱ (regularisedBesselSobolevToL2 s hs vHeat) ξ =
    ℱ (heatSemigroup t ht (regularisedBesselSobolevToL2 s hs v)) ξ
  calc
    ℱ (regularisedBesselSobolevToL2 s hs vHeat) ξ =
        (((1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ) •
          ℱ vHeat.toLp ξ := hL
    _ = (((1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ) •
          (heatSymbol t ξ • ℱ v.toLp ξ) := by rw [hW]
    _ = heatSymbol t ξ •
          ((((1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ) •
            ℱ v.toLp ξ) := smul_comm _ _ _
    _ = heatSymbol t ξ •
          ℱ (regularisedBesselSobolevToL2 s hs v) ξ := by rw [hR]
    _ = ℱ (heatSemigroup t ht
          (regularisedBesselSobolevToL2 s hs v)) ξ := hP.symm

end CKN.Leray

end
