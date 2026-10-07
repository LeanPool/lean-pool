/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierPhysicalRange
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierHeat
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceFourierLimit
public import Mathlib.MeasureTheory.Function.Holder

/-!
# The heat multiplier and Fourier divergence

Scalar heat multiplication preserves Fourier orthogonality to the spatial
frequency, the Fourier-side ingredient for the divergence assertion in
`lem:reg-multiplier-bounds`.
-/

public section

open MeasureTheory Filter
open scoped ENNReal FourierTransform ComplexInnerProductSpace

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The heat semigroup preserves frequency orthogonality to the divergence
direction. -/
theorem heatSemigroup_preserves_fourierOrthogonal
    (t : ℝ) (ht : 0 ≤ t) (v : ComplexVectorL2)
    (hv : ∀ᵐ ξ ∂volume,
      inner ℂ (complexifyFrequency ξ)
        ((MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3) v ξ) = 0) :
    ∀ᵐ ξ ∂volume,
      inner ℂ (complexifyFrequency ξ)
        ((MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3)
          (heatSemigroup t ht v) ξ) = 0 := by
  let ℱ := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  have htransform : ℱ (heatSemigroup t ht v) = heatMultiplier t ht • ℱ v := by
    change ℱ (ℱ.symm (heatMultiplier t ht • ℱ v)) = _
    exact ℱ.apply_symm_apply _
  have htransformAE := (Lp.ext_iff).mp htransform
  have hHeatMem : MemLp (heatSymbol t) ∞ volume := by
    apply memLp_top_of_bound
    · fun_prop [heatSymbol]
    · filter_upwards [] with ξ
      exact heatSymbol_norm_le_one ht ξ
  have hdef : heatMultiplier t ht = hHeatMem.toLp (heatSymbol t) := by
    rfl
  have hmul : ∀ᵐ ξ ∂volume, heatMultiplier t ht ξ = heatSymbol t ξ := by
    filter_upwards [hHeatMem.coeFn_toLp] with ξ hξ
    rw [hdef]
    exact hξ
  have hsmul : (fun ξ : L2Vec3 => (heatMultiplier t ht • ℱ v) ξ) =ᵐ[volume]
      fun ξ => heatMultiplier t ht ξ • ℱ v ξ :=
    Lp.coeFn_lpSMul (heatMultiplier t ht) (ℱ v)
  filter_upwards [htransformAE, hmul, hsmul, hv] with ξ hξ hμ hs hvξ
  rw [hξ, hs, hμ]
  rw [inner_smul_right, hvξ]
  simp

/-- The real heat operator has weakly divergence-free range whenever its
complex Fourier input is orthogonal to frequency. -/
theorem realHeatOperator_isInJ_of_fourierOrthogonal
    (t : ℝ) (ht : 0 ≤ t) (f : RealVectorL2)
    (hf : ∀ᵐ ξ ∂volume,
      inner ℂ (complexifyFrequency ξ)
        ((MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3)
          (complexifyVectorL2 f) ξ) = 0) :
    CKN.IsInJ (realVectorL2Representative (realHeatOperator t ht f)) := by
  let v := complexifyVectorL2 f
  let sh := heatSemigroup t ht v
  have hFourier : ∀ᵐ ξ ∂volume,
      inner ℂ (complexifyFrequency ξ)
        ((MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3) sh ξ) = 0 := by
    exact heatSemigroup_preserves_fourierOrthogonal t ht v hf
  have hweak : CKN.IsWeakDivFreeL2 (realPartVectorL2Representative sh) :=
    realPart_isWeakDivFree_of_fourierOrthogonal sh hFourier
  have hrep : realVectorL2Representative (realHeatOperator t ht f) =ᵐ[volume]
      realPartVectorL2Representative sh := by
    have h := realPartVectorL2Representative_eq_ae sh
    simpa [realHeatOperator, sh, v] using h
  exact (CKN.isInJ_iff_weakDivFree).2 (isWeakDivFree_congr_ae hrep.symm hweak)

end CKN.Leray

end
