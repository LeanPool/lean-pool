/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.LocalGradientTopology
public import LeanPool.HighContrastHomogenization.Provider.Response.AdaptedWeakTransport

/-!
# High-contrast homogenization: Provider.Regularity.AffineGradientQuotientPullback

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Affine pullback on gradient quotient classes

This file defines the affine action directly on the Hilbert `L²`
quotient carrier.  Its public characterization is an almost-everywhere
formula, so later transfers never need to choose a raw representative.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- Almost-everywhere identities pull back through an invertible matrix on
the exact inverse-image domain. -/
theorem ae_affinePullback {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) {P : Vec d → Prop}
    (hP : ∀ᵐ x ∂(volumeMeasureOn U), P x) :
    ∀ᵐ y ∂(volumeMeasureOn (matImage L⁻¹ U)), P (matVecMul L y) := by
  let hq : Measure.QuasiMeasurePreserving (matVecMul L)
      (volumeMeasureOn (matImage L⁻¹ U)) (volumeMeasureOn U) := by
    refine ⟨(continuous_matVecMul L).measurable, ?_⟩
    rw [map_restrict_volume_affinePullback hL hU]
    exact Measure.AbsolutelyContinuous.rfl.smul_left _
  exact hq.tendsto_ae hP

private theorem memVectorL2_toVec_hilbertVectorL2 {U : Set (Vec d)}
    (F : HilbertVectorL2 U) :
    MemVectorL2 U (fun x ↦ (F x).toVec) := by
  exact MemLp.ae_eq
    (coeFn_hilbertVectorL2ToVectorL2 (U := U) F)
    (Lp.memLp (hilbertVectorL2ToVectorL2 (U := U) F))

private theorem memVectorL2_constMatVecMul (A : Mat d) {U : Set (Vec d)}
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    MemVectorL2 U (fun x ↦ matVecMul A (f x)) := by
  let T : Vec d →L[ℝ] Vec d :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)
  refine MemLp.of_le_mul (c := ‖T‖) hf ?_ ?_
  · simpa only [T, matVecMul] using!
      T.continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable
  · filter_upwards [] with x
    simpa only [T, matVecMul] using! T.le_opNorm (f x)

/-- Square integrability of the literal matrix-valued affine pullback of a
Hilbert `L²` quotient representative. -/
theorem memVectorL2_affineGradientPullback {L : Mat d} (hL : IsUnit L.det)
    {U V : Set (Vec d)} (hU : MeasurableSet U)
    (hV : V = matImage L⁻¹ U) (A : Mat d) (F : HilbertVectorL2 U) :
    MemVectorL2 V
      (fun y ↦ matVecMul A ((F (matVecMul L y)).toVec)) := by
  have hcomp : MemVectorL2 (matImage L⁻¹ U)
      (fun y ↦ (F (matVecMul L y)).toVec) :=
    Response.memVectorL2_affinePullback hL hU
      (memVectorL2_toVec_hilbertVectorL2 F)
  rw [hV]
  exact memVectorL2_constMatVecMul A hcomp

/-- Pull a Hilbert `L²` gradient quotient from `U` to the inverse-image
domain `V`, composing its representative with `L` and applying the fixed
matrix `A` to its values. -/
@[expose]
noncomputable def affineGradientQuotientPullback {L : Mat d}
    (hL : IsUnit L.det) {U V : Set (Vec d)} (hU : MeasurableSet U)
    (hV : V = matImage L⁻¹ U) (A : Mat d) :
    HilbertVectorL2 U → HilbertVectorL2 V :=
  fun F ↦ toHilbertVectorL2OfVecField
    (memVectorL2_affineGradientPullback hL hU hV A F)

/-- The quotient pullback has the literal affine representative almost
everywhere on its target domain. -/
theorem coeFn_affineGradientQuotientPullback {L : Mat d}
    (hL : IsUnit L.det) {U V : Set (Vec d)} (hU : MeasurableSet U)
    (hV : V = matImage L⁻¹ U) (A : Mat d) (F : HilbertVectorL2 U) :
    affineGradientQuotientPullback hL hU hV A F
      =ᵐ[volumeMeasureOn V]
      fun y ↦ HilbertVec.ofVec
        (matVecMul A ((F (matVecMul L y)).toVec)) := by
  exact coeFn_toHilbertVectorL2OfVecField
    (memVectorL2_affineGradientPullback hL hU hV A F)

end

end HighContrast
end HCPolySupport
