/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneCoefficientScaling

/-!
# Coordinate compatibility of the affine coefficient pullback

Scalar coordinate projection commutes exactly with the unnormalized coefficient pullback
`P_[p,ℓ]` on `L∞` of `FastDynamo/Analysis/WholePlaneCoefficientScaling.lean`.  The module then
records the two exact covariance identities for Hölder multiplication — scalar times vector and
vector times scalar — in which the `ℓ⁻¹` factors cancel precisely because the coefficient is
pulled back without normalization (Lemma 5.2, `lem:exact-renormalization`).

The module is separate from `FastDynamo/Analysis/WholePlaneCoefficientScaling.lean` for build
weight: that module sits under some one hundred and seventy dependents, and no declaration
there refers to any of these three theorems.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-! ## Coordinate compatibility -/

/-- Coordinate projection commutes exactly with coefficient pullback. -/
theorem wholePlaneCoordLInf_coeffPullback (i : Fin 3)
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (v : WholePlaneC3LInf) :
    wholePlaneCoordLInf i (wholePlaneCoeffPullback C3 p ell hell v) =
      wholePlaneCoeffPullback ℂ p ell hell (wholePlaneCoordLInf i v) := by
  apply Lp.ext
  have hleft := (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
    (p := ∞) (μ := (volume : Measure WholePlane))
    (wholePlaneCoeffPullback C3 p ell hell v)
  have hvalue := wholePlaneCoeffPullback_coe_ae C3 p ell hell v
  have hright := wholePlaneCoeffPullback_coe_ae ℂ p ell hell
    (wholePlaneCoordLInf i v)
  have hbaseScaled := Measure.ae_smul_measure
    ((EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
      (p := ∞) (μ := (volume : Measure WholePlane)) v)
    (ENNReal.ofReal (ell ^ 2))
  have hbasePull :=
    (measurePreserving_wholePlaneAffine p ell hell).quasiMeasurePreserving.ae_eq_comp
      hbaseScaled
  filter_upwards [hleft, hvalue, hright, hbasePull]
    with y hl hv hr hb
  change (((EuclideanSpace.proj (𝕜 := ℂ) i).compLpL ∞ volume
      (wholePlaneCoeffPullback C3 p ell hell v) : WholePlaneScalarLInf) :
        WholePlane → ℂ) y =
    (wholePlaneCoeffPullback ℂ p ell hell
      ((EuclideanSpace.proj (𝕜 := ℂ) i).compLpL ∞ volume v) :
        WholePlane → ℂ) y
  have hr' :
      (wholePlaneCoeffPullback ℂ p ell hell
        ((EuclideanSpace.proj (𝕜 := ℂ) i).compLpL ∞ volume v) :
          WholePlane → ℂ) y =
        (((EuclideanSpace.proj (𝕜 := ℂ) i).compLpL ∞ volume v :
          WholePlaneScalarLInf) : WholePlane → ℂ)
            (wholePlaneAffine p ell y) := by
    simpa only [wholePlaneCoordLInf] using hr
  rw [hl, hv, hr']
  have hb' :
      (((EuclideanSpace.proj (𝕜 := ℂ) i).compLpL ∞ volume v :
        WholePlaneScalarLInf) : WholePlane → ℂ)
          (wholePlaneAffine p ell y) =
        (EuclideanSpace.proj (𝕜 := ℂ) i) (v (wholePlaneAffine p ell y)) := by
    simpa only [Function.comp_apply] using hb
  rw [hb']

section Mul

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Exact covariance of scalar-times-vector multiplication under affine scaling: multiplying
the pulled-back coefficient by the normalized rescaling of `b` gives the normalized
rescaling of `a b`.  The `ℓ⁻¹` factors cancel precisely because the coefficient is pulled
back without normalization. -/
theorem scalarVectorMulL2_coeffPullback_rescale (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (a : WholePlaneLInf ℂ) (b : WholePlaneL2 F) :
    scalarVectorMulL2 volume
        (wholePlaneCoeffPullback ℂ p ell hell a)
        (wholePlaneRescale F p ell hell b) =
      wholePlaneRescale F p ell hell (scalarVectorMulL2 volume a b) := by
  apply Lp.ext
  have hbaseScaled := Measure.ae_smul_measure
    (scalarVectorMulL2_coe_ae volume a b)
    (ENNReal.ofReal (ell ^ 2))
  have hbasePull :=
    (measurePreserving_wholePlaneAffine p ell hell).quasiMeasurePreserving.ae_eq_comp
      hbaseScaled
  filter_upwards [scalarVectorMulL2_coe_ae volume
      (wholePlaneCoeffPullback ℂ p ell hell a)
      (wholePlaneRescale F p ell hell b),
    wholePlaneCoeffPullback_coe_ae ℂ p ell hell a,
    wholePlaneRescale_coe_ae F p ell hell b,
    wholePlaneRescale_coe_ae F p ell hell (scalarVectorMulL2 volume a b),
    hbasePull] with y hout ha hb hr hbase
  rw [hout, ha, hb, hr]
  have hbase' :
      (scalarVectorMulL2 volume a b : WholePlane → F)
          (wholePlaneAffine p ell y) =
        a (wholePlaneAffine p ell y) • b (wholePlaneAffine p ell y) := by
    simpa only [Function.comp_apply] using hbase
  rw [hbase']
  simp only [smul_smul]
  rw [mul_comm]

/-- The same exact covariance for vector-times-scalar multiplication: the pulled-back
vector coefficient acting on the rescaled scalar field is the rescaling of the product. -/
theorem vectorScalarMulL2_coeffPullback_rescale (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (a : WholePlaneLInf F) (b : WholePlaneL2 ℂ) :
    vectorScalarMulL2 volume
        (wholePlaneCoeffPullback F p ell hell a)
        (wholePlaneRescale ℂ p ell hell b) =
      wholePlaneRescale F p ell hell (vectorScalarMulL2 volume a b) := by
  apply Lp.ext
  have hbaseScaled := Measure.ae_smul_measure
    (vectorScalarMulL2_coe_ae volume a b)
    (ENNReal.ofReal (ell ^ 2))
  have hbasePull :=
    (measurePreserving_wholePlaneAffine p ell hell).quasiMeasurePreserving.ae_eq_comp
      hbaseScaled
  filter_upwards [vectorScalarMulL2_coe_ae volume
      (wholePlaneCoeffPullback F p ell hell a)
      (wholePlaneRescale ℂ p ell hell b),
    wholePlaneCoeffPullback_coe_ae F p ell hell a,
    wholePlaneRescale_coe_ae ℂ p ell hell b,
    wholePlaneRescale_coe_ae F p ell hell (vectorScalarMulL2 volume a b),
    hbasePull] with y hout ha hb hr hbase
  rw [hout, ha, hb, hr]
  have hbase' :
      (vectorScalarMulL2 volume a b : WholePlane → F)
          (wholePlaneAffine p ell y) =
        b (wholePlaneAffine p ell y) • a (wholePlaneAffine p ell y) := by
    simpa only [Function.comp_apply] using hbase
  rw [hbase']
  simp only [smul_smul, smul_eq_mul]

end Mul

end

end FastDynamo
