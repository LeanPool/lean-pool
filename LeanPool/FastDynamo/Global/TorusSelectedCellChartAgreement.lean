/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusSelectedCellVelocityFacts
public import LeanPool.FastDynamo.Global.TorusChartActionBridge

/-!
# The chart coefficient agreement at a placed cell

The proof of `lem:parametrix-error` (§7.1): "the coefficients of the horizontal operator on `T²` and
the operator on `ℝ²` for the selected cell agree on `supp psi_n`, since the added axial velocity
profile in the selected cell of `T²` is constant there and all other cells are disjoint".
`Global/TorusChartActionBridge.lean` isolates that sentence as the hypothesis
`ChartCoefficientAgreement s u v a`; this module discharges it, on the closed Euclidean disc
`closedBall(p_n, 3 R_n/4)` — the support of the auxiliary cut-off `psi-tilde_n`, a device of the
formalisation that does not occur in the paper — for

* `u` the global velocity `parameterizedFullGlobalW1Inf` of `eq:global-u`;
* `v` the rescaled seed coefficients `rescaledWholePlaneVelocityCoefficients v_h p_n ell_n` of
  `eq:local-copy`;
* `a` the plateau amplitude `a_n = tau/(2 pi K_n)` of `eq:axial-offset`.

The statements are parametric in the profile data `(h, Omega, U)` and hold for an arbitrary
placement.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Metric Set
open TransverseSmoothBumpPeriodization
open scoped ENNReal LineDeriv SchwartzMap

namespace ScaleFamily.TorusCellPlacement

open FullVelocityConcrete
open TorusChartL2

variable {sp : LocalSeedParameters} {r : ScaleRatios sp}

/-! ## The two canonical representatives -/

/-- The `WholePlane`-valued canonical representative of the chart layer is the one used by the
placed cut-offs. -/
theorem torusWholePlaneRepresentative_eq_ioc (q : TransverseTorus) :
    torusWholePlaneRepresentative q = wholePlaneIocRepresentative q := by
  ext j
  fin_cases j <;> rfl

/-- The coordinate pair of the canonical whole-plane representative is the canonical pair
representative. -/
theorem coordinatePair_torusWholePlaneRepresentative (q : TransverseTorus) :
    ((torusWholePlaneRepresentative q) 0, (torusWholePlaneRepresentative q) 1) =
      transverseIocRepresentative q := by
  apply Prod.ext <;> rfl

/-- Membership in the closed three-quarter buffer ball, read on the canonical pair
representative. -/
theorem pairEuclideanDist_le_of_mem_closedBall {supportRadius : ℝ}
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) {q : TransverseTorus}
    (hq : torusWholePlaneRepresentative q ∈
      closedBall (pairToWholePlane (P.scaleFamily.cellCenter n))
        (3 * P.scaleFamily.bufferRadius n / 4)) :
    pairEuclideanDist (transverseIocRepresentative q) (P.scaleFamily.cellCenter n) ≤
      3 * P.scaleFamily.bufferRadius n / 4 := by
  rw [← dist_wholePlaneIocRepresentative_cellCenter P.scaleFamily n q,
    ← torusWholePlaneRepresentative_eq_ioc q]
  simpa [mem_closedBall] using hq

/-! ## The rescaled seed coefficients and the placed Euclidean source -/

variable (h : PonomarenkoSmoothingWidth) (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
  (angularSpeed axialSpeed : ℝ)

/-- The value coefficient of the rescaled-coefficient package at the cell `n` is represented by
the placed Euclidean cell source (`eq:local-copy`). -/
theorem rescaledHelicalCoefficients_value_ae (n : ℕ) :
    (((rescaledWholePlaneVelocityCoefficients
        (wholePlaneSchwartzVelocityCoefficients
          (parameterizedSmoothedVelocity h angularSpeed axialSpeed))
        (pairToWholePlane (P.scaleFamily.cellCenter n))
        (P.scaleFamily.ell n) (P.scaleFamily.ell_pos n)).value : WholePlane → C3)) =ᵐ[volume]
      fun y ↦ parameterizedHelicalCellSource h P angularSpeed axialSpeed n (y 0, y 1) := by
  set center : WholePlane := pairToWholePlane (P.scaleFamily.cellCenter n) with hcenter
  set ell : ℝ := P.scaleFamily.ell n with hell'
  have hell : 0 < ell := P.scaleFamily.ell_pos n
  set vel : SchwartzMap WholePlane C3 :=
    parameterizedSmoothedVelocity h angularSpeed axialSpeed with hvel
  have hpull := wholePlaneCoeffPullback_coe_ae C3 center ell hell
    (wholePlaneSchwartzVelocityCoefficients vel).value
  have hseedScaled := Measure.ae_smul_measure (vel.coeFn_toLp ∞ volume)
    (ENNReal.ofReal (ell ^ 2))
  have hseed :=
    (measurePreserving_wholePlaneAffine center ell hell).quasiMeasurePreserving.ae_eq_comp
      hseedScaled
  have hsmul := Lp.coeFn_smul (ell : ℂ)
    (wholePlaneCoeffPullback C3 center ell hell
      (wholePlaneSchwartzVelocityCoefficients vel).value)
  change (((ell : ℂ) •
      wholePlaneCoeffPullback C3 center ell hell
        (wholePlaneSchwartzVelocityCoefficients vel).value :
          WholePlaneC3LInf) : WholePlane → C3) =ᵐ[volume] _
  filter_upwards [hsmul, hpull, hseed] with y hsmul_y hpull_y hseed_y
  rw [hsmul_y]
  simp only [Pi.smul_apply]
  rw [hpull_y]
  change (ell : ℂ) • ((vel.toLp ∞ volume : WholePlaneC3LInf) : WholePlane → C3)
      (wholePlaneAffine center ell y) = _
  rw [show ((vel.toLp ∞ volume : WholePlaneC3LInf) : WholePlane → C3)
        (wholePlaneAffine center ell y) = vel (wholePlaneAffine center ell y) by
      simpa only [Function.comp_apply] using hseed_y]
  simpa only [hcenter, hell', pairToWholePlane_coordinatePair] using
    (parameterizedHelicalCellSource_eq_affineRepresentative h P angularSpeed axialSpeed n
      (y 0, y 1)).symm

/-- Each stored derivative coefficient of the rescaled-coefficient package at the cell `n` is
represented by the corresponding placed Euclidean derivative. -/
theorem rescaledHelicalCoefficients_deriv_ae (n : ℕ) (j : Fin 2) :
    (((rescaledWholePlaneVelocityCoefficients
        (wholePlaneSchwartzVelocityCoefficients
          (parameterizedSmoothedVelocity h angularSpeed axialSpeed))
        (pairToWholePlane (P.scaleFamily.cellCenter n))
        (P.scaleFamily.ell n) (P.scaleFamily.ell_pos n)).deriv j : WholePlane → C3)) =ᵐ[volume]
      fun y ↦ parameterizedHelicalCellSourceDeriv h P angularSpeed axialSpeed n j (y 0, y 1) := by
  set center : WholePlane := pairToWholePlane (P.scaleFamily.cellCenter n) with hcenter
  set ell : ℝ := P.scaleFamily.ell n with hell'
  have hell : 0 < ell := P.scaleFamily.ell_pos n
  set vel : SchwartzMap WholePlane C3 :=
    parameterizedSmoothedVelocity h angularSpeed axialSpeed with hvel
  have hpull := wholePlaneCoeffPullback_coe_ae C3 center ell hell
    ((wholePlaneSchwartzVelocityCoefficients vel).deriv j)
  have hseedScaled := Measure.ae_smul_measure
    ((∂_{wholePlaneBasis j} vel).coeFn_toLp ∞ volume) (ENNReal.ofReal (ell ^ 2))
  have hseed :=
    (measurePreserving_wholePlaneAffine center ell hell).quasiMeasurePreserving.ae_eq_comp
      hseedScaled
  change ((wholePlaneCoeffPullback C3 center ell hell
      ((wholePlaneSchwartzVelocityCoefficients vel).deriv j) : WholePlaneC3LInf) :
        WholePlane → C3) =ᵐ[volume] _
  filter_upwards [hpull, hseed] with y hpull_y hseed_y
  rw [hpull_y]
  change (((∂_{wholePlaneBasis j} vel).toLp ∞ volume : WholePlaneC3LInf) : WholePlane → C3)
      (wholePlaneAffine center ell y) = _
  have hseed_y' : (((∂_{wholePlaneBasis j} vel).toLp ∞ volume : WholePlaneC3LInf) :
      WholePlane → C3) (wholePlaneAffine center ell y) =
      (∂_{wholePlaneBasis j} vel) (wholePlaneAffine center ell y) := by
    simpa only [Function.comp_apply] using hseed_y
  rw [hseed_y']
  simpa only [hcenter, hell', pairToWholePlane_coordinatePair] using
    (parameterizedHelicalCellSourceDeriv_eq_affineRepresentative h P angularSpeed axialSpeed n j
      (y 0, y 1)).symm

/-! ## The global velocity on the closed three-quarter buffer disc -/

variable (tau : ℝ) (htau : 0 ≤ tau)

/-- **The splitting of `eq:global-u` on the constant axial region** (the paragraph after
`eq:axial-offset`): on the
closed disc `closedBall(p_n, 3R_n/4)` the global velocity is the placed local copy plus the constant
axial vector `a_n e₃`, because the other cells are supported in disjoint buffers and the axial
plateau equals one there. -/
theorem parameterizedFullGlobalTorusSource_eq_cell_add_axial (n : ℕ) {q : TransverseTorus}
    (hq : pairEuclideanDist (transverseIocRepresentative q) (P.scaleFamily.cellCenter n) ≤
      3 * P.scaleFamily.bufferRadius n / 4) :
    parameterizedFullGlobalTorusSource h P angularSpeed axialSpeed tau q =
      parameterizedHelicalCellSource h P angularSpeed axialSpeed n
          (transverseIocRepresentative q) +
        complexifyR3 (P.scaleFamily.axialAmplitude tau n • axialUnitR3) := by
  rw [parameterizedFullGlobalTorusSource,
    parameterizedHelicalGlobalTorusSource_eq_cell_of_mem_buffer h P angularSpeed axialSpeed
      (P.mem_torusBufferDisk_of_representative_dist_le_three_quarters n hq),
    torusSource_eq_source_transverseIocRepresentative h P angularSpeed axialSpeed n q,
    P.axialOffsetGlobalTorus_eq_axialAmplitude_of_representative_core tau n hq]

/-- The same splitting for the stored derivatives: the constant axial plateau contributes
nothing. -/
theorem parameterizedFullGlobalTorusFirstDerivative_eq_cell (n : ℕ) (j : Fin 2)
    {q : TransverseTorus}
    (hq : pairEuclideanDist (transverseIocRepresentative q) (P.scaleFamily.cellCenter n) ≤
      3 * P.scaleFamily.bufferRadius n / 4) :
    parameterizedFullGlobalTorusFirstDerivative h P angularSpeed axialSpeed tau j q =
      parameterizedHelicalCellSourceDeriv h P angularSpeed axialSpeed n j
        (transverseIocRepresentative q) := by
  rw [parameterizedFullGlobalTorusFirstDerivative,
    parameterizedHelicalGlobalTorusFirstDerivative_eq_cell_of_mem_buffer h P angularSpeed
      axialSpeed (P.mem_torusBufferDisk_of_representative_dist_le_three_quarters n hq) j,
    torusFirstDerivative_eq_firstDerivative_transverseIocRepresentative h P angularSpeed
      axialSpeed n j q,
    P.axialOffsetGlobalTorusDerivative_eq_zero_of_representative_core tau n j hq, map_zero,
    add_zero]

/-! ## The agreement record -/

/-- **`ChartCoefficientAgreement` at the selected cell** (proof of `lem:parametrix-error`): on
the closed disc
`closedBall(p_n, 3R_n/4)`, the support of the auxiliary cut-off `psi-tilde_n`, the global torus
velocity
and the rescaled seed velocity have the same transverse coordinates and the same gradient
coefficients, and their axial coordinates differ by exactly the plateau amplitude `a_n`. -/
theorem chartCoefficientAgreement_parameterizedFullGlobalW1Inf (n : ℕ) :
    TorusChartActionBridge.ChartCoefficientAgreement
      (closedBall (pairToWholePlane (P.scaleFamily.cellCenter n))
        (3 * P.scaleFamily.bufferRadius n / 4))
      (parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau)
      (rescaledWholePlaneVelocityCoefficients
        (wholePlaneSchwartzVelocityCoefficients
          (parameterizedSmoothedVelocity h angularSpeed axialSpeed))
        (pairToWholePlane (P.scaleFamily.cellCenter n))
        (P.scaleFamily.ell n) (P.scaleFamily.ell_pos n))
      (P.scaleFamily.axialAmplitude tau n) := by
  classical
  set v : WholePlaneVelocityCoefficients :=
    rescaledWholePlaneVelocityCoefficients
      (wholePlaneSchwartzVelocityCoefficients
        (parameterizedSmoothedVelocity h angularSpeed axialSpeed))
      (pairToWholePlane (P.scaleFamily.cellCenter n))
      (P.scaleFamily.ell n) (P.scaleFamily.ell_pos n) with hv
  have hvalueRestrict : ((v.value : WholePlane → C3)) =ᵐ[volume.restrict
      TorusChartL2.wholePlaneFundamentalBox]
      fun y ↦ parameterizedHelicalCellSource h P angularSpeed axialSpeed n (y 0, y 1) :=
    (rescaledHelicalCoefficients_value_ae h P angularSpeed axialSpeed n).filter_mono
      (ae_mono Measure.restrict_le_self)
  have hvalueChart :=
    measurePreserving_torusWholePlaneRepresentative.quasiMeasurePreserving.ae_eq_comp
      hvalueRestrict
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have hcoordRestrict :
        ((wholePlaneCoordLInf j.castSucc v.value : WholePlane → ℂ)) =ᵐ[volume.restrict
          TorusChartL2.wholePlaneFundamentalBox]
          fun y ↦ (v.value : WholePlane → C3) y j.castSucc :=
      ((EuclideanSpace.proj (𝕜 := ℂ) j.castSucc).coeFn_compLpL v.value).filter_mono
        (ae_mono Measure.restrict_le_self)
    have hcoordChart :=
      measurePreserving_torusWholePlaneRepresentative.quasiMeasurePreserving.ae_eq_comp
        hcoordRestrict
    filter_upwards [transverseW1InfComplexValueCoord_parameterizedFullGlobalW1Inf_coe_ae
        h P angularSpeed axialSpeed tau htau j.castSucc, hcoordChart, hvalueChart]
      with q hfull hcoord hvalueq hmem
    have hq := pairEuclideanDist_le_of_mem_closedBall P n hmem
    rw [hfull, parameterizedFullGlobalTorusSource_eq_cell_add_axial h P angularSpeed axialSpeed
      tau n hq]
    have hcoord' : (wholePlaneCoordLInf j.castSucc v.value : WholePlane → ℂ)
        (torusWholePlaneRepresentative q) =
        (v.value : WholePlane → C3) (torusWholePlaneRepresentative q) j.castSucc := by
      simpa only [Function.comp_apply] using hcoord
    have hvalue' : (v.value : WholePlane → C3) (torusWholePlaneRepresentative q) =
        parameterizedHelicalCellSource h P angularSpeed axialSpeed n
          (transverseIocRepresentative q) := by
      simpa only [Function.comp_apply, coordinatePair_torusWholePlaneRepresentative] using hvalueq
    rw [hcoord', hvalue', PiLp.add_apply]
    have haxial : complexifyR3 (P.scaleFamily.axialAmplitude tau n • axialUnitR3)
        j.castSucc = 0 := by
      simp [complexifyR3_apply, axialUnitR3, castSucc_ne_two j]
    rw [haxial, add_zero]
  · have hcoordRestrict :
        ((wholePlaneCoordLInf (2 : Fin 3) v.value : WholePlane → ℂ)) =ᵐ[volume.restrict
          TorusChartL2.wholePlaneFundamentalBox]
          fun y ↦ (v.value : WholePlane → C3) y 2 :=
      ((EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).coeFn_compLpL v.value).filter_mono
        (ae_mono Measure.restrict_le_self)
    have hcoordChart :=
      measurePreserving_torusWholePlaneRepresentative.quasiMeasurePreserving.ae_eq_comp
        hcoordRestrict
    filter_upwards [transverseW1InfComplexValueCoord_parameterizedFullGlobalW1Inf_coe_ae
        h P angularSpeed axialSpeed tau htau (2 : Fin 3), hcoordChart, hvalueChart]
      with q hfull hcoord hvalueq hmem
    have hq := pairEuclideanDist_le_of_mem_closedBall P n hmem
    rw [hfull, parameterizedFullGlobalTorusSource_eq_cell_add_axial h P angularSpeed axialSpeed
      tau n hq]
    have hcoord' : (wholePlaneCoordLInf (2 : Fin 3) v.value : WholePlane → ℂ)
        (torusWholePlaneRepresentative q) =
        (v.value : WholePlane → C3) (torusWholePlaneRepresentative q) 2 := by
      simpa only [Function.comp_apply] using hcoord
    have hvalue' : (v.value : WholePlane → C3) (torusWholePlaneRepresentative q) =
        parameterizedHelicalCellSource h P angularSpeed axialSpeed n
          (transverseIocRepresentative q) := by
      simpa only [Function.comp_apply, coordinatePair_torusWholePlaneRepresentative] using hvalueq
    rw [hcoord', hvalue', PiLp.add_apply]
    have haxial : complexifyR3 (P.scaleFamily.axialAmplitude tau n • axialUnitR3) (2 : Fin 3) =
        ((P.scaleFamily.axialAmplitude tau n : ℝ) : ℂ) := by
      simp [complexifyR3_apply, axialUnitR3]
    rw [haxial]
  · intro j
    have hderivRestrict : ((v.deriv j : WholePlane → C3)) =ᵐ[volume.restrict
        TorusChartL2.wholePlaneFundamentalBox]
        fun y ↦ parameterizedHelicalCellSourceDeriv h P angularSpeed axialSpeed n j (y 0, y 1) :=
      (rescaledHelicalCoefficients_deriv_ae h P angularSpeed axialSpeed n j).filter_mono
        (ae_mono Measure.restrict_le_self)
    have hderivChart :=
      measurePreserving_torusWholePlaneRepresentative.quasiMeasurePreserving.ae_eq_comp
        hderivRestrict
    filter_upwards [transverseW1InfComplexDeriv_parameterizedFullGlobalW1Inf_coe_ae
        h P angularSpeed axialSpeed tau htau j, hderivChart] with q hfull hderivq hmem
    have hq := pairEuclideanDist_le_of_mem_closedBall P n hmem
    rw [hfull, parameterizedFullGlobalTorusFirstDerivative_eq_cell h P angularSpeed axialSpeed
      tau n j hq]
    have hderiv' : (v.deriv j : WholePlane → C3) (torusWholePlaneRepresentative q) =
        parameterizedHelicalCellSourceDeriv h P angularSpeed axialSpeed n j
          (transverseIocRepresentative q) := by
      simpa only [Function.comp_apply, coordinatePair_torusWholePlaneRepresentative] using hderivq
    rw [hderiv']

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
