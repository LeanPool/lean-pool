/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusChartC2AuxiliaryCutoff

/-!
# The transported field and the two-component `commutator_eq`

This module closes the selected half of the proof of `lem:parametrix-error` at the
two-component fibre.  With

* `ed_R := extendDomainC2 p R hR` the output transport at the cut-off radius `R`,
* `ed_aux := extendDomainC2 p (3R/2)` the output transport at the auxiliary radius, whose
  profile `auxiliaryCutoff_n` is one on `supp ψ_n`,

the two facts proved here are

1. `ψ_n · (ed_aux w) = ed_R w` — multiplying the transported field by the periodized output
   cut-off recovers the smaller transport (`eq:parametrix-cutoff-identities` through the chart);
2. `ψ_n · (A_{ε,K} (ed_aux w)) = extendStateC2 (A^{(n)}_{ε,K,a} w)` — the chart action
   bridge of `Global/TorusChartActionBridge.lean` at the auxiliary radius, followed by the
   locality identity of `Global/TorusChartC2AuxiliaryCutoff.lean`.

Subtracting them gives exactly the `commutator_eq` field of `SelectedLocalResolventData`:
the two-component localization defect of the chart transports, evaluated at `w`, is the torus
commutator `[A_{ε,K}, ψ_n]` evaluated at the transported field `ed_aux w =
auxiliaryCutoff_n·w|_{T²}`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Metric Set

namespace TorusChartC2Transfer

open ParametrixCutoffs
open ParametrixExplicitCutoff
open TorusChartActionBridge
open TorusChartH2
open TorusChartL2
open LocalizedSummandAlgebra
open TorusPlacedCutoffC2
open TorusSupportedH2Output
open TransverseSmoothBumpPeriodization
open WholePlaneHorizontalFibre

variable (p : WholePlane) (R : ℝ) (hR : 0 < R)

/-! ## Two chart identities for the periodized output cut-off -/

/-- Multiplying the auxiliary output transport by the periodized output cut-off `ψ_n` returns
the output transport at the original radius. -/
theorem outputMul_stateMul_extendStateC2_aux
    (hbox : closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox)
    (Y : WholePlaneC2L2) :
    (outputMul p R hR).stateMul
        (extendStateC2 p (auxOutputRadius R) (auxOutputRadius_pos hR) Y) =
      extendStateC2 p R hR Y := by
  apply Lp.ext
  filter_upwards [scalarVectorMulL2_coe_ae (E := C2) transverseMeasure (outputMul p R hR).value
      (extendStateC2 p (auxOutputRadius R) (auxOutputRadius_pos hR) Y),
    outputMul_value_ae p R hR hbox,
    horizontalProjL2_coe_ae (wholePlaneOutputLocalizationL2 p (auxOutputRadius R)
      (auxOutputRadius_pos hR) (wholePlaneVerticalZeroExtendL2 Y)),
    wholePlaneOutputLocalizationL2_coe_ae p (auxOutputRadius R) (auxOutputRadius_pos hR)
      (wholePlaneVerticalZeroExtendL2 Y),
    horizontalProjL2_coe_ae (wholePlaneOutputLocalizationL2 p R hR
      (wholePlaneVerticalZeroExtendL2 Y)),
    wholePlaneOutputLocalizationL2_coe_ae p R hR (wholePlaneVerticalZeroExtendL2 Y)]
      with q h1 h2 h3 h4 h5 h6
  have hstate : (((outputMul p R hR).stateMul
        (extendStateC2 p (auxOutputRadius R) (auxOutputRadius_pos hR) Y) :
          TransverseC2L2) : TransverseTorus → C2) q =
      ((outputMul p R hR).value : TransverseTorus → ℂ) q •
        ((extendStateC2 p (auxOutputRadius R) (auxOutputRadius_pos hR) Y :
          TransverseC2L2) : TransverseTorus → C2) q := h1
  have hleft : ((extendStateC2 p (auxOutputRadius R) (auxOutputRadius_pos hR) Y :
        TransverseC2L2) : TransverseTorus → C2) q =
      horizontalProjPoint (((wholePlaneOutputLocalizationL2 p (auxOutputRadius R)
        (auxOutputRadius_pos hR) (wholePlaneVerticalZeroExtendL2 Y)) :
          TransverseTorus → C3) q) := h3
  have hright : ((extendStateC2 p R hR Y : TransverseC2L2) : TransverseTorus → C2) q =
      horizontalProjPoint (((wholePlaneOutputLocalizationL2 p R hR
        (wholePlaneVerticalZeroExtendL2 Y)) : TransverseTorus → C3) q) := h5
  rw [hstate, hleft, hright, h4, h6, h2, map_smul, map_smul, smul_smul,
    torusWholePlaneRepresentative_eq_iocRepresentative]
  congr 1
  unfold outputCutoffComplex
  rw [← Complex.ofReal_mul,
    outputCutoff_mul_auxOutputCutoff p R hR (wholePlaneIocRepresentative q)]

/-- The periodized output cut-off acting after chart descent is chart descent after the
whole-plane output cut-off. -/
theorem outputMul_stateMul_horizontalProjL2_wholePlaneToTorusL2
    (hbox : closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox)
    (Z : WholePlaneC3L2) :
    (outputMul p R hR).stateMul (horizontalProjL2 (wholePlaneToTorusL2 Z)) =
      horizontalProjL2 (wholePlaneToTorusL2 (outputCutoffMulL2 p R hR Z)) := by
  apply Lp.ext
  have hmul : ((outputCutoffMulL2 p R hR Z : WholePlaneC3L2) : WholePlane → C3) =ᵐ[volume]
      fun x ↦ (outputCutoffLInf p R hR : WholePlane → ℂ) x • (Z : WholePlane → C3) x :=
    scalarVectorMulL2_coe_ae (E := C3) volume (outputCutoffLInf p R hR) Z
  have hmulRestrict : ((outputCutoffMulL2 p R hR Z : WholePlaneC3L2) : WholePlane → C3)
      =ᵐ[volume.restrict wholePlaneFundamentalBox]
        fun x ↦ (outputCutoffLInf p R hR : WholePlane → ℂ) x • (Z : WholePlane → C3) x :=
    hmul.filter_mono (ae_mono Measure.restrict_le_self)
  have hmulChart : (fun q ↦ ((outputCutoffMulL2 p R hR Z : WholePlaneC3L2) : WholePlane → C3)
        (torusWholePlaneRepresentative q)) =ᵐ[transverseMeasure]
      fun q ↦ (outputCutoffLInf p R hR : WholePlane → ℂ) (torusWholePlaneRepresentative q) •
        (Z : WholePlane → C3) (torusWholePlaneRepresentative q) :=
    measurePreserving_torusWholePlaneRepresentative.quasiMeasurePreserving.ae_eq_comp
      hmulRestrict
  have hcoeff : (outputCutoffLInf p R hR : WholePlane → ℂ) =ᵐ[volume]
      outputCutoffComplex p R hR := outputCutoffLInf_coe_ae p R hR
  have hcoeffRestrict : (outputCutoffLInf p R hR : WholePlane → ℂ)
      =ᵐ[volume.restrict wholePlaneFundamentalBox] outputCutoffComplex p R hR :=
    hcoeff.filter_mono (ae_mono Measure.restrict_le_self)
  have hcoeffChart : (fun q ↦ (outputCutoffLInf p R hR : WholePlane → ℂ)
        (torusWholePlaneRepresentative q)) =ᵐ[transverseMeasure]
      fun q ↦ outputCutoffComplex p R hR (torusWholePlaneRepresentative q) :=
    measurePreserving_torusWholePlaneRepresentative.quasiMeasurePreserving.ae_eq_comp
      hcoeffRestrict
  filter_upwards [scalarVectorMulL2_coe_ae (E := C2) transverseMeasure (outputMul p R hR).value
      (horizontalProjL2 (wholePlaneToTorusL2 Z)),
    outputMul_value_ae p R hR hbox,
    horizontalProjL2_coe_ae (wholePlaneToTorusL2 Z),
    wholePlaneToTorusL2_coe_ae Z,
    horizontalProjL2_coe_ae (wholePlaneToTorusL2 (outputCutoffMulL2 p R hR Z)),
    wholePlaneToTorusL2_coe_ae (outputCutoffMulL2 p R hR Z), hmulChart, hcoeffChart]
      with q h1 h2 h3 h4 h5 h6 h7 h8
  have hstate : (((outputMul p R hR).stateMul (horizontalProjL2 (wholePlaneToTorusL2 Z)) :
        TransverseC2L2) : TransverseTorus → C2) q =
      ((outputMul p R hR).value : TransverseTorus → ℂ) q •
        ((horizontalProjL2 (wholePlaneToTorusL2 Z) : TransverseC2L2) :
          TransverseTorus → C2) q := h1
  rw [hstate, h3, h4, h5, h6, h7, h8, h2, map_smul,
    torusWholePlaneRepresentative_eq_iocRepresentative]
  rfl

/-! ## The transported field -/

variable (u : TransverseRealW1Inf) (epsilon : ℝ) (K : ℤ)
  (v : WholePlaneVelocityCoefficients) (shift : ℝ)

/-- Multiplying the auxiliary output transport by `ψ_n` returns the output transport at the
original radius, at `H²` regularity: the auxiliary cut-off `auxiliaryCutoff_n` is one on `supp
ψ_n`. -/
theorem outputMul_domainMul_extendDomainC2_aux
    (hboxIoc : closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox)
    (hbox : closedBall p (R / 2) ⊆ wholePlaneFundamentalBox)
    (hboxAux : closedBall p (auxOutputRadius R / 2) ⊆ wholePlaneFundamentalBox)
    (w : WholePlaneC2H2) :
    (outputMul p R hR).domainMul
        (extendDomainC2 p (auxOutputRadius R) (auxOutputRadius_pos hR) hboxAux w) =
      extendDomainC2 p R hR hbox w := by
  apply transverseH2Embedding_injective
  rw [(outputMul p R hR).embedding_domainMul,
    transverseH2Embedding_extendDomainC2 p (auxOutputRadius R) (auxOutputRadius_pos hR)
      hboxAux w,
    transverseH2Embedding_extendDomainC2 p R hR hbox w]
  exact outputMul_stateMul_extendStateC2_aux p R hR hboxIoc (wholePlaneH2Embedding C2 w)

/-- The torus action of the transported field, multiplied by `ψ_n`, is the output transport of
the selected whole-plane action.  This is the chart action bridge at the auxiliary radius
followed by the locality identity for `auxiliaryCutoff_n`. -/
theorem outputMul_stateMul_horizontalInductionAction_extendDomainC2_aux
    (hboxIoc : closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox)
    (hboxAux : closedBall p (auxOutputRadius R / 2) ⊆ wholePlaneFundamentalBox)
    (hagree : ChartCoefficientAgreement (closedBall p (auxOutputRadius R / 2)) u v shift)
    (w : WholePlaneC2H2) :
    (outputMul p R hR).stateMul (horizontalInductionAction u epsilon K
        (extendDomainC2 p (auxOutputRadius R) (auxOutputRadius_pos hR) hboxAux w)) =
      extendStateC2 p R hR (selectedWholePlaneC2InductionAction v epsilon K shift w) := by
  have hbridge := reducedInductionAction_chart
    (b := outputCutoffToChartSupportedH2 p (auxOutputRadius R) (auxOutputRadius_pos hR)
      hboxAux (wholePlaneVerticalZeroExtendH2 w))
    epsilon K hagree
    (outputCutoffToChartSupportedH2_supportedIn_closedHalfBall p (auxOutputRadius R)
      (auxOutputRadius_pos hR) hboxAux (wholePlaneVerticalZeroExtendH2 w))
  have htorus : horizontalInductionAction u epsilon K
        (extendDomainC2 p (auxOutputRadius R) (auxOutputRadius_pos hR) hboxAux w) =
      horizontalProjL2 (wholePlaneToTorusL2 (selectedWholePlaneInductionAction v epsilon K shift
        (wholePlaneScalarMulC3H2 (outputCutoffW2InfCertificate p (auxOutputRadius R)
          (auxOutputRadius_pos hR)) (wholePlaneVerticalZeroExtendH2 w)))) := by
    rw [extendDomainC2_apply,
      ← horizontalProjL2_reducedInductionAction u epsilon K
        (wholePlaneOutputLocalizationH2 p (auxOutputRadius R) (auxOutputRadius_pos hR)
          hboxAux (wholePlaneVerticalZeroExtendH2 w))]
    rw [show wholePlaneOutputLocalizationH2 p (auxOutputRadius R) (auxOutputRadius_pos hR)
        hboxAux (wholePlaneVerticalZeroExtendH2 w) =
      wholePlaneChartToTransverseH2 (outputCutoffToChartSupportedH2 p (auxOutputRadius R)
        (auxOutputRadius_pos hR) hboxAux (wholePlaneVerticalZeroExtendH2 w)) from rfl, hbridge]
    rfl
  have hplane : wholePlaneHorizontalProjL2 (selectedWholePlaneInductionAction v epsilon K shift
        (wholePlaneVerticalZeroExtendH2 w)) =
      selectedWholePlaneC2InductionAction v epsilon K shift w := by
    rw [wholePlaneHorizontalProjL2_selectedWholePlaneInductionAction,
      wholePlaneHorizontalProjH2_wholePlaneVerticalZeroExtendH2]
  rw [htorus,
    outputMul_stateMul_horizontalProjL2_wholePlaneToTorusL2 p R hR hboxIoc,
    outputCutoffMulL2_selectedAction_auxMul p R hR v epsilon K shift
      (wholePlaneVerticalZeroExtendH2 w),
    ← hplane]
  exact (extendStateC2_wholePlaneHorizontalProjL2 p R hR
    (selectedWholePlaneInductionAction v epsilon K shift
      (wholePlaneVerticalZeroExtendH2 w))).symm

/-- **The two-component `commutator_eq`.**  The localization defect of the chart transports at
radius `R`, evaluated at a whole-plane `H²` field `w`, is the torus commutator `[A_{ε,K}, ψ_n]`
evaluated at the transported field `auxiliaryCutoff_n·w|_{T²}` (the Lean form of the selected
summand of
`eq:Rapp`).  This is the selected half of the proof of `lem:parametrix-error`. -/
theorem localizationCommutatorC2_eq_horizontalCutoffCommutator
    (hboxIoc : closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox)
    (hbox : closedBall p (R / 2) ⊆ wholePlaneFundamentalBox)
    (hboxAux : closedBall p (auxOutputRadius R / 2) ⊆ wholePlaneFundamentalBox)
    (hagree : ChartCoefficientAgreement (closedBall p (auxOutputRadius R / 2)) u v shift)
    (w : WholePlaneC2H2) :
    localizationCommutator (horizontalInductionOperator u epsilon K)
        (selectedWholePlaneC2InductionOperator v epsilon K shift)
        (extendDomainC2 p R hR hbox) (extendStateC2 p R hR) w =
      HorizontalCutoffCommutator.commutator (outputMul p R hR) u epsilon K
        (extendDomainC2 p (auxOutputRadius R) (auxOutputRadius_pos hR) hboxAux w) := by
  have h1 := outputMul_domainMul_extendDomainC2_aux p R hR hboxIoc hbox hboxAux w
  have h2 := outputMul_stateMul_horizontalInductionAction_extendDomainC2_aux
    p R hR u epsilon K v shift hboxIoc hboxAux hagree w
  change horizontalInductionAction u epsilon K (extendDomainC2 p R hR hbox w) -
      extendStateC2 p R hR (selectedWholePlaneC2InductionAction v epsilon K shift w) = _
  rw [← h1, ← h2]
  rfl

end TorusChartC2Transfer

end

end FastDynamo
