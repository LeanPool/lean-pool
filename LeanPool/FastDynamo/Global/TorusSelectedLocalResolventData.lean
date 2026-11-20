/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.TorusChartC2TransportedBounds
public import LeanPool.FastDynamo.Global.WholePlaneScaledLocalResolvent
public import LeanPool.FastDynamo.Global.TorusTwoSummandParametrix

/-!
# The selected summand of `eq:Rapp`

This module assembles the record
`TorusTwoSummandParametrix.SelectedLocalResolventData WholePlaneC2L2 WholePlaneC2H2 u ε K Γ_τ
φ_n ψ_n` of §7.1 of the paper (`eq:Rapp` and `eq:parametrix-uniform-bound`) out of

* the conjugated whole-plane resolvent `R_n(z) = U_n R_{δ_n}(z + iτ) U_n⁻¹` of
  `Global/WholePlaneScaledLocalResolvent.lean` (`cor:scaled-local-resolvents`);
* the chart transports of `Global/TorusChartC2Transfer.lean` and the transported field
  `auxiliaryCutoff_n·(R_n(z)φ_n·)` of `Global/TorusChartC2AuxiliaryCutoff.lean`;
* the localization-defect identity of `Global/TorusChartC2TransportedField.lean`
  (`commutator_eq`, the coefficient agreement on `supp ψ_n` in the proof of
  `lem:parametrix-error`);
* the norm bounds of `Global/TorusChartC2TransportedBounds.lean`.

The one hypothesis that is *not* discharged here is the coefficient agreement
`ChartCoefficientAgreement` on the closed three-quarter buffer disc, which is a statement about
the velocity field and is discharged in `Global/TorusSelectedCellChartAgreement.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Metric Set

namespace TorusChartC2Transfer

open ParametrixExplicitCutoff
open TorusChartActionBridge
open TorusChartL2
open LocalizedSummandAlgebra
open TorusPlacedCutoffC2
open TorusTwoSummandParametrix
open TransverseSmoothBumpPeriodization

/-! ## The constant of the selected summand -/

/-- The constant of `eq:local-gradient` transported to the torus: the seed resolvent bound
`bound` inflated by the Leibniz factor of the auxiliary cut-off. -/
def selectedTransportedBound (R : ℝ) (epsilon deltaUpper bound : ℝ) : ℝ :=
  bound * (1 + Real.sqrt 2 *
    (firstDerivativeConstant / auxOutputRadius R * Real.sqrt epsilon +
      Real.sqrt deltaUpper))

/-- The Leibniz inflation factor is at least one. -/
theorem one_le_selectedTransportedFactor {R : ℝ} (hR : 0 < R) (epsilon deltaUpper : ℝ) :
    1 ≤ 1 + Real.sqrt 2 *
      (firstDerivativeConstant / auxOutputRadius R * Real.sqrt epsilon +
        Real.sqrt deltaUpper) := by
  have h1 : 0 ≤ firstDerivativeConstant / auxOutputRadius R * Real.sqrt epsilon :=
    mul_nonneg (div_nonneg (le_of_lt firstDerivativeConstant_pos)
      (le_of_lt (auxOutputRadius_pos hR))) (Real.sqrt_nonneg _)
  have h2 : 0 ≤ Real.sqrt deltaUpper := Real.sqrt_nonneg _
  nlinarith [Real.sqrt_nonneg 2]

/-- The transported bound is nonnegative. -/
theorem selectedTransportedBound_nonneg {R : ℝ} (hR : 0 < R) {epsilon deltaUpper bound : ℝ}
    (hbound : 0 ≤ bound) : 0 ≤ selectedTransportedBound R epsilon deltaUpper bound := by
  unfold selectedTransportedBound
  have h := one_le_selectedTransportedFactor hR epsilon deltaUpper
  nlinarith

/-- The seed bound is dominated by the transported bound. -/
theorem le_selectedTransportedBound {R : ℝ} (hR : 0 < R) {epsilon deltaUpper bound : ℝ}
    (hbound : 0 ≤ bound) : bound ≤ selectedTransportedBound R epsilon deltaUpper bound := by
  unfold selectedTransportedBound
  have h := one_le_selectedTransportedFactor hR epsilon deltaUpper
  nlinarith

/-! ## The record -/

variable {v : WholePlaneVelocityCoefficients} {pt : WholePlane}
  {s : WholePlaneExactScalingParameters} {S : Set ℂ} {bound deltaUpper : ℝ}
  {u : TransverseRealW1Inf} {p : WholePlane} {R : ℝ}

/-- **The selected local resolvent datum of `eq:Rapp`.**  All twelve fields of
`SelectedLocalResolventData` at the chart of a single cell: the local operator is the selected
whole-plane operator at the matching scaling parameters, the resolvent is `R_n(z)`, the three
transports are the chart maps of `Global/TorusChartC2Transfer.lean`, and the transported field
is `auxiliaryCutoff_n·(R_n(z)φ_n·)`. -/
def selectedLocalResolventData (hR : 0 < R)
    (hbox : closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox)
    (hboxAux : closedBall p (auxOutputRadius R / 2) ⊆ wholePlaneFundamentalBox)
    (L : WholePlaneLocalResolventBound v s.N s.delta S bound)
    (hbound : 0 ≤ bound) (hepsilon : 0 ≤ s.epsilon) (hdelta : 0 ≤ s.delta)
    (hle : s.delta ≤ deltaUpper)
    (hagree : ChartCoefficientAgreement (closedBall p (auxOutputRadius R / 2)) u
      (rescaledWholePlaneVelocityCoefficients v pt s.ell s.ell_pos) s.a) :
    SelectedLocalResolventData WholePlaneC2L2 WholePlaneC2H2 u s.epsilon s.K
      (verticallyShiftedSet s.tau S) (inputMul p R hR) (outputMul p R hR) where
  localOperator := selectedScaledOperator v pt s
  resolvent := scaledLocalResolventInv v pt s L
  restrictInput := restrictInputC2 p R hR
  extendDomain := extendDomainC2 p R hR hbox
  extendState := extendStateC2 p R hR
  transported := fun z ↦
    (extendDomainC2 p (auxOutputRadius R) (auxOutputRadius_pos hR) hboxAux).comp
      ((scaledLocalResolventInv v pt s L z).comp (restrictInputC2 p R hR))
  bound := selectedTransportedBound R s.epsilon deltaUpper bound
  bound_nonneg := selectedTransportedBound_nonneg hR hbound
  embedding_intertwining := transverseH2Embedding_comp_extendDomainC2 p R hR hbox
  right_inv := fun z hz ↦ (scaledLocalResolvent v pt s L).right_inv z hz
  roundTrip := extendStateC2_comp_restrictInputC2 p R hR hbox
  continuousOn := by
    have hres : ContinuousOn (scaledLocalResolventInv v pt s L)
        (verticallyShiftedSet s.tau S) := (scaledLocalResolvent v pt s L).continuousOn
    have hmid : ContinuousOn
        (fun z ↦ (scaledLocalResolventInv v pt s L z).comp (restrictInputC2 p R hR))
        (verticallyShiftedSet s.tau S) := hres.clm_comp continuousOn_const
    exact ContinuousOn.clm_comp continuousOn_const hmid
  commutator_eq := by
    intro z _hz
    apply ContinuousLinearMap.ext
    intro f
    exact localizationCommutatorC2_eq_horizontalCutoffCommutator p R hR u s.epsilon s.K
      (rescaledWholePlaneVelocityCoefficients v pt s.ell s.ell_pos) s.a hbox hbox hboxAux
      hagree (scaledLocalResolventInv v pt s L z (restrictInputC2 p R hR f))
  norm_le := by
    intro z hz f
    refine le_trans (norm_transverseH2Embedding_extendDomainC2_le p (auxOutputRadius R)
      (auxOutputRadius_pos hR) hboxAux _) ?_
    refine le_trans (norm_embedding_scaledLocalResolventInv_le v pt s L hz _) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (norm_restrictInputC2_apply_le p R hR f) hbound) ?_
    exact mul_le_mul_of_nonneg_right (le_selectedTransportedBound hR hbound) (norm_nonneg f)
  sqrt_gradient_le := by
    intro z hz f
    have hkey : ∀ j : Fin 2, Real.sqrt s.epsilon *
        ‖transverseVecDerivFromH2 (Fin 2) j
          ((extendDomainC2 p (auxOutputRadius R) (auxOutputRadius_pos hR) hboxAux).comp
            ((scaledLocalResolventInv v pt s L z).comp (restrictInputC2 p R hR)) f)‖ ≤
        (firstDerivativeConstant / auxOutputRadius R * Real.sqrt s.epsilon +
          Real.sqrt deltaUpper) * (bound * ‖f‖) := by
      intro j
      simp only [ContinuousLinearMap.comp_apply]
      have hgrad := norm_transverseVecDerivFromH2_extendDomainC2_le p (auxOutputRadius R)
        (auxOutputRadius_pos hR) hboxAux j
        (scaledLocalResolventInv v pt s L z (restrictInputC2 p R hR f))
      have hvalue := norm_embedding_scaledLocalResolventInv_le v pt s L hz
        (restrictInputC2 p R hR f)
      have hderiv := sqrt_epsilon_mul_norm_deriv_le_of_delta_le v pt s L hdelta hle hbound hz
        (restrictInputC2 p R hR f) j
      have hin : bound * ‖restrictInputC2 p R hR f‖ ≤ bound * ‖f‖ :=
        mul_le_mul_of_nonneg_left (norm_restrictInputC2_apply_le p R hR f) hbound
      have hcoef : 0 ≤ firstDerivativeConstant / auxOutputRadius R :=
        div_nonneg (le_of_lt firstDerivativeConstant_pos)
          (le_of_lt (auxOutputRadius_pos hR))
      have hvf : ‖wholePlaneH2Embedding C2
            (scaledLocalResolventInv v pt s L z (restrictInputC2 p R hR f))‖ ≤
          bound * ‖f‖ := hvalue.trans hin
      have h1 : Real.sqrt s.epsilon * ‖wholePlaneH2Embedding C2
            (scaledLocalResolventInv v pt s L z (restrictInputC2 p R hR f))‖ ≤
          Real.sqrt s.epsilon * (bound * ‖f‖) :=
        mul_le_mul_of_nonneg_left hvf (Real.sqrt_nonneg _)
      have h2 : Real.sqrt s.epsilon * ‖wholePlaneH2FirstDerivative C2 j
            (scaledLocalResolventInv v pt s L z (restrictInputC2 p R hR f))‖ ≤
          Real.sqrt deltaUpper * (bound * ‖f‖) :=
        hderiv.trans (mul_le_mul_of_nonneg_left hin (Real.sqrt_nonneg _))
      have hA := mul_le_mul_of_nonneg_left hgrad (Real.sqrt_nonneg s.epsilon)
      have hB : Real.sqrt s.epsilon *
            (firstDerivativeConstant / auxOutputRadius R * ‖wholePlaneH2Embedding C2
                (scaledLocalResolventInv v pt s L z (restrictInputC2 p R hR f))‖ +
              ‖wholePlaneH2FirstDerivative C2 j
                (scaledLocalResolventInv v pt s L z (restrictInputC2 p R hR f))‖) =
          firstDerivativeConstant / auxOutputRadius R *
              (Real.sqrt s.epsilon * ‖wholePlaneH2Embedding C2
                (scaledLocalResolventInv v pt s L z (restrictInputC2 p R hR f))‖) +
            Real.sqrt s.epsilon * ‖wholePlaneH2FirstDerivative C2 j
              (scaledLocalResolventInv v pt s L z (restrictInputC2 p R hR f))‖ := by
        ring
      have hC := mul_le_mul_of_nonneg_left h1 hcoef
      have hD : firstDerivativeConstant / auxOutputRadius R *
            (Real.sqrt s.epsilon * (bound * ‖f‖)) + Real.sqrt deltaUpper * (bound * ‖f‖) =
          (firstDerivativeConstant / auxOutputRadius R * Real.sqrt s.epsilon +
            Real.sqrt deltaUpper) * (bound * ‖f‖) := by
        ring
      linarith
    refine le_trans (sqrt_mul_transverseGradientEnergy_le hepsilon ?_ _ hkey) ?_
    · refine mul_nonneg ?_ (mul_nonneg hbound (norm_nonneg f))
      have hc : 0 ≤ firstDerivativeConstant / auxOutputRadius R :=
        div_nonneg (le_of_lt firstDerivativeConstant_pos) (le_of_lt (auxOutputRadius_pos hR))
      have hprod := mul_nonneg hc (Real.sqrt_nonneg s.epsilon)
      linarith [Real.sqrt_nonneg deltaUpper]
    · have hring : selectedTransportedBound R s.epsilon deltaUpper bound * ‖f‖ =
          bound * ‖f‖ + Real.sqrt 2 *
            ((firstDerivativeConstant / auxOutputRadius R * Real.sqrt s.epsilon +
              Real.sqrt deltaUpper) * (bound * ‖f‖)) := by
        unfold selectedTransportedBound
        ring
      rw [hring]
      linarith [mul_nonneg hbound (norm_nonneg f)]
  norm_summand_le := by
    intro z hz f
    refine le_trans (norm_transverseH2Embedding_extendDomainC2_le p R hR hbox _) ?_
    refine le_trans (norm_embedding_scaledLocalResolventInv_le v pt s L hz _) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (norm_restrictInputC2_apply_le p R hR f) hbound) ?_
    exact mul_le_mul_of_nonneg_right (le_selectedTransportedBound hR hbound) (norm_nonneg f)

end TorusChartC2Transfer

end

end FastDynamo
