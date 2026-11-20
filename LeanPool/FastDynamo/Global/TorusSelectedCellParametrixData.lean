/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusSelectedLocalResolventData
public import LeanPool.FastDynamo.Global.TorusParametrixError

/-!
# The two-summand parametrix datum at a selected cell, and the global contour resolvent

This module assembles `TorusTwoSummandParametrix.TwoSummandParametrixData` at one cell, as in
§7.1 of the paper, from

* the three placed cut-offs `φ_n`, `ψ_n`, `χ_n` of `Global/TorusPlacedCutoffC2.lean`;
* the background resolvent datum of `Global/TorusTwoSummandParametrix.lean` (produced from §6 by
  `Global/TorusBackgroundParametrixBridge.lean`);
* the selected local resolvent datum of `Global/TorusSelectedLocalResolventData.lean`;
* the three velocity facts of `Global/TorusPlacedCutoffVelocity.lean`, whose
  `TransverseVelocityLocalized` and coefficient-agreement hypotheses are taken here as explicit
  arguments — they are statements about the global velocity field and are discharged by the
  parameter chain, not by §6.

The last theorem is `lem:global-contour-resolvent` under the explicit threshold
`scaleErrorMajorant … < 1` in place of `eq:error-small` (the paper enlarges `K_0` until the
error is below `η_* < 1/2`; here any majorant below `1` suffices for the resolvent).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Metric Set

namespace TorusChartC2Transfer

open HorizontalCutoffCommutator
open ParametrixCutoffs
open TorusChartActionBridge
open TorusParametrixError
open TorusPlacedCutoffC2
open TorusTwoSummandParametrix
open TransverseSmoothBumpPeriodization

variable {v : WholePlaneVelocityCoefficients} {pt : WholePlane}
  {s : WholePlaneExactScalingParameters} {S : Set ℂ} {bound deltaUpper : ℝ}
  {u ubg : TransverseRealW1Inf} {p : WholePlane} {R : ℝ}

/-- **The two-summand parametrix datum at the selected cell** (`eq:Rapp`).
The velocity hypotheses are explicit: `hlocalized` says that the transverse velocity is
supported, modulo a null set, in the core `D(p_n, inner)` or outside `D(p_n, outer)` with
`inner ≤ R/10` and `R/2 ≤ outer`, and `hvalue`/`hderiv` say that the full and background
coefficients agree off `closedBall(p_n, R/10)`. -/
def selectedCellParametrixData (hR : 0 < R)
    (hbox : closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox)
    (hboxAux : closedBall p (auxOutputRadius R / 2) ⊆ TorusChartL2.wholePlaneFundamentalBox)
    (L : WholePlaneLocalResolventBound v s.N s.delta S bound)
    (hbound : 0 ≤ bound) (hepsilon : 0 ≤ s.epsilon) (hdelta : 0 ≤ s.delta)
    (hle : s.delta ≤ deltaUpper)
    (hagree : ChartCoefficientAgreement (closedBall p (auxOutputRadius R / 2)) u
      (rescaledWholePlaneVelocityCoefficients v pt s.ell s.ell_pos) s.a)
    (bg : BackgroundParametrixData ubg s.epsilon s.K (verticallyShiftedSet s.tau S))
    {inner outer : ℝ} (hinner : inner ≤ R / 10) (houter : R / 2 ≤ outer)
    (hlocalized : TransverseVelocityLocalized p inner outer u)
    (hvalue : ∀ i : Fin 3, ∀ᵐ q ∂transverseMeasure,
      dist (wholePlaneIocRepresentative q) p ≤ R / 10 ∨
        (transverseW1InfComplexValueCoordLInf i u) q =
          (transverseW1InfComplexValueCoordLInf i ubg) q)
    (hderiv : ∀ j : Fin 2, ∀ᵐ q ∂transverseMeasure,
      dist (wholePlaneIocRepresentative q) p ≤ R / 10 ∨
        (transverseW1InfHorizontalDerivLInf j u) q =
          (transverseW1InfHorizontalDerivLInf j ubg) q) :
    TwoSummandParametrixData WholePlaneC2L2 WholePlaneC2H2 u ubg s.epsilon s.K R
      (verticallyShiftedSet s.tau S) where
  cutoffs := placedCutoffs p R hR hbox
  background := bg
  selected := selectedLocalResolventData hR hbox hboxAux L hbound hepsilon hdelta hle hagree
  backgroundAgreement :=
    backgroundMul_agreement p R hR hbox u ubg s.epsilon s.K hvalue hderiv
  backgroundVanishes :=
    velocityVanishesOnGradient_backgroundMul p R hR hbox u hinner
      (by linarith [hR] : R / 6 ≤ outer) hlocalized
  outputVanishes :=
    velocityVanishesOnGradient_outputMul p R hR hbox u
      (by linarith [hR] : inner ≤ R / 3) houter hlocalized

/-- **`lem:global-contour-resolvent`** at the selected cell: under the explicit
numerical threshold `scaleErrorMajorant … < 1` (cf. `eq:error-small`), the whole contour `Γ_τ`
lies in the resolvent set of the torus operator `A_{ε,K_n}`. -/
def selectedCellGlobalContourResolvent (hR : 0 < R)
    (hbox : closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox)
    (hboxAux : closedBall p (auxOutputRadius R / 2) ⊆ TorusChartL2.wholePlaneFundamentalBox)
    (L : WholePlaneLocalResolventBound v s.N s.delta S bound)
    (hbound : 0 ≤ bound) (hepsilonPos : 0 < s.epsilon) (hdelta : 0 ≤ s.delta)
    (hle : s.delta ≤ deltaUpper)
    (hagree : ChartCoefficientAgreement (closedBall p (auxOutputRadius R / 2)) u
      (rescaledWholePlaneVelocityCoefficients v pt s.ell s.ell_pos) s.a)
    (bg : BackgroundParametrixData ubg s.epsilon s.K (verticallyShiftedSet s.tau S))
    {inner outer : ℝ} (hinner : inner ≤ R / 10) (houter : R / 2 ≤ outer)
    (hlocalized : TransverseVelocityLocalized p inner outer u)
    (hvalue : ∀ i : Fin 3, ∀ᵐ q ∂transverseMeasure,
      dist (wholePlaneIocRepresentative q) p ≤ R / 10 ∨
        (transverseW1InfComplexValueCoordLInf i u) q =
          (transverseW1InfComplexValueCoordLInf i ubg) q)
    (hderiv : ∀ j : Fin 2, ∀ᵐ q ∂transverseMeasure,
      dist (wholePlaneIocRepresentative q) p ≤ R / 10 ∨
        (transverseW1InfHorizontalDerivLInf j u) q =
          (transverseW1InfHorizontalDerivLInf j ubg) q)
    (hmaj : scaleErrorMajorant
      (parametrixErrorConstant bg.bound
        (selectedTransportedBound R s.epsilon deltaUpper bound)) s.epsilon R < 1) :
    HasResolventOn (horizontalInductionOperator u s.epsilon s.K)
      (verticallyShiftedSet s.tau S) :=
  globalContourResolvent
    (selectedCellParametrixData hR hbox hboxAux L hbound (le_of_lt hepsilonPos) hdelta hle
      hagree bg hinner houter hlocalized hvalue hderiv)
    hepsilonPos
    (error_norm_lt_one_of_majorant _ (le_of_lt hepsilonPos) hmaj)

end TorusChartC2Transfer

end

end FastDynamo
