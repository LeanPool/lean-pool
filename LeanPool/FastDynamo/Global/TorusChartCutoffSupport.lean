/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.TorusChartActionBridge

/-!
# The output cut-off jet is supported in the closed half-ball

The chart action bridge of `Global/TorusChartActionBridge.lean` identifies the torus action of a
chart-supported whole-plane `H²` jet with the chart image of the whole-plane action, under two
hypotheses: coefficient agreement on a set `s`, and support of the jet's value and first
derivatives in `s`.  This module supplies the second hypothesis for the jets produced by the
output cut-off: multiplying a whole-plane `H²` jet by the cut-off `ψ` at `(p, R)` gives a jet
whose value and first weak derivatives vanish almost everywhere off `closedBall(p, R/2)`
(`outputCutoffToChartSupportedH2_supportedIn_closedHalfBall`).
`Global/TorusChartC2TransportedField.lean` applies it at the auxiliary radius `3R/2`, in the
proof of the selected half of `lem:parametrix-error`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Metric Set

namespace TorusChartActionBridge

open ParametrixExplicitCutoff
open TorusChartH2
open TorusChartL2
open WholePlaneAESupport
open LocalizedSummandAlgebra
open TorusSupportedH2Output
open WholePlaneHorizontalFibre

variable (p : WholePlane) (R : ℝ) (hR : 0 < R)

/-! ## The output cut-off jet is supported in the closed half-ball -/

/-- Multiplying by a scalar `L∞` class that vanishes off `s` produces a class supported in `s`. -/
private theorem scalarMul_supportedIn {s : Set WholePlane}
    (a : WholePlaneScalarLInf) (f : WholePlaneC3L2)
    (ha : ∀ᵐ x ∂volume, x ∉ s → (a : WholePlane → ℂ) x = 0) :
    IsAEL2SupportedIn s (wholePlaneScalarMulC3L2 a f) := by
  have hmul : (wholePlaneScalarMulC3L2 a f : WholePlane → C3) =ᵐ[volume]
      fun x ↦ a x • f x := by
    simpa only [wholePlaneScalarMulC3L2] using scalarVectorMulL2_coe_ae (E := C3) volume a f
  filter_upwards [hmul, ha] with x hmulx hzero hx
  rw [hmulx, hzero hx, zero_smul]

/-- The output cut-off value vanishes almost everywhere off the closed half-ball. -/
private theorem outputCutoffValue_ae_zero_off_closedHalfBall :
    ∀ᵐ x ∂volume, x ∉ closedBall p (R / 2) →
      (((outputCutoffW2InfCertificate p R hR).value : WholePlane → ℂ) x) = 0 := by
  filter_upwards [outputCutoffW2InfCertificate_value_coe_ae p R hR] with x hx hout
  have hdist : R / 2 ≤ dist x p := le_of_lt (by simpa [mem_closedBall, not_le] using hout)
  rw [hx]
  unfold outputCutoffComplex
  rw [outputCutoff_eq_zero_of_radius_le_dist p R hR hdist]
  norm_num

/-- Each stored first derivative of the output cut-off vanishes almost everywhere off the closed
half-ball. -/
private theorem outputCutoffDeriv_ae_zero_off_closedHalfBall (j : Fin 2) :
    ∀ᵐ x ∂volume, x ∉ closedBall p (R / 2) →
      (((outputCutoffW2InfCertificate p R hR).deriv j : WholePlane → ℂ) x) = 0 := by
  filter_upwards [outputCutoffW2InfCertificate_deriv_coe_ae p R hR j] with x hx hout
  have hdist : R / 2 < dist x p := by simpa [mem_closedBall, not_le] using hout
  rw [hx, outputCutoff_coordinateDerivative_eq_zero_of_radius_lt_dist p R hR j hdist]
  norm_num

/-- The output-cut-off jet satisfies the support premise of the chart action bridge, with the
closed half-ball `closedBall(p, R/2)` as agreement set. -/
theorem outputCutoffToChartSupportedH2_supportedIn_closedHalfBall
    (hbox : closedBall p (R / 2) ⊆ wholePlaneFundamentalBox) (b : WholePlaneC3H2) :
    H2StateSupportedIn (closedBall p (R / 2))
      (outputCutoffToChartSupportedH2 p R hR hbox b) where
  value := by
    change IsAEL2SupportedIn (closedBall p (R / 2))
      (wholePlaneH2Embedding C3
        (wholePlaneScalarMulC3H2 (outputCutoffW2InfCertificate p R hR) b))
    rw [wholePlaneH2Embedding_scalarMulC3H2]
    exact scalarMul_supportedIn _ _ (outputCutoffValue_ae_zero_off_closedHalfBall p R hR)
  firstDerivative := fun j ↦ by
    change IsAEL2SupportedIn (closedBall p (R / 2))
      (wholePlaneH2FirstDerivative C3 j
        (wholePlaneScalarMulC3H2 (outputCutoffW2InfCertificate p R hR) b))
    rw [wholePlaneH2FirstDerivative_scalarMulC3H2]
    unfold wholePlaneScalarMulC3H2FirstJet
    exact isAEL2SupportedIn_add
      (scalarMul_supportedIn _ _ (outputCutoffDeriv_ae_zero_off_closedHalfBall p R hR j))
      (scalarMul_supportedIn _ _ (outputCutoffValue_ae_zero_off_closedHalfBall p R hR))

end TorusChartActionBridge

end

end FastDynamo
