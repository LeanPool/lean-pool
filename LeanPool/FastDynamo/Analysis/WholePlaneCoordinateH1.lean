/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import Mathlib.LinearAlgebra.CrossProduct
public import LeanPool.FastDynamo.Analysis.WholePlaneScalarLeibniz
public import LeanPool.FastDynamo.Analysis.WholePlaneCoordinateDistributions

/-!
# Coordinates of whole-plane weak H¹ fields and of bounded coefficients

This module provides the coordinate interface between vector-valued and scalar
whole-plane fields used in the local form argument.  Coordinate extraction is a
bounded map from the three-vector weak `H¹` graph to the scalar one, compatible
with the `L²` value and with each weak derivative (`wholePlaneCoordH1`).  A
bounded three-vector coefficient accompanied by its two bounded distributional
derivatives (`HasWholePlaneLInfWeakGradient`) yields, coordinate by coordinate,
a scalar `W¹,∞` certificate (`wholePlaneCoordW1InfCertificate`), to which the
scalar weak Leibniz theorem applies.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal LineDeriv SchwartzMap

/-! ## Scalar coordinates of vector-valued H¹ -/

/-- Continuous ambient scalar jet obtained by extracting one coordinate of a
three-vector weak `H¹` jet. -/
def wholePlaneCoordH1Ambient (i : Fin 3) :
    WholePlaneC3H1 →L[ℂ] WholePlaneH1Ambient ℂ :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : WholePlaneJet1Index => WholePlaneScalarL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun q => q.elim
      ((wholePlaneCoordL2 i).comp (wholePlaneH1Embedding C3))
      (fun j =>
        (wholePlaneCoordL2 i).comp
          (wholePlaneH1FirstDerivative C3 j)))

/-- The value slot of the coordinate jet is the `i`th coordinate of the `L²` value of the
vector `H¹` field. -/
@[simp] theorem wholePlaneCoordH1Ambient_none (i : Fin 3)
    (b : WholePlaneC3H1) :
    wholePlaneCoordH1Ambient i b none =
      wholePlaneCoordL2 i (wholePlaneH1Embedding C3 b) := by
  rfl

/-- The `j`th derivative slot of the coordinate jet is the `i`th coordinate of the `j`th
weak derivative of the vector `H¹` field. -/
@[simp] theorem wholePlaneCoordH1Ambient_some (i : Fin 3)
    (b : WholePlaneC3H1) (j : Fin 2) :
    wholePlaneCoordH1Ambient i b (some j) =
      wholePlaneCoordL2 i (wholePlaneH1FirstDerivative C3 j b) := by
  rfl

/-- Coordinate extraction as a bounded map from vector-valued weak `H¹` to
scalar weak `H¹`. -/
def wholePlaneCoordH1 (i : Fin 3) :
    WholePlaneC3H1 →L[ℂ] WholePlaneScalarH1 :=
  (wholePlaneCoordH1Ambient i).codRestrict
    (wholePlaneH1Graph ℂ) (fun b => by
      rw [mem_wholePlaneH1Graph_iff]
      intro j
      simp only [wholePlaneCoordH1Ambient_none,
        wholePlaneCoordH1Ambient_some]
      rw [← wholePlaneCoordTempered_l2,
        ← wholePlaneCoordTempered_l2,
        ← wholePlaneCoordTempered_lineDeriv,
        wholePlaneH1_firstDerivative_distribution])

/-- Coordinate extraction on the `H¹` graph is compatible with the `L²` value map: the
value of `wholePlaneCoordH1 i b` is the `i`th coordinate of the value of `b`. -/
theorem wholePlaneH1Embedding_coordH1 (i : Fin 3)
    (b : WholePlaneC3H1) :
    wholePlaneH1Embedding ℂ (wholePlaneCoordH1 i b) =
      wholePlaneCoordL2 i (wholePlaneH1Embedding C3 b) := by
  rfl

/-- Coordinate extraction on the `H¹` graph commutes with taking the `j`th weak
derivative. -/
theorem wholePlaneH1FirstDerivative_coordH1 (i : Fin 3)
    (j : Fin 2) (b : WholePlaneC3H1) :
    wholePlaneH1FirstDerivative ℂ j (wholePlaneCoordH1 i b) =
      wholePlaneCoordL2 i (wholePlaneH1FirstDerivative C3 j b) := by
  rfl

/-! ## Coordinate certificates for bounded vector coefficients -/

/-- A bounded three-vector coefficient together with its bounded
weak transverse derivatives. -/
def HasWholePlaneLInfWeakGradient
    (w : WholePlaneC3LInf) (dw : Fin 2 → WholePlaneC3LInf) : Prop :=
  ∀ j : Fin 2,
    ∂_{wholePlaneBasis j} (wholePlaneLInfToTempered C3 w) =
      wholePlaneLInfToTempered C3 (dw j)

/-- Coordinate extraction commutes with the canonical whole-plane
`L∞ → tempered distributions` embedding. -/
theorem wholePlaneCoordTempered_linf (i : Fin 3)
    (b : WholePlaneC3LInf) :
    wholePlaneCoordTempered i (wholePlaneLInfToTempered C3 b) =
      wholePlaneLInfToTempered ℂ (wholePlaneCoordLInf i b) := by
  ext phi
  simp only [wholePlaneCoordTempered_apply_apply,
    wholePlaneLInfToTempered,
    MeasureTheory.Lp.toTemperedDistributionCLM_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply]
  have hint : Integrable (fun x : WholePlane ↦ phi x • (b x : C3)) volume :=
    memLp_one_iff_integrable.mp <|
      (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] C3 →L[ℂ] C3).memLp_of_bilin
        1 (phi.memLp 1 volume) (Lp.memLp b)
  calc
    (EuclideanSpace.proj i)
          (∫ x : WholePlane, phi x • (b x : C3) ∂volume) =
        ∫ x : WholePlane,
          (EuclideanSpace.proj i) (phi x • (b x : C3)) ∂volume :=
      ((EuclideanSpace.proj i).integral_comp_comm hint).symm
    _ = ∫ x : WholePlane,
          phi x • ((wholePlaneCoordLInf i b : WholePlane → ℂ) x)
          ∂volume := by
      apply integral_congr_ae
      filter_upwards [
        (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
          (p := ∞) (μ := (volume : Measure WholePlane)) b] with x hx
      calc
        (EuclideanSpace.proj i) (phi x • (b x : C3)) =
            phi x • (EuclideanSpace.proj i) (b x : C3) := by simp
        _ = phi x • ((wholePlaneCoordLInf i b : WholePlane → ℂ) x) := by
          simpa [wholePlaneCoordLInf] using
            congrArg (fun z : ℂ ↦ phi x • z) hx.symm

/-- A coordinate of a certified bounded vector coefficient, bundled with its
two scalar bounded weak derivatives. -/
def wholePlaneCoordW1InfCertificate
    (w : WholePlaneC3LInf) (dw : Fin 2 → WholePlaneC3LInf)
    (hw : HasWholePlaneLInfWeakGradient w dw) (i : Fin 3) :
    WholePlaneScalarW1InfCertificate where
  value := wholePlaneCoordLInf i w
  deriv j := wholePlaneCoordLInf i (dw j)
  hasWeakDerivative j := by
    unfold HasWholePlaneLInfWeakDerivative
    rw [← wholePlaneCoordTempered_linf,
      ← wholePlaneCoordTempered_linf,
      ← wholePlaneCoordTempered_lineDeriv,
      hw j]

end

end FastDynamo
