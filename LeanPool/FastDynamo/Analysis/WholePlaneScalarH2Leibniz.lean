/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneCoordinateH1

/-!
# Scalar weak Leibniz rule on whole-plane `H²`

This module upgrades the scalar `W¹,∞ × H¹ → H¹` multiplier theorem to
second order, for `C3`-valued fields multiplied by a scalar coefficient.  A
`WholePlaneScalarW2InfCertificate` records all ordered weak second derivatives
of the coefficient.  The product jet is then assembled componentwise from
bounded `L∞ × L² → L²` multiplication and restricted to the closed whole-plane
`H²` graph.

The resulting continuous linear map has exact value, first-derivative,
ordered-second-derivative, and Laplacian product rules.  Ordered derivatives
are retained throughout: the `(j,k)` coordinate means `∂_k ∂_j`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped LineDeriv

/-- A bounded scalar coefficient with bounded weak first and ordered second
derivatives.  The second-derivative field `secondDeriv j k` represents
`∂_k ∂_j value`. -/
structure WholePlaneScalarW2InfCertificate
    extends WholePlaneScalarW1InfCertificate where
  /-- Ordered bounded weak second derivatives. -/
  secondDeriv : Fin 2 → Fin 2 → WholePlaneScalarLInf
  /-- `secondDeriv j k` is the `k`-th weak derivative of `deriv j`. -/
  hasWeakSecondDerivative : ∀ j k,
    HasWholePlaneLInfWeakDerivative k (deriv j) (secondDeriv j k)

namespace WholePlaneScalarW2InfCertificate

/-- The certified `W¹,∞` row formed by the `j`-th derivative of a certified
`W²,∞` coefficient. -/
def derivativeCertificate (a : WholePlaneScalarW2InfCertificate)
    (j : Fin 2) : WholePlaneScalarW1InfCertificate where
  value := a.deriv j
  deriv := a.secondDeriv j
  hasWeakDerivative := a.hasWeakSecondDerivative j

/-- The value of the `j`-th derivative row of a `W²,∞` certificate is the coefficient's `j`-th
bounded weak derivative. -/
@[simp] theorem derivativeCertificate_value
    (a : WholePlaneScalarW2InfCertificate) (j : Fin 2) :
    (a.derivativeCertificate j).value = a.deriv j := by
  rfl

/-- The `k`-th derivative stored by the `j`-th derivative row is the ordered second derivative
`∂_k ∂_j` of the coefficient. -/
@[simp] theorem derivativeCertificate_deriv
    (a : WholePlaneScalarW2InfCertificate) (j k : Fin 2) :
    (a.derivativeCertificate j).deriv k = a.secondDeriv j k := by
  rfl

/-- The bounded scalar representing the weak Laplacian of the coefficient. -/
def laplacian (a : WholePlaneScalarW2InfCertificate) :
    WholePlaneScalarLInf :=
  ∑ j : Fin 2, a.secondDeriv j j

end WholePlaneScalarW2InfCertificate

/-! ## Componentwise `C3` multiplier -/

/-- Whole-plane multiplication of a `C3`-valued `L²` field by a bounded
scalar coefficient. -/
def wholePlaneScalarMulC3L2 :
    WholePlaneScalarLInf →L[ℂ]
      WholePlaneC3L2 →L[ℂ] WholePlaneC3L2 :=
  scalarVectorMulL2 volume

/-- Scalar coordinate extraction commutes with scalar multiplication of a
`C3`-valued `L²` field. -/
theorem wholePlaneCoordL2_scalarMulC3L2
    (a : WholePlaneScalarLInf) (b : WholePlaneC3L2) (i : Fin 3) :
    wholePlaneCoordL2 i (wholePlaneScalarMulC3L2 a b) =
      wholePlaneScalarMulL2 a (wholePlaneCoordL2 i b) := by
  apply Lp.ext
  have hout :
      ((wholePlaneCoordL2 i (wholePlaneScalarMulC3L2 a b) :
          WholePlaneScalarL2) : WholePlane → ℂ) =ᵐ[volume]
        fun x => (EuclideanSpace.proj i)
          ((wholePlaneScalarMulC3L2 a b : WholePlane → C3) x) := by
    simpa only [wholePlaneCoordL2] using
      (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
        (p := 2) (μ := (volume : Measure WholePlane))
        (wholePlaneScalarMulC3L2 a b)
  have hmul :
      (wholePlaneScalarMulC3L2 a b : WholePlane → C3) =ᵐ[volume]
        fun x => a x • b x := by
    simpa only [wholePlaneScalarMulC3L2] using
      scalarVectorMulL2_coe_ae (E := C3) volume a b
  have hb :
      (wholePlaneCoordL2 i b : WholePlane → ℂ) =ᵐ[volume]
        fun x => (EuclideanSpace.proj i) ((b : WholePlane → C3) x) := by
    simpa only [wholePlaneCoordL2] using
      (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
        (p := 2) (μ := (volume : Measure WholePlane)) b
  have hrhs := wholePlaneScalarMulL2_coe_ae a (wholePlaneCoordL2 i b)
  filter_upwards [hout, hmul, hb, hrhs] with x ho hm hbi hr
  rw [ho, hm, hr, hbi]
  simp

/-- The proposed first derivative of a scalar-times-`C3` `H²` product. -/
def wholePlaneScalarMulC3H2FirstJet
    (a : WholePlaneScalarW2InfCertificate) (u : WholePlaneC3H2)
    (j : Fin 2) : WholePlaneC3L2 :=
  wholePlaneScalarMulC3L2 (a.deriv j) (wholePlaneH2Embedding C3 u) +
    wholePlaneScalarMulC3L2 a.value
      (wholePlaneH2FirstDerivative C3 j u)

/-- The proposed ordered second derivative of a scalar-times-`C3` `H²`
product. -/
def wholePlaneScalarMulC3H2SecondJet
    (a : WholePlaneScalarW2InfCertificate) (u : WholePlaneC3H2)
    (j k : Fin 2) : WholePlaneC3L2 :=
  (wholePlaneScalarMulC3L2 (a.secondDeriv j k)
        (wholePlaneH2Embedding C3 u) +
      wholePlaneScalarMulC3L2 (a.deriv j)
        (wholePlaneH2FirstDerivative C3 k u)) +
    (wholePlaneScalarMulC3L2 (a.deriv k)
        (wholePlaneH2FirstDerivative C3 j u) +
      wholePlaneScalarMulC3L2 a.value
        (wholePlaneH2SecondDerivative C3 j k u))

/-- Component form of the first weak-derivative Leibniz identity for a certified scalar
coefficient times a `C3`-valued `H²` field: after extracting component `i` the identity reduces to
the scalar `W¹,∞ × H¹` product rule. -/
private theorem wholePlaneScalarMulC3H2_weakFirstDerivative_coord
    (a : WholePlaneScalarW2InfCertificate) (u : WholePlaneC3H2)
    (j : Fin 2) (i : Fin 3) :
    wholePlaneCoordTempered i
        (∂_{wholePlaneBasis j}
          (wholePlaneL2ToTempered C3
            (wholePlaneScalarMulC3L2 a.value
              (wholePlaneH2Embedding C3 u)))) =
      wholePlaneCoordTempered i
        (wholePlaneL2ToTempered C3
          (wholePlaneScalarMulC3H2FirstJet a u j)) := by
  rw [wholePlaneCoordTempered_lineDeriv]
  rw [wholePlaneCoordTempered_l2, wholePlaneCoordTempered_l2]
  rw [wholePlaneCoordL2_scalarMulC3L2]
  unfold wholePlaneScalarMulC3H2FirstJet
  rw [map_add, wholePlaneCoordL2_scalarMulC3L2,
    wholePlaneCoordL2_scalarMulC3L2]
  simpa only [HasWholePlaneL2WeakDerivative,
    wholePlaneH1Embedding_coordH1,
    wholePlaneH1FirstDerivative_coordH1,
    wholePlaneH1Embedding_H2ToH1,
    wholePlaneH1FirstDerivative_H2ToH1] using
    hasWholePlaneL2WeakDerivative_mul_h1
      a.toWholePlaneScalarW1InfCertificate
      (wholePlaneCoordH1 i (wholePlaneH2ToH1 C3 u)) j

/-- The exact first vector-valued weak derivative equation for multiplication
of a `C3` `H²` field by a certified scalar coefficient. -/
theorem wholePlaneScalarMulC3H2_weakFirstDerivative
    (a : WholePlaneScalarW2InfCertificate) (u : WholePlaneC3H2)
    (j : Fin 2) :
    ∂_{wholePlaneBasis j}
        (wholePlaneL2ToTempered C3
          (wholePlaneScalarMulC3L2 a.value
            (wholePlaneH2Embedding C3 u))) =
      wholePlaneL2ToTempered C3
        (wholePlaneScalarMulC3H2FirstJet a u j) := by
  ext phi i
  exact DFunLike.congr_fun
    (wholePlaneScalarMulC3H2_weakFirstDerivative_coord a u j i) phi

/-- Component form of the ordered second weak-derivative Leibniz identity: the `k`-th weak
derivative of the proposed first jet agrees, in each component, with the proposed second jet. -/
private theorem wholePlaneScalarMulC3H2_weakSecondDerivative_coord
    (a : WholePlaneScalarW2InfCertificate) (u : WholePlaneC3H2)
    (j k : Fin 2) (i : Fin 3) :
    wholePlaneCoordTempered i
        (∂_{wholePlaneBasis k}
          (wholePlaneL2ToTempered C3
            (wholePlaneScalarMulC3H2FirstJet a u j))) =
      wholePlaneCoordTempered i
        (wholePlaneL2ToTempered C3
          (wholePlaneScalarMulC3H2SecondJet a u j k)) := by
  rw [wholePlaneCoordTempered_lineDeriv]
  rw [wholePlaneCoordTempered_l2, wholePlaneCoordTempered_l2]
  unfold wholePlaneScalarMulC3H2FirstJet
    wholePlaneScalarMulC3H2SecondJet
  simp only [map_add, LineDeriv.lineDerivOp_add,
    wholePlaneCoordL2_scalarMulC3L2]
  have hleft := hasWholePlaneL2WeakDerivative_mul_h1
    (a.derivativeCertificate j)
    (wholePlaneCoordH1 i (wholePlaneH2ToH1 C3 u)) k
  have hright := hasWholePlaneL2WeakDerivative_mul_h1
    a.toWholePlaneScalarW1InfCertificate
    (wholePlaneCoordH1 i
      (wholePlaneFirstDerivativeToH1 C3 j u)) k
  unfold HasWholePlaneL2WeakDerivative at hleft hright
  simpa only [map_add, LineDeriv.lineDerivOp_add,
    wholePlaneH1Embedding_coordH1,
    wholePlaneH1FirstDerivative_coordH1,
    wholePlaneH1Embedding_H2ToH1,
    wholePlaneH1FirstDerivative_H2ToH1,
    wholePlaneH1Embedding_firstDerivativeToH1,
    wholePlaneH1FirstDerivative_firstDerivativeToH1,
    WholePlaneScalarW2InfCertificate.derivativeCertificate_value,
    WholePlaneScalarW2InfCertificate.derivativeCertificate_deriv] using
    congrArg₂ (fun x y => x + y) hleft hright

/-- The exact ordered second vector-valued weak derivative equation. -/
theorem wholePlaneScalarMulC3H2_weakSecondDerivative
    (a : WholePlaneScalarW2InfCertificate) (u : WholePlaneC3H2)
    (j k : Fin 2) :
    ∂_{wholePlaneBasis k}
        (wholePlaneL2ToTempered C3
          (wholePlaneScalarMulC3H2FirstJet a u j)) =
      wholePlaneL2ToTempered C3
        (wholePlaneScalarMulC3H2SecondJet a u j k) := by
  ext phi i
  exact DFunLike.congr_fun
    (wholePlaneScalarMulC3H2_weakSecondDerivative_coord a u j k i) phi

/-- Ambient second-order jet for scalar multiplication of a `C3` field. -/
def wholePlaneScalarMulC3H2Ambient
    (a : WholePlaneScalarW2InfCertificate) :
    WholePlaneC3H2 →L[ℂ] WholePlaneH2Ambient C3 :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : WholePlaneJet2Index => WholePlaneC3L2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun q => q.elim
      (fun r => r.elim
        ((wholePlaneScalarMulC3L2 a.value).comp
          (wholePlaneH2Embedding C3))
        (fun j =>
          (wholePlaneScalarMulC3L2 (a.deriv j)).comp
              (wholePlaneH2Embedding C3) +
            (wholePlaneScalarMulC3L2 a.value).comp
              (wholePlaneH2FirstDerivative C3 j)))
      (fun jk =>
        (((wholePlaneScalarMulC3L2 (a.secondDeriv jk.1 jk.2)).comp
              (wholePlaneH2Embedding C3) +
            (wholePlaneScalarMulC3L2 (a.deriv jk.1)).comp
              (wholePlaneH2FirstDerivative C3 jk.2)) +
          ((wholePlaneScalarMulC3L2 (a.deriv jk.2)).comp
              (wholePlaneH2FirstDerivative C3 jk.1) +
            (wholePlaneScalarMulC3L2 a.value).comp
              (wholePlaneH2SecondDerivative C3 jk.1 jk.2)))))

/-- Value coordinate of the `C3`-valued scalar product jet: the `L²` product `a·u`. -/
@[simp] theorem wholePlaneScalarMulC3H2Ambient_value
    (a : WholePlaneScalarW2InfCertificate) (u : WholePlaneC3H2) :
    wholePlaneScalarMulC3H2Ambient a u (Sum.inl none) =
      wholePlaneScalarMulC3L2 a.value (wholePlaneH2Embedding C3 u) := by
  rfl

/-- First-derivative coordinate of the `C3`-valued scalar product jet: the Leibniz expression
`(∂_j a)·u + a·(∂_j u)`. -/
@[simp] theorem wholePlaneScalarMulC3H2Ambient_firstDerivative
    (a : WholePlaneScalarW2InfCertificate) (u : WholePlaneC3H2)
    (j : Fin 2) :
    wholePlaneScalarMulC3H2Ambient a u (Sum.inl (some j)) =
      wholePlaneScalarMulC3H2FirstJet a u j := by
  rfl

/-- Ordered second-derivative coordinate of the `C3`-valued scalar product jet: the four-term
Leibniz expression `(∂_k ∂_j a)·u + (∂_j a)·(∂_k u) + (∂_k a)·(∂_j u) + a·(∂_k ∂_j u)`. -/
@[simp] theorem wholePlaneScalarMulC3H2Ambient_secondDerivative
    (a : WholePlaneScalarW2InfCertificate) (u : WholePlaneC3H2)
    (j k : Fin 2) :
    wholePlaneScalarMulC3H2Ambient a u (Sum.inr (j, k)) =
      wholePlaneScalarMulC3H2SecondJet a u j k := by
  rfl

/-- Bounded scalar multiplication on the whole-plane `C3`-valued weak `H²`
graph. -/
def wholePlaneScalarMulC3H2
    (a : WholePlaneScalarW2InfCertificate) :
    WholePlaneC3H2 →L[ℂ] WholePlaneC3H2 :=
  (wholePlaneScalarMulC3H2Ambient a).codRestrict
    (wholePlaneH2Graph C3) (fun u => by
      rw [mem_wholePlaneH2Graph_iff]
      constructor
      · intro j
        simpa only [wholePlaneScalarMulC3H2Ambient_value,
          wholePlaneScalarMulC3H2Ambient_firstDerivative] using
          wholePlaneScalarMulC3H2_weakFirstDerivative a u j
      · intro j k
        simpa only [wholePlaneScalarMulC3H2Ambient_firstDerivative,
          wholePlaneScalarMulC3H2Ambient_secondDerivative] using
          wholePlaneScalarMulC3H2_weakSecondDerivative a u j k)

/-- Exact physical value of the `C3` second-order multiplier. -/
theorem wholePlaneH2Embedding_scalarMulC3H2
    (a : WholePlaneScalarW2InfCertificate) (u : WholePlaneC3H2) :
    wholePlaneH2Embedding C3 (wholePlaneScalarMulC3H2 a u) =
      wholePlaneScalarMulC3L2 a.value
        (wholePlaneH2Embedding C3 u) := by
  rfl

/-- Exact first weak derivative of the `C3` second-order multiplier. -/
theorem wholePlaneH2FirstDerivative_scalarMulC3H2
    (a : WholePlaneScalarW2InfCertificate) (u : WholePlaneC3H2)
    (j : Fin 2) :
    wholePlaneH2FirstDerivative C3 j (wholePlaneScalarMulC3H2 a u) =
      wholePlaneScalarMulC3H2FirstJet a u j := by
  rfl

/-- Exact ordered second weak derivative of the `C3` multiplier. -/
theorem wholePlaneH2SecondDerivative_scalarMulC3H2
    (a : WholePlaneScalarW2InfCertificate) (u : WholePlaneC3H2)
    (j k : Fin 2) :
    wholePlaneH2SecondDerivative C3 j k (wholePlaneScalarMulC3H2 a u) =
      wholePlaneScalarMulC3H2SecondJet a u j k := by
  rfl

/-- The `C3`-valued contraction of the coefficient gradient with the field
gradient. -/
def wholePlaneScalarGradientDotC3H2
    (a : WholePlaneScalarW2InfCertificate) (u : WholePlaneC3H2) :
    WholePlaneC3L2 :=
  ∑ j : Fin 2,
    wholePlaneScalarMulC3L2 (a.deriv j)
      (wholePlaneH2FirstDerivative C3 j u)

/-- Exact vector-valued weak Laplacian product rule. -/
theorem wholePlaneLaplacian_scalarMulC3H2
    (a : WholePlaneScalarW2InfCertificate) (u : WholePlaneC3H2) :
    wholePlaneLaplacian C3 (wholePlaneScalarMulC3H2 a u) =
      wholePlaneScalarMulC3L2 a.value (wholePlaneLaplacian C3 u) +
        (2 : ℂ) • wholePlaneScalarGradientDotC3H2 a u +
        wholePlaneScalarMulC3L2 a.laplacian
          (wholePlaneH2Embedding C3 u) := by
  rw [wholePlaneLaplacian_apply,
    wholePlaneH2SecondDerivative_scalarMulC3H2,
    wholePlaneH2SecondDerivative_scalarMulC3H2,
    wholePlaneLaplacian_apply]
  simp only [wholePlaneScalarMulC3H2SecondJet,
    WholePlaneScalarW2InfCertificate.laplacian,
    wholePlaneScalarGradientDotC3H2, Fin.sum_univ_two, map_add,
    add_apply, two_smul]
  abel

end

end FastDynamo
