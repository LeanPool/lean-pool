/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WeakLeibniz

/-!
# Velocity coefficients in the weak Leibniz rule

The velocity-facing part of `FastDynamo/Analysis/WeakLeibniz.lean`: the specialization of the
transverse weak Leibniz rule to one coordinate of a `W¹,∞` velocity field, the reality and
symmetry statements for multiplication by such a coefficient, and the public interfaces that
the induction layer uses — transverse divergence freedom and the velocity-times-scalar
multiplication operator with its coordinate identity.

The module is separate from `FastDynamo/Analysis/WeakLeibniz.lean` for build weight: that
module sits under some one hundred and fifty dependents, and no declaration there refers
to any declaration below.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-! ## Velocity-coordinate specialization -/

/-- Coordinate extraction commutes with real-to-complex conversion and the
probability-space inclusion `L∞ → L²`. -/
theorem transverseScalarLInfToL2_coord_complexify
    (v : TransverseR3LInf) (i : Fin 3) :
    transverseScalarLInfToL2
        (transverseCoordLInf i (complexifyR3LInf v)) =
      transverseCoordL2 i (complexifyR3LTwo v) := by
  apply Lp.ext
  have hinc := transverseScalarLInfToL2_coe_ae
    (transverseCoordLInf i (complexifyR3LInf v))
  have hcoordInf := (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
    (complexifyR3LInf v)
  have hcompInf := complexifyR3.coeFn_compLpL v
  have hcoordL2 := (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
    (complexifyR3LTwo v)
  have hcompL2 := complexifyR3LTwo_coe_ae v
  filter_upwards [hinc, hcoordInf, hcompInf, hcoordL2, hcompL2]
    with x hi hci hcInf hc2 hcL2
  rw [hi]
  change (((EuclideanSpace.proj (𝕜 := ℂ) i).compLpL ∞ transverseMeasure
      (complexifyR3LInf v) : TransverseScalarLInf) :
        TransverseTorus → ℂ) x =
    (((EuclideanSpace.proj (𝕜 := ℂ) i).compLpL 2 transverseMeasure
      (complexifyR3LTwo v) : TransverseScalarL2) :
        TransverseTorus → ℂ) x
  rw [hci, hc2]
  change ((complexifyR3LInf v : TransverseC3LInf) :
      TransverseTorus → C3) x = complexifyR3 (v x) at hcInf
  rw [hcInf, hcL2]
  rfl

/-- Every scalar coordinate of a bundled real `W^{1,∞}` velocity satisfies
the scalar Fourier weak-derivative relation with its stored derivative. -/
theorem transverseW1InfCoord_hasScalarFourierDerivative
    (u : TransverseRealW1Inf) (j : Fin 2) (i : Fin 3) :
    HasTransverseScalarFourierDerivative j
      (transverseScalarLInfToL2
        (transverseW1InfComplexValueCoordLInf i u))
      (transverseScalarLInfToL2
        (transverseW1InfComplexDerivCoordLInf j i u)) := by
  intro n
  rw [show transverseW1InfComplexValueCoordLInf i u =
      transverseCoordLInf i
        (complexifyR3LInf (transverseW1InfValue u)) by rfl,
    show transverseW1InfComplexDerivCoordLInf j i u =
      transverseCoordLInf i
        (complexifyR3LInf (transverseW1InfDeriv j u)) by rfl,
    transverseScalarLInfToL2_coord_complexify,
    transverseScalarLInfToL2_coord_complexify]
  change transverseRealCoeffCLM n i (transverseW1InfDeriv j u) =
    transverseFourierDerivMultiplier j n *
      transverseRealCoeffCLM n i (transverseW1InfValue u)
  exact transverseW1Inf_fourier_weakDeriv u j n i

/-- Velocity-coordinate form of the product scalar `H¹` weak Leibniz rule. -/
theorem productScalarH1_velocityCoord_weakLeibniz
    (u : TransverseRealW1Inf) (j : Fin 2) (i : Fin 3)
    (d : ProductScalarH1) :
    HasProductScalarFlatTransverseDerivative j
      (scalarMulProduct
        (pullTransverseScalarLInf
          (transverseW1InfComplexValueCoordLInf i u))
        (productScalarH1Embedding d))
      (scalarMulProduct
          (pullTransverseScalarLInf
            (transverseW1InfComplexDerivCoordLInf j i u))
          (productScalarH1Embedding d) +
        scalarMulProduct
          (pullTransverseScalarLInf
            (transverseW1InfComplexValueCoordLInf i u))
          (productScalarTransverseDerivFromH1 j d)) :=
  productScalarH1_weakLeibniz
    (transverseW1InfCoord_hasScalarFourierDerivative u j i) d

/-! ## Reality and symmetry of velocity multiplication -/

/-- An essentially bounded complex scalar coefficient is real-valued almost
everywhere. -/
def IsRealProductScalarLInf (a : ProductScalarLInf) : Prop :=
  ∀ᵐ x ∂productMeasure, starRingEnd ℂ (a x) = a x

/-- Every pulled scalar component of the real velocity is real-valued almost
everywhere. -/
theorem pull_velocityCoord_isReal
    (u : TransverseRealW1Inf) (i : Fin 3) :
    IsRealProductScalarLInf
      (pullTransverseScalarLInf
        (transverseW1InfComplexValueCoordLInf i u)) := by
  have hcoord := (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
    (transverseW1InfComplexValueLInf u)
  have hcomp := transverseW1InfComplexValueLInf_coe_ae u
  have hrealTrans : ∀ᵐ y ∂transverseMeasure,
      starRingEnd ℂ ((transverseW1InfComplexValueCoordLInf i u) y) =
        (transverseW1InfComplexValueCoordLInf i u) y := by
    filter_upwards [hcoord, hcomp] with y hc hv
    change ((transverseCoordLInf i
      (transverseW1InfComplexValueLInf u) : TransverseScalarLInf) :
        TransverseTorus → ℂ) y = _ at hc
    change starRingEnd ℂ
        (((transverseCoordLInf i
          (transverseW1InfComplexValueLInf u) : TransverseScalarLInf) :
            TransverseTorus → ℂ) y) =
      (((transverseCoordLInf i
        (transverseW1InfComplexValueLInf u) : TransverseScalarLInf) :
          TransverseTorus → ℂ) y)
    rw [hc, hv]
    simp
  have hrealProduct :=
    (measurePreserving_fst (μ := transverseMeasure) (ν := axialMeasure))
      |>.quasiMeasurePreserving |>.ae_eq_comp hrealTrans
  have hpull := pullTransverseScalarLInf_coe_ae
    (transverseW1InfComplexValueCoordLInf i u)
  filter_upwards [hrealProduct, hpull] with x hr hp
  rw [hp]
  exact hr

/-! ## Public velocity/divergence interfaces -/

/-- The `x₃`-independent velocity is divergence-free when the two stored
transverse diagonal weak derivatives sum to zero.  There is no axial term
because the velocity has no `x₃` dependence. -/
def IsTransverseDivergenceFree (u : TransverseRealW1Inf) : Prop :=
  transverseW1InfComplexDerivCoordLInf (0 : Fin 2) (0 : Fin 3) u +
    transverseW1InfComplexDerivCoordLInf (1 : Fin 2) (1 : Fin 3) u = 0

/-- The three scalar coordinates of the product field `u d`. -/
def productVelocityTimesScalarCoords (u : TransverseRealW1Inf) :
    ProductScalarL2 →L[ℂ] ProductC3CoordinateL2 :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin 3 => ProductScalarL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      scalarMulProduct
        (pullTransverseScalarLInf
          (transverseW1InfComplexValueCoordLInf i u)))

/-- Pointwise scalar multiplication `d ↦ u d`, as a quotient-level bounded
map `L²(C) → L²(C³)`. -/
def productVelocityTimesScalar (u : TransverseRealW1Inf) :
    ProductScalarL2 →L[ℂ] ProductC3L2 :=
  productC3OfCoordsL2.comp (productVelocityTimesScalarCoords u)

/-- The `i`th coordinate of the vector field `u d` is multiplication of the scalar `d` by
the `i`th essentially bounded component of the velocity, lifted `x₃`-independently to the
product torus. -/
@[simp] theorem productCoordL2_productVelocityTimesScalar
    (u : TransverseRealW1Inf) (d : ProductScalarL2) (i : Fin 3) :
    productCoordL2 i (productVelocityTimesScalar u d) =
      scalarMulProduct
        (pullTransverseScalarLInf
          (transverseW1InfComplexValueCoordLInf i u)) d := by
  rw [productVelocityTimesScalar, ContinuousLinearMap.comp_apply,
    productCoordL2_productC3OfCoordsL2]
  rfl

end

end FastDynamo
