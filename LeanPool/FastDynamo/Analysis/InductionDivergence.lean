/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.WeakLeibnizAxial
public import LeanPool.FastDynamo.Analysis.WeakLeibnizVelocity
public import LeanPool.FastDynamo.Analysis.ProductDivergenceEnergy
public import LeanPool.FastDynamo.Operator.Product

/-!
# Divergence of the product induction action

This module proves the weak vector identity `Div[-(u·∇)B + (B·∇)u] = -u·∇ Div B`.
The paper uses only the distributional curl identity
`curl(u×V) = (V·∇)u − (u·∇)V` in the proof of `lem:axial-recovery`; the divergence identity
proved here has no counterpart there.  It feeds the auxiliary solenoidality argument of
`FastDynamo.Finish.RealSolution`, itself a result of the formalisation that the paper does not
contain.

For an `x₃`-independent divergence-free velocity, the lower-order induction action plus
`u (div B)` is a weak curl.  Consequently its weak divergence vanishes, and the divergence of the
full induction action is the scalar diffusion term minus the weak divergence of `u (div B)`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-! ## Scalar coordinate notation -/

/-- One scalar product `uᵢ f`. -/
def productVelocityMul (u : TransverseRealW1Inf) (i : Fin 3)
    (f : ProductScalarL2) : ProductScalarL2 :=
  scalarMulProduct
    (pullTransverseScalarLInf
      (transverseW1InfComplexValueCoordLInf i u)) f

/-- Multiplication by the pulled-back scalar velocity component `uᵢ` is additive in its `L²`
argument. -/
@[simp] theorem productVelocityMul_add
    (u : TransverseRealW1Inf) (i : Fin 3)
    (f g : ProductScalarL2) :
    productVelocityMul u i (f + g) =
      productVelocityMul u i f + productVelocityMul u i g := by
  exact (scalarMulProduct
    (pullTransverseScalarLInf
      (transverseW1InfComplexValueCoordLInf i u))).map_add f g

/-- One scalar product `(∂ⱼuᵢ) f`. -/
def productVelocityDerivMul (u : TransverseRealW1Inf)
    (j : Fin 2) (i : Fin 3) (f : ProductScalarL2) : ProductScalarL2 :=
  scalarMulProduct
    (pullTransverseScalarLInf
      (transverseW1InfComplexDerivCoordLInf j i u)) f

/-- One scalar coordinate of the physical `H²` field. -/
def productH2Coord (B : ProductC3H2) (i : Fin 3) : ProductScalarL2 :=
  productCoordL2 i (productH2Embedding B)

/-- One transverse derivative of one scalar coordinate of an `H²` field. -/
def productH2TransverseDerivCoord (B : ProductC3H2)
    (j : Fin 2) (i : Fin 3) : ProductScalarL2 :=
  productCoordL2 i (productTransverseDerivFromH2 j B)

/-- The axial derivative of one scalar coordinate of an `H²` field. -/
def productH2AxialDerivCoord (B : ProductC3H2)
    (i : Fin 3) : ProductScalarL2 :=
  productCoordL2 i (productAxialDerivFromH2 B)

/-! ## Quotient-level coordinate bridges -/

/-- Extract one scalar coordinate from a complex vector-valued product
`L∞` field. -/
def productCoordLInf (i : Fin 3) :
    ProductC3LInf →L[ℂ] ProductScalarLInf :=
  (EuclideanSpace.proj (𝕜 := ℂ) i).compLpL ⊤ productMeasure

/-- Taking the `i`-th coordinate commutes with multiplication by a scalar `L∞` factor:
the `i`-th coordinate of `a • b` is `a` times the `i`-th coordinate of `b`. -/
@[simp] theorem productCoordL2_scalarVectorMulProduct
    (a : ProductScalarLInf) (b : ProductC3L2) (i : Fin 3) :
    productCoordL2 i (scalarVectorMulProduct a b) =
      scalarMulProduct a (productCoordL2 i b) := by
  apply Lp.ext
  have hmul := scalarVectorMulProduct_coe_ae a b
  have hcoordMul := (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
    (scalarVectorMulProduct a b)
  have hcoord := (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL b
  have hscalar := scalarMulProduct_coe_ae a (productCoordL2 i b)
  filter_upwards [hmul, hcoordMul, hcoord, hscalar] with x hm hcm hc hs
  have hc' : (EuclideanSpace.proj (𝕜 := ℂ) i) (b x) =
      ((productCoordL2 i b : ProductScalarL2) : ProductTorus3 → ℂ) x := by
    change (EuclideanSpace.proj (𝕜 := ℂ) i) (b x) =
      ((((EuclideanSpace.proj (𝕜 := ℂ) i).compLpL 2 productMeasure) b :
        ProductScalarL2) : ProductTorus3 → ℂ) x
    exact hc.symm
  calc
    ((productCoordL2 i (scalarVectorMulProduct a b) : ProductScalarL2) :
        ProductTorus3 → ℂ) x
        = (EuclideanSpace.proj (𝕜 := ℂ) i)
            ((scalarVectorMulProduct a b) x) := hcm
    _ = (EuclideanSpace.proj (𝕜 := ℂ) i) (a x • b x) := by rw [hm]
    _ = a x * (EuclideanSpace.proj (𝕜 := ℂ) i) (b x) := by
      exact map_smul (EuclideanSpace.proj (𝕜 := ℂ) i) (a x) (b x)
    _ = a x *
        (((productCoordL2 i b : ProductScalarL2) : ProductTorus3 → ℂ) x) := by
      rw [hc']
    _ = ((scalarMulProduct a (productCoordL2 i b) : ProductScalarL2) :
        ProductTorus3 → ℂ) x := hs.symm

/-- The `i`-th coordinate of a `C³`-valued `L∞` coefficient `a` times a scalar `L²` function `b`
is the scalar product of `b` with the `i`-th coordinate of `a`. -/
@[simp] theorem productCoordL2_vectorScalarMulProduct
    (a : ProductC3LInf) (b : ProductScalarL2) (i : Fin 3) :
    productCoordL2 i (vectorScalarMulProduct a b) =
      scalarMulProduct (productCoordLInf i a) b := by
  apply Lp.ext
  have hmul := vectorScalarMulProduct_coe_ae a b
  have hcoordMul := (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
    (vectorScalarMulProduct a b)
  have hcoord := (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL a
  have hscalar := scalarMulProduct_coe_ae (productCoordLInf i a) b
  filter_upwards [hmul, hcoordMul, hcoord, hscalar] with x hm hcm hc hs
  have hc' : (EuclideanSpace.proj (𝕜 := ℂ) i) (a x) =
      ((productCoordLInf i a : ProductScalarLInf) : ProductTorus3 → ℂ) x := by
    change (EuclideanSpace.proj (𝕜 := ℂ) i) (a x) =
      ((((EuclideanSpace.proj (𝕜 := ℂ) i).compLpL ⊤ productMeasure) a :
        ProductScalarLInf) : ProductTorus3 → ℂ) x
    exact hc.symm
  calc
    ((productCoordL2 i (vectorScalarMulProduct a b) : ProductScalarL2) :
        ProductTorus3 → ℂ) x
        = (EuclideanSpace.proj (𝕜 := ℂ) i)
            ((vectorScalarMulProduct a b) x) := hcm
    _ = (EuclideanSpace.proj (𝕜 := ℂ) i) (b x • a x) := by rw [hm]
    _ = b x * (EuclideanSpace.proj (𝕜 := ℂ) i) (a x) := by
      exact map_smul (EuclideanSpace.proj (𝕜 := ℂ) i) (b x) (a x)
    _ = b x *
        (((productCoordLInf i a : ProductScalarLInf) : ProductTorus3 → ℂ) x) := by
      rw [hc']
    _ = (((productCoordLInf i a : ProductScalarLInf) : ProductTorus3 → ℂ) x) *
        b x := by rw [mul_comm]
    _ = ((scalarMulProduct (productCoordLInf i a) b : ProductScalarL2) :
        ProductTorus3 → ℂ) x := hs.symm

/-- Extracting the `i`-th coordinate commutes with pulling a transverse `C³`-valued `L∞` field
back to the product torus along `(y, x₃) ↦ y`. -/
@[simp] theorem productCoordLInf_pullTransverseVectorLInf
    (a : TransverseC3LInf) (i : Fin 3) :
    productCoordLInf i (pullTransverseVectorLInf a) =
      pullTransverseScalarLInf (transverseCoordLInf i a) := by
  apply Lp.ext
  have hpull := pullTransverseVectorLInf_coe_ae a
  have hcoordPull := (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
    (pullTransverseVectorLInf a)
  have hcoord := (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL a
  have hcoordProd :=
    (measurePreserving_fst (μ := transverseMeasure) (ν := axialMeasure)).quasiMeasurePreserving
      |>.ae_eq_comp hcoord
  have hscalarPull := pullTransverseScalarLInf_coe_ae (transverseCoordLInf i a)
  filter_upwards [hpull, hcoordPull, hcoordProd, hscalarPull] with x hp hcp hc hs
  have hc' : (EuclideanSpace.proj (𝕜 := ℂ) i) (a x.1) =
      ((transverseCoordLInf i a : TransverseScalarLInf) :
        TransverseTorus → ℂ) x.1 := by
    change (EuclideanSpace.proj (𝕜 := ℂ) i) (a x.1) =
      ((((EuclideanSpace.proj (𝕜 := ℂ) i).compLpL ⊤ transverseMeasure) a :
        TransverseScalarLInf) : TransverseTorus → ℂ) x.1
    exact hc.symm
  calc
    ((productCoordLInf i (pullTransverseVectorLInf a) : ProductScalarLInf) :
        ProductTorus3 → ℂ) x
        = (EuclideanSpace.proj (𝕜 := ℂ) i)
            ((pullTransverseVectorLInf a) x) := by
          simpa [productCoordLInf] using hcp
    _ = (EuclideanSpace.proj (𝕜 := ℂ) i) (a x.1) := by rw [hp]
    _ = ((transverseCoordLInf i a : TransverseScalarLInf) :
        TransverseTorus → ℂ) x.1 := by rw [hc']
    _ = ((pullTransverseScalarLInf (transverseCoordLInf i a) :
        ProductScalarLInf) : ProductTorus3 → ℂ) x := hs.symm

/-- Specialization of the previous coordinate/pullback exchange to the stored weak derivative
`∂ⱼu` of a `W^{1,∞}` transverse velocity: its `i`-th coordinate on the product torus is the
pullback of the scalar coefficient `∂ⱼuᵢ`. -/
theorem productCoordLInf_pullTransverseVectorLInf_deriv
    (u : TransverseRealW1Inf) (j : Fin 2) (i : Fin 3) :
    productCoordLInf i
        (pullTransverseVectorLInf (transverseW1InfComplexDerivLInf j u)) =
      pullTransverseScalarLInf
        (transverseW1InfComplexDerivCoordLInf j i u) := by
  rw [transverseW1InfComplexDerivCoordLInf_apply,
    productCoordLInf_pullTransverseVectorLInf]

/-- The `i`-th coordinate of the product of the pulled-back derivative field `∂ⱼu` with a scalar
field `f` on the three-torus is multiplication of `f` by the scalar coefficient `∂ⱼuᵢ`. -/
theorem productCoordL2_vectorScalarMulProduct_pullTransverseDeriv
    (u : TransverseRealW1Inf) (j : Fin 2) (i : Fin 3)
    (f : ProductScalarL2) :
    productCoordL2 i
        (vectorScalarMulProduct
          (pullTransverseVectorLInf
            (transverseW1InfComplexDerivLInf j u)) f) =
      scalarMulProduct
        (pullTransverseScalarLInf
          (transverseW1InfComplexDerivCoordLInf j i u)) f := by
  rw [productCoordL2_vectorScalarMulProduct,
    productCoordLInf_pullTransverseVectorLInf_deriv]

/-! ## The lower-order action and `u × B` -/

/-- Coordinate `i` of `-(u·∇)B + (B·∇)u`. -/
def productInductionLowerCoord (u : TransverseRealW1Inf)
    (B : ProductC3H2) (i : Fin 3) : ProductScalarL2 :=
  -(∑ j : Fin 2,
      productVelocityMul u j.castSucc
        (productH2TransverseDerivCoord B j i)) -
    productVelocityMul u (2 : Fin 3) (productH2AxialDerivCoord B i) +
    ∑ j : Fin 2,
      productVelocityDerivMul u j i (productH2Coord B j.castSucc)

/-- The lower-order induction field assembled from its scalar coordinates. -/
def productInductionLowerField (u : TransverseRealW1Inf)
    (B : ProductC3H2) : ProductC3L2 :=
  productC3OfCoordsL2
    ((PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin 3 => ProductScalarL2)).symm
        (fun i => productInductionLowerCoord u B i))

/-- The vector field assembled from the scalar expressions `productInductionLowerCoord u B i`
has exactly those expressions as its coordinates. -/
@[simp] theorem productCoordL2_productInductionLowerField
    (u : TransverseRealW1Inf) (B : ProductC3H2) (i : Fin 3) :
    productCoordL2 i (productInductionLowerField u B) =
      productInductionLowerCoord u B i := by
  rw [productInductionLowerField, productCoordL2_productC3OfCoordsL2]
  rfl

/-- Coordinate zero of `u × B`. -/
def productVelocityCrossCoord0 (u : TransverseRealW1Inf)
    (B : ProductC3H2) : ProductScalarL2 :=
  productVelocityMul u (1 : Fin 3) (productH2Coord B (2 : Fin 3)) -
    productVelocityMul u (2 : Fin 3) (productH2Coord B (1 : Fin 3))

/-- Coordinate one of `u × B`. -/
def productVelocityCrossCoord1 (u : TransverseRealW1Inf)
    (B : ProductC3H2) : ProductScalarL2 :=
  productVelocityMul u (2 : Fin 3) (productH2Coord B (0 : Fin 3)) -
    productVelocityMul u (0 : Fin 3) (productH2Coord B (2 : Fin 3))

/-- Coordinate two of `u × B`. -/
def productVelocityCrossCoord2 (u : TransverseRealW1Inf)
    (B : ProductC3H2) : ProductScalarL2 :=
  productVelocityMul u (0 : Fin 3) (productH2Coord B (1 : Fin 3)) -
    productVelocityMul u (1 : Fin 3) (productH2Coord B (0 : Fin 3))

/-! ## Weak derivative certificates for products -/

/-- Every coordinate of a product `H²` field has the expected transverse
`L²` weak derivative. -/
theorem productH2Coord_hasFlatTransverseDerivative
    (B : ProductC3H2) (j : Fin 2) (i : Fin 3) :
    HasProductScalarFlatTransverseDerivative j
      (productH2Coord B i) (productH2TransverseDerivCoord B j i) := by
  apply (hasProductNestedDerivative_iff_flat j _ _).1
  intro k n
  change productScalarFourierAnalysisNested
      (productCoordL2 i (productTransverseDerivFromH2 j B)) k n =
    transverseFourierDerivMultiplier j n *
      productScalarFourierAnalysisNested
        (productCoordL2 i (productH2Embedding B)) k n
  rw [productScalarFourierAnalysisNested_coord_eq_productCoeffCLM,
    productScalarFourierAnalysisNested_coord_eq_productCoeffCLM]
  exact productCoeffCLM_productTransverseDerivFromH2 j B n k i

/-- Every coordinate of a product `H²` field has the expected axial `L²`
weak derivative. -/
theorem productH2Coord_hasFlatAxialDerivative
    (B : ProductC3H2) (i : Fin 3) :
    HasProductScalarFlatAxialDerivative
      (productH2Coord B i) (productH2AxialDerivCoord B i) := by
  intro m
  calc
    productScalarFourierAnalysisFlat
        (productH2AxialDerivCoord B i) m =
      productScalarFourierAnalysisNested
        (productH2AxialDerivCoord B i) (m (Fin.last 2)) (Fin.init m) := by
        rw [productScalarFourierAnalysisNested_apply, Fin.snoc_init_self]
    _ = productCoeffCLM (Fin.init m) (m (Fin.last 2)) i
        (productAxialDerivFromH2 B) :=
      by
        change productScalarFourierAnalysisNested
          (productCoordL2 i (productAxialDerivFromH2 B))
            (m (Fin.last 2)) (Fin.init m) = _
        exact productScalarFourierAnalysisNested_coord_eq_productCoeffCLM _ _ _ _
    _ = (2 * Real.pi * Complex.I * (m (Fin.last 2) : ℂ)) *
        productCoeffCLM (Fin.init m) (m (Fin.last 2)) i
          (productH2Embedding B) :=
      productCoeffCLM_productAxialDerivFromH2 B
        (Fin.init m) (m (Fin.last 2)) i
    _ = (2 * Real.pi * Complex.I * (m (Fin.last 2) : ℂ)) *
        productScalarFourierAnalysisNested
          (productH2Coord B i) (m (Fin.last 2)) (Fin.init m) := by
      congr 1
      change productCoeffCLM (Fin.init m) (m (Fin.last 2)) i
          (productH2Embedding B) =
        productScalarFourierAnalysisNested
          (productCoordL2 i (productH2Embedding B))
            (m (Fin.last 2)) (Fin.init m)
      exact (productScalarFourierAnalysisNested_coord_eq_productCoeffCLM _ _ _ _).symm
    _ = (2 * Real.pi * Complex.I * (m (Fin.last 2) : ℂ)) *
        productScalarFourierAnalysisFlat (productH2Coord B i) m := by
      rw [productScalarFourierAnalysisNested_apply, Fin.snoc_init_self]

/-- Transverse weak Leibniz rule for `uᵢ Bₗ`. -/
theorem productVelocityMul_hasFlatTransverseDerivative
    (u : TransverseRealW1Inf) (B : ProductC3H2)
    (j : Fin 2) (i l : Fin 3) :
    HasProductScalarFlatTransverseDerivative j
      (productVelocityMul u i (productH2Coord B l))
      (productVelocityDerivMul u j i (productH2Coord B l) +
        productVelocityMul u i (productH2TransverseDerivCoord B j l)) := by
  exact hasProductFlatDeriv_scalarMul
    (transverseW1InfCoord_hasScalarFourierDerivative u j i)
    (productH2Coord_hasFlatTransverseDerivative B j l)

/-- Axial weak Leibniz rule for `uᵢ Bₗ`; the coefficient has no axial
dependence. -/
theorem productVelocityMul_hasFlatAxialDerivative
    (u : TransverseRealW1Inf) (B : ProductC3H2) (i l : Fin 3) :
    HasProductScalarFlatAxialDerivative
      (productVelocityMul u i (productH2Coord B l))
      (productVelocityMul u i (productH2AxialDerivCoord B l)) := by
  exact hasProductFlatAxialDeriv_scalarMul _
    (productH2Coord_hasFlatAxialDerivative B l)

/-! ## Weak curl certificate -/

/-- Transverse derivative candidate for coordinate zero of `u × B`. -/
def productVelocityCrossTransverseDerivCoord0
    (u : TransverseRealW1Inf) (B : ProductC3H2) (j : Fin 2) :
    ProductScalarL2 :=
  (productVelocityDerivMul u j (1 : Fin 3) (productH2Coord B (2 : Fin 3)) +
      productVelocityMul u (1 : Fin 3)
        (productH2TransverseDerivCoord B j (2 : Fin 3))) -
    (productVelocityDerivMul u j (2 : Fin 3) (productH2Coord B (1 : Fin 3)) +
      productVelocityMul u (2 : Fin 3)
        (productH2TransverseDerivCoord B j (1 : Fin 3)))

/-- Transverse derivative candidate for coordinate one of `u × B`. -/
def productVelocityCrossTransverseDerivCoord1
    (u : TransverseRealW1Inf) (B : ProductC3H2) (j : Fin 2) :
    ProductScalarL2 :=
  (productVelocityDerivMul u j (2 : Fin 3) (productH2Coord B (0 : Fin 3)) +
      productVelocityMul u (2 : Fin 3)
        (productH2TransverseDerivCoord B j (0 : Fin 3))) -
    (productVelocityDerivMul u j (0 : Fin 3) (productH2Coord B (2 : Fin 3)) +
      productVelocityMul u (0 : Fin 3)
        (productH2TransverseDerivCoord B j (2 : Fin 3)))

/-- Transverse derivative candidate for coordinate two of `u × B`. -/
def productVelocityCrossTransverseDerivCoord2
    (u : TransverseRealW1Inf) (B : ProductC3H2) (j : Fin 2) :
    ProductScalarL2 :=
  (productVelocityDerivMul u j (0 : Fin 3) (productH2Coord B (1 : Fin 3)) +
      productVelocityMul u (0 : Fin 3)
        (productH2TransverseDerivCoord B j (1 : Fin 3))) -
    (productVelocityDerivMul u j (1 : Fin 3) (productH2Coord B (0 : Fin 3)) +
      productVelocityMul u (1 : Fin 3)
        (productH2TransverseDerivCoord B j (0 : Fin 3)))

/-- Axial derivative candidate for coordinate zero of `u × B`. -/
def productVelocityCrossAxialDerivCoord0
    (u : TransverseRealW1Inf) (B : ProductC3H2) : ProductScalarL2 :=
  productVelocityMul u (1 : Fin 3) (productH2AxialDerivCoord B (2 : Fin 3)) -
    productVelocityMul u (2 : Fin 3) (productH2AxialDerivCoord B (1 : Fin 3))

/-- Axial derivative candidate for coordinate one of `u × B`. -/
def productVelocityCrossAxialDerivCoord1
    (u : TransverseRealW1Inf) (B : ProductC3H2) : ProductScalarL2 :=
  productVelocityMul u (2 : Fin 3) (productH2AxialDerivCoord B (0 : Fin 3)) -
    productVelocityMul u (0 : Fin 3) (productH2AxialDerivCoord B (2 : Fin 3))

/-- Flat transverse weak derivatives subtract: if `f` and `g` have `j`-th transverse weak
derivatives `df` and `dg`, then `f - g` has `j`-th transverse weak derivative `df - dg`. -/
private theorem HasProductScalarFlatTransverseDerivative.sub
    {j : Fin 2} {f g df dg : ProductScalarL2}
    (hf : HasProductScalarFlatTransverseDerivative j f df)
    (hg : HasProductScalarFlatTransverseDerivative j g dg) :
    HasProductScalarFlatTransverseDerivative j (f - g) (df - dg) := by
  simpa only [sub_eq_add_neg, neg_one_smul] using hf.add (hg.smul (-1))

/-- Flat axial weak derivatives subtract: if `f` and `g` have axial weak derivatives `df` and
`dg`, then `f - g` has axial weak derivative `df - dg`. -/
private theorem HasProductScalarFlatAxialDerivative.sub
    {f g df dg : ProductScalarL2}
    (hf : HasProductScalarFlatAxialDerivative f df)
    (hg : HasProductScalarFlatAxialDerivative g dg) :
    HasProductScalarFlatAxialDerivative (f - g) (df - dg) := by
  simpa only [sub_eq_add_neg, neg_one_smul] using hf.add (hg.smul (-1))

/-- The component `u₁B₂ - u₂B₁` of `u × B` has the Leibniz expression
`productVelocityCrossTransverseDerivCoord0 u B j` as its `j`-th transverse weak derivative. -/
theorem productVelocityCrossCoord0_hasFlatTransverseDerivative
    (u : TransverseRealW1Inf) (B : ProductC3H2) (j : Fin 2) :
    HasProductScalarFlatTransverseDerivative j
      (productVelocityCrossCoord0 u B)
      (productVelocityCrossTransverseDerivCoord0 u B j) := by
  exact (productVelocityMul_hasFlatTransverseDerivative u B j 1 2).sub
    (productVelocityMul_hasFlatTransverseDerivative u B j 2 1)

/-- The component `u₂B₀ - u₀B₂` of `u × B` has the Leibniz expression
`productVelocityCrossTransverseDerivCoord1 u B j` as its `j`-th transverse weak derivative. -/
theorem productVelocityCrossCoord1_hasFlatTransverseDerivative
    (u : TransverseRealW1Inf) (B : ProductC3H2) (j : Fin 2) :
    HasProductScalarFlatTransverseDerivative j
      (productVelocityCrossCoord1 u B)
      (productVelocityCrossTransverseDerivCoord1 u B j) := by
  exact (productVelocityMul_hasFlatTransverseDerivative u B j 2 0).sub
    (productVelocityMul_hasFlatTransverseDerivative u B j 0 2)

/-- The component `u₀B₁ - u₁B₀` of `u × B` has the Leibniz expression
`productVelocityCrossTransverseDerivCoord2 u B j` as its `j`-th transverse weak derivative. -/
theorem productVelocityCrossCoord2_hasFlatTransverseDerivative
    (u : TransverseRealW1Inf) (B : ProductC3H2) (j : Fin 2) :
    HasProductScalarFlatTransverseDerivative j
      (productVelocityCrossCoord2 u B)
      (productVelocityCrossTransverseDerivCoord2 u B j) := by
  exact (productVelocityMul_hasFlatTransverseDerivative u B j 0 1).sub
    (productVelocityMul_hasFlatTransverseDerivative u B j 1 0)

/-- The component `u₁B₂ - u₂B₁` of `u × B` has axial weak derivative
`u₁ ∂₃B₂ - u₂ ∂₃B₁`; only `B` is differentiated because `u` does not depend on `x₃`. -/
theorem productVelocityCrossCoord0_hasFlatAxialDerivative
    (u : TransverseRealW1Inf) (B : ProductC3H2) :
    HasProductScalarFlatAxialDerivative
      (productVelocityCrossCoord0 u B)
      (productVelocityCrossAxialDerivCoord0 u B) := by
  exact (productVelocityMul_hasFlatAxialDerivative u B 1 2).sub
    (productVelocityMul_hasFlatAxialDerivative u B 2 1)

/-- The component `u₂B₀ - u₀B₂` of `u × B` has axial weak derivative
`u₂ ∂₃B₀ - u₀ ∂₃B₂`; only `B` is differentiated because `u` does not depend on `x₃`. -/
theorem productVelocityCrossCoord1_hasFlatAxialDerivative
    (u : TransverseRealW1Inf) (B : ProductC3H2) :
    HasProductScalarFlatAxialDerivative
      (productVelocityCrossCoord1 u B)
      (productVelocityCrossAxialDerivCoord1 u B) := by
  exact (productVelocityMul_hasFlatAxialDerivative u B 2 0).sub
    (productVelocityMul_hasFlatAxialDerivative u B 0 2)

/-- Coordinate zero of the weak curl candidate. -/
def productVelocityCrossWeakCurlCoord0
    (u : TransverseRealW1Inf) (B : ProductC3H2) : ProductScalarL2 :=
  productVelocityCrossTransverseDerivCoord2 u B (1 : Fin 2) -
    productVelocityCrossAxialDerivCoord1 u B

/-- Coordinate one of the weak curl candidate. -/
def productVelocityCrossWeakCurlCoord1
    (u : TransverseRealW1Inf) (B : ProductC3H2) : ProductScalarL2 :=
  productVelocityCrossAxialDerivCoord0 u B -
    productVelocityCrossTransverseDerivCoord2 u B (0 : Fin 2)

/-- Coordinate two of the weak curl candidate. -/
def productVelocityCrossWeakCurlCoord2
    (u : TransverseRealW1Inf) (B : ProductC3H2) : ProductScalarL2 :=
  productVelocityCrossTransverseDerivCoord1 u B (0 : Fin 2) -
    productVelocityCrossTransverseDerivCoord0 u B (1 : Fin 2)

/-- The `L²` weak curl candidate assembled coordinatewise. -/
def productVelocityCrossWeakCurl
    (u : TransverseRealW1Inf) (B : ProductC3H2) : ProductC3L2 :=
  productC3OfCoordsL2
    ((PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin 3 => ProductScalarL2)).symm
        ![productVelocityCrossWeakCurlCoord0 u B,
          productVelocityCrossWeakCurlCoord1 u B,
          productVelocityCrossWeakCurlCoord2 u B])

/-- The vector field assembled from the three weak-curl components has exactly those components
as its coordinates. -/
@[simp] theorem productCoordL2_productVelocityCrossWeakCurl
    (u : TransverseRealW1Inf) (B : ProductC3H2) (i : Fin 3) :
    productCoordL2 i (productVelocityCrossWeakCurl u B) =
      ![productVelocityCrossWeakCurlCoord0 u B,
        productVelocityCrossWeakCurlCoord1 u B,
        productVelocityCrossWeakCurlCoord2 u B] i := by
  rw [productVelocityCrossWeakCurl, productCoordL2_productC3OfCoordsL2]
  rfl

/-- Flat three-torus Fourier analysis is additive: the coefficient of `f - g` at a frequency is
the difference of the coefficients of `f` and `g`. -/
private theorem productScalarFourierAnalysisFlat_sub
    (f g : ProductScalarL2) (m : FlatTorus3Frequency) :
    productScalarFourierAnalysisFlat (f - g) m =
      productScalarFourierAnalysisFlat f m -
        productScalarFourierAnalysisFlat g m := by
  exact congrArg (fun x : FlatTorus3ScalarFourierL2 => x m)
    (map_sub productScalarFourierAnalysisFlat f g)

/-- Fourier symbol of the first component of `curl (u × B)`: its coefficient at frequency `m` is
`2πi m₁` times the coefficient of `(u × B)₂` minus `2πi m₂` times that of `(u × B)₁`. -/
theorem productVelocityCrossWeakCurlCoord0_flatCoeff
    (u : TransverseRealW1Inf) (B : ProductC3H2)
    (m : FlatTorus3Frequency) :
    productScalarFourierAnalysisFlat
        (productVelocityCrossWeakCurlCoord0 u B) m =
      (2 * Real.pi * Complex.I * (m (1 : Fin 3) : ℂ)) *
          productScalarFourierAnalysisFlat
            (productVelocityCrossCoord2 u B) m -
        (2 * Real.pi * Complex.I * (m (2 : Fin 3) : ℂ)) *
          productScalarFourierAnalysisFlat
            (productVelocityCrossCoord1 u B) m := by
  rw [productVelocityCrossWeakCurlCoord0,
    productScalarFourierAnalysisFlat_sub,
    productVelocityCrossCoord2_hasFlatTransverseDerivative u B (1 : Fin 2) m,
    productVelocityCrossCoord1_hasFlatAxialDerivative u B m]
  rfl

/-- Fourier symbol of the second component of `curl (u × B)`: its coefficient at frequency `m` is
`2πi m₂` times the coefficient of `(u × B)₀` minus `2πi m₀` times that of `(u × B)₂`. -/
theorem productVelocityCrossWeakCurlCoord1_flatCoeff
    (u : TransverseRealW1Inf) (B : ProductC3H2)
    (m : FlatTorus3Frequency) :
    productScalarFourierAnalysisFlat
        (productVelocityCrossWeakCurlCoord1 u B) m =
      (2 * Real.pi * Complex.I * (m (2 : Fin 3) : ℂ)) *
          productScalarFourierAnalysisFlat
            (productVelocityCrossCoord0 u B) m -
        (2 * Real.pi * Complex.I * (m (0 : Fin 3) : ℂ)) *
          productScalarFourierAnalysisFlat
            (productVelocityCrossCoord2 u B) m := by
  rw [productVelocityCrossWeakCurlCoord1,
    productScalarFourierAnalysisFlat_sub,
    productVelocityCrossCoord0_hasFlatAxialDerivative u B m,
    productVelocityCrossCoord2_hasFlatTransverseDerivative u B (0 : Fin 2) m]
  rfl

/-- Fourier symbol of the third component of `curl (u × B)`: its coefficient at frequency `m` is
`2πi m₀` times the coefficient of `(u × B)₁` minus `2πi m₁` times that of `(u × B)₀`. -/
theorem productVelocityCrossWeakCurlCoord2_flatCoeff
    (u : TransverseRealW1Inf) (B : ProductC3H2)
    (m : FlatTorus3Frequency) :
    productScalarFourierAnalysisFlat
        (productVelocityCrossWeakCurlCoord2 u B) m =
      (2 * Real.pi * Complex.I * (m (0 : Fin 3) : ℂ)) *
          productScalarFourierAnalysisFlat
            (productVelocityCrossCoord1 u B) m -
        (2 * Real.pi * Complex.I * (m (1 : Fin 3) : ℂ)) *
          productScalarFourierAnalysisFlat
            (productVelocityCrossCoord0 u B) m := by
  rw [productVelocityCrossWeakCurlCoord2,
    productScalarFourierAnalysisFlat_sub,
    productVelocityCrossCoord1_hasFlatTransverseDerivative u B (0 : Fin 2) m,
    productVelocityCrossCoord0_hasFlatTransverseDerivative u B (1 : Fin 2) m]
  rfl

/-- The nested Fourier coefficient at transverse frequency `n` and axial frequency `k` of the
`i`-th coordinate of a product `L²` vector field is the flat three-torus Fourier coefficient of
that coordinate at the concatenated frequency `Fin.snoc n k`. -/
theorem productCoeffCLM_eq_flatCoordAnalysis
    (V : ProductC3L2) (n : TransverseFrequency) (k : ℤ) (i : Fin 3) :
    productCoeffCLM n k i V =
      productScalarFourierAnalysisFlat (productCoordL2 i V) (Fin.snoc n k) := by
  rw [← productScalarFourierAnalysisNested_coord_eq_productCoeffCLM,
    productScalarFourierAnalysisNested_apply]

/-- The coordinatewise weak curl candidate is distributionally
divergence-free. -/
theorem productVelocityCrossWeakCurl_solenoidal
    (u : TransverseRealW1Inf) (B : ProductC3H2) :
    IsProductSolenoidal (productVelocityCrossWeakCurl u B) := by
  intro n k
  simp only [Fin.sum_univ_two]
  rw [productCoeffCLM_eq_flatCoordAnalysis,
    productCoeffCLM_eq_flatCoordAnalysis,
    productCoeffCLM_eq_flatCoordAnalysis]
  rw [productCoordL2_productVelocityCrossWeakCurl u B (Fin.castSucc 0),
    productCoordL2_productVelocityCrossWeakCurl u B (Fin.castSucc 1),
    productCoordL2_productVelocityCrossWeakCurl u B (2 : Fin 3)]
  change
    (2 * Real.pi * Complex.I * (n 0 : ℂ)) *
          productScalarFourierAnalysisFlat
            (productVelocityCrossWeakCurlCoord0 u B) (Fin.snoc n k) +
        (2 * Real.pi * Complex.I * (n 1 : ℂ)) *
          productScalarFourierAnalysisFlat
            (productVelocityCrossWeakCurlCoord1 u B) (Fin.snoc n k) +
      (2 * Real.pi * Complex.I * (k : ℂ)) *
        productScalarFourierAnalysisFlat
          (productVelocityCrossWeakCurlCoord2 u B) (Fin.snoc n k) = 0
  rw [productVelocityCrossWeakCurlCoord0_flatCoeff,
    productVelocityCrossWeakCurlCoord1_flatCoeff,
    productVelocityCrossWeakCurlCoord2_flatCoeff]
  have hm0 : (Fin.snoc n k : Fin 3 → ℤ) (0 : Fin 3) = n 0 := by
    change (Fin.snoc n k : Fin 3 → ℤ) (Fin.castSucc (0 : Fin 2)) = n 0
    rw [Fin.snoc_castSucc]
  have hm1 : (Fin.snoc n k : Fin 3 → ℤ) (1 : Fin 3) = n 1 := by
    change (Fin.snoc n k : Fin 3 → ℤ) (Fin.castSucc (1 : Fin 2)) = n 1
    rw [Fin.snoc_castSucc]
  have hm2 : (Fin.snoc n k : Fin 3 → ℤ) (2 : Fin 3) = k := by
    change (Fin.snoc n k : Fin 3 → ℤ) (Fin.last 2) = k
    rw [Fin.snoc_last]
  rw [hm0, hm1, hm2]
  ring

/-! ## The vector identity -/

/-- Multiplication by the transverse divergence of a divergence-free
velocity vanishes. -/
theorem productVelocityDiagonalDerivMul_add_eq_zero
    (u : TransverseRealW1Inf) (hdiv : IsTransverseDivergenceFree u)
    (f : ProductScalarL2) :
    productVelocityDerivMul u (0 : Fin 2) (0 : Fin 3) f +
      productVelocityDerivMul u (1 : Fin 2) (1 : Fin 3) f = 0 := by
  unfold productVelocityDerivMul
  rw [← add_apply, ← map_add, ← map_add, hdiv]
  simp

/-- First component of the vector identity `-(u·∇)B + (B·∇)u + u (div B) = curl (u × B)` for an
`x₃`-independent divergence-free velocity; this is the transport--stretching divergence
identity of the module header. -/
theorem productInductionLowerCoord_add_velocityDiv_coord0
    (u : TransverseRealW1Inf) (hdiv : IsTransverseDivergenceFree u)
    (B : ProductC3H2) :
    productInductionLowerCoord u B (0 : Fin 3) +
        productVelocityMul u (0 : Fin 3) (productDivergenceFromH2 B) =
      productVelocityCrossWeakCurlCoord0 u B := by
  have hd := productVelocityDiagonalDerivMul_add_eq_zero u hdiv
    (productH2Coord B (0 : Fin 3))
  rw [productDivergenceFromH2_apply]
  simp only [productInductionLowerCoord, Fin.sum_univ_two,
    productVelocityCrossWeakCurlCoord0,
    productVelocityCrossTransverseDerivCoord2,
    productVelocityCrossAxialDerivCoord1,
    productVelocityMul_add, productH2Coord,
    productH2TransverseDerivCoord, productH2AxialDerivCoord] at hd ⊢
  have hc0 : Fin.castSucc (0 : Fin 2) = (0 : Fin 3) := by decide
  have hc1 : Fin.castSucc (1 : Fin 2) = (1 : Fin 3) := by decide
  rw [hc0, hc1]
  rw [eq_neg_of_add_eq_zero_left hd]
  module

/-- Second component of the vector identity `-(u·∇)B + (B·∇)u + u (div B) = curl (u × B)` for an
`x₃`-independent divergence-free velocity; this is the transport--stretching divergence
identity of the module header. -/
theorem productInductionLowerCoord_add_velocityDiv_coord1
    (u : TransverseRealW1Inf) (hdiv : IsTransverseDivergenceFree u)
    (B : ProductC3H2) :
    productInductionLowerCoord u B (1 : Fin 3) +
        productVelocityMul u (1 : Fin 3) (productDivergenceFromH2 B) =
      productVelocityCrossWeakCurlCoord1 u B := by
  have hd := productVelocityDiagonalDerivMul_add_eq_zero u hdiv
    (productH2Coord B (1 : Fin 3))
  rw [productDivergenceFromH2_apply]
  simp only [productInductionLowerCoord, Fin.sum_univ_two,
    productVelocityCrossWeakCurlCoord1,
    productVelocityCrossAxialDerivCoord0,
    productVelocityCrossTransverseDerivCoord2,
    productVelocityMul_add, productH2Coord,
    productH2TransverseDerivCoord, productH2AxialDerivCoord] at hd ⊢
  have hc0 : Fin.castSucc (0 : Fin 2) = (0 : Fin 3) := by decide
  have hc1 : Fin.castSucc (1 : Fin 2) = (1 : Fin 3) := by decide
  rw [hc0, hc1]
  rw [eq_neg_of_add_eq_zero_left hd]
  module

/-- Third component of the vector identity `-(u·∇)B + (B·∇)u + u (div B) = curl (u × B)` for an
`x₃`-independent divergence-free velocity; this is the transport--stretching divergence
identity of the module header. -/
theorem productInductionLowerCoord_add_velocityDiv_coord2
    (u : TransverseRealW1Inf) (hdiv : IsTransverseDivergenceFree u)
    (B : ProductC3H2) :
    productInductionLowerCoord u B (2 : Fin 3) +
        productVelocityMul u (2 : Fin 3) (productDivergenceFromH2 B) =
      productVelocityCrossWeakCurlCoord2 u B := by
  have hd := productVelocityDiagonalDerivMul_add_eq_zero u hdiv
    (productH2Coord B (2 : Fin 3))
  rw [productDivergenceFromH2_apply]
  simp only [productInductionLowerCoord, Fin.sum_univ_two,
    productVelocityCrossWeakCurlCoord2,
    productVelocityCrossTransverseDerivCoord1,
    productVelocityCrossTransverseDerivCoord0,
    productVelocityMul_add, productH2Coord,
    productH2TransverseDerivCoord, productH2AxialDerivCoord] at hd ⊢
  have hc0 : Fin.castSucc (0 : Fin 2) = (0 : Fin 3) := by decide
  have hc1 : Fin.castSucc (1 : Fin 2) = (1 : Fin 3) := by decide
  rw [hc0, hc1]
  rw [eq_neg_of_add_eq_zero_left hd]
  module

/-- The lower-order induction action plus `u (div B)` is the weak curl of
`u × B`. -/
theorem productInductionLowerField_add_velocityDiv_eq_weakCurl
    (u : TransverseRealW1Inf) (hdiv : IsTransverseDivergenceFree u)
    (B : ProductC3H2) :
    productInductionLowerField u B +
        productVelocityTimesScalar u (productDivergenceFromH2 B) =
      productVelocityCrossWeakCurl u B := by
  apply productC3L2_ext_coeff
  intro n k i
  have hi :
      productCoordL2 i
          (productInductionLowerField u B +
            productVelocityTimesScalar u (productDivergenceFromH2 B)) =
        productCoordL2 i (productVelocityCrossWeakCurl u B) := by
    rw [map_add, productCoordL2_productInductionLowerField,
      productCoordL2_productVelocityTimesScalar,
      productCoordL2_productVelocityCrossWeakCurl]
    fin_cases i
    · exact productInductionLowerCoord_add_velocityDiv_coord0 u hdiv B
    · exact productInductionLowerCoord_add_velocityDiv_coord1 u hdiv B
    · exact productInductionLowerCoord_add_velocityDiv_coord2 u hdiv B
  have hc := congrArg
    (fun f : ProductScalarL2 =>
      productScalarFourierAnalysisNested f k n) hi
  simpa only [productScalarFourierAnalysisNested_coord_eq_productCoeffCLM]
    using hc

/-! ## Identification with the operator action -/

/-- The `i`-th coordinate of the transverse transport term `(u_⊥·∇_⊥)B` is the sum over the two
transverse directions `j` of `uⱼ ∂ⱼBᵢ`. -/
theorem productCoordL2_productInductionTransverseTransport
    (u : TransverseRealW1Inf) (B : ProductC3H2) (i : Fin 3) :
    productCoordL2 i (productInductionTransverseTransport u B) =
      ∑ j : Fin 2,
        productVelocityMul u j.castSucc
          (productH2TransverseDerivCoord B j i) := by
  rw [productInductionTransverseTransport_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [productCoordL2_scalarVectorMulProduct]
  rfl

/-- The `i`-th coordinate of the axial transport term `u₃ ∂₃B` is `u₃ ∂₃Bᵢ`. -/
theorem productCoordL2_productInductionAxialTransport
    (u : TransverseRealW1Inf) (B : ProductC3H2) (i : Fin 3) :
    productCoordL2 i (productInductionAxialTransport u B) =
      productVelocityMul u (2 : Fin 3)
        (productH2AxialDerivCoord B i) := by
  rw [productInductionAxialTransport_apply,
    productCoordL2_scalarVectorMulProduct]
  rfl

/-- The `i`-th coordinate of the stretching term `(B·∇)u` is the sum over the two transverse
directions `j` of `(∂ⱼuᵢ) Bⱼ`; there is no axial column because `u` is `x₃`-independent. -/
theorem productCoordL2_productInductionStretching
    (u : TransverseRealW1Inf) (B : ProductC3H2) (i : Fin 3) :
    productCoordL2 i (productInductionStretching u B) =
      ∑ j : Fin 2,
        productVelocityDerivMul u j i (productH2Coord B j.castSucc) := by
  rw [productInductionStretching_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [productCoordL2_vectorScalarMulProduct_pullTransverseDeriv]
  rfl

/-- The coordinatewise lower field is exactly the three lower-order terms
used in `productInductionAction`; it is not a separate stand-in for the
PDE action. -/
theorem productInductionLowerField_eq_operatorLower
    (u : TransverseRealW1Inf) (B : ProductC3H2) :
    productInductionLowerField u B =
      -productInductionTransverseTransport u B -
        productInductionAxialTransport u B +
          productInductionStretching u B := by
  apply productC3L2_ext_coeff
  intro n k i
  have hi :
      productCoordL2 i (productInductionLowerField u B) =
        productCoordL2 i
          (-productInductionTransverseTransport u B -
            productInductionAxialTransport u B +
              productInductionStretching u B) := by
    rw [map_add, map_sub, map_neg,
      productCoordL2_productInductionLowerField,
      productCoordL2_productInductionTransverseTransport,
      productCoordL2_productInductionAxialTransport,
      productCoordL2_productInductionStretching]
    rfl
  have hc := congrArg
    (fun f : ProductScalarL2 =>
      productScalarFourierAnalysisNested f k n) hi
  simpa only [productScalarFourierAnalysisNested_coord_eq_productCoeffCLM]
    using hc

/-- The full operator action is diffusion plus the rigorously identified
lower-order field. -/
theorem productInductionAction_eq_diffusion_add_lower
    (u : TransverseRealW1Inf) (ε : ℝ) (B : ProductC3H2) :
    productInductionAction u ε B =
      (ε : ℂ) • productLaplacianFromH2 B +
        productInductionLowerField u B := by
  rw [productInductionAction_apply,
    productInductionLowerField_eq_operatorLower,
    productInductionTransverseTransport_apply,
    productInductionAxialTransport_apply,
    productInductionStretching_apply]
  module

/-- Every coefficientwise solenoidal product `L²` field has zero weak
divergence. -/
theorem productWeakDivergence_eq_zero_of_solenoidal
    {V : ProductC3L2} (hV : IsProductSolenoidal V) :
    productWeakDivergence V = 0 := by
  have hcoeff : productWeakDivergenceCoeffMap V = 0 := by
    apply lp.ext
    funext k
    apply lp.ext
    funext n
    rw [productWeakDivergenceCoeffMap_apply]
    change productFrequencyDivergenceCoeff n k V /
      (productH1Weight n k : ℂ) = 0
    rw [show productFrequencyDivergenceCoeff n k V = 0 by exact hV n k]
    simp
  change productScalarHMinus1OfCoeff
      (productWeakDivergenceCoeffMap V) = 0
  rw [hcoeff, map_zero]

/-- The weak divergence of the weak curl `curl (u × B)` vanishes. -/
theorem productWeakDivergence_velocityCrossWeakCurl
    (u : TransverseRealW1Inf) (B : ProductC3H2) :
    productWeakDivergence (productVelocityCrossWeakCurl u B) = 0 :=
  productWeakDivergence_eq_zero_of_solenoidal
    (productVelocityCrossWeakCurl_solenoidal u B)

/-- For divergence-free velocity, the divergence of the lower-order
induction action is `-div (u div B)`. -/
theorem productWeakDivergence_inductionLowerField
    (u : TransverseRealW1Inf) (hdiv : IsTransverseDivergenceFree u)
    (B : ProductC3H2) :
    productWeakDivergence (productInductionLowerField u B) =
      -productWeakDivergence
        (productVelocityTimesScalar u (productDivergenceFromH2 B)) := by
  have h := congrArg productWeakDivergence
    (productInductionLowerField_add_velocityDiv_eq_weakCurl u hdiv B)
  rw [map_add, productWeakDivergence_velocityCrossWeakCurl] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Distributional divergence equation for the actual all-frequency
induction action.  This is the non-circular PDE identity used by the auxiliary
solenoidality argument of `FastDynamo.Finish.RealSolution`. -/
theorem productWeakDivergence_productInductionAction
    (u : TransverseRealW1Inf) (hdiv : IsTransverseDivergenceFree u)
    (ε : ℝ) (B : ProductC3H2) :
    productWeakDivergence (productInductionAction u ε B) =
      (ε : ℂ) • productScalarWeakLaplacian (productDivergenceH1 B) -
        productWeakDivergence
          (productVelocityTimesScalar u
            (productScalarH1Embedding (productDivergenceH1 B))) := by
  rw [productInductionAction_eq_diffusion_add_lower,
    map_add, map_smul, productWeakDivergence_laplacian,
    productWeakDivergence_inductionLowerField u hdiv,
    productScalarH1Embedding_productDivergenceH1]
  rfl

end

end FastDynamo
