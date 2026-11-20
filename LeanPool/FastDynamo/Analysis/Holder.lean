/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Fourier.ProductH2
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Hölder multiplication on the periodic `L²` spaces

This module supplies the lower-order multiplication layer used by the
induction operator.  The definitions are quotient-level continuous bilinear
maps, rather than operations on arbitrarily chosen representatives:

* scalar `L∞` times vector-valued `L²`;
* vector-valued `L∞` times scalar `L²`;
* the bounded inclusion `L∞ → L²` on a probability space;
* pullback of transverse `L∞` coefficients to the product torus.

The final two theorems prove that both kinds of multiplication commute
exactly with a fixed-frequency axial lift.  These are the pointwise
identities needed for transport and stretching in the reduced/full operator
intertwining proof.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-! ## Generic `L∞ × L² → L²` maps -/

section Generic

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Pointwise scalar multiplication as a continuous bilinear map
`L∞(ℂ) × L²(E) → L²(E)`. -/
def scalarVectorMulL2 (μ : Measure X) :
    Lp ℂ ∞ μ →L[ℂ] Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E).holderL μ ∞ 2 2

/-- Pointwise multiplication in the opposite input order as a continuous
bilinear map `L∞(E) × L²(ℂ) → L²(E)`. -/
def vectorScalarMulL2 (μ : Measure X) :
    Lp E ∞ μ →L[ℂ] Lp ℂ 2 μ →L[ℂ] Lp E 2 μ :=
  (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E).flip.holderL μ ∞ 2 2

/-- Almost-everywhere representative of scalar-vector multiplication. -/
theorem scalarVectorMulL2_coe_ae (μ : Measure X)
    (a : Lp ℂ ∞ μ) (b : Lp E 2 μ) :
    (scalarVectorMulL2 μ a b : X → E) =ᵐ[μ] fun x ↦ a x • b x := by
  exact ContinuousLinearMap.coeFn_holder _ _ _

/-- Almost-everywhere representative of vector-scalar multiplication. -/
theorem vectorScalarMulL2_coe_ae (μ : Measure X)
    (a : Lp E ∞ μ) (b : Lp ℂ 2 μ) :
    (vectorScalarMulL2 μ a b : X → E) =ᵐ[μ] fun x ↦ b x • a x := by
  simpa [vectorScalarMulL2] using
    ContinuousLinearMap.coeFn_holder
      ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E).flip) a b

/-- Hölder's norm estimate for scalar-vector multiplication. -/
theorem norm_scalarVectorMulL2_apply_le (μ : Measure X)
    (a : Lp ℂ ∞ μ) (b : Lp E 2 μ) :
    ‖scalarVectorMulL2 μ a b‖ ≤ ‖a‖ * ‖b‖ := by
  calc
    ‖scalarVectorMulL2 μ a b‖ ≤
        ‖(ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E)‖ * ‖a‖ * ‖b‖ :=
      ContinuousLinearMap.norm_holder_apply_apply_le _ _ _
    _ ≤ 1 * ‖a‖ * ‖b‖ := by
      gcongr
      exact ContinuousLinearMap.opNorm_lsmul_le
    _ = ‖a‖ * ‖b‖ := by simp

section Probability

variable (μ : Measure X) [IsProbabilityMeasure μ]

/-- The canonical bounded inclusion `L∞(E) → L²(E)` on a probability
space, constructed by multiplication with the constant scalar function one. -/
def linftyToL2 : Lp E ∞ μ →L[ℂ] Lp E 2 μ :=
  (vectorScalarMulL2 (E := E) μ).flip (Lp.const 2 μ (1 : ℂ))

/-- The probability-space inclusion has the same representative almost everywhere. -/
theorem linftyToL2_coe_ae (a : Lp E ∞ μ) :
    (linftyToL2 μ a : X → E) =ᵐ[μ] a := by
  change (vectorScalarMulL2 (E := E) μ a (Lp.const 2 μ (1 : ℂ)) : X → E)
    =ᵐ[μ] a
  have h := vectorScalarMulL2_coe_ae μ a (Lp.const 2 μ (1 : ℂ))
  have h1 := Lp.coeFn_const (p := 2) (μ := μ) (1 : ℂ)
  filter_upwards [h, h1] with x hx h1x
  rw [hx, h1x]
  simp

end Probability

end Generic

/-! ## Concrete transverse and product spaces -/

/-- Transverse scalar `L∞`. -/
abbrev TransverseScalarLInf := Lp ℂ ∞ transverseMeasure

/-- Product scalar `L∞`. -/
abbrev ProductScalarLInf := Lp ℂ ∞ productMeasure

/-- Transverse `C3`-valued `L∞`. -/
abbrev TransverseC3LInf := Lp C3 ∞ transverseMeasure

/-- Product `C3`-valued `L∞`. -/
abbrev ProductC3LInf := Lp C3 ∞ productMeasure

/-- Scalar-vector multiplication on the transverse torus. -/
def scalarVectorMulTransverse :
    TransverseScalarLInf →L[ℂ] TransverseC3L2 →L[ℂ] TransverseC3L2 :=
  scalarVectorMulL2 transverseMeasure

/-- Scalar-vector multiplication on the product torus. -/
def scalarVectorMulProduct :
    ProductScalarLInf →L[ℂ] ProductC3L2 →L[ℂ] ProductC3L2 :=
  scalarVectorMulL2 productMeasure

/-- Vector-scalar multiplication on the transverse torus. -/
def vectorScalarMulTransverse :
    TransverseC3LInf →L[ℂ] TransverseScalarL2 →L[ℂ] TransverseC3L2 :=
  vectorScalarMulL2 transverseMeasure

/-- Vector-scalar multiplication on the product torus. -/
def vectorScalarMulProduct :
    ProductC3LInf →L[ℂ] ProductScalarL2 →L[ℂ] ProductC3L2 :=
  vectorScalarMulL2 productMeasure

/-! ### Fibre-generic transverse multipliers

`scalarVectorMulL2` and `vectorScalarMulL2` above are already generic in the fibre `E`, so a
transverse multiplier at any complex Euclidean fibre `ℂ^ι` is a direct instantiation.  The
`Fin 2` instances are the ones the horizontal torus operator of the paper needs.
-/

/-- Transverse `ℂ^ι`-valued `L∞`. -/
abbrev TransverseVecLInf (ι : Type*) [Fintype ι] :=
  Lp (EuclideanSpace ℂ ι) ∞ transverseMeasure

/-- Transverse `C2`-valued `L∞`. -/
abbrev TransverseC2LInf := TransverseVecLInf (Fin 2)

/-- Scalar-vector multiplication on the transverse torus with a fibre indexed by `ι`. -/
def scalarVectorMulTransverseVec (ι : Type*) [Fintype ι] :
    TransverseScalarLInf →L[ℂ] TransverseVecL2 ι →L[ℂ] TransverseVecL2 ι :=
  scalarVectorMulL2 transverseMeasure

/-- Vector-scalar multiplication on the transverse torus with a fibre indexed by `ι`. -/
def vectorScalarMulTransverseVec (ι : Type*) [Fintype ι] :
    TransverseVecLInf ι →L[ℂ] TransverseScalarL2 →L[ℂ] TransverseVecL2 ι :=
  vectorScalarMulL2 transverseMeasure

/-- Scalar-vector multiplication on the transverse torus at a two-component fibre. -/
abbrev scalarVectorMulTransverseC2 :
    TransverseScalarLInf →L[ℂ] TransverseC2L2 →L[ℂ] TransverseC2L2 :=
  scalarVectorMulTransverseVec (Fin 2)

/-- Vector-scalar multiplication on the transverse torus at a two-component fibre. -/
abbrev vectorScalarMulTransverseC2 :
    TransverseC2LInf →L[ℂ] TransverseScalarL2 →L[ℂ] TransverseC2L2 :=
  vectorScalarMulTransverseVec (Fin 2)

/-- The product of a transverse scalar `L∞` factor with a transverse `C³`-valued `L²` field is
represented almost everywhere by the pointwise product `y ↦ a y • b y`. -/
theorem scalarVectorMulTransverse_coe_ae
    (a : TransverseScalarLInf) (b : TransverseC3L2) :
    (scalarVectorMulTransverse a b : TransverseTorus → C3)
      =ᵐ[transverseMeasure] fun x ↦ a x • b x := by
  exact scalarVectorMulL2_coe_ae transverseMeasure a b

/-- The product of a scalar `L∞` factor with a `C³`-valued `L²` field on the product torus is
represented almost everywhere by the pointwise product `x ↦ a x • b x`. -/
theorem scalarVectorMulProduct_coe_ae
    (a : ProductScalarLInf) (b : ProductC3L2) :
    (scalarVectorMulProduct a b : ProductTorus3 → C3)
      =ᵐ[productMeasure] fun x ↦ a x • b x := by
  exact scalarVectorMulL2_coe_ae productMeasure a b

/-- The product of a transverse `C³`-valued `L∞` coefficient with a transverse scalar `L²`
function is represented almost everywhere by `y ↦ b y • a y`. -/
theorem vectorScalarMulTransverse_coe_ae
    (a : TransverseC3LInf) (b : TransverseScalarL2) :
    (vectorScalarMulTransverse a b : TransverseTorus → C3)
      =ᵐ[transverseMeasure] fun x ↦ b x • a x := by
  exact vectorScalarMulL2_coe_ae transverseMeasure a b

/-- The product of a `C³`-valued `L∞` coefficient with a scalar `L²` function on the product
torus is represented almost everywhere by `x ↦ b x • a x`. -/
theorem vectorScalarMulProduct_coe_ae
    (a : ProductC3LInf) (b : ProductScalarL2) :
    (vectorScalarMulProduct a b : ProductTorus3 → C3)
      =ᵐ[productMeasure] fun x ↦ b x • a x := by
  exact vectorScalarMulL2_coe_ae productMeasure a b

/-- Hölder's inequality on the transverse torus with exponents `∞` and `2`:
`‖a b‖_{L²} ≤ ‖a‖_{L∞} ‖b‖_{L²}` for a scalar factor `a` and a `C³`-valued field `b`. -/
theorem norm_scalarVectorMulTransverse_apply_le
    (a : TransverseScalarLInf) (b : TransverseC3L2) :
    ‖scalarVectorMulTransverse a b‖ ≤ ‖a‖ * ‖b‖ := by
  exact norm_scalarVectorMulL2_apply_le transverseMeasure a b

/-! ## Probability-space inclusions -/

/-- The normalized transverse volume is a probability measure. -/
instance instIsProbabilityMeasureTransverseMeasure :
    IsProbabilityMeasure transverseMeasure := by
  rw [show transverseMeasure = torusHaarMeasure (Fin 2) from
    volume_unitAddTorus_eq_haar]
  change IsProbabilityMeasure
    (Measure.pi (fun _ : Fin 2 ↦ AddCircle.haarAddCircle :
      Fin 2 → Measure UnitAddCircle))
  infer_instance

/-- The bounded inclusion of transverse scalar `L∞` into scalar `L²`. -/
def transverseScalarLInfToL2 : TransverseScalarLInf →L[ℂ] TransverseScalarL2 :=
  linftyToL2 transverseMeasure

/-- The bounded inclusion of transverse `C3`-valued `L∞` into `L²`. -/
def transverseC3LInfToL2 : TransverseC3LInf →L[ℂ] TransverseC3L2 :=
  linftyToL2 transverseMeasure

/-- The inclusion of transverse scalar `L∞` into `L²` does not change the function: it has the
same representative almost everywhere. -/
theorem transverseScalarLInfToL2_coe_ae (a : TransverseScalarLInf) :
    (transverseScalarLInfToL2 a : TransverseTorus → ℂ)
      =ᵐ[transverseMeasure] a := by
  exact linftyToL2_coe_ae transverseMeasure a

/-- The inclusion of transverse `C³`-valued `L∞` into `L²` does not change the field: it has the
same representative almost everywhere. -/
theorem transverseC3LInfToL2_coe_ae (a : TransverseC3LInf) :
    (transverseC3LInfToL2 a : TransverseTorus → C3)
      =ᵐ[transverseMeasure] a := by
  exact linftyToL2_coe_ae transverseMeasure a

/-! ## Pullback and exact axial commutation -/

/-- Pull a scalar transverse `L∞` coefficient back to the product torus. -/
def pullTransverseScalarLInf :
    TransverseScalarLInf →ₗᵢ[ℂ] ProductScalarLInf :=
  Lp.compMeasurePreservingₗᵢ ℂ Prod.fst measurePreserving_fst

/-- Pull a `C3`-valued transverse `L∞` coefficient back to the product torus. -/
def pullTransverseVectorLInf :
    TransverseC3LInf →ₗᵢ[ℂ] ProductC3LInf :=
  Lp.compMeasurePreservingₗᵢ ℂ Prod.fst measurePreserving_fst

/-- The pullback of a transverse scalar `L∞` coefficient along `(y, x₃) ↦ y` is represented
almost everywhere by `x ↦ a x.1`; in particular it does not depend on the axial variable. -/
theorem pullTransverseScalarLInf_coe_ae (a : TransverseScalarLInf) :
    (pullTransverseScalarLInf a : ProductTorus3 → ℂ)
      =ᵐ[productMeasure] fun x ↦ a x.1 := by
  exact Lp.coeFn_compMeasurePreserving a
    (measurePreserving_fst (μ := transverseMeasure) (ν := axialMeasure))

/-- The pullback of a transverse `C³`-valued `L∞` coefficient along `(y, x₃) ↦ y` is represented
almost everywhere by `x ↦ a x.1`; in particular it does not depend on the axial variable. -/
theorem pullTransverseVectorLInf_coe_ae (a : TransverseC3LInf) :
    (pullTransverseVectorLInf a : ProductTorus3 → C3)
      =ᵐ[productMeasure] fun x ↦ a x.1 := by
  exact Lp.coeFn_compMeasurePreserving a
    (measurePreserving_fst (μ := transverseMeasure) (ν := axialMeasure))

/-- Representative formula for the bundled scalar axial lift. -/
theorem scalarAxialLiftL2_coe_ae (K : ℤ) (b : TransverseScalarL2) :
    (scalarAxialLiftL2 K b : ProductTorus3 → ℂ)
      =ᵐ[productMeasure] fun x ↦ axialCharacter K x.2 * b x.1 := by
  exact scalarAxialLiftL2Fun_ae K b

/-- Multiplication by a transverse scalar coefficient commutes exactly with
the fixed-frequency axial vector lift. -/
theorem scalarVectorMul_axialLift (a : TransverseScalarLInf)
    (K : ℤ) (b : TransverseC3L2) :
    scalarVectorMulProduct (pullTransverseScalarLInf a) (axialLiftL2 K b) =
      axialLiftL2 K (scalarVectorMulTransverse a b) := by
  apply Lp.ext
  have hmulProd := scalarVectorMulProduct_coe_ae
    (pullTransverseScalarLInf a) (axialLiftL2 K b)
  have hpull := pullTransverseScalarLInf_coe_ae a
  have hlift := axialLiftL2_coe_ae K b
  have hmulTrans := scalarVectorMulTransverse_coe_ae a b
  have hmulTransProd :=
    (measurePreserving_fst (μ := transverseMeasure) (ν := axialMeasure)).quasiMeasurePreserving
      |>.ae_eq_comp hmulTrans
  have hliftOut := axialLiftL2_coe_ae K (scalarVectorMulTransverse a b)
  filter_upwards [hmulProd, hpull, hlift, hmulTransProd, hliftOut]
    with x hm hp hl hmt hlo
  change (scalarVectorMulTransverse a b : TransverseTorus → C3) x.1 =
    a x.1 • b x.1 at hmt
  rw [hm, hp, hl, hlo, hmt]
  simp [smul_smul, mul_comm]

/-- Multiplication of a lifted scalar field by a transverse vector coefficient
commutes exactly with the fixed-frequency axial lift. -/
theorem vectorScalarMul_axialLift (a : TransverseC3LInf)
    (K : ℤ) (b : TransverseScalarL2) :
    vectorScalarMulProduct (pullTransverseVectorLInf a) (scalarAxialLiftL2 K b) =
      axialLiftL2 K (vectorScalarMulTransverse a b) := by
  apply Lp.ext
  have hmulProd := vectorScalarMulProduct_coe_ae
    (pullTransverseVectorLInf a) (scalarAxialLiftL2 K b)
  have hpull := pullTransverseVectorLInf_coe_ae a
  have hlift := scalarAxialLiftL2_coe_ae K b
  have hmulTrans := vectorScalarMulTransverse_coe_ae a b
  have hmulTransProd :=
    (measurePreserving_fst (μ := transverseMeasure) (ν := axialMeasure)).quasiMeasurePreserving
      |>.ae_eq_comp hmulTrans
  have hliftOut := axialLiftL2_coe_ae K (vectorScalarMulTransverse a b)
  filter_upwards [hmulProd, hpull, hlift, hmulTransProd, hliftOut]
    with x hm hp hl hmt hlo
  change (vectorScalarMulTransverse a b : TransverseTorus → C3) x.1 =
    b x.1 • a x.1 at hmt
  rw [hm, hp, hl, hlo, hmt]
  simp [smul_smul]

end

end FastDynamo
