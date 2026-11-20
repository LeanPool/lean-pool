/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.TorusHaarTransport
public import LeanPool.FastDynamo.Fourier.ProductH2
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Complete scalar Fourier analysis on the split product torus

The product `T² × T¹` used by the axial-mode development is measurably
equivalent to the ordinary three-torus.  This file transports Mathlib's
complete three-torus Fourier basis across that equivalence.  The result is an
analysis/synthesis isometry on product `L²`, rather than only a family
of coefficient functionals.

The measure-preserving equivalence and the isometric `L²` transport it induces
are set up here once and for all, for an arbitrary Banach-module-valued `L²`
space (`productToLiteral`, `toLiteralL2`).  The scalar case
(`productScalarL2EquivFlat`) is what the Fourier transport below uses; the real
and complex vector-valued cases are what
`FastDynamo/Analysis/LiteralThreeTorus.lean` uses to state the magnetic clauses
on the literal `Torus 3`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-- The unsplit three-torus used only as a bridge to Mathlib's Fourier basis. -/
abbrev FlatTorus3 := UnitAddTorus (Fin 3)

/-- Scalar `L²` on the unsplit three-torus. -/
abbrev FlatTorus3ScalarL2 := Lp ℂ 2 (volume : Measure FlatTorus3)

/-- Flat three-dimensional integer frequencies. -/
abbrev FlatTorus3Frequency := Fin 3 → ℤ

/-- Split off the last coordinate and place it after the transverse pair. -/
def flatTorus3ToProduct : FlatTorus3 ≃ᵐ ProductTorus3 :=
  (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin 3 => UnitAddCircle) (Fin.last 2)).trans
    MeasurableEquiv.prodComm

/-- The project's explicit split product measure is the ordinary product volume. -/
theorem productMeasure_eq_volume :
    productMeasure = (volume : Measure ProductTorus3) := by
  rw [Measure.volume_eq_prod]
  simp only [productMeasure, transverseMeasure, axialMeasure]
  rw [volume_unitAddCircle_eq_haar]

/-- The coordinate-splitting equivalence preserves the project's product measure. -/
theorem flatTorus3ToProduct_measurePreserving :
    MeasurePreserving flatTorus3ToProduct
      (volume : Measure FlatTorus3) productMeasure := by
  rw [productMeasure_eq_volume]
  have hsplit := volume_preserving_piFinSuccAbove
    (fun _ : Fin 3 => UnitAddCircle) (Fin.last 2)
  have hswap : MeasurePreserving
      (Prod.swap : UnitAddCircle × TransverseTorus →
        TransverseTorus × UnitAddCircle) :=
    Measure.measurePreserving_swap
  change MeasurePreserving
    (Prod.swap ∘ (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin 3 => UnitAddCircle) (Fin.last 2))) volume volume
  exact hswap.comp hsplit

/-! ## Isometric `L²` transport to the literal three-torus

The coordinate splitting is measure preserving, so composition with it transports `L²` classes
between the two models isometrically.  The construction is carried out **once**, for an arbitrary
Banach-module-valued `L²` space, and every model of the development — the scalar one used by the
Fourier analysis below, and the real and complex vector-valued ones used by
`FastDynamo/Analysis/LiteralThreeTorus.lean` to state the magnetic clauses on `Torus 3` — is a
specialisation of it.
-/

/-- The measurable identification of the product model with the literal three-torus.  It is the
inverse of the coordinate split `flatTorus3ToProduct`. -/
def productToLiteral : ProductTorus3 ≃ᵐ Torus 3 := flatTorus3ToProduct.symm

/-- Explicit coordinate formula: the identification appends the axial coordinate. -/
@[simp] theorem productToLiteral_apply (y : TransverseTorus) (s : AxialCircle) :
    productToLiteral (y, s) = Fin.snoc y s :=
  Fin.insertNth_last' s y

/-- Explicit coordinate formula for the inverse identification: it reads off the two transverse
coordinates and the axial one. -/
@[simp] theorem productToLiteral_symm_apply (x : Torus 3) :
    productToLiteral.symm x = (fun j : Fin 2 => x j.castSucc, x (Fin.last 2)) := by
  have h : (fun j : Fin 2 => x ((Fin.last 2).succAbove j)) = fun j : Fin 2 => x j.castSucc := by
    funext j
    exact congrArg x (Fin.succAbove_last_apply j)
  change ((fun j : Fin 2 => x ((Fin.last 2).succAbove j)), x (Fin.last 2)) = _
  rw [h]

/-- The identification of the product model with the literal three-torus is measure preserving:
it carries `productMeasure` to the ambient volume of `Torus 3`. -/
theorem measurePreserving_productToLiteral :
    MeasurePreserving productToLiteral productMeasure (volume : Measure (Torus 3)) :=
  flatTorus3ToProduct_measurePreserving.symm flatTorus3ToProduct

/-! Generic facts about the `L²` pullback along a measure-preserving map.  They are stated for an
arbitrary pair of measure spaces and kept out of the root namespace, where their names would be
collision-prone. -/

namespace LpTransport

/-- Composition with a measure-preserving map, packaged as a linear isometry, agrees with the
additive-group-homomorphism packaging. -/
theorem compMeasurePreservingₗᵢ_eq {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (𝕜 : Type*) [NormedRing 𝕜] {E : Type*}
    [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {F : X → Y} (hF : MeasurePreserving F μ ν) (g : Lp E p ν) :
    Lp.compMeasurePreservingₗᵢ 𝕜 F hF g = Lp.compMeasurePreserving F hF g := rfl

/-- Composing the two `L²` pullbacks attached to a pair of mutually inverse measure-preserving
maps returns the original `L²` class.  This is Mathlib's `Lp.compMeasurePreserving_comp_apply`
followed by `Lp.compMeasurePreserving_id_apply`. -/
theorem compMeasurePreservingₗᵢ_comp_self {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (𝕜 : Type*) [NormedRing 𝕜] {E : Type*}
    [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {F : X → Y} {G : Y → X} (hF : MeasurePreserving F μ ν) (hG : MeasurePreserving G ν μ)
    (hGF : G ∘ F = id) (u : Lp E p μ) :
    Lp.compMeasurePreservingₗᵢ 𝕜 F hF (Lp.compMeasurePreservingₗᵢ 𝕜 G hG u) = u := by
  simp only [compMeasurePreservingₗᵢ_eq]
  rw [← Lp.compMeasurePreserving_comp_apply u hG hF]
  refine Eq.trans ?_ (Lp.compMeasurePreserving_id_apply u)
  congr 1
  congr 1

end LpTransport

/-- Pullback along `productToLiteral.symm`: the forward `L²` transport to the literal torus. -/
def toLiteralL2ₗᵢ (𝕜 E : Type*) [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] :
    Lp E 2 productMeasure →ₗᵢ[𝕜] Lp E 2 (volume : Measure (Torus 3)) :=
  Lp.compMeasurePreservingₗᵢ 𝕜 (⇑productToLiteral.symm)
    (measurePreserving_productToLiteral.symm productToLiteral)

/-- Pullback along `productToLiteral`: the inverse `L²` transport from the literal torus. -/
def fromLiteralL2ₗᵢ (𝕜 E : Type*) [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] :
    Lp E 2 (volume : Measure (Torus 3)) →ₗᵢ[𝕜] Lp E 2 productMeasure :=
  Lp.compMeasurePreservingₗᵢ 𝕜 (⇑productToLiteral) measurePreserving_productToLiteral

/-- The isometric `L²` transport between the product model and the literal three-torus. -/
def toLiteralL2 (𝕜 E : Type*) [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] :
    Lp E 2 productMeasure ≃ₗᵢ[𝕜] Lp E 2 (volume : Measure (Torus 3)) where
  toFun := toLiteralL2ₗᵢ 𝕜 E
  map_add' u v := map_add (toLiteralL2ₗᵢ 𝕜 E) u v
  map_smul' c u := map_smul (toLiteralL2ₗᵢ 𝕜 E) c u
  invFun := fromLiteralL2ₗᵢ 𝕜 E
  left_inv u :=
    LpTransport.compMeasurePreservingₗᵢ_comp_self 𝕜 measurePreserving_productToLiteral
      (measurePreserving_productToLiteral.symm productToLiteral)
      (funext productToLiteral.symm_apply_apply) u
  right_inv u :=
    LpTransport.compMeasurePreservingₗᵢ_comp_self 𝕜
      (measurePreserving_productToLiteral.symm productToLiteral)
      measurePreserving_productToLiteral
      (funext productToLiteral.apply_symm_apply) u
  norm_map' u := (toLiteralL2ₗᵢ 𝕜 E).norm_map u

/-- Pull a scalar product-torus `L²` field back to the ordinary three-torus: the scalar case of
the general transport `toLiteralL2ₗᵢ`. -/
def productScalarL2ToFlat : ProductScalarL2 →ₗᵢ[ℂ] FlatTorus3ScalarL2 := toLiteralL2ₗᵢ ℂ ℂ

/-- The split and unsplit scalar `L²` models are linearly isometrically equivalent: the scalar
case of the general transport `toLiteralL2`. -/
def productScalarL2EquivFlat : ProductScalarL2 ≃ₗᵢ[ℂ] FlatTorus3ScalarL2 := toLiteralL2 ℂ ℂ

/-! ## Complete flat-frequency analysis and synthesis -/

/-- Square-summable scalar arrays indexed by ordinary three-dimensional frequencies. -/
abbrev FlatTorus3ScalarFourierL2 :=
  lp (fun _ : FlatTorus3Frequency => ℂ) 2

/-- Mathlib's three-torus Fourier basis transported to the physical-volume
instance used by this project. -/
def flatTorus3FourierBasis :
    HilbertBasis FlatTorus3Frequency ℂ FlatTorus3ScalarL2 := by
  change HilbertBasis FlatTorus3Frequency ℂ
    (Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))))
  rw [volume_unitAddTorus_eq_haar]
  exact UnitAddTorus.mFourierBasis (d := Fin 3)

/-- Fourier analysis on the split product, transported from Mathlib's complete
three-torus Hilbert basis. -/
def productScalarFourierAnalysisFlat :
    ProductScalarL2 ≃ₗᵢ[ℂ] FlatTorus3ScalarFourierL2 :=
  productScalarL2EquivFlat.trans
    flatTorus3FourierBasis.repr

/-- The transported complete Hilbert basis on the split product torus. -/
def productScalarFourierBasisFlat :
    HilbertBasis FlatTorus3Frequency ℂ ProductScalarL2 :=
  HilbertBasis.ofRepr productScalarFourierAnalysisFlat

/-! ## Reindexing and the project's nested coefficient space -/

section Reindex

variable {I J : Type*}

/-- Reindex scalar square-summable families along an equivalence. -/
def scalarL2ReindexLinearEquiv (e : I ≃ J) :
    lp (fun _ : I => ℂ) 2 ≃ₗ[ℂ] lp (fun _ : J => ℂ) 2 where
  toFun f := ⟨fun j => f (e.symm j), memℓp_gen <|
    e.symm.summable_iff.mpr ((lp.memℓp f).summable (by norm_num))⟩
  invFun g := ⟨fun i => g (e i), memℓp_gen <|
    e.summable_iff.mpr ((lp.memℓp g).summable (by norm_num))⟩
  left_inv f := by
    apply lp.ext
    funext i
    exact congrArg f (e.symm_apply_apply i)
  right_inv g := by
    apply lp.ext
    funext j
    exact congrArg g (e.apply_symm_apply j)
  map_add' f g := by
    apply lp.ext
    rfl
  map_smul' c f := by
    apply lp.ext
    rfl

/-- Reindexing is an isometry on scalar `ℓ²`. -/
def scalarL2Reindex (e : I ≃ J) :
    lp (fun _ : I => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : J => ℂ) 2 :=
  LinearIsometryEquiv.mk (scalarL2ReindexLinearEquiv e) (by
    intro f
    rw [lp.norm_eq_tsum_rpow (by norm_num),
      lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    change (∑' j : J, ‖f (e.symm j)‖ ^ (2 : ℝ≥0∞).toReal) =
      ∑' i : I, ‖f i‖ ^ (2 : ℝ≥0∞).toReal
    exact e.symm.tsum_eq (fun i => ‖f i‖ ^ (2 : ℝ≥0∞).toReal))

end Reindex

section Nested

variable {I J : Type*}

/-- A nested scalar `ℓ²` family. -/
abbrev ScalarL2Nested := lp (fun _ : I => lp (fun _ : J => ℂ) 2) 2

/-- The corresponding flat scalar `ℓ²` family. -/
abbrev ScalarL2Flat := lp (fun _ : I × J => ℂ) 2

/-- Flatten a nested scalar `ℓ²` family. -/
def scalarL2NestedToFlat (a : ScalarL2Nested (I := I) (J := J)) :
    ScalarL2Flat (I := I) (J := J) := by
  refine ⟨fun ij => a ij.1 ij.2, memℓp_gen ?_⟩
  rw [summable_prod_of_nonneg (fun _ => by positivity)]
  constructor
  · intro i
    exact (lp.memℓp (a i)).summable (by norm_num)
  · have hout := (lp.memℓp a).summable (by norm_num)
    convert hout using 1
    funext i
    exact (lp.norm_rpow_eq_tsum (by norm_num) (a i)).symm

/-- Regroup a flat scalar `ℓ²` family into nested rows. -/
def scalarL2FlatToNested (f : ScalarL2Flat (I := I) (J := J)) :
    ScalarL2Nested (I := I) (J := J) := by
  have hflat := (lp.memℓp f).summable (by norm_num)
  have hsplit := (summable_prod_of_nonneg (fun _ => by positivity)).mp hflat
  let row : I → lp (fun _ : J => ℂ) 2 := fun i =>
    ⟨fun j => f (i, j), memℓp_gen (hsplit.1 i)⟩
  refine ⟨row, memℓp_gen ?_⟩
  convert hsplit.2 using 1
  funext i
  exact lp.norm_rpow_eq_tsum (by norm_num) (row i)

/-- Flattening and regrouping are inverse complex-linear maps. -/
def scalarL2NestedFlatLinearEquiv :
    ScalarL2Nested (I := I) (J := J) ≃ₗ[ℂ]
      ScalarL2Flat (I := I) (J := J) where
  toFun := scalarL2NestedToFlat
  invFun := scalarL2FlatToNested
  left_inv a := by
    apply lp.ext
    funext i
    apply lp.ext
    rfl
  right_inv f := by
    apply lp.ext
    rfl
  map_add' a b := by
    apply lp.ext
    rfl
  map_smul' c a := by
    apply lp.ext
    rfl

/-- The canonical isometry between nested and flat scalar `ℓ²`. -/
def scalarL2NestedFlat :
    ScalarL2Nested (I := I) (J := J) ≃ₗᵢ[ℂ]
      ScalarL2Flat (I := I) (J := J) :=
  LinearIsometryEquiv.mk scalarL2NestedFlatLinearEquiv (by
    intro a
    rw [lp.norm_eq_tsum_rpow (by norm_num),
      lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    change (∑' ij : I × J, ‖a ij.1 ij.2‖ ^ (2 : ℝ≥0∞).toReal) =
      ∑' i : I, ‖a i‖ ^ (2 : ℝ≥0∞).toReal
    have hflat : Summable
        (fun ij : I × J => ‖a ij.1 ij.2‖ ^ (2 : ℝ≥0∞).toReal) := by
      simpa only [scalarL2NestedToFlat] using
        (lp.memℓp (scalarL2NestedToFlat a)).summable (by norm_num)
    rw [hflat.tsum_prod]
    apply tsum_congr
    intro i
    exact (lp.norm_rpow_eq_tsum (by norm_num) (a i)).symm)

end Nested

/-- Split a flat frequency into its transverse pair and last axial entry. -/
def flatFrequencyToProduct :
    FlatTorus3Frequency ≃ TransverseFrequency × ℤ :=
  ((Fin.insertNthEquiv (fun _ : Fin 3 => ℤ) (Fin.last 2)).symm).trans
    (Equiv.prodComm ℤ TransverseFrequency)

/-- Fourier analysis with a flat `(transverse, axial)` index. -/
def productScalarFourierAnalysisPair :
    ProductScalarL2 ≃ₗᵢ[ℂ]
      lp (fun _ : TransverseFrequency × ℤ => ℂ) 2 :=
  productScalarFourierAnalysisFlat.trans
    (scalarL2Reindex flatFrequencyToProduct)

/-- Complete product Fourier analysis in the nested coefficient model already
used by `ProductC3H2`: axial frequency outside, transverse frequency inside. -/
def productScalarFourierAnalysisNested :
    ProductScalarL2 ≃ₗᵢ[ℂ] ProductScalarFourierL2 :=
  productScalarFourierAnalysisPair.trans
    ((scalarL2Reindex (Equiv.prodComm TransverseFrequency ℤ)).trans
      scalarL2NestedFlat.symm)

/-- Fourier synthesis from the project's nested product coefficients. -/
def productScalarFourierSynthesisNested :
    ProductScalarFourierL2 →L[ℂ] ProductScalarL2 :=
  productScalarFourierAnalysisNested.symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- Nested Fourier analysis inverts nested Fourier synthesis: analysing the field synthesized
from a nested coefficient array returns that array. -/
@[simp] theorem productScalarFourierAnalysisNested_synthesis
    (a : ProductScalarFourierL2) :
    productScalarFourierAnalysisNested
      (productScalarFourierSynthesisNested a) = a :=
  productScalarFourierAnalysisNested.apply_symm_apply a

/-- Nested Fourier synthesis inverts nested Fourier analysis: summing the nested Fourier series
of a scalar product `L²` field returns the field. -/
@[simp] theorem productScalarFourierSynthesisNested_analysis
    (f : ProductScalarL2) :
    productScalarFourierSynthesisNested
      (productScalarFourierAnalysisNested f) = f :=
  productScalarFourierAnalysisNested.symm_apply_apply f

/-- Scalar product `L²` fields are determined by all nested Fourier entries. -/
theorem productScalarL2_ext_nested_coeff {f g : ProductScalarL2}
    (h : ∀ k n, productScalarFourierAnalysisNested f k n =
      productScalarFourierAnalysisNested g k n) :
    f = g := by
  apply productScalarFourierAnalysisNested.injective
  apply lp.ext
  funext k
  apply lp.ext
  funext n
  exact h k n

/-! ## Compatibility with the split monomials -/

/-- The `(k,n)` entry of nested analysis is the flat entry at `Fin.snoc n k`. -/
theorem productScalarFourierAnalysisNested_apply
    (f : ProductScalarL2) (k : ℤ) (n : TransverseFrequency) :
    productScalarFourierAnalysisNested f k n =
      productScalarFourierAnalysisFlat f (Fin.snoc n k) := by
  change productScalarFourierAnalysisFlat f
    ((Fin.insertNthEquiv (fun _ : Fin 3 => ℤ) (Fin.last 2)) (k, n)) = _
  rw [Fin.insertNthEquiv_last]
  rfl

/-- Transport an `L²` class on the three-torus from the Haar-measure instance to the `volume`
instance used by this project, along the equality of the two measures. -/
private def flatHaarToPhysical
    (f : Lp ℂ 2 (torusHaarMeasure (Fin 3))) : FlatTorus3ScalarL2 :=
  cast (congrArg (fun μ : Measure FlatTorus3 => ↥(Lp ℂ 2 μ))
    (volume_unitAddTorus_eq_haar (d := Fin 3)).symm) f

/-- The transported basis vector at frequency `m` is the image, under the measure-instance
transport, of Mathlib's Haar-normalized three-torus Fourier basis vector at `m`. -/
private lemma flatBasis_eq_haarMonomial (m : FlatTorus3Frequency) :
    flatTorus3FourierBasis m =
      flatHaarToPhysical
        (UnitAddTorus.mFourierBasis (d := Fin 3) m) := by
  apply eq_of_heq
  unfold flatTorus3FourierBasis flatHaarToPhysical
  exact heq_of_eq (castHilbertBasis_apply
    (volume_unitAddTorus_eq_haar (d := Fin 3))
    (UnitAddTorus.mFourierBasis (d := Fin 3)) m)

/-- The `L²` class, for the physical volume measure on the three-torus, of the continuous
character `x ↦ e^{2πi m·x}`. -/
private def flatPhysicalMonomial (m : FlatTorus3Frequency) :
    FlatTorus3ScalarL2 :=
  ContinuousMap.toLp 2 (volume : Measure FlatTorus3) ℂ
    (UnitAddTorus.mFourier m)

/-- Each vector of the transported three-torus Fourier basis is the `L²` class of the continuous
character of the same frequency. -/
private lemma flatBasis_eq_physicalMonomial (m : FlatTorus3Frequency) :
    flatTorus3FourierBasis m = flatPhysicalMonomial m := by
  let _ : IsFiniteMeasure (torusHaarMeasure (Fin 3)) := by
    rw [← volume_unitAddTorus_eq_haar]
    infer_instance
  rw [flatBasis_eq_haarMonomial, UnitAddTorus.coe_mFourierBasis]
  exact castContinuousMapToLp
    (volume_unitAddTorus_eq_haar (d := Fin 3))
    (UnitAddTorus.mFourier m)

/-- The transverse Fourier basis vector at frequency `n` is represented almost everywhere by the
continuous character `x ↦ e^{2πi n·x}`. -/
private lemma transverseBasis_coe_ae (n : TransverseFrequency) :
    (transverseScalarFourierBasis n : TransverseTorus → ℂ) =ᵐ[transverseMeasure]
      UnitAddTorus.mFourier n := by
  rw [transverseBasis_eq_physicalMonomial]
  exact ContinuousMap.coeFn_toLp transverseMeasure (UnitAddTorus.mFourier n)

/-- The three-torus Fourier basis vector at frequency `m` is represented almost everywhere by the
continuous character `x ↦ e^{2πi m·x}`. -/
private lemma flatBasis_coe_ae (m : FlatTorus3Frequency) :
    (flatTorus3FourierBasis m : FlatTorus3 → ℂ) =ᵐ[volume]
      UnitAddTorus.mFourier m := by
  rw [flatBasis_eq_physicalMonomial]
  exact ContinuousMap.coeFn_toLp (volume : Measure FlatTorus3)
    (UnitAddTorus.mFourier m)

/-- Explicit coordinates of the measurable splitting equivalence. -/
theorem flatTorus3ToProduct_apply (x : FlatTorus3) :
    flatTorus3ToProduct x =
      ((fun j : Fin 2 => x j.castSucc), x (Fin.last 2)) := by
  change (Fin.removeNth (Fin.last 2) x, x (Fin.last 2)) = _
  congr
  funext j
  change x ((Fin.last 2).succAbove j) = x j.castSucc
  rw [Fin.succAbove_last_apply]

/-- A split product monomial pulls back to the corresponding ordinary
three-torus monomial. -/
theorem productScalarL2ToFlat_productMonomial
    (n : TransverseFrequency) (k : ℤ) :
    productScalarL2ToFlat (productMonomialL2 n k) =
      flatTorus3FourierBasis (Fin.snoc n k) := by
  apply Lp.ext
  have hpull := Lp.coeFn_compMeasurePreserving (productMonomialL2 n k)
    flatTorus3ToProduct_measurePreserving
  have hproduct := scalarAxialLiftL2Fun_ae k (transverseMonomialL2 n)
  have hproductFlat :=
    flatTorus3ToProduct_measurePreserving.quasiMeasurePreserving.ae_eq_comp hproduct
  have htrans := transverseBasis_coe_ae n
  have hfst : MeasurePreserving
      (fun x : FlatTorus3 => (flatTorus3ToProduct x).1)
      (volume : Measure FlatTorus3) transverseMeasure :=
    (measurePreserving_fst (μ := transverseMeasure) (ν := axialMeasure)).comp
      flatTorus3ToProduct_measurePreserving
  have htransFlat := hfst.quasiMeasurePreserving.ae_eq_comp htrans
  have hflat := flatBasis_coe_ae (Fin.snoc n k)
  filter_upwards [hpull, hproductFlat, htransFlat, hflat] with x hp hprod htr hfl
  change ((productScalarL2ToFlat (productMonomialL2 n k) :
    FlatTorus3ScalarL2) : FlatTorus3 → ℂ) x =
      ((productMonomialL2 n k : ProductScalarL2) : ProductTorus3 → ℂ)
        (flatTorus3ToProduct x) at hp
  change ((productMonomialL2 n k : ProductScalarL2) : ProductTorus3 → ℂ)
      (flatTorus3ToProduct x) =
        axialCharacter k (flatTorus3ToProduct x).2 *
          ((transverseMonomialL2 n : TransverseScalarL2) :
            TransverseTorus → ℂ) (flatTorus3ToProduct x).1 at hprod
  change ((transverseMonomialL2 n : TransverseScalarL2) :
      TransverseTorus → ℂ) (flatTorus3ToProduct x).1 =
        UnitAddTorus.mFourier n (flatTorus3ToProduct x).1 at htr
  rw [hp, hprod, htr, hfl, flatTorus3ToProduct_apply]
  simp only [UnitAddTorus.mFourier, Fin.prod_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last, axialCharacter]
  simp only [ContinuousMap.coe_mk]
  ring

/-- The transported complete basis agrees exactly with the split monomial
family already used to define `productCoeffCLM`. -/
theorem productScalarFourierBasisFlat_snoc
    (n : TransverseFrequency) (k : ℤ) :
    productScalarFourierBasisFlat (Fin.snoc n k) =
      productMonomialL2 n k := by
  apply productScalarL2EquivFlat.injective
  rw [show productScalarFourierBasisFlat (Fin.snoc n k) =
      productScalarL2EquivFlat.symm
        (flatTorus3FourierBasis (Fin.snoc n k)) by rfl]
  rw [productScalarL2EquivFlat.apply_symm_apply]
  exact (productScalarL2ToFlat_productMonomial n k).symm

/-- Exact compatibility between complete nested Fourier analysis and the
split-monomial inner products. -/
theorem productScalarFourierAnalysisNested_eq_inner
    (f : ProductScalarL2) (k : ℤ) (n : TransverseFrequency) :
    productScalarFourierAnalysisNested f k n =
      inner ℂ (productMonomialL2 n k) f := by
  rw [productScalarFourierAnalysisNested_apply]
  change productScalarFourierBasisFlat.repr f (Fin.snoc n k) = _
  rw [HilbertBasis.repr_apply_apply, productScalarFourierBasisFlat_snoc]

/-- Scalar product `L²` fields are determined by their split-monomial
coefficients. -/
theorem productScalarL2_ext_coeff {f g : ProductScalarL2}
    (h : ∀ n k, inner ℂ (productMonomialL2 n k) f =
      inner ℂ (productMonomialL2 n k) g) :
    f = g := by
  apply productScalarL2_ext_nested_coeff
  intro k n
  rw [productScalarFourierAnalysisNested_eq_inner,
    productScalarFourierAnalysisNested_eq_inner]
  exact h n k

/-- Vector-valued product `L²` fields are determined by their
`productCoeffCLM` coefficients. -/
theorem productC3L2_ext_coeff {f g : ProductC3L2}
    (h : ∀ n k i, productCoeffCLM n k i f =
      productCoeffCLM n k i g) :
    f = g := by
  have hcoord : ∀ i : Fin 3, productCoordL2 i f =
      productCoordL2 i g := by
    intro i
    apply productScalarL2_ext_coeff
    intro n k
    exact h n k i
  apply Lp.ext
  have hcoord_ae : ∀ i : Fin 3,
      ((productCoordL2 i f : ProductScalarL2) : ProductTorus3 → ℂ)
        =ᵐ[productMeasure]
      ((productCoordL2 i g : ProductScalarL2) : ProductTorus3 → ℂ) := by
    intro i
    rw [hcoord i]
  have hf : ∀ i : Fin 3,
      ((productCoordL2 i f : ProductScalarL2) : ProductTorus3 → ℂ)
        =ᵐ[productMeasure] fun x => (f x) i := by
    intro i
    exact (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL f
  have hg : ∀ i : Fin 3,
      ((productCoordL2 i g : ProductScalarL2) : ProductTorus3 → ℂ)
        =ᵐ[productMeasure] fun x => (g x) i := by
    intro i
    exact (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL g
  filter_upwards [ae_all_iff.2 hcoord_ae, ae_all_iff.2 hf,
    ae_all_iff.2 hg] with x hfg hfx hgx
  apply PiLp.ext
  intro i
  calc
    (f x) i = (productCoordL2 i f : ProductScalarL2) x :=
      (hfx i).symm
    _ = (productCoordL2 i g : ProductScalarL2) x := hfg i
    _ = (g x) i := hgx i

end

end FastDynamo
