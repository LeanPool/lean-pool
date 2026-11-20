/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.ProductVectorCalculus
public import LeanPool.FastDynamo.Analysis.WeakLeibniz

/-!
# Realification and conjugation on the product torus

This module supplies the real-linear maps needed to turn a complex axial
eigenmode into a real field.  Conjugation on the Fourier graph reverses
both the transverse and axial frequencies; this is proved rather than hidden
behind a choice of representatives.

`norm_complexifyProductR3L2` records that the inclusion of the real field into
the complex one is an isometry, which is what lets the real datum
`B_in^ε = Re V^ε` of `eq:main-thm-growth` be compared with its image in the complex space
where the induction semigroup acts.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-! ## Pointwise maps and their `L²` lifts -/

/-- Coordinatewise complex conjugation on `ℂ³`, as a real-linear map. -/
def conjC3LinearMap : C3 →ₗ[ℝ] C3 where
  toFun z := WithLp.toLp 2 (fun i : Fin 3 => starRingEnd ℂ (z i))
  map_add' z w := by
    apply PiLp.ext
    intro i
    simp
  map_smul' r z := by
    apply PiLp.ext
    intro i
    simp [Complex.conj_ofReal]

/-- Coordinatewise complex conjugation on `ℂ³`, continuously real-linear. -/
def conjC3 : C3 →L[ℝ] C3 :=
  ⟨conjC3LinearMap, conjC3LinearMap.continuous_of_finiteDimensional⟩

/-- Coordinatewise conjugation on `ℂ³` acts on each entry by complex conjugation. -/
@[simp] theorem conjC3_apply (z : C3) (i : Fin 3) :
    conjC3 z i = starRingEnd ℂ (z i) :=
  rfl

/-- Coordinatewise conjugation on `ℂ³` is an involution. -/
@[simp] theorem conjC3_involutive (z : C3) : conjC3 (conjC3 z) = z := by
  apply PiLp.ext
  intro i
  simp

/-- Complexification of real vector fields on the product torus. -/
def complexifyProductR3L2 : ProductR3L2 →L[ℝ] ProductC3L2 :=
  complexifyR3.compLpL 2 productMeasure

/-- The complexification of a real vector field is represented almost everywhere by the
pointwise complexification `x ↦ complexifyR3 (v x)`. -/
theorem complexifyProductR3L2_coe_ae (v : ProductR3L2) :
    (complexifyProductR3L2 v : ProductTorus3 → C3) =ᵐ[productMeasure]
      fun x => complexifyR3 (v x) := by
  exact complexifyR3.coeFn_compLpL v

/-- **Complexification is an isometry on `ℝ³`**: `‖(v₁, v₂, v₃)‖ = ‖(v₁, v₂, v₃)‖` read in
`ℂ³`, because `‖(r : ℂ)‖ = |r|` coordinatewise. -/
theorem norm_complexifyR3 (v : R3) : ‖complexifyR3 v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [complexifyR3_apply, Complex.norm_real]

/-- **Complexification is an isometry on product `L²`**: the real field `v` and the complex
field `complexifyProductR3L2 v` have the same `L²` norm.

This is the small norm computation that lets the real datum `B_in^ε = Re V^ε`, which lives in
`L²(T³;ℝ³)`, be compared with its image in `L²(T³;ℂ³)`, where the induction semigroup acts:
`complexifyR3` is a pointwise isometry, and `eLpNorm` only sees pointwise norms.  It is used
for the exact growth law `eq:main-thm-growth` of the semigroup orbit. -/
theorem norm_complexifyProductR3L2 (v : ProductR3L2) :
    ‖complexifyProductR3L2 v‖ = ‖v‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) ?_
  filter_upwards [complexifyProductR3L2_coe_ae v] with x hx
  rw [hx, norm_complexifyR3]

/-- Complexification does not create or destroy the zero field. -/
@[simp] theorem complexifyProductR3L2_eq_zero_iff (v : ProductR3L2) :
    complexifyProductR3L2 v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hn : ‖v‖ = 0 := by rw [← norm_complexifyProductR3L2, h, norm_zero]
    exact norm_eq_zero.1 hn
  · rintro rfl
    exact map_zero _

/-- Pointwise scalar conjugation on product `L²`. -/
def productScalarConjL2 : ProductScalarL2 →L[ℝ] ProductScalarL2 :=
  Complex.conjCLE.toContinuousLinearMap.compLpL 2 productMeasure

/-- Conjugation of a scalar product `L²` class is represented almost everywhere by pointwise
complex conjugation. -/
theorem productScalarConjL2_coe_ae (f : ProductScalarL2) :
    (productScalarConjL2 f : ProductTorus3 → ℂ) =ᵐ[productMeasure]
      fun x => starRingEnd ℂ (f x) := by
  exact Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL f

/-- Pointwise coordinatewise conjugation on vector-valued product `L²`. -/
def productConjL2 : ProductC3L2 →L[ℝ] ProductC3L2 :=
  conjC3.compLpL 2 productMeasure

/-- Conjugation of a `C³`-valued product `L²` class is represented almost everywhere by
coordinatewise pointwise conjugation. -/
theorem productConjL2_coe_ae (V : ProductC3L2) :
    (productConjL2 V : ProductTorus3 → C3) =ᵐ[productMeasure]
      fun x => conjC3 (V x) := by
  exact conjC3.coeFn_compLpL V

/-- Conjugation on scalar product `L²` is an involution. -/
@[simp] theorem productScalarConjL2_involutive (f : ProductScalarL2) :
    productScalarConjL2 (productScalarConjL2 f) = f := by
  apply Lp.ext
  filter_upwards [productScalarConjL2_coe_ae f,
    productScalarConjL2_coe_ae (productScalarConjL2 f)] with x hf hh
  rw [hh, hf]
  simp

/-- Conjugation on `C³`-valued product `L²` is an involution. -/
@[simp] theorem productConjL2_involutive (V : ProductC3L2) :
    productConjL2 (productConjL2 V) = V := by
  apply Lp.ext
  filter_upwards [productConjL2_coe_ae V,
    productConjL2_coe_ae (productConjL2 V)] with x hV hh
  rw [hh, hV, conjC3_involutive]

/-- Taking the real part of a complexified real field returns the original real field. -/
theorem realPartL2_complexifyProductR3L2 (v : ProductR3L2) :
    realPartL2 (complexifyProductR3L2 v) = v := by
  apply Lp.ext
  have hre := realPartL2_coe_ae (complexifyProductR3L2 v)
  filter_upwards [hre, complexifyProductR3L2_coe_ae v] with x hr hc
  rw [hr, hc]
  apply PiLp.ext
  intro i
  simp [vecRe]

/-- The complex-valued realization of coordinatewise real part. -/
def productRealPartL2 : ProductC3L2 →L[ℝ] ProductC3L2 :=
  (1 / 2 : ℝ) •
    ((ContinuousLinearMap.id ℝ ProductC3L2) + productConjL2)

/-- The complex realization of the real part acts as `V ↦ (V + conj V)/2`. -/
theorem productRealPartL2_apply (V : ProductC3L2) :
    productRealPartL2 V = (1 / 2 : ℝ) • (V + productConjL2 V) := by
  rfl

/-- The two descriptions of the real part agree: complexifying the real-valued real part of `V`
gives `(V + conj V)/2`. -/
theorem complexifyProductR3L2_realPartL2 (V : ProductC3L2) :
    complexifyProductR3L2 (realPartL2 V) = productRealPartL2 V := by
  apply Lp.ext
  have hc := complexifyProductR3L2_coe_ae (realPartL2 V)
  have hr := realPartL2_coe_ae V
  have hj := productConjL2_coe_ae V
  have hout := Lp.coeFn_smul (1 / 2 : ℝ) (V + productConjL2 V)
  have hadd := Lp.coeFn_add V (productConjL2 V)
  filter_upwards [hc, hr, hj, hout, hadd] with x hc hr hj ho ha
  rw [hc, hr]
  rw [productRealPartL2_apply, ho]
  simp only [Pi.smul_apply]
  rw [ha]
  simp only [Pi.add_apply]
  rw [hj]
  apply PiLp.ext
  intro i
  change ((V x i).re : ℂ) = (1 / 2 : ℝ) •
    (V x i + starRingEnd ℂ (V x i))
  apply Complex.ext
  · simp
    ring
  · simp

/-- Taking the real part twice is the same as taking it once, so `productRealPartL2` is a
projection onto the real fields inside complex product `L²`. -/
theorem productRealPartL2_idempotent (V : ProductC3L2) :
    productRealPartL2 (productRealPartL2 V) = productRealPartL2 V := by
  rw [← complexifyProductR3L2_realPartL2,
    ← complexifyProductR3L2_realPartL2,
    realPartL2_complexifyProductR3L2]

/-! ## Fourier behavior of pointwise conjugation -/

/-- Coordinate extraction commutes with conjugation: the `i`-th coordinate of `conj V` is the
scalar conjugate of the `i`-th coordinate of `V`. -/
theorem productCoordL2_productConjL2 (V : ProductC3L2) (i : Fin 3) :
    productCoordL2 i (productConjL2 V) =
      productScalarConjL2 (productCoordL2 i V) := by
  apply Lp.ext
  have hl := (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
    (productConjL2 V)
  have hr := productScalarConjL2_coe_ae (productCoordL2 i V)
  have hc := productConjL2_coe_ae V
  have hv := (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL V
  filter_upwards [hl, hr, hc, hv] with x hl hr hc hv
  change (((EuclideanSpace.proj (𝕜 := ℂ) i).compLp
      (productConjL2 V) : ProductScalarL2) : ProductTorus3 → ℂ) x =
    ((productScalarConjL2 (productCoordL2 i V) : ProductScalarL2) :
      ProductTorus3 → ℂ) x
  change (((EuclideanSpace.proj (𝕜 := ℂ) i).compLp
      (productConjL2 V) : ProductScalarL2) : ProductTorus3 → ℂ) x =
    (EuclideanSpace.proj (𝕜 := ℂ) i) ((productConjL2 V) x) at hl
  have hv' : ((productCoordL2 i V : ProductScalarL2) :
      ProductTorus3 → ℂ) x = (EuclideanSpace.proj (𝕜 := ℂ) i) (V x) := by
    simpa only [productCoordL2] using hv
  rw [hl, hr, hc, hv']
  rfl

/-- Conjugation reverses a split product Fourier monomial. -/
theorem productScalarConjL2_productMonomialL2
    (n : TransverseFrequency) (k : ℤ) :
    productScalarConjL2 (productMonomialL2 n k) =
      productMonomialL2 (-n) (-k) := by
  apply Lp.ext
  have hconj := productScalarConjL2_coe_ae (productMonomialL2 n k)
  have hmono := scalarAxialLiftL2Fun_ae k (transverseMonomialL2 n)
  have hmonoNeg := scalarAxialLiftL2Fun_ae (-k) (transverseMonomialL2 (-n))
  have htrans := (measurePreserving_fst
    (μ := transverseMeasure) (ν := axialMeasure)).quasiMeasurePreserving.ae_eq_comp
      (transverseMonomialL2_coe_ae n)
  have htransNeg := (measurePreserving_fst
    (μ := transverseMeasure) (ν := axialMeasure)).quasiMeasurePreserving.ae_eq_comp
      (transverseMonomialL2_coe_ae (-n))
  filter_upwards [hconj, hmono, hmonoNeg, htrans, htransNeg] with x hc hm hmn ht htn
  rw [hc]
  change starRingEnd ℂ
      (((scalarAxialLiftL2Fun k (transverseMonomialL2 n) :
        ProductScalarL2) : ProductTorus3 → ℂ) x) =
    (((scalarAxialLiftL2Fun (-k) (transverseMonomialL2 (-n)) :
      ProductScalarL2) : ProductTorus3 → ℂ) x)
  change (transverseMonomialL2 n : TransverseTorus → ℂ) x.1 =
    UnitAddTorus.mFourier n x.1 at ht
  change (transverseMonomialL2 (-n) : TransverseTorus → ℂ) x.1 =
    UnitAddTorus.mFourier (-n) x.1 at htn
  rw [hm, hmn, ht, htn, axialCharacter_neg,
    UnitAddTorus.mFourier_neg]
  simp

/-- Conjugation is an anti-unitary involution on scalar product `L²`: `⟪f, conj g⟫` is the
complex conjugate of `⟪conj f, g⟫`. -/
theorem inner_productScalarConjL2
    (f g : ProductScalarL2) :
    inner ℂ f (productScalarConjL2 g) =
      starRingEnd ℂ (inner ℂ (productScalarConjL2 f) g) := by
  rw [L2.inner_def, L2.inner_def, ← integral_conj]
  apply integral_congr_ae
  have hf := productScalarConjL2_coe_ae f
  have hg := productScalarConjL2_coe_ae g
  filter_upwards [hf, hg] with x hf hg
  rw [hf, hg]
  simp [RCLike.inner_apply]

/-- Pointwise conjugation reverses the Fourier frequencies and conjugates the coefficients: the
`(k, n)` coefficient of `conj f` is the conjugate of the `(-k, -n)` coefficient of `f`. -/
theorem productScalarFourierAnalysisNested_productScalarConjL2
    (f : ProductScalarL2) (k : ℤ) (n : TransverseFrequency) :
    productScalarFourierAnalysisNested (productScalarConjL2 f) k n =
      starRingEnd ℂ (productScalarFourierAnalysisNested f (-k) (-n)) := by
  rw [productScalarFourierAnalysisNested_eq_inner,
    productScalarFourierAnalysisNested_eq_inner,
    inner_productScalarConjL2,
    productScalarConjL2_productMonomialL2]

/-- Vector form of the conjugation/frequency-reversal rule: the `(n, k, i)` coefficient of
`conj V` is the conjugate of the `(-n, -k, i)` coefficient of `V`. -/
theorem productCoeffCLM_productConjL2
    (n : TransverseFrequency) (k : ℤ) (i : Fin 3) (V : ProductC3L2) :
    productCoeffCLM n k i (productConjL2 V) =
      starRingEnd ℂ (productCoeffCLM (-n) (-k) i V) := by
  rw [productCoeffCLM, ContinuousLinearMap.comp_apply,
    productCoordL2_productConjL2]
  change inner ℂ (productMonomialL2 n k)
      (productScalarConjL2 (productCoordL2 i V)) =
    starRingEnd ℂ
      (inner ℂ (productMonomialL2 (-n) (-k)) (productCoordL2 i V))
  rw [← productScalarFourierAnalysisNested_eq_inner,
    productScalarFourierAnalysisNested_productScalarConjL2,
    productScalarFourierAnalysisNested_eq_inner]

/-! ## Conjugation of the weighted product Fourier graph -/

/-- Simultaneous reversal of the axial and transverse frequency indices. -/
def productPairFrequencyNeg :
    (ℤ × TransverseFrequency) ≃ (ℤ × TransverseFrequency) :=
  Equiv.prodCongr (Equiv.neg ℤ) (Equiv.neg TransverseFrequency)

/-- Conjugate a nested scalar coefficient array and reverse all frequencies. -/
def productScalarFourierConj :
    ProductScalarFourierL2 →L[ℝ] ProductScalarFourierL2 := by
  let flatten : ProductScalarFourierL2 →L[ℝ]
      lp (fun _ : ℤ × TransverseFrequency => ℂ) 2 :=
    (scalarL2NestedFlat (I := ℤ) (J := TransverseFrequency)).toContinuousLinearEquiv
      |>.toContinuousLinearMap.restrictScalars ℝ
  let reverse : lp (fun _ : ℤ × TransverseFrequency => ℂ) 2 →L[ℝ]
      lp (fun _ : ℤ × TransverseFrequency => ℂ) 2 :=
    (scalarL2Reindex productPairFrequencyNeg).toContinuousLinearEquiv
      |>.toContinuousLinearMap.restrictScalars ℝ
  let conjugate : lp (fun _ : ℤ × TransverseFrequency => ℂ) 2 →L[ℝ]
      lp (fun _ : ℤ × TransverseFrequency => ℂ) 2 :=
    lp.mapCLM 2
      (fun _ => Complex.conjCLE.toContinuousLinearMap)
      zero_le_one (fun _ => by
        apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        intro z
        simp)
  let unflatten : lp (fun _ : ℤ × TransverseFrequency => ℂ) 2 →L[ℝ]
      ProductScalarFourierL2 :=
    (scalarL2NestedFlat (I := ℤ) (J := TransverseFrequency)).symm.toContinuousLinearEquiv
      |>.toContinuousLinearMap.restrictScalars ℝ
  exact unflatten.comp (conjugate.comp (reverse.comp flatten))

/-- Entrywise description of coefficient conjugation: the `(k, n)` entry of the image is the
conjugate of the `(-k, -n)` entry of the input array. -/
@[simp] theorem productScalarFourierConj_apply
    (a : ProductScalarFourierL2) (k : ℤ) (n : TransverseFrequency) :
    productScalarFourierConj a k n = starRingEnd ℂ (a (-k) (-n)) := by
  rfl

/-- Conjugate and reverse every coordinate of a weighted vector coefficient
array. -/
def productWeightedFourierConj :
    WeightedProductC3Coeffs →L[ℝ] WeightedProductC3Coeffs :=
  (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin 3 => ProductScalarFourierL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : Fin 3 =>
      productScalarFourierConj.comp
        (PiLp.proj 2 (fun _ : Fin 3 => ProductScalarFourierL2) i))

/-- Entrywise description of coefficient conjugation on three-component arrays: the `(i, k, n)`
entry of the image is the conjugate of the `(i, -k, -n)` entry of the input. -/
@[simp] theorem productWeightedFourierConj_apply
    (a : WeightedProductC3Coeffs) (i : Fin 3) (k : ℤ)
    (n : TransverseFrequency) :
    productWeightedFourierConj a i k n =
      starRingEnd ℂ (a i (-k) (-n)) := by
  rfl

/-- Conjugation with frequency reversal is an involution on scalar coefficient arrays. -/
@[simp] theorem productScalarFourierConj_involutive
    (a : ProductScalarFourierL2) :
    productScalarFourierConj (productScalarFourierConj a) = a := by
  apply lp.ext
  funext k
  apply lp.ext
  funext n
  simp

/-- Conjugation with frequency reversal is an involution on three-component coefficient
arrays. -/
@[simp] theorem productWeightedFourierConj_involutive
    (a : WeightedProductC3Coeffs) :
    productWeightedFourierConj (productWeightedFourierConj a) = a := by
  apply PiLp.ext
  intro i
  apply lp.ext
  funext k
  apply lp.ext
  funext n
  simp

/-- The order-two Fourier weight is invariant under reversing both frequencies, which is what
lets conjugation act on the `H²` graph. -/
theorem productH2Weight_neg (n : TransverseFrequency) (k : ℤ) :
    productH2Weight (-n) (-k) = productH2Weight n k := by
  simp [productH2Weight]

/-- Conjugation on product `L²` is conjugate-linear: scaling by `c` before conjugating is scaling
by `conj c` afterwards. -/
theorem productConjL2_smul (c : ℂ) (V : ProductC3L2) :
    productConjL2 (c • V) =
      starRingEnd ℂ c • productConjL2 V := by
  apply Lp.ext
  have hl := productConjL2_coe_ae (c • V)
  have hr := productConjL2_coe_ae V
  have hsmul := Lp.coeFn_smul c V
  have hout := Lp.coeFn_smul (starRingEnd ℂ c) (productConjL2 V)
  filter_upwards [hl, hr, hsmul, hout] with x hl hr hs ho
  rw [hl, ho]
  simp only [Pi.smul_apply]
  rw [hs, hr]
  simp only [Pi.smul_apply]
  apply PiLp.ext
  intro i
  simp

/-- Conjugation of a product `H²` field, including its reversed weighted
Fourier certificate. -/
def productConjH2Fun (B : ProductC3H2) : ProductC3H2 :=
  ⟨(productConjL2 (productH2Embedding B),
      productWeightedFourierConj (productH2WeightedCoeffs B)), by
    rw [mem_productH2Submodule_iff]
    intro n k i
    rw [productWeightedFourierConj_apply,
      productH2WeightedCoeffs_apply,
      productCoeffCLM_productConjL2,
      productH2Weight_neg]
    simp ⟩

/-- Algebraic real-linear conjugation on the product `H²` graph. -/
def productConjH2LinearMap : ProductC3H2 →ₗ[ℝ] ProductC3H2 where
  toFun := productConjH2Fun
  map_add' B C := by
    apply Subtype.ext
    apply Prod.ext
    · simp [productConjH2Fun]
    · simp [productConjH2Fun]
  map_smul' r B := by
    apply Subtype.ext
    apply Prod.ext
    · simp [productConjH2Fun]
    · simp [productConjH2Fun]

/-- The ambient product map underlying `productConjH2`. -/
def productConjH2Ambient :
    (ProductC3L2 × WeightedProductC3Coeffs) →L[ℝ]
      (ProductC3L2 × WeightedProductC3Coeffs) :=
  (productConjL2.comp
      (ContinuousLinearMap.fst ℝ ProductC3L2 WeightedProductC3Coeffs)).prod
    (productWeightedFourierConj.comp
      (ContinuousLinearMap.snd ℝ ProductC3L2 WeightedProductC3Coeffs))

/-- Continuous real-linear conjugation on the complete product `H²` graph. -/
def productConjH2 : ProductC3H2 →L[ℝ] ProductC3H2 :=
  productConjH2LinearMap.mkContinuous ‖productConjH2Ambient‖ (by
    intro B
    change ‖productConjH2Ambient B.1‖ ≤ ‖productConjH2Ambient‖ * ‖B‖
    exact productConjH2Ambient.le_opNorm B.1)

/-- Conjugation on the `H²` graph is compatible with the graph embedding: the physical field of
`conj B` is the conjugate of the physical field of `B`. -/
theorem productH2Embedding_productConjH2 (B : ProductC3H2) :
    productH2Embedding (productConjH2 B) =
      productConjL2 (productH2Embedding B) :=
  rfl

/-- Conjugation on the `H²` graph acts on the stored coefficient certificate by conjugation with
frequency reversal. -/
@[simp] theorem productH2WeightedCoeffs_productConjH2 (B : ProductC3H2) :
    productH2WeightedCoeffs (productConjH2 B) =
      productWeightedFourierConj (productH2WeightedCoeffs B) :=
  rfl

/-- Conjugation on the product `H²` graph is an involution. -/
@[simp] theorem productConjH2_involutive (B : ProductC3H2) :
    productConjH2 (productConjH2 B) = B := by
  apply Subtype.ext
  apply Prod.ext
  · change productConjL2 (productConjL2 (productH2Embedding B)) =
      productH2Embedding B
    exact productConjL2_involutive _
  · change productWeightedFourierConj
        (productWeightedFourierConj (productH2WeightedCoeffs B)) =
      productH2WeightedCoeffs B
    exact productWeightedFourierConj_involutive _

/-! ## Real projection on `H²` -/

/-- Real-part projection on the product `H²` graph, represented inside the
complex graph as `(B + conj B) / 2`. -/
def productRealPartH2 : ProductC3H2 →L[ℝ] ProductC3H2 :=
  (1 / 2 : ℝ) •
    ((ContinuousLinearMap.id ℝ ProductC3H2) + productConjH2)

/-- The real-part projection on the `H²` graph acts as `B ↦ (B + conj B)/2`. -/
theorem productRealPartH2_apply (B : ProductC3H2) :
    productRealPartH2 B = (1 / 2 : ℝ) • (B + productConjH2 B) :=
  rfl

/-- The real-part projection commutes with the graph embedding: the physical field of the real
part of `B` is the real part of the physical field of `B`. -/
theorem productH2Embedding_productRealPartH2 (B : ProductC3H2) :
    productH2Embedding (productRealPartH2 B) =
      productRealPartL2 (productH2Embedding B) := by
  change productH2Embedding
      (((1 / 2 : ℝ) : ℂ) • (B + productConjH2 B)) =
    ((1 / 2 : ℝ) : ℂ) •
      (productH2Embedding B + productConjL2 (productH2Embedding B))
  rw [map_smul, map_add, productH2Embedding_productConjH2]

/-- The real-part map on the product `H²` graph is idempotent, hence a projection onto the real
fields of the graph. -/
@[simp] theorem productRealPartH2_idempotent (B : ProductC3H2) :
    productRealPartH2 (productRealPartH2 B) = productRealPartH2 B := by
  apply productH2Embedding_injective
  rw [productH2Embedding_productRealPartH2,
    productH2Embedding_productRealPartH2,
    productRealPartL2_idempotent]

/-! ## Divergence under conjugation and real projection -/

/-- Divergence commutes with conjugation: `div (conj B)` is the scalar conjugate of `div B`. -/
theorem productDivergenceFromH2_productConjH2 (B : ProductC3H2) :
    productDivergenceFromH2 (productConjH2 B) =
      productScalarConjL2 (productDivergenceFromH2 B) := by
  apply productScalarL2_ext_coeff
  intro n k
  change productScalarCoeffCLM n k
      (productDivergenceFromH2 (productConjH2 B)) =
    productScalarCoeffCLM n k
      (productScalarConjL2 (productDivergenceFromH2 B))
  rw [productScalarCoeffCLM_productDivergenceFromH2]
  change _ = inner ℂ (productMonomialL2 n k)
    (productScalarConjL2 (productDivergenceFromH2 B))
  rw [inner_productScalarConjL2,
    productScalarConjL2_productMonomialL2]
  change _ = starRingEnd ℂ
    (productScalarCoeffCLM (-n) (-k) (productDivergenceFromH2 B))
  rw [productScalarCoeffCLM_productDivergenceFromH2]
  simp only [productH2Embedding_productConjH2,
    productCoeffCLM_productConjL2, Fin.sum_univ_two]
  simp [Complex.conj_I, map_ofNat]

/-- The complex-valued realization of scalar real part. -/
def productScalarRealPartL2 : ProductScalarL2 →L[ℝ] ProductScalarL2 :=
  (1 / 2 : ℝ) •
    ((ContinuousLinearMap.id ℝ ProductScalarL2) + productScalarConjL2)

/-- Divergence commutes with the real-part projection: `div (Re B)` is the scalar real part of
`div B`. -/
theorem productDivergenceFromH2_productRealPartH2 (B : ProductC3H2) :
    productDivergenceFromH2 (productRealPartH2 B) =
      productScalarRealPartL2 (productDivergenceFromH2 B) := by
  change productDivergenceFromH2
      (((1 / 2 : ℝ) : ℂ) • (B + productConjH2 B)) =
    ((1 / 2 : ℝ) : ℂ) •
      (productDivergenceFromH2 B +
        productScalarConjL2 (productDivergenceFromH2 B))
  rw [map_smul, map_add, productDivergenceFromH2_productConjH2]

/-- The real part of a divergence-free `H²` field is divergence-free.  This is what keeps the
real datum `B_in^ε = Re V^ε` of the proof of Paper Theorem 1.2 (`thm:main`, Section 8) inside the
solenoidal space. -/
theorem productRealPartH2_preserves_divergenceFree {B : ProductC3H2}
    (hB : productDivergenceFromH2 B = 0) :
    productDivergenceFromH2 (productRealPartH2 B) = 0 := by
  rw [productDivergenceFromH2_productRealPartH2, hB, map_zero]

end

end FastDynamo
