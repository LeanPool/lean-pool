/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Fourier.PeriodicH2
public import LeanPool.FastDynamo.Fourier.PeriodicH2AxialSector

/-!
# Fourier-graph periodic `H²` on the split product torus

This module defines the product-frequency coefficient functionals and the
closed Fourier graph for `H²(T² × T¹; ℂ³)`.  It then proves that multiplication
by the axial character of any integer frequency `K` sends the transverse
Fourier-graph `H²` continuously and injectively into the product graph.

The proof records the exact coefficient support `k = K` and the graph-norm
bound `1 + (2πK)²`.  Identifying these Fourier-graph spaces with an independently
defined distributional Sobolev space is not attempted here.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-- Scalar complex `L²` fields on the product model of the three-torus. -/
abbrev ProductScalarL2 := Lp ℂ 2 productMeasure

/-- Pull back a transverse scalar `L²` field along the product projection. -/
def pullTransverseScalarL2 : TransverseScalarL2 →ₗᵢ[ℂ] ProductScalarL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ Prod.fst measurePreserving_fst

/-- Unbundled fixed-frequency axial lift for scalar `L²` fields. -/
def scalarAxialLiftL2Fun (K : ℤ) (f : TransverseScalarL2) : ProductScalarL2 :=
  (productAxialCharacterLInf K • pullTransverseScalarL2 f : ProductScalarL2)

/--
A representative of the scalar axial lift is given almost everywhere by
`(y, x₃) ↦ e^{2π i K x₃} f(y)`.
-/
lemma scalarAxialLiftL2Fun_ae (K : ℤ) (f : TransverseScalarL2) :
    (scalarAxialLiftL2Fun K f : ProductTorus3 → ℂ) =ᵐ[productMeasure]
      fun x => axialCharacter K x.2 * f x.1 := by
  have hmul := Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
    (productAxialCharacterLInf K) (pullTransverseScalarL2 f)
  have hchar := ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ)
    productMeasure (productAxialCharacter K)
  have hpull := Lp.coeFn_compMeasurePreserving f
    (measurePreserving_fst (μ := transverseMeasure) (ν := axialMeasure))
  filter_upwards [hmul, hchar, hpull] with x hx hχ hf
  change ((productAxialCharacterLInf K • pullTransverseScalarL2 f : ProductScalarL2) :
    ProductTorus3 → ℂ) x = _
  rw [hx]
  change (productAxialCharacterLInf K : ProductTorus3 → ℂ) x *
    (pullTransverseScalarL2 f : ProductTorus3 → ℂ) x = _
  change (productAxialCharacterLInf K : ProductTorus3 → ℂ) x =
    axialCharacter K x.2 at hχ
  change (pullTransverseScalarL2 f : ProductTorus3 → ℂ) x = f x.1 at hf
  rw [hχ, hf]

/--
The scalar axial lift preserves the `L²` norm, since the axial character has modulus one and
pullback along the measure-preserving projection is isometric.
-/
lemma norm_scalarAxialLiftL2Fun (K : ℤ) (f : TransverseScalarL2) :
    ‖scalarAxialLiftL2Fun K f‖ = ‖f‖ := by
  calc
    ‖scalarAxialLiftL2Fun K f‖ = ‖pullTransverseScalarL2 f‖ := by
      rw [Lp.norm_def, Lp.norm_def]
      congr 1
      apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
      have hpull := Lp.coeFn_compMeasurePreserving f
        (measurePreserving_fst (μ := transverseMeasure) (ν := axialMeasure))
      filter_upwards [scalarAxialLiftL2Fun_ae K f, hpull] with x hx hp
      change (pullTransverseScalarL2 f : ProductTorus3 → ℂ) x = f x.1 at hp
      rw [hx, hp, norm_mul, norm_axialCharacter, one_mul]
    _ = ‖f‖ := pullTransverseScalarL2.norm_map f

/-- Scalar axial Fourier lift as a complex linear isometry. -/
def scalarAxialLiftL2 (K : ℤ) : TransverseScalarL2 →ₗᵢ[ℂ] ProductScalarL2 where
  toFun := scalarAxialLiftL2Fun K
  map_add' f g := by
    simp only [scalarAxialLiftL2Fun, map_add]
    exact Lp.add_smul (productAxialCharacterLInf K)
      (pullTransverseScalarL2 f) (pullTransverseScalarL2 g)
  map_smul' c f := by
    simp only [scalarAxialLiftL2Fun, map_smul]
    simpa only [RingHom.id_apply] using
      (Lp.smul_comm (p := ∞) (q := 2) (r := 2) c
        (productAxialCharacterLInf K) (pullTransverseScalarL2 f)).symm
  norm_map' := norm_scalarAxialLiftL2Fun K

/--
Distinct axial sectors are orthogonal: the inner product of two scalar axial lifts is the
transverse inner product when `k = K` and zero otherwise. This is Fubini together with
orthonormality of the circle characters.
-/
theorem inner_scalarAxialLiftL2 (k K : ℤ)
    (f g : TransverseScalarL2) :
    inner ℂ (scalarAxialLiftL2 k f) (scalarAxialLiftL2 K g) =
      if k = K then inner ℂ f g else 0 := by
  have haxial :
      ∫ x : AxialCircle, starRingEnd ℂ (axialCharacter k x) * axialCharacter K x
        ∂axialMeasure = if k = K then 1 else 0 := by
    have h := (orthonormal_iff_ite.mp
      (orthonormal_fourier (T := (1 : ℝ)))) k K
    simpa [MeasureTheory.ContinuousMap.inner_toLp, axialCharacter, mul_comm] using h
  rw [MeasureTheory.L2.inner_def]
  have hpoint :
      (fun x : ProductTorus3 =>
        inner ℂ ((scalarAxialLiftL2 k f : ProductScalarL2) x)
          ((scalarAxialLiftL2 K g : ProductScalarL2) x)) =ᵐ[productMeasure]
      fun x => (starRingEnd ℂ (f x.1) * g x.1) *
        (starRingEnd ℂ (axialCharacter k x.2) * axialCharacter K x.2) := by
    filter_upwards [scalarAxialLiftL2Fun_ae k f,
      scalarAxialLiftL2Fun_ae K g] with x hf hg
    change inner ℂ ((scalarAxialLiftL2Fun k f : ProductScalarL2) x)
      ((scalarAxialLiftL2Fun K g : ProductScalarL2) x) = _
    rw [hf, hg]
    simp only [RCLike.inner_apply, map_mul]
    ring
  rw [integral_congr_ae hpoint]
  change
    ∫ x : TransverseTorus × AxialCircle,
      ((starRingEnd ℂ (f x.1) * g x.1) *
        (starRingEnd ℂ (axialCharacter k x.2) * axialCharacter K x.2))
      ∂transverseMeasure.prod axialMeasure = _
  calc
    (∫ x : TransverseTorus × AxialCircle,
        ((starRingEnd ℂ (f x.1) * g x.1) *
          (starRingEnd ℂ (axialCharacter k x.2) * axialCharacter K x.2))
        ∂transverseMeasure.prod axialMeasure) =
        (∫ y : TransverseTorus, starRingEnd ℂ (f y) * g y ∂transverseMeasure) *
          ∫ x : AxialCircle,
            starRingEnd ℂ (axialCharacter k x) * axialCharacter K x ∂axialMeasure := by
      exact integral_prod_mul
        (fun y : TransverseTorus => starRingEnd ℂ (f y) * g y)
        (fun x : AxialCircle =>
          starRingEnd ℂ (axialCharacter k x) * axialCharacter K x)
    _ = if k = K then inner ℂ f g else 0 := by
      have htrans :
          (∫ y : TransverseTorus, starRingEnd ℂ (f y) * g y
            ∂transverseMeasure) = inner ℂ f g := by
        rw [MeasureTheory.L2.inner_def]
        apply integral_congr_ae
        filter_upwards with y
        simp only [RCLike.inner_apply, mul_comm]
      rw [haxial, htrans]
      split_ifs <;> simp

/-- Extract one scalar coordinate from a complex vector-valued product `L²` field. -/
def productCoordL2 (i : Fin 3) :
    ProductC3L2 →L[ℂ] ProductScalarL2 :=
  (EuclideanSpace.proj i).compLpL 2 productMeasure

/--
Taking the `i`-th component commutes with the axial lift: the `i`-th coordinate of a lifted
vector field is the scalar axial lift of the `i`-th coordinate of the amplitude.
-/
theorem productCoordL2_axialLiftL2 (K : ℤ)
    (b : TransverseC3L2) (i : Fin 3) :
    productCoordL2 i (axialLiftL2 K b) =
      scalarAxialLiftL2 K (transverseCoordL2 i b) := by
  apply Lp.ext
  have hfull := (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
    (axialLiftL2 K b)
  have hlift := axialLiftL2_coe_ae K b
  have hscalar := scalarAxialLiftL2Fun_ae K (transverseCoordL2 i b)
  have htrans := (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL b
  have htransProd :=
    (measurePreserving_fst (μ := transverseMeasure) (ν := axialMeasure)).quasiMeasurePreserving
      |>.ae_eq_comp htrans
  filter_upwards [hfull, hlift, hscalar, htransProd] with x hf hl hs ht
  change (((EuclideanSpace.proj (𝕜 := ℂ) i).compLp
    (axialLiftL2 K b) : ProductScalarL2) : ProductTorus3 → ℂ) x = _
  change ((transverseCoordL2 i b : TransverseScalarL2) :
    TransverseTorus → ℂ) x.1 =
      (EuclideanSpace.proj (𝕜 := ℂ) i) (b x.1) at ht
  change (((EuclideanSpace.proj (𝕜 := ℂ) i).compLp
    (axialLiftL2 K b) : ProductScalarL2) : ProductTorus3 → ℂ) x = _ at hf
  change ((scalarAxialLiftL2Fun K (transverseCoordL2 i b) :
    ProductScalarL2) : ProductTorus3 → ℂ) x = _ at hs
  calc
    (((EuclideanSpace.proj (𝕜 := ℂ) i).compLp
      (axialLiftL2 K b) : ProductScalarL2) : ProductTorus3 → ℂ) x =
        (EuclideanSpace.proj (𝕜 := ℂ) i) ((axialLiftL2 K b) x) := hf
    _ = (EuclideanSpace.proj (𝕜 := ℂ) i)
        (axialCharacter K x.2 • b x.1) := by rw [hl]
    _ = axialCharacter K x.2 *
        (EuclideanSpace.proj (𝕜 := ℂ) i) (b x.1) := by
      exact map_smul (EuclideanSpace.proj (𝕜 := ℂ) i)
        (axialCharacter K x.2) (b x.1)
    _ = axialCharacter K x.2 * (transverseCoordL2 i b) x.1 := by rw [ht]
    _ = ((scalarAxialLiftL2Fun K (transverseCoordL2 i b) :
        ProductScalarL2) : ProductTorus3 → ℂ) x := hs.symm

/-- Nested square-summable scalar Fourier coefficients indexed by axial and transverse frequency. -/
abbrev ProductScalarFourierL2 :=
  lp (fun _ : ℤ => TransverseScalarFourierL2) 2

/-- The normalized scalar product-torus Fourier monomial at frequency `(n, k)`. -/
def productMonomialL2 (n : TransverseFrequency) (k : ℤ) : ProductScalarL2 :=
  scalarAxialLiftL2 k (transverseMonomialL2 n)

/-- Extract one coordinate Fourier coefficient of a product-torus vector field. -/
def productCoeffCLM (n : TransverseFrequency) (k : ℤ) (i : Fin 3) :
    ProductC3L2 →L[ℂ] ℂ :=
  (innerSL ℂ (productMonomialL2 n k)).comp (productCoordL2 i)

/--
The Fourier coefficients of an axial lift are supported on the single axial frequency `K`, where
they equal the transverse Fourier coefficients of the amplitude.
-/
theorem productCoeffCLM_axialLiftL2 (n : TransverseFrequency)
    (k K : ℤ) (i : Fin 3) (b : TransverseC3L2) :
    productCoeffCLM n k i (axialLiftL2 K b) =
      if k = K then transverseCoeffCLM n i b else 0 := by
  rw [productCoeffCLM, ContinuousLinearMap.comp_apply,
    productCoordL2_axialLiftL2]
  change inner ℂ
    (scalarAxialLiftL2 k (transverseMonomialL2 n))
    (scalarAxialLiftL2 K (transverseCoordL2 i b)) = _
  rw [inner_scalarAxialLiftL2]
  by_cases hk : k = K
  · simp only [hk, ite_true]
    rw [transverseCoeffCLM, ContinuousLinearMap.comp_apply,
      transverseScalarCoeffCLM_eq_inner]
  · simp [hk]

/-! ## Weighted product coefficients and fixed-sector insertion -/

/-- Weighted product-frequency coefficient arrays for three complex components. -/
abbrev WeightedProductC3Coeffs :=
  PiLp 2 (fun _ : Fin 3 => ProductScalarFourierL2)

/-- The inhomogeneous order-two Fourier weight on the product torus. -/
def productH2Weight (n : TransverseFrequency) (k : ℤ) : ℝ :=
  1 + (2 * Real.pi) ^ 2 *
    ((∑ j, (n j : ℝ) ^ 2) + (k : ℝ) ^ 2)

/-- A convenient uniform bound for insertion into the fixed axial sector `K`. -/
def fixedKWeightBound (K : ℤ) : ℝ :=
  1 + (2 * Real.pi * (K : ℝ)) ^ 2

/--
The product order-two weight splits as the transverse weight plus the axial contribution
`(2πk)²`.
-/
lemma productH2Weight_eq_transverse_add (n : TransverseFrequency) (k : ℤ) :
    productH2Weight n k =
      transverseH2Weight n + (2 * Real.pi * (k : ℝ)) ^ 2 := by
  unfold productH2Weight transverseH2Weight transverseFrequencyEnergy
  ring

/-- The fixed-sector weight bound `1 + (2πK)²` is at least one. -/
lemma one_le_fixedKWeightBound (K : ℤ) :
    1 ≤ fixedKWeightBound K := by
  unfold fixedKWeightBound
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The fixed-sector weight bound is nonnegative, as required to use it as an operator-norm
bound. -/
lemma fixedKWeightBound_nonneg (K : ℤ) :
    0 ≤ fixedKWeightBound K :=
  zero_le_one.trans (one_le_fixedKWeightBound K)

/-- The ratio converting stored transverse `H²` coefficients into full `H²` coefficients. -/
def fixedKWeightRatio (K : ℤ) (n : TransverseFrequency) : ℂ :=
  (productH2Weight n K : ℂ) / (transverseH2Weight n : ℂ)

/--
The ratio of the product weight at `(n, K)` to the transverse weight at `n` is bounded uniformly
in `n` by `fixedKWeightBound K = 1 + (2πK)²`; this uses `1 ≤ transverseH2Weight n`.
-/
lemma norm_fixedKWeightRatio_le (K : ℤ) (n : TransverseFrequency) :
    ‖fixedKWeightRatio K n‖ ≤ fixedKWeightBound K := by
  rw [fixedKWeightRatio, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (transverseH2Weight_pos n)]
  have hp : 0 < productH2Weight n K := by
    rw [productH2Weight_eq_transverse_add]
    exact add_pos_of_pos_of_nonneg (transverseH2Weight_pos n) (sq_nonneg _)
  rw [abs_of_pos hp]
  apply (div_le_iff₀ (transverseH2Weight_pos n)).2
  rw [productH2Weight_eq_transverse_add]
  have hw : 1 ≤ transverseH2Weight n := one_le_transverseH2Weight n
  have hc : 0 ≤ (2 * Real.pi * (K : ℝ)) ^ 2 := sq_nonneg _
  unfold fixedKWeightBound
  nlinarith [mul_nonneg hc (sub_nonneg.mpr hw)]

/-- Multiply transverse weighted coefficients by the fixed-sector weight ratio. -/
def fixedKRatioCoeffMap (K : ℤ) :
    TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2 :=
  lp.mapCLM 2
    (fun n => (ContinuousLinearMap.lsmul ℂ ℂ) (fixedKWeightRatio K n))
    (fixedKWeightBound_nonneg K)
    (fun n => (ContinuousLinearMap.opNorm_lsmul_apply_le
      (E := ℂ) (fixedKWeightRatio K n)).trans
        (norm_fixedKWeightRatio_le K n))

/--
The weight-ratio coefficient map acts diagonally, multiplying the `n`-th coefficient by
`fixedKWeightRatio K n`.
-/
@[simp] lemma fixedKRatioCoeffMap_apply (K : ℤ)
    (a : TransverseScalarFourierL2) (n : TransverseFrequency) :
    fixedKRatioCoeffMap K a n = fixedKWeightRatio K n * a n :=
  rfl

/-- The weight-ratio coefficient map has operator norm at most `fixedKWeightBound K`. -/
lemma norm_fixedKRatioCoeffMap_le (K : ℤ) :
    ‖fixedKRatioCoeffMap K‖ ≤ fixedKWeightBound K := by
  exact lp.norm_mapCLM_le 2 _ (fixedKWeightBound_nonneg K)
    (fun n => (ContinuousLinearMap.opNorm_lsmul_apply_le
      (E := ℂ) (fixedKWeightRatio K n)).trans
        (norm_fixedKWeightRatio_le K n))

/-- Insert converted scalar coefficients at the axial frequency `K`. -/
def fixedKScalarWeightedLift (K : ℤ) :
    TransverseScalarFourierL2 →L[ℂ] ProductScalarFourierL2 :=
  (lp.singleContinuousLinearMap ℂ
    (fun _ : ℤ => TransverseScalarFourierL2) 2 K).comp
      (fixedKRatioCoeffMap K)

/--
The scalar weighted lift places the converted coefficients at the single axial frequency `K` and
zero at every other axial frequency.
-/
theorem fixedKScalarWeightedLift_apply (K k : ℤ)
    (a : TransverseScalarFourierL2) (n : TransverseFrequency) :
    fixedKScalarWeightedLift K a k n =
      if k = K then fixedKWeightRatio K n * a n else 0 := by
  by_cases hk : k = K
  · subst k
    simp [fixedKScalarWeightedLift]
  · simp [fixedKScalarWeightedLift, hk]

/--
The scalar weighted lift has operator norm at most `fixedKWeightBound K`: insertion at one
frequency is a `ℓ²` isometry onto its range, and the ratio map contributes the bound.
-/
lemma norm_fixedKScalarWeightedLift_le (K : ℤ) :
    ‖fixedKScalarWeightedLift K‖ ≤ fixedKWeightBound K := by
  let insert : TransverseScalarFourierL2 →L[ℂ] ProductScalarFourierL2 :=
    lp.singleContinuousLinearMap ℂ
      (fun _ : ℤ => TransverseScalarFourierL2) 2 K
  have hinsert : ‖insert‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro a
    rw [show insert a = lp.single 2 K a by rfl,
      lp.norm_single (by norm_num)]
    simp
  calc
    ‖fixedKScalarWeightedLift K‖ =
        ‖insert.comp (fixedKRatioCoeffMap K)‖ := by rfl
    _ ≤ ‖insert‖ * ‖fixedKRatioCoeffMap K‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * fixedKWeightBound K := by
      exact mul_le_mul hinsert (norm_fixedKRatioCoeffMap_le K)
        (norm_nonneg _) zero_le_one
    _ = fixedKWeightBound K := one_mul _

/-- Coordinatewise fixed-`K` insertion as an algebraic linear map. -/
def fixedKWeightedLiftLinearMap (K : ℤ) :
    WeightedTransverseC3Coeffs →ₗ[ℂ] WeightedProductC3Coeffs where
  toFun a := WithLp.toLp 2 (fun i => fixedKScalarWeightedLift K (a i))
  map_add' a b := by
    apply PiLp.ext
    intro i
    simp
  map_smul' c a := by
    apply PiLp.ext
    intro i
    simp

/-- The three-component weighted lift acts on each component by the scalar weighted lift. -/
@[simp] lemma fixedKWeightedLiftLinearMap_apply (K : ℤ)
    (a : WeightedTransverseC3Coeffs) (i : Fin 3) :
    fixedKWeightedLiftLinearMap K a i = fixedKScalarWeightedLift K (a i) :=
  rfl

/--
The three-component weighted lift satisfies the pointwise bound `‖·‖ ≤ fixedKWeightBound K * ‖a‖`,
obtained by summing the componentwise bounds in the `PiLp 2` norm.
-/
lemma norm_fixedKWeightedLiftLinearMap_apply_le (K : ℤ)
    (a : WeightedTransverseC3Coeffs) :
    ‖fixedKWeightedLiftLinearMap K a‖ ≤ fixedKWeightBound K * ‖a‖ := by
  have hcomponent : ∀ i : Fin 3,
      ‖fixedKScalarWeightedLift K (a i)‖ ≤ fixedKWeightBound K * ‖a i‖ :=
    fun i => (fixedKScalarWeightedLift K).le_of_opNorm_le
      (norm_fixedKScalarWeightedLift_le K) (a i)
  have hsquares :
      ‖fixedKWeightedLiftLinearMap K a‖ ^ 2 ≤
        (fixedKWeightBound K * ‖a‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      ∑ i : Fin 3, ‖(fixedKWeightedLiftLinearMap K a) i‖ ^ 2 ≤
          ∑ i : Fin 3, (fixedKWeightBound K * ‖a i‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact pow_le_pow_left₀ (norm_nonneg _) (hcomponent i) 2
      _ = fixedKWeightBound K ^ 2 *
          ∑ i : Fin 3, ‖a i‖ ^ 2 := by
        simp_rw [mul_pow]
        rw [Finset.mul_sum]
      _ = fixedKWeightBound K ^ 2 * ‖a‖ ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2]
      _ = (fixedKWeightBound K * ‖a‖) ^ 2 := by ring
  have hout : 0 ≤ ‖fixedKWeightedLiftLinearMap K a‖ := norm_nonneg _
  have hrhs : 0 ≤ fixedKWeightBound K * ‖a‖ :=
    mul_nonneg (fixedKWeightBound_nonneg K) (norm_nonneg _)
  nlinarith

/-- The bounded fixed-`K` insertion on three-component weighted coefficients. -/
def fixedKWeightedLift (K : ℤ) :
    WeightedTransverseC3Coeffs →L[ℂ] WeightedProductC3Coeffs :=
  (fixedKWeightedLiftLinearMap K).mkContinuous
    (fixedKWeightBound K) (norm_fixedKWeightedLiftLinearMap_apply_le K)

/--
Entrywise formula for the bounded weighted lift: the entry at axial frequency `k`, transverse
frequency `n` and component `i` is `fixedKWeightRatio K n * (a i) n` if `k = K`, else zero.
-/
@[simp] theorem fixedKWeightedLift_apply (K : ℤ)
    (a : WeightedTransverseC3Coeffs) (i : Fin 3) (k : ℤ)
    (n : TransverseFrequency) :
    fixedKWeightedLift K a i k n =
      if k = K then fixedKWeightRatio K n * (a i) n else 0 := by
  change fixedKScalarWeightedLift K (a i) k n = _
  exact fixedKScalarWeightedLift_apply K k (a i) n

/--
On its support `k = K`, the weighted lift multiplies the stored transverse coefficient by the
weight ratio.
-/
theorem fixedKWeightedLift_at_K (K : ℤ)
    (a : WeightedTransverseC3Coeffs) (i : Fin 3)
    (n : TransverseFrequency) :
    fixedKWeightedLift K a i K n =
      fixedKWeightRatio K n * (a i) n := by
  simp

/--
Multiplying the weight ratio by the transverse weight recovers the product weight at `(n, K)`;
this is what makes the lifted certificate satisfy the product graph equation.
-/
theorem fixedKWeightRatio_mul_transverseWeight (K : ℤ)
    (n : TransverseFrequency) :
    fixedKWeightRatio K n * (transverseH2Weight n : ℂ) =
      (productH2Weight n K : ℂ) := by
  unfold fixedKWeightRatio
  have hw : (transverseH2Weight n : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (transverseH2Weight_pos n))
  exact div_mul_cancel₀ _ hw

/--
If the transverse certificate satisfies the transverse graph equation at `n` with physical
coefficient `bhat`, then the lifted certificate satisfies the product graph equation at `(n, K)`
with the same physical coefficient.
-/
theorem fixedKWeightedLift_graph_at_K (K : ℤ)
    (a : WeightedTransverseC3Coeffs) (i : Fin 3)
    (n : TransverseFrequency) (bhat : ℂ)
    (ha : (a i) n = (transverseH2Weight n : ℂ) * bhat) :
    fixedKWeightedLift K a i K n =
      (productH2Weight n K : ℂ) * bhat := by
  rw [fixedKWeightedLift_at_K, ha, ← mul_assoc,
    fixedKWeightRatio_mul_transverseWeight]

/-- The lifted certificate vanishes at every axial frequency other than `K`. -/
theorem fixedKWeightedLift_off_support (K k : ℤ)
    (hk : k ≠ K) (a : WeightedTransverseC3Coeffs) (i : Fin 3)
    (n : TransverseFrequency) :
    fixedKWeightedLift K a i k n = 0 := by
  simp [fixedKWeightedLift_apply, hk]

/-- The bounded weighted lift has operator norm at most `fixedKWeightBound K`. -/
theorem norm_fixedKWeightedLift_le (K : ℤ) :
    ‖fixedKWeightedLift K‖ ≤ fixedKWeightBound K := by
  exact LinearMap.mkContinuous_norm_le _ (fixedKWeightBound_nonneg K)
    (norm_fixedKWeightedLiftLinearMap_apply_le K)

/-! ## The closed product `H²` graph -/

/-- Read one entry of a weighted product Fourier-coefficient array. -/
def weightedProductCoeffCLM (n : TransverseFrequency) (k : ℤ) (i : Fin 3) :
    WeightedProductC3Coeffs →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : TransverseFrequency => ℂ) 2 n).comp
    ((lp.evalCLM ℂ (fun _ : ℤ => TransverseScalarFourierL2) 2 k).comp
      (PiLp.proj 2 (fun _ : Fin 3 => ProductScalarFourierL2) i))

/-- The graph equation `aᵢ(n,k) = w₃(n,k) * V̂ᵢ(n,k)`. -/
def productH2Constraint (n : TransverseFrequency) (k : ℤ) (i : Fin 3) :
    (ProductC3L2 × WeightedProductC3Coeffs) →L[ℂ] ℂ :=
  (weightedProductCoeffCLM n k i).comp
      (ContinuousLinearMap.snd ℂ ProductC3L2 WeightedProductC3Coeffs) -
    (productH2Weight n k : ℂ) •
      (productCoeffCLM n k i).comp
        (ContinuousLinearMap.fst ℂ ProductC3L2 WeightedProductC3Coeffs)

/-- Closed Fourier-graph realization of periodic vector-valued `H²(T² × T¹)`. -/
def productH2Submodule :
    Submodule ℂ (ProductC3L2 × WeightedProductC3Coeffs) :=
  ⨅ n, ⨅ k, ⨅ i, (productH2Constraint n k i).ker

/--
A pair `(V, a)` lies in the product `H²` graph exactly when the graph equation
`aᵢ(n,k) = (1 + 4π²(|n|² + k²)) V̂ᵢ(n,k)` holds at every product frequency and component.
-/
theorem mem_productH2Submodule_iff (V : ProductC3L2)
    (a : WeightedProductC3Coeffs) :
    (V, a) ∈ productH2Submodule ↔
      ∀ n k i, (a i k) n =
        (productH2Weight n k : ℂ) * productCoeffCLM n k i V := by
  constructor
  · intro h n k i
    have hker : (V, a) ∈ (productH2Constraint n k i).ker :=
      (Submodule.mem_iInf _).mp
        ((Submodule.mem_iInf _).mp
          ((Submodule.mem_iInf _).mp h n) k) i
    change (a i k) n -
      (productH2Weight n k : ℂ) * productCoeffCLM n k i V = 0 at hker
    exact sub_eq_zero.mp hker
  · intro h
    rw [productH2Submodule, Submodule.mem_iInf]
    intro n
    rw [Submodule.mem_iInf]
    intro k
    rw [Submodule.mem_iInf]
    intro i
    change (a i k) n -
      (productH2Weight n k : ℂ) * productCoeffCLM n k i V = 0
    exact sub_eq_zero.mpr (h n k i)

/--
The product `H²` graph is closed, being an intersection of kernels of the continuous constraint
functionals `productH2Constraint`.
-/
lemma isClosed_productH2Submodule :
    IsClosed (productH2Submodule :
      Set (ProductC3L2 × WeightedProductC3Coeffs)) := by
  simpa only [productH2Submodule, Submodule.coe_iInf] using
    (isClosed_iInter fun n =>
      isClosed_iInter fun k =>
        isClosed_iInter fun i => (productH2Constraint n k i).isClosed_ker)

/-- The Fourier-graph model for periodic complex vector-valued `H²` on the product torus. -/
abbrev ProductC3H2 := productH2Submodule

/--
The product `H²` graph is complete, inherited from closedness inside
`ProductC3L2 × WeightedProductC3Coeffs`; this is what gives `ProductC3H2` a Banach
structure rather than the incomplete `L²` norm.
-/
instance : CompleteSpace ProductC3H2 :=
  isClosed_productH2Submodule.isComplete.completeSpace_coe

/-- Forget the weighted product coefficient certificate. -/
def productH2Embedding : ProductC3H2 →L[ℂ] ProductC3L2 :=
  (ContinuousLinearMap.fst ℂ ProductC3L2 WeightedProductC3Coeffs).domRestrict
    productH2Submodule

/-- The product `H²`-to-`L²` embedding is the first projection: it returns the stored physical
field. -/
@[simp] theorem productH2Embedding_apply (V : ProductC3H2) :
    productH2Embedding V = V.1.1 :=
  rfl

/-- Read the weighted coefficient certificate from a product `H²` field. -/
def productH2WeightedCoeffs :
    ProductC3H2 →L[ℂ] WeightedProductC3Coeffs :=
  (ContinuousLinearMap.snd ℂ ProductC3L2 WeightedProductC3Coeffs).domRestrict
    productH2Submodule

/--
The stored certificate of a product `H²` element is the product weight times the physical Fourier
coefficient at the same frequency and component.
-/
theorem productH2WeightedCoeffs_apply (V : ProductC3H2)
    (n : TransverseFrequency) (k : ℤ) (i : Fin 3) :
    (productH2WeightedCoeffs V i k) n =
      (productH2Weight n k : ℂ) *
        productCoeffCLM n k i (productH2Embedding V) := by
  exact (mem_productH2Submodule_iff V.1.1 V.1.2).mp V.2 n k i

/-- The physical product `L²` field uniquely determines its weighted certificate. -/
theorem productH2Embedding_injective :
    Function.Injective productH2Embedding := by
  intro x y hxy
  change x.1.1 = y.1.1 at hxy
  apply Subtype.ext
  apply Prod.ext
  · exact hxy
  · apply PiLp.ext
    intro i
    apply lp.ext
    funext k
    apply lp.ext
    funext n
    have hxker : x.1 ∈ (productH2Constraint n k i).ker :=
      (Submodule.mem_iInf _).mp
        ((Submodule.mem_iInf _).mp
          ((Submodule.mem_iInf _).mp x.2 n) k) i
    have hyker : y.1 ∈ (productH2Constraint n k i).ker :=
      (Submodule.mem_iInf _).mp
        ((Submodule.mem_iInf _).mp
          ((Submodule.mem_iInf _).mp y.2 n) k) i
    change (x.1.2 i k) n -
      (productH2Weight n k : ℂ) * productCoeffCLM n k i x.1.1 = 0 at hxker
    change (y.1.2 i k) n -
      (productH2Weight n k : ℂ) * productCoeffCLM n k i y.1.1 = 0 at hyker
    calc
      (x.1.2 i k) n =
          (productH2Weight n k : ℂ) * productCoeffCLM n k i x.1.1 :=
        sub_eq_zero.mp hxker
      _ = (productH2Weight n k : ℂ) * productCoeffCLM n k i y.1.1 := by
        rw [hxy]
      _ = (y.1.2 i k) n := (sub_eq_zero.mp hyker).symm

/-! ## The fixed-sector lift into product `H²` -/

/-- The fixed-`K` physical lift together with its product `H²` certificate. -/
def axialLiftH2Fun (K : ℤ) (b : TransverseC3H2) : ProductC3H2 :=
  ⟨(axialLiftFromH2 K b,
      fixedKWeightedLift K (transverseH2WeightedCoeffs b)), by
    rw [mem_productH2Submodule_iff]
    intro n k i
    by_cases hk : k = K
    · subst k
      rw [axialLiftFromH2_apply, productCoeffCLM_axialLiftL2]
      simp only [ite_true]
      exact fixedKWeightedLift_graph_at_K K
        (transverseH2WeightedCoeffs b) i n
        (transverseCoeffCLM n i (transverseH2Embedding b))
        (transverseH2WeightedCoeffs_apply b n i)
    · rw [fixedKWeightedLift_off_support K k hk]
      rw [axialLiftFromH2_apply, productCoeffCLM_axialLiftL2]
      simp [hk] ⟩

/-- Algebraic fixed-sector lift into the product `H²` graph. -/
def axialLiftH2LinearMap (K : ℤ) :
    TransverseC3H2 →ₗ[ℂ] ProductC3H2 where
  toFun := axialLiftH2Fun K
  map_add' b c := by
    apply Subtype.ext
    apply Prod.ext
    · simp [axialLiftH2Fun]
    · simp [axialLiftH2Fun]
  map_smul' c b := by
    apply Subtype.ext
    apply Prod.ext
    · simp [axialLiftH2Fun]
    · simp [axialLiftH2Fun]

/-- The physical part of a transverse `H²` element has `L²` norm at most its graph norm. -/
lemma norm_transverseH2Embedding_le (b : TransverseC3H2) :
    ‖transverseH2Embedding b‖ ≤ ‖b‖ := by
  change ‖b.1.1‖ ≤ ‖b.1‖
  rw [Prod.norm_def]
  exact le_max_left _ _

/-- The weighted certificate of a transverse `H²` element has norm at most its graph norm. -/
lemma norm_transverseH2WeightedCoeffs_le (b : TransverseC3H2) :
    ‖transverseH2WeightedCoeffs b‖ ≤ ‖b‖ := by
  change ‖b.1.2‖ ≤ ‖b.1‖
  rw [Prod.norm_def]
  exact le_max_right _ _

/--
The algebraic fixed-`K` lift is bounded on graph norms with constant `fixedKWeightBound K`,
bounding the physical part and the certificate separately in the max norm of the product.
-/
lemma norm_axialLiftH2LinearMap_apply_le (K : ℤ) (b : TransverseC3H2) :
    ‖axialLiftH2LinearMap K b‖ ≤ fixedKWeightBound K * ‖b‖ := by
  change ‖(axialLiftFromH2 K b,
    fixedKWeightedLift K (transverseH2WeightedCoeffs b))‖ ≤ _
  rw [Prod.norm_def, max_le_iff]
  constructor
  · calc
      ‖axialLiftFromH2 K b‖ = ‖transverseH2Embedding b‖ :=
        norm_axialLiftFromH2 K b
      _ ≤ ‖b‖ := norm_transverseH2Embedding_le b
      _ ≤ fixedKWeightBound K * ‖b‖ :=
        le_mul_of_one_le_left (norm_nonneg _) (one_le_fixedKWeightBound K)
  · calc
      ‖fixedKWeightedLift K (transverseH2WeightedCoeffs b)‖ ≤
          fixedKWeightBound K * ‖transverseH2WeightedCoeffs b‖ :=
        (fixedKWeightedLift K).le_of_opNorm_le
          (norm_fixedKWeightedLift_le K) _
      _ ≤ fixedKWeightBound K * ‖b‖ :=
        mul_le_mul_of_nonneg_left (norm_transverseH2WeightedCoeffs_le b)
          (fixedKWeightBound_nonneg K)

/-- The continuous fixed-`K` lift between the transverse and product Fourier-graph `H²` models. -/
def axialLiftH2 (K : ℤ) : TransverseC3H2 →L[ℂ] ProductC3H2 :=
  (axialLiftH2LinearMap K).mkContinuous
    (fixedKWeightBound K) (norm_axialLiftH2LinearMap_apply_le K)

/--
The physical field underlying the `H²` fixed-sector lift is the `L²` axial lift
`axialLiftFromH2 K b`, i.e. `e^{2π i K x₃} b`.
-/
theorem productH2Embedding_axialLiftH2 (K : ℤ)
    (b : TransverseC3H2) :
    productH2Embedding (axialLiftH2 K b) = axialLiftFromH2 K b :=
  rfl

/-- The certificate of the `H²` fixed-sector lift is the weighted lift of the transverse
certificate. -/
@[simp] theorem productH2WeightedCoeffs_axialLiftH2 (K : ℤ)
    (b : TransverseC3H2) :
    productH2WeightedCoeffs (axialLiftH2 K b) =
      fixedKWeightedLift K (transverseH2WeightedCoeffs b) :=
  rfl

/--
The product Fourier coefficients of a lifted `H²` amplitude are concentrated on the axial
frequency `K`, where they agree with the transverse coefficients of the amplitude.
-/
theorem productCoeffCLM_productH2Embedding_axialLiftH2
    (n : TransverseFrequency) (k K : ℤ) (i : Fin 3)
    (b : TransverseC3H2) :
    productCoeffCLM n k i (productH2Embedding (axialLiftH2 K b)) =
      if k = K then
        transverseCoeffCLM n i (transverseH2Embedding b) else 0 := by
  rw [productH2Embedding_axialLiftH2, axialLiftFromH2_apply,
    productCoeffCLM_axialLiftL2]
  simp only [transverseH2Embedding_apply]

/--
The `L²(T³)` norm of the lifted mode equals the `L²(T²)` norm of the transverse amplitude, the
norm identity `‖V‖ = ‖b‖` for the eigenmode `V^ε` of Paper Theorem 1.2
(`eq:main-spectral-conclusion`), which the paper uses without stating it.
-/
theorem norm_productH2Embedding_axialLiftH2 (K : ℤ)
    (b : TransverseC3H2) :
    ‖productH2Embedding (axialLiftH2 K b)‖ =
      ‖transverseH2Embedding b‖ := by
  rw [productH2Embedding_axialLiftH2, norm_axialLiftFromH2]

end

end FastDynamo
