/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.ProductScalarEnergy
public import LeanPool.FastDynamo.Analysis.TransverseW1Inf
public import LeanPool.FastDynamo.Analysis.PeriodicWeakDerivativeTest

/-!
# Weak Leibniz rules for bounded coefficients

Multiplication of a Sobolev field by a bounded coefficient with bounded weak derivatives, on the
transverse torus and on the split product torus.  The module builds the bounded multiplication
operators, proves the weak product rule against the Fourier-characterized transverse derivatives,
and supplies the flat-frequency finite Fourier approximation that the proof needs.

The velocity-coordinate specialization, the reality and symmetry statements and the public
velocity/divergence interfaces live in `FastDynamo/Analysis/WeakLeibnizVelocity.lean`; the axial
direction lives in `FastDynamo/Analysis/WeakLeibnizAxial.lean`.  Both are separate modules for
build weight.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-- Bounded multiplication of a transverse scalar `L∞` coefficient with a
transverse scalar `L²` field. -/
def scalarMulTransverse :
    TransverseScalarLInf →L[ℂ] TransverseScalarL2 →L[ℂ] TransverseScalarL2 :=
  scalarVectorMulL2 transverseMeasure

/-- Bounded multiplication of a product-torus scalar `L∞` coefficient with
a product-torus scalar `L²` field. -/
def scalarMulProduct :
    ProductScalarLInf →L[ℂ] ProductScalarL2 →L[ℂ] ProductScalarL2 :=
  scalarVectorMulL2 productMeasure

/-- Bounded transverse multiplication is the pointwise product almost everywhere:
`(a f)(x) = a x * f x`. -/
theorem scalarMulTransverse_coe_ae
    (a : TransverseScalarLInf) (f : TransverseScalarL2) :
    (scalarMulTransverse a f : TransverseTorus → ℂ)
      =ᵐ[transverseMeasure] fun x => a x * f x := by
  change ((scalarVectorMulL2 transverseMeasure a f : TransverseScalarL2) :
    TransverseTorus → ℂ) =ᵐ[transverseMeasure] fun x => a x * f x
  simpa only [smul_eq_mul] using
    scalarVectorMulL2_coe_ae transverseMeasure a f

/-- Bounded multiplication on the product torus is the pointwise product almost
everywhere: `(a f)(x) = a x * f x`. -/
theorem scalarMulProduct_coe_ae
    (a : ProductScalarLInf) (f : ProductScalarL2) :
    (scalarMulProduct a f : ProductTorus3 → ℂ)
      =ᵐ[productMeasure] fun x => a x * f x := by
  change ((scalarVectorMulL2 productMeasure a f : ProductScalarL2) :
    ProductTorus3 → ℂ) =ᵐ[productMeasure] fun x => a x * f x
  simpa only [smul_eq_mul] using
    scalarVectorMulL2_coe_ae productMeasure a f

/-- The transverse `L²` Fourier basis vector at frequency `n` is almost everywhere equal to
the continuous character `UnitAddTorus.mFourier n`. -/
theorem transverseMonomialL2_coe_ae (n : TransverseFrequency) :
    (transverseMonomialL2 n : TransverseTorus → ℂ)
      =ᵐ[transverseMeasure] UnitAddTorus.mFourier n := by
  change (transverseScalarFourierBasis n : TransverseTorus → ℂ)
      =ᵐ[transverseMeasure] UnitAddTorus.mFourier n
  rw [transverseBasis_eq_physicalMonomial]
  exact ContinuousMap.coeFn_toLp transverseMeasure
    (UnitAddTorus.mFourier n)

/-- Multiplication by one Fourier monomial shifts transverse coefficients. -/
theorem transverseCoeff_scalarMul_monomial
    (a : TransverseScalarLInf) (n q : TransverseFrequency) :
    transverseScalarCoeffCLM q
        (scalarMulTransverse a (transverseMonomialL2 n)) =
      transverseScalarCoeffCLM (q - n) (transverseScalarLInfToL2 a) := by
  rw [transverseScalarCoeffCLM_eq_inner,
    transverseScalarCoeffCLM_eq_inner, MeasureTheory.L2.inner_def,
    MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [transverseMonomialL2_coe_ae q,
    transverseMonomialL2_coe_ae n,
    transverseMonomialL2_coe_ae (q - n),
    scalarMulTransverse_coe_ae a (transverseMonomialL2 n),
    transverseScalarLInfToL2_coe_ae a] with x hq hn hqn hmul ha
  rw [hq, hmul, hn, hqn, ha]
  simp only [RCLike.inner_apply]
  rw [← UnitAddTorus.mFourier_neg (n := q) (x := x),
    ← UnitAddTorus.mFourier_neg (n := q - n) (x := x)]
  rw [mul_assoc, ← UnitAddTorus.mFourier_add]
  congr 2
  abel_nf

/-- Scalar version of the transverse Fourier weak derivative predicate. -/
def HasTransverseScalarFourierDerivative (j : Fin 2)
    (f df : TransverseScalarL2) : Prop :=
  ∀ n, transverseScalarCoeffCLM n df =
    transverseFourierDerivMultiplier j n * transverseScalarCoeffCLM n f

/-- Leibniz' rule when the second factor is one Fourier monomial. -/
theorem hasDeriv_scalarMul_monomial
    {j : Fin 2} {a da : TransverseScalarLInf}
    (ha : HasTransverseScalarFourierDerivative j
      (transverseScalarLInfToL2 a) (transverseScalarLInfToL2 da))
    (n : TransverseFrequency) :
    HasTransverseScalarFourierDerivative j
      (scalarMulTransverse a (transverseMonomialL2 n))
      (scalarMulTransverse da (transverseMonomialL2 n) +
        transverseFourierDerivMultiplier j n •
          scalarMulTransverse a (transverseMonomialL2 n)) := by
  intro q
  simp only [map_add, map_smul]
  rw [transverseCoeff_scalarMul_monomial,
    transverseCoeff_scalarMul_monomial,
    ha (q - n)]
  simp only [smul_eq_mul]
  change transverseFourierDerivMultiplier j (q - n) *
      transverseScalarCoeffCLM (q - n) (transverseScalarLInfToL2 a) +
      transverseFourierDerivMultiplier j n *
        transverseScalarCoeffCLM (q - n) (transverseScalarLInfToL2 a) =
    transverseFourierDerivMultiplier j q *
      transverseScalarCoeffCLM (q - n) (transverseScalarLInfToL2 a)
  have hm : transverseFourierDerivMultiplier j (q - n) +
      transverseFourierDerivMultiplier j n =
        transverseFourierDerivMultiplier j q := by
    unfold transverseFourierDerivMultiplier
    rw [Pi.sub_apply]
    push_cast
    ring
  rw [← hm]
  ring

/-- Leibniz' rule when the second factor is a finite trigonometric polynomial. -/
theorem hasDeriv_scalarMul_trig
    {j : Fin 2} {a da : TransverseScalarLInf}
    (ha : HasTransverseScalarFourierDerivative j
      (transverseScalarLInfToL2 a) (transverseScalarLInfToL2 da))
    (p : TransverseTrigPolynomial) :
    HasTransverseScalarFourierDerivative j
      (scalarMulTransverse a (transverseTrigPolynomialToL2 p))
      (scalarMulTransverse da (transverseTrigPolynomialToL2 p) +
        scalarMulTransverse a
          (transverseTrigPolynomialToL2
            (transverseTrigPolynomialDeriv j p))) := by
  induction p using Finsupp.induction_linear with
  | zero => simp [HasTransverseScalarFourierDerivative]
  | add p q hp hq =>
      intro n
      specialize hp n
      specialize hq n
      simp only [map_add] at hp hq ⊢
      linear_combination hp + hq
  | single n c =>
      have hmono := hasDeriv_scalarMul_monomial ha n
      intro q
      specialize hmono q
      simp only [transverseTrigPolynomialToL2_single,
        transverseTrigPolynomialDeriv_single, map_smul, one_smul,
        map_add] at hmono ⊢
      simp only [smul_eq_mul] at hmono ⊢
      linear_combination c * hmono

/-! ## Product-torus version for transverse coefficients -/

/-- Multiplication by an `x₃`-independent scalar coefficient commutes with a
scalar axial lift. -/
theorem scalarMul_axialLift (a : TransverseScalarLInf)
    (K : ℤ) (f : TransverseScalarL2) :
    scalarMulProduct (pullTransverseScalarLInf a) (scalarAxialLiftL2 K f) =
      scalarAxialLiftL2 K (scalarMulTransverse a f) := by
  apply Lp.ext
  have hmulProd := scalarMulProduct_coe_ae
    (pullTransverseScalarLInf a) (scalarAxialLiftL2 K f)
  have hpull := pullTransverseScalarLInf_coe_ae a
  have hlift := scalarAxialLiftL2Fun_ae K f
  have hmulTrans := scalarMulTransverse_coe_ae a f
  have hmulTransProd :=
    (measurePreserving_fst (μ := transverseMeasure) (ν := axialMeasure))
      |>.quasiMeasurePreserving |>.ae_eq_comp hmulTrans
  have hliftOut := scalarAxialLiftL2Fun_ae K (scalarMulTransverse a f)
  filter_upwards [hmulProd, hpull, hlift, hmulTransProd, hliftOut]
    with x hm hp hl hmt hlo
  change (scalarMulTransverse a f : TransverseTorus → ℂ) x.1 =
    a x.1 * f x.1 at hmt
  rw [hm, hp]
  change a x.1 *
      ((scalarAxialLiftL2Fun K f : ProductScalarL2) : ProductTorus3 → ℂ) x =
    ((scalarAxialLiftL2Fun K (scalarMulTransverse a f) : ProductScalarL2) :
      ProductTorus3 → ℂ) x
  rw [hl, hlo, hmt]
  ring

/-- Exact nested Fourier coefficients of a scalar axial lift. -/
theorem productScalarFourierAnalysisNested_scalarAxialLift
    (K k : ℤ) (f : TransverseScalarL2) (n : TransverseFrequency) :
    productScalarFourierAnalysisNested (scalarAxialLiftL2 K f) k n =
      if k = K then transverseScalarCoeffCLM n f else 0 := by
  rw [productScalarFourierAnalysisNested_eq_inner]
  change inner ℂ
    (scalarAxialLiftL2 k (transverseMonomialL2 n))
    (scalarAxialLiftL2 K f) = _
  rw [inner_scalarAxialLiftL2]
  by_cases hk : k = K
  · simp only [hk, ite_true]
    exact transverseScalarCoeffCLM_eq_inner f n |>.symm
  · simp [hk]

/-- A transverse Fourier weak derivative on the full product torus. -/
def HasProductScalarTransverseFourierDerivative (j : Fin 2)
    (f df : ProductScalarL2) : Prop :=
  ∀ k n, productScalarFourierAnalysisNested df k n =
    transverseFourierDerivMultiplier j n *
      productScalarFourierAnalysisNested f k n

/-- Axial lifting preserves transverse Fourier weak derivatives. -/
theorem HasTransverseScalarFourierDerivative.axialLift
    {j : Fin 2} {f df : TransverseScalarL2}
    (h : HasTransverseScalarFourierDerivative j f df)
    (K : ℤ) :
    HasProductScalarTransverseFourierDerivative j
      (scalarAxialLiftL2 K f) (scalarAxialLiftL2 K df) := by
  intro k n
  rw [productScalarFourierAnalysisNested_scalarAxialLift,
    productScalarFourierAnalysisNested_scalarAxialLift]
  by_cases hk : k = K
  · simp only [hk, ite_true]
    exact h n
  · simp [hk]

/-- Product-torus weak Leibniz rule for one product Fourier monomial. -/
theorem hasProductDeriv_scalarMul_monomial
    {j : Fin 2} {a da : TransverseScalarLInf}
    (ha : HasTransverseScalarFourierDerivative j
      (transverseScalarLInfToL2 a) (transverseScalarLInfToL2 da))
    (n : TransverseFrequency) (K : ℤ) :
    HasProductScalarTransverseFourierDerivative j
      (scalarMulProduct (pullTransverseScalarLInf a)
        (productMonomialL2 n K))
      (scalarMulProduct (pullTransverseScalarLInf da)
          (productMonomialL2 n K) +
        transverseFourierDerivMultiplier j n •
          scalarMulProduct (pullTransverseScalarLInf a)
            (productMonomialL2 n K)) := by
  rw [show productMonomialL2 n K =
      scalarAxialLiftL2 K (transverseMonomialL2 n) by rfl,
    scalarMul_axialLift, scalarMul_axialLift,
    ← map_smul, ← map_add]
  exact (hasDeriv_scalarMul_monomial ha n).axialLift K

/-! ## Flat-frequency finite Fourier approximation -/

/-- The same transverse derivative relation in the ordinary flat frequency
coordinates used by Mathlib's Hilbert basis. -/
def HasProductScalarFlatTransverseDerivative (j : Fin 2)
    (f df : ProductScalarL2) : Prop :=
  ∀ m : FlatTorus3Frequency,
    productScalarFourierAnalysisFlat df m =
      (2 * Real.pi * Complex.I * (m j.castSucc : ℂ)) *
        productScalarFourierAnalysisFlat f m

/-- The transverse weak-derivative relation stated in nested (transverse frequency, axial
index) coordinates is equivalent to the same relation stated in Mathlib's flat
three-dimensional frequency coordinates, the two being matched by `Fin.snoc`/`Fin.init`. -/
theorem hasProductNestedDerivative_iff_flat (j : Fin 2)
    (f df : ProductScalarL2) :
    HasProductScalarTransverseFourierDerivative j f df ↔
      HasProductScalarFlatTransverseDerivative j f df := by
  constructor
  · intro h m
    have hm := h (m (Fin.last 2)) (Fin.init m)
    rw [productScalarFourierAnalysisNested_apply,
      productScalarFourierAnalysisNested_apply,
      Fin.snoc_init_self] at hm
    exact hm
  · intro h k n
    have hm := h (Fin.snoc n k)
    rw [← productScalarFourierAnalysisNested_apply,
      ← productScalarFourierAnalysisNested_apply] at hm
    simpa [transverseFourierDerivMultiplier] using hm

/-- Scalar trigonometric polynomials on the full product torus, indexed in
the flat three-dimensional frequency coordinates. -/
abbrev ProductFlatTrigPolynomial := FlatTorus3Frequency →₀ ℂ

/-- Synthesis of a finite product-torus trigonometric polynomial. -/
def productFlatTrigPolynomialToL2 :
    ProductFlatTrigPolynomial →ₗ[ℂ] ProductScalarL2 :=
  Finsupp.linearCombination ℂ productScalarFourierBasisFlat

/-- Transverse differentiation of a finite product-torus trigonometric
polynomial. -/
def productFlatTrigPolynomialTransverseDeriv (j : Fin 2) :
    ProductFlatTrigPolynomial →ₗ[ℂ] ProductFlatTrigPolynomial :=
  Finsupp.linearCombination ℂ fun m =>
    (2 * Real.pi * Complex.I * (m j.castSucc : ℂ)) • Finsupp.single m 1

/-- Synthesis of a one-term trigonometric polynomial is the scalar multiple
`c • productScalarFourierBasisFlat m` of the corresponding basis vector. -/
@[simp] theorem productFlatTrigPolynomialToL2_single
    (m : FlatTorus3Frequency) (c : ℂ) :
    productFlatTrigPolynomialToL2 (Finsupp.single m c) =
      c • productScalarFourierBasisFlat m := by
  exact Finsupp.linearCombination_single ℂ c m

/-- Transverse differentiation multiplies a one-term trigonometric polynomial at flat
frequency `m` by the symbol `2π i m_{j}`, where `j.castSucc` picks the transverse slot. -/
@[simp] theorem productFlatTrigPolynomialTransverseDeriv_single
    (j : Fin 2) (m : FlatTorus3Frequency) (c : ℂ) :
    productFlatTrigPolynomialTransverseDeriv j (Finsupp.single m c) =
      c • ((2 * Real.pi * Complex.I * (m j.castSucc : ℂ)) •
        Finsupp.single m 1) := by
  exact Finsupp.linearCombination_single ℂ c m

/-- The flat product Fourier basis vector at `m` is the product monomial whose transverse
frequency is `Fin.init m` and whose axial index is `m (Fin.last 2)`. -/
lemma productScalarFourierBasisFlat_eq_productMonomial
    (m : FlatTorus3Frequency) :
    productScalarFourierBasisFlat m =
      productMonomialL2 (Fin.init m) (m (Fin.last 2)) := by
  calc
    productScalarFourierBasisFlat m =
        productScalarFourierBasisFlat
          (Fin.snoc (Fin.init m) (m (Fin.last 2))) :=
      congrArg productScalarFourierBasisFlat (Fin.snoc_init_self m).symm
    _ = productMonomialL2 (Fin.init m) (m (Fin.last 2)) :=
      productScalarFourierBasisFlat_snoc _ _

/-- The flat transverse weak-derivative relation is additive: if `df` and `dg` are the
`j`-th derivatives of `f` and `g`, then `df + dg` is the `j`-th derivative of `f + g`. -/
theorem HasProductScalarFlatTransverseDerivative.add
    {j : Fin 2} {f g df dg : ProductScalarL2}
    (hf : HasProductScalarFlatTransverseDerivative j f df)
    (hg : HasProductScalarFlatTransverseDerivative j g dg) :
    HasProductScalarFlatTransverseDerivative j (f + g) (df + dg) := by
  intro m
  have hdfmap : productScalarFourierAnalysisFlat (df + dg) m =
      productScalarFourierAnalysisFlat df m +
        productScalarFourierAnalysisFlat dg m := by
    exact congrArg (fun x : FlatTorus3ScalarFourierL2 => x m)
      (map_add productScalarFourierAnalysisFlat df dg)
  have hfmap : productScalarFourierAnalysisFlat (f + g) m =
      productScalarFourierAnalysisFlat f m +
        productScalarFourierAnalysisFlat g m := by
    exact congrArg (fun x : FlatTorus3ScalarFourierL2 => x m)
      (map_add productScalarFourierAnalysisFlat f g)
  rw [hdfmap, hfmap]
  rw [hf m, hg m]
  ring

/-- The flat transverse weak-derivative relation is homogeneous: scaling a field by `c`
scales its `j`-th derivative by `c`. -/
theorem HasProductScalarFlatTransverseDerivative.smul
    {j : Fin 2} {f df : ProductScalarL2}
    (hf : HasProductScalarFlatTransverseDerivative j f df)
    (c : ℂ) :
    HasProductScalarFlatTransverseDerivative j (c • f) (c • df) := by
  intro m
  have hdfmap : productScalarFourierAnalysisFlat (c • df) m =
      c * productScalarFourierAnalysisFlat df m := by
    exact congrArg (fun x : FlatTorus3ScalarFourierL2 => x m)
      (map_smul productScalarFourierAnalysisFlat c df)
  have hfmap : productScalarFourierAnalysisFlat (c • f) m =
      c * productScalarFourierAnalysisFlat f m := by
    exact congrArg (fun x : FlatTorus3ScalarFourierL2 => x m)
      (map_smul productScalarFourierAnalysisFlat c f)
  rw [hdfmap, hfmap]
  rw [hf m]
  ring

/-- Flat-coordinate product Leibniz rule for one Fourier basis vector. -/
theorem hasProductFlatDeriv_scalarMul_basis
    {j : Fin 2} {a da : TransverseScalarLInf}
    (ha : HasTransverseScalarFourierDerivative j
      (transverseScalarLInfToL2 a) (transverseScalarLInfToL2 da))
    (m : FlatTorus3Frequency) :
    HasProductScalarFlatTransverseDerivative j
      (scalarMulProduct (pullTransverseScalarLInf a)
        (productScalarFourierBasisFlat m))
      (scalarMulProduct (pullTransverseScalarLInf da)
          (productScalarFourierBasisFlat m) +
        (2 * Real.pi * Complex.I * (m j.castSucc : ℂ)) •
          scalarMulProduct (pullTransverseScalarLInf a)
            (productScalarFourierBasisFlat m)) := by
  apply (hasProductNestedDerivative_iff_flat j _ _).1
  rw [productScalarFourierBasisFlat_eq_productMonomial]
  exact hasProductDeriv_scalarMul_monomial ha (Fin.init m)
    (m (Fin.last 2))

/-- Weak Leibniz rule on every finite product-torus trigonometric polynomial. -/
theorem hasProductFlatDeriv_scalarMul_trig
    {j : Fin 2} {a da : TransverseScalarLInf}
    (ha : HasTransverseScalarFourierDerivative j
      (transverseScalarLInfToL2 a) (transverseScalarLInfToL2 da))
    (p : ProductFlatTrigPolynomial) :
    HasProductScalarFlatTransverseDerivative j
      (scalarMulProduct (pullTransverseScalarLInf a)
        (productFlatTrigPolynomialToL2 p))
      (scalarMulProduct (pullTransverseScalarLInf da)
          (productFlatTrigPolynomialToL2 p) +
        scalarMulProduct (pullTransverseScalarLInf a)
          (productFlatTrigPolynomialToL2
            (productFlatTrigPolynomialTransverseDeriv j p))) := by
  induction p using Finsupp.induction_linear with
  | zero => simp [HasProductScalarFlatTransverseDerivative]
  | add p q hp hq =>
      have h := hp.add hq
      convert h using 1
      · simp only [map_add]
      · simp only [map_add]
        abel
  | single m c =>
      have hmono := hasProductFlatDeriv_scalarMul_basis ha m
      have h := hmono.smul c
      convert h using 1 <;>
        simp only [productFlatTrigPolynomialToL2_single,
          productFlatTrigPolynomialTransverseDeriv_single,
          map_smul, one_smul, smul_add, smul_smul]

/-- One continuous flat Fourier coefficient functional. -/
def productFlatScalarCoeffCLM (m : FlatTorus3Frequency) :
    ProductScalarL2 →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : FlatTorus3Frequency => ℂ) 2 m).comp
    productScalarFourierAnalysisFlat.toContinuousLinearEquiv.toContinuousLinearMap

/-- The functional `productFlatScalarCoeffCLM m` returns the `m`-th flat Fourier
coefficient of a product-torus `L²` field. -/
@[simp] theorem productFlatScalarCoeffCLM_apply
    (m : FlatTorus3Frequency) (f : ProductScalarL2) :
    productFlatScalarCoeffCLM m f =
      productScalarFourierAnalysisFlat f m :=
  rfl

/-- The flat-coordinate weak derivative graph is closed in `L² × L²`, for
convergence along an arbitrary filter. -/
theorem HasProductScalarFlatTransverseDerivative.closed_of_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot] {j : Fin 2}
    {f df : ProductScalarL2} {fseq dfseq : ι → ProductScalarL2}
    (hseq : ∀ r, HasProductScalarFlatTransverseDerivative j
      (fseq r) (dfseq r))
    (hf : Filter.Tendsto fseq l (nhds f))
    (hdf : Filter.Tendsto dfseq l (nhds df)) :
    HasProductScalarFlatTransverseDerivative j f df := by
  intro m
  have hleft : Filter.Tendsto
      (fun r => productFlatScalarCoeffCLM m (dfseq r)) l
      (nhds (productFlatScalarCoeffCLM m df)) :=
    ((productFlatScalarCoeffCLM m).continuous.tendsto df).comp hdf
  have hright : Filter.Tendsto
      (fun r => (2 * Real.pi * Complex.I * (m j.castSucc : ℂ)) *
        productFlatScalarCoeffCLM m (fseq r)) l
      (nhds ((2 * Real.pi * Complex.I * (m j.castSucc : ℂ)) *
        productFlatScalarCoeffCLM m f)) :=
    tendsto_const_nhds.mul
      (((productFlatScalarCoeffCLM m).continuous.tendsto f).comp hf)
  apply tendsto_nhds_unique hleft
  exact hright.congr' (Filter.Eventually.of_forall fun r => (hseq r m).symm)

/-- Fourier integration by parts for arbitrary physical `L²` fields whose
transverse weak derivatives also lie in `L²`. -/
theorem HasProductScalarFlatTransverseDerivative.integrationByParts
    {j : Fin 2} {f df g dg : ProductScalarL2}
    (hf : HasProductScalarFlatTransverseDerivative j f df)
    (hg : HasProductScalarFlatTransverseDerivative j g dg) :
    inner ℂ f dg = -inner ℂ df g := by
  rw [← productScalarFourierAnalysisFlat.inner_map_map f dg,
    ← productScalarFourierAnalysisFlat.inner_map_map df g,
    lp.inner_eq_tsum, lp.inner_eq_tsum]
  rw [← tsum_neg]
  apply tsum_congr
  intro m
  rw [hg m, hf m]
  simp only [RCLike.inner_apply, map_mul, map_ofNat,
    Complex.conj_ofReal, Complex.conj_I, map_intCast]
  ring

/-- The finite Fourier partial sum whose coefficients are those of `f` on
the supplied finite frequency set. -/
def productFlatFourierPartial (f : ProductScalarL2)
    (s : Finset FlatTorus3Frequency) : ProductFlatTrigPolynomial :=
  ∑ m ∈ s, Finsupp.single m (productScalarFourierAnalysisFlat f m)

/-- The synthesis of the Fourier partial sum over a finite frequency set `s` is the finite
sum `∑_{m ∈ s} f̂(m) • e_m` of basis vectors. -/
theorem productFlatTrigPolynomialToL2_fourierPartial
    (f : ProductScalarL2) (s : Finset FlatTorus3Frequency) :
    productFlatTrigPolynomialToL2
        (productFlatFourierPartial f s) =
      ∑ m ∈ s, productScalarFourierAnalysisFlat f m •
        productScalarFourierBasisFlat m := by
  simp [productFlatFourierPartial]

/-- The Hilbert-basis representation coefficients of `f` coincide with the values of the
flat Fourier analysis map, so the two coefficient conventions may be used interchangeably. -/
lemma productScalarFourierBasisFlat_repr_apply
    (f : ProductScalarL2) (m : FlatTorus3Frequency) :
    productScalarFourierBasisFlat.repr f m =
      productScalarFourierAnalysisFlat f m :=
  rfl

/-- Fourier partial sums converge in physical product `L²`. -/
theorem productFlatFourierPartial_tendsto (f : ProductScalarL2) :
    Filter.Tendsto
      (fun s : Finset FlatTorus3Frequency =>
        productFlatTrigPolynomialToL2
          (productFlatFourierPartial f s))
      (SummationFilter.unconditional FlatTorus3Frequency).filter
      (nhds f) := by
  have h := productScalarFourierBasisFlat.hasSum_repr f
  change Filter.Tendsto
    (fun s : Finset FlatTorus3Frequency =>
      ∑ m ∈ s, productScalarFourierBasisFlat.repr f m •
        productScalarFourierBasisFlat m)
    (SummationFilter.unconditional FlatTorus3Frequency).filter (nhds f) at h
  convert h using 1
  funext s
  rw [productFlatTrigPolynomialToL2_fourierPartial]
  apply Finset.sum_congr rfl
  intro m hm
  rw [productScalarFourierBasisFlat_repr_apply]

/-- Differentiating a Fourier partial sum of `f` in the transverse direction `j` gives the
corresponding Fourier partial sum of its weak derivative `df`, over the same finite
frequency set. -/
theorem productFlatTrigDerivative_fourierPartial
    {j : Fin 2} {f df : ProductScalarL2}
    (h : HasProductScalarFlatTransverseDerivative j f df)
    (s : Finset FlatTorus3Frequency) :
    productFlatTrigPolynomialTransverseDeriv j
        (productFlatFourierPartial f s) =
      productFlatFourierPartial df s := by
  rw [productFlatFourierPartial, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [productFlatTrigPolynomialTransverseDeriv_single, h m]
  ext q
  by_cases hqm : q = m
  · subst q
    rw [Finsupp.smul_apply, Finsupp.smul_apply,
      Finsupp.single_eq_same, Finsupp.single_eq_same]
    simp only [smul_eq_mul]
    ring
  · simp [hqm]

/-- The derivatives of the finite Fourier partial sums converge to the weak
derivative in product `L²`. -/
theorem productFlatFourierPartial_deriv_tendsto
    {j : Fin 2} {f df : ProductScalarL2}
    (h : HasProductScalarFlatTransverseDerivative j f df) :
    Filter.Tendsto
      (fun s : Finset FlatTorus3Frequency =>
        productFlatTrigPolynomialToL2
          (productFlatTrigPolynomialTransverseDeriv j
            (productFlatFourierPartial f s)))
      (SummationFilter.unconditional FlatTorus3Frequency).filter
      (nhds df) := by
  convert productFlatFourierPartial_tendsto df using 1
  funext s
  rw [productFlatTrigDerivative_fourierPartial h s]

/-- Full weak Leibniz rule on the product torus for an arbitrary scalar field
with one `L²` transverse weak derivative. -/
theorem hasProductFlatDeriv_scalarMul
    {j : Fin 2} {a da : TransverseScalarLInf}
    (ha : HasTransverseScalarFourierDerivative j
      (transverseScalarLInfToL2 a) (transverseScalarLInfToL2 da))
    {f df : ProductScalarL2}
    (hf : HasProductScalarFlatTransverseDerivative j f df) :
    HasProductScalarFlatTransverseDerivative j
      (scalarMulProduct (pullTransverseScalarLInf a) f)
      (scalarMulProduct (pullTransverseScalarLInf da) f +
        scalarMulProduct (pullTransverseScalarLInf a) df) := by
  let l := (SummationFilter.unconditional FlatTorus3Frequency).filter
  apply HasProductScalarFlatTransverseDerivative.closed_of_tendsto
    (l := l)
    (fseq := fun s : Finset FlatTorus3Frequency =>
      scalarMulProduct (pullTransverseScalarLInf a)
        (productFlatTrigPolynomialToL2
          (productFlatFourierPartial f s)))
    (dfseq := fun s : Finset FlatTorus3Frequency =>
      scalarMulProduct (pullTransverseScalarLInf da)
          (productFlatTrigPolynomialToL2
            (productFlatFourierPartial f s)) +
        scalarMulProduct (pullTransverseScalarLInf a)
          (productFlatTrigPolynomialToL2
            (productFlatTrigPolynomialTransverseDeriv j
              (productFlatFourierPartial f s))))
  · intro s
    exact hasProductFlatDeriv_scalarMul_trig ha
      (productFlatFourierPartial f s)
  · exact ((scalarMulProduct (pullTransverseScalarLInf a)).continuous.tendsto f)
      |>.comp (productFlatFourierPartial_tendsto f)
  · exact (((scalarMulProduct (pullTransverseScalarLInf da)).continuous.tendsto f)
        |>.comp (productFlatFourierPartial_tendsto f)).add
      (((scalarMulProduct (pullTransverseScalarLInf a)).continuous.tendsto df)
        |>.comp (productFlatFourierPartial_deriv_tendsto hf))

/-- The public scalar `H¹` Fourier model has the advertised flat-frequency
weak transverse derivative. -/
theorem productScalarH1_hasFlatTransverseDerivative
    (j : Fin 2) (d : ProductScalarH1) :
    HasProductScalarFlatTransverseDerivative j
      (productScalarH1Embedding d)
      (productScalarTransverseDerivFromH1 j d) := by
  apply (hasProductNestedDerivative_iff_flat j _ _).1
  intro k n
  simpa [transverseFourierDerivMultiplier] using
    productScalarFourierAnalysisNested_transverseDerivFromH1 j d k n

/-- Multiplication by a transverse scalar `W^{1,∞}` coefficient maps the
physical scalar `H¹` graph to itself and satisfies the exact weak Leibniz
formula. -/
theorem productScalarH1_weakLeibniz
    {j : Fin 2} {a da : TransverseScalarLInf}
    (ha : HasTransverseScalarFourierDerivative j
      (transverseScalarLInfToL2 a) (transverseScalarLInfToL2 da))
    (d : ProductScalarH1) :
    HasProductScalarFlatTransverseDerivative j
      (scalarMulProduct (pullTransverseScalarLInf a)
        (productScalarH1Embedding d))
      (scalarMulProduct (pullTransverseScalarLInf da)
          (productScalarH1Embedding d) +
        scalarMulProduct (pullTransverseScalarLInf a)
          (productScalarTransverseDerivFromH1 j d)) :=
  hasProductFlatDeriv_scalarMul ha
    (productScalarH1_hasFlatTransverseDerivative j d)

end

end FastDynamo
