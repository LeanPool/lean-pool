/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.WeakLeibniz

/-!
# The axial Leibniz rule for transverse coefficients

The weak Leibniz rule of `FastDynamo/Analysis/WeakLeibniz.lean` in the axial direction: a
transverse (axially constant) `L∞` coefficient has vanishing axial derivative, so multiplying a
product-torus `H¹` field by it commutes with the flat axial derivative.  The module carries the
flat-axial derivative predicate, the approximation argument that establishes it for such
products, and the specialization to velocity coefficients.

The module is separate from `FastDynamo/Analysis/WeakLeibniz.lean` for build weight: that
module sits under some one hundred and fifty dependents, no declaration there refers to any
declaration below, and only two modules use them.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-! ## Axial Leibniz rule for transverse coefficients -/

/-- Axial weak derivative in flat product-frequency coordinates. -/
def HasProductScalarFlatAxialDerivative
    (f df : ProductScalarL2) : Prop :=
  ∀ m : FlatTorus3Frequency,
    productScalarFourierAnalysisFlat df m =
      (2 * Real.pi * Complex.I * (m (Fin.last 2) : ℂ)) *
        productScalarFourierAnalysisFlat f m

/-- Flat Fourier coefficient of a scalar axial lift. -/
theorem productScalarFourierAnalysisFlat_scalarAxialLift
    (K : ℤ) (f : TransverseScalarL2) (m : FlatTorus3Frequency) :
    productScalarFourierAnalysisFlat (scalarAxialLiftL2 K f) m =
      if m (Fin.last 2) = K then
        transverseScalarCoeffCLM (Fin.init m) f else 0 := by
  calc
    productScalarFourierAnalysisFlat (scalarAxialLiftL2 K f) m =
        productScalarFourierAnalysisFlat (scalarAxialLiftL2 K f)
          (Fin.snoc (Fin.init m) (m (Fin.last 2))) :=
      congrArg (fun q =>
        productScalarFourierAnalysisFlat (scalarAxialLiftL2 K f) q)
        (Fin.snoc_init_self m).symm
    _ = productScalarFourierAnalysisNested
        (scalarAxialLiftL2 K f) (m (Fin.last 2)) (Fin.init m) := by
      rw [productScalarFourierAnalysisNested_apply]
    _ = if m (Fin.last 2) = K then
          transverseScalarCoeffCLM (Fin.init m) f else 0 :=
      productScalarFourierAnalysisNested_scalarAxialLift
        K (m (Fin.last 2)) f (Fin.init m)

/-- An axial lift has the expected axial weak derivative. -/
theorem scalarAxialLift_hasFlatAxialDerivative
    (K : ℤ) (f : TransverseScalarL2) :
    HasProductScalarFlatAxialDerivative
      (scalarAxialLiftL2 K f)
      ((2 * Real.pi * Complex.I * (K : ℂ)) • scalarAxialLiftL2 K f) := by
  intro m
  have hsmul : productScalarFourierAnalysisFlat
        ((2 * Real.pi * Complex.I * (K : ℂ)) • scalarAxialLiftL2 K f) m =
      (2 * Real.pi * Complex.I * (K : ℂ)) *
        productScalarFourierAnalysisFlat (scalarAxialLiftL2 K f) m := by
    exact congrArg (fun x : FlatTorus3ScalarFourierL2 => x m)
      (map_smul productScalarFourierAnalysisFlat
        (2 * Real.pi * Complex.I * (K : ℂ)) (scalarAxialLiftL2 K f))
  rw [hsmul, productScalarFourierAnalysisFlat_scalarAxialLift]
  by_cases hm : m (Fin.last 2) = K
  · rw [ite_eq_left hm, hm]
  · rw [ite_eq_right hm]
    ring

/-- The flat axial weak-derivative relation is additive: if `df` and `dg` are the axial
derivatives of `f` and `g`, then `df + dg` is the axial derivative of `f + g`. -/
theorem HasProductScalarFlatAxialDerivative.add
    {f g df dg : ProductScalarL2}
    (hf : HasProductScalarFlatAxialDerivative f df)
    (hg : HasProductScalarFlatAxialDerivative g dg) :
    HasProductScalarFlatAxialDerivative (f + g) (df + dg) := by
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
  rw [hdfmap, hfmap, hf m, hg m]
  ring

/-- The flat axial weak-derivative relation is homogeneous: scaling a field by `c` scales
its axial derivative by `c`. -/
theorem HasProductScalarFlatAxialDerivative.smul
    {f df : ProductScalarL2}
    (hf : HasProductScalarFlatAxialDerivative f df) (c : ℂ) :
    HasProductScalarFlatAxialDerivative (c • f) (c • df) := by
  intro m
  have hdfmap : productScalarFourierAnalysisFlat (c • df) m =
      c * productScalarFourierAnalysisFlat df m := by
    exact congrArg (fun x : FlatTorus3ScalarFourierL2 => x m)
      (map_smul productScalarFourierAnalysisFlat c df)
  have hfmap : productScalarFourierAnalysisFlat (c • f) m =
      c * productScalarFourierAnalysisFlat f m := by
    exact congrArg (fun x : FlatTorus3ScalarFourierL2 => x m)
      (map_smul productScalarFourierAnalysisFlat c f)
  rw [hdfmap, hfmap, hf m]
  ring

/-- Axial differentiation of a finite flat trigonometric polynomial. -/
def productFlatTrigPolynomialAxialDeriv :
    ProductFlatTrigPolynomial →ₗ[ℂ] ProductFlatTrigPolynomial :=
  Finsupp.linearCombination ℂ fun m =>
    (2 * Real.pi * Complex.I * (m (Fin.last 2) : ℂ)) •
      Finsupp.single m 1

/-- Axial differentiation multiplies a one-term trigonometric polynomial at flat frequency
`m` by the symbol `2π i m_{2}`, the last slot being the axial one. -/
@[simp] theorem productFlatTrigPolynomialAxialDeriv_single
    (m : FlatTorus3Frequency) (c : ℂ) :
    productFlatTrigPolynomialAxialDeriv (Finsupp.single m c) =
      c • ((2 * Real.pi * Complex.I * (m (Fin.last 2) : ℂ)) •
        Finsupp.single m 1) := by
  exact Finsupp.linearCombination_single ℂ c m

/-- Multiplication by a transverse coefficient commutes with the axial weak
derivative on one product Fourier basis vector. -/
theorem hasProductFlatAxialDeriv_scalarMul_basis
    (a : TransverseScalarLInf) (m : FlatTorus3Frequency) :
    HasProductScalarFlatAxialDerivative
      (scalarMulProduct (pullTransverseScalarLInf a)
        (productScalarFourierBasisFlat m))
      (scalarMulProduct (pullTransverseScalarLInf a)
        ((2 * Real.pi * Complex.I * (m (Fin.last 2) : ℂ)) •
          productScalarFourierBasisFlat m)) := by
  rw [productScalarFourierBasisFlat_eq_productMonomial]
  change HasProductScalarFlatAxialDerivative
    (scalarMulProduct (pullTransverseScalarLInf a)
      (scalarAxialLiftL2 (m (Fin.last 2))
        (transverseMonomialL2 (Fin.init m))))
    (scalarMulProduct (pullTransverseScalarLInf a)
      ((2 * Real.pi * Complex.I * (m (Fin.last 2) : ℂ)) •
        scalarAxialLiftL2 (m (Fin.last 2))
          (transverseMonomialL2 (Fin.init m))))
  rw [scalarMul_axialLift, map_smul, scalarMul_axialLift]
  exact scalarAxialLift_hasFlatAxialDerivative
    (m (Fin.last 2))
    (scalarMulTransverse a (transverseMonomialL2 (Fin.init m)))

/-- Axial weak Leibniz rule on finite product trigonometric polynomials. -/
theorem hasProductFlatAxialDeriv_scalarMul_trig
    (a : TransverseScalarLInf) (p : ProductFlatTrigPolynomial) :
    HasProductScalarFlatAxialDerivative
      (scalarMulProduct (pullTransverseScalarLInf a)
        (productFlatTrigPolynomialToL2 p))
      (scalarMulProduct (pullTransverseScalarLInf a)
        (productFlatTrigPolynomialToL2
          (productFlatTrigPolynomialAxialDeriv p))) := by
  induction p using Finsupp.induction_linear with
  | zero => simp [HasProductScalarFlatAxialDerivative]
  | add p q hp hq =>
      have h := hp.add hq
      convert h using 1 <;> simp only [map_add]
  | single m c =>
      have hmono := hasProductFlatAxialDeriv_scalarMul_basis a m
      have h := hmono.smul c
      convert h using 1 <;>
        simp only [productFlatTrigPolynomialToL2_single,
          productFlatTrigPolynomialAxialDeriv_single,
          map_smul, one_smul, smul_smul]

/-- The axial weak-derivative graph is closed in `L² × L²`. -/
theorem HasProductScalarFlatAxialDerivative.closed_of_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {f df : ProductScalarL2} {fseq dfseq : ι → ProductScalarL2}
    (hseq : ∀ r, HasProductScalarFlatAxialDerivative
      (fseq r) (dfseq r))
    (hf : Filter.Tendsto fseq l (nhds f))
    (hdf : Filter.Tendsto dfseq l (nhds df)) :
    HasProductScalarFlatAxialDerivative f df := by
  intro m
  have hleft : Filter.Tendsto
      (fun r => productFlatScalarCoeffCLM m (dfseq r)) l
      (nhds (productFlatScalarCoeffCLM m df)) :=
    ((productFlatScalarCoeffCLM m).continuous.tendsto df).comp hdf
  have hright : Filter.Tendsto
      (fun r => (2 * Real.pi * Complex.I * (m (Fin.last 2) : ℂ)) *
        productFlatScalarCoeffCLM m (fseq r)) l
      (nhds ((2 * Real.pi * Complex.I * (m (Fin.last 2) : ℂ)) *
        productFlatScalarCoeffCLM m f)) :=
    tendsto_const_nhds.mul
      (((productFlatScalarCoeffCLM m).continuous.tendsto f).comp hf)
  apply tendsto_nhds_unique hleft
  exact hright.congr' (Filter.Eventually.of_forall fun r => (hseq r m).symm)

/-- Fourier integration by parts for the axial weak derivative. -/
theorem HasProductScalarFlatAxialDerivative.integrationByParts
    {f df g dg : ProductScalarL2}
    (hf : HasProductScalarFlatAxialDerivative f df)
    (hg : HasProductScalarFlatAxialDerivative g dg) :
    inner ℂ f dg = -inner ℂ df g := by
  rw [← productScalarFourierAnalysisFlat.inner_map_map f dg,
    ← productScalarFourierAnalysisFlat.inner_map_map df g,
    lp.inner_eq_tsum, lp.inner_eq_tsum, ← tsum_neg]
  apply tsum_congr
  intro m
  rw [hg m, hf m]
  simp only [RCLike.inner_apply, map_mul, map_ofNat,
    Complex.conj_ofReal, Complex.conj_I, map_intCast]
  ring

/-- Axially differentiating a Fourier partial sum of `f` gives the corresponding Fourier
partial sum of its axial weak derivative `df`, over the same finite frequency set. -/
theorem productFlatTrigAxialDerivative_fourierPartial
    {f df : ProductScalarL2}
    (h : HasProductScalarFlatAxialDerivative f df)
    (s : Finset FlatTorus3Frequency) :
    productFlatTrigPolynomialAxialDeriv
        (productFlatFourierPartial f s) =
      productFlatFourierPartial df s := by
  rw [productFlatFourierPartial, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [productFlatTrigPolynomialAxialDeriv_single, h m]
  ext q
  by_cases hqm : q = m
  · subst q
    rw [Finsupp.smul_apply, Finsupp.smul_apply,
      Finsupp.single_eq_same, Finsupp.single_eq_same]
    simp only [smul_eq_mul]
    ring
  · simp [hqm]

/-- The axial derivatives of the finite Fourier partial sums of `f` converge in product
`L²`, along the unconditional summation filter, to the axial weak derivative `df`. -/
theorem productFlatFourierPartial_axialDeriv_tendsto
    {f df : ProductScalarL2}
    (h : HasProductScalarFlatAxialDerivative f df) :
    Filter.Tendsto
      (fun s : Finset FlatTorus3Frequency =>
        productFlatTrigPolynomialToL2
          (productFlatTrigPolynomialAxialDeriv
            (productFlatFourierPartial f s)))
      (SummationFilter.unconditional FlatTorus3Frequency).filter
      (nhds df) := by
  convert productFlatFourierPartial_tendsto df using 1
  funext s
  rw [productFlatTrigAxialDerivative_fourierPartial h s]

/-- Full axial weak Leibniz rule: an `x₃`-independent coefficient commutes
with the axial weak derivative. -/
theorem hasProductFlatAxialDeriv_scalarMul
    (a : TransverseScalarLInf) {f df : ProductScalarL2}
    (hf : HasProductScalarFlatAxialDerivative f df) :
    HasProductScalarFlatAxialDerivative
      (scalarMulProduct (pullTransverseScalarLInf a) f)
      (scalarMulProduct (pullTransverseScalarLInf a) df) := by
  let l := (SummationFilter.unconditional FlatTorus3Frequency).filter
  apply HasProductScalarFlatAxialDerivative.closed_of_tendsto
    (l := l)
    (fseq := fun s : Finset FlatTorus3Frequency =>
      scalarMulProduct (pullTransverseScalarLInf a)
        (productFlatTrigPolynomialToL2
          (productFlatFourierPartial f s)))
    (dfseq := fun s : Finset FlatTorus3Frequency =>
      scalarMulProduct (pullTransverseScalarLInf a)
        (productFlatTrigPolynomialToL2
          (productFlatTrigPolynomialAxialDeriv
            (productFlatFourierPartial f s))))
  · intro s
    exact hasProductFlatAxialDeriv_scalarMul_trig a
      (productFlatFourierPartial f s)
  · exact ((scalarMulProduct (pullTransverseScalarLInf a)).continuous.tendsto f)
      |>.comp (productFlatFourierPartial_tendsto f)
  · exact ((scalarMulProduct (pullTransverseScalarLInf a)).continuous.tendsto df)
      |>.comp (productFlatFourierPartial_axialDeriv_tendsto hf)

/-- The scalar `H¹` model has the advertised flat-coordinate axial weak
derivative. -/
theorem productScalarH1_hasFlatAxialDerivative
    (d : ProductScalarH1) :
    HasProductScalarFlatAxialDerivative
      (productScalarH1Embedding d) (productScalarAxialDerivFromH1 d) := by
  intro m
  have h := productScalarFourierAnalysisNested_axialDerivFromH1 d
    (m (Fin.last 2)) (Fin.init m)
  rw [productScalarFourierAnalysisNested_apply,
    productScalarFourierAnalysisNested_apply,
    Fin.snoc_init_self] at h
  exact h

/-- Velocity-coordinate axial Leibniz theorem on scalar `H¹`. -/
theorem productScalarH1_velocityAxial_weakLeibniz
    (u : TransverseRealW1Inf) (d : ProductScalarH1) :
    HasProductScalarFlatAxialDerivative
      (scalarMulProduct
        (pullTransverseScalarLInf
          (transverseW1InfComplexValueCoordLInf (2 : Fin 3) u))
        (productScalarH1Embedding d))
      (scalarMulProduct
        (pullTransverseScalarLInf
          (transverseW1InfComplexValueCoordLInf (2 : Fin 3) u))
        (productScalarAxialDerivFromH1 d)) :=
  hasProductFlatAxialDeriv_scalarMul _
    (productScalarH1_hasFlatAxialDerivative d)

end

end FastDynamo
