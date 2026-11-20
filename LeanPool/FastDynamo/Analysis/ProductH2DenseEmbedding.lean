/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Operator.Product

/-!
# Density of the product-torus `H²` Fourier graph

This file proves that the full three-dimensional Fourier-graph domain
`ProductC3H2` is dense in physical product `L²`.  The coefficient model is
nested (`k : ℤ` outside and `n : ℤ²` inside), so we first use the
isometry from nested `ℓ²` to flat `ℓ²(ℤ × ℤ²)`.  Finite coordinate sums
in the flat model give simultaneous finite axial/transverse truncations.

For each physical vector field, its finite unweighted Fourier truncation is
paired with the finitely supported family obtained by multiplying every
retained coefficient by `productH2Weight`.  This pair satisfies the closed
graph equation exactly.  The resulting graph elements converge after the
canonical `productH2Embedding`, proving dense range and hence dense
definedness of `productInductionOperator`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

/-! ## Finite truncation of nested scalar product coefficients -/

/-- The joint axial/transverse index in the order used by the nested
coefficient model. -/
abbrev ProductNestedFrequency := ℤ × TransverseFrequency

/-- Flatten the project's nested scalar product coefficients isometrically. -/
def productScalarFourierNestedFlat :
    ProductScalarFourierL2 ≃ₗᵢ[ℂ]
      lp (fun _ : ProductNestedFrequency ↦ ℂ) 2 :=
  scalarL2NestedFlat

/-- Flattening the nested coefficient model reads the entry at the joint frequency `q` as the
nested entry at axial index `q.1` and transverse index `q.2`. -/
@[simp] theorem productScalarFourierNestedFlat_apply
    (a : ProductScalarFourierL2) (q : ProductNestedFrequency) :
    productScalarFourierNestedFlat a q = a q.1 q.2 :=
  rfl

/-- Un-flattening reads the nested entry at `(k, n)` as the flat entry at the joint frequency
`(k, n)`. -/
@[simp] theorem productScalarFourierNestedFlat_symm_apply
    (a : lp (fun _ : ProductNestedFrequency ↦ ℂ) 2)
    (k : ℤ) (n : TransverseFrequency) :
    productScalarFourierNestedFlat.symm a k n = a (k, n) :=
  rfl

/-- Restrict a flat scalar square-summable family to a finite set of joint
product frequencies. -/
def productScalarFourierFlatTruncation
    (a : lp (fun _ : ProductNestedFrequency ↦ ℂ) 2)
    (s : Finset ProductNestedFrequency) :
    lp (fun _ : ProductNestedFrequency ↦ ℂ) 2 :=
  ∑ q ∈ s, lp.single 2 q (a q)

/-- The finite truncation of a square-summable family keeps the coefficients indexed by the
finite set `s` and sets all others to zero. -/
@[simp] theorem productScalarFourierFlatTruncation_apply
    (a : lp (fun _ : ProductNestedFrequency ↦ ℂ) 2)
    (s : Finset ProductNestedFrequency) (q : ProductNestedFrequency) :
    productScalarFourierFlatTruncation a s q =
      if q ∈ s then a q else 0 := by
  classical
  unfold productScalarFourierFlatTruncation
  rw [show ((∑ r ∈ s, lp.single 2 r (a r)) :
      lp (fun _ : ProductNestedFrequency ↦ ℂ) 2) q =
        ∑ r ∈ s, (lp.single 2 r (a r)) q by
    simpa only [Finset.sum_apply] using congrFun
      (lp.coeFn_sum (fun r ↦ lp.single 2 r (a r)) s) q]
  by_cases hq : q ∈ s
  · rw [ite_eq_left hq, Finset.sum_eq_single q]
    · exact lp.single_apply_self 2 q _
    · intro r hr hrq
      exact lp.single_apply_ne 2 r _ (Ne.symm hrq)
    · exact fun h ↦ (h hq).elim
  · rw [ite_eq_right hq]
    apply Finset.sum_eq_zero
    intro r hr
    exact lp.single_apply_ne 2 r _ (by
      intro h
      apply hq
      simpa [h] using hr)

/-- Flat finite coordinate sums converge to every scalar product Fourier
family. -/
theorem tendsto_productScalarFourierFlatTruncation
    (a : lp (fun _ : ProductNestedFrequency ↦ ℂ) 2) :
    Tendsto (fun s : Finset ProductNestedFrequency ↦
      productScalarFourierFlatTruncation a s) atTop (nhds a) := by
  have hsum := lp.hasSum_single ENNReal.ofNat_ne_top a
  change Tendsto (fun s : Finset ProductNestedFrequency ↦
    ∑ q ∈ s, lp.single 2 q (a q)) atTop (nhds a) at hsum
  simpa only [productScalarFourierFlatTruncation] using hsum

/-- Finite joint-frequency truncation transported back to the nested
coefficient model. -/
def productScalarFourierTruncation
    (a : ProductScalarFourierL2) (s : Finset ProductNestedFrequency) :
    ProductScalarFourierL2 :=
  productScalarFourierNestedFlat.symm
    (productScalarFourierFlatTruncation
      (productScalarFourierNestedFlat a) s)

/-- In the nested model, the truncation at a finite set `s` of joint frequencies keeps the
coefficient at `(k, n)` when `(k, n) ∈ s` and is zero otherwise. -/
@[simp] theorem productScalarFourierTruncation_apply
    (a : ProductScalarFourierL2) (s : Finset ProductNestedFrequency)
    (k : ℤ) (n : TransverseFrequency) :
    productScalarFourierTruncation a s k n =
      if (k, n) ∈ s then a k n else 0 := by
  rw [productScalarFourierTruncation,
    productScalarFourierNestedFlat_symm_apply,
    productScalarFourierFlatTruncation_apply,
    productScalarFourierNestedFlat_apply]

/-- Finite joint-frequency truncations converge in the nested scalar
coefficient norm. -/
theorem tendsto_productScalarFourierTruncation
    (a : ProductScalarFourierL2) :
    Tendsto (fun s : Finset ProductNestedFrequency ↦
      productScalarFourierTruncation a s) atTop (nhds a) := by
  have h := productScalarFourierNestedFlat.symm.continuous.tendsto
      (productScalarFourierNestedFlat a) |>.comp
    (tendsto_productScalarFourierFlatTruncation
      (productScalarFourierNestedFlat a))
  rw [productScalarFourierNestedFlat.symm_apply_apply] at h
  exact h.congr' (Eventually.of_forall fun s ↦ rfl)

/-! ## Vector product Fourier analysis, synthesis, and truncation -/

/-- Coordinatewise complete nested Fourier analysis of a physical product
`C3` field. -/
def productC3L2FourierAnalysisForDensity :
    ProductC3L2 →L[ℂ] WeightedProductC3Coeffs :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin 3 ↦ ProductScalarFourierL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦
      productScalarFourierAnalysisNested.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (productCoordL2 i))

/-- Coordinatewise nested Fourier analysis of a physical field returns its vector Fourier
coefficients: the `(i, k, n)` entry is `productCoeffCLM n k i V`. -/
@[simp] theorem productC3L2FourierAnalysisForDensity_apply
    (V : ProductC3L2) (i : Fin 3) (k : ℤ)
    (n : TransverseFrequency) :
    productC3L2FourierAnalysisForDensity V i k n =
      productCoeffCLM n k i V := by
  change productScalarFourierAnalysisNested (productCoordL2 i V) k n = _
  exact productScalarFourierAnalysisNested_coord_eq_productCoeffCLM V i k n

/-- Coordinatewise complete nested Fourier synthesis of a product `C3`
coefficient family. -/
def productC3L2FourierSynthesisForDensity :
    WeightedProductC3Coeffs →L[ℂ] ProductC3L2 :=
  productC3OfCoordsL2.comp
    (mapWeightedProductCoords productScalarFourierSynthesisNested)

/-- Synthesizing a three-component nested coefficient family produces a field whose vector
Fourier coefficients are exactly the entries of that family. -/
@[simp] theorem productCoeffCLM_productC3L2FourierSynthesisForDensity
    (a : WeightedProductC3Coeffs) (n : TransverseFrequency)
    (k : ℤ) (i : Fin 3) :
    productCoeffCLM n k i (productC3L2FourierSynthesisForDensity a) =
      a i k n := by
  exact productCoeffCLM_productC3OfCoordsL2_synthesis a n k i

/-- Product Fourier synthesis is a left inverse to coordinatewise analysis. -/
@[simp] theorem productC3L2FourierSynthesisForDensity_analysis
    (V : ProductC3L2) :
    productC3L2FourierSynthesisForDensity
        (productC3L2FourierAnalysisForDensity V) = V := by
  apply productC3L2_ext_coeff
  intro n k i
  rw [productCoeffCLM_productC3L2FourierSynthesisForDensity,
    productC3L2FourierAnalysisForDensity_apply]

/-- Simultaneously truncate all three nested scalar coordinate families to
one finite set of joint product frequencies. -/
def productC3L2FourierTruncation
    (a : WeightedProductC3Coeffs) (s : Finset ProductNestedFrequency) :
    WeightedProductC3Coeffs :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin 3 ↦ ProductScalarFourierL2)).symm
    (fun i ↦ productScalarFourierTruncation (a i) s)

/-- Simultaneous truncation acts coordinatewise: its `i`-th component is the scalar truncation of
the `i`-th component to the same finite frequency set. -/
@[simp] theorem productC3L2FourierTruncation_apply
    (a : WeightedProductC3Coeffs) (s : Finset ProductNestedFrequency)
    (i : Fin 3) :
    productC3L2FourierTruncation a s i =
      productScalarFourierTruncation (a i) s :=
  rfl

/-- Simultaneous finite truncations converge in the three-component nested
coefficient space. -/
theorem tendsto_productC3L2FourierTruncation
    (a : WeightedProductC3Coeffs) :
    Tendsto (fun s : Finset ProductNestedFrequency ↦
      productC3L2FourierTruncation a s) atTop (nhds a) := by
  let e := PiLp.continuousLinearEquiv 2 ℂ
    (fun _ : Fin 3 ↦ ProductScalarFourierL2)
  have hcoords : Tendsto (fun s : Finset ProductNestedFrequency ↦
      fun i : Fin 3 ↦ productScalarFourierTruncation (a i) s)
      atTop (nhds (fun i : Fin 3 ↦ a i)) := by
    rw [tendsto_pi_nhds]
    intro i
    exact tendsto_productScalarFourierTruncation (a i)
  have h := e.symm.continuous.tendsto (fun i : Fin 3 ↦ a i) |>.comp hcoords
  have ha : e.symm (fun i : Fin 3 ↦ a i) = a := by
    apply e.injective
    rw [e.apply_symm_apply]
    rfl
  change Tendsto (fun s : Finset ProductNestedFrequency ↦
      e.symm (fun i : Fin 3 ↦ productScalarFourierTruncation (a i) s))
      atTop (nhds (e.symm (fun i : Fin 3 ↦ a i))) at h
  rw [ha] at h
  simpa only [e, productC3L2FourierTruncation] using h

/-! ## Physical partial sums and exact product `H²` certificates -/

/-- The physical vector Fourier partial sum over a finite joint-frequency
set. -/
def productC3L2FourierPartialSum
    (V : ProductC3L2) (s : Finset ProductNestedFrequency) :
    ProductC3L2 :=
  productC3L2FourierSynthesisForDensity
    (productC3L2FourierTruncation
      (productC3L2FourierAnalysisForDensity V) s)

/-- The Fourier coefficients of a finite partial sum agree with those of `V` on the retained
frequency set `s` and vanish off it. -/
theorem productCoeffCLM_productC3L2FourierPartialSum
    (V : ProductC3L2) (s : Finset ProductNestedFrequency)
    (n : TransverseFrequency) (k : ℤ) (i : Fin 3) :
    productCoeffCLM n k i (productC3L2FourierPartialSum V s) =
      if (k, n) ∈ s then productCoeffCLM n k i V else 0 := by
  rw [productC3L2FourierPartialSum,
    productCoeffCLM_productC3L2FourierSynthesisForDensity,
    productC3L2FourierTruncation_apply,
    productScalarFourierTruncation_apply,
    productC3L2FourierAnalysisForDensity_apply]

/-- The physical product Fourier partial sums converge in `L²`. -/
theorem tendsto_productC3L2FourierPartialSum (V : ProductC3L2) :
    Tendsto (fun s : Finset ProductNestedFrequency ↦
      productC3L2FourierPartialSum V s) atTop (nhds V) := by
  have h := productC3L2FourierSynthesisForDensity.continuous.tendsto
      (productC3L2FourierAnalysisForDensity V) |>.comp
    (tendsto_productC3L2FourierTruncation
      (productC3L2FourierAnalysisForDensity V))
  rw [productC3L2FourierSynthesisForDensity_analysis] at h
  exact h.congr' (Eventually.of_forall fun s ↦ rfl)

/-- Multiply a finite scalar product Fourier truncation by the full
three-dimensional order-two weight. -/
def productScalarH2WeightedTruncation
    (a : ProductScalarFourierL2) (s : Finset ProductNestedFrequency) :
    ProductScalarFourierL2 :=
  productScalarFourierNestedFlat.symm
    (∑ q ∈ s, lp.single 2 q
      ((productH2Weight q.2 q.1 : ℂ) * a q.1 q.2))

/-- The weighted truncation carries the coefficient `productH2Weight n k * a k n` at every
retained frequency `(k, n) ∈ s` and zero elsewhere; this is the `H²` graph certificate attached
to the partial sum. -/
@[simp] theorem productScalarH2WeightedTruncation_apply
    (a : ProductScalarFourierL2) (s : Finset ProductNestedFrequency)
    (k : ℤ) (n : TransverseFrequency) :
    productScalarH2WeightedTruncation a s k n =
      if (k, n) ∈ s then
        (productH2Weight n k : ℂ) * a k n else 0 := by
  classical
  rw [productScalarH2WeightedTruncation,
    productScalarFourierNestedFlat_symm_apply]
  rw [show ((∑ q ∈ s, lp.single 2 q
      ((productH2Weight q.2 q.1 : ℂ) * a q.1 q.2)) :
        lp (fun _ : ProductNestedFrequency ↦ ℂ) 2) (k, n) =
      ∑ q ∈ s, (lp.single 2 q
        ((productH2Weight q.2 q.1 : ℂ) * a q.1 q.2)) (k, n) by
    simpa only [Finset.sum_apply] using congrFun
      (lp.coeFn_sum (fun q ↦ lp.single 2 q
        ((productH2Weight q.2 q.1 : ℂ) * a q.1 q.2)) s) (k, n)]
  by_cases hkn : (k, n) ∈ s
  · rw [ite_eq_left hkn, Finset.sum_eq_single (k, n)]
    · exact lp.single_apply_self 2 (k, n) _
    · intro q hq hqkn
      exact lp.single_apply_ne 2 q _ (Ne.symm hqkn)
    · exact fun h ↦ (h hkn).elim
  · rw [ite_eq_right hkn]
    apply Finset.sum_eq_zero
    intro q hq
    exact lp.single_apply_ne 2 q _ (by
      intro h
      apply hkn
      simpa [h] using hq)

/-- Three-component weighted graph certificate for a physical product
Fourier partial sum. -/
def productC3H2WeightedTruncation
    (V : ProductC3L2) (s : Finset ProductNestedFrequency) :
    WeightedProductC3Coeffs :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin 3 ↦ ProductScalarFourierL2)).symm
    (fun i ↦ productScalarH2WeightedTruncation
      (productC3L2FourierAnalysisForDensity V i) s)

/-- The three-component weighted certificate acts coordinatewise: its `i`-th component is the
weighted truncation of the `i`-th Fourier coordinate of `V`. -/
@[simp] theorem productC3H2WeightedTruncation_coord
    (V : ProductC3L2) (s : Finset ProductNestedFrequency) (i : Fin 3) :
    productC3H2WeightedTruncation V s i =
      productScalarH2WeightedTruncation
        (productC3L2FourierAnalysisForDensity V i) s :=
  rfl

/-- Entrywise value of the weighted certificate: `productH2Weight n k * productCoeffCLM n k i V`
at retained frequencies `(k, n) ∈ s`, and zero elsewhere. -/
theorem productC3H2WeightedTruncation_apply
    (V : ProductC3L2) (s : Finset ProductNestedFrequency)
    (i : Fin 3) (k : ℤ) (n : TransverseFrequency) :
    productC3H2WeightedTruncation V s i k n =
      if (k, n) ∈ s then
        (productH2Weight n k : ℂ) * productCoeffCLM n k i V else 0 := by
  rw [productC3H2WeightedTruncation_coord,
    productScalarH2WeightedTruncation_apply,
    productC3L2FourierAnalysisForDensity_apply]

/-- A finite product Fourier partial sum bundled with its exact weighted
coefficient certificate in the closed `H²` graph. -/
def productH2FourierTruncation
    (V : ProductC3L2) (s : Finset ProductNestedFrequency) :
    ProductC3H2 :=
  ⟨(productC3L2FourierPartialSum V s,
      productC3H2WeightedTruncation V s), by
    rw [mem_productH2Submodule_iff]
    intro n k i
    rw [productC3H2WeightedTruncation_apply,
      productCoeffCLM_productC3L2FourierPartialSum]
    by_cases hkn : (k, n) ∈ s <;> simp [hkn]⟩

/-- Forgetting the `H²` certificate of the bundled finite truncation returns the physical Fourier
partial sum of `V` over the frequency set `s`. -/
theorem productH2Embedding_productH2FourierTruncation
    (V : ProductC3L2) (s : Finset ProductNestedFrequency) :
    productH2Embedding (productH2FourierTruncation V s) =
      productC3L2FourierPartialSum V s :=
  rfl

/-- Canonical finite product `H²` graph approximants converge to every
physical product `L²` field after applying the graph embedding. -/
theorem tendsto_productH2Embedding_fourierTruncation (V : ProductC3L2) :
    Tendsto (fun s : Finset ProductNestedFrequency ↦
      productH2Embedding (productH2FourierTruncation V s))
      atTop (nhds V) := by
  simpa only [productH2Embedding_productH2FourierTruncation] using
    tendsto_productC3L2FourierPartialSum V

/-! ## Dense range and the all-frequency induction domain -/

/-- The canonical embedding of the full periodic product `H²` Fourier graph
into physical product `L²` has dense range. -/
theorem denseRange_productH2Embedding : DenseRange productH2Embedding := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro V
  apply mem_closure_of_tendsto
    (tendsto_productH2Embedding_fourierTruncation V)
  exact Eventually.of_forall fun s ↦
    ⟨productH2FourierTruncation V s, rfl⟩

/-- The domain embedding of the all-frequency induction operator is the canonical inclusion of
the product `H²` Fourier graph into physical `L²`. -/
@[simp] theorem productInductionOperator_embedding
    (u : TransverseRealW1Inf) (ε : ℝ) :
    (productInductionOperator u ε).embedding = productH2Embedding :=
  rfl

/-- The full all-frequency induction operator is densely defined in product
`L²`, uniformly in the velocity and diffusivity. -/
theorem denseRange_productInductionOperator_embedding
    (u : TransverseRealW1Inf) (ε : ℝ) :
    DenseRange (productInductionOperator u ε).embedding := by
  simpa only [productInductionOperator_embedding] using
    denseRange_productH2Embedding

end

end FastDynamo
