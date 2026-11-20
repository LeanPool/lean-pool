/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.FixedSectorBasic
public import LeanPool.FastDynamo.Analysis.ProductH2DenseEmbedding

/-!
# Compactness of the product-torus `H² → L²` embedding

The Fourier-graph realisation `ProductC3H2` of periodic `H²(T² × T; ℂ³)` embeds compactly into
`ProductC3L2` (Rellich theorem on the product torus).  The embedding factors as the coefficient
map `productH2WeightedCoeffs`, the coordinatewise division of the Fourier coefficients by the
weight `productH2Weight`, and Fourier synthesis.  Division by a weight that tends to infinity is a
norm limit of finite-rank truncations on `ℓ²`, hence compact.  The argument is the one used on
the transverse torus for `isCompactOperator_transverseVecH2Embedding`
(Paper Lemma 5.1, `lem:torus-sector-basic`).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open scoped ENNReal

/-! ## Diagonal operators on `ℓ²` -/

section Diagonal

variable {J : Type*}

/-- The diagonal operator on `ℓ²(J; ℂ)` with a bounded multiplier. -/
def lpDiagonal (c : J → ℂ) (C : ℝ) (hC : 0 ≤ C) (hc : ∀ j, ‖c j‖ ≤ C) :
    lp (fun _ : J ↦ ℂ) 2 →L[ℂ] lp (fun _ : J ↦ ℂ) 2 :=
  lp.mapCLM 2 (fun j ↦ (ContinuousLinearMap.lsmul ℂ ℂ) (c j)) hC
    (fun j ↦ (ContinuousLinearMap.opNorm_lsmul_apply_le (E := ℂ) (c j)).trans (hc j))

/-- The diagonal operator multiplies the `j`-th entry by `c j`. -/
@[simp] theorem lpDiagonal_apply (c : J → ℂ) (C : ℝ) (hC : 0 ≤ C) (hc : ∀ j, ‖c j‖ ≤ C)
    (a : lp (fun _ : J ↦ ℂ) 2) (j : J) : lpDiagonal c C hC hc a j = c j * a j :=
  rfl

/-- The operator norm of a diagonal operator is at most the bound of its multiplier. -/
theorem norm_lpDiagonal_le (c : J → ℂ) (C : ℝ) (hC : 0 ≤ C) (hc : ∀ j, ‖c j‖ ≤ C) :
    ‖lpDiagonal c C hC hc‖ ≤ C :=
  lp.norm_mapCLM_le 2 _ hC
    (fun j ↦ (ContinuousLinearMap.opNorm_lsmul_apply_le (E := ℂ) (c j)).trans (hc j))

/-- A finite sum of compact operators is compact. -/
theorem isCompactOperator_finset_sum {ι X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y] (s : Finset ι)
    (f : ι → X →L[ℂ] Y) (hf : ∀ i, IsCompactOperator (f i)) :
    IsCompactOperator ⇑(∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isCompactOperator_zero : IsCompactOperator (0 : X → Y))
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hf i).add ih

/-- The restriction of a diagonal operator to a finite set of coordinates. -/
def lpDiagonalFinite [DecidableEq J] (c : J → ℂ) (s : Finset J) :
    lp (fun _ : J ↦ ℂ) 2 →L[ℂ] lp (fun _ : J ↦ ℂ) 2 :=
  ∑ j ∈ s, (lp.singleContinuousLinearMap ℂ (fun _ : J ↦ ℂ) 2 j).comp
    (((ContinuousLinearMap.lsmul ℂ ℂ) (c j)).comp
      (lp.evalCLM ℂ (fun _ : J ↦ ℂ) 2 j))

/-- The finite restriction of a diagonal operator keeps the entries in `s`, multiplied by `c`,
and is zero elsewhere. -/
theorem lpDiagonalFinite_apply [DecidableEq J] (c : J → ℂ) (s : Finset J)
    (a : lp (fun _ : J ↦ ℂ) 2) (j : J) :
    lpDiagonalFinite c s a j = if j ∈ s then c j * a j else 0 := by
  have h : lpDiagonalFinite c s a = ∑ i ∈ s, lp.single 2 i (c i * a i) := by
    simp [lpDiagonalFinite]
    rfl
  rw [h, show ((∑ i ∈ s, lp.single 2 i (c i * a i) : lp (fun _ : J ↦ ℂ) 2) j) =
      ∑ i ∈ s, (lp.single 2 i (c i * a i) : lp (fun _ : J ↦ ℂ) 2) j by
    simpa only [Finset.sum_apply] using congrFun
      (lp.coeFn_sum (fun i ↦ lp.single 2 i (c i * a i)) s) j]
  by_cases hj : j ∈ s
  · rw [ite_eq_left hj, Finset.sum_eq_single j]
    · exact lp.single_apply_self 2 j _
    · intro i _ hij
      exact lp.single_apply_ne 2 i _ (Ne.symm hij)
    · exact fun h ↦ (h hj).elim
  · rw [ite_eq_right hj]
    refine Finset.sum_eq_zero fun i hi ↦ lp.single_apply_ne 2 i _ ?_
    rintro rfl
    exact hj hi

/-- A truncated diagonal operator has finite rank, hence is compact. -/
theorem isCompactOperator_lpDiagonalFinite [DecidableEq J] (c : J → ℂ) (s : Finset J) :
    IsCompactOperator (lpDiagonalFinite c s) :=
  isCompactOperator_finset_sum s _ fun j ↦
    ((isCompactOperator_of_locallyCompactSpace_dom
      (((ContinuousLinearMap.lsmul ℂ ℂ) (c j)).comp (lp.evalCLM ℂ (fun _ : J ↦ ℂ) 2 j))).clm_comp
        (lp.singleContinuousLinearMap ℂ (fun _ : J ↦ ℂ) 2 j))

/-- A diagonal operator whose multiplier tends to zero off finite sets is compact on `ℓ²`. -/
theorem isCompactOperator_lpDiagonal (c : J → ℂ) (C : ℝ) (hC : 0 ≤ C) (hc : ∀ j, ‖c j‖ ≤ C)
    (hz : ∀ δ : ℝ, 0 < δ → ∃ s : Finset J, ∀ j ∉ s, ‖c j‖ < δ) :
    IsCompactOperator (lpDiagonal c C hC hc) := by
  classical
  apply (isClosed_setOfPred_isCompactOperator :
    IsClosed {T : lp (fun _ : J ↦ ℂ) 2 →L[ℂ] lp (fun _ : J ↦ ℂ) 2 |
      IsCompactOperator T}).closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨s, hs⟩ := hz (ε / 2) (by linarith)
  let c' : J → ℂ := fun j ↦ if j ∈ s then 0 else c j
  have hc' : ∀ j, ‖c' j‖ ≤ ε / 2 := by
    intro j
    by_cases hj : j ∈ s
    · simpa [c', hj] using (by linarith : 0 ≤ ε / 2)
    · simpa only [c', ite_eq_right hj] using (hs j hj).le
  have htail : ‖lpDiagonal c' (ε / 2) (by linarith) hc'‖ ≤ ε / 2 :=
    norm_lpDiagonal_le _ _ _ _
  have heq : lpDiagonal c C hC hc - lpDiagonalFinite c s =
      lpDiagonal c' (ε / 2) (by linarith) hc' := by
    ext a j
    by_cases hj : j ∈ s <;> simp [lpDiagonalFinite_apply, c', hj]
  refine ⟨lpDiagonalFinite c s, isCompactOperator_lpDiagonalFinite c s, ?_⟩
  rw [dist_eq_norm, heq]
  exact htail.trans_lt (by linarith)

end Diagonal

/-! ## Division by the product `H²` weight -/

/-- The inverse product weight at the joint frequency `q = (k, n)`. -/
def productH2InverseWeight (q : ProductNestedFrequency) : ℂ :=
  (productH2Weight q.2 q.1 : ℂ)⁻¹

/-- The product `H²` weight is at least `1`. -/
theorem one_le_productH2Weight (n : TransverseFrequency) (k : ℤ) : 1 ≤ productH2Weight n k := by
  unfold productH2Weight
  have h : 0 ≤ (∑ j, (n j : ℝ) ^ 2) + (k : ℝ) ^ 2 :=
    add_nonneg (Finset.sum_nonneg fun j _ ↦ sq_nonneg _) (sq_nonneg _)
  nlinarith [mul_nonneg (sq_nonneg (2 * Real.pi)) h]

/-- The inverse product weight has norm at most `1`. -/
theorem norm_productH2InverseWeight_le (q : ProductNestedFrequency) :
    ‖productH2InverseWeight q‖ ≤ 1 := by
  have hpos : 0 < productH2Weight q.2 q.1 := lt_of_lt_of_le one_pos (one_le_productH2Weight _ _)
  rw [productH2InverseWeight, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  exact (inv_le_one₀ hpos).2 (one_le_productH2Weight _ _)

/-- Each frequency coordinate is bounded by the product `H²` weight. -/
theorem abs_le_productH2Weight (n : TransverseFrequency) (k : ℤ) :
    |(k : ℝ)| ≤ productH2Weight n k ∧ ∀ j : Fin 2, |(n j : ℝ)| ≤ productH2Weight n k := by
  have hpi : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.one_le_pi_div_two]
  have hS : 0 ≤ ∑ j, (n j : ℝ) ^ 2 := Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  have habs : ∀ x : ℝ, |x| ≤ 1 + x ^ 2 := fun x ↦ by
    nlinarith [sq_nonneg (|x| - 1), abs_nonneg x, sq_abs x]
  refine ⟨?_, fun j ↦ ?_⟩
  · have h1 := habs (k : ℝ)
    have h2 : (k : ℝ) ^ 2 ≤ (2 * Real.pi) ^ 2 * ((∑ j, (n j : ℝ) ^ 2) + (k : ℝ) ^ 2) := by
      nlinarith [sq_nonneg (k : ℝ),
        mul_nonneg (sub_nonneg.2 hpi) (add_nonneg hS (sq_nonneg (k : ℝ)))]
    unfold productH2Weight
    linarith
  · have h1 := habs (n j : ℝ)
    have hj : (n j : ℝ) ^ 2 ≤ ∑ i, (n i : ℝ) ^ 2 :=
      Finset.single_le_sum (fun i _ ↦ sq_nonneg (n i : ℝ)) (Finset.mem_univ j)
    have h2 : (n j : ℝ) ^ 2 ≤
        (2 * Real.pi) ^ 2 * ((∑ j, (n j : ℝ) ^ 2) + (k : ℝ) ^ 2) := by
      nlinarith [sq_nonneg (k : ℝ),
        mul_nonneg (sub_nonneg.2 hpi) (add_nonneg hS (sq_nonneg (k : ℝ)))]
    unfold productH2Weight
    linarith

/-- The inverse product weight is small off a finite set of frequencies. -/
theorem productH2InverseWeight_czero (δ : ℝ) (hδ : 0 < δ) :
    ∃ s : Finset ProductNestedFrequency, ∀ q ∉ s, ‖productH2InverseWeight q‖ < δ := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_ge (1 / δ)
  refine ⟨Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ transverseFrequencyBox N, ?_⟩
  rintro ⟨k, n⟩ hq
  have hbig : 1 / δ < productH2Weight n k := by
    rw [Finset.mem_product, not_and_or] at hq
    rcases hq with hk | hn
    · have hk' : (N : ℝ) < |(k : ℝ)| := by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hk
        rcases hk with hk | hk
        · have : (k : ℝ) < -(N : ℝ) := by exact_mod_cast hk
          exact lt_of_lt_of_le (by linarith) (neg_le_abs (k : ℝ))
        · have : (N : ℝ) < (k : ℝ) := by exact_mod_cast hk
          exact lt_of_lt_of_le this (le_abs_self _)
      exact hN.trans_lt (hk'.trans_le (abs_le_productH2Weight n k).1)
    · obtain ⟨j, hj⟩ := exists_abs_gt_of_not_mem_transverseFrequencyBox N n hn
      exact hN.trans_lt (hj.trans_le ((abs_le_productH2Weight n k).2 j))
  have hpos : 0 < productH2Weight n k := lt_of_lt_of_le one_pos (one_le_productH2Weight _ _)
  change ‖(productH2Weight n k : ℂ)⁻¹‖ < δ
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
    inv_lt_iff_one_lt_mul₀ hpos]
  have hmul := mul_lt_mul_of_pos_left hbig hδ
  simpa [hδ.ne'] using hmul

/-- Division of flat `ℓ²` coefficients by the product `H²` weight. -/
def productH2FlatInverseWeight :
    lp (fun _ : ProductNestedFrequency ↦ ℂ) 2 →L[ℂ] lp (fun _ : ProductNestedFrequency ↦ ℂ) 2 :=
  lpDiagonal productH2InverseWeight 1 zero_le_one norm_productH2InverseWeight_le

/-- Division of nested scalar product coefficients by the product `H²` weight. -/
def productH2ScalarInverseWeight : ProductScalarFourierL2 →L[ℂ] ProductScalarFourierL2 :=
  (productScalarFourierNestedFlat.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (productH2FlatInverseWeight.comp
      productScalarFourierNestedFlat.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Division of the nested scalar coefficient at `(k, n)` by `productH2Weight n k`. -/
theorem productH2ScalarInverseWeight_apply (a : ProductScalarFourierL2) (k : ℤ)
    (n : TransverseFrequency) :
    productH2ScalarInverseWeight a k n = (productH2Weight n k : ℂ)⁻¹ * a k n :=
  rfl

/-- Division of nested scalar coefficients by the product `H²` weight is compact. -/
theorem isCompactOperator_productH2ScalarInverseWeight :
    IsCompactOperator productH2ScalarInverseWeight :=
  ((isCompactOperator_lpDiagonal productH2InverseWeight 1 zero_le_one
    norm_productH2InverseWeight_le productH2InverseWeight_czero).comp_clm
      productScalarFourierNestedFlat.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
        productScalarFourierNestedFlat.symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- Rellich theorem on the product torus: the embedding of the Fourier-graph space `ProductC3H2`
of periodic `H²(T² × T; ℂ³)` into `ProductC3L2` is a compact operator.  Compactness of this
embedding is the input for the compactness of the resolvent of the induction operator
(Paper Lemma A.1, `lem:semigroup-spectral-growth`). -/
theorem isCompactOperator_productH2Embedding : IsCompactOperator productH2Embedding := by
  set T : ProductScalarFourierL2 →L[ℂ] ProductScalarL2 :=
    productScalarFourierSynthesisNested.comp productH2ScalarInverseWeight with hT
  set S : WeightedProductC3Coeffs →L[ℂ] ProductC3L2 := ∑ i : Fin 3,
    (scalarToC3CoordProductL2 i).comp
      (T.comp (PiLp.proj 2 (fun _ : Fin 3 ↦ ProductScalarFourierL2) i)) with hS
  have hsum : IsCompactOperator ⇑S :=
    isCompactOperator_finset_sum _ _ fun i ↦
      (((isCompactOperator_productH2ScalarInverseWeight).clm_comp
        productScalarFourierSynthesisNested).comp_clm
          (PiLp.proj 2 (fun _ : Fin 3 ↦ ProductScalarFourierL2) i)).clm_comp
            (scalarToC3CoordProductL2 i)
  have hEq : productH2Embedding = S.comp productH2WeightedCoeffs := by
    ext1 B
    apply productC3L2_ext_coeff
    intro n k i
    set a : WeightedProductC3Coeffs :=
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 ↦ ProductScalarFourierL2)).symm
        (fun j ↦ productH2ScalarInverseWeight (productH2WeightedCoeffs B j)) with ha
    have h1 : S (productH2WeightedCoeffs B) =
        productC3OfCoordsL2 (mapWeightedProductCoords productScalarFourierSynthesisNested a) := by
      simp [hS, productC3OfCoordsL2, mapWeightedProductCoords_apply, ha, hT]
    rw [ContinuousLinearMap.comp_apply, h1,
      productCoeffCLM_productC3OfCoordsL2_synthesis]
    have hw : (productH2Weight n k : ℂ) ≠ 0 := by
      exact_mod_cast (lt_of_lt_of_le one_pos (one_le_productH2Weight n k)).ne'
    simp only [ha, PiLp.continuousLinearEquiv_symm_apply, productH2ScalarInverseWeight_apply,
      productH2WeightedCoeffs_apply, productH2Embedding_apply]
    field_simp [hw]
  rw [hEq]
  exact hsum.comp_clm productH2WeightedCoeffs

end

end FastDynamo
