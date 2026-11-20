/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.Assembly.AxialHilbertSum
public import LeanPool.FastDynamo.Operator.Product
public import LeanPool.FastDynamo.Dynamics.StrongSolutionUniqueness

/-!
# The axial sector decomposition of the product `H²` domain

`FastDynamo/Dynamics/Assembly/AxialHilbertSum.lean` decomposes the ambient
space `ProductC3L2` into its axial Fourier sectors.  This module lifts that
decomposition to the Fourier-graph domain `ProductC3H2` and uses it to transfer
the fixed-sector energy estimate `re_inner_reducedInductionAction_le` of
`FastDynamo/Dynamics/StrongSolutionUniqueness.lean` to the all-frequency
induction operator.

## Contents

* **The sector projection reads the axial Fourier row.**  `inner_axialLiftL2_left`
  identifies `axialSectorProjL2 K` as the adjoint of the sector isometry
  `axialLiftL2 K`, and `transverseCoeffCLM_axialSectorProjL2` turns that into the
  coefficient identity `(P_K V)^(n) = V^(n, K)`.
* **The domain-level projection.**  `axialSectorProjH2 K : ProductC3H2 →L[ℂ]
  TransverseC3H2` pairs the physical field `axialSectorProjL2 K (productH2Embedding B)`
  with the `K`-th row of the stored certificate, rescaled by the ratio
  `transverseH2Weight n / productH2Weight n K ≤ 1`.  Unlike the lift `axialLiftH2 K`,
  which is only `1 + (2πK)²`-bounded, this map has operator norm at most one
  uniformly in `K` (`norm_axialSectorProjH2_le`).  It satisfies
  `transverseH2Embedding_axialSectorProjH2` and `axialSectorProjH2_axialLiftH2`.
* **The sector expansion in the graph norm.**  `hasSum_axialLiftH2_axialSectorProjH2`
  states that every `B : ProductC3H2` is the `H²`-convergent sum of its axial
  sectors.  This is the density statement that upgrades the fixed-sector
  intertwining `productInductionAction_axialLiftH2` to the block-diagonality
  `axialSectorProjL2_productInductionAction` on the whole domain.
* **The product numerical range.**  Parseval for the axial decomposition
  (`hasSum_re_inner_axialSector`, `hasSum_norm_sq_axialSector`) sums the uniform
  fixed-sector bound `re_inner_reducedInductionAction_le` into
  `re_inner_productInductionAction_le`, whence
  `productInductionOperator_forwardStrongSolutionsUnique`.

The energy competition is never redone at the product level: transport skewness
and the diffusion sign are consumed only through the reduced operator, sector by
sector, which is what makes the constant `‖transverseStretchingCoefficient u‖`
independent of `ε` and of the axial index.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

/-! ## The sector projection reads the axial Fourier row -/

/--
Adjointness of the transverse coordinate insertion: pairing a transverse vector
field against an inserted scalar field is the scalar pairing against the `i`-th
coordinate.  This is the transverse companion of `inner_axialLiftL2_insert`.
-/
theorem inner_transverseInsertL2 (i : Fin 3) (g : TransverseScalarL2)
    (b : TransverseC3L2) :
    inner ℂ (transverseInsertL2 i g) b = inner ℂ g (transverseCoordL2 i b) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [transverseInsertL2_coe_ae i g,
    (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL (p := 2) (μ := transverseMeasure) b]
    with y h1 h2
  rw [h1]
  have h2' : ((transverseCoordL2 i b : TransverseScalarL2) : TransverseTorus → ℂ) y
      = (b y) i := h2
  rw [h2', inner_smul_left]
  simp only [EuclideanSpace.inner_single_left, RCLike.inner_apply, map_one]
  ring

/--
The sector projection is the adjoint of the sector lift: pairing a product field
against `axialLiftL2 K c` is the transverse pairing against the `K`-th sector.
This is `lp.inner_single_left` transported through the unitary
`axialDecomposition`.
-/
theorem inner_axialLiftL2_left (K : ℤ) (c : TransverseC3L2) (V : ProductC3L2) :
    inner ℂ (axialLiftL2 K c) V = inner ℂ c (axialSectorProjL2 K V) := by
  rw [← axialDecomposition.inner_map_map (axialLiftL2 K c) V,
    axialDecomposition_axialLiftL2, lp.inner_single_left]
  rfl

/--
**The sector projection reads one axial Fourier row.**  The `n`-th transverse
Fourier coefficient of the `K`-th axial sector of `V` is the product Fourier
coefficient of `V` at the frequency `(n, K)`.
-/
theorem transverseCoeffCLM_axialSectorProjL2 (n : TransverseFrequency) (K : ℤ)
    (i : Fin 3) (V : ProductC3L2) :
    transverseCoeffCLM n i (axialSectorProjL2 K V) = productCoeffCLM n K i V := by
  have h := inner_axialLiftL2_insert K i (transverseMonomialL2 n) V
  rw [inner_axialLiftL2_left, inner_transverseInsertL2] at h
  rw [transverseCoeffCLM, ContinuousLinearMap.comp_apply,
    transverseScalarCoeffCLM_eq_inner, h]
  rfl

/-- The sector projection is a contraction: it is one coordinate of the unitary
`axialDecomposition`. -/
lemma norm_axialSectorProjL2_apply_le (K : ℤ) (V : ProductC3L2) :
    ‖axialSectorProjL2 K V‖ ≤ ‖V‖ := by
  rw [axialSectorProjL2_apply, ← axialDecomposition.norm_map V]
  exact lp.norm_apply_le_norm (by norm_num) _ K

/-! ## The inverse weight ratio -/

/--
The ratio converting a stored product `H²` coefficient at the axial frequency
`K` back into a transverse `H²` coefficient.  It is the reciprocal of
`fixedKWeightRatio K`.
-/
def inverseFixedKWeightRatio (K : ℤ) (n : TransverseFrequency) : ℂ :=
  (transverseH2Weight n : ℂ) / (productH2Weight n K : ℂ)

/--
The inverse weight ratio has modulus at most one, uniformly in `n` **and** in
`K`, because the product weight dominates the transverse weight by the
nonnegative axial contribution `(2πK)²`.  This uniformity is what makes
`axialSectorProjH2` a contraction, in contrast with the lift `axialLiftH2 K`.
-/
lemma norm_inverseFixedKWeightRatio_le_one (K : ℤ) (n : TransverseFrequency) :
    ‖inverseFixedKWeightRatio K n‖ ≤ 1 := by
  rw [inverseFixedKWeightRatio, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (transverseH2Weight_pos n),
    abs_of_pos (productH2Weight_pos n K), div_le_one (productH2Weight_pos n K),
    productH2Weight_eq_transverse_add]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Multiplying the inverse ratio by the product weight at `(n, K)` returns the
transverse weight at `n`; this is what makes the projected certificate satisfy
the transverse graph equation. -/
lemma inverseFixedKWeightRatio_mul_productH2Weight (K : ℤ)
    (n : TransverseFrequency) :
    inverseFixedKWeightRatio K n * (productH2Weight n K : ℂ) =
      (transverseH2Weight n : ℂ) := by
  rw [inverseFixedKWeightRatio]
  refine div_mul_cancel₀ _ ?_
  exact_mod_cast (productH2Weight_pos n K).ne'

/-- The weight ratio of `FastDynamo/Fourier/ProductH2.lean` and the inverse ratio
are reciprocal. -/
lemma fixedKWeightRatio_mul_inverseFixedKWeightRatio (K : ℤ)
    (n : TransverseFrequency) :
    fixedKWeightRatio K n * inverseFixedKWeightRatio K n = 1 := by
  rw [fixedKWeightRatio, inverseFixedKWeightRatio]
  have h1 : (transverseH2Weight n : ℂ) ≠ 0 := by
    exact_mod_cast (transverseH2Weight_pos n).ne'
  have h2 : (productH2Weight n K : ℂ) ≠ 0 := by
    exact_mod_cast (productH2Weight_pos n K).ne'
  field_simp

/-- Multiply stored coefficients by the inverse weight ratio; a contraction of
`ℓ²`, uniformly in the axial frequency `K`. -/
def inverseFixedKRatioCoeffMap (K : ℤ) :
    TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2 :=
  lp.mapCLM 2
    (fun n => (ContinuousLinearMap.lsmul ℂ ℂ) (inverseFixedKWeightRatio K n))
    zero_le_one
    (fun n => (ContinuousLinearMap.opNorm_lsmul_apply_le
      (E := ℂ) (inverseFixedKWeightRatio K n)).trans
        (norm_inverseFixedKWeightRatio_le_one K n))

/-- The inverse-ratio coefficient map acts diagonally. -/
@[simp] lemma inverseFixedKRatioCoeffMap_apply (K : ℤ)
    (a : TransverseScalarFourierL2) (n : TransverseFrequency) :
    inverseFixedKRatioCoeffMap K a n = inverseFixedKWeightRatio K n * a n :=
  rfl

/-- The inverse-ratio coefficient map is a contraction, uniformly in `K`. -/
lemma norm_inverseFixedKRatioCoeffMap_le (K : ℤ) :
    ‖inverseFixedKRatioCoeffMap K‖ ≤ 1 :=
  lp.norm_mapCLM_le 2 _ zero_le_one
    (fun n => (ContinuousLinearMap.opNorm_lsmul_apply_le
      (E := ℂ) (inverseFixedKWeightRatio K n)).trans
        (norm_inverseFixedKWeightRatio_le_one K n))

/-- Read the `K`-th axial row of a stored scalar product certificate and convert
it into a transverse certificate. -/
def axialSectorScalarCoeffProj (K : ℤ) :
    ProductScalarFourierL2 →L[ℂ] TransverseScalarFourierL2 :=
  (inverseFixedKRatioCoeffMap K).comp
    (lp.evalCLM ℂ (fun _ : ℤ => TransverseScalarFourierL2) 2 K)

/-- Entrywise formula for the scalar certificate projection. -/
@[simp] lemma axialSectorScalarCoeffProj_apply (K : ℤ)
    (a : ProductScalarFourierL2) (n : TransverseFrequency) :
    axialSectorScalarCoeffProj K a n = inverseFixedKWeightRatio K n * (a K) n :=
  rfl

/-- The scalar certificate projection is a contraction: reading one row of a
nested `ℓ²` array is, and the inverse ratio does not increase norms. -/
lemma norm_axialSectorScalarCoeffProj_apply_le (K : ℤ)
    (a : ProductScalarFourierL2) :
    ‖axialSectorScalarCoeffProj K a‖ ≤ ‖a‖ := by
  calc ‖axialSectorScalarCoeffProj K a‖
      = ‖inverseFixedKRatioCoeffMap K (a K)‖ := rfl
    _ ≤ 1 * ‖a K‖ :=
      (inverseFixedKRatioCoeffMap K).le_of_opNorm_le
        (norm_inverseFixedKRatioCoeffMap_le K) _
    _ = ‖a K‖ := one_mul _
    _ ≤ ‖a‖ := lp.norm_apply_le_norm (by norm_num) a K

/-- The three-component certificate projection: apply the scalar row projection
in each of the three stored components. -/
def axialSectorWeightedProj (K : ℤ) :
    WeightedProductC3Coeffs →L[ℂ] WeightedTransverseC3Coeffs :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin 3 => TransverseScalarFourierL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (axialSectorScalarCoeffProj K).comp
      (PiLp.proj 2 (fun _ : Fin 3 => ProductScalarFourierL2) i))

/-- The three-component certificate projection acts componentwise. -/
@[simp] lemma axialSectorWeightedProj_apply (K : ℤ)
    (a : WeightedProductC3Coeffs) (i : Fin 3) :
    axialSectorWeightedProj K a i = axialSectorScalarCoeffProj K (a i) :=
  rfl

/-- The three-component certificate projection is a contraction, by summing the
componentwise bounds in the `PiLp 2` norm. -/
lemma norm_axialSectorWeightedProj_apply_le (K : ℤ)
    (a : WeightedProductC3Coeffs) :
    ‖axialSectorWeightedProj K a‖ ≤ ‖a‖ := by
  have hsq : ‖axialSectorWeightedProj K a‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_le_sum fun i _ => ?_
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_axialSectorScalarCoeffProj_apply_le K (a i)) 2
  nlinarith [norm_nonneg (axialSectorWeightedProj K a), norm_nonneg a]

/-- The physical part of a product `H²` element has `L²` norm at most its graph
norm. -/
lemma norm_productH2Embedding_le (B : ProductC3H2) :
    ‖productH2Embedding B‖ ≤ ‖B‖ := by
  change ‖B.1.1‖ ≤ ‖B.1‖
  rw [Prod.norm_def]
  exact le_max_left _ _

/-- The stored certificate of a product `H²` element has norm at most its graph
norm. -/
lemma norm_productH2WeightedCoeffs_le (B : ProductC3H2) :
    ‖productH2WeightedCoeffs B‖ ≤ ‖B‖ := by
  change ‖B.1.2‖ ≤ ‖B.1‖
  rw [Prod.norm_def]
  exact le_max_right _ _

/-! ## The domain-level sector projection -/

/--
**The `K`-th axial sector projection of the product `H²` domain.**  The physical
part is the ambient sector projection `axialSectorProjL2 K` of the stored field;
the certificate is the `K`-th row of the stored product certificate, rescaled by
`transverseH2Weight n / productH2Weight n K`.  The graph equation for the
projected pair is exactly the coefficient identity
`transverseCoeffCLM_axialSectorProjL2`.
-/
def axialSectorProjH2 (K : ℤ) : ProductC3H2 →L[ℂ] TransverseC3H2 :=
  ContinuousLinearMap.codRestrict
    (((axialSectorProjL2 K).comp productH2Embedding).prod
      ((axialSectorWeightedProj K).comp productH2WeightedCoeffs))
    transverseH2Submodule
    (fun B => by
      change (axialSectorProjL2 K (productH2Embedding B),
        axialSectorWeightedProj K (productH2WeightedCoeffs B)) ∈ transverseH2Submodule
      rw [mem_transverseH2Submodule_iff]
      intro n i
      rw [axialSectorWeightedProj_apply, axialSectorScalarCoeffProj_apply,
        productH2WeightedCoeffs_apply, ← mul_assoc,
        inverseFixedKWeightRatio_mul_productH2Weight,
        transverseCoeffCLM_axialSectorProjL2])

/--
**Compatibility of the domain and ambient sector projections.**  The physical
field underlying `axialSectorProjH2 K B` is the ambient sector projection of the
physical field underlying `B`.
-/
theorem transverseH2Embedding_axialSectorProjH2 (K : ℤ) (B : ProductC3H2) :
    transverseH2Embedding (axialSectorProjH2 K B) =
      axialSectorProjL2 K (productH2Embedding B) :=
  rfl

/-- The certificate of the projected field is the projected certificate. -/
@[simp] theorem transverseH2WeightedCoeffs_axialSectorProjH2 (K : ℤ)
    (B : ProductC3H2) :
    transverseH2WeightedCoeffs (axialSectorProjH2 K B) =
      axialSectorWeightedProj K (productH2WeightedCoeffs B) :=
  rfl

/-- The domain-level sector projection does not increase the graph norm: both
the physical part and the certificate are contracted. -/
theorem norm_axialSectorProjH2_apply_le (K : ℤ) (B : ProductC3H2) :
    ‖axialSectorProjH2 K B‖ ≤ ‖B‖ := by
  change ‖(axialSectorProjL2 K (productH2Embedding B),
    axialSectorWeightedProj K (productH2WeightedCoeffs B))‖ ≤ ‖B‖
  rw [Prod.norm_def, max_le_iff]
  exact ⟨(norm_axialSectorProjL2_apply_le K _).trans (norm_productH2Embedding_le B),
    (norm_axialSectorWeightedProj_apply_le K _).trans
      (norm_productH2WeightedCoeffs_le B)⟩

/--
**The domain-level sector projection is a contraction, uniformly in `K`.**  This
is the asymmetry between the two directions of the sector decomposition: the
lift `axialLiftH2 K` is only `fixedKWeightBound K = 1 + (2πK)²`-bounded,
while the projection has operator norm at most one for
every axial index.
-/
theorem norm_axialSectorProjH2_le (K : ℤ) : ‖axialSectorProjH2 K‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun B => by simpa using norm_axialSectorProjH2_apply_le K B)

/--
The domain-level projections are dual to the domain-level lifts: they recover
the amplitude of a `k`-mode and annihilate every other mode.
-/
theorem axialSectorProjH2_axialLiftH2 (k K : ℤ) (b : TransverseC3H2) :
    axialSectorProjH2 K (axialLiftH2 k b) = if k = K then b else 0 := by
  apply transverseH2Embedding_injective
  rw [transverseH2Embedding_axialSectorProjH2, productH2Embedding_axialLiftH2,
    axialLiftFromH2_apply]
  change axialSectorProjL2 K (axialLiftL2 k (transverseH2Embedding b)) = _
  rw [axialSectorProjL2_axialLiftL2]
  by_cases hk : k = K <;> simp [hk]

/-! ## The axial sector expansion of a product `H²` field -/

/--
**Ambient sector expansion.**  Every product `L²` field is the unconditional
`L²`-sum of its axial sectors; this is `lp.hasSum_single` transported through
`axialDecomposition`.
-/
theorem hasSum_axialLiftL2_axialSectorProjL2 (V : ProductC3L2) :
    HasSum (fun K : ℤ => axialLiftL2 K (axialSectorProjL2 K V)) V := by
  have h := lp.hasSum_single (E := fun _ : ℤ => TransverseC3L2) (p := 2)
    (by simp) (axialDecomposition V)
  have h2 := h.map
    axialDecomposition.symm.toLinearIsometry.toContinuousLinearMap
    axialDecomposition.symm.continuous
  simpa only [Function.comp_def, ContinuousLinearMap.coe_coe,
    LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, axialDecomposition_symm_single,
    LinearIsometryEquiv.symm_apply_apply, axialSectorProjL2_apply] using h2

/--
The certificate of the `K`-th sector of `B`, lifted back into the product graph,
is the `K`-th row of the certificate of `B`: the two weight ratios cancel.
-/
theorem productH2WeightedCoeffs_axialLiftH2_axialSectorProjH2 (K : ℤ)
    (B : ProductC3H2) (i : Fin 3) :
    productH2WeightedCoeffs (axialLiftH2 K (axialSectorProjH2 K B)) i =
      lp.single 2 K (productH2WeightedCoeffs B i K) := by
  refine lp.ext (funext fun k => lp.ext (funext fun n => ?_))
  rw [productH2WeightedCoeffs_axialLiftH2, fixedKWeightedLift_apply,
    lp.single_apply, Pi.single_apply]
  rw [transverseH2WeightedCoeffs_axialSectorProjH2, axialSectorWeightedProj_apply,
    axialSectorScalarCoeffProj_apply, ← mul_assoc,
    fixedKWeightRatio_mul_inverseFixedKWeightRatio, one_mul]
  by_cases hk : k = K <;> simp [hk]

/--
**Certificate half of the graph-norm sector expansion.**  The stored
certificates of the axial sectors of `B` sum, in `ℓ²`, to the certificate of `B`.
-/
theorem hasSum_productH2WeightedCoeffs_axialSector (B : ProductC3H2) :
    HasSum (fun K : ℤ =>
        productH2WeightedCoeffs (axialLiftH2 K (axialSectorProjH2 K B)))
      (productH2WeightedCoeffs B) := by
  have hcomp : HasSum
      (fun K : ℤ => (PiLp.continuousLinearEquiv 2 ℂ
          (fun _ : Fin 3 => ProductScalarFourierL2))
        (productH2WeightedCoeffs (axialLiftH2 K (axialSectorProjH2 K B))))
      ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ProductScalarFourierL2))
        (productH2WeightedCoeffs B)) := by
    rw [Pi.hasSum]
    intro i
    have h := lp.hasSum_single (E := fun _ : ℤ => TransverseScalarFourierL2)
      (p := 2) (by simp) (productH2WeightedCoeffs B i)
    refine h.congr_fun ?_
    intro K
    exact productH2WeightedCoeffs_axialLiftH2_axialSectorProjH2 K B i
  have h2 := hcomp.map
    (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin 3 => ProductScalarFourierL2)).symm.toContinuousLinearMap
    (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin 3 => ProductScalarFourierL2)).symm.continuous
  simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply] using h2

/--
**Sector expansion in the graph norm.**  Every element of the product `H²`
domain is the unconditional sum, *in the `H²` graph norm*, of the lifts of its
axial sectors.  Both the physical part and the stored certificate converge, so
the sum converges in the subspace topology of `ProductC3H2`.  Equivalently:
the axially band-limited elements are dense in `ProductC3H2`.
-/
theorem hasSum_axialLiftH2_axialSectorProjH2 (B : ProductC3H2) :
    HasSum (fun K : ℤ => axialLiftH2 K (axialSectorProjH2 K B)) B := by
  have hphys : HasSum (fun K : ℤ =>
      productH2Embedding (axialLiftH2 K (axialSectorProjH2 K B)))
      (productH2Embedding B) := by
    refine (hasSum_axialLiftL2_axialSectorProjL2 (productH2Embedding B)).congr_fun ?_
    intro K
    rw [productH2Embedding_axialLiftH2, axialLiftFromH2_apply]
    rfl
  have hcert := hasSum_productH2WeightedCoeffs_axialSector B
  refine tendsto_subtype_rng.mpr ?_
  refine (hphys.prodMk hcert).congr ?_
  intro s
  rw [AddSubmonoidClass.coe_finsetSum]
  rfl

/-! ## Block diagonality of the induction action -/

/--
Block diagonality on a single sector: the `K`-th sector of the induction action
of a `k`-mode is the reduced action of the `K`-th sector of that mode.  This is
`productInductionAction_axialLiftH2` combined with
`fixedSectorInductionAction_intertwines`.
-/
theorem axialSectorProjL2_productInductionAction_axialLiftH2
    (u : TransverseRealW1Inf) (ε : ℝ) (k K : ℤ) (b : TransverseC3H2) :
    axialSectorProjL2 K (productInductionAction u ε (axialLiftH2 k b)) =
      reducedInductionAction u ε K (axialSectorProjH2 K (axialLiftH2 k b)) := by
  rw [productInductionAction_axialLiftH2, fixedSectorInductionAction_intertwines,
    axialSectorProjL2_axialLiftL2, axialSectorProjH2_axialLiftH2]
  by_cases hk : k = K
  · subst hk
    simp
  · simp [hk]

/--
**The induction action is block-diagonal in the axial frequency.**  For every
product `H²` field the `K`-th axial sector of `productInductionAction u ε B` is
the reduced action `reducedInductionAction u ε K` applied to the `K`-th sector
of `B`.

Both sides are continuous linear in `B` and agree on every axial mode
(`axialSectorProjL2_productInductionAction_axialLiftH2`); the graph-norm sector
expansion `hasSum_axialLiftH2_axialSectorProjH2` extends the agreement to the
whole domain.
-/
theorem axialSectorProjL2_productInductionAction
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (B : ProductC3H2) :
    axialSectorProjL2 K (productInductionAction u ε B) =
      reducedInductionAction u ε K (axialSectorProjH2 K B) := by
  have hsum := hasSum_axialLiftH2_axialSectorProjH2 B
  have hL := hsum.map ((axialSectorProjL2 K).comp (productInductionAction u ε))
    (ContinuousLinearMap.continuous _)
  have hR := hsum.map ((reducedInductionAction u ε K).comp (axialSectorProjH2 K))
    (ContinuousLinearMap.continuous _)
  simp only [Function.comp_def, ContinuousLinearMap.coe_comp,
    ContinuousLinearMap.comp_apply] at hL hR
  exact hL.unique (hR.congr_fun fun k =>
    axialSectorProjL2_productInductionAction_axialLiftH2 u ε k K _)

/-! ## Parseval and the product-level numerical range -/

/--
**Parseval for the axial decomposition, polarized form.**  The real parts of the
sector pairings of two product fields sum to the real part of their pairing.
-/
theorem hasSum_re_inner_axialSector (V W : ProductC3L2) :
    HasSum (fun K : ℤ => (inner ℂ (axialSectorProjL2 K V) (axialSectorProjL2 K W)).re)
      ((inner ℂ V W).re) := by
  have h := (lp.hasSum_inner (axialDecomposition V) (axialDecomposition W)).map
    Complex.reCLM Complex.reCLM.continuous
  simpa only [Function.comp_def, Complex.reCLM_apply, axialSectorProjL2_apply,
    axialDecomposition.inner_map_map] using h

/--
**Parseval for the axial decomposition.**  The squared sector norms of a product
field are summable with sum its squared norm.
-/
theorem hasSum_norm_sq_axialSector (V : ProductC3L2) :
    HasSum (fun K : ℤ => ‖axialSectorProjL2 K V‖ ^ 2) (‖V‖ ^ 2) := by
  have h := hasSum_re_inner_axialSector V V
  have htot : (inner ℂ V V).re = ‖V‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) V
  rw [← htot]
  exact h.congr_fun fun K =>
    (inner_self_eq_norm_sq (𝕜 := ℂ) (axialSectorProjL2 K V)).symm

/--
**Half-plane numerical range of the all-frequency induction operator.**  For a
divergence-free transverse velocity and a nonnegative diffusivity,

`Re ⟪B, 𝒜_ε B⟫ ≤ ‖∇⊥ u‖_∞ ‖B‖²`  for every `B : ProductC3H2`,

with the same constant as in every fixed sector.  The estimate is *not* redone at
the product level: block diagonality
(`axialSectorProjL2_productInductionAction`) splits both sides of the pairing
into axial sectors, `re_inner_reducedInductionAction_le` bounds each sector by
`‖∇⊥ u‖_∞` times its squared norm, and Parseval
(`hasSum_norm_sq_axialSector`) reassembles the right-hand side.  It is the
all-frequency form of the paper's (formal) energy competition
`eq:energy-competition`.
-/
theorem re_inner_productInductionAction_le (u : TransverseRealW1Inf)
    (hu : IsTransverseDivergenceFree u) {ε : ℝ} (hε : 0 ≤ ε) (B : ProductC3H2) :
    (inner ℂ (productH2Embedding B) (productInductionAction u ε B)).re ≤
      ‖transverseStretchingCoefficient u‖ * ‖productH2Embedding B‖ ^ 2 := by
  have hcross := hasSum_re_inner_axialSector (productH2Embedding B)
    (productInductionAction u ε B)
  have hnorm := (hasSum_norm_sq_axialSector (productH2Embedding B)).mul_left
    ‖transverseStretchingCoefficient u‖
  refine hasSum_le (fun K => ?_) hcross hnorm
  rw [axialSectorProjL2_productInductionAction,
    ← transverseH2Embedding_axialSectorProjH2]
  exact re_inner_reducedInductionAction_le u hu ε hε K (axialSectorProjH2 K B)

/--
**Uniqueness of forward strong solutions of the all-frequency induction
equation.**  For every divergence-free transverse velocity and every nonnegative
diffusivity, two forward strong solutions of `productInductionOperator u ε` with
the same initial `L²` state agree in `L²` at every nonnegative time.

This needs no further hypothesis: `re_inner_productInductionAction_le` supplies the
hypothesis of `DomainOperator.forwardStrongSolutionsUnique_of_re_inner_le` with
`M = ‖transverseStretchingCoefficient u‖`.  It is the all-frequency form of
`reducedInductionOperator_forwardStrongSolutionsUnique`, and it discharges the
`ForwardStrongSolutionsUnique` hypothesis of the growth-bound comparison
`re_le_growthBound_of_eigenpair` for the product operator.

What is proved here is uniqueness for an autonomous `u`, for `H²` data, in the
classical one-sided-derivative sense of
`DomainOperator.IsForwardStrongSolution`, and for the auxiliary operator
`productInductionOperator u ε` rather than the paper's curl form `L_{ε,u}`
on `L²_σ`; the corresponding statement for the curl form, which reduces to this one, is
`productPhysicalInductionOperator_forwardStrongSolutionsUnique`.
-/
theorem productInductionOperator_forwardStrongSolutionsUnique
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (productInductionOperator u ε).ForwardStrongSolutionsUnique :=
  DomainOperator.forwardStrongSolutionsUnique_of_re_inner_le _
    ‖transverseStretchingCoefficient u‖
    (fun B => re_inner_productInductionAction_le u hu hε B)

end

end FastDynamo
