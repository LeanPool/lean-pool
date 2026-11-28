/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Manifolds.ChartSobolev
public import LeanPool.FunctionSpaces.Domains.Spectral.NeumannEigenbasis

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The eigenbasis of the chart form on a compact manifold

Let `M` be a compact manifold with model `I` whose range `Ω_I = range I` is a Besov domain, of
dimension `n = dim E ≥ 1`, with a smooth measure `μ` and a Besov atlas `A`; `O_I = interior Ω_I`
is the open model set, `P_k` the pieces, `L_k` the lifts and `J : H^1_A(M) → L_2(μ)` the chart
Sobolev embedding (`Manifold.BesovAtlas.chartSobolevEmbedding`). Inner products are
conjugate-linear in the first argument, as in Mathlib.

* **Bounded convex pieces**: the piece `P_k f` vanishes outside the ball `B(0, R_k)` of
  `Manifold.BesovAtlas.pieceRadius`, so it lives on the bounded convex Lipschitz domain
  `D_k = O_I ∩ B(0, R_k + 1)` (`Manifold.BesovAtlas.pieceDomain`): it is the zero extension of its
  restriction to `D_k` (`Manifold.BesovAtlas.indicatorExtendLp_neumannEmbedding_toNeumann`).
  Restricting the jets of `u ∈ H^1_A(M)` to `D_k` (`Rd.restrictSubsetLp`) maps `H^1_A(M)` into
  the Neumann space of `D_k` (`Manifold.BesovAtlas.toNeumann`).
* **Rellich's theorem**: `J = ∑_k L_k E_k J^N_k T_k` with the Neumann embeddings `J^N_k` of the
  `D_k` and the zero extensions `E_k` (`Manifold.BesovAtlas.chartSobolevEmbedding_eq_sum`), so `J`
  is compact (`Manifold.BesovAtlas.isCompactOperator_chartSobolevEmbedding`).
* **Density**: lifts of `H^1(E)` functions lie in the range of `J`
  (`Manifold.BesovAtlas.chartLiftLp_toL2_mem_range`), and with `∑_k L_k P_k = id` the range of `J`
  is dense (`Manifold.BesovAtlas.denseRange_chartSobolevEmbedding`).
* **The eigenbasis**: `J` is a compact dense embedding
  (`Manifold.BesovAtlas.chartCompactEmbedding`) with the spectral scheme
  `Manifold.BesovAtlas.chartScheme`, a Hilbert basis `(e_i)` of `L_2(μ)` with eigenvalues
  `λ_i = σ_i⁻² - 1 ≥ 0`, levels `⌊√(1 + λ_i)⌋₊`, only finitely many eigenvalues below each bound
  (`Manifold.BesovAtlas.finite_setOf_chartEigenvalue_le`), and eigenfunctions `φ_i ∈ H^1_A(M)`
  with `J φ_i = e_i`. The eigenfunctions satisfy `a_A(φ_i, w) = λ_i ⟨e_i, J w⟩` for every
  `w ∈ H^1_A(M)` (`Manifold.BesovAtlas.chartForm_eigenfunction`, in integrals
  `Manifold.BesovAtlas.chartForm_eigenfunction_integral`), the weak eigenvalue equation of the
  chart form with the natural boundary condition.
* **`H^1(M)` in the eigenbasis**: `f ∈ B^1_{2,2}(M)` iff
  `∑_i (1 + ⌊√(1 + λ_i)⌋₊)² |⟨e_i, f⟩|² < ∞` (`Manifold.BesovAtlas.memBesov_one_two_iff_spectral`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology TopologicalSpace Module Metric
open scoped ENNReal Manifold ContDiff InnerProductSpace BesselPotentialSpace ComplexConjugate

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

namespace BesovAtlas

variable (A : BesovAtlas I M) {μ : Measure M} [IsSmoothMeasure I μ]

/-! ### The bounded convex piece of a chart -/

variable [Rd.BesovDomain (range I)]

/-- **The bounded convex piece of the `k`-th chart**: `D_k = O_I ∩ B(0, R_k + 1)`, a bounded convex
Lipschitz domain (`Rd.BesovDomain.ballDomain`), which contains the points of the carrier of the
`k`-th piece in the open model set. -/
noncomputable abbrev pieceDomain (k : Fin A.n) : Rd.BoundedLipschitzDomain E :=
  Rd.BesovDomain.ballDomain (range I) (A.pieceRadius k + 1)

omit [MeasurableSpace M] [BorelSpace M] [IsSmoothMeasure I μ] in
/-- The piece `D_k` lies in the open model set `O_I`. -/
theorem pieceDomain_subset_interior (k : Fin A.n) :
    ((A.pieceDomain k).toOpens : Set E) ⊆ interior (range I) :=
  Rd.BesovDomain.ballDomain_subset_interior (range I) _

/-- **The pieces vanish outside `D_k`**: `P_k f = 0` almost everywhere outside
`D_k = O_I ∩ B(0, R_k + 1)`. Outside the carrier `κ_k(tsupport ψ_k) ⊆ range I ∩ B(0, R_k)` the
piece vanishes (`Manifold.BesovAtlas.pieceLp_eq_zero_off`), and `range I \ O_I` is a null set
(`Manifold.modelInterior_ae_eq_range`). -/
theorem pieceLp_eq_zero_off_pieceDomain {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (k : Fin A.n)
    (f : Lp ℂ p μ) :
    ∀ᵐ y ∂volume, y ∉ ((A.pieceDomain k).toOpens : Set E) → A.pieceLp μ hp k f y = 0 := by
  filter_upwards [A.pieceLp_eq_zero_off hp k f, (modelInterior_ae_eq_range I).mem_iff]
    with y h1 h2 hy
  refine h1 fun hc => hy ?_
  exact ⟨h2.2 (A.pieceCarrier_subset_range k hc),
    ball_subset_ball (le_add_of_nonneg_right zero_le_one) (A.pieceCarrier_subset_ball k hc)⟩

/-! ### From the chart Sobolev space to the Neumann spaces of the pieces -/

variable (μ) in
/-- **The jets of the `k`-th piece on `D_k`**: `u = (f, g) ↦ ((P_k f)|_{D_k}, (g_{kj}|_{D_k})_j)`,
a bounded linear operator from the chart Sobolev space to `L_2(D_k) × L_2(D_k)^n`. -/
noncomputable def toNeumannValueGradient (k : Fin A.n) :
    A.chartSobolev μ →L[ℂ] Rd.ValueGradientL2 (A.pieceDomain k).toOpens :=
  let domain := (A.pieceDomain k).toOpens
  let domainMeasure := volume.restrict (domain : Set E)
  let value : A.chartSobolev μ →L[ℂ] Lp ℂ 2 domainMeasure :=
    LpToLpRestrictCLM E ℂ ℂ volume 2 (domain : Set E) ∘L
      A.pieceCLM μ Rd.two_ne_top k ∘L A.chartSobolevEmbedding μ
  let coordinate (j : Fin (finrank ℝ E)) : A.chartSobolev μ →L[ℂ] Lp ℂ 2 domainMeasure :=
    Rd.restrictSubsetLp domain.isOpen.measurableSet (A.pieceDomain_subset_interior k) ∘L
      PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin A.n × Fin (finrank ℝ E) =>
        Lp ℂ 2 (volume.restrict (interior (range I)))) (k, j) ∘L
      WithLp.sndL 2 ℂ _ _ ∘L (A.chartSobolev μ).subtypeL
  let gradient : A.chartSobolev μ →L[ℂ] PiLp 2
      (fun _ : Fin (finrank ℝ E) => Lp ℂ 2 domainMeasure) :=
    (PiLp.continuousLinearEquiv 2 ℂ _).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.pi coordinate
  (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm.toContinuousLinearMap ∘L value.prod gradient

/-- The jets of the `k`-th piece on `D_k` lie in the Neumann space of `D_k`: weak derivatives on
`O_I` are weak derivatives on `D_k ⊆ O_I` (`Rd.HasWeakLineDeriv.mono`). -/
theorem toNeumannValueGradient_mem (k : Fin A.n) (u : A.chartSobolev μ) :
    A.toNeumannValueGradient μ k u ∈ Rd.neumannSpace (A.pieceDomain k).toOpens := fun j =>
  ((u.2 (k, j)).mono (Rd.BesovDomain.toOpens_ballDomain_le (range I) _)).congr_ae
    (LpToLpRestrictCLM_coeFn ℂ _ _).symm (Rd.restrictSubsetLp_ae _ _ _).symm

variable (μ) in
/-- **From the chart Sobolev space to the Neumann space of `D_k`**: `u = (f, g) ↦
((P_k f)|_{D_k}, (g_{kj}|_{D_k})_j)`, a bounded linear operator into `W^1_2(D_k)`. -/
noncomputable def toNeumann (k : Fin A.n) :
    A.chartSobolev μ →L[ℂ] Rd.neumannSpace (A.pieceDomain k).toOpens :=
  (A.toNeumannValueGradient μ k).codRestrict _ (A.toNeumannValueGradient_mem k)

/-- The value of `toNeumann k u` is the restriction to `D_k` of the piece `P_k (J u)`. -/
theorem neumannEmbedding_toNeumann (k : Fin A.n) (u : A.chartSobolev μ) :
    Rd.neumannEmbedding (A.pieceDomain k).toOpens (A.toNeumann μ k u) =
      LpToLpRestrictCLM E ℂ ℂ volume 2 ((A.pieceDomain k).toOpens : Set E)
        (A.pieceLp μ Rd.two_ne_top k (A.chartSobolevEmbedding μ u)) :=
  rfl

/-- **The piece is the zero extension of its restriction to `D_k`**: `E_k J^N_k T_k u = P_k (J u)`,
since `P_k (J u)` vanishes outside `D_k` (`Manifold.BesovAtlas.pieceLp_eq_zero_off_pieceDomain`,
`Rd.indicatorExtendLp_restrict_of_ae_eq_zero`). -/
theorem indicatorExtendLp_neumannEmbedding_toNeumann (k : Fin A.n) (u : A.chartSobolev μ) :
    Rd.indicatorExtendLp (A.pieceDomain k).toOpens.isOpen.measurableSet subset_rfl
        (Rd.neumannEmbedding (A.pieceDomain k).toOpens (A.toNeumann μ k u)) =
      A.pieceLp μ Rd.two_ne_top k (A.chartSobolevEmbedding μ u) := by
  rw [neumannEmbedding_toNeumann]
  exact Rd.indicatorExtendLp_restrict_of_ae_eq_zero _
    (A.pieceLp_eq_zero_off_pieceDomain Rd.two_ne_top k _)

/-! ### Rellich's theorem -/

/-- **The chart Sobolev embedding through the Neumann spaces of the pieces**:
`J = ∑_k L_k ∘ E_k ∘ J^N_k ∘ T_k`, with `T_k` the restriction of the jets to `D_k`
(`Manifold.BesovAtlas.toNeumann`), `J^N_k` the Neumann embedding of `D_k` and `E_k` the zero
extension; by the retract identity `∑_k L_k P_k = id`
(`Manifold.BesovAtlas.sum_chartLiftLp_pieceLp`) and
`Manifold.BesovAtlas.indicatorExtendLp_neumannEmbedding_toNeumann`. -/
theorem chartSobolevEmbedding_eq_sum :
    A.chartSobolevEmbedding μ = ∑ k, A.chartLiftCLM μ Rd.two_ne_top k ∘L
      (Rd.indicatorExtendLp (A.pieceDomain k).toOpens.isOpen.measurableSet subset_rfl ∘L
        (Rd.neumannEmbedding (A.pieceDomain k).toOpens ∘L A.toNeumann μ k)) := by
  ext1 u
  rw [FunLike.coe_sum, Finset.sum_apply]
  conv_lhs => rw [← A.sum_chartLiftLp_pieceLp Rd.two_ne_top (A.chartSobolevEmbedding μ u)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, A.indicatorExtendLp_neumannEmbedding_toNeumann k u]
  rfl

/-- **Rellich's theorem for the chart Sobolev space**: for a compact manifold whose model range is
a Besov domain in dimension `n ≥ 1`, the embedding `J : H^1_A(M) → L_2(μ)` is compact. Each
summand of `J = ∑_k L_k E_k J^N_k T_k` (`Manifold.BesovAtlas.chartSobolevEmbedding_eq_sum`)
contains the Neumann embedding `J^N_k` of the bounded convex Lipschitz domain `D_k`, which is
compact (`Rd.BoundedLipschitzDomain.isCompactOperator_neumannEmbedding`); compact operators form a
subspace (Mathlib's `compactOperator`, `IsCompactOperator.comp_clm`, `IsCompactOperator.clm_comp`).
The same proof covers manifolds with and without boundary. -/
theorem isCompactOperator_chartSobolevEmbedding [Nontrivial E] :
    IsCompactOperator (A.chartSobolevEmbedding μ) := by
  rw [A.chartSobolevEmbedding_eq_sum]
  refine (compactOperator (RingHom.id ℂ) (A.chartSobolev μ) (Lp ℂ 2 μ)).sum_mem fun k _ => ?_
  change IsCompactOperator _
  exact ((((A.pieceDomain k).isCompactOperator_neumannEmbedding).comp_clm
    (A.toNeumann μ k)).clm_comp
      (Rd.indicatorExtendLp (A.pieceDomain k).toOpens.isOpen.measurableSet subset_rfl)).clm_comp
        (A.chartLiftCLM μ Rd.two_ne_top k)

/-! ### Density -/

/-- **Lifts of `H^1(E)` functions are values of the chart Sobolev embedding**: for every
`U ∈ H^1(E)` and every chart index `k`, `L_k (ι U) = J u` for some `u ∈ H^1_A(M)`. The function
`ι U` has finite `B^1_{2,2}(E)` quasi-norm (`Rd.memSobolev_toL2`, `Rd.memSobolev_one_iff_modulus`),
so its lift lies in `B^1_{2,2}(M)` (`Manifold.BesovAtlas.memBesov_chartLiftLp`), which is the range
of `J` (`Manifold.BesovAtlas.mem_range_chartSobolevEmbedding_iff_memBesov`). -/
theorem chartLiftLp_toL2_mem_range [IsManifold I ∞ M] (k : Fin A.n) (U : H^{1}(E)) :
    A.chartLiftLp μ Rd.two_ne_top k (Rd.toL2 U) ∈ range (A.chartSobolevEmbedding μ) := by
  rw [A.mem_range_chartSobolevEmbedding_iff_memBesov]
  exact A.memBesov_chartLiftLp Rd.two_ne_top k (r := 2) one_le_two one_pos (by norm_num)
    one_le_two ((Rd.memSobolev_one_iff_modulus le_rfl _).1 (Rd.memSobolev_toL2 U))

/-- **The chart Sobolev embedding has dense range**: every `f ∈ L_2(μ)` is `∑_k L_k P_k f`
(`Manifold.BesovAtlas.sum_chartLiftLp_pieceLp`); the Schwartz functions are dense in `L_2(E)`
(Mathlib's `SchwartzMap.denseRange_toLpCLM`), they lie in `H^1(E)` (`Rd.toL2_ofSchwartz`), and
their lifts are values of `J` (`Manifold.BesovAtlas.chartLiftLp_toL2_mem_range`). So each
`L_k P_k f` lies in the closure of the range of `J`, and so does their sum. -/
theorem denseRange_chartSobolevEmbedding [IsManifold I ∞ M] :
    DenseRange (A.chartSobolevEmbedding μ) := by
  intro f
  set W := LinearMap.range (A.chartSobolevEmbedding μ : A.chartSobolev μ →ₗ[ℂ] Lp ℂ 2 μ)
  have hW : ∀ k, A.chartLiftLp μ Rd.two_ne_top k (A.pieceLp μ Rd.two_ne_top k f) ∈
      W.topologicalClosure := fun k => by
    refine DenseRange.induction_on (SchwartzMap.denseRange_toLpCLM (F := ℂ)
      (μ := (volume : Measure E)) Rd.two_ne_top) (A.pieceLp μ Rd.two_ne_top k f)
      (W.isClosed_topologicalClosure.preimage (A.chartLiftCLM μ Rd.two_ne_top k).continuous)
      fun φ => W.le_topologicalClosure ?_
    have h := A.chartLiftLp_toL2_mem_range (μ := μ) k (Rd.ofSchwartz 1 φ)
    rw [Rd.toL2_ofSchwartz] at h
    rw [SchwartzMap.toLpCLM_apply]
    exact h
  have hsum := W.topologicalClosure.sum_mem fun k (_ : k ∈ Finset.univ) => hW k
  rw [A.sum_chartLiftLp_pieceLp] at hsum
  rwa [← SetLike.mem_coe, Submodule.topologicalClosure_coe, LinearMap.coe_range] at hsum

/-! ### The eigenbasis of the chart form -/

variable [Nontrivial E] [IsManifold I ∞ M]

variable (μ) in
/-- **`H^1_A(M) ↪ L_2(μ)` as a compact dense embedding**, for a compact manifold whose model range
is a Besov domain in dimension `n ≥ 1`
(`Manifold.BesovAtlas.isCompactOperator_chartSobolevEmbedding`,
`Manifold.BesovAtlas.chartSobolevEmbedding_injective`,
`Manifold.BesovAtlas.denseRange_chartSobolevEmbedding`). -/
noncomputable def chartCompactEmbedding :
    @CompactDenseEmbedding (A.chartSobolev μ) (Lp ℂ 2 μ)
      (Submodule.normedAddCommGroup (A.chartSobolev μ))
      (Submodule.innerProductSpace (A.chartSobolev μ)) inferInstance inferInstance where
  toCLM := A.chartSobolevEmbedding μ
  isCompact := A.isCompactOperator_chartSobolevEmbedding
  injective := A.chartSobolevEmbedding_injective
  denseRange := A.denseRange_chartSobolevEmbedding

/-- The embedding of `Manifold.BesovAtlas.chartCompactEmbedding` is the chart Sobolev
embedding. -/
@[simp]
theorem chartCompactEmbedding_toCLM :
    (A.chartCompactEmbedding μ).toCLM = A.chartSobolevEmbedding μ :=
  rfl

variable (μ) in
/-- **The eigenbasis of the chart form as a spectral scheme**: the Hilbert basis `(e_i)` of
`L_2(μ)` of eigenvectors of `J J†`, `J` the chart Sobolev embedding, with the levels `⌊σ_i⁻¹⌋₊` of
the singular values (`CompactDenseEmbedding.spectralScheme`). With the chart form in the inner
product of `H^1_A(M)`, `σ_i⁻² = 1 + λ_i` for the eigenvalue `λ_i` of the chart form
(`Manifold.BesovAtlas.one_add_chartEigenvalue`), so the level is `⌊√(1 + λ_i)⌋₊`
(`Manifold.BesovAtlas.chartScheme_level`). -/
noncomputable def chartScheme :
    SpectralScheme (A.chartCompactEmbedding μ).index (Lp ℂ 2 μ) :=
  (A.chartCompactEmbedding μ).spectralScheme

/-- The singular values of the chart Sobolev embedding are at most `1`
(`Manifold.BesovAtlas.norm_chartSobolevEmbedding_le`). -/
theorem singularValue_chartCompactEmbedding_le_one (i : (A.chartCompactEmbedding μ).index) :
    (A.chartCompactEmbedding μ).singularValue i ≤ 1 :=
  ((A.chartCompactEmbedding μ).singularValue_le_norm i).trans A.norm_chartSobolevEmbedding_le

variable (μ) in
/-- **The eigenvalue of the chart form** `λ_i = σ_i⁻² - 1` of the index `i`, `σ_i` the singular
value of the chart Sobolev embedding; `a_A(φ_i, w) = λ_i ⟨e_i, J w⟩` for every `w`
(`Manifold.BesovAtlas.chartForm_eigenfunction`). -/
noncomputable def chartEigenvalue (i : (A.chartCompactEmbedding μ).index) : ℝ :=
  ((A.chartCompactEmbedding μ).singularValue i)⁻¹ ^ 2 - 1

/-- The eigenvalues of the chart form are nonnegative, since `σ_i ≤ 1`
(`Manifold.BesovAtlas.singularValue_chartCompactEmbedding_le_one`). -/
theorem chartEigenvalue_nonneg (i : (A.chartCompactEmbedding μ).index) :
    0 ≤ A.chartEigenvalue μ i := by
  have h1 : 1 ≤ ((A.chartCompactEmbedding μ).singularValue i)⁻¹ :=
    one_le_inv_iff₀.2 ⟨(A.chartCompactEmbedding μ).singularValue_pos i,
      A.singularValue_chartCompactEmbedding_le_one i⟩
  have h2 : 1 ≤ ((A.chartCompactEmbedding μ).singularValue i)⁻¹ ^ 2 := one_le_pow₀ h1
  unfold chartEigenvalue
  linarith

/-- `1 + λ_i = σ_i⁻²`. -/
theorem one_add_chartEigenvalue (i : (A.chartCompactEmbedding μ).index) :
    1 + A.chartEigenvalue μ i = ((A.chartCompactEmbedding μ).singularValue i)⁻¹ ^ 2 := by
  unfold chartEigenvalue
  ring

/-- `σ_i⁻¹ = √(1 + λ_i)`. -/
theorem inv_singularValue_eq_sqrt (i : (A.chartCompactEmbedding μ).index) :
    ((A.chartCompactEmbedding μ).singularValue i)⁻¹ = Real.sqrt (1 + A.chartEigenvalue μ i) := by
  rw [one_add_chartEigenvalue, Real.sqrt_sq
    (inv_nonneg.2 ((A.chartCompactEmbedding μ).singularValue_pos i).le)]

/-- **The level of an eigenfunction of the chart form** is `⌊√(1 + λ_i)⌋₊`. -/
theorem chartScheme_level (i : (A.chartCompactEmbedding μ).index) :
    (A.chartScheme μ).level i = ⌊Real.sqrt (1 + A.chartEigenvalue μ i)⌋₊ := by
  rw [← inv_singularValue_eq_sqrt]
  rfl

/-- **Finitely many eigenvalues below each bound**: for every `Λ`, only finitely many indices have
`λ_i ≤ Λ`, since then the level `⌊√(1 + λ_i)⌋₊` is at most `⌊√(1 + Λ)⌋₊`
(`Manifold.BesovAtlas.chartScheme_level`, `SpectralScheme.finite_level`). -/
theorem finite_setOf_chartEigenvalue_le (Λ : ℝ) :
    {i | A.chartEigenvalue μ i ≤ Λ}.Finite :=
  ((A.chartScheme μ).finite_level (⌊Real.sqrt (1 + Λ)⌋₊ + 1)).subset fun i hi => by
    change (A.chartScheme μ).level i < _
    rw [A.chartScheme_level i]
    exact Nat.lt_succ_of_le (Nat.floor_mono (Real.sqrt_le_sqrt (by linarith [hi.out])))

variable (μ) in
/-- **The eigenfunction of the chart form** `φ_i = σ_i⁻¹ v_i ∈ H^1_A(M)`, `v_i` the singular basis
of the chart Sobolev embedding; its value is the basis vector `e_i` of `L_2(μ)`
(`Manifold.BesovAtlas.chartSobolevEmbedding_chartEigenfunction`). -/
noncomputable def chartEigenfunction (i : (A.chartCompactEmbedding μ).index) : A.chartSobolev μ :=
  ((((A.chartCompactEmbedding μ).singularValue i)⁻¹ : ℝ) : ℂ) •
    (A.chartCompactEmbedding μ).singularBasis i

/-- **`J φ_i = e_i`**: the chart Sobolev embedding maps the eigenfunction `φ_i` to the basis vector
`e_i` of the chart scheme, since `J v_i = σ_i e_i` (`CompactDenseEmbedding.apply_singularBasis`). -/
theorem chartSobolevEmbedding_chartEigenfunction (i : (A.chartCompactEmbedding μ).index) :
    A.chartSobolevEmbedding μ (A.chartEigenfunction μ i) = (A.chartScheme μ).basis i := by
  have h := (A.chartCompactEmbedding μ).apply_singularBasis i
  rw [chartCompactEmbedding_toCLM] at h
  rw [chartEigenfunction, map_smul, h, smul_smul, ← Complex.ofReal_mul,
    inv_mul_cancel₀ ((A.chartCompactEmbedding μ).singularValue_pos i).ne', Complex.ofReal_one,
    one_smul]
  rfl

/-! ### The weak eigenvalue equation of the chart form -/

/-- **The weak eigenvalue equation of the chart form**: for every index `i` and every
`w ∈ H^1_A(M)`, `a_A(φ_i, w) = λ_i ⟨e_i, J w⟩_{L_2(μ)}`, with the chart form `a_A`
(`Manifold.BesovAtlas.chartForm`). It is the weak eigenvalue equation
`⟨v_i, w⟩ = σ_i⁻² ⟨J v_i, J w⟩` of the singular basis
(`CompactDenseEmbedding.inner_singularBasis`) with the inner product
`⟨u, w⟩ = ⟨J u, J w⟩ + a_A(u, w)` of `H^1_A(M)` (`Manifold.BesovAtlas.inner_chartSobolev`). The
test functions `w` are arbitrary near the boundary of `M`, so the boundary condition is the natural
one. -/
theorem chartForm_eigenfunction (i : (A.chartCompactEmbedding μ).index) (w : A.chartSobolev μ) :
    A.chartForm μ (A.chartEigenfunction μ i) w =
      (A.chartEigenvalue μ i : ℂ) * ⟪(A.chartScheme μ).basis i, A.chartSobolevEmbedding μ w⟫_ℂ := by
  have hφ : ⟪A.chartEigenfunction μ i, w⟫_ℂ =
      ((((A.chartCompactEmbedding μ).singularValue i)⁻¹ ^ 2 : ℝ) : ℂ) *
        ⟪A.chartSobolevEmbedding μ (A.chartEigenfunction μ i), A.chartSobolevEmbedding μ w⟫_ℂ := by
    -- the scalar multiplication of the subspace matches `inner_smul_left` up to unfolding
    -- instances, so the lemma is applied by unification instead of rewriting
    refine (inner_smul_left (𝕜 := ℂ) (E := A.chartSobolev μ)
      ((A.chartCompactEmbedding μ).singularBasis i) w _).trans ?_
    rw [chartEigenfunction, map_smul, inner_smul_left,
      (A.chartCompactEmbedding μ).inner_singularBasis i w, chartCompactEmbedding_toCLM]
    ring
  rw [A.inner_chartSobolev] at hφ
  rw [← A.chartSobolevEmbedding_chartEigenfunction i]
  change _ = _ * ⟪A.chartSobolevEmbedding μ (A.chartEigenfunction μ i),
    A.chartSobolevEmbedding μ w⟫_ℂ
  rw [chartSobolevEmbedding_apply, chartSobolevEmbedding_apply] at hφ ⊢
  unfold chartEigenvalue
  push_cast at hφ ⊢
  linear_combination hφ

omit [Rd.BesovDomain (range I)] [Nontrivial E] [IsManifold I ∞ M] in
/-- **The chart form as a sum of integrals**: for `u = (f, g)` and `w = (f', g')` in the chart
Sobolev space, `a_A(u, w) = ∑_{k,j} ∫_{O_I} conj (g_{kj}) g'_{kj}` (Mathlib's
`MeasureTheory.L2.inner_def`, `RCLike.inner_apply'`). -/
theorem chartForm_eq_sum_integral (u w : A.chartSobolev μ) :
    A.chartForm μ u w = ∑ ij, ∫ y in interior (range I),
      conj ((u : A.chartValueGradientL2 μ).snd ij y) * (w : A.chartValueGradientL2 μ).snd ij y := by
  simp only [chartForm, MeasureTheory.L2.inner_def, RCLike.inner_apply']

/-- **The weak eigenvalue equation in integrals**: for every index `i` and every
`w = (f', g') ∈ H^1_A(M)`, with `φ_i = (e_i, g)`,
`∑_{k,j} ∫_{O_I} conj (g_{kj}) g'_{kj} = λ_i ∫_M conj (e_i) f' dμ`, where
`g_{kj} = ∂_{b_j} P_k e_i` weakly on `O_I` (`Manifold.BesovAtlas.chartForm_eigenfunction`,
`Manifold.BesovAtlas.chartForm_eq_sum_integral`). -/
theorem chartForm_eigenfunction_integral (i : (A.chartCompactEmbedding μ).index)
    (w : A.chartSobolev μ) :
    ∑ ij, ∫ y in interior (range I),
        conj ((A.chartEigenfunction μ i : A.chartValueGradientL2 μ).snd ij y) *
          (w : A.chartValueGradientL2 μ).snd ij y =
      (A.chartEigenvalue μ i : ℂ) *
        ∫ x, conj ((A.chartScheme μ).basis i x) * A.chartSobolevEmbedding μ w x ∂μ := by
  rw [← chartForm_eq_sum_integral, chartForm_eigenfunction, MeasureTheory.L2.inner_def]
  simp only [RCLike.inner_apply']

/-! ### `H^1(M)` in the eigenbasis -/

/-- **The chart Sobolev space in the eigenbasis**: `f ∈ L_2(μ)` is a value of the chart Sobolev
embedding iff `∑_i (1 + ⌊√(1 + λ_i)⌋₊)² |⟨e_i, f⟩|² < ∞`. This is the Sobolev space of order `1`
of the chart scheme (`CompactDenseEmbedding.range_eq_range_sobolevEmbed`,
`SpectralScheme.mem_range_sobolevEmbed_iff`), whose levels are `⌊√(1 + λ_i)⌋₊`
(`Manifold.BesovAtlas.chartScheme_level`). -/
theorem mem_range_chartSobolevEmbedding_iff_spectral (f : Lp ℂ 2 μ) :
    f ∈ range (A.chartSobolevEmbedding μ) ↔
      Memℓp (fun i => ((1 + ⌊Real.sqrt (1 + A.chartEigenvalue μ i)⌋₊ : ℕ) : ℂ) *
        (A.chartScheme μ).basis.repr f i) 2 := by
  simp only [← A.chartScheme_level]
  -- unfolding the scheme first keeps the definitional unfolding in the rewrites cheap
  unfold chartScheme
  have hw : ∀ i, (((A.chartCompactEmbedding μ).spectralScheme.weight 1 i : ℝ) : ℂ) =
      ((1 + (A.chartCompactEmbedding μ).spectralScheme.level i : ℕ) : ℂ) := fun i => by
    simp [SpectralScheme.weight]
  refine ((Set.ext_iff.1 (A.chartCompactEmbedding μ).range_eq_range_sobolevEmbed f).trans
    ((A.chartCompactEmbedding μ).spectralScheme.mem_range_sobolevEmbed_iff 1 zero_le_one f)).trans
      ?_
  simp only [hw]

/-- **`H^1(M) = B^1_{2,2}(M)` in the eigenbasis of the chart form**: `f ∈ B^1_{2,2}(M)` iff
`∑_i (1 + ⌊√(1 + λ_i)⌋₊)² |⟨e_i, f⟩|² < ∞`
(`Manifold.BesovAtlas.mem_range_chartSobolevEmbedding_iff`,
`Manifold.BesovAtlas.mem_range_chartSobolevEmbedding_iff_spectral`). -/
theorem memBesov_one_two_iff_spectral [T2Space M] (f : Lp ℂ 2 μ) :
    Manifold.MemBesov I μ Rd.two_ne_top 1 2 f ↔
      Memℓp (fun i => ((1 + ⌊Real.sqrt (1 + A.chartEigenvalue μ i)⌋₊ : ℕ) : ℂ) *
        (A.chartScheme μ).basis.repr f i) 2 :=
  (A.mem_range_chartSobolevEmbedding_iff f).symm.trans
    (A.mem_range_chartSobolevEmbedding_iff_spectral f)

end BesovAtlas

end Manifold
