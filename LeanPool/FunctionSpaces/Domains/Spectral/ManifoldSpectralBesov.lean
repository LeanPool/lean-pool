/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Spectral.ChartFormEigenbasis
public import LeanPool.FunctionSpaces.Domains.Spectral.SpectralBesov
public import LeanPool.FunctionSpaces.Domains.Manifolds.SmoothLocalGraphs
public import LeanPool.FunctionSpaces.Domains.Manifolds.SmoothMeasureExistence

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Besov spaces on compact manifolds by eigenfunction expansions

Let `M` be a compact manifold with model `I` whose range `Ω_I = range I` is a Besov domain, of
dimension `n = dim E ≥ 1`, with a smooth measure `μ` and a Besov atlas `A`; `P_k` are the pieces,
`L_k` the lifts, `J : H^1_A(M) → L_2(μ)` the chart Sobolev embedding and `(e_i)` the eigenbasis of
the chart form (`Manifold.BesovAtlas.chartScheme`). Let `0 < θ < 1` and `1 ≤ q ≤ ∞`.

* **The pieces of interpolation functions**: `P_k` followed by the restriction to the bounded
  convex piece `D_k` maps the couple `(L_2(μ), J(H^1_A(M)))` into the Neumann couple of `D_k`
  (`Manifold.BesovAtlas.memKMethod_neumann_pieceLp_of_memKMethod`), so every piece of
  `f ∈ (L_2(μ), H^1_A(M))_{θ,q}` has a finite intrinsic `B^θ_{2,q}(Ω_I)` quasi-norm
  (`Manifold.BesovAtlas.modNormOn_pieceLp_lt_top_of_memKMethod`).
* **Lifts map couples**: `U ↦ J⁻¹ (L_k ι U)` is a bounded linear operator `H^1(E) → H^1_A(M)`
  by the closed graph theorem (`Manifold.BesovAtlas.chartLiftSobolev`), so `L_k` maps
  `(L_2(E), H^1(E))_{θ,q}` into `(L_2(μ), H^1_A(M))_{θ,q}`
  (`Manifold.BesovAtlas.memKMethod_chartLiftLp`).
* **The couple by the pieces**: `f ∈ (L_2(μ), H^1_A(M))_{θ,q}` iff every piece has a finite
  intrinsic quasi-norm (`Manifold.BesovAtlas.memKMethod_chartSobolev_iff`); the converse extends
  the pieces to `E`, lifts them and sums with `∑_k L_k P_k = id`.
* **The main theorem** (`Manifold.BesovAtlas.memApprox_chartScheme_iff`): `f ∈ B^θ_{2,q}(M)` iff
  `f` lies in the approximation space `A^θ_q` of the eigenbasis of the chart form; equivalently
  `‖P_1 f‖_2 + ‖(2^(kθ) ‖Δ_k f‖_2)_k‖_{ℓ_q} < ∞` for the dyadic blocks `Δ_k f` of its
  eigenfunction expansion (`Manifold.BesovAtlas.memBesov_iff_blockNorm_lt_top`), and for `q = 2`,
  `∑_i (1 + λ_i)^θ |⟨e_i, f⟩|² < ∞` (`Manifold.BesovAtlas.memBesov_two_iff_chartEigenvalue`).
* **Smooth domains**: on the closure of a bounded smooth domain `Ω ⊆ ℝ^n`, the approximation
  spaces of the chart scheme are the intrinsic `B^θ_{2,q}(Ω)`
  (`Rd.SmoothDomain.memApprox_chartScheme_iff_modNormOn`), for example on the closed ball
  (`Rd.SmoothDomain.memApprox_chartScheme_ball_iff`).
* **The sphere**: on the sphere `S^n`, `n ≥ 1`, a compact manifold without boundary, with the
  chart measure of a Besov atlas, the approximation spaces of the chart scheme are
  `B^θ_{2,q}(S^n)` (`Manifold.memApprox_chartScheme_sphere_iff`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology TopologicalSpace Module Metric
open scoped ENNReal Manifold ContDiff BesselPotentialSpace

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [Rd.BesovDomain (range I)] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

namespace BesovAtlas

variable (A : BesovAtlas I M) {μ : Measure M} [IsSmoothMeasure I μ] {θ : ℝ} {q : ℝ≥0∞}

/-! ### The pieces of interpolation functions -/

omit [Nontrivial E] [IsManifold I ∞ M] in
/-- **The pieces map the chart couple into the Neumann couples**: if `f ∈ L_2(μ)` lies in
`(L_2(μ), H^1_A(M))_{θ,q}`, then `(P_k f)|_{D_k}` lies in `(L_2(D_k), W^1_2(D_k))_{θ,q}`. The
operators `f ↦ (P_k f)|_{D_k}` on `L_2(μ)` and `T_k` (`Manifold.BesovAtlas.toNeumann`) on
`H^1_A(M)` are compatible with the embeddings (`Manifold.BesovAtlas.neumannEmbedding_toNeumann`),
so the interpolation property applies (`ApproximationScheme.MemKMethod.map`). -/
theorem memKMethod_neumann_pieceLp_of_memKMethod {f : Lp ℂ 2 μ}
    (hf : (InterpCouple.ofMap ((A.chartSobolevEmbedding μ).restrictScalars ℝ)).MemKMethod θ q f)
    (k : Fin A.n) :
    (InterpCouple.ofMap
      ((Rd.neumannEmbedding (A.pieceDomain k).toOpens).restrictScalars ℝ)).MemKMethod θ q
      (LpToLpRestrictCLM E ℂ ℂ volume 2 ((A.pieceDomain k).toOpens : Set E)
        (A.pieceLp μ Rd.two_ne_top k f)) := by
  refine InterpCouple.memKMethod_ofMap_iff.2 (ApproximationScheme.MemKMethod.map
    ((LpToLpRestrictCLM E ℂ ℂ volume 2 ((A.pieceDomain k).toOpens : Set E) ∘L
      A.pieceCLM μ Rd.two_ne_top k).restrictScalars ℝ)
    ((A.toNeumann μ k).restrictScalars ℝ) ?_ (InterpCouple.memKMethod_ofMap_iff.1 hf))
  ext1 u
  exact (A.neumannEmbedding_toNeumann k u).symm

omit [IsManifold I ∞ M] in
/-- **The pieces of interpolation functions are Besov on `Ω_I`**: for `0 < θ < 1`, `1 ≤ q ≤ ∞`,
every order `r ≥ 1` and every `f ∈ (L_2(μ), H^1_A(M))_{θ,q}`, every piece `P_k f` has a finite
intrinsic quasi-norm `N_{Ω_I}(P_k f)` with moduli of order `r`. The restriction of `P_k f` to
`D_k` lies in the Neumann approximation space
(`Manifold.BesovAtlas.memKMethod_neumann_pieceLp_of_memKMethod`,
`Rd.BoundedLipschitzDomain.memKMethod_neumann_iff`), so `N_{D_k}(P_k f) < ∞`
(`Rd.BoundedLipschitzDomain.memApprox_neumannScheme_iff`), and `P_k f` vanishes outside
`B(0, R_k)` (`Rd.BesovDomain.modNormOn_lt_top_iff_ballDomain`). -/
theorem modNormOn_pieceLp_lt_top_of_memKMethod (hθ : 0 < θ) (hθ' : θ < 1) (hq : 1 ≤ q)
    {r : ℕ} (hr : 1 ≤ r) {f : Lp ℂ 2 μ}
    (hf : (InterpCouple.ofMap ((A.chartSobolevEmbedding μ).restrictScalars ℝ)).MemKMethod θ q f)
    (k : Fin A.n) :
    Rd.modNormOn (Rd.BesovDomain.measurableSet (range I)) r θ q (A.pieceLp μ Rd.two_ne_top k f) <
      ⊤ := by
  have h1 := ((A.pieceDomain k).memKMethod_neumann_iff hθ hθ' hq).1
    (A.memKMethod_neumann_pieceLp_of_memKMethod hf k)
  have h2 := ((A.pieceDomain k).memApprox_neumannScheme_iff hθ hθ' hq hr _).1 h1
  exact (Rd.BesovDomain.modNormOn_lt_top_iff_ballDomain (Ω := range I) Rd.two_ne_top hθ
    (hθ'.trans_le (Nat.one_le_cast.2 hr)) hq (lt_add_one _)
    (A.pieceLp_eq_zero_off_ball Rd.two_ne_top k f)).2 h2

/-! ### Lifts map couples -/

variable (μ) in
/-- **The lift on `H^1(E)` as a linear map into the chart Sobolev space**: `U ↦ J⁻¹ (L_k ι U)`,
well defined since `L_k ι U` lies in the range of the injective `J`
(`Manifold.BesovAtlas.chartLiftLp_toL2_mem_range`, Mathlib's `LinearEquiv.ofInjective`). -/
noncomputable def chartLiftSobolevLinear (k : Fin A.n) : H^{1}(E) →ₗ[ℂ] A.chartSobolev μ :=
  (LinearEquiv.ofInjective (A.chartSobolevEmbedding μ : A.chartSobolev μ →ₗ[ℂ] Lp ℂ 2 μ)
      A.chartSobolevEmbedding_injective).symm.toLinearMap ∘ₗ
    ((A.chartLiftCLM μ Rd.two_ne_top k ∘L Rd.toL2 : H^{1}(E) →L[ℂ] Lp ℂ 2 μ) :
      H^{1}(E) →ₗ[ℂ] Lp ℂ 2 μ).codRestrict _
      fun U => LinearMap.mem_range.2 (A.chartLiftLp_toL2_mem_range k U)

omit [Nontrivial E] in
/-- `J (chartLiftSobolevLinear k U) = L_k ι U`. -/
theorem chartSobolevEmbedding_chartLiftSobolevLinear (k : Fin A.n) (U : H^{1}(E)) :
    A.chartSobolevEmbedding μ (A.chartLiftSobolevLinear μ k U) =
      A.chartLiftLp μ Rd.two_ne_top k (Rd.toL2 U) := by
  have h := LinearEquiv.ofInjective_apply
    (A.chartSobolevEmbedding μ : A.chartSobolev μ →ₗ[ℂ] Lp ℂ 2 μ)
    (h := A.chartSobolevEmbedding_injective) (A.chartLiftSobolevLinear μ k U)
  rw [chartLiftSobolevLinear, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] at h
  exact h.symm

omit [Nontrivial E] in
/-- **The graph of the lift is closed**: `u = J⁻¹ (L_k ι U)` iff `J u = L_k ι U`, a closed
condition in `(U, u)` since `J`, `L_k` and `ι` are continuous. -/
theorem isClosed_graph_chartLiftSobolevLinear (k : Fin A.n) :
    IsClosed ((A.chartLiftSobolevLinear μ k).graph : Set (H^{1}(E) × A.chartSobolev μ)) := by
  have hset : ((A.chartLiftSobolevLinear μ k).graph : Set (H^{1}(E) × A.chartSobolev μ)) =
      {x | A.chartSobolevEmbedding μ x.2 = (A.chartLiftCLM μ Rd.two_ne_top k ∘L Rd.toL2) x.1} := by
    ext x
    rw [SetLike.mem_coe, LinearMap.mem_graph_iff, mem_ofPred_eq, ContinuousLinearMap.comp_apply,
      chartLiftCLM_apply, ← A.chartSobolevEmbedding_chartLiftSobolevLinear k x.1]
    exact (A.chartSobolevEmbedding_injective.eq_iff).symm
  rw [hset]
  exact isClosed_eq ((A.chartSobolevEmbedding μ).continuous.comp continuous_snd)
    ((A.chartLiftCLM μ Rd.two_ne_top k ∘L Rd.toL2).continuous.comp continuous_fst)

variable (μ) in
/-- **The lift `H^1(E) → H^1_A(M)`**: `U ↦ J⁻¹ (L_k ι U)` is a bounded linear operator, by the
closed graph theorem (Mathlib's `ContinuousLinearMap.ofIsClosedGraph`,
`Manifold.BesovAtlas.isClosed_graph_chartLiftSobolevLinear`). -/
noncomputable def chartLiftSobolev (k : Fin A.n) : H^{1}(E) →L[ℂ] A.chartSobolev μ :=
  ContinuousLinearMap.ofIsClosedGraph (A.isClosed_graph_chartLiftSobolevLinear k)

omit [Nontrivial E] in
/-- **`J ∘ S_k = L_k ∘ ι`**: the chart Sobolev embedding of the lift of `U ∈ H^1(E)` is the lift
`L_k ι U` of its `L_2` function. -/
theorem chartSobolevEmbedding_chartLiftSobolev (k : Fin A.n) (U : H^{1}(E)) :
    A.chartSobolevEmbedding μ (A.chartLiftSobolev μ k U) =
      A.chartLiftLp μ Rd.two_ne_top k (Rd.toL2 U) :=
  A.chartSobolevEmbedding_chartLiftSobolevLinear k U

omit [Nontrivial E] in
/-- **Lifts map the whole-space couple into the chart couple**: for every chart index `k` and every
`F ∈ (L_2(E), H^1(E))_{θ,q}`, the lift `L_k F` lies in `(L_2(μ), H^1_A(M))_{θ,q}`. The bounded
operators `L_k` and `S_k` (`Manifold.BesovAtlas.chartLiftSobolev`) satisfy `L_k ι = J S_k`, so the
interpolation property applies (`ApproximationScheme.MemKMethod.map`). -/
theorem memKMethod_chartLiftLp {F : Lp ℂ 2 (volume : Measure E)}
    (hF : (InterpCouple.ofMap
      ((Rd.toL2 : H^{1}(E) →L[ℂ] Lp ℂ 2 (volume : Measure E)).restrictScalars ℝ)).MemKMethod
        θ q F) (k : Fin A.n) :
    (InterpCouple.ofMap ((A.chartSobolevEmbedding μ).restrictScalars ℝ)).MemKMethod θ q
      (A.chartLiftLp μ Rd.two_ne_top k F) := by
  refine InterpCouple.memKMethod_ofMap_iff.2 (ApproximationScheme.MemKMethod.map
    ((A.chartLiftCLM μ Rd.two_ne_top k).restrictScalars ℝ)
    ((A.chartLiftSobolev μ k).restrictScalars ℝ) ?_ (InterpCouple.memKMethod_ofMap_iff.1 hF))
  ext1 U
  exact (A.chartSobolevEmbedding_chartLiftSobolev k U).symm

/-! ### The chart couple by the pieces -/

/-- **Lifts of extended pieces**: if every piece `P_k f` has a finite intrinsic quasi-norm on
`Ω_I` with moduli of an order `r > θ`, then `L_k P_k f ∈ (L_2(μ), H^1_A(M))_{θ,q}`. The extension
property of `Ω_I` (`Rd.BesovDomain.hasBesovExtension`) gives `F ∈ L_2(E)` with `F = P_k f` on
`Ω_I` and finite whole-space quasi-norm, so `F ∈ (L_2(E), H^1(E))_{θ,q}`
(`Rd.memKMethod_ofMap_toL2_iff`); `L_k F = L_k P_k f`
(`Manifold.BesovAtlas.chartLiftLp_eq_of_ae_eq_on`), and `Manifold.BesovAtlas.memKMethod_chartLiftLp`
applies. -/
theorem memKMethod_chartLiftLp_pieceLp (hθ : 0 < θ) (hθ' : θ < 1) (hq : 1 ≤ q) {r : ℕ}
    (hθr : θ < r) {f : Lp ℂ 2 μ} (k : Fin A.n)
    (hf : Rd.modNormOn (Rd.BesovDomain.measurableSet (range I)) r θ q
      (A.pieceLp μ Rd.two_ne_top k f) < ⊤) :
    (InterpCouple.ofMap ((A.chartSobolevEmbedding μ).restrictScalars ℝ)).MemKMethod θ q
      (A.chartLiftLp μ Rd.two_ne_top k (A.pieceLp μ Rd.two_ne_top k f)) := by
  obtain ⟨C, hC, hext⟩ := Rd.BesovDomain.hasBesovExtension (range I) 2 Rd.two_ne_top r θ hθ hθr
    q hq
  obtain ⟨F, hFf, hF⟩ := hext _ hf
  have hFK := (Rd.memKMethod_ofMap_toL2_iff hθ hθ' hq hθr F).2
    (hF.trans_lt (ENNReal.mul_lt_top hC.lt_top hf))
  have hae := (Rd.indicatorLp_eq_iff_ae_eq_restrict (Rd.BesovDomain.measurableSet (range I))).1 hFf
  rw [← A.chartLiftLp_eq_of_ae_eq_on Rd.two_ne_top k
    (((ae_restrict_iff' (Rd.BesovDomain.measurableSet (range I))).1 hae).mono
      fun y hy hy' => hy (A.liftCarrier_subset_range k hy'.1))]
  exact A.memKMethod_chartLiftLp hFK k

/-- **The chart couple by the pieces**: for `0 < θ < 1`, `1 ≤ q ≤ ∞`, every order `r ≥ 1` and
every `f ∈ L_2(μ)`, `f ∈ (L_2(μ), H^1_A(M))_{θ,q}` iff every piece `P_k f` has a finite intrinsic
quasi-norm `N_{Ω_I}(P_k f)` with moduli of order `r`.
`⇒` is `Manifold.BesovAtlas.modNormOn_pieceLp_lt_top_of_memKMethod`; for `⇐`,
`f = ∑_k L_k P_k f` (`Manifold.BesovAtlas.sum_chartLiftLp_pieceLp`), each term lies in the
interpolation space (`Manifold.BesovAtlas.memKMethod_chartLiftLp_pieceLp`), which is a linear
subspace (`InterpCouple.kMethodSpace`). -/
theorem memKMethod_chartSobolev_iff (hθ : 0 < θ) (hθ' : θ < 1) (hq : 1 ≤ q) {r : ℕ}
    (hr : 1 ≤ r) (f : Lp ℂ 2 μ) :
    (InterpCouple.ofMap ((A.chartSobolevEmbedding μ).restrictScalars ℝ)).MemKMethod θ q f ↔
      ∀ k, Rd.modNormOn (Rd.BesovDomain.measurableSet (range I)) r θ q
        (A.pieceLp μ Rd.two_ne_top k f) < ⊤ := by
  refine ⟨fun hf k => A.modNormOn_pieceLp_lt_top_of_memKMethod hθ hθ' hq hr hf k, fun hf => ?_⟩
  have hsum := (InterpCouple.kMethodSpace InterpCouple.isQuasiNormed_ofMap
    InterpCouple.isHomogeneous_ofMap θ q).sum_mem fun k (_ : k ∈ Finset.univ) =>
      A.memKMethod_chartLiftLp_pieceLp hθ hθ' hq (hθ'.trans_le (Nat.one_le_cast.2 hr)) k (hf k)
  rwa [A.sum_chartLiftLp_pieceLp] at hsum

/-! ### Besov spaces by the eigenbasis of the chart form -/

/-- **Besov spaces on compact manifolds by eigenfunction expansions**: for a compact manifold
whose model range is a Besov domain in dimension `n ≥ 1`, with a smooth measure `μ` and a Besov
atlas `A`, for `0 < θ < 1`, `1 ≤ q ≤ ∞` and every `f ∈ L_2(μ)`, `f` lies in the approximation
space `A^θ_q` of the eigenbasis of the chart form iff `f ∈ B^θ_{2,q}(M)`. The approximation space
is `(L_2(μ), H^1_A(M))_{θ,q}` (`CompactDenseEmbedding.memKMethod_iff_memApprox`), described by
the pieces (`Manifold.BesovAtlas.memKMethod_chartSobolev_iff` with `r = 1`), and so is
`B^θ_{2,q}(M)` (`Manifold.BesovAtlas.memBesov_iff_forall_modNormOn_lt_top`,
`Manifold.memBesov_iff`). -/
theorem memApprox_chartScheme_iff [T2Space M] (hθ : 0 < θ) (hθ' : θ < 1) (hq : 1 ≤ q)
    (f : Lp ℂ 2 μ) :
    (A.chartScheme μ).toScheme.MemApprox θ q f ↔ Manifold.MemBesov I μ Rd.two_ne_top θ q f := by
  rw [Manifold.memBesov_iff I μ Rd.two_ne_top A hθ hq,
    A.memBesov_iff_forall_modNormOn_lt_top Rd.two_ne_top hθ (r := 1) (by exact_mod_cast hθ') hq,
    ← A.memKMethod_chartSobolev_iff hθ hθ' hq le_rfl f]
  exact ((A.chartCompactEmbedding μ).memKMethod_iff_memApprox hθ hθ' hq).symm

/-- **`B^θ_{2,q}(M)` by dyadic blocks of the eigenfunction expansion**: for `0 < θ < 1`,
`1 ≤ q ≤ ∞` and every `f ∈ L_2(μ)`, `f ∈ B^θ_{2,q}(M)` iff
`‖P_1 f‖ + ‖(2^(kθ) ‖Δ_k f‖)_k‖_{ℓ_q} < ∞` for the dyadic blocks `Δ_k f` of the expansion of `f`
in the eigenbasis of the chart form (`Manifold.BesovAtlas.memApprox_chartScheme_iff`,
`SpectralScheme.memApprox_iff_blockNorm_lt_top`). -/
theorem memBesov_iff_blockNorm_lt_top [T2Space M] (hθ : 0 < θ) (hθ' : θ < 1) (hq : 1 ≤ q)
    (f : Lp ℂ 2 μ) :
    Manifold.MemBesov I μ Rd.two_ne_top θ q f ↔
      (A.chartScheme μ).projectionScheme.blockNorm θ q f < ⊤ := by
  rw [← A.memApprox_chartScheme_iff hθ hθ' hq,
    (A.chartScheme μ).memApprox_iff_blockNorm_lt_top hθ hq]

/-- **`B^θ_{2,2}(M)` by the eigenvalues of the chart form**: for `0 < θ < 1` and every
`f ∈ L_2(μ)`, `f ∈ B^θ_{2,2}(M)` iff `∑_i (1 + λ_i)^θ |⟨e_i, f⟩|² < ∞`, that is, the sequence
`((1 + λ_i)^(θ/2) ⟨e_i, f⟩)_i` lies in `ℓ_2` (`Manifold.BesovAtlas.memApprox_chartScheme_iff`,
`CompactDenseEmbedding.memApprox_two_iff` and `1 + λ_i = σ_i⁻²`). -/
theorem memBesov_two_iff_chartEigenvalue [T2Space M] (hθ : 0 < θ) (hθ' : θ < 1)
    (f : Lp ℂ 2 μ) :
    Manifold.MemBesov I μ Rd.two_ne_top θ 2 f ↔
      Memℓp (fun i => (((1 + A.chartEigenvalue μ i) ^ (θ / 2) : ℝ) : ℂ) *
        (A.chartScheme μ).basis.repr f i) 2 := by
  have h : ∀ i, (1 + A.chartEigenvalue μ i) ^ (θ / 2) =
      ((A.chartCompactEmbedding μ).singularValue i)⁻¹ ^ θ := fun i => by
    rw [one_add_chartEigenvalue, ← Real.rpow_natCast,
      ← Real.rpow_mul (inv_nonneg.2 ((A.chartCompactEmbedding μ).singularValue_pos i).le)]
    congr 1
    push_cast
    ring
  rw [← A.memApprox_chartScheme_iff hθ hθ' one_le_two]
  simp only [h]
  exact (A.chartCompactEmbedding μ).memApprox_two_iff hθ _

end BesovAtlas

/-- **The sphere by the chart eigenbasis**: for `n ≥ 1`, every Besov atlas `A` of the sphere
`S^n ⊆ ℝ^(n+1)`, a compact manifold without boundary modelled on `ℝ^n`, with its chart measure
`μ_A` (`Manifold.BesovAtlas.isSmoothMeasure_chartMeasure`), for `0 < θ < 1`, `1 ≤ q ≤ ∞` and every
`f ∈ L_2(μ_A)`, `f` lies in the approximation space `A^θ_q` of the eigenbasis of the chart form iff
`f ∈ B^θ_{2,q}(S^n)` (`Manifold.BesovAtlas.memApprox_chartScheme_iff`). -/
theorem memApprox_chartScheme_sphere_iff {n : ℕ} [NeZero n]
    (A : BesovAtlas (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) {θ : ℝ} {q : ℝ≥0∞}
    (hθ : 0 < θ) (hθ' : θ < 1) (hq : 1 ≤ q) (f : Lp ℂ 2 A.chartMeasure) :
    (A.chartScheme A.chartMeasure).toScheme.MemApprox θ q f ↔
      Manifold.MemBesov (𝓡 n) A.chartMeasure Rd.two_ne_top θ q f :=
  A.memApprox_chartScheme_iff hθ hθ' hq f

end Manifold

namespace Rd

namespace SmoothDomain

variable {n : ℕ} [NeZero n] {θ : ℝ} {q : ℝ≥0∞}

/-- **Smooth domains by the chart eigenbasis**: for a bounded smooth domain `Ω ⊆ ℝ^n`, `n ≥ 1`,
and every Besov atlas `A` of the compact manifold with boundary `closure Ω` with the Lebesgue
measure, for `0 < θ < 1`, `1 ≤ q ≤ ∞`, every order `r ≥ 1` and every `f ∈ L_2(closure Ω)`, `f`
lies in the approximation space `A^θ_q` of the eigenbasis of the chart form iff
`‖f‖_{L_2(Ω)} + ‖(2^(kθ) ω_r(f, 2^(-k), Ω)_2)_k‖_{ℓ_q} < ∞`
(`Manifold.BesovAtlas.memApprox_chartScheme_iff`,
`Rd.SmoothDomain.memBesov_iff_modNormOn_lt_top`). -/
theorem memApprox_chartScheme_iff_modNormOn (Ω : SmoothDomain n)
    (A : Manifold.BesovAtlas (𝓡∂ n) (closure Ω.carrier)) (hθ : 0 < θ) (hθ' : θ < 1) (hq : 1 ≤ q)
    {r : ℕ} (hr : 1 ≤ r) (f : Lp ℂ 2 Ω.volumeOn) :
    (A.chartScheme Ω.volumeOn).toScheme.MemApprox θ q f ↔
      modNormOn Ω.measurableSet r θ q (Ω.extLp two_ne_top f) < ⊤ :=
  (A.memApprox_chartScheme_iff hθ hθ' hq f).trans
    (memBesov_iff_modNormOn_lt_top two_ne_top hθ (hθ'.trans_le (Nat.one_le_cast.2 hr)) hq f)

/-- **The closed ball by the chart eigenbasis**: for the ball `B(c, R) ⊆ ℝ^n`, `n ≥ 1`, and every
Besov atlas `A` of its closure with the Lebesgue measure, for `0 < θ < 1`, `1 ≤ q ≤ ∞`, every order
`r ≥ 1` and every `f`, `f` lies in the approximation space `A^θ_q` of the eigenbasis of the chart
form iff `‖f‖_{L_2(B)} + ‖(2^(kθ) ω_r(f, 2^(-k), B)_2)_k‖_{ℓ_q} < ∞`
(`Manifold.BesovAtlas.memApprox_chartScheme_iff`, `Rd.SmoothDomain.memBesov_ball_iff`). -/
theorem memApprox_chartScheme_ball_iff (c : EuclideanSpace ℝ (Fin n)) (R : ℝ)
    (A : Manifold.BesovAtlas (𝓡∂ n) (closure (SmoothDomain.ball c R).carrier)) (hθ : 0 < θ)
    (hθ' : θ < 1) (hq : 1 ≤ q) {r : ℕ} (hr : 1 ≤ r) (f : Lp ℂ 2 (SmoothDomain.ball c R).volumeOn) :
    (A.chartScheme (SmoothDomain.ball c R).volumeOn).toScheme.MemApprox θ q f ↔
      modNormOn (measurableSet_ball : MeasurableSet (ball c R)) r θ q
        ((SmoothDomain.ball c R).extLp two_ne_top f) < ⊤ :=
  (A.memApprox_chartScheme_iff hθ hθ' hq f).trans
    (memBesov_ball_iff c R two_ne_top hθ (hθ'.trans_le (Nat.one_le_cast.2 hr)) hq f)

end SmoothDomain

end Rd
