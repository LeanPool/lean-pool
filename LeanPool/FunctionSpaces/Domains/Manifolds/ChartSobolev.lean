/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Manifolds.Besov
public import LeanPool.FunctionSpaces.Domains.Lipschitz.BesovDomainLocalisation
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Instances.Real

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The chart Sobolev space of a compact manifold

Let `M` be a compact manifold with model `I` whose range `Ω_I = range I` is a Besov domain (no
boundary, the half-space, the quadrant), `μ` a smooth measure and `A` a Besov atlas with charts
`κ_i`, partition of unity `ψ_i` and cut-offs `θ_i`. Write `O_I = interior Ω_I`
(`Manifold.modelInterior`): all of `E` for manifolds without boundary
(`Manifold.modelInterior_eq_top`), the open half-space `{y_0 > 0}` for manifolds with boundary
(`Manifold.modelInterior_euclideanHalfSpace`); `Ω_I \ O_I` is a null set
(`Manifold.modelInterior_ae_eq_range`).

* **Pieces and lifts as operators**: `P_i f = (ψ_i f) ∘ κ_i⁻¹` and `L_k F = θ_k · F ∘ κ_k` are
  bounded linear operators `L_p(μ) → L_p(E)` and `L_p(E) → L_p(μ)` (`Manifold.BesovAtlas.pieceCLM`,
  `Manifold.BesovAtlas.chartLiftCLM`), and `∑_k L_k P_k = id`
  (`Manifold.BesovAtlas.sum_chartLiftCLM_comp_pieceCLM`). The lift `L_k F` sees `F` only on
  `κ_k(tsupport θ_k) ∩ O_I`, where `κ_k(tsupport θ_k)` is compact
  (`Manifold.BesovAtlas.isCompact_liftCarrier`, `Manifold.BesovAtlas.chartLiftLp_eq_of_ae_eq_on`),
  and `P_i f` vanishes outside the compact `κ_i(tsupport ψ_i) ⊆ Ω_I`
  (`Manifold.BesovAtlas.pieceLp_eq_zero_off`), hence outside a ball `B(0, R_i)`
  (`Manifold.BesovAtlas.pieceRadius`, `Manifold.BesovAtlas.pieceLp_eq_zero_off_ball`).
* **The chart Sobolev space** `H^1_A(M)` (`Manifold.BesovAtlas.chartSobolev`) is the graph space of
  the pairs `(f, g)` in `L_2(μ) × ∏_{i,j} L_2(O_I)` with `g_{ij} = ∂_{b_j} P_i f` weakly on `O_I`
  for the basis `b_j = Rd.gridBasis E j`. It is a closed subspace
  (`Manifold.BesovAtlas.isClosed_chartSobolev`), with the inner product
  `⟨f, f'⟩_{L_2(μ)} + a_A(u, u')` of the **chart form** `a_A(u, u') = ∑_{i,j} ⟨g_{ij}, g'_{ij}⟩`
  (`Manifold.BesovAtlas.chartForm`, `Manifold.BesovAtlas.inner_chartSobolev`), and
  `J (f, g) = f` (`Manifold.BesovAtlas.chartSobolevEmbedding`) is injective of norm at most `1`
  (`Manifold.BesovAtlas.chartSobolevEmbedding_injective`,
  `Manifold.BesovAtlas.norm_chartSobolevEmbedding_le`).
* **`H^1_A(M) = B^1_{2,2}(M)`**: the range of `J` is the Besov space `B^1_{2,2}(M)`
  (`Manifold.BesovAtlas.mem_range_chartSobolevEmbedding_iff`), piece by piece through
  `W^1_2 = B^1_{2,2}` for compactly supported functions on the Besov domain `Ω_I`
  (`Rd.BesovDomain.exists_hasWeakLineDeriv_iff_modNormOn_lt_top`); so it is the same for every
  Besov atlas (`Manifold.BesovAtlas.range_chartSobolevEmbedding_eq`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology TopologicalSpace Module Metric
open scoped ENNReal Manifold ContDiff InnerProductSpace

namespace Manifold

/-! ### The open model set -/

section ModelInterior

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)

/-- The **open model set** `O_I = interior (range I)`, as an open set of `E`: the open half-space
for manifolds with boundary, the open quadrant for manifolds with corners, `E` for manifolds without
boundary. -/
noncomputable abbrev modelInterior : Opens E :=
  Opens.interior (range I)

omit [FiniteDimensional ℝ E] in
/-- **Without boundary the open model set is `E`**, since `range I = E`. -/
theorem modelInterior_eq_top [I.Boundaryless] : modelInterior I = ⊤ :=
  Opens.ext (by simp [ModelWithCorners.Boundaryless.range_eq_univ])

/-- **The open model set is the range up to a null set** when the range is a Besov domain: the
frontier of a convex set is a null set (`Rd.BesovDomain.interior_ae_eq`). -/
theorem modelInterior_ae_eq_range [MeasurableSpace E] [BorelSpace E] [Rd.BesovDomain (range I)] :
    (modelInterior I : Set E) =ᵐ[volume] range I :=
  Rd.BesovDomain.interior_ae_eq (range I)

end ModelInterior

/-- **The open model set of the half-space** `𝓡∂ n` is the open half-space `{y | 0 < y 0}`
(Mathlib's `interior_range_modelWithCornersEuclideanHalfSpace`). -/
theorem modelInterior_euclideanHalfSpace (n : ℕ) [NeZero n] :
    (modelInterior (𝓡∂ n) : Set (EuclideanSpace ℝ (Fin n))) = {y | 0 < y 0} :=
  interior_range_modelWithCornersEuclideanHalfSpace n

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

namespace BesovAtlas

variable (A : BesovAtlas I M) {μ : Measure M} [IsSmoothMeasure I μ] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  (hp : p ≠ ⊤)

/-! ### Pieces and lifts as bounded operators -/

variable (μ) in
/-- **The `i`-th piece as a bounded operator** `L_p(μ) → L_p(E)`, `f ↦ (ψ_i f) ∘ κ_i⁻¹`: linear
(`Manifold.BesovAtlas.pieceLp_add`, `Manifold.BesovAtlas.pieceLp_smul`) and bounded
(`Manifold.BesovAtlas.exists_eLpNorm_piece_le`). -/
noncomputable def pieceCLM (i : Fin A.n) : Lp ℂ p μ →L[ℂ] Lp ℂ p (volume : Measure E) :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := A.pieceLp μ hp i
      map_add' := A.pieceLp_add hp i
      map_smul' := A.pieceLp_smul hp i } (by
    obtain ⟨C, hC, hle⟩ := A.exists_eLpNorm_piece_le μ i
      (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
    refine ⟨C.toReal, fun f => ?_⟩
    have h : ‖A.pieceLp μ hp i f‖ₑ ≤ C * ‖f‖ₑ := by
      rw [Lp.eNorm_def, Lp.eNorm_def, eLpNorm_congr_ae (A.pieceLp_ae μ hp i f)]
      exact hle f (Lp.stronglyMeasurable f)
    change ‖A.pieceLp μ hp i f‖ ≤ _
    rw [← toReal_eNorm, ← toReal_eNorm f, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hC eNorm_ne_top) h)

/-- `pieceCLM i f` is the piece `(ψ_i f) ∘ κ_i⁻¹`. -/
theorem pieceCLM_apply (i : Fin A.n) (f : Lp ℂ p μ) : A.pieceCLM μ hp i f = A.pieceLp μ hp i f :=
  rfl

variable (μ) in
/-- **The lift from the `k`-th chart as a bounded operator** `L_p(E) → L_p(μ)`,
`F ↦ θ_k · F ∘ κ_k` (`Manifold.exists_eLpNorm_chartLift_le`). -/
noncomputable def chartLiftCLM (k : Fin A.n) : Lp ℂ p (volume : Measure E) →L[ℂ] Lp ℂ p μ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := A.chartLiftLp μ hp k
      map_add' := A.chartLiftLp_add hp k
      map_smul' := A.chartLiftLp_smul hp k } (by
    obtain ⟨C, hC, hle⟩ := exists_eLpNorm_chartLift_le (I := I) μ (A.chart_mem k)
      (A.contMDiff_theta k).continuous (A.tsupport_theta_subset k)
      (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
    refine ⟨C.toReal, fun F => ?_⟩
    have h : ‖A.chartLiftLp μ hp k F‖ₑ ≤ C * ‖F‖ₑ := by
      rw [Lp.eNorm_def, Lp.eNorm_def, eLpNorm_congr_ae (A.chartLiftLp_ae hp k F)]
      exact hle F (Lp.stronglyMeasurable F)
    change ‖A.chartLiftLp μ hp k F‖ ≤ _
    rw [← toReal_eNorm, ← toReal_eNorm F, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hC eNorm_ne_top) h)

/-- `chartLiftCLM k F` is the lift `θ_k · F ∘ κ_k`. -/
theorem chartLiftCLM_apply (k : Fin A.n) (F : Lp ℂ p (volume : Measure E)) :
    A.chartLiftCLM μ hp k F = A.chartLiftLp μ hp k F :=
  rfl

/-! ### The retract identity -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] [CompactSpace M] in
/-- **The lift of a piece** (pointwise): `θ_k · (piece_k g) ∘ κ_k = ψ_k g`, since
`κ_k⁻¹ ∘ κ_k = id` on the source and `θ_k ψ_k = ψ_k`. -/
theorem chartLift_piece (k : Fin A.n) (g : M → ℂ) :
    chartLift I (A.chart k) (A.theta k) (A.piece k g) = fun x => (A.psi k x : ℂ) * g x := by
  funext x
  by_cases hx : x ∈ (A.chart k).source
  · have hx' : x ∈ (A.ext k).source := by rwa [OpenPartialHomeomorph.extend_source]
    rw [chartLift, indicator_of_mem hx, piece, indicator_of_mem ((A.ext k).map_source hx'),
      (A.ext k).left_inv hx', ← mul_assoc, ← Complex.ofReal_mul, A.theta_mul_psi]
  · have hψ : A.psi k x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hx (A.tsupport_psi_subset k h)
    rw [chartLift, indicator_of_notMem hx, hψ, Complex.ofReal_zero, zero_mul]

/-- **The retract identity**: `∑_k θ_k · (P_k f) ∘ κ_k = f` for every `f ∈ L_p(μ)`, since the lift
of the `k`-th piece is `ψ_k f` (`Manifold.BesovAtlas.chartLift_piece`) and `∑_k ψ_k = 1`. -/
theorem sum_chartLiftLp_pieceLp (f : Lp ℂ p μ) :
    ∑ k, A.chartLiftLp μ hp k (A.pieceLp μ hp k f) = f := by
  refine Lp.ext ?_
  have h : ∀ k, (A.chartLiftLp μ hp k (A.pieceLp μ hp k f) : M → ℂ) =ᵐ[μ]
      fun x => (A.psi k x : ℂ) * f x := fun k =>
    (A.chartLiftLp_ae hp k _).trans ((chartLift_ae_eq (I := I) (μ := μ) (A.chart_mem k)
      (A.tsupport_theta_subset k) (A.pieceLp_ae μ hp k f)).trans
        (EventuallyEq.of_eq (A.chartLift_piece k f)))
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun k => A.chartLiftLp μ hp k (A.pieceLp μ hp k f)), ae_all_iff.2 h] with x h1 h2
  rw [h1, Finset.sum_congr rfl fun k _ => h2 k, ← Finset.sum_mul, ← Complex.ofReal_sum,
    A.sum_psi, Complex.ofReal_one, one_mul]

/-- **The retract identity for operators**: `∑_k L_k ∘ P_k = id` on `L_p(μ)`
(`Manifold.BesovAtlas.sum_chartLiftLp_pieceLp`). -/
theorem sum_chartLiftCLM_comp_pieceCLM :
    ∑ k, (A.chartLiftCLM μ hp k).comp (A.pieceCLM μ hp k) =
      ContinuousLinearMap.id ℂ (Lp ℂ p μ) := by
  ext1 f
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
    chartLiftCLM_apply, pieceCLM_apply, ContinuousLinearMap.id_apply]
  exact A.sum_chartLiftLp_pieceLp hp f

/-! ### Where lifts and pieces live -/

/-- **The carrier of the `k`-th lift**: the compact set `κ_k(tsupport θ_k) ⊆ range I`, the only
part of `E` that the lift `θ_k · F ∘ κ_k` sees. -/
noncomputable def liftCarrier (k : Fin A.n) : Set E :=
  A.ext k '' tsupport (A.theta k)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] in
/-- The carrier of a lift is compact, the image of the compact `tsupport θ_k` under the chart. -/
theorem isCompact_liftCarrier (k : Fin A.n) : IsCompact (A.liftCarrier k) :=
  (isClosed_tsupport _).isCompact.image_of_continuousOn ((A.chart k).continuousOn_extend.mono
    (by rw [OpenPartialHomeomorph.extend_source]; exact A.tsupport_theta_subset k))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] [CompactSpace M] in
/-- The carrier of a lift lies in `range I`, since the extended charts take values there. -/
theorem liftCarrier_subset_range (k : Fin A.n) : A.liftCarrier k ⊆ range I := by
  rintro _ ⟨x, -, rfl⟩
  exact ⟨A.chart k x, rfl⟩

/-- **Lifts are local**: if `F = G` almost everywhere on `κ_k(tsupport θ_k) ∩ O_I`, then the lifts
`θ_k · F ∘ κ_k` and `θ_k · G ∘ κ_k` agree in `L_p(μ)`; the points of `range I \ O_I` form a null
set (`Manifold.modelInterior_ae_eq_range`), whose preimage is `μ`-null
(`Manifold.IsSmoothMeasure.ae_comp_extend`). -/
theorem chartLiftLp_eq_of_ae_eq_on [Rd.BesovDomain (range I)] (k : Fin A.n)
    {F G : Lp ℂ p (volume : Measure E)}
    (h : ∀ᵐ y ∂volume, y ∈ A.liftCarrier k ∩ interior (range I) → F y = G y) :
    A.chartLiftLp μ hp k F = A.chartLiftLp μ hp k G := by
  have hO : ∀ᵐ y ∂(volume : Measure E), y ∈ range I → y ∈ interior (range I) :=
    (modelInterior_ae_eq_range I).mem_iff.mono fun y hy h => hy.2 h
  refine Lp.ext ?_
  filter_upwards [A.chartLiftLp_ae hp k F, A.chartLiftLp_ae hp k G,
    IsSmoothMeasure.ae_comp_extend (I := I) (μ := μ) (A.chart_mem k) (isClosed_tsupport (A.theta k))
      (A.tsupport_theta_subset k) (h.and hO)] with x h1 h2 h3
  rw [h1, h2]
  by_cases hxs : x ∈ (A.chart k).source
  · simp only [chartLift, indicator_of_mem hxs]
    by_cases hxt : x ∈ tsupport (A.theta k)
    · have hy : A.ext k x ∈ A.liftCarrier k := mem_image_of_mem _ hxt
      rw [(h3 hxt).1 ⟨hy, (h3 hxt).2 (A.liftCarrier_subset_range k hy)⟩]
    · rw [image_eq_zero_of_notMem_tsupport hxt, Complex.ofReal_zero, zero_mul, zero_mul]
  · simp only [chartLift, indicator_of_notMem hxs]

/-- **The piece in `L_p` vanishes off its carrier**: `P_i f = 0` almost everywhere outside the
compact `κ_i(tsupport ψ_i)`. -/
theorem pieceLp_eq_zero_off (i : Fin A.n) (f : Lp ℂ p μ) :
    ∀ᵐ y ∂volume, y ∉ A.pieceCarrier i → A.pieceLp μ hp i f y = 0 :=
  (A.pieceLp_ae μ hp i f).mono fun y hy hy' => by
    rw [hy]
    exact A.piece_eq_zero_of_notMem i _ hy'

/-- **The radius of the `i`-th piece**: a radius `R_i` with `κ_i(tsupport ψ_i) ⊆ B(0, R_i)`, which
exists as the carrier of the piece is compact (`Manifold.BesovAtlas.isCompact_pieceCarrier`). -/
noncomputable def pieceRadius (i : Fin A.n) : ℝ :=
  Classical.choose ((A.isCompact_pieceCarrier i).isBounded.subset_ball (0 : E))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] in
/-- The carrier `κ_i(tsupport ψ_i)` of the `i`-th piece lies in the ball `B(0, R_i)`. -/
theorem pieceCarrier_subset_ball (i : Fin A.n) : A.pieceCarrier i ⊆ ball 0 (A.pieceRadius i) :=
  Classical.choose_spec ((A.isCompact_pieceCarrier i).isBounded.subset_ball (0 : E))

/-- **The pieces vanish outside the ball of radius `R_i`**: `P_i f = 0` almost everywhere outside
`B(0, R_i)`, for every `f ∈ L_p(μ)` (`Manifold.BesovAtlas.pieceLp_eq_zero_off`). -/
theorem pieceLp_eq_zero_off_ball (i : Fin A.n) (f : Lp ℂ p μ) :
    ∀ᵐ y ∂volume, y ∉ ball (0 : E) (A.pieceRadius i) → A.pieceLp μ hp i f y = 0 :=
  (A.pieceLp_eq_zero_off hp i f).mono fun _ hy hyR =>
    hy fun h => hyR (A.pieceCarrier_subset_ball i h)

/-- **The pieces vanish outside a ball**: there is `R` with `P_i f = 0` almost everywhere outside
`B(0, R)` for every `f ∈ L_p(μ)`, for example `R = R_i`
(`Manifold.BesovAtlas.pieceLp_eq_zero_off_ball`). -/
theorem exists_pieceLp_eq_zero_off_ball (i : Fin A.n) :
    ∃ R : ℝ, ∀ f : Lp ℂ p μ, ∀ᵐ y ∂volume, y ∉ ball (0 : E) R → A.pieceLp μ hp i f y = 0 :=
  ⟨A.pieceRadius i, A.pieceLp_eq_zero_off_ball hp i⟩

/-! ### The chart Sobolev space -/

variable (μ) in
/-- **Values and chart gradients**: the Hilbert space `L_2(μ) × ∏_{(i,j)} L_2(O_I)` of pairs
`(f, g)`, `i` over the charts and `j < dim E`, with the inner product
`⟨f, f'⟩_{L_2(μ)} + ∑_{i,j} ⟨g_{ij}, g'_{ij}⟩_{L_2(O_I)}`. -/
abbrev chartValueGradientL2 : Type _ :=
  WithLp 2 (Lp ℂ 2 μ × PiLp 2 (fun _ : Fin A.n × Fin (finrank ℝ E) =>
    Lp ℂ 2 (volume.restrict (interior (range I)))))

variable (μ) in
/-- **The chart Sobolev space** `H^1_A(M)`: the pairs `(f, g)` in `L_2(μ) × ∏_{(i,j)} L_2(O_I)`
with `g_{ij} = ∂_{b_j} P_i f` weakly on the open model set `O_I` for the basis
`b_j = Rd.gridBasis E j`, where `P_i f = (ψ_i f) ∘ κ_i⁻¹`. For manifolds with boundary `O_I` is the
open half-space (`Manifold.modelInterior_euclideanHalfSpace`). -/
noncomputable def chartSobolev : Submodule ℂ (A.chartValueGradientL2 μ) where
  carrier := {u | ∀ ij : Fin A.n × Fin (finrank ℝ E), Rd.HasWeakLineDeriv (modelInterior I)
    (fun _ : Fin 1 => Rd.gridBasis E ij.2) (A.pieceLp μ Rd.two_ne_top ij.1 u.fst) (u.snd ij)}
  zero_mem' := fun ij => by
    rw [WithLp.zero_fst, A.pieceLp_zero, WithLp.zero_snd, PiLp.zero_apply]
    exact Rd.hasWeakLineDeriv_zero.congr_ae (ae_restrict_of_ae (Lp.coeFn_zero ..).symm)
      (Lp.coeFn_zero ..).symm
  add_mem' := fun {u w} hu hw ij => by
    rw [WithLp.add_fst, A.pieceLp_add, WithLp.add_snd, PiLp.add_apply]
    exact ((hu ij).add (hw ij)).congr_ae (ae_restrict_of_ae (Lp.coeFn_add ..).symm)
      (Lp.coeFn_add ..).symm
  smul_mem' := fun c u hu ij => by
    rw [WithLp.smul_fst, A.pieceLp_smul, WithLp.smul_snd, PiLp.smul_apply]
    exact ((hu ij).smul c).congr_ae (ae_restrict_of_ae (Lp.coeFn_smul ..).symm)
      (Lp.coeFn_smul ..).symm

/-- Membership in the chart Sobolev space: `g_{ij} = ∂_{b_j} P_i f` weakly on `O_I` for all
`i, j`. -/
theorem mem_chartSobolev {u : A.chartValueGradientL2 μ} :
    u ∈ A.chartSobolev μ ↔ ∀ ij : Fin A.n × Fin (finrank ℝ E),
      Rd.HasWeakLineDeriv (modelInterior I) (fun _ : Fin 1 => Rd.gridBasis E ij.2)
        (A.pieceLp μ Rd.two_ne_top ij.1 u.fst) (u.snd ij) :=
  Iff.rfl

variable (μ) in
/-- **The chart Sobolev space is closed**: the pieces depend continuously on `f`
(`Manifold.BesovAtlas.pieceCLM`), and weak derivatives pass to limits in `L_2(O_I)`
(`Rd.HasWeakLineDeriv.of_tendsto`). -/
theorem isClosed_chartSobolev : IsClosed (A.chartSobolev μ : Set (A.chartValueGradientL2 μ)) := by
  refine IsSeqClosed.isClosed fun {u u₀} hu hlim ij => ?_
  have h0 : Tendsto (fun n => (u n).fst) atTop (𝓝 u₀.fst) :=
    ((WithLp.fstL 2 ℂ _ _).continuous.tendsto u₀).comp hlim
  have h1 : Tendsto (fun n => A.pieceLp μ Rd.two_ne_top ij.1 (u n).fst) atTop
      (𝓝 (A.pieceLp μ Rd.two_ne_top ij.1 u₀.fst)) :=
    ((A.pieceCLM μ Rd.two_ne_top ij.1).continuous.tendsto _).comp h0
  have h2 : Tendsto (fun n => (u n).snd ij) atTop (𝓝 (u₀.snd ij)) :=
    ((PiLp.continuous_apply 2 _ ij).tendsto _).comp
      (((WithLp.sndL 2 ℂ _ _).continuous.tendsto u₀).comp hlim)
  refine Rd.HasWeakLineDeriv.of_tendsto one_le_two one_le_two (fun n => hu n ij)
    ((Lp.memLp _).restrict _) (Lp.memLp _) ?_ ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 h2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 h1) (fun n => zero_le)
    fun n => eLpNorm_mono_measure _ Measure.restrict_le_self

/-- The chart Sobolev space is a Hilbert space, as a closed subspace
(`Manifold.BesovAtlas.isClosed_chartSobolev`). -/
instance completeSpace_chartSobolev : CompleteSpace (A.chartSobolev μ) :=
  (A.isClosed_chartSobolev μ).completeSpace_coe

variable (μ) in
/-- **The chart form** `a_A(u, w) = ∑_{i,j} ⟨g_{ij}, g'_{ij}⟩_{L_2(O_I)}` for `u = (f, g)` and
`w = (f', g')` in the chart Sobolev space: the sum over the charts of the gradient forms
`∑_j ∫_{O_I} conj (∂_{b_j} P_i f) · ∂_{b_j} P_i f'`. -/
noncomputable def chartForm (u w : A.chartSobolev μ) : ℂ :=
  ∑ ij, ⟪(u : A.chartValueGradientL2 μ).snd ij, (w : A.chartValueGradientL2 μ).snd ij⟫_ℂ

/-- **The inner product of the chart Sobolev space**: `⟨u, w⟩ = ⟨f, f'⟩_{L_2(μ)} + a_A(u, w)` for
`u = (f, g)` and `w = (f', g')`. -/
theorem inner_chartSobolev (u w : A.chartSobolev μ) :
    ⟪u, w⟫_ℂ =
      ⟪(u : A.chartValueGradientL2 μ).fst, (w : A.chartValueGradientL2 μ).fst⟫_ℂ +
        A.chartForm μ u w := by
  rw [Submodule.coe_inner, WithLp.prod_inner_apply, PiLp.inner_apply]
  rfl

variable (μ) in
/-- **The chart Sobolev embedding** `J : H^1_A(M) → L_2(μ)`, `(f, g) ↦ f`. -/
noncomputable def chartSobolevEmbedding : A.chartSobolev μ →L[ℂ] Lp ℂ 2 μ :=
  WithLp.fstL 2 ℂ _ _ ∘L (A.chartSobolev μ).subtypeL

/-- `J u` is the value `f` of `u = (f, g)`. -/
theorem chartSobolevEmbedding_apply (u : A.chartSobolev μ) :
    A.chartSobolevEmbedding μ u = (u : A.chartValueGradientL2 μ).fst :=
  rfl

/-- The chart Sobolev embedding has norm at most `1`. -/
theorem norm_chartSobolevEmbedding_le : ‖A.chartSobolevEmbedding μ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    rw [one_mul]
    exact WithLp.norm_fst_le _ (u : A.chartValueGradientL2 μ)

/-- **The chart Sobolev embedding is injective**: the weak derivatives of the pieces are determined
by `f` (`Rd.HasWeakLineDeriv.unique`). -/
theorem chartSobolevEmbedding_injective : Function.Injective (A.chartSobolevEmbedding μ) := by
  intro u w h
  have hs : ∀ ij,
      (u : A.chartValueGradientL2 μ).snd ij = (w : A.chartValueGradientL2 μ).snd ij := by
    intro ij
    have hw := w.2 ij
    rw [← (show (u : A.chartValueGradientL2 μ).fst = (w : A.chartValueGradientL2 μ).fst
      from h)] at hw
    exact Lp.ext ((u.2 ij).unique hw)
  exact Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext h (WithLp.ofLp_injective 2 (funext hs))))

/-! ### The range of the chart Sobolev embedding -/

/-- **The range by the pieces**: `f ∈ L_2(μ)` is a value of the chart Sobolev embedding iff every
piece `P_i f` has weak derivatives `∂_{b_j} P_i f ∈ L_2(O_I)` on `O_I` along the basis vectors
`b_j = Rd.gridBasis E j`. -/
theorem mem_range_chartSobolevEmbedding_iff_forall_piece (f : Lp ℂ 2 μ) :
    f ∈ range (A.chartSobolevEmbedding μ) ↔ ∀ i, ∃ g : Fin (finrank ℝ E) →
      Lp ℂ 2 (volume.restrict (interior (range I))), ∀ j, Rd.HasWeakLineDeriv (modelInterior I)
        (fun _ : Fin 1 => Rd.gridBasis E j) (A.pieceLp μ Rd.two_ne_top i f) (g j) := by
  constructor
  · rintro ⟨u, rfl⟩ i
    exact ⟨fun j => (u : A.chartValueGradientL2 μ).snd (i, j), fun j => u.2 (i, j)⟩
  · intro h
    choose g hg using h
    exact ⟨⟨WithLp.toLp 2 (f, WithLp.toLp 2 fun ij => g ij.1 ij.2), fun ij => hg ij.1 ij.2⟩, rfl⟩

/-- **`H^1_A(M) = B^1_{2,2}(M)` for one atlas**: `f ∈ L_2(μ)` is a value of the chart Sobolev
embedding iff `f ∈ B^1_{2,2}` for the atlas `A`. Each piece vanishes outside a ball
(`Manifold.BesovAtlas.exists_pieceLp_eq_zero_off_ball`), so it has a weak gradient in `L_2(O_I)`
iff its intrinsic `B^1_{2,2}` quasi-norm on `range I` of order `2` is finite
(`Rd.BesovDomain.exists_hasWeakLineDeriv_iff_modNormOn_lt_top`). -/
theorem mem_range_chartSobolevEmbedding_iff_memBesov [Rd.BesovDomain (range I)]
    (f : Lp ℂ 2 μ) :
    f ∈ range (A.chartSobolevEmbedding μ) ↔ A.MemBesov Rd.two_ne_top 1 2 f := by
  rw [A.mem_range_chartSobolevEmbedding_iff_forall_piece,
    A.memBesov_iff_forall_modNormOn_lt_top Rd.two_ne_top (r := 2) one_pos (by norm_num) one_le_two]
  refine forall_congr' fun i => ?_
  obtain ⟨R, hR⟩ := A.exists_pieceLp_eq_zero_off_ball (μ := μ) Rd.two_ne_top i
  exact Rd.BesovDomain.exists_hasWeakLineDeriv_iff_modNormOn_lt_top le_rfl (hR f)

/-- **The chart Sobolev space is the same for every atlas**: two Besov atlases `A, A'` give the
same range `J(H^1_A(M)) = J(H^1_{A'}(M))` in `L_2(μ)`, since both are `B^1_{2,2}(M)`
(`Manifold.BesovAtlas.memBesov_iff_memBesov`). -/
theorem range_chartSobolevEmbedding_eq [Rd.BesovDomain (range I)] [IsManifold I ∞ M]
    (A' : BesovAtlas I M) :
    range (A.chartSobolevEmbedding μ) = range (A'.chartSobolevEmbedding μ) := by
  ext f
  rw [A.mem_range_chartSobolevEmbedding_iff_memBesov,
    A'.mem_range_chartSobolevEmbedding_iff_memBesov]
  exact A.memBesov_iff_memBesov Rd.two_ne_top A' one_pos one_le_two f

/-- **`H^1_A(M) = B^1_{2,2}(M)`**: for every Besov atlas `A` of a compact manifold whose model range
is a Besov domain, `f ∈ L_2(μ)` is a value of the chart Sobolev embedding iff `f` lies in the Besov
space `B^1_{2,2}(M)` (`Manifold.BesovAtlas.mem_range_chartSobolevEmbedding_iff_memBesov`,
`Manifold.memBesov_iff`). -/
theorem mem_range_chartSobolevEmbedding_iff [Rd.BesovDomain (range I)] [T2Space M]
    [IsManifold I ∞ M] (f : Lp ℂ 2 μ) :
    f ∈ range (A.chartSobolevEmbedding μ) ↔ Manifold.MemBesov I μ Rd.two_ne_top 1 2 f := by
  rw [Manifold.memBesov_iff I μ Rd.two_ne_top A one_pos one_le_two f]
  exact A.mem_range_chartSobolevEmbedding_iff_memBesov f

end BesovAtlas

end Manifold
