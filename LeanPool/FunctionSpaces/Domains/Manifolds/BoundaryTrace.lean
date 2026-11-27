/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Manifolds.BoundaryBesov
public import LeanPool.FunctionSpaces.Domains.Manifolds.Besov

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The trace theorem on a compact manifold with boundary

Let `M` be a compact manifold with boundary modelled on the half-space `𝓡∂ n`, `μ` a smooth
measure, `A` a Besov atlas, and `Tr` the trace of order `L` of the half-space
(`Rd.LipschitzGraph.trace` for the flat domain `Manifold.flatDomain n`).

**The trace commutes with the changes of charts** (`Manifold.trace_chartChange_applyLp`): for a
change of charts with a cut-off `T` and its restriction `T^∂` to the boundary hyperplane `H₀`,
`Tr (T G) = T^∂ (Tr G)`. For the continuous partial sums `G_J` of the reproducing formula both
sides are restrictions to `H₀` of `T G_J`, which is continuous on the closed half-space
(`Rd.trace_ae_eq_of_continuousOn`), and both sides are continuous in `G` for the norm of
`B^{1/p}_{p,1}` (`Rd.LipschitzGraph.enorm_trace_le_modNormOn`).

**The trace on the boundary** of `f ∈ L_p(μ)` is `Tr_A f = ∑_i θ_i · Tr(piece_i f) ∘ P ∘ κ_i`
(`Manifold.BesovAtlas.boundaryTrace`). For `s > 0` and `f ∈ B^{s+1/p}_{p,q}(M)` its boundary
pieces are the traces of the pieces of `f` (`Manifold.BesovAtlas.boundaryPiece_boundaryTrace`),
for the boundary pieces of every atlas (`Manifold.BesovAtlas.boundaryPiece_boundaryTrace_of_atlas`).
Hence:

* **the trace is bounded**: the boundary pieces of `Tr_A f` have Besov quasi-norms at most `C`
  times the Besov quasi-norm of `f` (`Manifold.BesovAtlas.exists_boundaryTrace_norm_le`), so
  `Tr_A f ∈ B^s_{p,q}(∂M)` (`Manifold.BesovAtlas.memBoundaryBesov_boundaryTrace`);
* **the trace is onto**: every `g ∈ B^s_{p,q}(∂M)` is the trace of `f = ∑_k θ_k · (E G_k) ∘ κ_k`,
  with the extensions `E G_k` of the boundary pieces of `g`
  (`Manifold.BesovAtlas.exists_boundaryTrace_eq`).

So `B^s_{p,q}(∂M)` is the trace space of `B^{s+1/p}_{p,q}(M)` for every `s > 0`
(`Manifold.BesovAtlas.memBoundaryBesov_iff_exists_boundaryTrace`). For `f` with a continuous
representative `g`, the boundary pieces of `Tr_A f` are those of `g`: the trace is the restriction
to the boundary (`Manifold.BesovAtlas.boundaryPiece_boundaryTrace_of_continuous`).

The closure of a smooth bounded domain is such a manifold (`Rd.SmoothDomain.isManifold`); there
both statements hold for the Lebesgue measure
(`Rd.SmoothDomain.memBoundaryBesov_iff_exists_boundaryTrace`,
`Rd.SmoothDomain.boundaryPiece_boundaryTrace_of_continuous`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal Manifold ContDiff

open ENNReal (lqNorm dyadicWeight)

namespace Manifold

variable {n : ℕ} [NeZero n]

/-! ### The closed and the open half-space -/

/-- The range of the half-space model is the flat domain up to the null set `H₀`. -/
theorem range_ae_eq_domain : range (𝓡∂ n) =ᵐ[volume] (flatDomain n).domain := by
  rw [range_eq_closedHalfSpace]
  exact Rd.closedHalfSpace_ae_eq Rd.norm_e0

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The cut-off to the open half-space is the cut-off to the closed half-space. -/
theorem cutoff_eq_indicatorLp (hΩm : MeasurableSet (range (𝓡∂ n)))
    (G : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (flatDomain n).cutoff G = Rd.indicatorLp hΩm G :=
  (Rd.indicatorLp_congr_set hΩm (flatDomain n).measurableSet_domain range_ae_eq_domain G).symm

/-- **The intrinsic quasi-norms of the closed and of the open half-space agree**: the two sets
differ by the null set `H₀`. -/
theorem modNormOn_range_eq (hΩm : MeasurableSet (range (𝓡∂ n))) (r : ℕ) (σ : ℝ) (q : ℝ≥0∞)
    (G : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Rd.modNormOn hΩm r σ q G = Rd.modNormOn (flatDomain n).measurableSet_domain r σ q G :=
  Rd.modNormOn_congr_set hΩm (flatDomain n).measurableSet_domain range_ae_eq_domain r σ q G

/-! ### The trace commutes with the changes of charts -/

section Commutation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (𝓡∂ n) ∞ M] [CompactSpace M]
  {e e' : OpenPartialHomeomorph M (EuclideanHalfSpace n)} (he : e ∈ atlas _ M)
  (he' : e' ∈ atlas _ M) (c : M → ℝ) (hc : ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ c)
  (hcs : tsupport c ⊆ e.source ∩ e'.source) (hp : p ≠ ⊤)

/-- **The trace commutes with a change of charts, for continuous functions**: if `G` has a finite
`B^{s+1/p}_{p,q}`-norm of order `L > s + 1/p` and a continuous representative `g`, then
`Tr (T G) = T^∂ (Tr G)`: both are the restriction of `T g` to `H₀`. -/
theorem trace_chartChange_applyLp_of_continuous {L : ℕ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s)
    (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {G : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin n)))}
    (hG : ‖G‖ₑ + lqNorm q (fun k => dyadicWeight (s + 1 / p.toReal) k * Rd.lpModulus p L G k) < ⊤)
    {g : EuclideanSpace ℝ (Fin n) → ℂ} (hgc : Continuous g) (hGg : (G : _ → ℂ) =ᵐ[volume] g) :
    (flatDomain n).trace hp L ((BesovAtlas.chartChange he he' c hc hcs).applyLp
        Rd.BesovDomain.convex Rd.BesovDomain.interior_nonempty
        (Rd.BesovDomain.measurableSet _) hp G) =
      (boundaryChartChange he he' c hc hcs).applyLp convex_univ
        BesovAtlas.interior_univ_bdry_nonempty MeasurableSet.univ hp
        ((flatDomain n).trace hp L G) := by
  have hσ0 : 0 < s + 1 / p.toReal := by positivity
  set Ω := flatDomain n
  set T := BesovAtlas.chartChange he he' c hc hcs
  set T' := boundaryChartChange he he' c hc hcs
  set hΩm := Rd.BesovDomain.measurableSet (range (𝓡∂ n))
  obtain ⟨C, hC, hTle⟩ := T.modNormOn_applyLp_le Rd.BesovDomain.convex
    Rd.BesovDomain.interior_nonempty hΩm hp hL hσ0 hsL hq
  have hfin := (hTle G).trans_lt (ENNReal.mul_lt_top hC.lt_top hG)
  rw [modNormOn_range_eq hΩm] at hfin
  have h1 : (T.applyLp Rd.BesovDomain.convex Rd.BesovDomain.interior_nonempty hΩm hp G :
      _ → ℂ) =ᵐ[volume] T.apply g :=
    (T.applyLp_ae _ _ hΩm hp G).trans (T.apply_ae_eq (hGg.mono fun y hy _ => hy))
  have htr1 := Rd.trace_ae_eq_of_continuousOn Rd.norm_e0 hp hL hs hq hfin
    (by rw [← range_eq_closedHalfSpace]; exact T.continuousOn_apply hgc) T.isCompact_carrier
    (fun x _ hx => T.apply_eq_zero_of_notMem _ hx) (h1.mono fun x hx _ => hx)
  have htr2 : Ω.trace hp L G =ᵐ[volume] fun x' => g x' := by
    filter_upwards [Ω.trace_ae_eq_comp_graphMap hp hL hs hq
      (Ω.intrinsicNorm_lt_top_of_modNorm hp L hq hG).1 hgc hGg] with x' hx'
    rw [hx', Function.comp_apply, Rd.LipschitzGraph.flat_graphMap]
  refine Lp.ext ?_
  filter_upwards [htr1, T'.applyLp_ae convex_univ BesovAtlas.interior_univ_bdry_nonempty
    MeasurableSet.univ hp (Ω.trace hp L G), T'.apply_ae_eq (htr2.mono fun x' hx' _ => hx')]
    with x' h1 h2 h3
  rw [h1, h2, h3]
  exact chartChange_apply_coe he he' c hc hcs g x'

/-- **The trace commutes with a change of charts**: for `F ∈ L_p(ℝ^n)` with a finite
`B^{s+1/p}_{p,q}`-norm of order `L > s + 1/p`, `Tr (T F) = T^∂ (Tr F)` on `H₀`. The partial sums
`G_J` of the reproducing formula are continuous, so the identity holds for them
(`Manifold.trace_chartChange_applyLp_of_continuous`); they converge to `F` in `B^{1/p}_{p,1}`,
where `T` and the trace are bounded, and `Tr G_J → Tr F` in `L_p(H₀)`, where `T^∂` is bounded. -/
theorem trace_chartChange_applyLp_of_modNorm {L : ℕ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s)
    (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {F : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin n)))}
    (hF : ‖F‖ₑ + lqNorm q (fun k => dyadicWeight (s + 1 / p.toReal) k * Rd.lpModulus p L F k) < ⊤) :
    (flatDomain n).trace hp L ((BesovAtlas.chartChange he he' c hc hcs).applyLp
        Rd.BesovDomain.convex Rd.BesovDomain.interior_nonempty
        (Rd.BesovDomain.measurableSet _) hp F) =
      (boundaryChartChange he he' c hc hcs).applyLp convex_univ
        BesovAtlas.interior_univ_bdry_nonempty MeasurableSet.univ hp
        ((flatDomain n).trace hp L F) := by
  have hp1 : 1 ≤ p := Fact.out
  have hpr : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le hp1 hp
  have hpinv0 : 0 < 1 / p.toReal := by positivity
  have hpL : 1 / p.toReal < L := by linarith
  have hσ0 : 0 < s + 1 / p.toReal := by positivity
  set Ω := flatDomain n
  set T := BesovAtlas.chartChange he he' c hc hcs
  set hΩm := Rd.BesovDomain.measurableSet (range (𝓡∂ n))
  set TL := T.applyLp Rd.BesovDomain.convex Rd.BesovDomain.interior_nonempty hΩm hp
  set TL' := (boundaryChartChange he he' c hc hcs).applyLp convex_univ
    BesovAtlas.interior_univ_bdry_nonempty MeasurableSet.univ hp
  set b := Ω.coneBump
  have hGfin : ∀ J, ‖b.partialSum hp L J F‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * Rd.lpModulus p L (b.partialSum hp L J F) k) < ⊤ :=
    fun J => b.modNorm_partialSum_lt_top hp L J hσ0 hsL hq F
  -- intrinsic norms of the images
  obtain ⟨C, hC, hTle⟩ := T.modNormOn_applyLp_le Rd.BesovDomain.convex
    Rd.BesovDomain.interior_nonempty hΩm hp hL hσ0 hsL hq
  have hint : ∀ {H : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin n)))},
      ‖H‖ₑ + lqNorm q (fun k => dyadicWeight (s + 1 / p.toReal) k * Rd.lpModulus p L H k) < ⊤ →
        Ω.intrinsicNorm hp L (s + 1 / p.toReal) q (TL H) < ⊤ := fun {H} hH => by
    have h := (hTle H).trans_lt (ENNReal.mul_lt_top hC.lt_top hH)
    rw [modNormOn_range_eq hΩm] at h
    exact Ω.intrinsicNorm_lt_top hp L _ hq h
  -- the left sides converge
  obtain ⟨C1, hC1, hT1⟩ := T.modNormOn_applyLp_le Rd.BesovDomain.convex
    Rd.BesovDomain.interior_nonempty hΩm hp hL hpinv0 hpL le_rfl
  obtain ⟨K, hK, hKle⟩ := Ω.enorm_trace_le_modNormOn hp L
  have happ := b.tendsto_modNorm_sub_partialSum hp hL hpinv0 (by linarith) hpL hq hF
  have hb : Tendsto (fun J => K * (C1 * (‖F - b.partialSum hp L J F‖ₑ + lqNorm 1 (fun k =>
      dyadicWeight (1 / p.toReal) k * Rd.lpModulus p L (F - b.partialSum hp L J F) k))))
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul happ (Or.inr hC1))
      (Or.inr hK)
  have hleft : Tendsto (fun J => Ω.trace hp L (TL (b.partialSum hp L J F))) atTop
      (𝓝 (Ω.trace hp L (TL F))) := by
    rw [tendsto_iff_edist_tendsto_0]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => zero_le)
      fun J => ?_
    rw [edist_comm, eDist_eq_eNorm_sub, ← Ω.trace_sub hp L hs hq (hint hF) (hint (hGfin J)),
      ← map_sub TL F (b.partialSum hp L J F)]
    refine (hKle _).trans (mul_le_mul' le_rfl ?_)
    rw [← modNormOn_range_eq hΩm]
    exact hT1 _
  -- the right sides converge
  have hright : Tendsto (fun J => TL' (Ω.trace hp L (b.partialSum hp L J F))) atTop
      (𝓝 (TL' (Ω.trace hp L F))) :=
    (TL'.continuous.tendsto _).comp (Ω.tendsto_trace_partialSum b hp hL hs hsL hq hF)
  have hpart : ∀ J, Ω.trace hp L (TL (b.partialSum hp L J F)) =
      TL' (Ω.trace hp L (b.partialSum hp L J F)) := fun J =>
    trace_chartChange_applyLp_of_continuous he he' c hc hcs hp hL hs hsL hq (hGfin J)
      (b.continuous_partialSum_rep hp L J F) (b.partialSum_ae hp L J F)
  simp_rw [hpart] at hleft
  exact tendsto_nhds_unique hleft hright

/-- **The trace commutes with a change of charts** for `G` with a finite intrinsic
`B^{s+1/p}_{p,q}`-norm of order `L > s + 1/p` on the closed half-space: extend `G` to `ℝ^n`
(the half-space is a Besov domain); neither side sees the extension. -/
theorem trace_chartChange_applyLp {L : ℕ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s)
    (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {G : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin n)))}
    (hG : Rd.modNormOn (Rd.BesovDomain.measurableSet (range (𝓡∂ n))) L (s + 1 / p.toReal) q
      G < ⊤) :
    (flatDomain n).trace hp L ((BesovAtlas.chartChange he he' c hc hcs).applyLp
        Rd.BesovDomain.convex Rd.BesovDomain.interior_nonempty
        (Rd.BesovDomain.measurableSet _) hp G) =
      (boundaryChartChange he he' c hc hcs).applyLp convex_univ
        BesovAtlas.interior_univ_bdry_nonempty MeasurableSet.univ hp
        ((flatDomain n).trace hp L G) := by
  have hσ0 : 0 < s + 1 / p.toReal := by positivity
  obtain ⟨C, hC, hext⟩ := Rd.BesovDomain.exists_extension (Ω := range (𝓡∂ n)) p hp L
    (s + 1 / p.toReal) hσ0 hsL q hq
  obtain ⟨F, hFG, hFle⟩ := hext G hG
  have hF := hFle.trans_lt (ENNReal.mul_lt_top hC.lt_top hG)
  have hcut : (flatDomain n).cutoff F = (flatDomain n).cutoff G := by
    rw [cutoff_eq_indicatorLp (Rd.BesovDomain.measurableSet _),
      cutoff_eq_indicatorLp (Rd.BesovDomain.measurableSet _)]
    exact hFG
  rw [← (BesovAtlas.chartChange he he' c hc hcs).applyLp_eq_of_indicatorLp_eq hp hFG,
    ← (flatDomain n).trace_congr hp L hcut]
  exact trace_chartChange_applyLp_of_modNorm he he' c hc hcs hp hL hs hsL hq hF

end Commutation

/-! ### Extensions from the boundary hyperplane -/

/-- **Extensions from the boundary hyperplane**: for `G ∈ L_p(H₀)` with
`‖G‖_p + ‖(2^(ks) ω_r(G, 2^(-k))_p)_k‖_{ℓ_q} < ∞`, `r = ⌊s⌋ + 1`, the extension `E G` of moment
order `r` (`Rd.LipschitzGraph.graphExtension` of the flat graph) has a finite
`B^{s+1/p}_{p,q}`-norm of order `L` and the trace `Tr (E G) = G`
(`Rd.LipschitzGraph.trace_flatExtension`). -/
theorem exists_flatGraphExtension (hp : p ≠ ⊤) {L : ℕ} (hL : 2 ≤ L) {s : ℝ} (hs : 0 < s)
    (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {G : Lp ℂ p (volume : Measure (bdry n))}
    (hG : ‖G‖ₑ + lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p (⌊s⌋₊ + 1) G k) < ⊤) :
    ∃ F : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin n))),
      ‖F‖ₑ + lqNorm q (fun k =>
        dyadicWeight (s + 1 / p.toReal) k * Rd.lpModulus p L F k) < ⊤ ∧
      (flatDomain n).trace hp L F = G := by
  have hr : 1 ≤ ⌊s⌋₊ + 1 := Nat.le_add_left 1 _
  have hX : (flatDomain n).graphBump.localMeansNorm hp (⌊s⌋₊ + 1) s q G < ⊤ :=
    ((flatDomain n).graphBump.localMeansNorm_le hp _ s hq G).trans_lt
      (ENNReal.mul_lt_top ((flatDomain n).graphBump.upperConst_ne_top _ s).lt_top hG)
  obtain ⟨K, hK, hle⟩ := Rd.LipschitzGraph.modNorm_flatExtension_le_localMeansNorm
    (Rd.e0 : EuclideanSpace ℝ (Fin n)) Rd.norm_e0 hp (⌊s⌋₊ + 1) hs hsL hq
  exact ⟨_, (hle G hX).trans_lt (ENNReal.mul_lt_top hK.lt_top hX),
    Rd.LipschitzGraph.trace_flatExtension _ _ hp hL hr hs hsL hq hX⟩

/-! ### The trace on the boundary -/

namespace BesovAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (𝓡∂ n) ∞ M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (A : BesovAtlas (𝓡∂ n) M) (μ : Measure M) [IsSmoothMeasure (𝓡∂ n) μ] (hp : p ≠ ⊤)

/-- The **trace on the boundary** of `f ∈ L_p(μ)` in the atlas `A`:
`Tr_A f = ∑_i θ_i · Tr(piece_i f) ∘ P ∘ κ_i` on the chart sources, with the trace `Tr` of order
`L` of the half-space and the projection `P` onto `H₀`. On `∂M` the points `κ_i x` lie in `H₀`. -/
noncomputable def boundaryTrace (L : ℕ) (f : Lp ℂ p μ) (x : M) : ℂ :=
  ∑ i, (A.chart i).source.indicator (fun x => (A.theta i x : ℂ) *
    (flatDomain n).trace hp L (A.pieceLp μ hp i f) ((flatDomain n).proj (A.ext i x))) x

/-- **The boundary pieces of the trace**, pointwise on `H₀`: the `k`-th boundary piece of
`Tr_A f` is `∑_i T^∂_{ki} (Tr (piece_i f))`, since `ψ_k θ_i` is the cut-off of `T^∂_{ki}`. -/
theorem boundaryPiece_boundaryTrace_eq_sum (L : ℕ) (f : Lp ℂ p μ) (k : Fin A.n) (x' : bdry n) :
    A.boundaryPiece k (A.boundaryTrace μ hp L f) x' =
      ∑ i, (A.boundaryTransition A k i).apply
        ((flatDomain n).trace hp L (A.pieceLp μ hp i f)) x' := by
  rw [boundaryPiece, piece]
  by_cases hx : (x' : EuclideanSpace ℝ (Fin n)) ∈ (A.ext k).target
  · rw [indicator_of_mem hx, boundaryTrace, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hz : (A.ext k).symm x' ∈ (A.chart i).source
    · have hU : (x' : EuclideanSpace ℝ (Fin n)) ∈
          ((𝓡∂ n).extendCoordChange (A.chart k) (A.chart i)).source :=
        (mem_coordChange_source _ _).2 ⟨hx, hz⟩
      have hΦ := coe_proj_coordChange (A.chart_mem k) (A.chart_mem i) hU
      have hmem : A.ext i ((A.ext k).symm x') ∈ (A.ext i).target :=
        (A.ext i).map_source (by rw [OpenPartialHomeomorph.extend_source]; exact hz)
      rw [indicator_of_mem hz, Rd.CutoffDiffeo.apply, indicator_of_mem]
      swap
      · exact ⟨mem_univ _, (mem_coordChange_source_iff_of_bdry (e := A.chart k)
          (e' := A.chart i) x').2 hU⟩
      change _ = (A.transition A k i).chi
        (((flatDomain n).proj ((𝓡∂ n).extendCoordChange (A.chart k) (A.chart i) x') : bdry n) :
          EuclideanSpace ℝ (Fin n)) * (flatDomain n).trace hp L (A.pieceLp μ hp i f)
            ((flatDomain n).proj ((𝓡∂ n).extendCoordChange (A.chart k) (A.chart i) x'))
      rw [hΦ, coordChange_apply]
      change _ = (A.ext i).target.indicator (fun y => ((A.psi k ((A.ext i).symm y) *
        A.theta i ((A.ext i).symm y) : ℝ) : ℂ)) (A.ext i ((A.ext k).symm x')) * _
      rw [indicator_of_mem hmem, (A.ext i).left_inv
        (by rw [OpenPartialHomeomorph.extend_source]; exact hz)]
      push_cast
      ring
    · rw [indicator_of_notMem hz, mul_zero, Rd.CutoffDiffeo.apply, indicator_of_notMem]
      intro h
      exact hz ((mem_coordChange_source _ _).1 ((mem_coordChange_source_iff_of_bdry
        (e := A.chart k) (e' := A.chart i) x').1 h.2)).2
  · rw [indicator_of_notMem hx]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Rd.CutoffDiffeo.apply, indicator_of_notMem]
    intro h
    exact hx ((mem_coordChange_source _ _).1 ((mem_coordChange_source_iff_of_bdry
      (e := A.chart k) (e' := A.chart i) x').1 h.2)).1

/-- **The traces of the pieces of two atlases**: for `s > 0`, `L > s + 1/p` and
`f ∈ B^{s+1/p}_{p,q}(M)`, `Tr (piece_i f) = ∑_j T^∂_{ij} (Tr (piece'_j f))`. The pieces satisfy
`piece_i f = ∑_j T_{ij} (piece'_j f)`, and the trace commutes with the changes of charts
(`Manifold.trace_chartChange_applyLp`). -/
theorem trace_pieceLp_eq_sum (A' : BesovAtlas (𝓡∂ n) M) {L : ℕ} (hL : 1 ≤ L) {s : ℝ}
    (hs : 0 < s) (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q) {f : Lp ℂ p μ}
    (hf : A'.MemBesov hp (s + 1 / p.toReal) q f) (i : Fin A.n) :
    (flatDomain n).trace hp L (A.pieceLp μ hp i f) = ∑ j, (A.boundaryTransition A' i j).applyLp
      convex_univ interior_univ_bdry_nonempty MeasurableSet.univ hp
        ((flatDomain n).trace hp L (A'.pieceLp μ hp j f)) := by
  have hσ0 : 0 < s + 1 / p.toReal := by positivity
  set Ω := flatDomain n
  set hΩm := Rd.BesovDomain.measurableSet (range (𝓡∂ n))
  have hG := fun j => hf.modNormOn_pieceLp_lt_top hp A' hσ0 hsL hq j
  have hint : ∀ j, Ω.intrinsicNorm hp L (s + 1 / p.toReal) q ((A.transition A' i j).applyLp
      Rd.BesovDomain.convex Rd.BesovDomain.interior_nonempty hΩm hp (A'.pieceLp μ hp j f)) < ⊤ :=
    fun j => by
      obtain ⟨C, hC, hle⟩ :=
        (A.transition A' i j).modNormOn_applyLp_le_modNormOn hp hL hσ0 hsL hq
      have h := (hle _ (hG j)).trans_lt (ENNReal.mul_lt_top hC.lt_top (hG j))
      rw [modNormOn_range_eq hΩm] at h
      exact Ω.intrinsicNorm_lt_top hp L _ hq h
  rw [A.pieceLp_eq_sum A' μ hp i f,
    Ω.trace_finsetSum_of_intrinsicNorm hp L hs hq _ fun j _ => hint j]
  exact Finset.sum_congr rfl fun j _ =>
    trace_chartChange_applyLp _ _ _ _ _ hp hL hs hsL hq (hG j)

/-- **The boundary pieces of the trace are the traces of the pieces**: for `s > 0`, `L > s + 1/p`
and `f ∈ B^{s+1/p}_{p,q}(M)`, the `k`-th boundary piece of `Tr_A f` is `Tr (piece_k f)` almost
everywhere on `H₀`: both are `∑_i T^∂_{ki} (Tr (piece_i f))`. -/
theorem boundaryPiece_boundaryTrace {L : ℕ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s)
    (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q) {f : Lp ℂ p μ}
    (hf : A.MemBesov hp (s + 1 / p.toReal) q f) (k : Fin A.n) :
    A.boundaryPiece k (A.boundaryTrace μ hp L f) =ᵐ[volume]
      (flatDomain n).trace hp L (A.pieceLp μ hp k f) := by
  set Ω := flatDomain n
  rw [A.trace_pieceLp_eq_sum μ hp A hL hs hsL hq hf k]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => (A.boundaryTransition A k i).applyLp
      convex_univ interior_univ_bdry_nonempty MeasurableSet.univ hp
        (Ω.trace hp L (A.pieceLp μ hp i f))),
    ae_all_iff.2 fun i => (A.boundaryTransition A k i).applyLp_ae convex_univ
      interior_univ_bdry_nonempty MeasurableSet.univ hp (Ω.trace hp L (A.pieceLp μ hp i f))]
    with x' h1 h2
  rw [h1, A.boundaryPiece_boundaryTrace_eq_sum μ hp L f k x']
  exact Finset.sum_congr rfl fun i _ => (h2 i).symm

/-- **The trace does not depend on the atlas**: for two Besov atlases `A, A'` and
`f ∈ B^{s+1/p}_{p,q}(M)`, the boundary pieces for `A` of `Tr_{A'} f` are the traces of the pieces
of `f` for `A`, as for `Tr_A f`. -/
theorem boundaryPiece_boundaryTrace_of_atlas (A' : BesovAtlas (𝓡∂ n) M) {L : ℕ} (hL : 1 ≤ L)
    {s : ℝ} (hs : 0 < s) (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q) {f : Lp ℂ p μ}
    (hf : A'.MemBesov hp (s + 1 / p.toReal) q f) (i : Fin A.n) :
    A.boundaryPiece i (A'.boundaryTrace μ hp L f) =ᵐ[volume]
      (flatDomain n).trace hp L (A.pieceLp μ hp i f) := by
  set Ω := flatDomain n
  rw [A.trace_pieceLp_eq_sum μ hp A' hL hs hsL hq hf i]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun j =>
      (A.boundaryTransition A' i j).applyLp convex_univ interior_univ_bdry_nonempty
        MeasurableSet.univ hp (Ω.trace hp L (A'.pieceLp μ hp j f))),
    ae_all_iff.2 fun j => ((A.boundaryTransition A' i j).applyLp_ae convex_univ
      interior_univ_bdry_nonempty MeasurableSet.univ hp _).trans
        ((A.boundaryTransition A' i j).apply_ae_eq
          ((A'.boundaryPiece_boundaryTrace μ hp hL hs hsL hq hf j).mono fun y hy _ => hy.symm))]
    with x' h1 h2
  rw [h1, A.boundaryPiece_eq_sum A' i _ x']
  exact Finset.sum_congr rfl fun j _ => (h2 j).symm

/-- **The trace is bounded**: for `s > 0`, `1 ≤ q ≤ ∞` and `L > s + 1/p` there is `C < ∞` such
that for every `f ∈ B^{s+1/p}_{p,q}(M)` each boundary piece of `Tr_A f` agrees almost everywhere
with some `G ∈ L_p(H₀)` of Besov quasi-norm
`‖G‖_p + ‖(2^(js) ω_{⌊s⌋+1}(G, 2^(-j))_p)_j‖_{ℓ_q} ≤ C ‖f‖_{A, L, s+1/p, q}`, with the Besov
quasi-norm of the atlas with differences of order `L` (`Manifold.BesovAtlas.besovNorm`). `G` is
the trace of the piece of `f` (`Manifold.BesovAtlas.boundaryPiece_boundaryTrace`), bounded by the
trace theorem of the half-space (`Rd.LipschitzGraph.modNorm_trace_le_flat`); the piece is one
term of the sum `‖f‖_{A, L, s+1/p, q}`. -/
theorem exists_boundaryTrace_norm_le {L : ℕ} {s : ℝ} (hs : 0 < s)
    (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : Lp ℂ p μ, A.MemBesov hp (s + 1 / p.toReal) q f → ∀ k,
      ∃ G : Lp ℂ p (volume : Measure (bdry n)),
        (G : bdry n → ℂ) =ᵐ[volume] A.boundaryPiece k (A.boundaryTrace μ hp L f) ∧
        ‖G‖ₑ + lqNorm q (fun j => dyadicWeight s j * Rd.lpModulus p (⌊s⌋₊ + 1) G j) ≤
          C * A.besovNorm hp L (s + 1 / p.toReal) q f := by
  have hσ0 : 0 < s + 1 / p.toReal := by positivity
  have hL : 1 ≤ L := Nat.cast_pos.1 (hσ0.trans hsL)
  have hr : 1 ≤ ⌊s⌋₊ + 1 := Nat.le_add_left 1 _
  have hsr : s < ((⌊s⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    exact Nat.lt_floor_add_one s
  obtain ⟨K, hK, hle⟩ := Rd.LipschitzGraph.modNorm_trace_le_flat
    (Rd.e0 : EuclideanSpace ℝ (Fin n)) Rd.norm_e0 hp L hr hs hsr hq
  refine ⟨K, hK, fun f hf k =>
    ⟨_, (A.boundaryPiece_boundaryTrace μ hp hL hs hsL hq hf k).symm, ?_⟩⟩
  have hG := hf.modNormOn_pieceLp_lt_top hp A hσ0 hsL hq k
  have hk := A.modNormOn_pieceLp_le_besovNorm hp L (s + 1 / p.toReal) q f k
  rw [modNormOn_range_eq] at hG hk
  exact (hle _ hG).trans (mul_le_mul' le_rfl hk)

/-- **The trace maps into the boundary space**: for `s > 0`, `1 ≤ q ≤ ∞`, `L > s + 1/p` and
`f ∈ B^{s+1/p}_{p,q}(M)`, the trace `Tr_A f` lies in `B^s_{p,q}(∂M)`: the quasi-norm bound
`Manifold.BesovAtlas.exists_boundaryTrace_norm_le`, with `‖f‖_{A, L, s+1/p, q} < ∞`
(`Manifold.BesovAtlas.memBesov_iff_besovNorm_lt_top`). -/
theorem memBoundaryBesov_boundaryTrace {L : ℕ} {s : ℝ} (hs : 0 < s)
    (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q) {f : Lp ℂ p μ}
    (hf : A.MemBesov hp (s + 1 / p.toReal) q f) :
    A.MemBoundaryBesov p s q (A.boundaryTrace μ hp L f) := by
  obtain ⟨C, hC, h⟩ := A.exists_boundaryTrace_norm_le μ hp hs hsL hq
  have hfin := (A.memBesov_iff_besovNorm_lt_top hp (by positivity) hsL hq f).1 hf
  intro k
  obtain ⟨G, hG, hle⟩ := h f hf k
  exact ⟨G, hG, hle.trans_lt (ENNReal.mul_lt_top hC.lt_top hfin)⟩

/-- **The trace of a continuous function is its restriction to the boundary**: for `s > 0`,
`1 ≤ q ≤ ∞`, `L > s + 1/p` and `f ∈ B^{s+1/p}_{p,q}(M)` with a continuous representative
`g : M → ℂ`, every boundary piece of `Tr_A f` agrees almost everywhere with the boundary piece of
`g`, the restriction of `(ψ_k g) ∘ κ_k⁻¹` to `H₀`. The boundary pieces of `Tr_A f` are the traces
of the pieces of `f` (`Manifold.BesovAtlas.boundaryPiece_boundaryTrace`); the piece
`(ψ_k g) ∘ κ_k⁻¹` is continuous on the closed half-space and vanishes off a compact set
(`Manifold.BesovAtlas.continuousOn_piece`), so its trace is its restriction to `H₀`
(`Rd.trace_ae_eq_of_continuousOn`). -/
theorem boundaryPiece_boundaryTrace_of_continuous {L : ℕ} {s : ℝ} (hs : 0 < s)
    (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q) {f : Lp ℂ p μ}
    (hf : A.MemBesov hp (s + 1 / p.toReal) q f) {g : M → ℂ} (hg : Continuous g)
    (hfg : (f : M → ℂ) =ᵐ[μ] g) (k : Fin A.n) :
    A.boundaryPiece k (A.boundaryTrace μ hp L f) =ᵐ[volume] A.boundaryPiece k g := by
  have hσ0 : 0 < s + 1 / p.toReal := by positivity
  have hL : 1 ≤ L := Nat.cast_pos.1 (hσ0.trans hsL)
  have hG := hf.modNormOn_pieceLp_lt_top hp A hσ0 hsL hq k
  rw [modNormOn_range_eq] at hG
  have hpg : A.pieceLp μ hp k f =ᵐ[volume] A.piece k g :=
    (A.pieceLp_ae μ hp k f).trans
      (A.piece_ae_eq k (Lp.stronglyMeasurable f) hg.stronglyMeasurable hfg)
  refine (A.boundaryPiece_boundaryTrace μ hp hL hs hsL hq hf k).trans ?_
  exact Rd.trace_ae_eq_of_continuousOn Rd.norm_e0 hp hL hs hq hG
    (by rw [← range_eq_closedHalfSpace]; exact A.continuousOn_piece k hg)
    (A.isCompact_pieceCarrier k) (fun x _ hx => A.piece_eq_zero_of_notMem k g hx)
    (hpg.mono fun x hx _ => hx)

/-- **The trace is onto**: for `s > 0` and `L ≥ 2` with `L > s + 1/p`, every
`g ∈ B^s_{p,q}(∂M)` is the trace of some `f ∈ B^{s+1/p}_{p,q}(M)`, in the sense that the boundary
pieces of `Tr_A f` and of `g` agree almost everywhere. The function is
`f = ∑_k θ_k · (E G_k) ∘ κ_k` with the extensions `E G_k` of the boundary pieces of `g`
(`Manifold.exists_flatGraphExtension`); its pieces are `piece_i f = ∑_k T_{ik} (E G_k)`, whose
traces are `∑_k T^∂_{ik} G_k`, the `i`-th boundary piece of `g`. -/
theorem exists_boundaryTrace_eq {L : ℕ} (hL : 2 ≤ L) {s : ℝ} (hs : 0 < s)
    (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q) {g : M → ℂ}
    (hg : A.MemBoundaryBesov p s q g) :
    ∃ f : Lp ℂ p μ, A.MemBesov hp (s + 1 / p.toReal) q f ∧
      ∀ i, A.boundaryPiece i (A.boundaryTrace μ hp L f) =ᵐ[volume] A.boundaryPiece i g := by
  have hσ0 : 0 < s + 1 / p.toReal := by positivity
  have hL1 : 1 ≤ L := by omega
  set Ω := flatDomain n
  set hΩm := Rd.BesovDomain.measurableSet (range (𝓡∂ n))
  choose G hGae hGfin using hg
  choose F hFfin hFtr using fun k => exists_flatGraphExtension hp hL hs hsL hq (hGfin k)
  set f := ∑ k, A.chartLiftLp μ hp k (F k)
  have hf : A.MemBesov hp (s + 1 / p.toReal) q f :=
    MemBesov.finsetSum hp A hq _ fun k _ => A.memBesov_chartLiftLp hp k hL1 hσ0 hsL hq (hFfin k)
  refine ⟨f, hf, fun i => ?_⟩
  have hint : ∀ k, Ω.intrinsicNorm hp L (s + 1 / p.toReal) q ((A.transition A i k).applyLp
      Rd.BesovDomain.convex Rd.BesovDomain.interior_nonempty hΩm hp (F k)) < ⊤ := fun k => by
    obtain ⟨C, hC, hle⟩ := (A.transition A i k).modNormOn_applyLp_le Rd.BesovDomain.convex
      Rd.BesovDomain.interior_nonempty hΩm hp hL1 hσ0 hsL hq
    have h := (hle (F k)).trans_lt (ENNReal.mul_lt_top hC.lt_top (hFfin k))
    rw [modNormOn_range_eq hΩm] at h
    exact Ω.intrinsicNorm_lt_top hp L _ hq h
  have htr : Ω.trace hp L (A.pieceLp μ hp i f) = ∑ k, (A.boundaryTransition A i k).applyLp
      convex_univ interior_univ_bdry_nonempty MeasurableSet.univ hp (G k) := by
    rw [A.pieceLp_finsetSum hp i]
    simp_rw [A.pieceLp_chartLiftLp hp i]
    rw [Ω.trace_finsetSum_of_intrinsicNorm hp L hs hq _ fun k _ => hint k]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hFtr k]
    exact trace_chartChange_applyLp_of_modNorm _ _ _ _ _ hp hL1 hs hsL hq (hFfin k)
  refine (A.boundaryPiece_boundaryTrace μ hp hL1 hs hsL hq hf i).trans ?_
  rw [htr]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun k => (A.boundaryTransition A i k).applyLp
      convex_univ interior_univ_bdry_nonempty MeasurableSet.univ hp (G k)),
    ae_all_iff.2 fun k => ((A.boundaryTransition A i k).applyLp_ae convex_univ
      interior_univ_bdry_nonempty MeasurableSet.univ hp (G k)).trans
        ((A.boundaryTransition A i k).apply_ae_eq ((hGae k).mono fun y hy _ => hy))]
    with x' h1 h2
  rw [h1, A.boundaryPiece_eq_sum A i g x']
  exact Finset.sum_congr rfl fun k _ => h2 k

/-- **The trace theorem on a compact manifold with boundary**: for `1 ≤ p < ∞`, `s > 0`,
`1 ≤ q ≤ ∞` and an order `L ≥ 2` of the trace with `L > s + 1/p`, `B^s_{p,q}(∂M)` is the trace
space of `B^{s+1/p}_{p,q}(M)`: `g ∈ B^s_{p,q}(∂M)` iff the boundary pieces of `g` agree almost
everywhere with those of `Tr_A f` for some `f ∈ B^{s+1/p}_{p,q}(M)`. -/
theorem memBoundaryBesov_iff_exists_boundaryTrace {L : ℕ} (hL : 2 ≤ L) {s : ℝ} (hs : 0 < s)
    (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q) (g : M → ℂ) :
    A.MemBoundaryBesov p s q g ↔ ∃ f : Lp ℂ p μ, A.MemBesov hp (s + 1 / p.toReal) q f ∧
      ∀ i, A.boundaryPiece i (A.boundaryTrace μ hp L f) =ᵐ[volume] A.boundaryPiece i g := by
  refine ⟨A.exists_boundaryTrace_eq μ hp hL hs hsL hq, fun ⟨f, hf, htr⟩ i => ?_⟩
  obtain ⟨G, hG, hGfin⟩ := A.memBoundaryBesov_boundaryTrace μ hp hs hsL hq hf i
  exact ⟨G, hG.trans (htr i), hGfin⟩

end BesovAtlas

end Manifold

/-! ### The boundary of a smooth bounded domain -/

namespace Rd.SmoothDomain

open Manifold

variable {n : ℕ} [NeZero n] (Ω : SmoothDomain n) {p : ℝ≥0∞} [Fact (1 ≤ p)]
  (A : Manifold.BesovAtlas (𝓡∂ n) (closure Ω.carrier)) (hp : p ≠ ⊤)

/-- **The trace theorem on the boundary of a smooth bounded domain**: for the closure of a smooth
bounded domain `Ω`, a compact manifold with boundary (`Rd.SmoothDomain.isManifold`) with the
Lebesgue measure (`Rd.SmoothDomain.volumeOn`), a Besov atlas `A`, `1 ≤ p < ∞`, `s > 0`,
`1 ≤ q ≤ ∞` and an order `L ≥ 2` with `L > s + 1/p`, the chart-defined space `B^s_{p,q}(∂Ω)` is the
trace space of `B^{s+1/p}_{p,q}(closure Ω)`
(`Manifold.BesovAtlas.memBoundaryBesov_iff_exists_boundaryTrace`). -/
theorem memBoundaryBesov_iff_exists_boundaryTrace {L : ℕ} (hL : 2 ≤ L) {s : ℝ} (hs : 0 < s)
    (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q) (g : closure Ω.carrier → ℂ) :
    A.MemBoundaryBesov p s q g ↔ ∃ f : Lp ℂ p Ω.volumeOn, A.MemBesov hp (s + 1 / p.toReal) q f ∧
      ∀ i, A.boundaryPiece i (A.boundaryTrace Ω.volumeOn hp L f) =ᵐ[volume] A.boundaryPiece i g :=
  A.memBoundaryBesov_iff_exists_boundaryTrace Ω.volumeOn hp hL hs hsL hq g

/-- **The trace of a continuous function on the closure of a smooth bounded domain** is its
restriction to the boundary: for `f ∈ B^{s+1/p}_{p,q}(closure Ω)` with a continuous representative
`g`, `s > 0`, `1 ≤ q ≤ ∞` and `L > s + 1/p`, every boundary piece of `Tr_A f` agrees almost
everywhere with that of `g` (`Manifold.BesovAtlas.boundaryPiece_boundaryTrace_of_continuous`). -/
theorem boundaryPiece_boundaryTrace_of_continuous {L : ℕ} {s : ℝ} (hs : 0 < s)
    (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q) {f : Lp ℂ p Ω.volumeOn}
    (hf : A.MemBesov hp (s + 1 / p.toReal) q f) {g : closure Ω.carrier → ℂ} (hg : Continuous g)
    (hfg : (f : closure Ω.carrier → ℂ) =ᵐ[Ω.volumeOn] g) (k : Fin A.n) :
    A.boundaryPiece k (A.boundaryTrace Ω.volumeOn hp L f) =ᵐ[volume] A.boundaryPiece k g :=
  A.boundaryPiece_boundaryTrace_of_continuous Ω.volumeOn hp hs hsL hq hf hg hfg k

end Rd.SmoothDomain
