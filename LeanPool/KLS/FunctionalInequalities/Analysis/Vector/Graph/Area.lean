/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Vector.Graph.Sandwich

/-! # The codimension-`m` area formula for `C¹` graphs

The `k`-dimensional measure of the graph of a `C¹`
`K`-valued map over a measurable set is the integral of `√det (1 + Dγᵀ Dγ)`.

One step differs from codimension one and is the reason this step needs its own partition.  The
codimension-one proof uses that the Jacobian `√(1 + ‖a‖²)` is **globally `1`-Lipschitz** in the
slope, so that closeness of the derivatives transfers to closeness of the Jacobians.  In
codimension `m` the Jacobian `√det (1 + AᵀA)` is **not** uniformly Lipschitz — already for
`A = t • id` on a two-dimensional parameter space it grows like `1 + t²` — so
`exists_approximating_partition_with_jacobian` below asks the partition to control the Jacobian
**directly**, which continuity supplies.  Everything after that mirrors the codimension-one file,
and the limit lemmas `tendsto_aux`, `tendsto_aux'` are graph-independent and reused unchanged.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace FunctionalInequalities.Analysis

variable {H K V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace H] [BorelSpace H] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ K] in
/-- The graph volume factor is continuous in the slope. -/
theorem continuous_graphMapLinear_normDet (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V) :
    Continuous (fun A : H →L[ℝ] K =>
      LinearMap.normDet ((graphMapLinear ι κ A : H →ₗ[ℝ] V))) := by
  refine continuous_normDet.comp ?_
  exact continuous_const.add ((ContinuousLinearMap.compL ℝ H K V
    κ.toContinuousLinearMap).continuous)

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ K] in
/-- The approximating partition, **also controlling the Jacobian**.  In codimension one this extra
clause is free from a global Lipschitz bound on the Jacobian; in codimension `m` no such bound
exists, so it is imposed here and supplied by continuity. -/
theorem exists_approximating_partition_with_jacobian (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    {γ : H → K} (hγ : ContDiff ℝ 1 γ) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ (t : ℕ → Set H) (A : ℕ → (H →L[ℝ] K)),
      (∀ n, MeasurableSet (t n)) ∧ Pairwise (Function.onFun Disjoint t) ∧
      (⋃ n, t n) = Set.univ ∧
      (∀ n, ApproximatesLinearOn (vectorGraphMap ι κ γ) (graphMapLinear ι κ (A n)) (t n) ε) ∧
      (∀ n, ∀ z ∈ t n,
        |LinearMap.normDet ((graphMapLinear ι κ (fderiv ℝ γ z) : H →ₗ[ℝ] V))
          - LinearMap.normDet ((graphMapLinear ι κ (A n) : H →ₗ[ℝ] V))| ≤ (ε : ℝ)) := by
  classical
  have hpos : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hgc : Continuous (fderiv ℝ γ) := hγ.continuous_fderiv one_ne_zero
  have hJc : Continuous (fun z : H =>
      LinearMap.normDet ((graphMapLinear ι κ (fderiv ℝ γ z) : H →ₗ[ℝ] V))) :=
    (continuous_graphMapLinear_normDet ι κ).comp hgc
  have hrad : ∀ y₀ : H, ∃ r : ℝ, 0 < r ∧
      (∀ z ∈ Metric.ball y₀ r, ‖fderiv ℝ γ z - fderiv ℝ γ y₀‖ ≤ (ε : ℝ)) ∧
      (∀ z ∈ Metric.ball y₀ r,
        |LinearMap.normDet ((graphMapLinear ι κ (fderiv ℝ γ z) : H →ₗ[ℝ] V))
          - LinearMap.normDet ((graphMapLinear ι κ (fderiv ℝ γ y₀) : H →ₗ[ℝ] V))| ≤ (ε : ℝ)) := by
    intro y₀
    obtain ⟨r₁, hr₁, hball₁⟩ := Metric.continuousAt_iff.mp hgc.continuousAt (ε : ℝ) hpos
    obtain ⟨r₂, hr₂, hball₂⟩ := Metric.continuousAt_iff.mp hJc.continuousAt (ε : ℝ) hpos
    refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun z hz => ?_, fun z hz => ?_⟩
    · have := hball₁ (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_left _ _))
      rw [dist_eq_norm] at this
      exact this.le
    · have := hball₂ (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _))
      rw [Real.dist_eq] at this
      exact this.le
  choose r hrpos hrball hrJ using hrad
  have hfnhds : ∀ x : H, Metric.ball x (r x) ∈ 𝓝 x := fun x => Metric.ball_mem_nhds x (hrpos x)
  obtain ⟨c, hc, hcu⟩ := TopologicalSpace.countable_cover_nhds hfnhds
  have hcne : c.Nonempty := by
    have hmem : (0 : H) ∈ (Set.univ : Set H) := Set.mem_univ _
    rw [← hcu] at hmem
    obtain ⟨x, hx, -⟩ := Set.mem_iUnion₂.mp hmem
    exact ⟨x, hx⟩
  obtain ⟨w, hw⟩ := hc.exists_eq_range hcne
  set B : ℕ → Set H := fun n => Metric.ball (w n) (r (w n)) with hB
  have hBu : (⋃ n, B n) = Set.univ := by rw [← hcu, hw, Set.biUnion_range]
  refine ⟨fun n => disjointed B n, fun n => fderiv ℝ γ (w n), ?_, ?_, ?_, ?_, ?_⟩
  · exact fun n => MeasurableSet.disjointed (fun i => Metric.isOpen_ball.measurableSet) n
  · exact disjoint_disjointed B
  · rw [iUnion_disjointed, hBu]
  · intro n
    exact approximatesLinearOn_vectorGraphMap ι κ hγ (hrball (w n)) (disjointed_subset B n)
  · intro n z hz
    exact hrJ (w n) z (disjointed_subset B n hz)

/-- Two-sided estimate at scale `ε`. -/
theorem vectorGraphMap_estimates (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) {γ : H → K} (hγ : ContDiff ℝ 1 γ)
    {s : Set H} (hs : MeasurableSet s) {ε : ℝ≥0} (hε : 0 < ε) :
    μH[(Module.finrank ℝ H : ℝ)] (vectorGraphMap ι κ γ '' s)
        ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ H : ℝ)
          * (∫⁻ y in s, ENNReal.ofReal
                (LinearMap.normDet ((graphMapLinear ι κ (fderiv ℝ γ y) : H →ₗ[ℝ] V)))
              ∂(μH[(Module.finrank ℝ H : ℝ)] : Measure H)
            + ε * μH[(Module.finrank ℝ H : ℝ)] s)
      ∧ ∫⁻ y in s, ENNReal.ofReal
              (LinearMap.normDet ((graphMapLinear ι κ (fderiv ℝ γ y) : H →ₗ[ℝ] V)))
            ∂(μH[(Module.finrank ℝ H : ℝ)] : Measure H)
        ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ H : ℝ)
            * μH[(Module.finrank ℝ H : ℝ)] (vectorGraphMap ι κ γ '' s)
          + ε * μH[(Module.finrank ℝ H : ℝ)] s := by
  classical
  set k : ℝ := (Module.finrank ℝ H : ℝ) with hk
  set μ : Measure H := (μH[k] : Measure H) with hμ
  set Ψ : H → V := vectorGraphMap ι κ γ with hΨ
  set J : H → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (LinearMap.normDet ((graphMapLinear ι κ (fderiv ℝ γ y) : H →ₗ[ℝ] V))) with hJ
  have hJmeas : Measurable J :=
    ENNReal.measurable_ofReal.comp (measurable_vectorGraphJacobian ι κ γ)
  have hgcont : Continuous γ := hγ.continuous
  obtain ⟨t, A, hmeas, hdisj, hcover, happ, hjac⟩ :=
    exists_approximating_partition_with_jacobian ι κ hγ hε
  set u : ℕ → Set H := fun n => s ∩ t n with hu
  have humeas : ∀ n, MeasurableSet (u n) := fun n => hs.inter (hmeas n)
  have hudisj : Pairwise (Function.onFun Disjoint u) := fun i j hij =>
    Disjoint.mono Set.inter_subset_right Set.inter_subset_right (hdisj hij)
  have huunion : (⋃ n, u n) = s := by rw [hu, ← Set.inter_iUnion, hcover, Set.inter_univ]
  have hsub : ∀ n, u n ⊆ t n := fun n => Set.inter_subset_right
  have himgdisj : Pairwise (Function.onFun Disjoint (fun n => Ψ '' (u n))) := fun i j hij =>
    Set.disjoint_image_of_injective (vectorGraphMap_injective ι κ hperp γ) (hudisj hij)
  have himgmeas : ∀ n, MeasurableSet (Ψ '' (u n)) := fun n =>
    measurableSet_image_vectorGraphMap ι κ hperp hgcont (humeas n)
  have himg : Ψ '' s = ⋃ n, Ψ '' (u n) := by rw [← Set.image_iUnion, huunion]
  have hsplitμ : μH[k] (Ψ '' s) = ∑' n, μH[k] (Ψ '' (u n)) := by
    rw [himg, measure_iUnion himgdisj himgmeas]
  have hsplitint : ∫⁻ y in s, J y ∂μ = ∑' n, ∫⁻ y in u n, J y ∂μ := by
    rw [← huunion, lintegral_iUnion humeas hudisj]
  have hsplitmeas : μ s = ∑' n, μ (u n) := by
    rw [← huunion, measure_iUnion hudisj humeas]
  have hJcmp : ∀ n, ∀ y ∈ u n,
      ENNReal.ofReal (LinearMap.normDet ((graphMapLinear ι κ (A n) : H →ₗ[ℝ] V)))
        ≤ J y + ENNReal.ofReal (ε : ℝ) := by
    intro n y hy
    have h2 := hjac n y (hsub n hy)
    have h4 : LinearMap.normDet ((graphMapLinear ι κ (A n) : H →ₗ[ℝ] V))
        ≤ LinearMap.normDet ((graphMapLinear ι κ (fderiv ℝ γ y) : H →ₗ[ℝ] V)) + (ε : ℝ) := by
      cases abs_le.mp h2 with
      | intro hlo hhi => linarith
    calc ENNReal.ofReal (LinearMap.normDet ((graphMapLinear ι κ (A n) : H →ₗ[ℝ] V)))
        ≤ ENNReal.ofReal
            (LinearMap.normDet ((graphMapLinear ι κ (fderiv ℝ γ y) : H →ₗ[ℝ] V)) + (ε : ℝ)) :=
          ENNReal.ofReal_le_ofReal h4
      _ = J y + ENNReal.ofReal (ε : ℝ) := by
          rw [hJ, ENNReal.ofReal_add (LinearMap.normDet_nonneg _) (NNReal.coe_nonneg ε)]
  have hJcmp' : ∀ n, ∀ y ∈ u n,
      J y ≤ ENNReal.ofReal (LinearMap.normDet ((graphMapLinear ι κ (A n) : H →ₗ[ℝ] V)))
        + ENNReal.ofReal (ε : ℝ) := by
    intro n y hy
    have h2 := hjac n y (hsub n hy)
    have h4 : LinearMap.normDet ((graphMapLinear ι κ (fderiv ℝ γ y) : H →ₗ[ℝ] V))
        ≤ LinearMap.normDet ((graphMapLinear ι κ (A n) : H →ₗ[ℝ] V)) + (ε : ℝ) := by
      cases abs_le.mp h2 with
      | intro hlo hhi => linarith
    calc J y ≤ ENNReal.ofReal
            (LinearMap.normDet ((graphMapLinear ι κ (A n) : H →ₗ[ℝ] V)) + (ε : ℝ)) :=
          ENNReal.ofReal_le_ofReal h4
      _ = _ := by rw [ENNReal.ofReal_add (LinearMap.normDet_nonneg _) (NNReal.coe_nonneg ε)]
  constructor
  · rw [hsplitμ]
    have hterm : ∀ n, μH[k] (Ψ '' (u n))
        ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ k * (∫⁻ y in u n, J y ∂μ + ε * μ (u n)) := by
      intro n
      have h1 := hausdorffMeasure_image_vectorGraphMap_le ι κ hperp γ (A n)
        ((happ n).mono_set (hsub n))
      have h2 : ENNReal.ofReal (LinearMap.normDet ((graphMapLinear ι κ (A n) : H →ₗ[ℝ] V)))
            * μ (u n)
          ≤ ∫⁻ y in u n, J y ∂μ + ε * μ (u n) := by
        have hconst : ENNReal.ofReal
              (LinearMap.normDet ((graphMapLinear ι κ (A n) : H →ₗ[ℝ] V))) * μ (u n)
            = ∫⁻ _y in u n,
                ENNReal.ofReal (LinearMap.normDet ((graphMapLinear ι κ (A n) : H →ₗ[ℝ] V))) ∂μ := by
          rw [setLIntegral_const]
        rw [hconst]
        calc ∫⁻ _y in u n,
              ENNReal.ofReal (LinearMap.normDet ((graphMapLinear ι κ (A n) : H →ₗ[ℝ] V))) ∂μ
            ≤ ∫⁻ y in u n, (J y + ENNReal.ofReal (ε : ℝ)) ∂μ :=
              setLIntegral_mono' (humeas n) (hJcmp n)
          _ = ∫⁻ y in u n, J y ∂μ + ENNReal.ofReal (ε : ℝ) * μ (u n) := by
              rw [lintegral_add_right _ measurable_const, setLIntegral_const]
          _ = ∫⁻ y in u n, J y ∂μ + ε * μ (u n) := by rw [ENNReal.ofReal_coe_nnreal]
      calc μH[k] (Ψ '' (u n))
          ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ k
              * ENNReal.ofReal (LinearMap.normDet ((graphMapLinear ι κ (A n) : H →ₗ[ℝ] V)))
              * μH[k] (u n) := h1
        _ = ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ k
              * (ENNReal.ofReal (LinearMap.normDet ((graphMapLinear ι κ (A n) : H →ₗ[ℝ] V)))
                * μ (u n)) := by rw [mul_assoc]
        _ ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ k * (∫⁻ y in u n, J y ∂μ + ε * μ (u n)) := by gcongr
    simpa only [ENNReal.tsum_mul_left, ENNReal.tsum_add, ← hsplitint, ← hsplitmeas]
      using ENNReal.tsum_le_tsum hterm
  · rw [hsplitint]
    have hterm : ∀ n, ∫⁻ y in u n, J y ∂μ
        ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ k * μH[k] (Ψ '' (u n)) + ε * μ (u n) := by
      intro n
      have h1 := le_hausdorffMeasure_image_vectorGraphMap ι κ hperp γ (A n)
        ((happ n).mono_set (hsub n))
      calc ∫⁻ y in u n, J y ∂μ
          ≤ ∫⁻ _y in u n,
              (ENNReal.ofReal (LinearMap.normDet ((graphMapLinear ι κ (A n) : H →ₗ[ℝ] V)))
                + ENNReal.ofReal (ε : ℝ)) ∂μ :=
            setLIntegral_mono' (humeas n) (hJcmp' n)
        _ = ENNReal.ofReal (LinearMap.normDet ((graphMapLinear ι κ (A n) : H →ₗ[ℝ] V))) * μ (u n)
              + ε * μ (u n) := by
            rw [setLIntegral_const, add_mul, ENNReal.ofReal_coe_nnreal]
        _ ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ k * μH[k] (Ψ '' (u n)) + ε * μ (u n) := by gcongr
    calc ∑' n, ∫⁻ y in u n, J y ∂μ
        ≤ ∑' n, (((1 + ε : ℝ≥0) : ℝ≥0∞) ^ k * μH[k] (Ψ '' (u n)) + ε * μ (u n)) :=
          ENNReal.tsum_le_tsum hterm
      _ = ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ k * (∑' n, μH[k] (Ψ '' (u n))) + ε * ∑' n, μ (u n) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      _ = ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ k * μH[k] (Ψ '' s) + ε * μ s := by
          rw [← hsplitμ, ← hsplitmeas]

/-! ### The area formula -/

private theorem hausdorffMeasure_image_vectorGraphMap_of_finite (ι : H →ₗᵢ[ℝ] V)
    (κ : K →ₗᵢ[ℝ] V) (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ))
    {γ : H → K} (hγ : ContDiff ℝ 1 γ) {s : Set H} (hs : MeasurableSet s)
    (hsfin : (μH[(Module.finrank ℝ H : ℝ)] : Measure H) s ≠ ⊤) :
    μH[(Module.finrank ℝ H : ℝ)] (vectorGraphMap ι κ γ '' s)
      = ∫⁻ y in s, ENNReal.ofReal
          (LinearMap.normDet ((graphMapLinear ι κ (fderiv ℝ γ y) : H →ₗ[ℝ] V)))
          ∂(μH[(Module.finrank ℝ H : ℝ)] : Measure H) := by
  set n : ℕ := Module.finrank ℝ H with hn
  set μ : Measure H := (μH[(n : ℝ)] : Measure H) with hμ
  set Amea : ℝ≥0∞ := μH[(n : ℝ)] (vectorGraphMap ι κ γ '' s) with hAmea
  set I : ℝ≥0∞ := ∫⁻ y in s, ENNReal.ofReal
    (LinearMap.normDet ((graphMapLinear ι κ (fderiv ℝ γ y) : H →ₗ[ℝ] V))) ∂μ with hI
  set M : ℝ≥0∞ := μ s with hM
  have hrw : ∀ x : ℝ≥0∞, x ^ ((n : ℕ) : ℝ) = x ^ n := fun x => ENNReal.rpow_natCast x n
  have hest : ∀ ε : ℝ≥0, 0 < ε →
      Amea ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ n * (I + (ε : ℝ≥0∞) * M) ∧
      I ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ n * Amea + (ε : ℝ≥0∞) * M := by
    intro ε hε
    obtain ⟨h1, h2⟩ := vectorGraphMap_estimates ι κ hperp hγ hs hε
    rw [hrw] at h1 h2
    exact ⟨h1, h2⟩
  rcases eq_or_ne I ⊤ with hItop | hItop
  · have h2 := (hest 1 one_pos).2
    rw [hItop] at h2
    have hAtop : Amea = ⊤ := by
      by_contra hAne
      have hfin : ((1 + (1 : ℝ≥0) : ℝ≥0) : ℝ≥0∞) ^ n * Amea + ((1 : ℝ≥0) : ℝ≥0∞) * M ≠ ⊤ := by
        refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by simp) hAne, ?_⟩
        exact ENNReal.mul_ne_top (by simp) hsfin
      exact hfin (top_le_iff.mp h2)
    rw [hAtop, hItop]
  · have hAle : Amea ≤ I := by
      refine ge_of_tendsto (tendsto_aux n hsfin (X := I)) ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hest ε hε).1
    have hAne : Amea ≠ ⊤ := by
      have h1 := (hest 1 one_pos).1
      refine ne_top_of_le_ne_top ?_ h1
      exact ENNReal.mul_ne_top (by simp)
        (ENNReal.add_ne_top.mpr ⟨hItop, ENNReal.mul_ne_top (by simp) hsfin⟩)
    have hIle : I ≤ Amea := by
      refine ge_of_tendsto (tendsto_aux' n hAne hsfin) ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hest ε hε).2
    exact le_antisymm hAle hIle

/--
**vector-valued graph area: the codimension-`m` area formula for `C¹` graphs.**  The `k`-dimensional
Hausdorff
measure of the graph of a `C¹` `K`-valued map over a measurable set is the integral of the graph
volume factor `√det (1 + Dγᵀ Dγ)`.  No finiteness, boundedness or injectivity hypothesis: a graph
map is injective by construction. -/
theorem hausdorffMeasure_image_vectorGraphMap (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) {γ : H → K} (hγ : ContDiff ℝ 1 γ)
    {s : Set H} (hs : MeasurableSet s) :
    μH[(Module.finrank ℝ H : ℝ)] (vectorGraphMap ι κ γ '' s) =
      ∫⁻ y in s,
        ENNReal.ofReal
          (LinearMap.normDet
            ((graphMapLinear ι κ (fderiv ℝ γ y) :
              H →ₗ[ℝ] V))) ∂(μH[(Module.finrank ℝ H : ℝ)] : Measure H) := by
  set n : ℕ := Module.finrank ℝ H with hn
  set μ : Measure H := (μH[(n : ℝ)] : Measure H) with hμ
  set J : H → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (LinearMap.normDet ((graphMapLinear ι κ (fderiv ℝ γ y) : H →ₗ[ℝ] V))) with hJ
  have hJmeas : Measurable J :=
    ENNReal.measurable_ofReal.comp (measurable_vectorGraphJacobian ι κ γ)
  set sm : ℕ → Set H := fun m => s ∩ Metric.ball (0 : H) (m + 1) with hsm
  have hsmmeas : ∀ m, MeasurableSet (sm m) := fun m => hs.inter Metric.isOpen_ball.measurableSet
  have hsmmono : Monotone sm := by
    intro i j hij
    refine Set.inter_subset_inter_right _ (Metric.ball_subset_ball ?_)
    have : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
    linarith
  have hsmunion : (⋃ m, sm m) = s := by
    simp only [sm, ← Set.inter_iUnion, Metric.iUnion_ball_nat_succ, Set.inter_univ]
  have hsmfin : ∀ m, μ (sm m) ≠ ⊤ := by
    intro m
    exact
      ((Metric.isBounded_ball (x := (0 : H)) (r := (m : ℝ) + 1)).subset
          Set.inter_subset_right).measure_lt_top.ne
  have hLim :
    Tendsto (fun m => μH[(n : ℝ)] (vectorGraphMap ι κ γ '' sm m)) atTop
      (𝓝 (μH[(n : ℝ)] (vectorGraphMap ι κ γ '' s))) := by
    have himg : (⋃ m, vectorGraphMap ι κ γ '' sm m) = vectorGraphMap ι κ γ '' s := by
      rw [← Set.image_iUnion, hsmunion]
    rw [← himg]
    exact tendsto_measure_iUnion_atTop (fun i j hij => Set.image_mono (hsmmono hij))
  have hRlim : Tendsto (fun m => ∫⁻ y in sm m, J y ∂μ) atTop (𝓝 (∫⁻ y in s, J y ∂μ)) := by
    have hd : Directed (· ⊆ ·) sm := fun i j =>
      ⟨max i j, hsmmono (le_max_left _ _), hsmmono (le_max_right _ _)⟩
    rw [← hsmunion, setLIntegral_iUnion_of_directed J hd]
    exact tendsto_atTop_iSup fun i j hij => lintegral_mono_set (hsmmono hij)
  refine tendsto_nhds_unique hLim ?_
  have heq : ∀ m, μH[(n : ℝ)] (vectorGraphMap ι κ γ '' sm m) = ∫⁻ y in sm m, J y ∂μ := fun m =>
    hausdorffMeasure_image_vectorGraphMap_of_finite ι κ hperp hγ (hsmmeas m) (hsmfin m)
  simpa only [heq] using hRlim

/-- **The codimension-`m` area formula in the normalized convention**, integrated against
Lebesgue measure on the parameter space.  This is the form the codimension-`m` coarea formula
uses. -/
theorem hausdorffNormalized_image_vectorGraphMap (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ))
    {γ : H → K} (hγ : ContDiff ℝ 1 γ) {s : Set H} (hs : MeasurableSet s) :
    KLS.hausdorffNormalized V (Module.finrank ℝ H) (vectorGraphMap ι κ γ '' s)
      = ∫⁻ y in s, ENNReal.ofReal
          (LinearMap.normDet ((graphMapLinear ι κ (fderiv ℝ γ y) : H →ₗ[ℝ] V)))
          ∂(volume : Measure H) := by
  set k : ℕ := Module.finrank ℝ H with hk
  have hωpos : 0 < KLS.unitBallVolume k := by unfold KLS.unitBallVolume; positivity
  have hcancel : ENNReal.ofReal (KLS.unitBallVolume k / 2 ^ k)
      * ENNReal.ofReal (2 ^ k / KLS.unitBallVolume k) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [show KLS.unitBallVolume k / 2 ^ k * (2 ^ k / KLS.unitBallVolume k) = 1 by field_simp]
    exact ENNReal.ofReal_one
  rw [KLS.hausdorffNormalized, Measure.smul_apply, smul_eq_mul,
    hausdorffMeasure_image_vectorGraphMap ι κ hperp hγ hs]
  rw [hausdorffMeasure_finrank_eq_smul_volume H]
  rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← hk, ← mul_assoc, hcancel,
    one_mul]

end FunctionalInequalities.Analysis
