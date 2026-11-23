/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedSupport
import Mathlib.Topology.MetricSpace.Cover

/-! # Sigma compactness from finite weighted volume -/

@[expose] public section

open Bundle Function MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal Manifold NNReal Topology

namespace CutCur

private theorem countable_net_of_finite_openPosMeasure {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] {r : ℝ≥0} (hr : 0 < r) :
    ∃ s : Set X, s.Countable ∧ Metric.IsCover r univ s := by
  obtain ⟨s, hs⟩ := zorn_subset {s : Set X | Metric.IsSeparated r s} (by
    intro c hc hchain
    refine ⟨⋃₀ c, ?_, fun _ ht ↦ subset_sUnion_of_mem ht⟩
    intro x hx y hy hxy
    obtain ⟨u, hu, hxu⟩ := mem_sUnion.mp hx
    obtain ⟨v, hv, hyv⟩ := mem_sUnion.mp hy
    rcases hchain.total hu hv with huv | hvu
    · exact hc hv (huv hxu) hyv hxy
    · exact hc hu hxu (hvu hyv) hxy)
  let balls : s → Set X := fun x ↦ Metric.eball (x : X) ((r / 2 : ℝ≥0) : ℝ≥0∞)
  have hr' : (0 : ℝ≥0∞) < ((r / 2 : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast (show 0 < r / 2 by positivity)
  have hdisjoint : Pairwise (Disjoint on balls) := by
    intro x y hxy
    refine Set.disjoint_left.mpr fun z hz hz' ↦ ?_
    have hle : edist (x : X) (y : X) ≤ (r : ℝ≥0∞) := by
      have h1 : edist z (x : X) < ((r / 2 : ℝ≥0) : ℝ≥0∞) := hz
      have h2 : edist z (y : X) < ((r / 2 : ℝ≥0) : ℝ≥0∞) := hz'
      calc
        _ ≤ edist z (x : X) + edist z (y : X) := by
          rw [edist_comm z (x : X)]
          exact edist_triangle _ z _
        _ ≤ ((r / 2 : ℝ≥0) : ℝ≥0∞) + ((r / 2 : ℝ≥0) : ℝ≥0∞) := add_le_add h1.le h2.le
        _ = _ := by exact_mod_cast add_halves r
    exact (not_le_of_gt (hs.prop x.2 y.2 (Subtype.val_injective.ne hxy))) hle
  have hpos (x : s) : 0 < μ (balls x) := Metric.isOpen_eball.measure_pos μ
    ⟨x, Metric.mem_eball_self hr'⟩
  have hcount := Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ)
    (fun x : s ↦ (show IsOpen (balls x) from Metric.isOpen_eball).measurableSet) hdisjoint
  have huniv : {x : s | 0 < μ (balls x)} = univ := eq_univ_of_forall hpos
  rw [huniv] at hcount
  refine ⟨s, Set.countable_coe_iff.mp (Set.countable_univ_iff.mp hcount), ?_⟩
  apply Metric.IsCover.of_maximal_isSeparated (s := univ)
  exact ⟨⟨subset_univ s, hs.prop⟩, fun t ht hst ↦ hs.2 ht.2 hst⟩

private theorem separableSpace_of_finite_openPosMeasure {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] : SeparableSpace X := by
  let r (n : ℕ) : ℝ≥0 := 1 / (n + 1)
  choose S hcount hcover using fun n : ℕ ↦ countable_net_of_finite_openPosMeasure μ
    (r := r n) (by dsimp [r]; positivity)
  refine ⟨⋃ n, S n, Set.countable_iUnion hcount, fun x ↦ ?_⟩
  rw [EMetric.mem_closure_iff]
  intro ε hε
  obtain ⟨d, hd₀, hdε⟩ := exists_between hε
  lift d to ℝ≥0 using ne_top_of_lt hdε
  have hd : 0 < (d : ℝ) := by exact_mod_cast hd₀
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hd
  have hrn : (r n : ℝ≥0∞) < (d : ℝ≥0∞) := by
    rw [ENNReal.coe_lt_coe]
    change 1 / ((n : ℝ≥0) + 1) < d
    exact_mod_cast hn
  obtain ⟨y, hy, hxy⟩ := hcover n (mem_univ x)
  exact ⟨y, mem_iUnion.mpr ⟨n, hy⟩, lt_of_le_of_lt hxy (hrn.trans hdε)⟩

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

/-- Finite weighted volume is positive on every nonempty open set. This makes the
modelled extended metric space separable, and local compactness gives σ-compactness. -/
theorem sigmaCompactSpace_of_finite_weightedVolume {V : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
    {μ : Measure M} (hμ : IsWeightedVolume F μ V) [IsFiniteMeasure μ] : SigmaCompactSpace M := by
  let : μ.IsOpenPosMeasure := isOpenPosMeasure_of_weighted F hV hμ
  let : SeparableSpace M := separableSpace_of_finite_openPosMeasure μ
  let : SecondCountableTopology M := UniformSpace.secondCountable_of_separable M
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace F M
  infer_instance

end CutCur
