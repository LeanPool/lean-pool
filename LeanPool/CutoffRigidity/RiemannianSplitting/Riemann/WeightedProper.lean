/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedInterface
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedProperLength
public import Mathlib.Geometry.Manifold.Riemannian.PathELength

/-! # Complete connected Riemannian manifolds are proper

Hopf–Rinow–Cohn-Vossen: the Riemannian distance of a connected manifold is finite, it has the
approximate segment property (`CutCur.ApproxSegment`), hence a complete Riemannian manifold is
proper.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set Manifold
open scoped Manifold ContDiff ENNReal Topology

namespace CutCur

section Proper

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M]

include F


omit [IsRiemannianManifold 𝓘(ℝ, F) M] in
omit [FiniteDimensional ℝ F] in
/-- A smooth Riemannian bundle structure on the tangent bundle is in particular continuous. -/
theorem isContinuousRiemannianBundle_tangent :
    IsContinuousRiemannianBundle F (fun x : M => TangentSpace 𝓘(ℝ, F) x) := by
  obtain ⟨g, hg, hgg⟩ := (inferInstance : IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F
    (fun x : M => TangentSpace 𝓘(ℝ, F) x)).exists_contMDiff
  exact ⟨g, hg.continuous, hgg⟩

omit [FiniteDimensional ℝ F] in
/-- On a connected Riemannian manifold the distance is finite. -/
theorem edist_ne_top_of_connected [ConnectedSpace M] (x y : M) : edist x y ≠ ⊤ := by
  have := isContinuousRiemannianBundle_tangent (F := F) (M := M)
  have hopen : ∀ a : M, ∀ᶠ z in 𝓝 a, edist a z < 1 := fun a => by
    simpa only [IsRiemannianManifold.out (I := 𝓘(ℝ, F))] using
      eventually_riemannianEDist_lt 𝓘(ℝ, F) a (c := 1) one_pos
  have hcl : IsClopen {z : M | edist x z ≠ ⊤} := by
    constructor
    · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro a ha
      simp only [mem_compl_iff, mem_ofPred_eq, not_not] at ha
      filter_upwards [hopen a] with z hz
      simp only [mem_compl_iff, mem_ofPred_eq, not_not]
      have := edist_triangle x z a
      rw [edist_comm z a] at this
      rw [ha] at this
      by_contra hne
      exact absurd (this.trans_lt (ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hne, hz.trans
        ENNReal.one_lt_top⟩)) (by simp)
    · rw [isOpen_iff_mem_nhds]
      intro a ha
      filter_upwards [hopen a] with z hz
      have := edist_triangle x a z
      exact (this.trans_lt (ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 ha, hz.trans
        ENNReal.one_lt_top⟩)).ne
  have := hcl.eq_univ ⟨x, by simp⟩
  have hy : y ∈ {z : M | edist x z ≠ ⊤} := by rw [this]; trivial
  exact hy

omit [FiniteDimensional ℝ F] in
/-- The Riemannian distance has the approximate segment property. -/
theorem approxSegment_of_riemannian [ConnectedSpace M] :
    @ApproxSegment M (EMetricSpace.toMetricSpace (edist_ne_top_of_connected F)) := by
  let _ : MetricSpace M := EMetricSpace.toMetricSpace (edist_ne_top_of_connected F)
  have := isContinuousRiemannianBundle_tangent (F := F) (M := M)
  intro x y s η hs hsD hη
  have hD : edist x y = ENNReal.ofReal (dist x y) := edist_dist x y
  have hlt : riemannianEDist 𝓘(ℝ, F) x y < ENNReal.ofReal (dist x y + η) := by
    rw [← IsRiemannianManifold.out, hD]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  obtain ⟨γ, h0, h1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hlt
  have hφ : ContinuousOn (fun t => dist x (γ t)) (Icc 0 1) :=
    ((continuous_const (y := x)).dist continuous_id).comp_continuousOn hγ.continuousOn
  have hivt := intermediate_value_Icc (zero_le_one' ℝ) hφ
  have hs' : s ∈ Icc (dist x (γ 0)) (dist x (γ 1)) := by
    simp only [h0, h1, dist_self]; exact ⟨hs, hsD⟩
  obtain ⟨t, ht, hts⟩ := hivt hs'
  refine ⟨γ t, hts, ?_⟩
  have hA : riemannianEDist 𝓘(ℝ, F) x (γ t) ≤ pathELength 𝓘(ℝ, F) γ 0 t :=
    riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc_right ht.2)) h0 rfl ht.1
  have hB : riemannianEDist 𝓘(ℝ, F) (γ t) y ≤ pathELength 𝓘(ℝ, F) γ t 1 :=
    riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc_left ht.1)) rfl h1 ht.2
  have hsum := pathELength_add (I := 𝓘(ℝ, F)) (γ := γ) ht.1 ht.2
  have hAB : edist x (γ t) + edist (γ t) y < ENNReal.ofReal (dist x y + η) := by
    rw [IsRiemannianManifold.out (I := 𝓘(ℝ, F)), IsRiemannianManifold.out (I := 𝓘(ℝ, F))]
    calc _ ≤ pathELength 𝓘(ℝ, F) γ 0 t + pathELength 𝓘(ℝ, F) γ t 1 := add_le_add hA hB
      _ = pathELength 𝓘(ℝ, F) γ 0 1 := hsum
      _ < _ := hlen
  rw [edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg,
    ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hAB
  have hts' : dist x (γ t) = s := hts
  rw [hts'] at hAB
  linarith

/-- The real-valued Riemannian distance on a connected Riemannian manifold (same `edist`,
same uniformity as the given `EMetricSpace`). -/
noncomputable abbrev riemannianMetricSpace [ConnectedSpace M] : MetricSpace M :=
  EMetricSpace.toMetricSpace (edist_ne_top_of_connected F)

/-- **Hopf–Rinow–Cohn-Vossen**: a complete connected Riemannian manifold is proper. -/
theorem properSpace_of_complete_riemannian [ConnectedSpace M] [CompleteSpace M] :
    @ProperSpace M (riemannianMetricSpace F).toPseudoMetricSpace := by
  let : MetricSpace M := riemannianMetricSpace F
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace F M
  exact properSpace_of_approxSegment (approxSegment_of_riemannian F)

/-- Edist-closed balls of a complete connected Riemannian manifold are compact. -/
theorem isCompact_edist_le [ConnectedSpace M] [CompleteSpace M] (x₀ : M) {r : ℝ} (hr : 0 ≤ r) :
    IsCompact {y : M | edist x₀ y ≤ ENNReal.ofReal r} := by
  let : MetricSpace M := riemannianMetricSpace F
  have := properSpace_of_complete_riemannian (F := F) (M := M)
  have h := isCompact_closedBall x₀ r
  convert h using 1
  ext y
  simp only [mem_ofPred_eq, Metric.mem_closedBall]
  rw [edist_le_ofReal hr, dist_comm]

/-- A complete connected Riemannian manifold is `σ`-compact. -/
theorem sigmaCompactSpace_of_complete_riemannian [ConnectedSpace M] [CompleteSpace M] :
    SigmaCompactSpace M := by
  let : MetricSpace M := riemannianMetricSpace F
  have := properSpace_of_complete_riemannian (F := F) (M := M)
  infer_instance

end Proper

end CutCur
