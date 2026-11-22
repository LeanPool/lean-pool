/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic.Linarith

/-! # Locally uniform existence time for actual manifold integral curves
A C¹ tangent field admits integral curves with one common positive lifetime for
all initial points in a neighborhood. The curves are produced by the actual
coordinate Picard theorem and pulled back through the actual chart.
-/

@[expose] public section
open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [BoundarylessManifold I M]

/-- Uniform local existence near each initial point, without a supplied local
flow or a supplied uniform lifetime. -/
theorem exists_continuous_localIntegralFlow
    {X : (x : M) → TangentSpace I x} {x₀ : M}
    (hX : ContMDiffAt I I.tangent 1 (T% X) x₀) :
    ∃ ε > (0 : ℝ), ∃ U ∈ 𝓝 x₀, ∃ Φ : M × ℝ → M,
      ContinuousOn Φ (U ×ˢ Ioo (-ε) ε) ∧
      ∀ x ∈ U, Φ (x, 0) = x ∧
        IsMIntegralCurveOn (fun t ↦ Φ (x, t)) X (Ioo (-ε) ε) := by
  let e := extChartAt I x₀
  let z := e x₀
  let F : E → E := fun y ↦ tangentCoordChange I (e.symm y) x₀ (e.symm y) (X (e.symm y))
  have hF : ContDiffAt ℝ 1 F z := by
    rw [contMDiffAt_iff] at hX
    exact (hX.2.contDiffAt (range_mem_nhds_isInteriorPoint
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀)))).snd
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hF
  obtain ⟨α, hα, hαcont⟩ := (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have hz : z ∈ Metric.closedBall z (r : ℝ) := Metric.mem_closedBall_self r.property
  have hαzero : α (z, 0) = z := (hα z hz).1
  have hdomain : Metric.closedBall z (r : ℝ) ×ˢ Icc (0 - ε) (0 + ε) ∈ 𝓝 (z, 0) := by
    apply prod_mem_nhds
    · exact Metric.closedBall_mem_nhds z hr
    · exact Icc_mem_nhds (by linarith) (by linarith)
  have htarget : α ⁻¹' interior e.target ∈ 𝓝 (z, 0) := by
    apply (hαcont.continuousAt hdomain).preimage_mem_nhds
    rw [hαzero]
    exact isOpen_interior.mem_nhds
      ((I.isInteriorPoint_iff).mp (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀)))
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp (inter_mem htarget hdomain)
  obtain ⟨δ, hδ, hδv⟩ := Metric.mem_nhds_iff.mp hv
  let θ := min ε δ
  have hθ : 0 < θ := lt_min hε hδ
  have hnear : ∀ᶠ x in 𝓝 x₀, e x ∈ u ∧ x ∈ e.source := by
    filter_upwards [(continuousAt_extChartAt x₀).preimage_mem_nhds hu,
      extChartAt_source_mem_nhds (I := I) x₀] with x hx hxsrc
    exact ⟨hx, hxsrc⟩
  let U : Set M := {x | e x ∈ u ∧ x ∈ e.source}
  have hU : U ∈ 𝓝 x₀ := hnear
  have hgood (x : M) (hx : x ∈ U) (t : ℝ) (ht : t ∈ Ioo (-θ) θ) :
      α (e x, t) ∈ interior e.target ∧
        (e x ∈ Metric.closedBall z (r : ℝ) ∧ t ∈ Icc (0 - ε) (0 + ε)) := by
    have htv : t ∈ v := hδv (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_right ε δ)) ht.1,
        ht.2.trans_le (min_le_right ε δ)⟩)
    exact huv ⟨hx.1, htv⟩
  let Φ : M × ℝ → M := fun p ↦ e.symm (α (e p.1, p.2))
  have hΦcont : ContinuousOn Φ (U ×ˢ Ioo (-θ) θ) := by
    apply (continuousOn_extChartAt_symm x₀).comp
    · apply hαcont.comp
      · apply ContinuousOn.prodMk
        · exact (continuousOn_extChartAt x₀).comp continuousOn_fst
            (fun p hp ↦ hp.1.2)
        · exact continuousOn_snd
      · intro p hp
        exact (hgood p.1 hp.1 p.2 hp.2).2
    · intro p hp
      exact interior_subset (hgood p.1 hp.1 p.2 hp.2).1
  refine ⟨θ, hθ, U, hU, Φ, hΦcont, ?_⟩
  intro x hx
  have hxball : e x ∈ Metric.closedBall z (r : ℝ) := (hgood x hx 0 ⟨by linarith, hθ⟩).2.1
  refine ⟨?_, ?_⟩
  · change e.symm (α (e x, 0)) = x
    rw [(hα (e x) hxball).1, e.left_inv hx.2]
  · intro t ht
    let f : ℝ → E := fun t ↦ α (e x, t)
    let xₜ : M := e.symm (f t)
    have htime : t ∈ Ioo (0 - ε) (0 + ε) := by
      have hm := min_le_left ε δ
      constructor <;> dsimp [θ] at ht <;> linarith [ht.1, ht.2]
    have hd : HasDerivAt f (F (f t)) t :=
      ((hα (e x) hxball).2 t (hgood x hx t ht).2.2).hasDerivAt
        (Icc_mem_nhds htime.1 htime.2)
    have hf3 : f t ∈ e.target := interior_subset (hgood x hx t ht).1
    have hft1 : xₜ ∈ e.source := e.map_target hf3
    have hft2 := mem_extChartAt_source (I := I) xₜ
    apply HasMFDerivAt.hasMFDerivWithinAt
    refine ⟨(continuousAt_extChartAt_symm'' hf3).comp hd.continuousAt, ?_⟩
    apply HasDerivWithinAt.hasFDerivWithinAt
    simp only [mfld_simps]
    refine HasDerivAt.hasDerivWithinAt ?_
    change HasDerivAt ((extChartAt I xₜ ∘ e.symm) ∘ f) (X xₜ) t
    rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := X xₜ) hft2,
      ← tangentCoordChange_comp (I := I) (w := xₜ) (x := x₀) (y := xₜ)
        (z := xₜ) (v := (X xₜ : E)) ⟨⟨hft2, hft1⟩, hft2⟩]
    apply HasFDerivAt.comp_hasDerivAt _ _ hd
    apply HasFDerivWithinAt.hasFDerivAt (s := range I) _
      (mem_nhds_iff.mpr ⟨interior e.target,
        subset_trans interior_subset (extChartAt_target_subset_range ..),
        isOpen_interior, (hgood x hx t ht).1⟩)
    change HasFDerivWithinAt (extChartAt I xₜ ∘ e.symm)
      (tangentCoordChange I x₀ xₜ xₜ) (range I) (f t)
    rw [← e.right_inv hf3]
    exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

/-- Uniform lifetime corollary of the actual continuous local flow. -/
theorem exists_eventually_isMIntegralCurveOn
    {X : (x : M) → TangentSpace I x} {x₀ : M}
    (hX : ContMDiffAt I I.tangent 1 (T% X) x₀) :
    ∃ ε > (0 : ℝ), ∀ᶠ x in 𝓝 x₀,
      ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ X (Ioo (-ε) ε) := by
  obtain ⟨ε, hε, U, hU, Φ, _, hΦ⟩ := exists_continuous_localIntegralFlow hX
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hU] with x hx
  exact ⟨fun t ↦ Φ (x, t), hΦ x hx⟩

end CutoffRigidity
