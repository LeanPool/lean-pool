/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.ManifoldUniformLocalFlow
public import LeanPool.CutoffRigidity.RiemannianSplitting.C1LocalExtension
public import LeanPool.CutoffRigidity.RiemannianSplitting.DifferentiableCoordinateLocalFlow

/-! # Actual manifold local flows with C¹ initial-point dependence
The actual coordinate field is genuinely extended near the chart center, its
actual C¹ Picard family is constructed, and actual chart pullback gives the
manifold family. No differentiable-flow assumption is introduced.
-/

@[expose] public section
open Bundle Set Filter Function
open scoped Manifold ContDiff Topology

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]

/-- Actual local manifold integral flows are jointly continuous and C¹ in the
initial point, derived solely from the actual C¹ tangent field. -/
theorem exists_contMDiff_localIntegralFlow
    {X : (x : M) → TangentSpace I x} {x₀ : M}
    (hX : ContMDiffAt I I.tangent 1 (T% X) x₀) :
    ∃ ε > (0 : ℝ), ∃ U ∈ 𝓝 x₀, ∃ Φ : M × ℝ → M,
      ContinuousOn Φ (U ×ˢ Ioo (-ε) ε) ∧
      (∀ x ∈ U, Φ (x, 0) = x ∧
        IsMIntegralCurveOn (fun t ↦ Φ (x, t)) X (Ioo (-ε) ε)) ∧
      ∀ t ∈ Ioo (-ε) ε, ContMDiffOn I I 1 (fun x ↦ Φ (x, t)) U := by
  let e := extChartAt I x₀
  let z := e x₀
  let F : E → E := fun y ↦ tangentCoordChange I (e.symm y) x₀ (e.symm y) (X (e.symm y))
  have hF : ContDiffAt ℝ 1 F z := by
    rw [contMDiffAt_iff] at hX
    exact (hX.2.contDiffAt (range_mem_nhds_isInteriorPoint
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀)))).snd
  obtain ⟨G, hG, hGF⟩ := exists_contDiff_one_eventuallyEq_of_contDiffAt hF
  obtain ⟨r, hr, θ, hθ, α, hαC, hα, hαC1⟩ := exists_contDiff_coordinate_localFlow hG z
  have hzball : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  have hαzero : α z 0 = z := (hα z hzball).1
  have hdomain : Metric.ball z r ×ˢ Ioo (-θ) θ ∈ 𝓝 (z, 0) :=
    (Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨hzball, by constructor <;> linarith⟩
  let W := interior e.target ∩ {y | G y = F y}
  have hW : W ∈ 𝓝 z := inter_mem
    (isOpen_interior.mem_nhds ((I.isInteriorPoint_iff).mp
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀)))) hGF
  have hαW : (uncurry α) ⁻¹' W ∈ 𝓝 (z, 0) := by
    apply (hαC.continuousAt hdomain).preimage_mem_nhds
    simpa only [uncurry_apply_pair, hαzero] using hW
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp (inter_mem hαW hdomain)
  obtain ⟨ε, hε, hεv⟩ := Metric.mem_nhds_iff.mp hv
  let U : Set M := {x | e x ∈ u ∧ x ∈ e.source}
  have hU : U ∈ 𝓝 x₀ := by
    filter_upwards [(continuousAt_extChartAt x₀).preimage_mem_nhds hu,
      extChartAt_source_mem_nhds (I := I) x₀] with x hx hs
    exact ⟨hx, hs⟩
  have hgood (x : M) (hx : x ∈ U) (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      α (e x) t ∈ W ∧ (e x ∈ Metric.ball z r ∧ t ∈ Ioo (-θ) θ) := by
    have htv : t ∈ v := by
      apply hεv
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨ht.1, ht.2⟩
    exact huv (show (e x, t) ∈ u ×ˢ v from ⟨hx.1, htv⟩)
  let Φ : M × ℝ → M := fun p ↦ e.symm (α (e p.1) p.2)
  have hΦC : ContinuousOn Φ (U ×ˢ Ioo (-ε) ε) := by
    apply (continuousOn_extChartAt_symm x₀).comp
    · apply hαC.comp (f := fun p : M × ℝ ↦ (e p.1, p.2))
      · have chartSource (p : M × ℝ) (hp : p ∈ U ×ˢ Ioo (-ε) ε) :
            p.1 ∈ (extChartAt I x₀).source := hp.1.2
        exact ((continuousOn_extChartAt x₀).comp continuousOn_fst chartSource).prodMk
          continuousOn_snd
      · intro p hp
        exact (hgood p.1 hp.1 p.2 hp.2).2
    · intro p hp
      exact interior_subset (hgood p.1 hp.1 p.2 hp.2).1.1
  refine ⟨ε, hε, U, hU, Φ, hΦC, ?_, ?_⟩
  · intro x hx
    have hxball := (hgood x hx 0 ⟨by linarith, hε⟩).2.1
    refine ⟨?_, ?_⟩
    · change e.symm (α (e x) 0) = x
      rw [(hα (e x) hxball).1, e.left_inv hx.2]
    · intro t ht
      let f : ℝ → E := α (e x)
      let xₜ : M := e.symm (f t)
      have hd : HasDerivAt f (F (f t)) t := by
        have hh := (hα (e x) hxball).2 t (hgood x hx t ht).2.2
        rw [(hgood x hx t ht).1.2] at hh
        exact hh
      have hf3 : f t ∈ e.target := interior_subset (hgood x hx t ht).1.1
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
          isOpen_interior, (hgood x hx t ht).1.1⟩)
      change HasFDerivWithinAt (extChartAt I xₜ ∘ e.symm)
        (tangentCoordChange I x₀ xₜ xₜ) (range I) (f t)
      rw [← e.right_inv hf3]
      exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩
  · intro t ht
    have hx₀ : x₀ ∈ U := mem_of_mem_nhds hU
    have hαt := hαC1 t (hgood x₀ hx₀ t ht).2.2
    change ContMDiffOn I I 1 (e.symm ∘ (fun x ↦ α (e x) t)) U
    apply (contMDiffOn_extChartAt_symm x₀).comp (f := fun x ↦ α (e x) t)
    · apply hαt.contMDiffOn.comp (f := e)
      · exact contMDiffOn_extChartAt.mono (fun x hx ↦ by simpa [e, extChartAt_source] using hx.2)
      · exact fun x hx ↦ (hgood x hx t ht).2.1
    · intro x hx
      change α (e x) t ∈ e.target
      exact interior_subset (hgood x hx t ht).1.1

end CutoffRigidity
