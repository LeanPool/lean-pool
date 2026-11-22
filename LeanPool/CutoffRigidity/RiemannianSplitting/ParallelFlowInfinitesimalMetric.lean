/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianCoordinateLocalEvolution
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianChartFlowDifferential
public import LeanPool.CutoffRigidity.RiemannianSplitting.ManifoldChartODE
public import LeanPool.CutoffRigidity.RiemannianSplitting.TangentMetricGerm
public import LeanPool.CutoffRigidity.RiemannianSplitting.CompleteBoundedFlowC1

/-! # Actual parallel flow metric derivative at time zero
The true coordinate Picard family, actual chart tangent maps, and actual ODE
uniqueness identify the true canonical flow pairing with the constructed
coordinate pairing. Levi-Civita parallelism then proves its actual derivative
vanishes, without an isometric-flow premise.
-/

@[expose] public section
open Bundle Set Filter Function Metric
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] [BoundarylessManifold I M] [CompleteSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

/-- The original Riemannian metric pairing of the true canonical flow's actual
tangent differential has derivative zero at time zero for an actual parallel
field. No infinitesimal-isometry premise is supplied. -/
theorem hasDerivAt_completeBoundedFlow_gram_zero_of_parallel
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    {C : ℝ≥0} (hbound : ∀ x, ‖X x‖ₑ ≤ C)
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
    (x₀ : M) (u v : TangentSpace I x₀) :
    HasDerivAt (fun t ↦ inner ℝ
      ((mfderiv I I (fun y ↦ completeBoundedFlow hX hbound y t) x₀) u)
      ((mfderiv I I (fun y ↦ completeBoundedFlow hX hbound y t) x₀) v)) 0 0 := by
  obtain ⟨G, _, _, r, hr, ε, hε, α, L, _, hα, _, hαC1, hgood, hGram⟩ :=
    exists_parallel_coordinate_localEvolution x₀ (hX.contMDiffAt (x := x₀)) (hpX x₀)
  let e := extChartAt I x₀
  let z := e x₀
  let u' : E := u
  let v' : E := v
  have hnear : ∀ᶠ y in 𝓝 x₀, e y ∈ ball z r ∧ y ∈ e.source := by
    filter_upwards [(continuousAt_extChartAt x₀).preimage_mem_nhds (ball_mem_nhds z hr),
      extChartAt_source_mem_nhds (I := I) x₀] with y hy hs
    exact ⟨hy, hs⟩
  have heq (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      (fun y ↦ completeBoundedFlow hX hbound y t) =ᶠ[𝓝 x₀]
        (fun y ↦ e.symm (α (e y) t)) := by
    filter_upwards [hnear] with y hy
    have hcoord (s : ℝ) (hs : s ∈ Ioo (-ε) ε) :
        HasDerivAt (α (e y)) (chartCoordinateField (I := I) x₀ X (α (e y) s)) s := by
      have hd := (hα (e y) hy.1).2 s hs
      rw [(hgood (e y) hy.1 s hs).2] at hd
      exact hd
    have hcurve := isMIntegralCurveOn_chart_inverse_of_coordinateODE x₀ hcoord
      (fun s hs ↦ (hgood (e y) hy.1 s hs).1)
    have hzero : (e.symm ∘ α (e y)) 0 = y := by
      rw [comp_apply, (hα (e y) hy.1).1, e.left_inv hy.2]
    have huniq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
      (t₀ := 0) ⟨by linarith, hε⟩ hX
      ((completeBoundedFlow_isMIntegralCurve hX hbound y).isMIntegralCurveOn _) hcurve
      ((completeBoundedFlow_zero hX hbound y).trans hzero.symm)
    exact huniq ht
  have hnorm (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      inner ℝ
        ((mfderiv I I (fun y ↦ completeBoundedFlow hX hbound y t) x₀) u)
        ((mfderiv I I (fun y ↦ completeBoundedFlow hX hbound y t) x₀) v) =
      chartMetric (I := I) x₀ (α z t)
        ((fderiv ℝ (fun y ↦ α y t) z) u') ((fderiv ℝ (fun y ↦ α y t) z) v') := by
    rw [inner_mfderiv_eq_of_eventuallyEq (heq t ht) u v]
    have hAt := ((hαC1 t ht).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self
        hr))).differentiableAt one_ne_zero
    have hm := inner_mfderiv_chart_conjugate x₀ hAt
      (hgood z (mem_ball_self hr) t ht).1 u' v'
    simpa only [chartFrame_self] using hm
  apply (hGram u' v').congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (by linarith : -ε < 0) hε] with t ht
  exact hnorm t ht

end CutoffRigidity
