/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.ManifoldJointC1LocalFlow
public import LeanPool.CutoffRigidity.RiemannianSplitting.CompleteBoundedFlowC1

/-! # Genuine joint `C¹` regularity of the complete manifold flow
Local actual Picard regularity is identified by actual ODE uniqueness. The
actual group law and proved time-slice regularity propagate this to every time.
-/

@[expose] public section
open Bundle Set Filter
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace CutoffRigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] [BoundarylessManifold I M] [CompleteSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
  {C : ℝ≥0} (hbound : ∀ x, ‖X x‖ₑ ≤ C)

/-- Actual joint manifold differentiability at time zero, without a supplied
flow differentiability premise. -/
theorem contMDiffAt_completeBoundedFlow_joint_zero (x₀ : M) :
    ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I 1
      (fun p : M × ℝ ↦ completeBoundedFlow hX hbound p.1 p.2) (x₀, 0) := by
  obtain ⟨ε, hε, U, hU, Φ, _, hΦ, hΦC1⟩ :=
    exists_jointContMDiff_localIntegralFlow (hX.contMDiffAt (x := x₀))
  have hdomain : U ×ˢ Ioo (-ε) ε ∈ 𝓝 (x₀, 0) :=
    prod_mem_nhds hU (Ioo_mem_nhds (by linarith) hε)
  have hloc := hΦC1.contMDiffAt hdomain
  apply hloc.congr_of_eventuallyEq
  filter_upwards [hdomain] with p hp
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := 0) ⟨by linarith, hε⟩ hX
    ((completeBoundedFlow_isMIntegralCurve hX hbound p.1).isMIntegralCurveOn _)
    (hΦ p.1 hp.1).2
    ((completeBoundedFlow_zero hX hbound p.1).trans (hΦ p.1 hp.1).1.symm)
  exact heq hp.2

/-- The actual complete flow is jointly `C¹` in the initial point and time. -/
theorem contMDiff_completeBoundedFlow_joint :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) I 1
      (fun p : M × ℝ ↦ completeBoundedFlow hX hbound p.1 p.2) := by
  intro p
  let q : M × ℝ → M × ℝ := fun z ↦ (z.1, z.2 - p.2)
  have hq : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) 1 q p :=
    contMDiffAt_fst.prodMk (contMDiffAt_snd.sub contMDiffAt_const)
  have hq0 : q p = (p.1, 0) := by simp [q]
  have hinner := (contMDiffAt_completeBoundedFlow_joint_zero hX hbound p.1).comp_of_eq hq hq0
  have hout := (contMDiff_completeBoundedFlow_timeSlice hX hbound p.2).contMDiffAt.comp p hinner
  have heq : (fun x ↦ completeBoundedFlow hX hbound x p.2) ∘
      ((fun z : M × ℝ ↦ completeBoundedFlow hX hbound z.1 z.2) ∘ q) =
      (fun z : M × ℝ ↦ completeBoundedFlow hX hbound z.1 z.2) := by
    funext z
    change completeBoundedFlow hX hbound (completeBoundedFlow hX hbound z.1 (z.2 - p.2)) p.2 = _
    rw [← completeBoundedFlow_add]
    congr 1
    ring
  rwa [heq] at hout

end CutoffRigidity
