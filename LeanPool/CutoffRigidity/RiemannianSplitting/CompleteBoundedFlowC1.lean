/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.ManifoldC1LocalFlow
public import LeanPool.CutoffRigidity.RiemannianSplitting.CompleteBoundedFlowContinuity
public import Mathlib.Geometry.Manifold.Diffeomorph

/-! # Actual C¹ diffeomorphisms supplied by the complete bounded-field flow
Actual coordinate Picard differentiation supplies the local C¹ statement.
Actual ODE uniqueness and the actual flow group law propagate it globally.
-/

@[expose] public section
open Bundle Set Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] [BoundarylessManifold I M] [CompleteSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
  {C : ℝ≥0} (hbound : ∀ x, ‖X x‖ₑ ≤ C)

/-- The actual canonical global flow has C¹ time slices locally in both
initial position and time, as derived from coordinate Picard differentiation. -/
theorem exists_contMDiffOn_completeBoundedFlow_local (x₀ : M) :
    ∃ ε > (0 : ℝ), ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧
      ∀ t ∈ Ioo (-ε) ε, ContMDiffOn I I 1
        (fun x ↦ completeBoundedFlow hX hbound x t) U := by
  obtain ⟨ε, hε, U, hU, Φ, _, hΦ, hΦC1⟩ :=
    exists_contMDiff_localIntegralFlow (hX.contMDiffAt (x := x₀))
  refine ⟨ε, hε, interior U, isOpen_interior, mem_interior_iff_mem_nhds.mpr hU, ?_⟩
  intro t ht
  apply ((hΦC1 t ht).mono interior_subset).congr
  intro x hx
  have hxU : x ∈ U := interior_subset hx
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := 0) ⟨by linarith, hε⟩ hX
    ((completeBoundedFlow_isMIntegralCurve hX hbound x).isMIntegralCurveOn _)
    (hΦ x hxU).2
    ((completeBoundedFlow_zero hX hbound x).trans (hΦ x hxU).1.symm)
  exact heq ht

/-- Every actual time slice is C¹ globally; no differentiability of the flow
is supplied as a premise. -/
theorem contMDiff_completeBoundedFlow_timeSlice (t : ℝ) :
    ContMDiff I I 1 (fun x : M ↦ completeBoundedFlow hX hbound x t) := by
  intro x₀
  let G : Set ℝ := {s | ContMDiffAt I I 1 (fun x ↦ completeBoundedFlow hX hbound x s) x₀}
  have transfer {ε : ℝ} {U : Set M} (hU : IsOpen U)
      (hlocal : ∀ q ∈ Ioo (-ε) ε, ContMDiffOn I I 1
        (fun x ↦ completeBoundedFlow hX hbound x q) U) {s r : ℝ} (hs : s ∈ G)
      (hstate : completeBoundedFlow hX hbound x₀ s ∈ U)
      (htime : r - s ∈ Ioo (-ε) ε) : r ∈ G := by
    change ContMDiffAt I I 1 (fun x ↦ completeBoundedFlow hX hbound x s) x₀ at hs
    have hlocAt := (hlocal (r - s) htime).contMDiffAt (hU.mem_nhds hstate)
    have hcomp := hlocAt.comp x₀ hs
    have heq : ((fun x ↦ completeBoundedFlow hX hbound x (r - s)) ∘
        (fun x ↦ completeBoundedFlow hX hbound x s)) =
        (fun x ↦ completeBoundedFlow hX hbound x r) := by
      funext x
      simp only [Function.comp_apply]
      rw [← completeBoundedFlow_add, sub_add_cancel]
    rwa [heq] at hcomp
  have hGopen : IsOpen G := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    obtain ⟨ε, hε, U, hU, hstate, hlocal⟩ :=
      exists_contMDiffOn_completeBoundedFlow_local hX hbound
        (completeBoundedFlow hX hbound x₀ s)
    apply mem_of_superset (Ioo_mem_nhds (by linarith : s - ε < s)
      (by linarith : s < s + ε))
    intro r hr
    exact transfer hU hlocal hs hstate ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hGclosed : IsClosed G := by
    apply isClosed_of_closure_subset
    intro r hr
    obtain ⟨ε, hε, U, hU, hstate, hlocal⟩ :=
      exists_contMDiffOn_completeBoundedFlow_local hX hbound
        (completeBoundedFlow hX hbound x₀ r)
    let J := (completeBoundedFlow hX hbound x₀) ⁻¹' U ∩ Ioo (r - ε) (r + ε)
    have hJopen : IsOpen J :=
      (hU.preimage (continuous_completeBoundedFlow_orbit hX hbound x₀)).inter isOpen_Ioo
    have hrJ : r ∈ J := ⟨hstate, by constructor <;> linarith⟩
    obtain ⟨s, hsJ, hsG⟩ := mem_closure_iff.mp hr J hJopen hrJ
    exact transfer hU hlocal hsG hsJ.1
      ⟨by linarith [hsJ.2.2], by linarith [hsJ.2.1]⟩
  have hzero : (0 : ℝ) ∈ G := by
    change ContMDiffAt I I 1 (fun x ↦ completeBoundedFlow hX hbound x 0) x₀
    simp only [completeBoundedFlow_zero]
    convert! (contMDiffAt_id (I := I) (x := x₀)) using 1
  have hGuniv : G = univ := (show IsClopen G from ⟨hGclosed, hGopen⟩).eq_univ ⟨0, hzero⟩
  exact (show t ∈ G from hGuniv ▸ mem_univ t)

/-- The genuine time-t flow is a C¹ diffeomorphism with genuine inverse the
negative-time flow of the same vector field. -/
noncomputable def completeBoundedFlowDiffeomorph (t : ℝ) : Diffeomorph I I M M 1 where
  toEquiv := completeBoundedFlowEquiv hX hbound t
  contMDiff_toFun := contMDiff_completeBoundedFlow_timeSlice hX hbound t
  contMDiff_invFun := contMDiff_completeBoundedFlow_timeSlice hX hbound (-t)

end CutoffRigidity
