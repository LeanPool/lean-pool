/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.CompleteBoundedFlow

/-! # Joint continuity of the actual complete bounded flow
Coordinate Picard dependence gives local joint continuity. The actual group law
and continuity of each orbit propagate it to all initial points and times.
-/

@[expose] public section
open Bundle Set Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] [BoundarylessManifold I M] [CompleteSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
  {C : ℝ≥0} (hbound : ∀ x, ‖X x‖ₑ ≤ C)

/-- The canonical actual flow inherits joint continuity from the local
coordinate Picard family, using actual ODE uniqueness on the overlap. -/
theorem exists_continuousOn_completeBoundedFlow_local (x₀ : M) :
    ∃ ε > (0 : ℝ), ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧
      ContinuousOn (fun p : M × ℝ ↦ completeBoundedFlow hX hbound p.1 p.2)
        (U ×ˢ Ioo (-ε) ε) := by
  obtain ⟨ε, hε, U, hU, Φ, hΦcont, hΦ⟩ :=
    exists_continuous_localIntegralFlow (hX.contMDiffAt (x := x₀))
  refine ⟨ε, hε, interior U, isOpen_interior, mem_interior_iff_mem_nhds.mpr hU, ?_⟩
  apply (hΦcont.mono (Set.prod_mono interior_subset Subset.rfl)).congr
  intro p hp
  have hxp : p.1 ∈ U := interior_subset hp.1
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := 0) ⟨by linarith, hε⟩ hX
    ((completeBoundedFlow_isMIntegralCurve hX hbound p.1).isMIntegralCurveOn _)
    (hΦ p.1 hxp).2
    ((completeBoundedFlow_zero hX hbound p.1).trans (hΦ p.1 hxp).1.symm)
  exact heq hp.2

/-- Every fixed-time slice of the actual global flow is continuous. -/
theorem continuous_completeBoundedFlow_timeSlice (t : ℝ) :
    Continuous (fun x : M ↦ completeBoundedFlow hX hbound x t) := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  let G : Set ℝ := {s | ContinuousAt (fun x : M ↦ completeBoundedFlow hX hbound x s) x₀}
  have transfer {ε : ℝ} {U : Set M} (hU : IsOpen U)
      (hlocal : ContinuousOn (fun p : M × ℝ ↦ completeBoundedFlow hX hbound p.1 p.2)
        (U ×ˢ Ioo (-ε) ε)) {s r : ℝ} (hs : s ∈ G)
      (hstate : completeBoundedFlow hX hbound x₀ s ∈ U)
      (htime : r - s ∈ Ioo (-ε) ε) : r ∈ G := by
    change ContinuousAt (fun x ↦ completeBoundedFlow hX hbound x s) x₀ at hs
    have hcomp := (hlocal.continuousAt
      ((hU.prod isOpen_Ioo).mem_nhds ⟨hstate, htime⟩)).comp
        (hs.prodMk continuousAt_const)
    change ContinuousAt
      (fun x ↦ completeBoundedFlow hX hbound
        (completeBoundedFlow hX hbound x s) (r - s)) x₀ at hcomp
    have heq : (fun x ↦ completeBoundedFlow hX hbound
        (completeBoundedFlow hX hbound x s) (r - s)) =
        (fun x ↦ completeBoundedFlow hX hbound x r) := by
      funext x
      rw [← completeBoundedFlow_add, sub_add_cancel]
    rwa [heq] at hcomp
  have hGopen : IsOpen G := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    obtain ⟨ε, hε, U, hU, hstate, hlocal⟩ :=
      exists_continuousOn_completeBoundedFlow_local hX hbound
        (completeBoundedFlow hX hbound x₀ s)
    apply mem_of_superset (Ioo_mem_nhds (by linarith : s - ε < s)
      (by linarith : s < s + ε))
    intro r hr
    exact transfer hU hlocal hs hstate ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hGclosed : IsClosed G := by
    apply isClosed_of_closure_subset
    intro r hr
    obtain ⟨ε, hε, U, hU, hstate, hlocal⟩ :=
      exists_continuousOn_completeBoundedFlow_local hX hbound
        (completeBoundedFlow hX hbound x₀ r)
    let J := (completeBoundedFlow hX hbound x₀) ⁻¹' U ∩ Ioo (r - ε) (r + ε)
    have hJopen : IsOpen J :=
      (hU.preimage (continuous_completeBoundedFlow_orbit hX hbound x₀)).inter isOpen_Ioo
    have hrJ : r ∈ J := ⟨hstate, by constructor <;> linarith⟩
    obtain ⟨s, hsJ, hsG⟩ := mem_closure_iff.mp hr J hJopen hrJ
    exact transfer hU hlocal hsG hsJ.1
      ⟨by linarith [hsJ.2.2], by linarith [hsJ.2.1]⟩
  have hzero : (0 : ℝ) ∈ G := by
    change ContinuousAt (fun x ↦ completeBoundedFlow hX hbound x 0) x₀
    simp only [completeBoundedFlow_zero]
    convert! (continuousAt_id : ContinuousAt (id : M → M) x₀) using 1
  have hGuniv : G = univ := (show IsClopen G from ⟨hGclosed, hGopen⟩).eq_univ ⟨0, hzero⟩
  exact (show t ∈ G from hGuniv ▸ mem_univ t)

/-- The actual complete bounded-field flow is jointly continuous in its
initial point and time, without a flow-dependence hypothesis. -/
theorem continuous_completeBoundedFlow :
    Continuous (fun p : M × ℝ ↦ completeBoundedFlow hX hbound p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨ε, hε, U, hU, hstate, hlocal⟩ :=
    exists_continuousOn_completeBoundedFlow_local hX hbound
      (completeBoundedFlow hX hbound p.1 p.2)
  have hc : ContinuousAt
      (fun q : M × ℝ ↦ (completeBoundedFlow hX hbound q.1 p.2, q.2 - p.2)) p :=
    ((continuous_completeBoundedFlow_timeSlice hX hbound p.2).continuousAt.comp
      continuousAt_fst).prodMk (continuousAt_snd.sub continuousAt_const)
  have hlocAt : ContinuousAt
      (fun q : M × ℝ ↦ completeBoundedFlow hX hbound q.1 q.2)
      (completeBoundedFlow hX hbound p.1 p.2, p.2 - p.2) :=
    hlocal.continuousAt ((hU.prod isOpen_Ioo).mem_nhds
      ⟨hstate, by simp only [sub_self]; constructor <;> linarith⟩)
  have hcomp := hlocAt.comp_of_eq hc rfl
  change ContinuousAt
    (fun q : M × ℝ ↦ completeBoundedFlow hX hbound
      (completeBoundedFlow hX hbound q.1 p.2) (q.2 - p.2)) p at hcomp
  have heq : (fun q : M × ℝ ↦ completeBoundedFlow hX hbound
      (completeBoundedFlow hX hbound q.1 p.2) (q.2 - p.2)) =
      (fun q : M × ℝ ↦ completeBoundedFlow hX hbound q.1 q.2) := by
    funext q
    rw [← completeBoundedFlow_add, sub_add_cancel]
  rwa [heq] at hcomp

/-- Actual time slices are homeomorphisms, with inverse the actual negative-time
slice of the same vector field. -/
noncomputable def completeBoundedFlowHomeomorph (t : ℝ) : M ≃ₜ M where
  toEquiv := completeBoundedFlowEquiv hX hbound t
  continuous_toFun := continuous_completeBoundedFlow_timeSlice hX hbound t
  continuous_invFun := continuous_completeBoundedFlow_timeSlice hX hbound (-t)

end CutoffRigidity
