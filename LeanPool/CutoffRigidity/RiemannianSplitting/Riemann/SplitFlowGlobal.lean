/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitFlowManifold
public import LeanPool.CutoffRigidity.RiemannianSplitting.CompleteBoundedFlowJointC1

/-! # The complete flow of a smooth bounded field is `C^∞` jointly in point and time
-/

@[expose] public section
open Bundle Set Filter
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace CutoffRigidity.Riemann
open CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M] [CompleteSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {X : (x : M) → TangentSpace I x} (m : ℕ) (hX1 : ContMDiff I I.tangent 1 (T% X))
  (hXinf : ContMDiff I I.tangent ∞ (T% X))
  {C : ℝ≥0} (hbound : ∀ x, ‖X x‖ₑ ≤ C)
include hX1 hXinf

/-- The actual canonical global flow has C¹ time slices locally in both
initial position and time, as derived from coordinate Picard differentiation. -/
theorem exists_contMDiffOn_completeBoundedFlow_local_nat (x₀ : M) :
    ∃ ε > (0 : ℝ), ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧
      ∀ t ∈ Ioo (-ε) ε, ContMDiffOn I I ((m + 1 : ℕ) : WithTop ℕ∞)
        (fun x ↦ completeBoundedFlow hX1 hbound x t) U := by
  obtain ⟨ε, hε, U, hU, Φ, _, hΦ, hΦC1⟩ :=
    exists_contMDiff_localIntegralFlow_nat m ((hXinf.contMDiffAt (x := x₀)).of_le (by
        exact_mod_cast le_top))
  refine ⟨ε, hε, interior U, isOpen_interior, mem_interior_iff_mem_nhds.mpr hU, ?_⟩
  intro t ht
  have hslice : ContMDiffOn I I ((m + 1 : ℕ) : WithTop ℕ∞) (fun x : M => Φ (x, t)) U :=
    hΦC1.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
      (fun x hx => ⟨hx, ht⟩)
  apply (hslice.mono interior_subset).congr
  intro x hx
  have hxU : x ∈ U := interior_subset hx
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := 0) ⟨by linarith, hε⟩ hX1
    ((completeBoundedFlow_isMIntegralCurve hX1 hbound x).isMIntegralCurveOn _)
    (hΦ x hxU).2
    ((completeBoundedFlow_zero hX1 hbound x).trans (hΦ x hxU).1.symm)
  exact heq ht

/-- Every actual time slice is C¹ globally; no differentiability of the flow
is supplied as a premise. -/
theorem contMDiff_completeBoundedFlow_timeSlice_nat (t : ℝ) :
    ContMDiff I I ((m + 1 : ℕ) : WithTop ℕ∞) (fun x : M ↦ completeBoundedFlow hX1 hbound x t) := by
  intro x₀
  let G : Set ℝ := {s | ContMDiffAt I I ((m + 1 : ℕ) : WithTop ℕ∞) (fun x ↦ completeBoundedFlow
      hX1 hbound x s) x₀}
  have transfer {ε : ℝ} {U : Set M} (hU : IsOpen U)
      (hlocal : ∀ q ∈ Ioo (-ε) ε, ContMDiffOn I I ((m + 1 : ℕ) : WithTop ℕ∞)
        (fun x ↦ completeBoundedFlow hX1 hbound x q) U) {s r : ℝ} (hs : s ∈ G)
      (hstate : completeBoundedFlow hX1 hbound x₀ s ∈ U)
      (htime : r - s ∈ Ioo (-ε) ε) : r ∈ G := by
    change ContMDiffAt I I ((m + 1 : ℕ) : WithTop ℕ∞) (fun x ↦ completeBoundedFlow hX1 hbound x s)
        x₀ at hs
    have hlocAt := (hlocal (r - s) htime).contMDiffAt (hU.mem_nhds hstate)
    have hcomp := hlocAt.comp x₀ hs
    have heq : ((fun x ↦ completeBoundedFlow hX1 hbound x (r - s)) ∘
        (fun x ↦ completeBoundedFlow hX1 hbound x s)) =
        (fun x ↦ completeBoundedFlow hX1 hbound x r) := by
      funext x
      simp only [Function.comp_apply]
      rw [← completeBoundedFlow_add, sub_add_cancel]
    rwa [heq] at hcomp
  have hGopen : IsOpen G := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    obtain ⟨ε, hε, U, hU, hstate, hlocal⟩ :=
      exists_contMDiffOn_completeBoundedFlow_local_nat m hX1 hXinf hbound
        (completeBoundedFlow hX1 hbound x₀ s)
    apply mem_of_superset (Ioo_mem_nhds (by linarith : s - ε < s)
      (by linarith : s < s + ε))
    intro r hr
    exact transfer hU hlocal hs hstate ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hGclosed : IsClosed G := by
    apply isClosed_of_closure_subset
    intro r hr
    obtain ⟨ε, hε, U, hU, hstate, hlocal⟩ :=
      exists_contMDiffOn_completeBoundedFlow_local_nat m hX1 hXinf hbound
        (completeBoundedFlow hX1 hbound x₀ r)
    let J := (completeBoundedFlow hX1 hbound x₀) ⁻¹' U ∩ Ioo (r - ε) (r + ε)
    have hJopen : IsOpen J :=
      (hU.preimage (continuous_completeBoundedFlow_orbit hX1 hbound x₀)).inter isOpen_Ioo
    have hrJ : r ∈ J := ⟨hstate, by constructor <;> linarith⟩
    obtain ⟨s, hsJ, hsG⟩ := mem_closure_iff.mp hr J hJopen hrJ
    exact transfer hU hlocal hsG hsJ.1
      ⟨by linarith [hsJ.2.2], by linarith [hsJ.2.1]⟩
  have hzero : (0 : ℝ) ∈ G := by
    change ContMDiffAt I I ((m + 1 : ℕ) : WithTop ℕ∞) (fun x ↦ completeBoundedFlow hX1 hbound x 0)
        x₀
    simp only [completeBoundedFlow_zero]
    convert! (contMDiffAt_id (I := I) (x := x₀)) using 1
  have hGuniv : G = univ := (show IsClopen G from ⟨hGclosed, hGopen⟩).eq_univ ⟨0, hzero⟩
  exact (show t ∈ G from hGuniv ▸ mem_univ t)

/-- Actual joint manifold differentiability at time zero, without a supplied
flow differentiability premise. -/
theorem contMDiffAt_completeBoundedFlow_joint_zero_nat (x₀ : M) :
    ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I ((m + 1 : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ ↦ completeBoundedFlow hX1 hbound p.1 p.2) (x₀, 0) := by
  obtain ⟨ε, hε, U, hU, Φ, _, hΦ, hΦC1⟩ :=
    exists_contMDiff_localIntegralFlow_nat m ((hXinf.contMDiffAt (x := x₀)).of_le (by
        exact_mod_cast le_top))
  have hdomain : U ×ˢ Ioo (-ε) ε ∈ 𝓝 (x₀, 0) :=
    prod_mem_nhds hU (Ioo_mem_nhds (by linarith) hε)
  have hloc := hΦC1.contMDiffAt hdomain
  apply hloc.congr_of_eventuallyEq
  filter_upwards [hdomain] with p hp
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := 0) ⟨by linarith, hε⟩ hX1
    ((completeBoundedFlow_isMIntegralCurve hX1 hbound p.1).isMIntegralCurveOn _)
    (hΦ p.1 hp.1).2
    ((completeBoundedFlow_zero hX1 hbound p.1).trans (hΦ p.1 hp.1).1.symm)
  exact heq hp.2

/-- The actual complete flow is jointly `C¹` in the initial point and time. -/
theorem contMDiff_completeBoundedFlow_joint_nat :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) I ((m + 1 : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ ↦ completeBoundedFlow hX1 hbound p.1 p.2) := by
  intro p
  let q : M × ℝ → M × ℝ := fun z ↦ (z.1, z.2 - p.2)
  have hq : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ((m + 1 : ℕ) : WithTop ℕ∞) q p :=
    contMDiffAt_fst.prodMk (contMDiffAt_snd.sub contMDiffAt_const)
  have hq0 : q p = (p.1, 0) := by simp [q]
  have hinner := (contMDiffAt_completeBoundedFlow_joint_zero_nat m hX1 hXinf hbound
      p.1).comp_of_eq hq hq0
  have hout := (contMDiff_completeBoundedFlow_timeSlice_nat m hX1 hXinf hbound
      p.2).contMDiffAt.comp p hinner
  have heq : (fun x ↦ completeBoundedFlow hX1 hbound x p.2) ∘
      ((fun z : M × ℝ ↦ completeBoundedFlow hX1 hbound z.1 z.2) ∘ q) =
      (fun z : M × ℝ ↦ completeBoundedFlow hX1 hbound z.1 z.2) := by
    funext z
    change completeBoundedFlow hX1 hbound (completeBoundedFlow hX1 hbound z.1 (z.2 - p.2)) p.2 = _
    rw [← completeBoundedFlow_add]
    congr 1
    ring
  rwa [heq] at hout


/-- The complete flow of a smooth bounded field is jointly `C^∞` in the initial point and time. -/
theorem contMDiff_completeBoundedFlow_joint_infty :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) I ∞
      (fun p : M × ℝ ↦ completeBoundedFlow hX1 hbound p.1 p.2) := by
  rw [contMDiff_infty]
  intro n
  cases n with
  | zero => exact (contMDiff_completeBoundedFlow_joint hX1 hbound).of_le (by simp)
  | succ n => exact contMDiff_completeBoundedFlow_joint_nat n hX1 hXinf hbound

end CutoffRigidity.Riemann
