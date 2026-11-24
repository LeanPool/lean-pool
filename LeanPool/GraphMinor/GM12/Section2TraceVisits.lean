/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2TraceParameters
import LeanPool.GraphMinor.GM11.Regions

/-!
# Every visited vertex and region occurs in the trace

For the restriction step in XII (2.1), pages 243--244, a trace records
every vertex visit and every intervening region. On each two-edge
step, the open parameter interval misses drawing vertices and the
middle walk vertex is the hub of that interval's region. Induction
through the steps therefore records all vertex and region visits
of the original curve.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- Every drawing vertex visited during trace steps is a vertex of
the trace walk. -/
theorem traceSteps_vertex_visit
    {S : Type*} [TopologicalSpace S] {Γ K : Drawing S} {f : ℝ → S}
    {a b : ℝ} {u v : S} (W : GraphWalk K.toGraph u v)
    (hW : TraceSteps Γ K f a b W) {s : ℝ} (hs : s ∈ Icc a b) (hfs : f s ∈ Γ.V) :
    f s ∈ W.support := by
  cases hWcase : W with
  | nil hv =>
    rw [hWcase] at hW
    obtain ⟨hab, hfa, _⟩ := hW
    have hsa : s = a := le_antisymm (hs.2.trans_eq hab.symm) hs.1
    have heq : f s = u := (congrArg f hsa).trans hfa
    rw [heq]
    exact GraphWalk.start_mem_support _
  | cons hlink rest =>
    rw [hWcase] at hW
    cases hrestcase : rest with
    | nil hv => rw [hrestcase] at hW; exact hW.elim
    | cons hlink' tail =>
      rw [hrestcase] at hW
      obtain ⟨c, hac, hfa, _, _, _, r, hr, _, hfr, _, _, htail⟩ := hW
      by_cases hsa : s = a
      · have heq : f s = u := (congrArg f hsa).trans hfa
        rw [heq]
        exact GraphWalk.start_mem_support _
      · by_cases hsc : s < c
        · have has : a < s := lt_of_le_of_ne hs.1 (Ne.symm hsa)
          exact (region_subset hr (hfr s ⟨has, hsc⟩) (Γ.V_subset_U hfs)).elim
        · have hm := traceSteps_vertex_visit tail htail ⟨le_of_not_gt hsc, hs.2⟩ hfs
          simp only [GraphWalk.support, List.mem_cons]
          exact Or.inr (Or.inr hm)
termination_by W.length
decreasing_by
  simp_all only [GraphWalk.length, GraphWalk.edges, List.length_cons]
  omega

/-- Every region visited during trace steps contains a walk vertex,
namely the hub of one of the visited parameter intervals. -/
theorem traceSteps_region_visit
    {S : Type*} [TopologicalSpace S] {Γ K : Drawing S} {f : ℝ → S}
    {a b : ℝ} {u v : S} (W : GraphWalk K.toGraph u v)
    (hW : TraceSteps Γ K f a b W) {s : ℝ} (hs : s ∈ Icc a b)
    {r : Set S} (hr : r ∈ Γ.R) (hfs : f s ∈ r) :
    ∃ w ∈ W.support, w ∈ r := by
  cases hWcase : W with
  | nil hv =>
    rw [hWcase] at hW
    obtain ⟨hab, hfa, hu⟩ := hW
    have hsa : s = a := le_antisymm (hs.2.trans_eq hab.symm) hs.1
    have heq : f s = u := (congrArg f hsa).trans hfa
    exact (region_subset hr hfs (heq.symm ▸ Γ.V_subset_U hu)).elim
  | @cons _ w _ e hlink rest =>
    rw [hWcase] at hW
    cases hrestcase : rest with
    | nil hv => rw [hrestcase] at hW; exact hW.elim
    | cons hlink' tail =>
      rw [hrestcase] at hW
      obtain ⟨c, hac, hfa, hu, _, _, r', hr', hwr', hfr', _, _, htail⟩ := hW
      by_cases hsc : s < c
      · have has : a < s := lt_of_le_of_ne hs.1 (by
          intro heq
          have hfaU : f s ∈ Γ.U := by rw [← heq, hfa]; exact Γ.V_subset_U hu
          exact region_subset hr hfs hfaU)
        have hrr : r' = r := region_eq_of_mem hr' hr (hfr' s ⟨has, hsc⟩) hfs
        refine ⟨w, ?_, hrr ▸ hwr'⟩
        simp only [GraphWalk.support, List.mem_cons]
        exact Or.inr (Or.inl trivial)
      · obtain ⟨z, hz, hzr⟩ := traceSteps_region_visit tail htail ⟨le_of_not_gt hsc, hs.2⟩ hr hfs
        refine ⟨z, ?_, hzr⟩
        simp only [GraphWalk.support, List.mem_cons]
        exact Or.inr (Or.inr hz)
termination_by W.length
decreasing_by
  simp_all only [GraphWalk.length, GraphWalk.edges, List.length_cons]
  omega

end GraphMinor.GM12
