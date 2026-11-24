/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4SplitBranchConnected
import LeanPool.GraphMinor.GM12.Section4SplitDrawing

/-!
# The original graph is a minor of its subdivision

For the target replacement in XII (4.3), page 249, contract
the right half of every subdivided edge. The branch at an original
vertex contains its assigned midpoints. The left halves represent
the original edges. Distinct branches and distinct representing
edges stay distinct. An original loop has both ends of its left
half in one branch, exactly as required by the minor model.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- Contracting every right half recovers the original graph.
This verifies the minor requirement in XII (4.3)'s target replacement,
page 249, for subdivisions of arbitrary drawings, including loops. -/
theorem isMinorModel_of_splitData
    {S : Type*} [TopologicalSpace S] {Γ H : Drawing S}
    {A B : Set S → Set S} {m x y : Set S → S}
    (hd : SplitData Γ H A B m x y) :
    IsMinorModel Γ.toGraph H.toGraph (splitBranch Γ m y) A := by
  have hlink : ∀ e ∈ Γ.E, Γ.toGraph.IsLink e (x e) (y e) :=
    fun e he => ⟨he, hd.x_mem e he, hd.y_mem e he, hd.cap e he⟩
  refine {
    vertex_nonempty := fun v _ => ⟨v, Or.inl rfl⟩
    vertex_subset := fun _ hv => splitBranch_subset_vertices hd hv
    edge_mem := fun e he => hd.A_mem e he
    vertex_disjoint := fun _ hv _ hw hne => splitBranch_disjoint hd hv hw hne
    edge_injOn := ?_
    inc_iff := ?_
    isLoopAt_iff := ?_
    connected := fun _ hv => splitBranch_connected_subgraph hd hv }
  · intro e he f hf hef
    exact hd.edge_of_piece he hf (Or.inl hef)
  · intro v hv e he
    have hA := splitData_isLink_left hd he
    constructor
    · intro hev
      rcases hev.eq_or_eq_of_isLink (hlink e he) with hve | hve
      · exact ⟨v, Or.inl rfl, hve ▸ hA.inc_left⟩
      · exact ⟨m e, (mem_splitBranch_of_midpoint_iff hd hv he).mpr hve.symm, hA.inc_right⟩
    · rintro ⟨z, hz, hAz⟩
      rcases hAz.eq_or_eq_of_isLink hA with hzx | hzm
      · have hxB : x e ∈ splitBranch Γ m y v := hzx ▸ hz
        have hxv := (mem_splitBranch_of_original_vertex_iff hd (hd.x_mem e he)).mp hxB
        exact hxv ▸ (hlink e he).inc_left
      · have hmB : m e ∈ splitBranch Γ m y v := hzm ▸ hz
        have hyv := (mem_splitBranch_of_midpoint_iff hd hv he).mp hmB
        exact hyv ▸ (hlink e he).inc_right
  · intro v hv e he
    have hA := splitData_isLink_left hd he
    constructor
    · intro hloop z hAz
      have hxv : x e = v :=
        (Γ.toGraph.eq_or_eq_of_isLink_of_isLink (hlink e he) hloop).elim id id
      have hyv : y e = v :=
        (Γ.toGraph.eq_or_eq_of_isLink_of_isLink (hlink e he).symm hloop).elim id id
      rcases hAz.eq_or_eq_of_isLink hA with hzx | hzm
      · exact (hzx.trans hxv) ▸ (Or.inl rfl : v ∈ splitBranch Γ m y v)
      · exact hzm ▸ (mem_splitBranch_of_midpoint_iff hd hv he).mpr hyv
    · intro hall
      have hxv := (mem_splitBranch_of_original_vertex_iff hd (hd.x_mem e he)).mp
        (hall (x e) hA.inc_left)
      have hyv := (mem_splitBranch_of_midpoint_iff hd hv he).mp (hall (m e) hA.inc_right)
      change Γ.toGraph.IsLink e v v
      simpa only [hxv, hyv] using hlink e he

end GraphMinor.GM12
