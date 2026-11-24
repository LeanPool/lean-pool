/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM11.EdgeSides
import LeanPool.GraphMinor.GM11.Walks

/-!
# Small disjoint discs at target vertices

XII (4.3), claim (7), page 251, starts with small closed discs
at the vertices of a target drawing. Separate the finite vertex
set by disjoint open neighbourhoods. At each vertex also avoid
the closures of all nonincident edges. A smaller closed disc in
that neighbourhood has the required properties.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The small vertex discs used to form the residual edge arcs in
XII (4.3), claim (7), page 251. -/
theorem exists_vertex_disc_family
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (Γ : Drawing S) :
    ∃ D : Γ.V → Set S,
      (∀ v, IsClosedDisc (D v) ∧ v.val ∈ interior (D v) ∧ D v ∩ Γ.V = {v.val} ∧
        ∀ e ∈ Γ.E, ¬ Γ.toGraph.Inc e v.val → Disjoint (D v) (closure e)) ∧
      (∀ v w, v ≠ w → Disjoint (D v) (D w)) := by
  classical
  obtain ⟨U, hU, hUdisj⟩ := Γ.finite_V.t2_separation
  have hex : ∀ v : Γ.V, ∃ D : Set S, IsClosedDisc D ∧ v.val ∈ interior D ∧ D ⊆ U v.val ∧
      ∀ e ∈ Γ.E, ¬ Γ.toGraph.Inc e v.val → Disjoint D (closure e) := by
    intro v
    let F : Set (Set S) := {e ∈ Γ.E | ¬ Γ.toGraph.Inc e v.val}
    let Z : Set S := ⋃ e ∈ F, closure e
    have hF : F.Finite := Γ.finite_edges.subset (fun _ h => h.1)
    have hZ : IsClosed Z := hF.isClosed_biUnion fun _ _ => isClosed_closure
    have hvZ : v.val ∉ Z := by
      intro hvZ
      obtain ⟨e, ⟨he, hnot⟩, hve⟩ := mem_iUnion₂.mp hvZ
      obtain ⟨x, y, hl⟩ := Γ.toGraph.exists_isLink_of_mem_edgeSet he
      have hends : v.val ∈ ({x, y} : Set S) := hl.2.2.2 ▸ ⟨hve, v.property⟩
      rcases hends with hx | hy
      · exact hnot (hx ▸ hl.inc_left)
      · exact hnot ((Set.mem_singleton_iff.mp hy) ▸ hl.inc_right)
    have hO : IsOpen (U v.val ∩ Zᶜ) := (hU v.val).2.inter hZ.isOpen_compl
    obtain ⟨D, D', hD, hD'o, hvD', hD'D, hDO, _⟩ :=
      exists_closedDisc_nbhd hS hO ⟨(hU v.val).1, hvZ⟩
    refine ⟨D, hD, interior_maximal hD'D hD'o hvD', hDO.trans inter_subset_left, ?_⟩
    intro e he hnot
    apply Set.disjoint_left.mpr
    intro x hxD hxe
    exact (hDO hxD).2 (mem_iUnion₂.mpr ⟨e, ⟨he, hnot⟩, hxe⟩)
  choose D hD hvD hDU hDoff using hex
  refine ⟨D, ?_, ?_⟩
  · intro v
    refine ⟨hD v, hvD v, ?_, hDoff v⟩
    apply Set.Subset.antisymm
    · rintro x ⟨hxD, hxV⟩
      by_contra hxv
      have hvx : v.val ≠ x := Ne.symm hxv
      exact Set.disjoint_left.mp (hUdisj v.property hxV hvx) (hDU v hxD) (hU x).1
    · intro x hx
      have hxv := Set.mem_singleton_iff.mp hx
      exact hxv ▸ ⟨interior_subset (hvD v), v.property⟩
  · intro v w hvw
    have hvw' : v.val ≠ w.val := fun h => hvw (Subtype.ext h)
    exact (hUdisj v.property w.property hvw').mono (hDU v) (hDU w)

end GraphMinor.GM12
