/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section5b
public import LeanPool.GraphMinor.GM11.DrawingTopology
public import LeanPool.GraphMinor.GM11.ThreeCircuits
public import LeanPool.GraphMinor.Surface.Crossing

/-!
# The regions inside a circuit

For a circuit `C` of length `< 2θ`, let `A` be the set of regions of `Γ` included in `ins(C)`. The
proof of (5.4) in Graph Minors XI (pages 83–85) uses that `N(A) = C`, and that `ins(C) - U(C)` is a
region of `C` and so is connected. This file proves these facts.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface Metric Complex

universe u

variable {S : Type u} [TopologicalSpace S]

variable {Γ : Drawing S} {k : ℕ} {ins : Drawing S → Set S}

/-- The set `A` of regions of `Γ` included in `ins(C)`. -/
def insideRegions (Γ : Drawing S) (X : Set S) : Set (Set S) := {r | r ∈ Γ.R ∧ r ⊆ X}

/-- A vertex of a circuit lies on an edge of it. -/
theorem exists_edge_at_vertex {C : Drawing S} (hC : C.IsCircuit) {v : S} (hv : v ∈ C.V) :
    ∃ g ∈ C.E, v ∈ closure g := by
  obtain ⟨X, -, hpos, -, hE⟩ := exists_walk_at hC hv
  cases X with
  | nil _ => simp at hpos
  | @cons a y a' g hg t =>
    have hgC : g ∈ C.E := by rw [hE]; exact List.mem_cons_self
    have hm : v ∈ closure g ∩ C.V := by rw [hg.2.2.2]; simp
    exact ⟨g, hgC, hm.1⟩

/-- A circuit whose edges are edges of a subdrawing is a subdrawing of it. -/
theorem circuit_isSubdrawing_of_E {C N : Drawing S} (hC : C.IsCircuit)
    (hCs : C.IsSubdrawing Γ) (hNs : N.IsSubdrawing Γ) (hE : C.E ⊆ N.E) : C.IsSubdrawing N := by
  refine ⟨fun v hv => ?_, hE⟩
  obtain ⟨g, hg, hvg⟩ := exists_edge_at_vertex hC hv
  have hm : v ∈ closure g ∩ C.V := ⟨hvg, hv⟩
  rw [hCs.closure_inter_V hg, ← hNs.closure_inter_V (hE hg)] at hm
  exact hm.2

/-- An edge outside a subdrawing misses its point set. -/
theorem edge_disjoint_U {C : Drawing S} (hCs : C.IsSubdrawing Γ) {f : Set S}
    (hf : f ∈ Γ.E) (hfC : f ∉ C.E) : Disjoint f C.U := by
  refine disjoint_left.mpr fun y hy hyU => hfC ?_
  have hyV : y ∉ C.V := fun h => (hf.2.1 hy).2 (hCs.1 h)
  obtain ⟨g, hg, hyg⟩ := C.exists_edge_of_mem hyU hyV
  rw [Γ.edge_eq_of_mem hf (hCs.2 hg) hy hyg]
  exact hg

section Disc

variable [T2Space S] (hS : IsClosedSurface S) (hs : IsSlope Γ k ins) {C : Drawing S}
  (hC : C.IsCircuit) (hCs : C.IsSubdrawing Γ) (hl : C.length < k)
include hS hs hC hCs hl

/-- The interior `ins(C) - U(C)` is connected. -/
theorem isPreconnected_inner : IsPreconnected (ins C \ C.U) := by
  obtain ⟨-, hfr, -⟩ := ins_facts_of_length hs hC hCs hl
  have := IsClosedDisc.isPreconnected_diff_frontier hS (hs.isClosedDisc C hC hCs hl)
  rwa [hfr] at this

/-- If `ins(C) - U(C)` is not empty, it is a region of `C`. -/
theorem inner_mem_R {x : S} (hx : x ∈ ins C) (hxU : x ∉ C.U) :
    ins C \ C.U ∈ C.R := by
  have hs' := theorem_4_2_proof hs hCs
  obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem hxU
  have hsub : r ⊆ ins C :=
    (region_subset_or_disjoint hs' hC (Drawing.IsSubdrawing.refl C) hl hr).resolve_right
      fun h => disjoint_left.mp h hxr hx
  have heq : ins C \ C.U = r := by
    refine subset_antisymm ?_ fun y hy => ⟨hsub hy, fun hyU => region_subset hr hy hyU⟩
    exact subset_region hr (isPreconnected_inner hS hs hC hCs hl) disjoint_sdiff_left ⟨hx, hxU⟩ hxr
  rw [heq]
  exact hr

omit hS in
/-- A region with a point of the interior of `ins(C)` in its closure lies in `ins(C)`. -/
theorem region_subset_ins_of_closure {r : Set S} (hr : r ∈ Γ.R) {p : S} (hp : p ∈ closure r)
    (hpi : p ∈ ins C) (hpU : p ∉ C.U) : r ⊆ ins C := by
  obtain ⟨-, hfr, -⟩ := ins_facts_of_length hs hC hCs hl
  have hint : p ∈ interior (ins C) := by
    by_contra h
    apply hpU
    rw [← hfr]
    exact ⟨subset_closure hpi, h⟩
  obtain ⟨z, hz, hzr⟩ := mem_closure_iff.mp hp _ isOpen_interior hint
  exact (region_subset_or_disjoint hs hC hCs hl hr).resolve_right fun h =>
    disjoint_left.mp h hzr (interior_subset hz)

/-- `N(A) = C` for the set `A` of regions of `Γ` in `ins(C)` (Graph Minors XI, proof of (5.4), page
84: "`N(A) = C₁`"). -/
theorem boundaryDrawing_inside :
    boundaryDrawing Γ (insideRegions Γ (ins C)) = C := by
  obtain ⟨hcl, hfr, -⟩ := ins_facts_of_length hs hC hCs hl
  refine Drawing.ext_of_V_E ?_ ?_
  · ext v
    rw [mem_boundaryDrawing_V hS]
    constructor
    · rintro ⟨⟨a, ⟨ha, hai⟩, hva⟩, b, ⟨hb, hbn⟩, hvb⟩
      by_contra hvC
      have hvU : v ∉ C.U := by
        intro hvU
        obtain ⟨g, hg, hvg⟩ := C.exists_edge_of_mem hvU hvC
        exact ((hCs.2 hg).2.1 hvg).2 hva.1
      have hvi : v ∈ ins C := hcl.closure_subset_iff.mpr hai hva.2.2
      exact hbn ⟨hb, region_subset_ins_of_closure hs hC hCs hl hb hvb.2.2 hvi hvU⟩
    · intro hv
      obtain ⟨g, hg, hvg⟩ := exists_edge_at_vertex hC hv
      obtain ⟨⟨r, hr, h, hsub⟩, r', hr', h', hnot⟩ :=
        exists_regions_of_circuit_edge hS hs hC hCs hl hg
      exact ⟨⟨r, ⟨hr, hsub⟩, hCs.1 hv, Or.inr hr, closure_minimal h isClosed_closure hvg⟩, r',
        ⟨hr', fun h'' => hnot h''.2⟩, hCs.1 hv, Or.inr hr',
        closure_minimal h' isClosed_closure hvg⟩
  · ext e
    rw [mem_boundaryDrawing_E]
    constructor
    · rintro ⟨⟨a, ⟨ha, hai⟩, hia⟩, b, ⟨hb, hbn⟩, hib⟩
      by_contra heC
      obtain ⟨p, hpe, hpb⟩ := hib.2.2
      have hea := edge_subset_closure_of_incident hS hia.1 ha hia.2.2
      have hpi : p ∈ ins C := hcl.closure_subset_iff.mpr hai (hea hpe)
      have hpU : p ∉ C.U := disjoint_left.mp (edge_disjoint_U hCs hia.1 heC) hpe
      exact hbn ⟨hb, region_subset_ins_of_closure hs hC hCs hl hb hpb hpi hpU⟩
    · intro he
      obtain ⟨x, hx⟩ := he.1
      obtain ⟨⟨r, hr, h, hsub⟩, r', hr', h', hnot⟩ :=
        exists_regions_of_circuit_edge hS hs hC hCs hl he
      exact ⟨⟨r, ⟨hr, hsub⟩, hCs.2 he, hr, x, hx, h hx⟩, r', ⟨hr', fun h'' => hnot h''.2⟩, hCs.2 he,
        hr', x, hx, h' hx⟩

end Disc

end GraphMinor.GM11
