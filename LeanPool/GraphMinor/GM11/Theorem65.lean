/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.PaintingPerimeter
public import LeanPool.GraphMinor.GM11.Theorem63

/-!
# Theorem (6.5) of Graph Minors XI

Graph Minors XI, (6.5), pages 91–92. `theorem_6_5_painting` is the paper's statement for a painting.
`theorem_6_5` is the paper's statement for a drawing, with one correction. The converse, that an
even slope comes from a tangle, needs `θ ≠ 2` or that `Γ` has no loop (see the correction to (6.5)
in `corrections/GM11.md`). For one vertex and one loop in the sphere, at `θ = 2`, the empty slope is
even and `Γ` has no tangle of order 2.

Both follow from `tangle_iff_even`, the paper's proof. It uses two bounds on the perimeter of a
region of `Γ'`, which
are proved separately for drawings and for paintings. The first is that the perimeter of `r` has
length at least twice
the number of ends of the edge in `r`. The second is the fact that the converse needs: an edge with
fewer than `θ` ends
lies in a region with perimeter of length less than `2θ`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] {Γ' : Drawing S} {θ : ℕ}
  {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}

/-- **The proof of (6.5)** (pages 91–92), from the two bounds on perimeters. -/
theorem tangle_iff_even {Γ : PaintingOrDrawing S} (hS : IsClosedSurface S) (hE : Γ.E.Nonempty)
    (hT : IsPretangle Γ.toHypergraph θ T) (hresp : Γ.IsRespectful θ T) (hrad : Γ.IsRadialDrawing Γ')
    (hd : IsDerivedSlope Γ Γ' θ T ins) (hF : RegionFacts Γ Γ')
    (hlow : ∀ s ∈ Γ'.R, 2 * (Γ.V ∩ closure s).ncard ≤ perimeterLength Γ' s) :
    (GM10.IsTangle Γ.toHypergraph θ T → IsEvenSlope Γ' (2 * θ) ins) ∧
      ((∀ s ∈ Γ'.R, ∀ e ∈ Γ.E, e ⊆ s → GM10.edgeSize Γ.toHypergraph e < θ
        → perimeterLength Γ' s < 2 * θ) →
        IsEvenSlope Γ' (2 * θ) ins → GM10.IsTangle Γ.toHypergraph θ T) := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨hex, -, -⟩ := hF
  have ht := theorem_6_3_proof S hS inferInstance Γ Γ' θ T ins hrad.1 hE hT hresp hrad hd
  constructor
  · intro hTt s hs hlen
    obtain ⟨e, he, hes⟩ := hex s hs
    have heE : e ∈ Γ.toHypergraph.edgeSet := Γ.toHypergraph_edgeSet ▸ he
    have hsize : GM10.edgeSize Γ.toHypergraph e < θ := by
      have h₁ := hlow s hs
      have hsub : Γ.toHypergraph.ends e ⊆ Γ.V ∩ closure s := fun v hv => by
        obtain ⟨-, hv₁, hv₂⟩ := PaintingOrDrawing.toHypergraph_inc.mp hv
        exact ⟨hv₁, closure_mono hes hv₂⟩
      have hfin : Γ.V.Finite := Γ.toHypergraph_vertexSet ▸ Γ.toHypergraph.vertexSet_finite
      have h₂ := ncard_le_ncard hsub (hfin.subset inter_subset_left)
      have : GM10.edgeSize Γ.toHypergraph e = (Γ.toHypergraph.ends e).ncard := rfl
      omega
    have hm := (GM10.theorem_2_7_proof hT.one_le hT.isSeparation hT.order_lt hT.axiom1
      hT.axiom2).mp hTt e heE hsize
    have hsep := GM10.isSeparation_edgeHypergraph_deleteEdges (G := Γ.toHypergraph) heE
    have hord : separationOrder (GM10.edgeHypergraph Γ.toHypergraph e)
      (Γ.toHypergraph.deleteEdges {e}) < θ := by
      rwa [GM10.separationOrder_edgeHypergraph_deleteEdges]
    obtain ⟨k, C, hC, hcov⟩ := (ht.1 _ _ hsep hord).mp hm
    obtain ⟨i, hi⟩ := hcov e rfl
    obtain ⟨hcir, hsub, hl, -⟩ := hC i
    refine ⟨C i, hcir, hsub, hl, ?_⟩
    obtain ⟨d, b, -⟩ := hd (C i) hcir hsub hl
    have hfr : frontier (ins (C i)) ⊆ Γ'.U := by
      rw [← subBd_eq_frontier, b]
      exact hsub.U_subset
    have hc := (IsClosedDisc.isCompact d).isClosed
    obtain ⟨y, hy⟩ := (Γ.edge_props he).2.2.2
    have hsu : s ⊆ interior (ins (C i)) ∪ (ins (C i))ᶜ := fun x hx => by
      by_cases hxi : x ∈ ins (C i)
      · refine Or.inl ?_
        by_contra hn
        exact region_subset hs hx (hfr ⟨subset_closure hxi, hn⟩)
      · exact Or.inr hxi
    have hyi : y ∈ interior (ins (C i)) := (hsu (hes hy)).resolve_right fun h => h (hi hy)
    have := (region_isPreconnected hs).subset_left_of_subset_union isOpen_interior hc.isOpen_compl
      (disjoint_left.mpr fun x h₁ h₂ => h₂ (interior_subset h₁)) hsu ⟨y, hes hy, hyi⟩
    exact this.trans interior_subset
  · intro hup hev
    by_contra hnt
    have hne := mt (GM10.theorem_2_7_proof hT.one_le hT.isSeparation hT.order_lt hT.axiom1
      hT.axiom2).mpr hnt
    push Not at hne
    obtain ⟨e, he, hsize, hnm⟩ := hne
    have heE' : e ∈ Γ.E := Γ.toHypergraph_edgeSet ▸ he
    have heE : e ∈ Γ.toHypergraph.edgeSet := he
    have hsep := GM10.isSeparation_edgeHypergraph_deleteEdges (G := Γ.toHypergraph) heE
    have hord : separationOrder (GM10.edgeHypergraph Γ.toHypergraph e)
      (Γ.toHypergraph.deleteEdges {e}) < θ := by
      rwa [GM10.separationOrder_edgeHypergraph_deleteEdges]
    have hm := (hT.axiom1 hsep hord).resolve_left hnm
    obtain ⟨hpc, hdis, hU, y, hy⟩ := Γ.edge_props heE'
    have hoff : Disjoint e Γ'.U := disjoint_left.mpr fun x hx hxU => by
      have : x ∈ Γ.V := hrad.2.1.1.subset ⟨hU hx, hxU⟩
      exact disjoint_left.mp hdis hx this
    have hyU : y ∉ Γ'.U := disjoint_left.mp hoff hy
    obtain ⟨s, hs, hys⟩ := exists_region_of_notMem hyU
    have hes : e ⊆ s := subset_region hs hpc hoff hy hys
    have hlen : perimeterLength Γ' s < 2 * θ := hup s hs e heE' hes hsize
    obtain ⟨C, hC, hCs, hl, hsub⟩ := hev s hs hlen
    obtain ⟨d, -, hm'⟩ := hd C hC hCs hl
    have heΔ : closure e ⊆ ins C := closure_minimal (hes.trans hsub) (IsClosedDisc.isCompact
      d).isClosed
    refine hT.axiom2 hm hm' hm ?_
    apply Hypergraph.ext
    · ext x
      constructor
      · rintro ((h | h) | h)
        · exact h
        · exact Γ.toHypergraph_vertexSet ▸ h.1
        · exact h
      · exact fun h => Or.inl (Or.inl h)
    · ext f
      constructor
      · rintro ((h | h) | h)
        · exact h.1
        · exact Γ.toHypergraph_edgeSet ▸ h.1
        · exact h.1
      · intro hf
        by_cases hfe : f = e
        · exact Or.inl (Or.inr ⟨Γ.toHypergraph_edgeSet ▸ hf, hfe ▸ subset_closure.trans heΔ⟩)
        · exact Or.inr ⟨hf, hfe⟩
    · funext f v
      apply propext
      change ((Γ.toHypergraph.Inc f v ∧ f ∉ ({e} : Set (Set S))) ∨
        (Γ.toHypergraph.Inc f v ∧ f ⊆ ins C ∧ v ∈ ins C)) ∨ (Γ.toHypergraph.Inc f v ∧ f ∉
          ({e} : Set (Set S))) ↔
          Γ.toHypergraph.Inc f v
      constructor
      · rintro ((h | h) | h)
        · exact h.1
        · exact h.1
        · exact h.1
      · intro h
        by_cases hfe : f = e
        · subst hfe
          exact Or.inl (Or.inr ⟨h, subset_closure.trans heΔ, heΔ
            (PaintingOrDrawing.toHypergraph_inc.mp h).2.2⟩)
        · exact Or.inr ⟨h, hfe⟩

/-- **Graph Minors XI, (6.5)** (pages 91–92), for a drawing, with the correction for loops at
`θ = 2`. -/
theorem theorem_6_5_proof {Γ : Drawing S} (hS : IsClosedSurface S) (hE : Γ.E.Nonempty)
  (hT : IsPretangle Γ.toHypergraph θ T)
    (hresp : (PaintingOrDrawing.drawing Γ).IsRespectful θ T) (hrad : (PaintingOrDrawing.drawing
      Γ).IsRadialDrawing Γ')
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing Γ) Γ' θ T ins) :
    (GM10.IsTangle Γ.toHypergraph θ T → IsEvenSlope Γ' (2 * θ) ins) ∧
      ((θ ≠ 2 ∨ ∀ e ∈ Γ.E, ∃ x y, x ≠ y ∧ closure e ∩ Γ.V = {x, y}) → IsEvenSlope Γ' (2 * θ) ins →
        GM10.IsTangle Γ.toHypergraph θ T) := by
  have hpre : PreRad (PaintingOrDrawing.drawing Γ) Γ' := ⟨hrad.1, hrad.2.1⟩
  have hmax : RadMax (PaintingOrDrawing.drawing Γ) Γ' := hrad.2.2
  have hF := regionFacts_of_radial hpre hS hmax hE
  have hlow : ∀ s ∈ Γ'.R, 2 * (Γ.V ∩ closure s).ncard ≤ perimeterLength Γ' s := fun s hs =>
    two_mul_ends_le hpre hS hmax hE hs
  have hupE : ∀ (hloop : θ ≠ 2 ∨ ∀ e ∈ Γ.E, ∃ x y, x ≠ y ∧ closure e ∩ Γ.V = {x, y}) (s)
    (hs : s ∈ Γ'.R), ∀ e ∈ Γ.E,
      e ⊆ s → GM10.edgeSize Γ.toHypergraph e < θ → perimeterLength Γ' s < 2 * θ := by
    intro hloop s hs e heE hes hsize
    have hends : (Γ.toHypergraph.ends e) = closure e ∩ Γ.V := by
      ext v
      exact ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨heE, h.2, h.1⟩⟩
    have hsz : GM10.edgeSize Γ.toHypergraph e = (closure e ∩ Γ.V).ncard := by
      rw [GM10.edgeSize, hends]
    have hθ : 3 ≤ θ := by
      have hpos : 0 < (closure e ∩ Γ.V).ncard := by
        refine (ncard_pos (Γ.finite_V.subset inter_subset_right)).mpr ?_
        rcases Γ.edge_cond e heE with ⟨u, v, -, hc, -⟩ | ⟨u, hc, -⟩ <;> rw [hc] <;> simp
      by_contra h3
      have h2 : θ = 2 := by omega
      rcases hloop with hne | hl
      · exact hne h2
      · obtain ⟨x, y, hxy, hc⟩ := hl e heE
        rw [hc, ncard_pair hxy] at hsz
        omega
    exact (perimeterLength_le_four hpre hS hmax hE hs).trans_lt (by omega)
  have hmain := tangle_iff_even (Γ := PaintingOrDrawing.drawing Γ) hS hE hT hresp hrad hd hF hlow
  exact ⟨hmain.1, fun hloop => hmain.2 (hupE hloop)⟩

/-- **Graph Minors XI, (6.5)** (pages 91–92), for a painting. Here the perimeter of `r` has length
at most twice the
number of ends of the cell in `r`, so the converse needs no correction. -/
theorem theorem_6_5_painting {Γ : Painting S} (hS : IsClosedSurface S) (hE : Γ.E.Nonempty)
    (hT : IsPretangle (PaintingOrDrawing.painting Γ).toHypergraph θ T)
    (hresp : (PaintingOrDrawing.painting Γ).IsRespectful θ T)
    (hrad : (PaintingOrDrawing.painting Γ).IsRadialDrawing Γ')
    (hd : IsDerivedSlope (PaintingOrDrawing.painting Γ) Γ' θ T ins) :
    GM10.IsTangle (PaintingOrDrawing.painting Γ).toHypergraph θ T ↔ IsEvenSlope Γ' (2 * θ) ins := by
  classical
  have hpre : PreRad (PaintingOrDrawing.painting Γ) Γ' := ⟨hrad.1, hrad.2.1⟩
  have hF := regionFacts_of_painting hpre hrad.2.2 hS hE
  by_cases hfree : ∃ e ∈ Γ.E, closure e ∩ Γ.V = ∅
  · -- With a cell with no end, `Γ` has no vertex, so `Γ'` has no edge.
    obtain ⟨e₀, he₀, hf₀⟩ := hfree
    obtain ⟨hV, -⟩ := free_cell hS hrad.1.2 he₀ hf₀
    have hE' : Γ'.E = ∅ := eq_empty_of_forall_notMem fun h hh => by
      obtain ⟨v, hv, -⟩ := hrad.2.1.2.2.2.2.1 h hh
      change v ∈ Γ.V at hv
      rw [hV] at hv
      exact hv
    have hzero : ∀ s, perimeterLength Γ' s = 0 := fun s => by
      have hP : (perimeter Γ' s).E = ∅ := eq_empty_of_forall_notMem fun h hh => by
        have := (mem_interSet_E_iff.mp hh).1
        rw [hE'] at this
        exact this
      rw [perimeterLength, hP, finsum_mem_empty]
    have hmain := tangle_iff_even (Γ := PaintingOrDrawing.painting Γ) hS hE hT hresp hrad hd hF
      (fun s _ => by
      rw [hzero s, show (PaintingOrDrawing.painting Γ).V = Γ.V from rfl, hV]
      simp)
    exact ⟨hmain.1, hmain.2 fun s _ e _ _ hsize => by
      rw [hzero s]
      omega⟩
  · have hv : ∀ e ∈ Γ.E, (closure e ∩ Γ.V).Nonempty := fun e he => by
      by_contra h
      exact hfree ⟨e, he, not_nonempty_iff_eq_empty.mp h⟩
    have hmain := tangle_iff_even (Γ := PaintingOrDrawing.painting Γ) hS hE hT hresp hrad hd hF
      (fun s hs => two_mul_ends_le_painting hS hrad hE hv hs)
    refine ⟨hmain.1, hmain.2 fun s hs e he hes hsize => ?_⟩
    have hends : (PaintingOrDrawing.painting Γ).toHypergraph.ends e = Γ.V ∩ closure e := by
      ext v
      constructor
      · intro h
        obtain ⟨-, h₁, h₂⟩ := (PaintingOrDrawing.toHypergraph_inc (Γ := PaintingOrDrawing.painting
          Γ)).mp h
        exact ⟨h₁, h₂⟩
      · exact fun h => (PaintingOrDrawing.toHypergraph_inc (Γ := PaintingOrDrawing.painting Γ)).mpr
          ⟨he, h⟩
    have hsz : GM10.edgeSize (PaintingOrDrawing.painting Γ).toHypergraph e =
      (Γ.V ∩ closure e).ncard := by
      rw [GM10.edgeSize, hends]
    have := perimeterLength_le_painting hS hrad hE hv hs he hes
    omega

end GraphMinor.GM11
