/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72ParallelInside
public import LeanPool.GraphMinor.GM12.Section72DiscGluing
import LeanPool.GraphMinor.GM11.Section810

/-!
# Replacing the deleted parallel spoke

For maximality in XII (7.2), page 260, move a new spoke outside the
removed disc and use old maximality to find a parallel old spoke.
Every other old boundary spoke misses the disc between them. Its
open interior therefore misses the removed disc. The old parallel
spoke is retained unless it is the deleted one. In that case glue
the two discs along the deleted spoke to obtain a disc between the
new spoke and the retained boundary spoke.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The old parallel spoke is retained, or gluing along the deleted
spoke gives a new empty bigon with the retained boundary spoke.
This is the parallel-spoke comparison for XII (7.2), page 260. -/
theorem parallel_spoke_retained_or_replaced
    {S : Type*} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    {Γ K C : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    (hC : C.IsSubdrawing K) {D Q r e f g L : Set S} {v u : S}
    (hD : IsClosedDisc D) (hbdD : discBd D = C.U) (hCE : C.E = {e, f}) (hef : e ≠ f)
    (hCU : C.U = closure e ∪ closure f)
    (he : K.toGraph.IsLink e v u) (hf : K.toGraph.IsLink f v u)
    (hr : r ∈ Γ.R) (hv : v ∈ Γ.V) (hur : u ∈ r) (huK : u ∈ K.V)
    (hg : g ∈ K.E) (hcapg : closure g ∩ K.V = {v, u})
    (hL : IsLineWithEnds L v u) (hLD : L ∩ D ⊆ {v, u})
    (hLK : Disjoint (L \ {v, u}) K.U)
    (hQ : IsClosedDisc Q) (hQr : Q ⊆ r ∪ {v}) (hbdQ : discBd Q = closure g ∪ L) :
    g ∈ (radialDiscDeletion K D f).E ∨
      ∃ P : Set S, IsClosedDisc P ∧ P ⊆ (r ∪ (D \ {v})) ∪ {v} ∧
        subBd P = closure e ∪ L := by
  have hopen : IsOpen (discInt Q) := hQ.isOpen_discInt fun z => (hS.2.2 z).isManifoldPoint
  have hdisBoundary : ∀ k ∈ C.E, Disjoint (discInt Q) (closure k) := by
    intro k hk
    have hcapk : closure k ∩ K.V = {v, u} := by
      rcases hCE.subset hk with rfl | rfl
      · exact he.2.2.2
      · exact hf.2.2.2
    by_cases hkg : k = g
    · subst k
      exact disjoint_left.mpr fun z hzQ hzg => hzQ.2 (hbdQ.symm ▸ Or.inl hzg)
    · have hdis := parallel_spoke_disjoint_region_bigon hS hK (hC.2 hk) hg hkg
        hv hr hur huK hcapk hcapg hQ hQr hbdQ hLK
      exact (hdis.mono_right (discInt_subset Q)).closure_left hopen |>.symm
  have hdis : Disjoint (discInt Q) (discBd D) := by
    rw [hbdD, hCU]
    exact disjoint_union_right.mpr ⟨hdisBoundary e (hCE.symm ▸ Or.inl rfl),
      hdisBoundary f (hCE.symm ▸ Or.inr rfl)⟩
  obtain ⟨z, hzL, hzn⟩ := (isPathConnected_sdiff_pair hL).nonempty
  have hzQ : z ∈ Q := Surface.discBd_subset Q (hbdQ.symm ▸ Or.inr hzL)
  have hzD : z ∉ D := fun hzD => hzn (hLD ⟨hzL, hzD⟩)
  have houtside := discInt_disjoint_of_boundary_point_outside hS hD hQ hdis hzQ hzD
  have hinterBd : Q ∩ D ⊆ discBd Q ∩ discBd D := disc_inter_subset_boundaries hS hQ hD houtside
  have hgQ : closure g ⊆ Q := (hbdQ.symm ▸ subset_union_left).trans (Surface.discBd_subset Q)
  have hgOut : g ⊆ closure (univ \ D) := by
    intro y hy
    by_cases hyD : y ∈ D
    · have hybd := (hinterBd ⟨hgQ (subset_closure hy), hyD⟩).2
      have hyfront : y ∈ frontier D := IsClosedDisc.frontier_eq_discBd hS hD |>.symm ▸ hybd
      rw [frontier_eq_closure_inter_closure] at hyfront
      simpa only [compl_eq_univ_sdiff] using hyfront.2
    · exact subset_closure ⟨mem_univ _, hyD⟩
  by_cases hgf : g = f
  · subst g
    have hinter : D ∩ Q = closure f := by
      apply Subset.antisymm
      · rintro y ⟨hyD, hyQ⟩
        have hybd := (hinterBd ⟨hyQ, hyD⟩).1
        rw [hbdQ] at hybd
        rcases hybd with hyf | hyL
        · exact hyf
        · exact (hf.2.2.2.superset (hLD ⟨hyL, hyD⟩)).1
      · intro y hyf
        exact ⟨Surface.discBd_subset D (hbdD.symm ▸ hCU.symm ▸ Or.inr hyf), hgQ hyf⟩
    have hEF : closure e ∩ closure f ⊆ {v, u} := fun y hy =>
      he.2.2.2.subset ⟨hy.1, closure_inter_subset_V he.1 hf.1 hef hy⟩
    have hLF : L ∩ closure f ⊆ {v, u} := fun y hy => hLD ⟨hy.1,
      Surface.discBd_subset D (hbdD.symm ▸ hCU.symm ▸ Or.inr hy.2)⟩
    have hends : ({v, u} : Set S) ⊆ closure e := fun y hy => (he.2.2.2.superset hy).1
    have hvu : v ≠ u := fun h => region_subset hr (h ▸ hur) (Γ.V_subset_U hv)
    have hlinef := isLine_closure hf.1 hvu hf.2.2.2
    obtain ⟨hP, hPbd⟩ := glue_bigons_along_spoke hD hQ hlinef hinter
      (hbdD.trans hCU) hbdQ hEF hLF hends
    have hPY : D ∪ Q ⊆ (r ∪ (D \ {v})) ∪ {v} := by
      rintro y (hyD | hyQ)
      · by_cases hyv : y = v
        · exact Or.inr hyv
        · exact Or.inl (Or.inr ⟨hyD, hyv⟩)
      · rcases hQr hyQ with hyr | hyv
        · exact Or.inl (Or.inl hyr)
        · exact Or.inr hyv
    exact Or.inr ⟨D ∪ Q, hP, hPY, (subBd_eq_frontier _).trans
      ((IsClosedDisc.frontier_eq_discBd hS hP).trans hPbd)⟩
  · left
    rw [radialDiscDeletion_E]
    exact ⟨hg, hgOut, hgf⟩

end GraphMinor.GM12
