/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72BigonSides
public import LeanPool.GraphMinor.GM12.Section72ChordBigon
import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# No new empty bigon in the merged region

For XII (7.2), page 260, two retained spokes cannot bound an empty
bigon in the merged region. If their old end differs from the removed
boundary vertex, the bigon misses that vertex and was already empty.
At the boundary vertex, a bigon containing the removed disc can be
cut along the deleted spoke. One side of this cut was an old empty
bigon. Both cases contradict the original radial condition.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

variable {S : Type*} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
private theorem subset_old_region_of_disjoint_inside {D Q r : Set S} {v : S}
    (hbd : discBd D ⊆ r ∪ {v}) (hQ : Q ⊆ (r ∪ (D \ {v})) ∪ {v})
    (hdis : Disjoint (discInt D) Q) : Q ⊆ r ∪ {v} := by
  intro x hx
  rcases hQ hx with (hxr | ⟨hxD, _⟩) | hxv
  · exact Or.inl hxr
  · have hxb : x ∈ discBd D := by
      by_contra hnb
      exact disjoint_left.mp hdis ⟨hxD, hnb⟩ hx
    exact hbd hxb
  · exact Or.inr hxv

/-- Retained spokes cannot bound a new empty bigon in the merged
region of XII (7.2), page 260. Cutting along the deleted spoke handles
the case in which the bigon contains the removed disc. -/
theorem no_empty_bigon_in_merged_region (hS : IsClosedSurface S)
    {Γ K C : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    (hC : C.IsSubdrawing K) {D r f g h : Set S} {v u x : S}
    (hD : IsClosedDisc D) (hb : frontier D = C.U) (hCZ : C.U ⊆ r ∪ {v})
    (hr : r ∈ Γ.R) (hv : v ∈ Γ.V) (hur : u ∈ r) (huK : u ∈ K.V)
    (hfC : f ∈ C.E) (hf : K.toGraph.IsLink f v u)
    (hg : g ∈ (radialDiscDeletion K D f).E)
    (hh : h ∈ (radialDiscDeletion K D f).E) (hgh : g ≠ h)
    (hx : x ∈ Γ.V) (hcapg : closure g ∩ K.V = {x, u})
    (hcaph : closure h ∩ K.V = {x, u}) :
    ¬ ∃ Q : Set S, IsClosedDisc Q ∧ Q ⊆ (r ∪ (D \ {v})) ∪ {x} ∧
      subBd Q = closure g ∪ closure h := by
  rintro ⟨Q, hQ, hQY, hQbd⟩
  have hgd := (radialDiscDeletion_E K D f).subset hg
  have hhd := (radialDiscDeletion_E K D f).subset hh
  have hfg : f ≠ g := Ne.symm hgd.2.2
  have hfh : f ≠ h := Ne.symm hhd.2.2
  have hbdD : discBd D = C.U := (IsClosedDisc.frontier_eq_discBd hS hD).symm.trans hb
  have hbdQ : discBd Q = closure g ∪ closure h :=
    (IsClosedDisc.frontier_eq_discBd hS hQ).symm.trans
      ((subBd_eq_frontier Q).symm.trans hQbd)
  have hQout : discBd Q ⊆ closure (univ \ D) := by
    rw [hbdQ]
    exact union_subset (closure_minimal hgd.2.1 isClosed_closure)
      (closure_minimal hhd.2.1 isClosed_closure)
  have hvD : v ∈ D := by
    have hvcl : v ∈ closure f := (hf.2.2.2.superset (Or.inl rfl)).1
    exact Surface.discBd_subset D (hbdD.symm ▸ C.closure_subset_U hfC hvcl)
  have hbdDZ : discBd D ⊆ r ∪ {v} := hbdD ▸ hCZ
  by_cases hxv : x = v
  · subst x
    have hvu : v ≠ u := fun heq => region_subset hr (heq ▸ hur) (Γ.V_subset_U hv)
    have hlinef := isLine_closure (hC.2 hfC) hvu hf.2.2.2
    have hlineg := isLine_closure hgd.1 hvu hcapg
    have hlineh := isLine_closure hhd.1 hvu hcaph
    have hGF : closure g ∩ closure h ⊆ {v, u} := by
      intro y hy
      exact hcapg.subset ⟨hy.1, closure_inter_subset_V hgd.1 hhd.1 hgh hy⟩
    rcases disc_subset_or_disjoint_interior_of_boundary_outside hS hD hQ hQout with hDQ | hdis
    · have hFbd : closure f ⊆ discBd D := hbdD.symm ▸ C.closure_subset_U hfC
      have hFQ : closure f ∩ discBd Q = {v, u} := by
        apply Subset.antisymm
        · rintro y ⟨hyf, hyQ⟩
          rw [hbdQ] at hyQ
          have hyV : y ∈ K.V := by
            rcases hyQ with hyg | hyh
            · exact closure_inter_subset_V (hC.2 hfC) hgd.1 hfg ⟨hyf, hyg⟩
            · exact closure_inter_subset_V (hC.2 hfC) hhd.1 hfh ⟨hyf, hyh⟩
          exact hf.2.2.2.subset ⟨hyf, hyV⟩
        · intro y hy
          exact ⟨(hf.2.2.2.superset hy).1, hbdQ.symm ▸ Or.inl ((hcapg.superset hy).1)⟩
      obtain ⟨P, hP, hPQ, hPbd, hPdis⟩ := exists_chord_bigon_outside_nested_disc
        hD hQ hDQ hlinef hlineg hlineh hvu hFbd hbdQ hGF hFQ
      have hPZ : P ⊆ r ∪ {v} :=
        subset_old_region_of_disjoint_inside hbdDZ (hPQ.trans hQY) hPdis
      have hPbd' : subBd P = discBd P :=
        (subBd_eq_frontier P).trans (IsClosedDisc.frontier_eq_discBd hS hP)
      rcases hPbd with hPG | hPH
      · exact hK.2.2.2.2.2 g hgd.1 f (hC.2 hfC) hgd.2.2 v hv r hr u ⟨hur, huK⟩
          hcapg hf.2.2.2 ⟨P, hP, hPZ, hPbd'.trans hPG⟩
      · exact hK.2.2.2.2.2 h hhd.1 f (hC.2 hfC) hhd.2.2 v hv r hr u ⟨hur, huK⟩
          hcaph hf.2.2.2 ⟨P, hP, hPZ, hPbd'.trans hPH⟩
    · exact hK.2.2.2.2.2 g hgd.1 h hhd.1 hgh v hv r hr u ⟨hur, huK⟩
        hcapg hcaph ⟨Q, hQ, subset_old_region_of_disjoint_inside hbdDZ hQY hdis, hQbd⟩
  · have hvY : v ∉ r ∪ (D \ {v}) := by
      rintro (hvr | ⟨_, hvv⟩)
      · exact region_subset hr hvr (Γ.V_subset_U hv)
      · exact hvv rfl
    have hvQ : v ∉ Q := by
      intro hvQ
      rcases hQY hvQ with hvY' | hvx
      · exact hvY hvY'
      · exact hxv (mem_singleton_iff.mp hvx).symm
    have hQold := disc_subset_old_region_of_missing_boundary_vertex hS hD hQ hvD hvQ
      hQout hbdDZ hQY
    exact hK.2.2.2.2.2 g hgd.1 h hhd.1 hgh x hx r hr u ⟨hur, huK⟩
      hcapg hcaph ⟨Q, hQ, hQold, hQbd⟩

end GraphMinor.GM12
