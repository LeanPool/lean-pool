/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73SpliceFibre
public import LeanPool.GraphMinor.GM12.Section73RadialStarDrawing
import LeanPool.GraphMinor.GM11.RadialCorners
import LeanPool.GraphMinor.GM11.RadialBasics
import LeanPool.GraphMinor.GM11.Fan

/-!
# The radial splice meets the star in a point or an arc

For XII (7.3), Claim (1), page 262, the retained path misses
the merged region and hence the star. Each surviving spoke can
meet the star only in an old radial vertex, which must be its
region hub. The intersection calculation for the splice now
gives a singleton or the two star spokes. If the hubs differ,
those two spokes meet only at the deleted vertex and form a line.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

open Classical in
/-- The actual radial splice has the fibre shape required for
the selected-disc comparison in XII (7.3), Claim (1), page 262.
The point case has a common old hub; the arc case has two hubs. -/
theorem radial_spliced_circuit_fibre_shape
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ K D : Drawing S}
    (hK : PreRad (PaintingOrDrawing.drawing Γ) K) {v : S} (hv : v ∈ Γ.V)
    {r : Set S} (hr : r ∈ (deleteVertices Γ {v}).R) (hvr : v ∈ r)
    {p q x y : S} {k g g' k' : Set S}
    (hkl : K.toGraph.IsLink k v p) (hgl : K.toGraph.IsLink g p x)
    (hgl' : K.toGraph.IsLink g' q y) (hkl' : K.toGraph.IsLink k' v q)
    (hvg : v ∉ closure g) (hvg' : v ∉ closure g')
    (Q : GraphWalk K.toGraph x y) (hDis : Disjoint (walkDrawing K Q).U r)
    (hDV : D.V = ({z | z ∈ Q.support} ∪ {p, q}) ∪ (if p = q then ∅ else {v}))
    (hDE : D.E = if p = q then insert g (insert g' {e | e ∈ Q.edges})
      else insert k (insert g (insert g' (insert k' {e | e ∈ Q.edges})))) :
    (D.U ∩ ({v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e)).Subsingleton ∨
      ∃ a b, IsLineWithEnds
        (D.U ∩ ({v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e)) a b := by
  classical
  let A : Set S := {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e
  have hAr : A ⊆ r := radial_star_subset_deleted_region hS hK hv hr hvr
  have hkA : closure k ⊆ A := fun z hz => Or.inr (mem_iUnion₂.mpr
    ⟨k, ⟨hkl.1, (hkl.2.2.2.superset (Or.inl rfl)).1⟩, hz⟩)
  have hkA' : closure k' ⊆ A := fun z hz => Or.inr (mem_iUnion₂.mpr
    ⟨k', ⟨hkl'.1, (hkl'.2.2.2.superset (Or.inl rfl)).1⟩, hz⟩)
  have hQout : ∀ z ∈ Q.support, z ∉ r := by
    intro z hz
    have hzV : z ∈ (walkDrawing K Q).V := by rw [walkDrawing_V]; exact hz
    exact disjoint_left.mp hDis ((walkDrawing K Q).V_subset_U hzV)
  have hgA : closure g ∩ A ⊆ {p} := by
    rintro z ⟨hzg, hzA⟩
    have hzK := (radial_edge_inter_star hS hK hv hgl.1 hvg).2 ⟨hzg, hzA⟩
    rcases hgl.2.2.2.subset ⟨hzg, hzK⟩ with hzp | hzx
    · exact hzp
    · exact (hQout x Q.start_mem_support (hzx ▸ hAr hzA)).elim
  have hgA' : closure g' ∩ A ⊆ {q} := by
    rintro z ⟨hzg, hzA⟩
    have hzK := (radial_edge_inter_star hS hK hv hgl'.1 hvg').2 ⟨hzg, hzA⟩
    rcases hgl'.2.2.2.subset ⟨hzg, hzK⟩ with hzq | hzy
    · exact hzq
    · exact (hQout y Q.end_mem_support (hzy ▸ hAr hzA)).elim
  have heq : D.U ∩ A = if p = q then {p} else closure k ∪ closure k' :=
    spliced_circuit_inter_collapse_set hkl hkl'.symm Q hDV hDE
      (hDis.mono_right hAr) hkA hkA' hgA hgA'
  by_cases hpq : p = q
  · left
    change (D.U ∩ A).Subsingleton
    rw [heq, ite_eq_left hpq]
    exact subsingleton_singleton
  · right
    have hkk : k ≠ k' := by
      intro hkk
      have hkl₀ : K.toGraph.IsLink k' v p := hkk ▸ hkl
      exact hpq (hkl₀.right_unique hkl')
    have hmeet : closure k ∩ closure k' = {v} := by
      apply Subset.antisymm
      · rintro z ⟨hzk, hzk'⟩
        have hzK := closure_inter_subset_V hkl.1 hkl'.1 hkk ⟨hzk, hzk'⟩
        rcases hkl.2.2.2.subset ⟨hzk, hzK⟩ with hzv | hzp
        · exact hzv
        · rcases hkl'.2.2.2.subset ⟨hzk', hzK⟩ with hzv | hzq
          · exact hzv
          · exact (hpq (hzp.symm.trans hzq)).elim
      · rintro z rfl
        exact ⟨(hkl.2.2.2.superset (Or.inl rfl)).1, (hkl'.2.2.2.superset (Or.inl rfl)).1⟩
    have hvp : v ≠ p := fun heq =>
      ((bipartite_of_preRadial hK.2 k v p hkl).mp hv) (heq ▸ hv)
    have hvq : v ≠ q := fun heq =>
      ((bipartite_of_preRadial hK.2 k' v q hkl').mp hv) (heq ▸ hv)
    refine ⟨p, q, ?_⟩
    change IsLineWithEnds (D.U ∩ A) p q
    rw [heq, ite_eq_right hpq]
    exact GM11.IsLineWithEnds.union (isLine_closure hkl.1 hvp hkl.2.2.2)
      (isLine_closure hkl'.1 hvq hkl'.2.2.2) hmeet

end GraphMinor.GM12
