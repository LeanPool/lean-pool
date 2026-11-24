/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section5
import LeanPool.GraphMinor.GM16.Section5Proof
import LeanPool.GraphMinor.GM16.Section5Paths
import LeanPool.GraphMinor.GM16.Section5Degree
import LeanPool.GraphMinor.GM16.Section5Connections
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.Walks

/-!
# Graph Minors XVI (5.4)

Form the union of the spokes and the disjoint paths, and delete their
common start. Mark the vertices of `Z` in components containing at least
two vertices of `Z`. Apply (5.3) with five paths in the fan alternative.
The degree bound excludes that alternative. If there are too few marked
vertices, two spoke ends lie outside these components, and their spokes
avoid every given path. Joining these spokes gives the extra path.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09
universe u v

/-- **Graph Minors XVI, (5.4)** (pages 56–57), with the distinct-end
correction documented in `GM16Theorem54Statement`. We retain unmarked
components when applying (5.3). This has no effect on its paths, whose
ends lie in components containing two marked vertices. -/
theorem theorem_5_4_proof : GM16Theorem54Statement.{u, v} := by
  classical
  intro α β G v n m P u Q s t hV hE hv hP hPP hQ hst hQQ hn
  dsimp only
  let Z := range u ∪ range s ∪ range t
  let H := subgraphSUnion G (range P ∪ range Q)
  let D := deleteVertices H {v}
  have hfamily : ∀ R ∈ range P ∪ range Q, R ≤ G := by
    rintro R (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact (hP i).2.le
    · exact (hQ j).2.le
  have hHG : H ≤ G := subgraphSUnion_le hfamily
  have hDH : D ≤ H := deleteVertices_le H {v}
  have hDG : D ≤ G := hDH.trans hHG
  have hDV : V(D).Finite := hV.subset hDG.vertexSet_mono
  have hDE : E(D).Finite := hE.subset hDG.edgeSet_mono
  have hPH : ∀ i, IsGraphPathWithEnds H (P i) v (u i) := fun i =>
    (hP i).2.of_le (le_subgraphSUnion hfamily (Or.inl ⟨i, rfl⟩))
  have hQH : ∀ j, IsGraphPathWithEnds H (Q j) (s j) (t j) := fun j =>
    (hQ j).2.of_le (le_subgraphSUnion hfamily (Or.inr ⟨j, rfl⟩))
  let Y : Set α := {y | y ∈ Z ∧ ∃ z ∈ Z, z ≠ y ∧ Nonempty (GraphWalk D y z)}
  have hYD : Y ⊆ V(D) := by
    rintro y ⟨_, z, _, _, ⟨W⟩⟩
    exact W.mem_vertexSet_of_mem_support W.start_mem_support
  have hYfin : Y.Finite := hDV.subset hYD
  have hcomp : ∀ y ∈ Y, ∃ z ∈ Y, z ≠ y ∧ Relation.ReflTransGen D.Adj y z := by
    rintro y ⟨hyZ, z, hzZ, hzy, ⟨W⟩⟩
    exact ⟨z, ⟨hzZ, y, hyZ, hzy.symm, ⟨W.reverse⟩⟩, hzy, graphWalk_adj_reachable W⟩
  have hdegree : ∀ x ∈ V(D), {z | D.Adj x z}.ncard ≤ 4 := by
    intro x hxD
    have hxv : x ≠ v := by
      have hx : x ∈ V(H) \ {v} := hxD
      exact fun h => hx.2 (mem_singleton_iff.mpr h)
    have hPu : ∀ i j, x ∈ V(P i) → x ∈ V(P j) → i = j := by
      intro i j hxi hxj
      by_contra hij
      have hx : x ∈ ({v} : Set α) := (hPP i j hij).1 ▸ ⟨hxi, hxj⟩
      exact hxv (mem_singleton_iff.mp hx)
    have hQu : ∀ i j, x ∈ V(Q i) → x ∈ V(Q j) → i = j := by
      intro i j hxi hxj
      by_contra hij
      exact (Set.disjoint_left.mp (hQQ hij)) hxi hxj
    have hHdegree := two_path_families_neighbors_ncard_le_four hV
      (fun i => (hP i).2) (fun j => (hQ j).2) hPu hQu
    change {z | H.Adj x z}.ncard ≤ 4 at hHdegree
    have hsub : {z | D.Adj x z} ⊆ {z | H.Adj x z} := by
      rintro z ⟨e, he⟩
      exact ⟨e, he.mono hDH⟩
    have hfin : {z | H.Adj x z}.Finite := hV.subset (by
      rintro z ⟨e, he⟩
      exact hHG.vertexSet_mono he.right_mem)
    exact (ncard_le_ncard hsub hfin).trans hHdegree
  by_cases hlarge : 5 * m < Y.ncard
  · have hcount : 5 * ((m + 1) - 1) < Y.ncard := by simpa using hlarge
    rcases theorem_5_3_proof D Y (m + 1) 5 hDV hDE hYD hcomp hcount with
      ⟨R, a, b, hdisj, hR⟩ | ⟨x, R, b, hxD, hinter, hR⟩
    · refine ⟨R, a, b, hdisj, ?_⟩
      intro i
      obtain ⟨ha, hb, hab, hp, _⟩ := hR i
      exact ⟨ha.1, hb.1, hab, hp.mono hDG⟩
    · have hfan := fan_card_le_neighbors_ncard hDV
        (fun i => ⟨(hR i).2.1, (hR i).2.2.1⟩)
        (fun i j hij => (hinter i j hij).1.subset)
      have hbound := hdegree x hxD
      omega
  · have hsmall : Y.ncard ≤ 5 * m := Nat.le_of_not_gt hlarge
    have huinj : Function.Injective u := spoke_ends_injective hP
      (fun i j hij => (hPP i j hij).1)
    obtain ⟨i, j, hij, hiY, hjY⟩ := exists_two_spoke_ends_outside huinj hYfin hsmall hn
    have havoid : ∀ i, u i ∉ Y → ∀ j, Disjoint V(P i) V(Q j) := by
      intro i hi j
      apply Set.disjoint_left.mpr
      intro w hwP hwQ
      obtain ⟨z, hz, hzu, hwalk⟩ := spoke_end_reaches_other_marked_end
        (hPH i) (hQH j) (hst j) (hQ j).1 ⟨w, hwP, hwQ⟩
      have hzZ : z ∈ Z := by
        rcases hz with rfl | hz
        · exact Or.inl (Or.inr ⟨j, rfl⟩)
        · have hzt := mem_singleton_iff.mp hz
          subst z
          exact Or.inr ⟨j, rfl⟩
      exact hi ⟨Or.inl (Or.inl ⟨i, rfl⟩), z, hzZ, hzu, hwalk⟩
    exact theorem_5_4_of_two_avoiding_spokes (hP i).2 (hP j).2 (hP i).1
      (hPP i j hij).1 (Or.inl (Or.inl ⟨i, rfl⟩)) (Or.inl (Or.inl ⟨j, rfl⟩))
      (fun k => (hQ k).2)
      (fun k => ⟨Or.inl (Or.inr ⟨k, rfl⟩), Or.inr ⟨k, rfl⟩, hst k⟩)
      hQQ (havoid i hiY) (havoid j hjY)

end GraphMinor.GM16
