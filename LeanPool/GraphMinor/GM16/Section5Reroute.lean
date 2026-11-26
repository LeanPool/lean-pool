/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section5
import LeanPool.GraphMinor.GM16.Section5Four
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section2c
import LeanPool.GraphMinor.GM09.Section3c

/-!
# Rerouting the paths in XVI (5.5)

Apply (5.4) in the union of the selected spokes and old paths. Shorten
each resulting path at its first other marked vertex. The union meets
the old graph only at the marked vertices and has no edge of that graph,
so the shortened paths are old-graph paths. Only the common spoke start
can be a new horn vertex on these paths.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM14
universe u v

/-- The shortening step on page 58 in XVI (5.5). A path with distinct
marked ends contains a path from its first end to another marked vertex
with no marked internal vertex. -/
theorem path_trim_marked
    {α : Type u} {β : Type v} {G P : Graph α β} {a b : α} {Z : Set α}
    (hP : IsGraphPathWithEnds G P a b) (ha : a ∈ Z) (hb : b ∈ Z) (hab : a ≠ b) :
    ∃ (c : α) (R : Graph α β), c ∈ Z ∧ a ≠ c ∧ R ≤ P ∧
      IsGraphPathWithEnds G R a c ∧ V(R) ∩ Z = {a, c} := by
  obtain ⟨c, ⟨_, hcZ, hca⟩, R, hRP, hR, hhit, _⟩ :=
    hP.exists_first_hit (S := Z \ {a}) ⟨b, hP.right_mem, hb, by simpa using hab.symm⟩
  have hRG := hR.mono hP.le
  refine ⟨c, R, hcZ, fun h => hca (mem_singleton_iff.mpr h.symm), hRP, hRG,
    Set.Subset.antisymm ?_ ?_⟩
  · rintro z ⟨hzR, hzZ⟩
    by_cases hza : z = a
    · exact Or.inl hza
    · have hz : z ∈ ({c} : Set α) := hhit ▸ ⟨hzR, hzZ, by simpa using hza⟩
      exact Or.inr hz
  · rintro z (rfl | hz)
    · exact ⟨hRG.left_mem, ha⟩
    · have hzc := mem_singleton_iff.mp hz
      subst z
      exact ⟨hRG.right_mem, hcZ⟩

/-- The graph part of the induction step in XVI (5.5), Claim (1),
pages 57–58. The new paths have ends among the old ends and selected
spoke ends, and use at most one more horn vertex. -/
theorem theorem_5_5_reroute
    {α : Type u} {β : Type v} {G H : Graph α β} {X : Set α}
    {x : α} {n m : ℕ} {P : Fin n → Graph α β} {u : Fin n → α}
    {Q : Fin m → Graph α β} {s t : Fin m → α}
    (hV : V(G).Finite) (hE : E(G).Finite) (hHG : H ≤ G)
    (hX : X.Finite) (_hxG : x ∈ V(G))
    (hP : ∀ i, u i ≠ x ∧ IsGraphPathWithEnds G (P i) x (u i))
    (hPu : ∀ i, u i ∈ V(H))
    (hPH : ∀ i, V(P i) ∩ V(H) = {u i})
    (hPP : ∀ i j, i ≠ j → V(P i) ∩ V(P j) = {x} ∧ Disjoint E(P i) E(P j))
    (hPX : ∀ i, V(P i) ∩ X = {x})
    (hQ : ∀ j, IsHPathWithEnds G H (Q j) (s j) (t j))
    (hQQ : Pairwise (fun i j => Disjoint V(Q i) V(Q j)))
    (hxQ : ∀ j, x ∉ V(Q j))
    (hcount : ((⋃ j, V(Q j)) ∩ X).ncard ≤ m)
    (hn : 5 * m + 2 ≤ n) :
    ∃ (R : Fin (m + 1) → Graph α β) (a b : Fin (m + 1) → α),
      (∀ i, IsHPathWithEnds G H (R i) (a i) (b i)) ∧
      Pairwise (fun i j => Disjoint V(R i) V(R j)) ∧
      ((⋃ i, V(R i)) ∩ X).ncard ≤ m + 1 ∧
      ∀ i, a i ∈ range u ∪ range s ∪ range t ∧ b i ∈ range u ∪ range s ∪ range t := by
  classical
  let Z := range u ∪ range s ∪ range t
  let J := subgraphSUnion G (range P ∪ range Q)
  have hfamily : ∀ R ∈ range P ∪ range Q, R ≤ G := by
    rintro R (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact (hP i).2.le
    · exact (hQ j).2.1.le
  have hJG : J ≤ G := subgraphSUnion_le hfamily
  have hPJ : ∀ i, IsGraphPathWithEnds J (P i) x (u i) := fun i =>
    (hP i).2.of_le (le_subgraphSUnion hfamily (Or.inl ⟨i, rfl⟩))
  have hQJ : ∀ j, IsGraphPathWithEnds J (Q j) (s j) (t j) := fun j =>
    (hQ j).2.1.of_le (le_subgraphSUnion hfamily (Or.inr ⟨j, rfl⟩))
  have hnpos : 0 < n := by omega
  let i₀ : Fin n := ⟨0, hnpos⟩
  have hxJ : x ∈ V(J) := (hPJ i₀).le.vertexSet_mono (hPJ i₀).left_mem
  obtain ⟨R₀, a, b₀, hdisj₀, hR₀⟩ := theorem_5_4_proof J x n m P u Q s t
    (hV.subset hJG.vertexSet_mono) (hE.subset hJG.edgeSet_mono) hxJ
    (fun i => ⟨(hP i).1, hPJ i⟩) hPP
    (fun j => ⟨hxQ j, hQJ j⟩) (fun j => (hQ j).2.2.1) hQQ hn
  have htrim : ∀ i, ∃ (b : α) (R : Graph α β), b ∈ Z ∧ a i ≠ b ∧ R ≤ R₀ i ∧
      IsGraphPathWithEnds J R (a i) b ∧ V(R) ∩ Z = {a i, b} := by
    intro i
    obtain ⟨ha, hb, hab, hp⟩ := hR₀ i
    exact path_trim_marked hp ha hb hab
  choose b R hb hab hRR hR hRZ using htrim
  have hZH : Z ⊆ V(H) := by
    rintro z ((⟨i, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩)
    · exact hPu i
    · exact (hQ j).2.2.2.1
    · exact (hQ j).2.2.2.2.1
  have hJH : V(J) ∩ V(H) ⊆ Z := by
    rintro z ⟨hzJ, hzH⟩
    obtain ⟨L, hL, hzL⟩ := mem_iUnion₂.mp hzJ
    rcases hL with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · have hzu := mem_singleton_iff.mp ((hPH i).subset ⟨hzL, hzH⟩)
      exact Or.inl (Or.inl ⟨i, hzu.symm⟩)
    · have hzst : z ∈ ({s j, t j} : Set α) := (hQ j).2.2.2.2.2.1 ▸ ⟨hzL, hzH⟩
      rcases hzst with hzs | hzt
      · exact Or.inl (Or.inr ⟨j, hzs.symm⟩)
      · exact Or.inr ⟨j, (mem_singleton_iff.mp hzt).symm⟩
  have hJedges : Disjoint E(J) E(H) := by
    apply Set.disjoint_left.mpr
    intro e heJ heH
    rw [edgeSet_subgraphSUnion hfamily] at heJ
    obtain ⟨L, hL, heL⟩ := mem_iUnion₂.mp heJ
    rcases hL with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · have hd := disjoint_edgeSet_of_inter_singleton (hP i).2 hHG (hPH i).subset
      exact (Set.disjoint_left.mp hd) heL heH
    · exact (Set.disjoint_left.mp (hQ j).2.2.2.2.2.2) heL heH
  have hRX : ((⋃ i, V(R i)) ∩ X).ncard ≤ m + 1 := by
    have hsub : (⋃ i, V(R i)) ∩ X ⊆ insert x ((⋃ j, V(Q j)) ∩ X) := by
      rintro z ⟨hzR, hzX⟩
      obtain ⟨i, hzi⟩ := mem_iUnion.mp hzR
      have hzJ := (hR i).le.vertexSet_mono hzi
      obtain ⟨L, hL, hzL⟩ := mem_iUnion₂.mp hzJ
      rcases hL with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exact Or.inl (mem_singleton_iff.mp ((hPX j).subset ⟨hzL, hzX⟩))
      · exact Or.inr ⟨mem_iUnion.mpr ⟨j, hzL⟩, hzX⟩
    have hfin := (hX.subset (inter_subset_right (s := ⋃ j, V(Q j)))).insert x
    have hc := (ncard_le_ncard hsub hfin).trans (ncard_insert_le x ((⋃ j, V(Q j)) ∩ X))
    omega
  refine ⟨R, a, b, ?_, ?_, hRX, ?_⟩
  · intro i
    have ha : a i ∈ Z := (hR₀ i).1
    refine ⟨hHG, (hR i).mono hJG, hab i, hZH ha, hZH (hb i),
      Set.Subset.antisymm ?_ ?_, ?_⟩
    · rintro z ⟨hzR, hzH⟩
      exact (hRZ i).subset ⟨hzR, hJH ⟨(hR i).le.vertexSet_mono hzR, hzH⟩⟩
    · rintro z (rfl | hz)
      · exact ⟨(hR i).left_mem, hZH ha⟩
      · have hzb := mem_singleton_iff.mp hz
        subst z
        exact ⟨(hR i).right_mem, hZH (hb i)⟩
    · exact hJedges.mono_left (hR i).le.edgeSet_mono
  · intro i j hij
    exact (hdisj₀ hij).mono (hRR i).vertexSet_mono (hRR j).vertexSet_mono
  · intro i
    exact ⟨(hR₀ i).1, hb i⟩

end GraphMinor.GM16
