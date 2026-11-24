/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section5
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.Walks

/-!
# The degree bounds in XVI (5.4)

A path has at most one neighbor at either end and at most two neighbors
at any vertex. Splitting at the vertex reduces the latter fact to the
former. These bounds exclude a fan of five paths in the union of the
spokes and the disjoint paths away from the common start.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09
universe u v

/-- An end of a path has at most one neighbor in the path. -/
theorem path_start_neighbors_subsingleton
    {α : Type u} {β : Type v} {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) : {z | P.Adj a z}.Subsingleton := by
  obtain ⟨_, W, hsimple, _, hE⟩ := hP
  cases W with
  | nil ha =>
    intro z hz
    obtain ⟨e, he⟩ := hz
    have heE := he.edge_mem
    rw [hE] at heE
    have : e ∈ ([] : List β) := heE
    exact False.elim (List.not_mem_nil this)
  | @cons a c b e he W =>
    have haW : a ∉ W.support := (List.nodup_cons.mp hsimple).1
    have hneighbor : ∀ z, P.Adj a z → z = c := by
      intro z ⟨f, hf⟩
      have hfE := hf.edge_mem
      rw [hE] at hfE
      change f ∈ e :: W.edges at hfE
      rcases List.mem_cons.mp hfE with rfl | hfE
      · exact hf.right_unique he
      · exact False.elim (haW (walk_isLink_mem_support W hfE hf).1)
    intro z hz z' hz'
    exact (hneighbor z hz).trans (hneighbor z' hz').symm

/-- Every vertex of a path has at most two neighbors in it. This is the
path degree bound used in XVI (5.4), page 56. -/
theorem path_neighbors_ncard_le_two
    {α : Type u} {β : Type v} {G P : Graph α β} {a b x : α}
    (hP : IsGraphPathWithEnds G P a b) : {z | P.Adj x z}.ncard ≤ 2 := by
  classical
  by_cases hx : x ∈ V(P)
  · obtain ⟨P₁, P₂, h₁, h₂, hp₁, hp₂, hunion, _, _⟩ := hP.exists_split_at hx
    have hs₁ := path_start_neighbors_subsingleton hp₁.symm
    have hs₂ := path_start_neighbors_subsingleton hp₂
    have heq : {z | P.Adj x z} = {z | P₁.Adj x z} ∪ {z | P₂.Adj x z} := by
      ext z
      rw [← hunion]
      constructor
      · rintro ⟨e, he⟩
        rcases (subgraphUnion_isLink h₁ h₂).mp he with h | h
        · exact Or.inl ⟨e, h⟩
        · exact Or.inr ⟨e, h⟩
      · rintro (⟨e, he⟩ | ⟨e, he⟩)
        · exact ⟨e, (subgraphUnion_isLink h₁ h₂).mpr (Or.inl he)⟩
        · exact ⟨e, (subgraphUnion_isLink h₁ h₂).mpr (Or.inr he)⟩
    rw [heq]
    have hc₁ := (ncard_le_one hs₁.finite).mpr (fun _ ha _ hb => hs₁ ha hb)
    have hc₂ := (ncard_le_one hs₂.finite).mpr (fun _ ha _ hb => hs₂ ha hb)
    have hc := ncard_union_le {z | P₁.Adj x z} {z | P₂.Adj x z}
    omega
  · have heq : {z | P.Adj x z} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨e, he⟩
      exact hx he.left_mem
    rw [heq, ncard_empty]
    exact Nat.zero_le _

/-- In a union of paths, a vertex belonging to at most one member
has at most two neighbors. -/
theorem path_family_neighbors_ncard_le_two
    {α : Type u} {β : Type v} {ι : Type*} {G : Graph α β}
    {P : ι → Graph α β} {a b : ι → α} {x : α}
    (hP : ∀ i, IsGraphPathWithEnds G (P i) (a i) (b i))
    (hunique : ∀ i j, x ∈ V(P i) → x ∈ V(P j) → i = j) :
    {z | (subgraphSUnion G (range P)).Adj x z}.ncard ≤ 2 := by
  classical
  let H := subgraphSUnion G (range P)
  have hPG : ∀ R ∈ range P, R ≤ G := by
    rintro R ⟨i, rfl⟩
    exact (hP i).le
  have hHG : H ≤ G := subgraphSUnion_le hPG
  have hmem : ∀ z, H.Adj x z → ∃ i, (P i).Adj x z := by
    intro z ⟨e, he⟩
    have heE := he.edge_mem
    rw [edgeSet_subgraphSUnion hPG] at heE
    obtain ⟨R, ⟨i, rfl⟩, hei⟩ := mem_iUnion₂.mp heE
    exact ⟨i, e, ((hP i).le.isLink_iff hei).mpr (he.mono hHG)⟩
  by_cases hex : ∃ i, x ∈ V(P i)
  · obtain ⟨i, hxi⟩ := hex
    have hsub : {z | H.Adj x z} ⊆ {z | (P i).Adj x z} := by
      intro z hz
      obtain ⟨j, hj⟩ := hmem z hz
      obtain ⟨e, he⟩ := hj
      have hji := hunique j i he.left_mem hxi
      subst j
      exact ⟨e, he⟩
    have hfin : {z | (P i).Adj x z}.Finite := (hP i).vertexSet_finite.subset
      (by rintro z ⟨e, he⟩; exact he.right_mem)
    exact (ncard_le_ncard hsub hfin).trans (path_neighbors_ncard_le_two (hP i))
  · have heq : {z | H.Adj x z} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨i, e, he⟩ := hmem z hz
      exact hex ⟨i, he.left_mem⟩
    rw [heq, ncard_empty]
    exact Nat.zero_le _

/-- A path with distinct ends has a neighbor different from its first
end. This follows from its first edge and its simple vertex list. -/
theorem path_exists_neighbor_at_start
    {α : Type u} {β : Type v} {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) (hab : a ≠ b) :
    ∃ y, P.Adj a y ∧ y ≠ a := by
  obtain ⟨_, W, hsimple, _, _⟩ := hP
  cases W with
  | nil _ => exact False.elim (hab rfl)
  | @cons a c b e he W =>
    refine ⟨c, ⟨e, he⟩, ?_⟩
    intro hca
    have haW := (List.nodup_cons.mp hsimple).1
    exact haW (hca ▸ W.start_mem_support)

/-- A fan of `n` paths with distinct other ends needs at least `n`
neighbors at its centre. This excludes the five-path alternative in
XVI (5.4) once the degree is bounded by four. -/
theorem fan_card_le_neighbors_ncard
    {α : Type u} {β : Type v} {G : Graph α β} {x : α} {n : ℕ}
    {P : Fin n → Graph α β} {b : Fin n → α}
    (hV : V(G).Finite)
    (hP : ∀ i, b i ≠ x ∧ IsGraphPathWithEnds G (P i) x (b i))
    (hinter : ∀ i j, i ≠ j → V(P i) ∩ V(P j) ⊆ {x}) :
    n ≤ {z | G.Adj x z}.ncard := by
  classical
  have hex := fun i => path_exists_neighbor_at_start (hP i).2 (hP i).1.symm
  choose y hy hne using hex
  have hyinj : Function.Injective y := by
    intro i j hyij
    by_contra hij
    obtain ⟨e, hei⟩ := hy i
    obtain ⟨f, hfj⟩ := hy j
    have hyj : y i ∈ V(P j) := hyij ▸ hfj.right_mem
    have heq := mem_singleton_iff.mp (hinter i j hij ⟨hei.right_mem, hyj⟩)
    exact hne i heq
  have hsub : range y ⊆ {z | G.Adj x z} := by
    rintro z ⟨i, rfl⟩
    obtain ⟨e, he⟩ := hy i
    exact ⟨e, he.mono (hP i).2.le⟩
  have hfin : {z | G.Adj x z}.Finite := hV.subset
    (by rintro z ⟨e, he⟩; exact he.right_mem)
  have hc := ncard_le_ncard hsub hfin
  simpa only [ncard_range_of_injective hyinj, Nat.card_fin] using hc

/-- The union of two path families has at most four neighbors at a
vertex belonging to at most one member of each family. This is the
bound for the graph `H` in XVI (5.4), pages 56–57. -/
theorem two_path_families_neighbors_ncard_le_four
    {α : Type u} {β : Type v} {ι κ : Type*} {G : Graph α β}
    {P : ι → Graph α β} {a b : ι → α}
    {Q : κ → Graph α β} {s t : κ → α} {x : α}
    (hV : V(G).Finite)
    (hP : ∀ i, IsGraphPathWithEnds G (P i) (a i) (b i))
    (hQ : ∀ j, IsGraphPathWithEnds G (Q j) (s j) (t j))
    (hPu : ∀ i j, x ∈ V(P i) → x ∈ V(P j) → i = j)
    (hQu : ∀ i j, x ∈ V(Q i) → x ∈ V(Q j) → i = j) :
    {z | (subgraphSUnion G (range P ∪ range Q)).Adj x z}.ncard ≤ 4 := by
  classical
  let HP := subgraphSUnion G (range P)
  let HQ := subgraphSUnion G (range Q)
  let H := subgraphSUnion G (range P ∪ range Q)
  have hPG : ∀ R ∈ range P, R ≤ G := by
    rintro R ⟨i, rfl⟩
    exact (hP i).le
  have hQG : ∀ R ∈ range Q, R ≤ G := by
    rintro R ⟨j, rfl⟩
    exact (hQ j).le
  have hRG : ∀ R ∈ range P ∪ range Q, R ≤ G := by
    intro R hR
    exact hR.elim (hPG R) (hQG R)
  have hHP : HP ≤ G := subgraphSUnion_le hPG
  have hHQ : HQ ≤ G := subgraphSUnion_le hQG
  have hH : H ≤ G := subgraphSUnion_le hRG
  have hsub : {z | H.Adj x z} ⊆ {z | HP.Adj x z} ∪ {z | HQ.Adj x z} := by
    rintro z ⟨e, he⟩
    have heE := he.edge_mem
    rw [edgeSet_subgraphSUnion hRG] at heE
    obtain ⟨R, hR, heR⟩ := mem_iUnion₂.mp heE
    have heR' := ((hRG R hR).isLink_iff heR).mpr (he.mono hH)
    rcases hR with hR | hR
    · exact Or.inl ⟨e, heR'.mono (le_subgraphSUnion hPG hR)⟩
    · exact Or.inr ⟨e, heR'.mono (le_subgraphSUnion hQG hR)⟩
  have hfin : ({z | HP.Adj x z} ∪ {z | HQ.Adj x z}).Finite := hV.subset (by
    rintro z (⟨e, he⟩ | ⟨e, he⟩)
    · exact hHP.vertexSet_mono he.right_mem
    · exact hHQ.vertexSet_mono he.right_mem)
  have hc := (ncard_le_ncard hsub hfin).trans
    (ncard_union_le {z | HP.Adj x z} {z | HQ.Adj x z})
  have hcP := path_family_neighbors_ncard_le_two hP hPu
  have hcQ := path_family_neighbors_ncard_le_two hQ hQu
  change {z | HP.Adj x z}.ncard ≤ 2 at hcP
  change {z | HQ.Adj x z}.ncard ≤ 2 at hcQ
  change {z | H.Adj x z}.ncard ≤ 4
  omega

end GraphMinor.GM16
