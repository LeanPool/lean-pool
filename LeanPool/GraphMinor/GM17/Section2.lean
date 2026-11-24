/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.CuffOrder
public import LeanPool.GraphMinor.GM10.TangleLemmas

import LeanPool.GraphMinor.Surface.Cuffs

/-!
# Sections 2 and 3 of Graph Minors XVII: Portrayals, (2.1), and Warp

This file formalizes Sections 2 and 3 (pages 165–169) of N. Robertson and P. D. Seymour,
*Graph Minors. XVII. Taming a vortex*, J. Combin. Theory Ser. B 77 (1999) 162–210:
- Basic properties of `Portrayal.borderPlus`, `Portrayal.gammaImage`, `Portrayal.cellsUnion`,
  `Portrayal.otherCellsGraph`, and `Portrayal.areaGraph`.
- Theorem (2.1) (`theorem_2_1`, pages 166–168), characterizing the intersection of `cellsUnion I₁`
  and `cellsUnion I₂` for a partition `(I₁, I₂)` of `C(Γ)`, with its subproof claims (1), (2), (3).
- Basic properties of cell warp (`CellWarpLE`, `cellWarp`), cuff warp (`warpAt`), and portrayal
  warp (`warp`) from Section 3 (page 168).
-/

public section

namespace GraphMinor.GM17

open Set Function Topology
open GraphMinor.Surface
open GraphMinor.GM10
open GraphMinor.Hypergraph

universe u v

/-! ## 1. Basic Lemmas on Portrayals -/

namespace Portrayal

variable {α : Type u} {β : Type v} {G : Hypergraph α β} (π : Portrayal G)

theorem mem_borderPlus_iff {n : π.S} {v : α} :
    v ∈ π.borderPlus n ↔ v ∈ π.borderSet n ∨ (n ∈ π.domγ ∧ v = π.nodeVertex n) :=
  Iff.rfl

theorem borderSet_subset_borderPlus (n : π.S) : π.borderSet n ⊆ π.borderPlus n :=
  fun _ hv => Or.inl hv

theorem nodeVertex_mem_borderPlus {n : π.S} (hn : n ∈ π.domγ) :
    π.nodeVertex n ∈ π.borderPlus n :=
  Or.inr ⟨hn, rfl⟩

theorem borderPlus_eq_borderSet {n : π.S} (hn : n ∉ π.domγ) :
    π.borderPlus n = π.borderSet n := by
  ext v
  simp only [borderPlus, mem_ofPred_eq, hn, false_and, or_false]

theorem borderPlus_eq_insert {n : π.S} (hn : n ∈ π.domγ) :
    π.borderPlus n = insert (π.nodeVertex n) (π.borderSet n) := by
  ext v
  simp only [borderPlus, mem_ofPred_eq, hn, true_and, mem_insert_iff, or_comm]

theorem borderSet_finite {n : π.S} (hn : n ∈ π.Γ.N ∩ bd π.S) :
    (π.borderSet n).Finite :=
  G.vertexSet_finite.subset (π.borderSet_subset n hn)

theorem borderPlus_subset_vertexSet {n : π.S} (hn : n ∈ π.Γ.N ∩ bd π.S) :
    π.borderPlus n ⊆ G.vertexSet := by
  rintro v (hv | ⟨hdom, rfl⟩)
  · exact π.borderSet_subset n hn hv
  · exact π.nodeVertex_mem n hdom

theorem borderPlus_finite {n : π.S} (hn : n ∈ π.Γ.N ∩ bd π.S) :
    (π.borderPlus n).Finite :=
  G.vertexSet_finite.subset (π.borderPlus_subset_vertexSet hn)

theorem ncard_borderPlus_of_mem_domγ {n : π.S} (hdom : n ∈ π.domγ) (hbd : n ∈ bd π.S) :
    (π.borderPlus n).ncard = (π.borderSet n).ncard + 1 := by
  have hn : n ∈ π.Γ.N ∩ bd π.S := ⟨π.domγ_subset hdom, hbd⟩
  rw [π.borderPlus_eq_insert hdom,
    ncard_insert_of_notMem (π.p3_notMem n ⟨hdom, hbd⟩) (π.borderSet_finite hn)]

theorem ncard_borderPlus_of_notMem_domγ {n : π.S} (hdom : n ∉ π.domγ) :
    (π.borderPlus n).ncard = (π.borderSet n).ncard := by
  rw [π.borderPlus_eq_borderSet hdom]

theorem ncard_borderPlus_le {n : π.S} (hn : n ∈ π.Γ.N ∩ bd π.S) :
    (π.borderPlus n).ncard ≤ (π.borderSet n).ncard + 1 := by
  by_cases hdom : n ∈ π.domγ
  · rw [π.ncard_borderPlus_of_mem_domγ hdom hn.2]
  · rw [π.ncard_borderPlus_of_notMem_domγ hdom]
    omega

theorem borderPlus_subset_cellGraph {c : Set π.S} (hc : c ∈ π.Γ.C)
    (hbd : (c ∩ bd π.S).Nonempty) {n : π.S} (hn : n ∈ tilde c) :
    π.borderPlus n ⊆ (π.cellGraph c).vertexSet := by
  rintro v (hv | ⟨hdom, rfl⟩)
  · exact π.p3_subset c hc hbd n hn hv
  · exact π.p2 c hc n ⟨hn, hdom⟩

theorem mem_gammaImage_iff {X : Set π.S} {v : α} :
    v ∈ π.gammaImage X ↔ ∃ n ∈ X ∩ π.domγ, π.nodeVertex n = v :=
  Iff.rfl

theorem gammaImage_mono {X Y : Set π.S} (h : X ⊆ Y) :
    π.gammaImage X ⊆ π.gammaImage Y :=
  image_mono (inter_subset_inter_left π.domγ h)

theorem gammaImage_inter {X Y : Set π.S} :
    π.gammaImage (X ∩ Y) = π.gammaImage X ∩ π.gammaImage Y := by
  have h : (X ∩ Y) ∩ π.domγ = (X ∩ π.domγ) ∩ (Y ∩ π.domγ) := by
    ext x; simp only [mem_inter_iff]; tauto
  unfold gammaImage
  rw [h]
  exact π.nodeVertex_injOn.image_inter inter_subset_right inter_subset_right

theorem gammaImage_tilde_subset_cellGraph {c : Set π.S} (hc : c ∈ π.Γ.C) :
    π.gammaImage (tilde c) ⊆ (π.cellGraph c).vertexSet := by
  rintro v ⟨n, hn, rfl⟩
  exact π.p2 c hc n hn

theorem cellsUnion_le (I : Set (Set π.S)) : π.cellsUnion I ≤ G where
  vertexSet_subset := iUnion₂_subset fun c hc => (π.cellGraph_le c hc.2).vertexSet_subset
  edgeSet_subset := iUnion₂_subset fun c hc => (π.cellGraph_le c hc.2).edgeSet_subset
  ends_eq e he := by
    obtain ⟨c, hc, hec⟩ := mem_iUnion₂.mp he
    ext v
    exact ⟨fun hinc => ⟨⟨c, hc, hec⟩, hinc⟩, fun ⟨_, hinc⟩ => hinc⟩

theorem cellGraph_le_cellsUnion {I : Set (Set π.S)} {c : Set π.S}
    (hcI : c ∈ I) (hcC : c ∈ π.Γ.C) :
    π.cellGraph c ≤ π.cellsUnion I := by
  rw [le_iff_of_le (π.cellGraph_le c hcC) (π.cellsUnion_le I)]
  exact ⟨subset_iUnion₂ (s := fun c _ => (π.cellGraph c).vertexSet) c ⟨hcI, hcC⟩,
         subset_iUnion₂ (s := fun c _ => (π.cellGraph c).edgeSet) c ⟨hcI, hcC⟩⟩

theorem cellsUnion_C : π.cellsUnion π.Γ.C = G := by
  apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq (π.cellsUnion_le π.Γ.C) le_rfl
  · refine Subset.antisymm (π.cellsUnion_le π.Γ.C).vertexSet_subset ?_
    intro v hv
    obtain ⟨c, hc, hvc⟩ := π.p1_vertex v hv
    exact mem_iUnion₂.mpr ⟨c, ⟨hc, hc⟩, hvc⟩
  · refine Subset.antisymm (π.cellsUnion_le π.Γ.C).edgeSet_subset ?_
    intro e he
    obtain ⟨c, hc, hec⟩ := π.p1_edge e he
    exact mem_iUnion₂.mpr ⟨c, ⟨hc, hc⟩, hec⟩

theorem cellsUnion_union (I₁ I₂ : Set (Set π.S)) :
    π.cellsUnion (I₁ ∪ I₂) = π.cellsUnion I₁ ∪ π.cellsUnion I₂ := by
  have h1 : π.cellsUnion (I₁ ∪ I₂) ≤ G := π.cellsUnion_le (I₁ ∪ I₂)
  have h2 : π.cellsUnion I₁ ∪ π.cellsUnion I₂ ≤ G :=
    union_le (π.cellsUnion_le I₁) (π.cellsUnion_le I₂)
  apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq h1 h2
  · ext v
    simp only [cellsUnion, union_vertexSet, mem_union, mem_iUnion₂, mem_inter_iff]
    constructor
    · rintro ⟨c, ⟨hc1 | hc2, hcC⟩, h⟩
      · exact Or.inl ⟨c, ⟨hc1, hcC⟩, h⟩
      · exact Or.inr ⟨c, ⟨hc2, hcC⟩, h⟩
    · rintro (⟨c, ⟨hc1, hcC⟩, h⟩ | ⟨c, ⟨hc2, hcC⟩, h⟩)
      · exact ⟨c, ⟨Or.inl hc1, hcC⟩, h⟩
      · exact ⟨c, ⟨Or.inr hc2, hcC⟩, h⟩
  · ext e
    simp only [cellsUnion, union_edgeSet, mem_union, mem_iUnion₂, mem_inter_iff]
    constructor
    · rintro ⟨c, ⟨hc1 | hc2, hcC⟩, h⟩
      · exact Or.inl ⟨c, ⟨hc1, hcC⟩, h⟩
      · exact Or.inr ⟨c, ⟨hc2, hcC⟩, h⟩
    · rintro (⟨c, ⟨hc1, hcC⟩, h⟩ | ⟨c, ⟨hc2, hcC⟩, h⟩)
      · exact ⟨c, ⟨Or.inl hc1, hcC⟩, h⟩
      · exact ⟨c, ⟨Or.inr hc2, hcC⟩, h⟩

theorem otherCellsGraph_vertexSet (c₀ : Set π.S) :
    (π.otherCellsGraph c₀).vertexSet = π.otherVertices c₀ := by
  ext v
  simp only [otherCellsGraph, cellsUnion, otherVertices, mem_iUnion, mem_inter_iff,
    mem_sdiff, mem_singleton_iff, mem_ofPred_eq]
  tauto

theorem p6_borderPlus {c : Set π.S} (hc : c ∈ π.Γ.C) (hbd : (c ∩ bd π.S).Nonempty)
    {v : α} (hvc : v ∈ (π.cellGraph c).vertexSet) (hvo : v ∈ π.otherVertices c) :
    ∃ n ∈ tilde c, v ∈ π.borderPlus n :=
  π.p6 c hc hbd v hvc hvo

/-- If $v \in V(\alpha(c) \cap \alpha(-c))$ and $v \notin \gamma(\tilde{c})$, then $c$ is a border
cell and $v \in \beta(n)$ for some $n \in \tilde{c}$. -/
theorem border_of_mem_otherVertices_notMem_gammaImage {c : Set π.S} (hc : c ∈ π.Γ.C)
    {v : α} (hvc : v ∈ (π.cellGraph c).vertexSet) (hvo : v ∈ π.otherVertices c)
    (hnot : v ∉ π.gammaImage (tilde c)) :
    (c ∩ bd π.S).Nonempty ∧ ∃ n ∈ tilde c, v ∈ π.borderSet n := by
  have hbd : (c ∩ bd π.S).Nonempty := by
    by_contra hnot_bd
    exact hnot (π.p5 c hc hnot_bd v hvc hvo)
  obtain ⟨n, hn, hvn⟩ := π.p6_borderPlus hc hbd hvc hvo
  rcases hvn with hvn | ⟨hdom, rfl⟩
  · exact ⟨hbd, n, hn, hvn⟩
  · exfalso
    exact hnot ⟨n, ⟨hn, hdom⟩, rfl⟩

/-- If $c_1, c_2 \in C(\Gamma)$ are distinct, $c_1$ borders a cuff $\Theta$, $n_1 \in \tilde{c}_1$,
$v \in \beta(n_1) \cap V(\alpha(c_2))$, and $c_2$ does not border $\Theta$, then $c_2$ is internal
and there exists $n \in \tilde{c}_2 \cap \operatorname{dom}(\gamma) \cap \Theta$ with
$v = \gamma(n)$.
Graph Minors XVII, proof of (2.1), Claim (3) (page 167). -/
theorem exists_node_of_not_borders_cuff {c₁ c₂ Θ : Set π.S}
    (hc₁ : c₁ ∈ π.Γ.C) (hc₂ : c₂ ∈ π.Γ.C) (hne : c₁ ≠ c₂)
    (hΘ : Θ ∈ cuffs π.S) (hc₁Θ : (c₁ ∩ Θ).Nonempty) (hc₂Θ : ¬ (c₂ ∩ Θ).Nonempty)
    {n₁ : π.S} (hn₁ : n₁ ∈ tilde c₁) {v : α}
    (hvn₁ : v ∈ π.borderSet n₁) (hvc₂ : v ∈ (π.cellGraph c₂).vertexSet) :
    ¬ (c₂ ∩ bd π.S).Nonempty ∧ ∃ n ∈ tilde c₂ ∩ π.domγ, n ∈ Θ ∧ v = π.nodeVertex n := by
  have hn₁Θ : n₁ ∈ π.Γ.N ∩ Θ := (π.Γ.border_cell_subset_cuff hc₁ hΘ hc₁Θ).2.2.2.1 hn₁
  have hvo₂ : v ∈ π.otherVertices c₂ :=
    ⟨c₁, hc₁, hne, π.p3_subset c₁ hc₁
      (by rw [(π.Γ.border_cell_subset_cuff hc₁ hΘ hc₁Θ).2.1]; exact hc₁Θ) n₁ hn₁ hvn₁⟩
  have hnot_bd₂ : ¬ (c₂ ∩ bd π.S).Nonempty := by
    rintro ⟨x, hxc₂, hxbd⟩
    let Θ' := connectedComponentIn (bd π.S) x
    have hΘ' : Θ' ∈ cuffs π.S := ⟨x, hxbd, rfl⟩
    have hc₂Θ' : (c₂ ∩ Θ').Nonempty := ⟨x, hxc₂, mem_connectedComponentIn hxbd⟩
    have hΘ_ne : Θ ≠ Θ' := fun h => hc₂Θ (h ▸ hc₂Θ')
    obtain ⟨n₂, hn₂, hvn₂⟩ := π.p6_borderPlus hc₂ ⟨x, hxc₂, hxbd⟩ hvc₂ hvo₂
    have hn₂Θ' : n₂ ∈ π.Γ.N ∩ Θ' := (π.Γ.border_cell_subset_cuff hc₂ hΘ' hc₂Θ').2.2.2.1 hn₂
    rcases hvn₂ with hvn₂ | ⟨hdom₂, rfl⟩
    · exact Set.disjoint_left.mp (π.p4_disjoint Θ hΘ Θ' hΘ' hΘ_ne n₁ hn₁Θ n₂ hn₂Θ') hvn₁ hvn₂
    · have hn₂_not_Θ : n₂ ∉ Θ := by
        intro hn₂_in_Θ
        rcases hΘ with ⟨x₀, hx₀, rfl⟩
        have heq : connectedComponentIn (bd π.S) x₀ = Θ' :=
          (connectedComponentIn_eq hn₂_in_Θ).trans (connectedComponentIn_eq hn₂Θ'.2).symm
        exact hΘ_ne heq
      exact π.p4_notMem Θ hΘ n₁ hn₁Θ n₂ hdom₂ hn₂_not_Θ hvn₁
  obtain ⟨n, hn, rfl⟩ := π.p5 c₂ hc₂ hnot_bd₂ v hvc₂ hvo₂
  have hn_in_Θ : n ∈ Θ := by
    by_contra hn_not_Θ
    exact π.p4_notMem Θ hΘ n₁ hn₁Θ n hn.2 hn_not_Θ hvn₁
  exact ⟨hnot_bd₂, n, hn, hn_in_Θ, rfl⟩

end Portrayal

/-! ## 2. Cyclic Partition Lemma on a Cuff Enumeration -/

private theorem cyclicDist_shift {k : ℕ} (hk : 0 < k) (base : Fin k) {u v : ℕ}
    (huv : u ≤ v) (hvu : v - u < k) :
    cyclicDist (⟨(base.1 + u) % k, Nat.mod_lt _ hk⟩ : Fin k)
      (⟨(base.1 + v) % k, Nat.mod_lt _ hk⟩ : Fin k) = v - u := by
  set r := (base.1 + u) % k
  set d := v - u
  have hr_lt : r < k := Nat.mod_lt _ hk
  have hiv_eq : (base.1 + v) % k = (r + d) % k := by
    dsimp [r, d]
    have heq : base.1 + v = (base.1 + u) + (v - u) := by omega
    rw [heq, Nat.mod_add_mod]
  rw [cyclicDist_eq_ite]
  dsimp
  by_cases hrd : r + d < k
  · have hiv_val : (base.1 + v) % k = r + d := hiv_eq.trans (Nat.mod_eq_of_lt hrd)
    split_ifs <;> omega
  · have hsub : (r + d - k) % k = r + d - k := Nat.mod_eq_of_lt (by omega)
    have hadd : ((r + d - k) + k) % k = (r + d - k) % k := Nat.add_mod_right _ _
    have heq : (r + d - k) + k = r + d := by omega
    have hmod_eq : ((r + d - k) + k) % k = (r + d) % k := congrArg (· % k) heq
    have hiv_val : (base.1 + v) % k = r + d - k := by omega
    split_ifs <;> omega

/-- If `E` is a cuff enumeration of $\Theta$ and `(I₁, I₂)` partitions the cells on $\Theta$, with
`E.cell j₁ ∈ I₁` and `E.cell j₂ ∈ I₂`, then for any $n_1 \in \widetilde{E.\text{cell } j_1}$ and
$n_2 \in \widetilde{E.\text{cell } j_2}$ there exist indices $r_3, r_4$ such that both `E.node r₃`
and `E.node r₄` lie in $\tilde{c}_1' \cap \tilde{c}_2'$ for some border cells $c_1' \in I_1$,
$c_2' \in I_2$, and `cyclicDist a₁ r₃ + cyclicDist r₃ a₂ + cyclicDist a₂ r₄ ≤ k` where
`E.node a₁ = n₁` and `E.node a₂ = n₂`.
Graph Minors XVII, proof of (2.1), Claim (3) (page 167). -/
theorem Painting.CuffEnumeration.exists_boundary_nodes_of_partition
    {S : Type} [TopologicalSpace S] {Γ : Painting S} {Θ : Set S} {k : ℕ}
    (E : Γ.CuffEnumeration Θ k) {I₁ I₂ : Set (Set S)}
    (hcov : ∀ i : Fin k, E.cell i ∈ I₁ ∨ E.cell i ∈ I₂)
    (hdisj : Disjoint I₁ I₂)
    {j₁ j₂ : Fin k} (hj₁ : E.cell j₁ ∈ I₁) (hj₂ : E.cell j₂ ∈ I₂)
    {n₁ n₂ : S} (hn₁ : n₁ ∈ tilde (E.cell j₁)) (hn₂ : n₂ ∈ tilde (E.cell j₂)) :
    ∃ a₁ r₃ a₂ r₄ : Fin k,
      E.node a₁ = n₁ ∧ E.node a₂ = n₂ ∧
      (∃ i₁ i₂ : Fin k, E.cell i₁ ∈ I₁ ∧ E.cell i₂ ∈ I₂ ∧
        E.node r₃ ∈ tilde (E.cell i₁) ∩ tilde (E.cell i₂)) ∧
      (∃ i₁ i₂ : Fin k, E.cell i₁ ∈ I₁ ∧ E.cell i₂ ∈ I₂ ∧
        E.node r₄ ∈ tilde (E.cell i₁) ∩ tilde (E.cell i₂)) ∧
      cyclicDist a₁ r₃ + cyclicDist r₃ a₂ + cyclicDist a₂ r₄ ≤ k := by
  have hk : 2 ≤ k := E.two_le
  have hk_pos : 0 < k := by omega
  have hj_ne : j₁ ≠ j₂ := fun h => Set.disjoint_left.mp hdisj hj₁ (h ▸ hj₂)
  set d₁₂ := cyclicDist j₁ j₂
  set d₂₁ := cyclicDist j₂ j₁
  have hd₁₂_pos : 0 < d₁₂ := cyclicDist_pos_of_ne hj_ne
  have hd₂₁_pos : 0 < d₂₁ := cyclicDist_pos_of_ne hj_ne.symm
  have hd_sum : d₁₂ + d₂₁ = k := by
    have h1 := cyclicDist_eq_ite j₁ j₂
    have h2 := cyclicDist_eq_ite j₂ j₁
    have := j₁.2; have := j₂.2
    split_ifs at h1 h2 <;> omega
  -- Step 1: find transition along forward arc from j₁ to j₂
  have hex₁ : ∃ t : ℕ, t < d₁₂ ∧
      E.cell ⟨(j₁.1 + t) % k, Nat.mod_lt _ hk_pos⟩ ∈ I₁ ∧
      E.cell ⟨(j₁.1 + (t + 1)) % k, Nat.mod_lt _ hk_pos⟩ ∈ I₂ := by
    by_contra hno
    push Not at hno
    have hall : ∀ t ≤ d₁₂, E.cell ⟨(j₁.1 + t) % k, Nat.mod_lt _ hk_pos⟩ ∈ I₁ := by
      intro t ht
      induction t with
      | zero =>
        have h0 : (⟨(j₁.1 + 0) % k, Nat.mod_lt _ hk_pos⟩ : Fin k) = j₁ := by
          apply Fin.ext; dsimp; exact Nat.mod_eq_of_lt j₁.2
        rw [h0]; exact hj₁
      | succ t ih =>
        have ht_lt : t < d₁₂ := by omega
        have hit := ih (by omega)
        rcases hcov ⟨(j₁.1 + (t + 1)) % k, Nat.mod_lt _ hk_pos⟩ with h1 | h2
        · exact h1
        · exact False.elim (hno t ht_lt hit h2)
    have hend := hall d₁₂ le_rfl
    have h_idx : (⟨(j₁.1 + d₁₂) % k, Nat.mod_lt _ hk_pos⟩ : Fin k) = j₂ := by
      apply Fin.ext; dsimp [d₁₂]
      have h1 := cyclicDist_eq_ite j₁ j₂
      have := j₁.2; have := j₂.2
      split_ifs at h1 with hle
      · rw [h1]
        have heq : j₁.1 + (j₂.1 - j₁.1) = j₂.1 := by omega
        rw [heq, Nat.mod_eq_of_lt j₂.2]
      · rw [h1]
        have heq : j₁.1 + (j₂.1 + k - j₁.1) = j₂.1 + k := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt j₂.2]
    rw [h_idx] at hend
    exact Set.disjoint_left.mp hdisj hend hj₂
  rcases hex₁ with ⟨t₁, ht₁_lt, ht₁_I₁, ht₁_I₂⟩
  -- Step 2: find transition along forward arc from j₂ to j₁
  have hex₂ : ∃ t : ℕ, t < d₂₁ ∧
      E.cell ⟨(j₂.1 + t) % k, Nat.mod_lt _ hk_pos⟩ ∈ I₂ ∧
      E.cell ⟨(j₂.1 + (t + 1)) % k, Nat.mod_lt _ hk_pos⟩ ∈ I₁ := by
    by_contra hno
    push Not at hno
    have hall : ∀ t ≤ d₂₁, E.cell ⟨(j₂.1 + t) % k, Nat.mod_lt _ hk_pos⟩ ∈ I₂ := by
      intro t ht
      induction t with
      | zero =>
        have h0 : (⟨(j₂.1 + 0) % k, Nat.mod_lt _ hk_pos⟩ : Fin k) = j₂ := by
          apply Fin.ext; dsimp; exact Nat.mod_eq_of_lt j₂.2
        rw [h0]; exact hj₂
      | succ t ih =>
        have ht_lt : t < d₂₁ := by omega
        have hit := ih (by omega)
        rcases hcov ⟨(j₂.1 + (t + 1)) % k, Nat.mod_lt _ hk_pos⟩ with h1 | h2
        · exact False.elim (hno t ht_lt hit h1)
        · exact h2
    have hend := hall d₂₁ le_rfl
    have h_idx : (⟨(j₂.1 + d₂₁) % k, Nat.mod_lt _ hk_pos⟩ : Fin k) = j₁ := by
      apply Fin.ext; dsimp [d₂₁]
      have h1 := cyclicDist_eq_ite j₂ j₁
      have := j₁.2; have := j₂.2
      split_ifs at h1 with hle
      · rw [h1]
        have heq : j₂.1 + (j₁.1 - j₂.1) = j₁.1 := by omega
        rw [heq, Nat.mod_eq_of_lt j₁.2]
      · rw [h1]
        have heq : j₂.1 + (j₁.1 + k - j₂.1) = j₁.1 + k := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt j₁.2]
    rw [h_idx] at hend
    exact Set.disjoint_left.mp hdisj hj₁ hend
  rcases hex₂ with ⟨t₂, ht₂_lt, ht₂_I₂, ht₂_I₁⟩
  let u₁ : Fin k := ⟨(j₁.1 + t₁) % k, Nat.mod_lt _ hk_pos⟩
  let r₃ : Fin k := ⟨(j₁.1 + (t₁ + 1)) % k, Nat.mod_lt _ hk_pos⟩
  let u₂ : Fin k := ⟨(j₂.1 + t₂) % k, Nat.mod_lt _ hk_pos⟩
  let r₄ : Fin k := ⟨(j₂.1 + (t₂ + 1)) % k, Nat.mod_lt _ hk_pos⟩
  have hr₃_u₁ : r₃ = ⟨(u₁.1 + 1) % k, Nat.mod_lt _ hk_pos⟩ := by
    apply Fin.ext; dsimp [r₃, u₁]
    simp only [← Nat.add_assoc, Nat.mod_add_mod]
  have hr₄_u₂ : r₄ = ⟨(u₂.1 + 1) % k, Nat.mod_lt _ hk_pos⟩ := by
    apply Fin.ext; dsimp [r₄, u₂]
    simp only [← Nat.add_assoc, Nat.mod_add_mod]
  have hr₃_tilde : E.node r₃ ∈ tilde (E.cell u₁) ∩ tilde (E.cell r₃) := by
    refine ⟨?_, ?_⟩
    · rw [E.cell_tilde u₁, hr₃_u₁]; exact mem_insert_of_mem _ rfl
    · rw [E.cell_tilde r₃]; exact mem_insert _ _
  have hr₄_tilde : E.node r₄ ∈ tilde (E.cell r₄) ∩ tilde (E.cell u₂) := by
    refine ⟨?_, ?_⟩
    · rw [E.cell_tilde r₄]; exact mem_insert _ _
    · rw [E.cell_tilde u₂, hr₄_u₂]; exact mem_insert_of_mem _ rfl
  -- Step 3: identify a₁ and a₂
  rw [E.cell_tilde j₁] at hn₁
  rw [E.cell_tilde j₂] at hn₂
  have ha₁_ex : ∃ s₁ ≤ 1, ∃ a₁ : Fin k,
      a₁ = ⟨(j₁.1 + s₁) % k, Nat.mod_lt _ hk_pos⟩ ∧ E.node a₁ = n₁ := by
    rcases hn₁ with rfl | rfl
    · refine ⟨0, by omega, j₁, ?_, rfl⟩
      apply Fin.ext; dsimp; exact (Nat.mod_eq_of_lt j₁.2).symm
    · exact ⟨1, le_rfl, ⟨(j₁.1 + 1) % k, Nat.mod_lt _ hk_pos⟩, rfl, rfl⟩
  have ha₂_ex : ∃ s₂ ≤ 1, ∃ a₂ : Fin k,
      a₂ = ⟨(j₂.1 + s₂) % k, Nat.mod_lt _ hk_pos⟩ ∧ E.node a₂ = n₂ := by
    rcases hn₂ with rfl | rfl
    · refine ⟨0, by omega, j₂, ?_, rfl⟩
      apply Fin.ext; dsimp; exact (Nat.mod_eq_of_lt j₂.2).symm
    · exact ⟨1, le_rfl, ⟨(j₂.1 + 1) % k, Nat.mod_lt _ hk_pos⟩, rfl, rfl⟩
  rcases ha₁_ex with ⟨s₁, hs₁_le, a₁, ha₁_eq, ha₁_node⟩
  rcases ha₂_ex with ⟨s₂, hs₂_le, a₂, ha₂_eq, ha₂_node⟩
  refine ⟨a₁, r₃, a₂, r₄, ha₁_node, ha₂_node,
    ⟨u₁, r₃, ht₁_I₁, ht₁_I₂, hr₃_tilde⟩,
    ⟨r₄, u₂, ht₂_I₁, ht₂_I₂, hr₄_tilde⟩, ?_⟩
  -- Step 4: bound cyclicDist a₁ r₃ + cyclicDist r₃ a₂ + cyclicDist a₂ r₄ ≤ k
  have hd₁₂_lt : d₁₂ < k := cyclicDist_lt hk_pos j₁ j₂
  have hd₂₁_lt : d₂₁ < k := cyclicDist_lt hk_pos j₂ j₁
  have hdist1 : cyclicDist a₁ r₃ = (t₁ + 1) - s₁ := by
    rw [ha₁_eq]
    exact cyclicDist_shift hk_pos j₁ (by omega) (by omega)
  have hdist3 : cyclicDist a₂ r₄ = (t₂ + 1) - s₂ := by
    rw [ha₂_eq]
    exact cyclicDist_shift hk_pos j₂ (by omega) (by omega)
  have ha₂_from_j₁ : a₂ = ⟨(j₁.1 + (d₁₂ + s₂)) % k, Nat.mod_lt _ hk_pos⟩ := by
    rw [ha₂_eq]
    apply Fin.ext; dsimp
    have hj₂_eq : j₂.1 = (j₁.1 + d₁₂) % k := by
      dsimp [d₁₂]
      have h1 := cyclicDist_eq_ite j₁ j₂
      have := j₁.2; have := j₂.2
      split_ifs at h1 with hle
      · rw [h1]
        have heq : j₁.1 + (j₂.1 - j₁.1) = j₂.1 := by omega
        rw [heq, Nat.mod_eq_of_lt j₂.2]
      · rw [h1]
        have heq : j₁.1 + (j₂.1 + k - j₁.1) = j₂.1 + k := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt j₂.2]
    rw [hj₂_eq, Nat.mod_add_mod, Nat.add_assoc]
  have hdist2 : cyclicDist r₃ a₂ = (d₁₂ + s₂) - (t₁ + 1) := by
    rw [ha₂_from_j₁]
    exact cyclicDist_shift hk_pos j₁ (by omega) (by omega)
  rw [hdist1, hdist2, hdist3]
  omega

/-! ## 3. Theorem (2.1) (Pages 166–168) -/

section Theorem21

variable {α : Type u} {β : Type v} {G : Hypergraph α β} (π : Portrayal G)

/-- Graph Minors XVII, (2.1), Claim (1) (page 167):
$\gamma(X_1 \cap X_2) \subseteq V(A_1 \cap A_2)$. -/
theorem theorem_2_1_claim_1 {I₁ I₂ : Set (Set π.S)}
    (hI₁ : I₁ ⊆ π.Γ.C) (hI₂ : I₂ ⊆ π.Γ.C) :
    π.gammaImage ((⋃ c ∈ I₁, tilde c) ∩ (⋃ c ∈ I₂, tilde c)) ⊆
      (π.cellsUnion I₁ ∩ π.cellsUnion I₂).vertexSet := by
  rintro v ⟨n, ⟨⟨hX₁, hX₂⟩, hdom⟩, rfl⟩
  rw [mem_iUnion₂] at hX₁ hX₂
  rcases hX₁ with ⟨c₁, hc₁I₁, hnc₁⟩
  rcases hX₂ with ⟨c₂, hc₂I₂, hnc₂⟩
  refine ⟨?_, ?_⟩
  · exact mem_iUnion₂.mpr ⟨c₁, ⟨hc₁I₁, hI₁ hc₁I₁⟩, π.p2 c₁ (hI₁ hc₁I₁) n ⟨hnc₁, hdom⟩⟩
  · exact mem_iUnion₂.mpr ⟨c₂, ⟨hc₂I₂, hI₂ hc₂I₂⟩, π.p2 c₂ (hI₂ hc₂I₂) n ⟨hnc₂, hdom⟩⟩

/-- Graph Minors XVII, (2.1), Claim (2) (page 167):
$\bigcup (\beta(n) : n \in Y_1 \cap Y_2) \subseteq V(A_1 \cap A_2)$. -/
theorem theorem_2_1_claim_2 {I₁ I₂ : Set (Set π.S)}
    (hI₁ : I₁ ⊆ π.Γ.C) (hI₂ : I₂ ⊆ π.Γ.C) :
    (⋃ n ∈ (⋃ c ∈ {c ∈ I₁ | (c ∩ bd π.S).Nonempty}, tilde c) ∩
            (⋃ c ∈ {c ∈ I₂ | (c ∩ bd π.S).Nonempty}, tilde c), π.borderSet n) ⊆
      (π.cellsUnion I₁ ∩ π.cellsUnion I₂).vertexSet := by
  intro v hv
  rw [mem_iUnion₂] at hv
  rcases hv with ⟨n, ⟨hY₁, hY₂⟩, hvn⟩
  rw [mem_iUnion₂] at hY₁ hY₂
  rcases hY₁ with ⟨c₁, ⟨hc₁I₁, hc₁bd⟩, hnc₁⟩
  rcases hY₂ with ⟨c₂, ⟨hc₂I₂, hc₂bd⟩, hnc₂⟩
  refine ⟨?_, ?_⟩
  · exact mem_iUnion₂.mpr ⟨c₁, ⟨hc₁I₁, hI₁ hc₁I₁⟩,
      π.p3_subset c₁ (hI₁ hc₁I₁) hc₁bd n hnc₁ hvn⟩
  · exact mem_iUnion₂.mpr ⟨c₂, ⟨hc₂I₂, hI₂ hc₂I₂⟩,
      π.p3_subset c₂ (hI₂ hc₂I₂) hc₂bd n hnc₂ hvn⟩

/-- Helper for (2.1) Claim (3) when both $c_1 \in I_1$ and $c_2 \in I_2$ border the same cuff
$\Theta$, with $v \in \beta(n_1) \cap V(\alpha(c_2))$. -/
private theorem theorem_2_1_claim_3_same_cuff
    {I₁ I₂ : Set (Set π.S)} (hcov : I₁ ∪ I₂ = π.Γ.C) (hdisj : Disjoint I₁ I₂)
    {c₁ c₂ Θ : Set π.S} (hc₁I₁ : c₁ ∈ I₁) (hc₂I₂ : c₂ ∈ I₂)
    (hΘ : Θ ∈ cuffs π.S) (hc₁Θ : (c₁ ∩ Θ).Nonempty) (hc₂Θ : (c₂ ∩ Θ).Nonempty)
    {n₁ : π.S} (hn₁ : n₁ ∈ tilde c₁) {v : α}
    (hvn₁ : v ∈ π.borderSet n₁) (hvc₂ : v ∈ (π.cellGraph c₂).vertexSet) :
    v ∈ π.gammaImage ((⋃ c ∈ I₁, tilde c) ∩ (⋃ c ∈ I₂, tilde c)) ∪
      (⋃ n ∈ (⋃ c ∈ {c ∈ I₁ | (c ∩ bd π.S).Nonempty}, tilde c) ∩
              (⋃ c ∈ {c ∈ I₂ | (c ∩ bd π.S).Nonempty}, tilde c), π.borderSet n) := by
  have hc₁C : c₁ ∈ π.Γ.C := hcov ▸ Or.inl hc₁I₁
  have hc₂C : c₂ ∈ π.Γ.C := hcov ▸ Or.inr hc₂I₂
  have hne : c₁ ≠ c₂ := fun h => Set.disjoint_left.mp hdisj hc₁I₁ (h ▸ hc₂I₂)
  have hc₁bd : (c₁ ∩ bd π.S).Nonempty := by
    rw [(π.Γ.border_cell_subset_cuff hc₁C hΘ hc₁Θ).2.1]; exact hc₁Θ
  have hc₂bd : (c₂ ∩ bd π.S).Nonempty := by
    rw [(π.Γ.border_cell_subset_cuff hc₂C hΘ hc₂Θ).2.1]; exact hc₂Θ
  have hvo₂ : v ∈ π.otherVertices c₂ :=
    ⟨c₁, hc₁C, hne, π.p3_subset c₁ hc₁C hc₁bd n₁ hn₁ hvn₁⟩
  obtain ⟨n₂, hn₂, hvn₂⟩ := π.p6_borderPlus hc₂C hc₂bd hvc₂ hvo₂
  have hΘ_arc : IsOArc Θ := (GraphMinor.Surface.cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
  obtain ⟨E⟩ := π.Γ.exists_cuffEnumeration hΘ hΘ_arc
  have hc₁_range : c₁ ∈ Set.range E.cell := by rw [E.range_cell]; exact ⟨hc₁C, hc₁Θ⟩
  have hc₂_range : c₂ ∈ Set.range E.cell := by rw [E.range_cell]; exact ⟨hc₂C, hc₂Θ⟩
  rcases hc₁_range with ⟨j₁, rfl⟩
  rcases hc₂_range with ⟨j₂, rfl⟩
  have hcov_E : ∀ i : Fin (π.Γ.N ∩ Θ).ncard, E.cell i ∈ I₁ ∨ E.cell i ∈ I₂ := by
    intro i
    have hiC : E.cell i ∈ π.Γ.C := by
      have : E.cell i ∈ Set.range E.cell := mem_range_self i
      rw [E.range_cell] at this
      exact this.1
    rwa [← hcov] at hiC
  obtain ⟨a₁, r₃, a₂, r₄, ha₁, ha₂, hr₃_mem, hr₄_mem, hdist⟩ :=
    E.exists_boundary_nodes_of_partition hcov_E hdisj hc₁I₁ hc₂I₂ hn₁ hn₂
  have hva₁ : v ∈ π.borderPlus (E.node a₁) := by
    rw [ha₁]; exact Or.inl hvn₁
  have hva₂ : v ∈ π.borderPlus (E.node a₂) := by
    rw [ha₂]; exact hvn₂
  have hv_or : v ∈ π.borderPlus (E.node r₃) ∨ v ∈ π.borderPlus (E.node r₄) :=
    π.p7_of_cyclicDist E hdist hva₁ hva₂
  have h_finish : ∀ r : Fin (π.Γ.N ∩ Θ).ncard,
      (∃ i₁ i₂ : Fin (π.Γ.N ∩ Θ).ncard, E.cell i₁ ∈ I₁ ∧ E.cell i₂ ∈ I₂ ∧
        E.node r ∈ tilde (E.cell i₁) ∩ tilde (E.cell i₂)) →
      v ∈ π.borderPlus (E.node r) →
      v ∈ π.gammaImage ((⋃ c ∈ I₁, tilde c) ∩ (⋃ c ∈ I₂, tilde c)) ∪
        (⋃ n ∈ (⋃ c ∈ {c ∈ I₁ | (c ∩ bd π.S).Nonempty}, tilde c) ∩
                (⋃ c ∈ {c ∈ I₂ | (c ∩ bd π.S).Nonempty}, tilde c), π.borderSet n) := by
    rintro r ⟨i₁, i₂, hi₁I₁, hi₂I₂, hnr₁, hnr₂⟩ hvr
    have hi₁_range : E.cell i₁ ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} := by
      rw [← E.range_cell]; exact mem_range_self i₁
    have hi₂_range : E.cell i₂ ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} := by
      rw [← E.range_cell]; exact mem_range_self i₂
    have hi₁_bd : (E.cell i₁ ∩ bd π.S).Nonempty := by
      rw [(π.Γ.border_cell_subset_cuff hi₁_range.1 hΘ hi₁_range.2).2.1]; exact hi₁_range.2
    have hi₂_bd : (E.cell i₂ ∩ bd π.S).Nonempty := by
      rw [(π.Γ.border_cell_subset_cuff hi₂_range.1 hΘ hi₂_range.2).2.1]; exact hi₂_range.2
    rcases hvr with hvr_b | ⟨hdom, rfl⟩
    · right
      refine mem_iUnion₂.mpr ⟨E.node r, ⟨?_, ?_⟩, hvr_b⟩
      · exact mem_iUnion₂.mpr ⟨E.cell i₁, ⟨hi₁I₁, hi₁_bd⟩, hnr₁⟩
      · exact mem_iUnion₂.mpr ⟨E.cell i₂, ⟨hi₂I₂, hi₂_bd⟩, hnr₂⟩
    · left
      refine ⟨E.node r, ⟨⟨?_, ?_⟩, hdom⟩, rfl⟩
      · exact mem_iUnion₂.mpr ⟨E.cell i₁, hi₁I₁, hnr₁⟩
      · exact mem_iUnion₂.mpr ⟨E.cell i₂, hi₂I₂, hnr₂⟩
  rcases hv_or with h3 | h4
  · exact h_finish r₃ hr₃_mem h3
  · exact h_finish r₄ hr₄_mem h4

/-- Helper for (2.1) Claim (3) when $c_1 \in I_1$ borders a cuff $\Theta$, $n_1 \in \tilde{c}_1$,
$v \in \beta(n_1)$, and $c_2 \in I_2$ satisfies $v \in V(\alpha(c_2))$. -/
private theorem theorem_2_1_claim_3_of_border
    {I₁ I₂ : Set (Set π.S)} (hcov : I₁ ∪ I₂ = π.Γ.C) (hdisj : Disjoint I₁ I₂)
    {c₁ c₂ : Set π.S} (hc₁I₁ : c₁ ∈ I₁) (hc₂I₂ : c₂ ∈ I₂)
    (hc₁bd : (c₁ ∩ bd π.S).Nonempty) {n₁ : π.S} (hn₁ : n₁ ∈ tilde c₁)
    {v : α} (hvn₁ : v ∈ π.borderSet n₁) (hvc₂ : v ∈ (π.cellGraph c₂).vertexSet) :
    v ∈ π.gammaImage ((⋃ c ∈ I₁, tilde c) ∩ (⋃ c ∈ I₂, tilde c)) ∪
      (⋃ n ∈ (⋃ c ∈ {c ∈ I₁ | (c ∩ bd π.S).Nonempty}, tilde c) ∩
              (⋃ c ∈ {c ∈ I₂ | (c ∩ bd π.S).Nonempty}, tilde c), π.borderSet n) := by
  have hc₁C : c₁ ∈ π.Γ.C := hcov ▸ Or.inl hc₁I₁
  have hc₂C : c₂ ∈ π.Γ.C := hcov ▸ Or.inr hc₂I₂
  have hne : c₁ ≠ c₂ := fun h => Set.disjoint_left.mp hdisj hc₁I₁ (h ▸ hc₂I₂)
  rcases hc₁bd with ⟨x, hxc₁, hxbd⟩
  let Θ := connectedComponentIn (bd π.S) x
  have hΘ : Θ ∈ cuffs π.S := ⟨x, hxbd, rfl⟩
  have hc₁Θ : (c₁ ∩ Θ).Nonempty := ⟨x, hxc₁, mem_connectedComponentIn hxbd⟩
  by_cases hc₂Θ : (c₂ ∩ Θ).Nonempty
  · exact theorem_2_1_claim_3_same_cuff π hcov hdisj hc₁I₁ hc₂I₂ hΘ hc₁Θ hc₂Θ hn₁ hvn₁ hvc₂
  · obtain ⟨_, n, ⟨hnc₂, hdom⟩, hnΘ, rfl⟩ :=
      π.exists_node_of_not_borders_cuff hc₁C hc₂C hne hΘ hc₁Θ hc₂Θ hn₁ hvn₁ hvc₂
    have hΘ_arc : IsOArc Θ := (GraphMinor.Surface.cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
    obtain ⟨E⟩ := π.Γ.exists_cuffEnumeration hΘ hΘ_arc
    have hn_range : n ∈ Set.range E.node := by
      rw [E.range_node]
      exact ⟨π.domγ_subset hdom, hnΘ⟩
    rcases hn_range with ⟨i, hi_eq⟩
    let c := E.cell i
    have hc_range : c ∈ {c' ∈ π.Γ.C | (c' ∩ Θ).Nonempty} := by
      rw [← E.range_cell]; exact mem_range_self i
    have hnc : n ∈ tilde c := by
      rw [E.cell_tilde i, ← hi_eq]
      exact mem_insert _ _
    have hvc : π.nodeVertex n ∈ (π.cellGraph c).vertexSet := π.p2 c hc_range.1 n ⟨hnc, hdom⟩
    have hc_mem : c ∈ I₁ ∪ I₂ := hcov.symm ▸ hc_range.1
    rcases hc_mem with hcI₁ | hcI₂
    · left
      refine ⟨n, ⟨⟨?_, ?_⟩, hdom⟩, rfl⟩
      · exact mem_iUnion₂.mpr ⟨c, hcI₁, hnc⟩
      · exact mem_iUnion₂.mpr ⟨c₂, hc₂I₂, hnc₂⟩
    · exact theorem_2_1_claim_3_same_cuff π hcov hdisj hc₁I₁ hcI₂
        hΘ hc₁Θ hc_range.2 hn₁ hvn₁ hvc

/-- Graph Minors XVII, (2.1), Claim (3) (pages 167–168):
$V(A_1 \cap A_2) \subseteq \gamma(X_1 \cap X_2) \cup \bigcup (\beta(n) : n \in Y_1 \cap Y_2)$. -/
theorem theorem_2_1_claim_3
    {I₁ I₂ : Set (Set π.S)} (hcov : I₁ ∪ I₂ = π.Γ.C) (hdisj : Disjoint I₁ I₂) :
    (π.cellsUnion I₁ ∩ π.cellsUnion I₂).vertexSet ⊆
      π.gammaImage ((⋃ c ∈ I₁, tilde c) ∩ (⋃ c ∈ I₂, tilde c)) ∪
        (⋃ n ∈ (⋃ c ∈ {c ∈ I₁ | (c ∩ bd π.S).Nonempty}, tilde c) ∩
                (⋃ c ∈ {c ∈ I₂ | (c ∩ bd π.S).Nonempty}, tilde c), π.borderSet n) := by
  rintro v ⟨hv₁, hv₂⟩
  rw [Portrayal.cellsUnion, mem_iUnion₂] at hv₁ hv₂
  rcases hv₁ with ⟨c₁, ⟨hc₁I₁, hc₁C⟩, hvc₁⟩
  rcases hv₂ with ⟨c₂, ⟨hc₂I₂, hc₂C⟩, hvc₂⟩
  have hne : c₁ ≠ c₂ := fun h => Set.disjoint_left.mp hdisj hc₁I₁ (h ▸ hc₂I₂)
  by_cases hγ₁ : v ∈ π.gammaImage (tilde c₁)
  · by_cases hγ₂ : v ∈ π.gammaImage (tilde c₂)
    · left
      have h_inter : v ∈ π.gammaImage (tilde c₁ ∩ tilde c₂) := by
        rw [π.gammaImage_inter]
        exact ⟨hγ₁, hγ₂⟩
      refine π.gammaImage_mono ?_ h_inter
      intro n ⟨hnc₁, hnc₂⟩
      exact ⟨mem_iUnion₂.mpr ⟨c₁, hc₁I₁, hnc₁⟩, mem_iUnion₂.mpr ⟨c₂, hc₂I₂, hnc₂⟩⟩
    · have hvo₂ : v ∈ π.otherVertices c₂ := ⟨c₁, hc₁C, hne, hvc₁⟩
      obtain ⟨hc₂bd, n₂, hn₂, hvn₂⟩ :=
        π.border_of_mem_otherVertices_notMem_gammaImage hc₂C hvc₂ hvo₂ hγ₂
      have hcov' : I₂ ∪ I₁ = π.Γ.C := by rw [Set.union_comm, hcov]
      have hsymm := theorem_2_1_claim_3_of_border π hcov' hdisj.symm hc₂I₂ hc₁I₁
        hc₂bd hn₂ hvn₂ hvc₁
      rw [Set.inter_comm (⋃ c ∈ I₂, tilde c),
          Set.inter_comm (⋃ c ∈ {c ∈ I₂ | (c ∩ bd π.S).Nonempty}, tilde c)] at hsymm
      exact hsymm
  · have hvo₁ : v ∈ π.otherVertices c₁ := ⟨c₂, hc₂C, hne.symm, hvc₂⟩
    obtain ⟨hc₁bd, n₁, hn₁, hvn₁⟩ :=
      π.border_of_mem_otherVertices_notMem_gammaImage hc₁C hvc₁ hvo₁ hγ₁
    exact theorem_2_1_claim_3_of_border π hcov hdisj hc₁I₁ hc₂I₂ hc₁bd hn₁ hvn₁ hvc₂

/-- **Graph Minors XVII, (2.1)** (page 166):
Given a portrayal $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ of $G$, let $(I_1, I_2)$ be a
partition of $C(\Gamma)$, and let $A_i = \bigcup (\alpha(c) : c \in I_i)$ for $i = 1, 2$. Then
$E(A_1 \cap A_2) = \emptyset$, and
$$V(A_1 \cap A_2) = \bigcup (\gamma(\tilde{c}_1) \cap \gamma(\tilde{c}_2) : c_1 \in I_1, c_2 \in
I_2)
  \cup \bigcup (\beta(n) : \exists \text{ border cells } c_1 \in I_1, c_2 \in I_2 \text{ with }
  n \in \tilde{c}_1 \cap \tilde{c}_2).$$ -/
theorem theorem_2_1_proof
    {I₁ I₂ : Set (Set π.S)} (hcov : I₁ ∪ I₂ = π.Γ.C) (hdisj : Disjoint I₁ I₂) :
    (π.cellsUnion I₁ ∩ π.cellsUnion I₂).edgeSet = ∅ ∧
    (π.cellsUnion I₁ ∩ π.cellsUnion I₂).vertexSet =
      (⋃ c₁ ∈ I₁, ⋃ c₂ ∈ I₂, π.gammaImage (tilde c₁) ∩ π.gammaImage (tilde c₂)) ∪
      (⋃ n ∈ {n : π.S | ∃ c₁ ∈ I₁, (c₁ ∩ bd π.S).Nonempty ∧
        ∃ c₂ ∈ I₂, (c₂ ∩ bd π.S).Nonempty ∧ n ∈ tilde c₁ ∩ tilde c₂}, π.borderSet n) := by
  have hI₁ : I₁ ⊆ π.Γ.C := hcov ▸ subset_union_left
  have hI₂ : I₂ ⊆ π.Γ.C := hcov ▸ subset_union_right
  refine ⟨?_, ?_⟩
  · ext e
    simp only [inter_edgeSet, Portrayal.cellsUnion, mem_inter_iff, mem_iUnion,
      mem_empty_iff_false, iff_false, not_and]
    rintro ⟨c₁, ⟨hc₁I₁, hc₁C⟩, he₁⟩ ⟨c₂, ⟨hc₂I₂, hc₂C⟩, he₂⟩
    have hne : c₁ ≠ c₂ := fun h => Set.disjoint_left.mp hdisj hc₁I₁ (h ▸ hc₂I₂)
    exact Set.disjoint_left.mp (π.p1_disjoint c₁ hc₁C c₂ hc₂C hne) he₁ he₂
  · have h_eq_X : π.gammaImage ((⋃ c ∈ I₁, tilde c) ∩ (⋃ c ∈ I₂, tilde c)) =
        ⋃ c₁ ∈ I₁, ⋃ c₂ ∈ I₂, π.gammaImage (tilde c₁) ∩ π.gammaImage (tilde c₂) := by
      ext v
      simp only [← π.gammaImage_inter, Portrayal.mem_gammaImage_iff, mem_iUnion]
      constructor
      · rintro ⟨n, ⟨⟨hX₁, hX₂⟩, hdom⟩, rfl⟩
        rw [mem_iUnion₂] at hX₁ hX₂
        rcases hX₁ with ⟨c₁, hc₁, hnc₁⟩
        rcases hX₂ with ⟨c₂, hc₂, hnc₂⟩
        exact ⟨c₁, hc₁, c₂, hc₂, n, ⟨⟨hnc₁, hnc₂⟩, hdom⟩, rfl⟩
      · rintro ⟨c₁, hc₁, c₂, hc₂, n, ⟨⟨hnc₁, hnc₂⟩, hdom⟩, rfl⟩
        exact ⟨n, ⟨⟨mem_iUnion₂.mpr ⟨c₁, hc₁, hnc₁⟩, mem_iUnion₂.mpr ⟨c₂, hc₂, hnc₂⟩⟩, hdom⟩, rfl⟩
    have h_eq_Y : (⋃ n ∈ (⋃ c ∈ {c ∈ I₁ | (c ∩ bd π.S).Nonempty}, tilde c) ∩
            (⋃ c ∈ {c ∈ I₂ | (c ∩ bd π.S).Nonempty}, tilde c), π.borderSet n) =
        ⋃ n ∈ {n : π.S | ∃ c₁ ∈ I₁, (c₁ ∩ bd π.S).Nonempty ∧
          ∃ c₂ ∈ I₂, (c₂ ∩ bd π.S).Nonempty ∧ n ∈ tilde c₁ ∩ tilde c₂}, π.borderSet n := by
      ext v
      simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
      tauto
    rw [← h_eq_X, ← h_eq_Y]
    exact Subset.antisymm (theorem_2_1_claim_3 π hcov hdisj)
      (union_subset (theorem_2_1_claim_1 π hI₁ hI₂) (theorem_2_1_claim_2 π hI₁ hI₂))

/-- For any partition $(I_1, I_2)$ of $C(\Gamma)$, $(\bigcup_{c \in I_1} \alpha(c),
\bigcup_{c \in I_2} \alpha(c))$ is a separation of $G$. -/
theorem Portrayal.isSeparation_cellsUnion {I₁ I₂ : Set (Set π.S)}
    (hcov : I₁ ∪ I₂ = π.Γ.C) (hdisj : Disjoint I₁ I₂) :
    G.IsSeparation (π.cellsUnion I₁) (π.cellsUnion I₂) where
  left_le := π.cellsUnion_le I₁
  right_le := π.cellsUnion_le I₂
  union_eq := by
    rw [← π.cellsUnion_union, hcov, π.cellsUnion_C]
  edgeSet_inter_eq := by
    ext e
    simp only [inter_edgeSet, Portrayal.cellsUnion, mem_inter_iff, mem_iUnion,
      mem_empty_iff_false, iff_false, not_and]
    rintro ⟨c₁, ⟨hc₁I₁, hc₁C⟩, he₁⟩ ⟨c₂, ⟨hc₂I₂, hc₂C⟩, he₂⟩
    have hne : c₁ ≠ c₂ := fun h => Set.disjoint_left.mp hdisj hc₁I₁ (h ▸ hc₂I₂)
    exact Set.disjoint_left.mp (π.p1_disjoint c₁ hc₁C c₂ hc₂C hne) he₁ he₂

end Theorem21

/-! ## 4. Properties of Warp (Section 3, Page 169) -/

namespace Portrayal

variable {α : Type u} {β : Type v} {G : Hypergraph α β} (π : Portrayal G)

theorem cellWarpLE_mono {c : Set π.S} (hc : c ∈ π.Γ.C) (hbd : (c ∩ bd π.S).Nonempty)
    {p q : ℕ} (hp : π.CellWarpLE c p) (hpq : p ≤ q) :
    π.CellWarpLE c q := by
  rcases eq_or_lt_of_le hpq with rfl | hlt
  · exact hp
  · intro n₁ hn₁ n₂ hn₂ hne
    obtain ⟨h1, h2, _⟩ := hp n₁ hn₁ n₂ hn₂ hne
    refine ⟨h1.trans hpq, h2.trans hpq, fun hplus₁ _ => ?_⟩
    obtain ⟨u, v, _, htilde, _, _, hu, hv⟩ := π.Γ.border_cell_exists_ends hc hbd
    have hn₁_mem : n₁ ∈ π.Γ.N ∩ bd π.S := by
      rw [htilde] at hn₁
      rcases hn₁ with rfl | rfl
      · exact hu
      · exact hv
    have hle := π.ncard_borderPlus_le hn₁_mem
    omega

theorem cellWarpLE_ncard_vertexSet {c : Set π.S} (hc : c ∈ π.Γ.C) (hbd : (c ∩ bd π.S).Nonempty) :
    π.CellWarpLE c G.vertexSet.ncard := by
  intro n₁ hn₁ n₂ hn₂ _
  obtain ⟨u, v, _, htilde, _, _, hu, hv⟩ := π.Γ.border_cell_exists_ends hc hbd
  have hn₁_mem : n₁ ∈ π.Γ.N ∩ bd π.S := by
    rw [htilde] at hn₁; rcases hn₁ with rfl | rfl <;> assumption
  have hn₂_mem : n₂ ∈ π.Γ.N ∩ bd π.S := by
    rw [htilde] at hn₂; rcases hn₂ with rfl | rfl <;> assumption
  have h1 : (π.borderSet n₁).ncard ≤ G.vertexSet.ncard :=
    ncard_le_ncard (π.borderSet_subset n₁ hn₁_mem) G.vertexSet_finite
  have h2 : (π.borderSet n₂).ncard ≤ G.vertexSet.ncard :=
    ncard_le_ncard (π.borderSet_subset n₂ hn₂_mem) G.vertexSet_finite
  refine ⟨h1, h2, fun hplus₁ _ => ?_⟩
  have hle : (π.borderPlus n₁).ncard ≤ G.vertexSet.ncard :=
    ncard_le_ncard (π.borderPlus_subset_vertexSet hn₁_mem) G.vertexSet_finite
  omega

theorem cellWarp_spec {c : Set π.S} (hc : c ∈ π.Γ.C) (hbd : (c ∩ bd π.S).Nonempty) :
    π.CellWarpLE c (π.cellWarp c) := by
  have hne : {p | π.CellWarpLE c p}.Nonempty :=
    ⟨G.vertexSet.ncard, π.cellWarpLE_ncard_vertexSet hc hbd⟩
  exact Nat.sInf_mem hne

theorem cellWarp_le_iff {c : Set π.S} (hc : c ∈ π.Γ.C) (hbd : (c ∩ bd π.S).Nonempty) {p : ℕ} :
    π.cellWarp c ≤ p ↔ π.CellWarpLE c p :=
  ⟨fun h => π.cellWarpLE_mono hc hbd (π.cellWarp_spec hc hbd) h,
   fun h => Nat.sInf_le h⟩

theorem ncard_borderSet_le_cellWarp {c : Set π.S} (hc : c ∈ π.Γ.C) (hbd : (c ∩ bd π.S).Nonempty)
    {n : π.S} (hn : n ∈ tilde c) :
    (π.borderSet n).ncard ≤ π.cellWarp c := by
  obtain ⟨u, v, huv, htilde, _, _, _, _⟩ := π.Γ.border_cell_exists_ends hc hbd
  have hu : u ∈ tilde c := htilde ▸ mem_insert u {v}
  have hv : v ∈ tilde c := htilde ▸ mem_insert_of_mem u rfl
  have hspec := π.cellWarp_spec hc hbd u hu v hv huv
  rw [htilde] at hn
  rcases hn with rfl | rfl
  · exact hspec.1
  · exact hspec.2.1

theorem bddAbove_warpAt_set (Θ : Set π.S) :
    BddAbove {p | ∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ p = π.cellWarp c} := by
  have hfin : {p | ∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ p = π.cellWarp c}.Finite := by
    refine (π.Γ.finite_cells.image π.cellWarp).subset ?_
    rintro p ⟨c, hc, _, rfl⟩
    exact ⟨c, hc, rfl⟩
  exact hfin.bddAbove

theorem cellWarp_le_warpAt {c Θ : Set π.S} (hc : c ∈ π.Γ.C) (hcΘ : (c ∩ Θ).Nonempty) :
    π.cellWarp c ≤ π.warpAt Θ :=
  le_csSup (π.bddAbove_warpAt_set Θ) ⟨c, hc, hcΘ, rfl⟩

theorem warpAt_le_iff {Θ : Set π.S} {q : ℕ} :
    π.warpAt Θ ≤ q ↔ ∀ c ∈ π.Γ.C, (c ∩ Θ).Nonempty → π.cellWarp c ≤ q := by
  unfold warpAt
  constructor
  · intro h c hc hcΘ
    exact (le_csSup (π.bddAbove_warpAt_set Θ) ⟨c, hc, hcΘ, rfl⟩).trans h
  · intro h
    by_cases hne : {p | ∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ p = π.cellWarp c}.Nonempty
    · refine csSup_le hne ?_
      rintro p ⟨c, hc, hcΘ, rfl⟩
      exact h c hc hcΘ
    · rw [not_nonempty_iff_eq_empty.mp hne, csSup_empty]
      exact Nat.zero_le q

theorem exists_cell_cellWarp_eq_warpAt {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (hΘ_arc : IsOArc Θ) :
    ∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ π.cellWarp c = π.warpAt Θ := by
  obtain ⟨E⟩ := π.Γ.exists_cuffEnumeration hΘ hΘ_arc
  have hc0 : E.cell ⟨0, by linarith [E.two_le]⟩ ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} := by
    rw [← E.range_cell]; exact mem_range_self _
  have hne : {p | ∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ p = π.cellWarp c}.Nonempty :=
    ⟨_, E.cell ⟨0, by linarith [E.two_le]⟩, hc0.1, hc0.2, rfl⟩
  have hmem := Nat.sSup_mem hne (π.bddAbove_warpAt_set Θ)
  rcases hmem with ⟨c, hc, hcΘ, h_eq⟩
  exact ⟨c, hc, hcΘ, h_eq.symm⟩

theorem ncard_borderSet_le_warpAt {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (hΘ_arc : IsOArc Θ)
    {n : π.S} (hn : n ∈ π.Γ.N ∩ Θ) :
    (π.borderSet n).ncard ≤ π.warpAt Θ := by
  obtain ⟨E⟩ := π.Γ.exists_cuffEnumeration hΘ hΘ_arc
  have hn_range : n ∈ Set.range E.node := by rw [E.range_node]; exact hn
  rcases hn_range with ⟨i, rfl⟩
  have hc_range : E.cell i ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} := by
    rw [← E.range_cell]; exact mem_range_self i
  have hbd : (E.cell i ∩ bd π.S).Nonempty := by
    rw [(π.Γ.border_cell_subset_cuff hc_range.1 hΘ hc_range.2).2.1]; exact hc_range.2
  have hni : E.node i ∈ tilde (E.cell i) := by
    rw [E.cell_tilde i]; exact mem_insert _ _
  exact (π.ncard_borderSet_le_cellWarp hc_range.1 hbd hni).trans
    (π.cellWarp_le_warpAt hc_range.1 hc_range.2)

theorem bddAbove_warp_set :
    BddAbove {p | ∃ Θ ∈ cuffs π.S, p = π.warpAt Θ} := by
  have hfin : {p | ∃ Θ ∈ cuffs π.S, p = π.warpAt Θ}.Finite := by
    refine ((GraphMinor.Surface.cuff_statement.{0} π.S π.isSurface).2.1.image π.warpAt).subset ?_
    rintro p ⟨Θ, hΘ, rfl⟩
    exact ⟨Θ, hΘ, rfl⟩
  exact hfin.bddAbove

theorem one_le_warp : 1 ≤ π.warp := by
  unfold warp
  split_ifs
  · exact le_max_left 1 _
  · exact le_rfl

theorem warpAt_le_warp {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S) :
    π.warpAt Θ ≤ π.warp := by
  have hne : (cuffs π.S).Nonempty := ⟨Θ, hΘ⟩
  unfold warp
  simp only [hne, ↓reduceIte]
  exact (le_csSup (π.bddAbove_warp_set) ⟨Θ, hΘ, rfl⟩).trans (le_max_right _ _)

theorem ncard_borderSet_le_warp
    {n : π.S} (hn : n ∈ π.Γ.N ∩ bd π.S) :
    (π.borderSet n).ncard ≤ π.warp := by
  let Θ := connectedComponentIn (bd π.S) n
  have hΘ : Θ ∈ cuffs π.S := ⟨n, hn.2, rfl⟩
  have hΘ_arc : IsOArc Θ := (GraphMinor.Surface.cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
  have hnΘ : n ∈ π.Γ.N ∩ Θ := ⟨hn.1, mem_connectedComponentIn hn.2⟩
  exact (π.ncard_borderSet_le_warpAt hΘ hΘ_arc hnΘ).trans (π.warpAt_le_warp hΘ)

end Portrayal

end GraphMinor.GM17
