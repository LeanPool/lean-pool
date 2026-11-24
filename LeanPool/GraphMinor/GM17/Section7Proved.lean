/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section7
import LeanPool.GraphMinor.GM17.Section5Proved
import LeanPool.GraphMinor.GM17.Section6Proved

public import LeanPool.GraphMinor.GM17.Section6
public import LeanPool.GraphMinor.Surface.DiscsInSurface

import LeanPool.GraphMinor.Surface.Cuffs

import LeanPool.GraphMinor.GM17.ArcDisc

import LeanPool.GraphMinor.GM17.MarkCross

import LeanPool.GraphMinor.GM17.PasteCuff

import LeanPool.GraphMinor.GM17.ReplaceDisc

/-!
# Graph Minors XVII: proved deductions of Section7

The portrayal deductions use the existing painting proofs. The definitions and
independent geometric lemmas are imported from `Section7`.
-/

public section

namespace GraphMinor.GM17

open Set Function Topology Metric
open GraphMinor.Surface
open GraphMinor.GM10
open GraphMinor.Hypergraph

universe u v

/-! ## 1. Discs and Normal Boundaries in Paintings -/

section DiscNormalLemmas

variable {S : Type} [TopologicalSpace S]

end DiscNormalLemmas

/-! ## 2. Removing a Disc with $\le 1$ Boundary Node: (7.1) (Page 178) -/

section Theorem71

variable {S : Type} [TopologicalSpace S]

end Theorem71

/-! ## 3. Replacing a Normal Disc with at Most Three Boundary Nodes ((7.2), Page 178) -/

section Theorem72

variable {S : Type} [TopologicalSpace S]

end Theorem72

/-! ## 4. Normal $1$-Arc Disc Replacement ((7.3) and (7.4), Pages 178–181) -/

section Theorem73And74

/-- If a map $f \colon \operatorname{Fin} k \to \alpha$ is injective and takes values in a finite
set $X$ with $X.\text{ncard} = k$, then every element of $X$ is in the range of $f$. -/
private lemma mem_range_of_injective_of_ncard_eq {α : Type u} {k : ℕ}
    {X : Set α} (hfin : X.Finite) (hcard : X.ncard = k)
    {f : Fin k → α} (hmem : ∀ i, f i ∈ X) (hinj : Function.Injective f)
    {x : α} (hx : x ∈ X) :
    ∃ i, f i = x := by
  have hsub : Set.range f ⊆ X := by rintro _ ⟨i, rfl⟩; exact hmem i
  have hrange_card : (Set.range f).ncard = k := by
    rw [ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hEq : Set.range f = X :=
    eq_of_subset_of_ncard_le hsub (by rw [hrange_card, hcard]) hfin
  rw [← hEq] at hx
  exact hx

/-- Every node in $\tilde{c}$ of a border cell $c \in \Gamma.C$ belongs to $\Gamma.N \cap
\operatorname{bd} S$. -/
private lemma border_cell_tilde_subset_N_inter_bd {S : Type} [TopologicalSpace S] (Γ : Painting S)
    {c : Set S} (hc : c ∈ Γ.C) (hbd : (c ∩ bd S).Nonempty) :
    tilde c ⊆ Γ.N ∩ bd S := by
  obtain ⟨u, v, _, htilde, _, _, hu, hv⟩ := Γ.border_cell_exists_ends hc hbd
  rw [htilde]
  rintro x (rfl | rfl)
  · exact hu
  · exact hv

/-- For any internal node $n \in \Gamma.N \setminus \operatorname{bd} S$ with $n \in
\operatorname{dom}(\gamma)$,
$\gamma(n)$ does not belong to $\beta(m+)$ for any border node $m \in \Gamma.N \cap
\operatorname{bd} S$. -/
private lemma nodeVertex_notMem_borderPlus_of_notMem_bd
    {α : Type u} {β : Type v} {G : Hypergraph α β} (π : Portrayal G)
    {n m : π.S} (hn_not_bd : n ∉ bd π.S) (hn_dom : n ∈ π.domγ)
    (hm_bd : m ∈ π.Γ.N ∩ bd π.S) :
    π.nodeVertex n ∉ π.borderPlus m := by
  let Θ' := connectedComponentIn (bd π.S) m
  have hΘ' : Θ' ∈ cuffs π.S := ⟨m, hm_bd.2, rfl⟩
  have hΘ'_bd : Θ' ⊆ bd π.S := connectedComponentIn_subset (bd π.S) m
  have hm_Θ' : m ∈ π.Γ.N ∩ Θ' := ⟨hm_bd.1, mem_connectedComponentIn hm_bd.2⟩
  have hn_not_Θ' : n ∉ Θ' := fun h => hn_not_bd (hΘ'_bd h)
  rintro (hmem_bs | ⟨hm_dom, hEq⟩)
  · exact π.p4_notMem Θ' hΘ' m hm_Θ' n hn_dom hn_not_Θ' hmem_bs
  · have hnm : n = m := π.nodeVertex_injOn hn_dom hm_dom hEq
    exact hn_not_bd (hnm ▸ hm_bd.2)

/-- Every border node $n \in \Gamma.N \cap \operatorname{bd} S$ belongs to $\tilde{d}$ for some
border cell $d \in \Gamma.C$. -/
private lemma exists_border_cell_of_mem_N_inter_bd
    {S : Type} [TopologicalSpace S] (hS : IsSurface S) (Γ : Painting S)
    {n : S} (hn : n ∈ Γ.N ∩ bd S) :
    ∃ d ∈ Γ.C, (d ∩ bd S).Nonempty ∧ n ∈ tilde d := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  let Θ' := connectedComponentIn (bd S) n
  have hΘ' : Θ' ∈ cuffs S := ⟨n, hn.2, rfl⟩
  have hΘ'_bd : Θ' ⊆ bd S := connectedComponentIn_subset (bd S) n
  have hΘ'_arc : IsOArc Θ' := (GraphMinor.Surface.cuff_statement.{0} S hS).2.2 Θ' hΘ'
  obtain ⟨E⟩ := Γ.exists_cuffEnumeration hΘ' hΘ'_arc
  have hn_range : n ∈ Set.range E.node := by
    rw [E.range_node]; exact ⟨hn.1, mem_connectedComponentIn hn.2⟩
  rcases hn_range with ⟨i, hi⟩
  have hc_range : E.cell i ∈ {d ∈ Γ.C | (d ∩ Θ').Nonempty} := by
    rw [← E.range_cell]; exact mem_range_self i
  exact ⟨E.cell i, hc_range.1, hc_range.2.mono (inter_subset_inter_right _ hΘ'_bd),
    hi ▸ (E.cell_tilde i) ▸ mem_insert _ _⟩

private theorem active_cell_unique_path
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    {p : ℕ}
    (P : Fin (p + 1) → PathFromTo (π.areaGraph Δ).skeleton (π.borderPlus n₁) (π.borderPlus n₂))
    (hP_disj : Pairwise fun i j => Disjoint {z | z ∈ (P i).walk.support} {z | z ∈ (P
      j).walk.support}) :
    ∀ {d : Set π.S}, d ∈ π.Γ.C → ∀ {l₁ l₂ : Fin (p + 1)}, (fun d l => 2 ≤ {z | z ∈ (P
      l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard) d l₁ → (fun d l => 2 ≤ {z |
      z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard) d l₂ → l₁ = l₂ := by
  let activeFor := fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩
    π.domγ)}.ncard
  intro d hd l₁ l₂ h₁ h₂
  by_contra hne_l
  let S₁ := {z ∈ (P l₁).walk.support | z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}
  let S₂ := {z ∈ (P l₂).walk.support | z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}
  have hdisj_S : Disjoint S₁ S₂ :=
    (hP_disj hne_l).mono (fun _ hz => hz.1) (fun _ hz => hz.1)
  have hfin_img : (π.nodeVertex '' (tilde d ∩ π.domγ)).Finite :=
    ((π.Γ.finite_tilde_cell hd).inter_of_left _).image _
  have hsub_S : S₁ ∪ S₂ ⊆ π.nodeVertex '' (tilde d ∩ π.domγ) := by
    rintro z (hz | hz) <;> exact hz.2
  have h1 : (S₁ ∪ S₂).ncard = S₁.ncard + S₂.ncard :=
    ncard_union_eq hdisj_S (hfin_img.subset fun _ hz => hz.2) (hfin_img.subset fun _ hz => hz.2)
  have h2 : (S₁ ∪ S₂).ncard ≤ (π.nodeVertex '' (tilde d ∩ π.domγ)).ncard :=
    ncard_le_ncard hsub_S hfin_img
  have h3 : (π.nodeVertex '' (tilde d ∩ π.domγ)).ncard ≤ (tilde d ∩ π.domγ).ncard :=
    ncard_image_le ((π.Γ.finite_tilde_cell hd).inter_of_left _)
  have h4 : (tilde d ∩ π.domγ).ncard ≤ (tilde d).ncard :=
    ncard_le_ncard inter_subset_left (π.Γ.finite_tilde_cell hd)
  have h5 : (tilde d).ncard ≤ 3 := π.Γ.ncard_tilde_cell_le hd
  change 2 ≤ S₁.ncard at h₁
  change 2 ≤ S₂.ncard at h₂
  omega

private theorem active_cell_marked_boundary
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    {p : ℕ}
    (P : Fin (p + 1) → PathFromTo (π.areaGraph Δ).skeleton (π.borderPlus n₁) (π.borderPlus n₂))
    (hP_disj : Pairwise fun i j => Disjoint {z | z ∈ (P i).walk.support} {z | z ∈ (P
      j).walk.support})
    (j₀ : Fin (p + 1))
    (hact_unique : ∀ {d : Set π.S}, d ∈ π.Γ.C → ∀ {l₁ l₂ : Fin (p + 1)}, (fun d l => 2 ≤ {z | z ∈
      (P l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard) d l₁ → (fun d l => 2 ≤
      {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard) d l₂ → l₁ = l₂) :
    ∀ d ∈ π.Γ.C, d ⊆ Δ → ¬(d ∩ bd π.S).Nonempty → (fun d => {n | n ∈ tilde d ∩ π.domγ ∧ ∃ l, (fun
      d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard) d l
      ∧ π.nodeVertex n ∈ (P l).walk.support}) d ⊆ tilde d ∧ ((fun d => {n | n ∈ tilde d ∩ π.domγ ∧
      ∃ l, (fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩
      π.domγ)}.ncard) d l ∧ π.nodeVertex n ∈ (P l).walk.support}) d = ∅ ∨ 2 ≤ ((fun d => {n | n ∈
      tilde d ∩ π.domγ ∧ ∃ l, (fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex ''
      (tilde d ∩ π.domγ)}.ncard) d l ∧ π.nodeVertex n ∈ (P l).walk.support}) d).ncard) ∧ ∀ x ∈
      (fun d => {n | n ∈ tilde d ∩ π.domγ ∧ ∃ l, (fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈
      π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard) d l ∧ π.nodeVertex n ∈ (P l).walk.support}) d, ∀
      y ∈ (fun d => {n | n ∈ tilde d ∩ π.domγ ∧ ∃ l, (fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧
      z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard) d l ∧ π.nodeVertex n ∈ (P l).walk.support})
      d, (fun m => m ∈ π.domγ ∧ π.nodeVertex m ∈ (P j₀).walk.support) x → (fun m => m ∈ π.domγ ∧
      π.nodeVertex m ∈ (P j₀).walk.support) y := by
  let activeFor := fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩
    π.domγ)}.ncard
  let e := fun d => {n | n ∈ tilde d ∩ π.domγ ∧ ∃ l, activeFor d l ∧ π.nodeVertex n ∈ (P
    l).walk.support}
  let P_mark := fun m => m ∈ π.domγ ∧ π.nodeVertex m ∈ (P j₀).walk.support
  intro d hd _ _
  refine ⟨fun _ hn => hn.1.1, ?_, ?_⟩
  · by_cases hne_e : (e d).Nonempty
    · right
      rcases hne_e with ⟨n₀, _, l, hact_l, _⟩
      have hsub_img : {z ∈ (P l).walk.support | z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)} ⊆
          π.nodeVertex '' e d := by
        rintro z ⟨hz_sup, n, hn_td, rfl⟩
        exact ⟨n, ⟨hn_td, l, hact_l, hz_sup⟩, rfl⟩
      have hfin_ed : (e d).Finite := (π.Γ.finite_tilde_cell hd).subset fun _ hn => hn.1.1
      have hle₁ := ncard_le_ncard hsub_img (hfin_ed.image _)
      have hle₂ := ncard_image_le (f := π.nodeVertex) hfin_ed
      change 2 ≤ ({z ∈ (P l).walk.support | z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}).ncard
        at hact_l
      change 2 ≤ (e d).ncard
      exact hact_l.trans (hle₁.trans hle₂)
    · exact Or.inl (not_nonempty_iff_eq_empty.mp hne_e)
  · rintro x ⟨_, l₁, hact₁, hx_l₁⟩ y ⟨⟨_, hy_dom⟩, l₂, hact₂, hy_l₂⟩ ⟨_, hx_j₀⟩
    have hl₁_eq : l₁ = l₂ := hact_unique hd hact₁ hact₂
    have hl₁_j₀ : l₁ = j₀ := by
      by_contra hne_l
      exact Set.disjoint_left.mp (hP_disj hne_l) hx_l₁ hx_j₀
    exact ⟨hy_dom, hl₁_j₀ ▸ hl₁_eq ▸ hy_l₂⟩

private theorem interior_cell_active_of_path_edge
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    {p : ℕ}
    (P : Fin (p + 1) → PathFromTo (π.areaGraph Δ).skeleton (π.borderPlus n₁) (π.borderPlus n₂))
    (c₁_end : Set π.S)
    (hc₁_C : c₁_end ∈ π.Γ.C)
    (hc₁_Δ : c₁_end ⊆ Δ)
    (hc₁_bd : (c₁_end ∩ bd π.S).Nonempty)
    (hn₁_c₁ : n₁ ∈ tilde c₁_end)
    (c₂_end : Set π.S)
    (hc₂_C : c₂_end ∈ π.Γ.C)
    (hc₂_Δ : c₂_end ⊆ Δ)
    (hc₂_bd : (c₂_end ∩ bd π.S).Nonempty)
    (hn₂_c₂ : n₂ ∈ tilde c₂_end)
    (j : Fin (p + 1)) :
    ∀ {d : Set π.S}, d ∈ ({d | d ∈ π.Γ.C ∧ d ⊆ Δ}) → ¬(d ∩ bd π.S).Nonempty → ∀ {x y : α}, x ∈ (P
      j).walk.support → y ∈ (P j).walk.support → x ≠ y → ∀ {e₀ : β}, (π.cellGraph d).Inc e₀ x →
      (π.cellGraph d).Inc e₀ y → (fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex ''
      (tilde d ∩ π.domγ)}.ncard) d j := by
  let activeFor := fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩
    π.domγ)}.ncard
  let I_Δ := {d | d ∈ π.Γ.C ∧ d ⊆ Δ}
  intro d hd hd_int x y hx_sup hy_sup hxy e₀ hincx hincy
  by_contra hnot_act
  have hle_one : ({z ∈ (P j).walk.support |
      z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}).ncard ≤ 1 := by
    change ¬ 2 ≤ _ at hnot_act
    omega
  let H₁ := π.cellsUnion (I_Δ \ {d})
  let H₂ := π.cellGraph d
  have hH₁_le : H₁ ≤ G := π.cellsUnion_le _
  have hH₂_le : H₂ ≤ G := π.cellGraph_le d hd.1
  have h_union : H₁ ∪ H₂ = π.areaGraph Δ := by
    apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq (union_le hH₁_le hH₂_le)
      (π.cellsUnion_le I_Δ)
    · ext v
      simp only [H₁, H₂, Portrayal.cellsUnion, union_vertexSet, mem_union, mem_iUnion]
      exact ⟨by rintro (⟨d', ⟨⟨hd'₁, hd'₂⟩, _⟩, hv⟩ | hv)
                · exact ⟨d', ⟨hd'₁, hd'₁.1⟩, hv⟩
                · exact ⟨d, ⟨hd, hd.1⟩, hv⟩,
             by rintro ⟨d', ⟨hd'₁, _⟩, hv⟩
                by_cases hEq : d' = d
                · exact Or.inr (hEq ▸ hv)
                · exact Or.inl ⟨d', ⟨⟨hd'₁, hEq⟩, hd'₁.1⟩, hv⟩⟩
    · ext e'
      simp only [H₁, H₂, Portrayal.cellsUnion, union_edgeSet, mem_union, mem_iUnion]
      exact ⟨by rintro (⟨d', ⟨⟨hd'₁, hd'₂⟩, _⟩, he'⟩ | he')
                · exact ⟨d', ⟨hd'₁, hd'₁.1⟩, he'⟩
                · exact ⟨d, ⟨hd, hd.1⟩, he'⟩,
             by rintro ⟨d', ⟨hd'₁, _⟩, he'⟩
                by_cases hEq : d' = d
                · exact Or.inr (hEq ▸ he')
                · exact Or.inl ⟨d', ⟨⟨hd'₁, hEq⟩, hd'₁.1⟩, he'⟩⟩
  have hu_H₁ : (P j).first ∈ H₁.vertexSet := by
    have hc₁_ne : c₁_end ≠ d := fun h => hd_int (h ▸ hc₁_bd)
    have hvc₁ : (P j).first ∈ (π.cellGraph c₁_end).vertexSet :=
      π.borderPlus_subset_cellGraph hc₁_C hc₁_bd hn₁_c₁ (P j).first_mem
    exact mem_biUnion ⟨⟨⟨hc₁_C, hc₁_Δ⟩, hc₁_ne⟩, hc₁_C⟩ hvc₁
  have hv_H₁ : (P j).last ∈ H₁.vertexSet := by
    have hc₂_ne : c₂_end ≠ d := fun h => hd_int (h ▸ hc₂_bd)
    have hvc₂ : (P j).last ∈ (π.cellGraph c₂_end).vertexSet :=
      π.borderPlus_subset_cellGraph hc₂_C hc₂_bd hn₂_c₂ (P j).last_mem
    exact mem_biUnion ⟨⟨⟨hc₂_C, hc₂_Δ⟩, hc₂_ne⟩, hc₂_C⟩ hvc₂
  have hsub_inter : {z ∈ (P j).walk.support | z ∈ H₁.vertexSet ∩ H₂.vertexSet} ⊆
      {z ∈ (P j).walk.support | z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)} := by
    rintro z ⟨hz_sup, hz₁, hz₂⟩
    change z ∈ ⋃ d' ∈ _, _ at hz₁
    rw [mem_iUnion₂] at hz₁
    rcases hz₁ with ⟨d', ⟨⟨hd'_I, hd'_ne⟩, _⟩, hzd'⟩
    exact ⟨hz_sup, π.p5 d hd.1 hd_int z hz₂ ⟨d', hd'_I.1, hd'_ne, hzd'⟩⟩
  have hcard_inter : ({z ∈ (P j).walk.support | z ∈ H₁.vertexSet ∩ H₂.vertexSet}).ncard ≤ 1
    := by
    have hfin : ({z ∈ (P j).walk.support |
        z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}).Finite :=
      (((π.Γ.finite_tilde_cell hd.1).inter_of_left _).image _).subset fun _ hz => hz.2
    exact (ncard_le_ncard hsub_inter hfin).trans hle_one
  have hlift_w : ∀ {a b : α} (w : (π.areaGraph Δ).skeleton.Walk a b),
      ∃ w' : (H₁ ∪ H₂).skeleton.Walk a b, w'.support = w.support := by
    intro a b w
    induction w with
    | nil => exact ⟨.nil, rfl⟩
    | @cons a u b hadj tail ih =>
      obtain ⟨tail', hsup⟩ := ih
      have hadj' : (H₁ ∪ H₂).skeleton.Adj a u := by
        rw [h_union]; exact hadj
      refine ⟨.cons hadj' tail', ?_⟩
      dsimp [SimpleGraph.Walk.support]
      rw [hsup]
  obtain ⟨w', hw'_sup⟩ := hlift_w (P j).walk
  have hw'_path : w'.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hw'_sup]
    exact (P j).isPath.support_nodup
  have hcard_w' : ({z ∈ w'.support | z ∈ H₁.vertexSet ∩ H₂.vertexSet}).ncard ≤ 1 := by
    simpa only [hw'_sup] using hcard_inter
  have hall_H₁ := walk_in_left_of_ncard_support_inter_le_one hH₁_le hH₂_le
    hu_H₁ hv_H₁ w' hw'_path hcard_w'
  have hx_H₁ : x ∈ H₁.vertexSet := hall_H₁ x (hw'_sup ▸ hx_sup)
  have hy_H₁ : y ∈ H₁.vertexSet := hall_H₁ y (hw'_sup ▸ hy_sup)
  have hx_H₂ : x ∈ H₂.vertexSet := H₂.vertex_mem_of_inc hincx
  have hy_H₂ : y ∈ H₂.vertexSet := H₂.vertex_mem_of_inc hincy
  have hpair : ({x, y} : Set α) ⊆
      {z ∈ (P j).walk.support | z ∈ H₁.vertexSet ∩ H₂.vertexSet} := by
    rintro z (rfl | rfl)
    · exact ⟨hx_sup, hx_H₁, hx_H₂⟩
    · exact ⟨hy_sup, hy_H₁, hy_H₂⟩
  have hfin₂ : ({z ∈ (P j).walk.support | z ∈ H₁.vertexSet ∩ H₂.vertexSet}).Finite :=
    H₁.vertexSet_finite.subset fun _ hz => hz.2.1
  have h2 : 2 ≤ ({z ∈ (P j).walk.support | z ∈ H₁.vertexSet ∩ H₂.vertexSet}).ncard := by
    rw [← ncard_pair hxy]
    exact ncard_le_ncard hpair hfin₂
  omega

private theorem disjoint_active_cell_sides
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    {p : ℕ}
    (hΘ_bd : Θ ⊆ bd π.S)
    (P : Fin (p + 1) → PathFromTo (π.areaGraph Δ).skeleton (π.borderPlus n₁) (π.borderPlus n₂))
    (c : Set π.S)
    (I₁ : Set π.S)
    (I₂ : Set π.S)
    (N₁ : Set π.S)
    (N₂ : Set π.S)
    (hI₁_sub : I₁ ⊆ Θ ∩ discBd Δ)
    (hI₂_sub : I₂ ⊆ Θ ∩ discBd Δ)
    (hdisj_I : Disjoint I₁ I₂)
    (hN₁_sub : N₁ ⊆ (π.Γ.N ∩ Δ) \ bd π.S)
    (hN₂_sub : N₂ ⊆ (π.Γ.N ∩ Δ) \ bd π.S)
    (hdisj_N : Disjoint N₁ N₂)
    (j : Fin (p + 1)) :
    Disjoint ({d | d ∈ ({d | d ∈ π.Γ.C ∧ d ⊆ Δ}) ∧ ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₁ ∨
      ¬(d ∩ bd π.S).Nonempty ∧ (fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex ''
      (tilde d ∩ π.domγ)}.ncard) d j ∧ (fun d => {n | n ∈ tilde d ∩ π.domγ ∧ ∃ l, (fun d l => 2 ≤
      {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard) d l ∧
      π.nodeVertex n ∈ (P l).walk.support}) d ⊆ N₁ ∪ I₁)}) ({d | d ∈ ({d | d ∈ π.Γ.C ∧ d ⊆ Δ}) ∧
      ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₂ ∨ ¬(d ∩ bd π.S).Nonempty ∧ (fun d l => 2 ≤ {z
      | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard) d j ∧ (fun d => {n
      | n ∈ tilde d ∩ π.domγ ∧ ∃ l, (fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex
      '' (tilde d ∩ π.domγ)}.ncard) d l ∧ π.nodeVertex n ∈ (P l).walk.support}) d ⊆ N₂ ∪ I₂)}) := by
  let activeFor := fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩
    π.domγ)}.ncard
  let e := fun d => {n | n ∈ tilde d ∩ π.domγ ∧ ∃ l, activeFor d l ∧ π.nodeVertex n ∈ (P
    l).walk.support}
  let I_Δ := {d | d ∈ π.Γ.C ∧ d ⊆ Δ}
  let D₁ := {d | d ∈ I_Δ ∧ ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₁ ∨ ¬(d ∩ bd π.S).Nonempty
    ∧ activeFor d j ∧ e d ⊆ N₁ ∪ I₁)}
  let D₂ := {d | d ∈ I_Δ ∧ ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₂ ∨ ¬(d ∩ bd π.S).Nonempty
    ∧ activeFor d j ∧ e d ⊆ N₂ ∪ I₂)}
  rw [Set.disjoint_left]
  rintro d ⟨hd_I, h₁⟩ ⟨_, h₂⟩
  rcases h₁ with ⟨hbd, _, ht₁⟩ | ⟨hint, hact, he₁⟩
  · rcases h₂ with ⟨_, _, ht₂⟩ | ⟨hint₂, _, _⟩
    · obtain ⟨u₀, _, _, htilde_d, _, _, _⟩ := π.Γ.border_cell_exists_ends hd_I.1 hbd
      have hu₀ : u₀ ∈ tilde d := htilde_d ▸ mem_insert _ _
      exact Set.disjoint_left.mp hdisj_I (ht₁ hu₀) (ht₂ hu₀)
    · exact hint₂ hbd
  · rcases h₂ with ⟨hbd, _, _⟩ | ⟨_, _, he₂⟩
    · exact hint hbd
    · have hsub_ed : {z ∈ (P j).walk.support |
          z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)} ⊆ π.nodeVertex '' e d := by
        rintro z ⟨hz_sup, n, hn_td, rfl⟩
        exact ⟨n, ⟨hn_td, j, hact, hz_sup⟩, rfl⟩
      have hfin_ed : (e d).Finite := (π.Γ.finite_tilde_cell hd_I.1).subset fun _ hn => hn.1.1
      have hcard_ed : 2 ≤ (e d).ncard := by
        have hle₁ := ncard_le_ncard hsub_ed (hfin_ed.image _)
        have hle₂ := ncard_image_le (f := π.nodeVertex) hfin_ed
        change 2 ≤ ({z ∈ (P j).walk.support |
          z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}).ncard at hact
        omega
      obtain ⟨n₀, hn₀⟩ : (e d).Nonempty := (ncard_pos hfin_ed).mp (by omega)
      have hdisj_NI : Disjoint (N₁ ∪ I₁) (N₂ ∪ I₂) := by
        refine Disjoint.union_left (Disjoint.union_right hdisj_N ?_)
          (Disjoint.union_right ?_ hdisj_I)
        · rw [Set.disjoint_left]
          exact fun x hx₁ hx₂ => (hN₁_sub hx₁).2 (hΘ_bd (hI₂_sub hx₂).1)
        · rw [Set.disjoint_left]
          exact fun x hx₁ hx₂ => (hN₂_sub hx₂).2 (hΘ_bd (hI₁_sub hx₁).1)
      exact Set.disjoint_left.mp hdisj_NI (he₁ hn₀) (he₂ hn₀)

private theorem path_lifts_to_cell_unions
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    {p : ℕ}
    (P : Fin (p + 1) → PathFromTo (π.areaGraph Δ).skeleton (π.borderPlus n₁) (π.borderPlus n₂))
    (m₁ : π.S)
    (m₂ : π.S)
    (c : Set π.S)
    (I₁ : Set π.S)
    (I₂ : Set π.S)
    (N₁ : Set π.S)
    (N₂ : Set π.S)
    (hc_C : c ∈ π.Γ.C)
    (htilde_c : tilde c = {m₁, m₂})
    (hborder_split : ∀ d ∈ π.Γ.C, d ⊆ Δ → (d ∩ bd π.S).Nonempty → d ≠ c → tilde d ⊆ I₁ ∨ tilde d ⊆
      I₂)
    (hint_split : ∀ d ∈ π.Γ.C, d ⊆ Δ → ¬(d ∩ bd π.S).Nonempty → (fun d => {n | n ∈ tilde d ∩
      π.domγ ∧ ∃ l, (fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩
      π.domγ)}.ncard) d l ∧ π.nodeVertex n ∈ (P l).walk.support}) d ⊆ N₁ ∪ I₁ ∨ (fun d => {n | n ∈
      tilde d ∩ π.domγ ∧ ∃ l, (fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex ''
      (tilde d ∩ π.domγ)}.ncard) d l ∧ π.nodeVertex n ∈ (P l).walk.support}) d ⊆ N₂ ∪ I₂)
    (hc_bd : (c ∩ bd π.S).Nonempty)
    (j : Fin (p + 1))
    (Q : PathFromTo (π.areaGraph Δ).skeleton (⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n) (⋃ n ∈ I₂ ∩ π.Γ.N,
      π.borderPlus n))
    (hQ_sub : {z | z ∈ Q.walk.support} ⊆ {z | z ∈ (P j).walk.support})
    :
    let activeFor := fun d l => 2 ≤
      {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard
    let e := fun d =>
      {n | n ∈ tilde d ∩ π.domγ ∧ ∃ l, activeFor d l ∧ π.nodeVertex n ∈ (P l).walk.support}
    let I_Δ := {d | d ∈ π.Γ.C ∧ d ⊆ Δ}
    let D₁ := {d | d ∈ I_Δ ∧ ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₁ ∨
      ¬(d ∩ bd π.S).Nonempty ∧ activeFor d j ∧ e d ⊆ N₁ ∪ I₁)}
    let D₂ := {d | d ∈ I_Δ ∧ ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₂ ∨
      ¬(d ∩ bd π.S).Nonempty ∧ activeFor d j ∧ e d ⊆ N₂ ∪ I₂)}
    let H₁ := π.cellsUnion D₁
    let H₂ := π.cellsUnion D₂
    let Hc := π.cellGraph c
    (∀ {d : Set π.S}, d ∈ I_Δ → ¬(d ∩ bd π.S).Nonempty →
      ∀ {x y : α}, x ∈ (P j).walk.support → y ∈ (P j).walk.support → x ≠ y →
      ∀ {e₀ : β}, (π.cellGraph d).Inc e₀ x → (π.cellGraph d).Inc e₀ y → activeFor d j) →
    D₁ ⊆ π.Γ.C → D₂ ⊆ π.Γ.C → Disjoint D₁ D₂ → c ∉ D₁ → c ∉ D₂ →
    Disjoint H₁.edgeSet (H₂ ∪ Hc).edgeSet → Disjoint H₂.edgeSet Hc.edgeSet →
    ∃ w₀ : (H₁ ∪ (H₂ ∪ Hc)).skeleton.Walk Q.first Q.last, w₀.support = Q.walk.support := by
  intro activeFor e I_Δ D₁ D₂ H₁ H₂ Hc hcell_active hD₁_sub hD₂_sub hdisj_D₁_D₂
    hc_not_D₁ hc_not_D₂ hdisjE_1_2c hdisjE_2_c
  have hstep_all : ∀ {x y : α}, x ∈ (P j).walk.support → y ∈ (P j).walk.support →
      (π.areaGraph Δ).skeleton.Adj x y → (H₁ ∪ (H₂ ∪ Hc)).skeleton.Adj x y := by
    rintro x y hx hy ⟨hxy, e₀, hincx, hincy⟩
    have he₀_mem : e₀ ∈ (π.areaGraph Δ).edgeSet :=
      (π.areaGraph Δ).edge_mem_of_inc hincx
    change e₀ ∈ ⋃ d ∈ _, _ at he₀_mem
    rw [mem_iUnion₂] at he₀_mem
    rcases he₀_mem with ⟨d, ⟨hd_I, hd_C⟩, hed⟩
    have hincx_G : G.Inc e₀ x :=
      (inc_iff_of_le (π.cellsUnion_le I_Δ) ((π.areaGraph Δ).edge_mem_of_inc hincx)).mp hincx
    have hincy_G : G.Inc e₀ y :=
      (inc_iff_of_le (π.cellsUnion_le I_Δ) ((π.areaGraph Δ).edge_mem_of_inc hincy)).mp hincy
    have hincx_d : (π.cellGraph d).Inc e₀ x :=
      (inc_iff_of_le (π.cellGraph_le d hd_C) hed).mpr hincx_G
    have hincy_d : (π.cellGraph d).Inc e₀ y :=
      (inc_iff_of_le (π.cellGraph_le d hd_C) hed).mpr hincy_G
    by_cases hdc : d = c
    · subst hdc
      exact ⟨hxy, e₀, Or.inr (Or.inr hincx_d), Or.inr (Or.inr hincy_d)⟩
    · by_cases hbd_d : (d ∩ bd π.S).Nonempty
      · rcases hborder_split d hd_I.1 hd_I.2 hbd_d hdc with ht₁ | ht₂
        · have hd_D₁ : d ∈ D₁ := ⟨hd_I, Or.inl ⟨hbd_d, hdc, ht₁⟩⟩
          refine ⟨hxy, e₀,
            Or.inl ((inc_iff_of_le (π.cellGraph_le_cellsUnion hd_D₁ hd_C) hed).mp hincx_d),
            Or.inl ((inc_iff_of_le (π.cellGraph_le_cellsUnion hd_D₁ hd_C) hed).mp hincy_d)⟩
        · have hd_D₂ : d ∈ D₂ := ⟨hd_I, Or.inl ⟨hbd_d, hdc, ht₂⟩⟩
          refine ⟨hxy, e₀,
            Or.inr (Or.inl ((inc_iff_of_le (π.cellGraph_le_cellsUnion hd_D₂ hd_C) hed).mp
              hincx_d)),
            Or.inr (Or.inl ((inc_iff_of_le (π.cellGraph_le_cellsUnion hd_D₂ hd_C) hed).mp
              hincy_d))⟩
      · have hact_d : activeFor d j :=
          hcell_active hd_I hbd_d hx hy hxy hincx_d hincy_d
        rcases hint_split d hd_I.1 hd_I.2 hbd_d with he₁ | he₂
        · have hd_D₁ : d ∈ D₁ := ⟨hd_I, Or.inr ⟨hbd_d, hact_d, he₁⟩⟩
          refine ⟨hxy, e₀,
            Or.inl ((inc_iff_of_le (π.cellGraph_le_cellsUnion hd_D₁ hd_C) hed).mp hincx_d),
            Or.inl ((inc_iff_of_le (π.cellGraph_le_cellsUnion hd_D₁ hd_C) hed).mp hincy_d)⟩
        · have hd_D₂ : d ∈ D₂ := ⟨hd_I, Or.inr ⟨hbd_d, hact_d, he₂⟩⟩
          refine ⟨hxy, e₀,
            Or.inr (Or.inl ((inc_iff_of_le (π.cellGraph_le_cellsUnion hd_D₂ hd_C) hed).mp
              hincx_d)),
            Or.inr (Or.inl ((inc_iff_of_le (π.cellGraph_le_cellsUnion hd_D₂ hd_C) hed).mp
              hincy_d))⟩
  have hlift_walk : ∀ {a b : α} (w : (π.areaGraph Δ).skeleton.Walk a b),
      {z | z ∈ w.support} ⊆ {z | z ∈ (P j).walk.support} →
      ∃ w₀ : (H₁ ∪ (H₂ ∪ Hc)).skeleton.Walk a b, w₀.support = w.support := by
    intro a b w hw_sub
    induction w with
    | nil => exact ⟨.nil, rfl⟩
    | @cons a x b hadj tail ih =>
      have ha_P : a ∈ (P j).walk.support := hw_sub (SimpleGraph.Walk.start_mem_support _)
      have hx_P : x ∈ (P j).walk.support :=
        hw_sub (List.mem_cons_of_mem a (SimpleGraph.Walk.start_mem_support tail))
      obtain ⟨tail₀, hsup⟩ := ih (fun z hz => hw_sub (List.mem_cons_of_mem a hz))
      refine ⟨.cons (hstep_all ha_P hx_P hadj) tail₀, ?_⟩
      dsimp [SimpleGraph.Walk.support]
      rw [hsup]
  exact hlift_walk Q.walk hQ_sub

private theorem first_side_path_boundary
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    {p : ℕ}
    (hΘ_bd : Θ ⊆ bd π.S)
    (P : Fin (p + 1) → PathFromTo (π.areaGraph Δ).skeleton (π.borderPlus n₁) (π.borderPlus n₂))
    (c : Set π.S)
    (I₁ : Set π.S)
    (I₂ : Set π.S)
    (N₁ : Set π.S)
    (N₂ : Set π.S)
    (hc_C : c ∈ π.Γ.C)
    (hI₂_sub : I₂ ⊆ Θ ∩ discBd Δ)
    (hdisj_I : Disjoint I₁ I₂)
    (hN₁_sub : N₁ ⊆ (π.Γ.N ∩ Δ) \ bd π.S)
    (hdisj_N : Disjoint N₁ N₂)
    (hc_bd : (c ∩ bd π.S).Nonempty)
    (j : Fin (p + 1))
    (Q : PathFromTo (π.areaGraph Δ).skeleton (⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n) (⋃ n ∈ I₂ ∩ π.Γ.N,
      π.borderPlus n))
    (hQ_sub : {z | z ∈ Q.walk.support} ⊆ {z | z ∈ (P j).walk.support})
    (hdisj_D₁_D₂ : Disjoint ({d | d ∈ ({d | d ∈ π.Γ.C ∧ d ⊆ Δ}) ∧ ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧
      tilde d ⊆ I₁ ∨ ¬(d ∩ bd π.S).Nonempty ∧ (fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈
      π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard) d j ∧ (fun d => {n | n ∈ tilde d ∩ π.domγ ∧ ∃ l,
      (fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard)
      d l ∧ π.nodeVertex n ∈ (P l).walk.support}) d ⊆ N₁ ∪ I₁)}) ({d | d ∈ ({d | d ∈ π.Γ.C ∧ d ⊆
      Δ}) ∧ ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₂ ∨ ¬(d ∩ bd π.S).Nonempty ∧ (fun d l => 2
      ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard) d j ∧ (fun d
      => {n | n ∈ tilde d ∩ π.domγ ∧ ∃ l, (fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈
      π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard) d l ∧ π.nodeVertex n ∈ (P l).walk.support}) d ⊆
      N₂ ∪ I₂)}))
    (hc_not_D₁ : c ∉ ({d | d ∈ ({d | d ∈ π.Γ.C ∧ d ⊆ Δ}) ∧ ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde
      d ⊆ I₁ ∨ ¬(d ∩ bd π.S).Nonempty ∧ (fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈
      π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard) d j ∧ (fun d => {n | n ∈ tilde d ∩ π.domγ ∧ ∃ l,
      (fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard)
      d l ∧ π.nodeVertex n ∈ (P l).walk.support}) d ⊆ N₁ ∪ I₁)})) :
    ∀ z ∈ Q.walk.support, z ∈ (π.cellsUnion ({d | d ∈ ({d | d ∈ π.Γ.C ∧ d ⊆ Δ}) ∧ ((d ∩ bd
      π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₁ ∨ ¬(d ∩ bd π.S).Nonempty ∧ (fun d l => 2 ≤ {z | z ∈ (P
      l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard) d j ∧ (fun d => {n | n ∈
      tilde d ∩ π.domγ ∧ ∃ l, (fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex ''
      (tilde d ∩ π.domγ)}.ncard) d l ∧ π.nodeVertex n ∈ (P l).walk.support}) d ⊆ N₁ ∪
      I₁)})).vertexSet → z ∈ ((π.cellsUnion ({d | d ∈ ({d | d ∈ π.Γ.C ∧ d ⊆ Δ}) ∧ ((d ∩ bd
      π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₂ ∨ ¬(d ∩ bd π.S).Nonempty ∧ (fun d l => 2 ≤ {z | z ∈ (P
      l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard) d j ∧ (fun d => {n | n ∈
      tilde d ∩ π.domγ ∧ ∃ l, (fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex ''
      (tilde d ∩ π.domγ)}.ncard) d l ∧ π.nodeVertex n ∈ (P l).walk.support}) d ⊆ N₂ ∪ I₂)})) ∪
      (π.cellGraph c)).vertexSet ∨ z ∈ (⋃ n ∈ I₂ ∩ π.Γ.N, π.borderPlus n) → z ∈ (⋃ n ∈ I₁ ∩ π.Γ.N,
      π.borderPlus n) := by
  let activeFor := fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩
    π.domγ)}.ncard
  let e := fun d => {n | n ∈ tilde d ∩ π.domγ ∧ ∃ l, activeFor d l ∧ π.nodeVertex n ∈ (P
    l).walk.support}
  let B₁ := ⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n
  let B₂ := ⋃ n ∈ I₂ ∩ π.Γ.N, π.borderPlus n
  let I_Δ := {d | d ∈ π.Γ.C ∧ d ⊆ Δ}
  let D₁ := {d | d ∈ I_Δ ∧ ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₁ ∨ ¬(d ∩ bd π.S).Nonempty
    ∧ activeFor d j ∧ e d ⊆ N₁ ∪ I₁)}
  let D₂ := {d | d ∈ I_Δ ∧ ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₂ ∨ ¬(d ∩ bd π.S).Nonempty
    ∧ activeFor d j ∧ e d ⊆ N₂ ∪ I₂)}
  let H₁ := π.cellsUnion D₁
  let H₂ := π.cellsUnion D₂
  let Hc := π.cellGraph c
  intro z hz_Q hz_H₁ hz_other
  have hz_P : z ∈ (P j).walk.support := hQ_sub hz_Q
  change z ∈ ⋃ d ∈ _, _ at hz_H₁
  rw [mem_iUnion₂] at hz_H₁
  rcases hz_H₁ with ⟨d₁, ⟨hd₁, hd₁_C⟩, hzd₁⟩
  -- Find a cell `d₂ ∈ π.Γ.C` with `d₂ ≠ d₁` and `z ∈ V(α(d₂))`.
  have hex_d₂ : ∃ d₂ ∈ π.Γ.C, d₂ ≠ d₁ ∧ z ∈ (π.cellGraph d₂).vertexSet ∧
      (d₂ ∈ D₂ ∨ (d₂ ∩ bd π.S).Nonempty) := by
    rcases hz_other with (hz_H₂ | hz_Hc) | hz_B₂
    · change z ∈ ⋃ d ∈ _, _ at hz_H₂
      rw [mem_iUnion₂] at hz_H₂
      rcases hz_H₂ with ⟨d₂, ⟨hd₂, hd₂_C⟩, hzd₂⟩
      exact ⟨d₂, hd₂_C, fun h => Set.disjoint_left.mp hdisj_D₁_D₂ hd₁ (h ▸ hd₂),
        hzd₂, Or.inl hd₂⟩
    · exact ⟨c, hc_C, fun h => hc_not_D₁ (h ▸ hd₁), hz_Hc, Or.inr hc_bd⟩
    · rw [mem_iUnion₂] at hz_B₂
      rcases hz_B₂ with ⟨m', hm'_I₂, hzm'⟩
      have hm'_bd : m' ∈ π.Γ.N ∩ bd π.S := ⟨hm'_I₂.2, hΘ_bd (hI₂_sub hm'_I₂.1).1⟩
      obtain ⟨d₂, hd₂_C, hd₂_bd, hm'_d₂⟩ :=
        exists_border_cell_of_mem_N_inter_bd π.isSurface π.Γ hm'_bd
      have hzd₂ : z ∈ (π.cellGraph d₂).vertexSet :=
        π.borderPlus_subset_cellGraph hd₂_C hd₂_bd hm'_d₂ hzm'
      have hd₂_ne : d₂ ≠ d₁ := by
        intro hEq
        rcases hd₁.2 with ⟨_, _, ht₁⟩ | ⟨hint, _, _⟩
        · exact Set.disjoint_left.mp hdisj_I (ht₁ (hEq ▸ hm'_d₂)) hm'_I₂.1
        · exact hint (hEq ▸ hd₂_bd)
      exact ⟨d₂, hd₂_C, hd₂_ne, hzd₂, Or.inr hd₂_bd⟩
  obtain ⟨d₂, hd₂_C, hd₂_ne, hzd₂, hd₂_kind⟩ := hex_d₂
  rcases hd₁.2 with ⟨hbd₁, _, ht₁⟩ | ⟨hint₁, hact₁, he₁⟩
  · obtain ⟨n, hn_t₁, hzn⟩ := π.p6_borderPlus hd₁_C hbd₁ hzd₁ ⟨d₂, hd₂_C, hd₂_ne, hzd₂⟩
    exact mem_biUnion ⟨ht₁ hn_t₁, π.Γ.tilde_subset_N hd₁_C hn_t₁⟩ hzn
  · obtain ⟨n, ⟨hn_t₁, hn_dom⟩, rfl⟩ :=
      π.p5 d₁ hd₁_C hint₁ z hzd₁ ⟨d₂, hd₂_C, hd₂_ne, hzd₂⟩
    have hn_ed₁ : n ∈ e d₁ := ⟨⟨hn_t₁, hn_dom⟩, j, hact₁, hz_P⟩
    rcases he₁ hn_ed₁ with hn_N₁ | hn_I₁
    · exfalso
      have hn_not_bd : n ∉ bd π.S := (hN₁_sub hn_N₁).2
      rcases hd₂_kind with hd₂_D₂ | hd₂_bd
      · rcases hd₂_D₂.2 with ⟨hbd₂, _, _⟩ | ⟨hint₂, hact₂, he₂⟩
        · obtain ⟨m', hm'_t₂, hnm'⟩ :=
            π.p6_borderPlus hd₂_C hbd₂ hzd₂ ⟨d₁, hd₁_C, hd₂_ne.symm, hzd₁⟩
          have hm'_bd : m' ∈ π.Γ.N ∩ bd π.S :=
            border_cell_tilde_subset_N_inter_bd π.Γ hd₂_C hbd₂ hm'_t₂
          exact nodeVertex_notMem_borderPlus_of_notMem_bd π hn_not_bd hn_dom hm'_bd hnm'
        · obtain ⟨n', ⟨hn'_t₂, hn'_dom⟩, hEq_nv⟩ :=
            π.p5 d₂ hd₂_C hint₂ (π.nodeVertex n) hzd₂ ⟨d₁, hd₁_C, hd₂_ne.symm, hzd₁⟩
          have hn_eq : n' = n := π.nodeVertex_injOn hn'_dom hn_dom hEq_nv
          have hn_ed₂ : n ∈ e d₂ := ⟨⟨hn_eq ▸ hn'_t₂, hn_dom⟩, j, hact₂, hz_P⟩
          rcases he₂ hn_ed₂ with hn_N₂ | hn_I₂
          · exact Set.disjoint_left.mp hdisj_N hn_N₁ hn_N₂
          · exact hn_not_bd (hΘ_bd (hI₂_sub hn_I₂).1)
      · obtain ⟨m', hm'_t₂, hnm'⟩ :=
          π.p6_borderPlus hd₂_C hd₂_bd hzd₂ ⟨d₁, hd₁_C, hd₂_ne.symm, hzd₁⟩
        have hm'_bd : m' ∈ π.Γ.N ∩ bd π.S :=
          border_cell_tilde_subset_N_inter_bd π.Γ hd₂_C hd₂_bd hm'_t₂
        exact nodeVertex_notMem_borderPlus_of_notMem_bd π hn_not_bd hn_dom hm'_bd hnm'
    · exact mem_biUnion ⟨hn_I₁, π.Γ.tilde_subset_N hd₁_C hn_t₁⟩ (Or.inr ⟨hn_dom, rfl⟩)

private theorem second_side_path_boundary
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    {p : ℕ}
    (hΘ_bd : Θ ⊆ bd π.S)
    (P : Fin (p + 1) → PathFromTo (π.areaGraph Δ).skeleton (π.borderPlus n₁) (π.borderPlus n₂))
    (c : Set π.S)
    (I₁ : Set π.S)
    (I₂ : Set π.S)
    (N₂ : Set π.S)
    (hc_C : c ∈ π.Γ.C)
    (hI₁_sub : I₁ ⊆ Θ ∩ discBd Δ)
    (hdisj_I : Disjoint I₁ I₂)
    (hN₂_sub : N₂ ⊆ (π.Γ.N ∩ Δ) \ bd π.S)
    (hc_bd : (c ∩ bd π.S).Nonempty)
    (j : Fin (p + 1))
    (Q : PathFromTo (π.areaGraph Δ).skeleton (⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n) (⋃ n ∈ I₂ ∩ π.Γ.N,
      π.borderPlus n))
    (hQ_sub : {z | z ∈ Q.walk.support} ⊆ {z | z ∈ (P j).walk.support})
    (hc_not_D₂ : c ∉ ({d | d ∈ ({d | d ∈ π.Γ.C ∧ d ⊆ Δ}) ∧ ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde
      d ⊆ I₂ ∨ ¬(d ∩ bd π.S).Nonempty ∧ (fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈
      π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard) d j ∧ (fun d => {n | n ∈ tilde d ∩ π.domγ ∧ ∃ l,
      (fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard)
      d l ∧ π.nodeVertex n ∈ (P l).walk.support}) d ⊆ N₂ ∪ I₂)})) :
    ∀ z ∈ Q.walk.support, z ∈ (π.cellsUnion ({d | d ∈ ({d | d ∈ π.Γ.C ∧ d ⊆ Δ}) ∧ ((d ∩ bd
      π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₂ ∨ ¬(d ∩ bd π.S).Nonempty ∧ (fun d l => 2 ≤ {z | z ∈ (P
      l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard) d j ∧ (fun d => {n | n ∈
      tilde d ∩ π.domγ ∧ ∃ l, (fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex ''
      (tilde d ∩ π.domγ)}.ncard) d l ∧ π.nodeVertex n ∈ (P l).walk.support}) d ⊆ N₂ ∪
      I₂)})).vertexSet → z ∈ (π.cellGraph c).vertexSet ∨ z ∈ (⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n) →
      z ∈ (⋃ n ∈ I₂ ∩ π.Γ.N, π.borderPlus n) := by
  let activeFor := fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩
    π.domγ)}.ncard
  let e := fun d => {n | n ∈ tilde d ∩ π.domγ ∧ ∃ l, activeFor d l ∧ π.nodeVertex n ∈ (P
    l).walk.support}
  let B₁ := ⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n
  let B₂ := ⋃ n ∈ I₂ ∩ π.Γ.N, π.borderPlus n
  let I_Δ := {d | d ∈ π.Γ.C ∧ d ⊆ Δ}
  let D₂ := {d | d ∈ I_Δ ∧ ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₂ ∨ ¬(d ∩ bd π.S).Nonempty
    ∧ activeFor d j ∧ e d ⊆ N₂ ∪ I₂)}
  let H₂ := π.cellsUnion D₂
  let Hc := π.cellGraph c
  intro z hz_Q hz_H₂ hz_other
  have hz_P : z ∈ (P j).walk.support := hQ_sub hz_Q
  change z ∈ ⋃ d ∈ _, _ at hz_H₂
  rw [mem_iUnion₂] at hz_H₂
  rcases hz_H₂ with ⟨d₂, ⟨hd₂, hd₂_C⟩, hzd₂⟩
  have hex_d₁ : ∃ d₁ ∈ π.Γ.C, d₁ ≠ d₂ ∧ z ∈ (π.cellGraph d₁).vertexSet ∧
      (d₁ ∩ bd π.S).Nonempty := by
    rcases hz_other with hz_Hc | hz_B₁
    · exact ⟨c, hc_C, fun h => hc_not_D₂ (h ▸ hd₂), hz_Hc, hc_bd⟩
    · rw [mem_iUnion₂] at hz_B₁
      rcases hz_B₁ with ⟨m', hm'_I₁, hzm'⟩
      have hm'_bd : m' ∈ π.Γ.N ∩ bd π.S := ⟨hm'_I₁.2, hΘ_bd (hI₁_sub hm'_I₁.1).1⟩
      obtain ⟨d₁, hd₁_C, hd₁_bd, hm'_d₁⟩ :=
        exists_border_cell_of_mem_N_inter_bd π.isSurface π.Γ hm'_bd
      have hzd₁ : z ∈ (π.cellGraph d₁).vertexSet :=
        π.borderPlus_subset_cellGraph hd₁_C hd₁_bd hm'_d₁ hzm'
      have hd₁_ne : d₁ ≠ d₂ := by
        intro hEq
        rcases hd₂.2 with ⟨_, _, ht₂⟩ | ⟨hint, _, _⟩
        · exact Set.disjoint_left.mp hdisj_I hm'_I₁.1 (ht₂ (hEq ▸ hm'_d₁))
        · exact hint (hEq ▸ hd₁_bd)
      exact ⟨d₁, hd₁_C, hd₁_ne, hzd₁, hd₁_bd⟩
  obtain ⟨d₁, hd₁_C, hd₁_ne, hzd₁, hd₁_bd⟩ := hex_d₁
  rcases hd₂.2 with ⟨hbd₂, _, ht₂⟩ | ⟨hint₂, hact₂, he₂⟩
  · obtain ⟨n, hn_t₂, hzn⟩ := π.p6_borderPlus hd₂_C hbd₂ hzd₂ ⟨d₁, hd₁_C, hd₁_ne, hzd₁⟩
    exact mem_biUnion ⟨ht₂ hn_t₂, π.Γ.tilde_subset_N hd₂_C hn_t₂⟩ hzn
  · obtain ⟨n, ⟨hn_t₂, hn_dom⟩, rfl⟩ :=
      π.p5 d₂ hd₂_C hint₂ z hzd₂ ⟨d₁, hd₁_C, hd₁_ne, hzd₁⟩
    have hn_ed₂ : n ∈ e d₂ := ⟨⟨hn_t₂, hn_dom⟩, j, hact₂, hz_P⟩
    rcases he₂ hn_ed₂ with hn_N₂ | hn_I₂
    · exfalso
      have hn_not_bd : n ∉ bd π.S := (hN₂_sub hn_N₂).2
      obtain ⟨m', hm'_t₁, hnm'⟩ :=
        π.p6_borderPlus hd₁_C hd₁_bd hzd₁ ⟨d₂, hd₂_C, hd₁_ne.symm, hzd₂⟩
      have hm'_bd : m' ∈ π.Γ.N ∩ bd π.S :=
        border_cell_tilde_subset_N_inter_bd π.Γ hd₁_C hd₁_bd hm'_t₁
      exact nodeVertex_notMem_borderPlus_of_notMem_bd π hn_not_bd hn_dom hm'_bd hnm'
    · exact mem_biUnion ⟨hn_I₂, π.Γ.tilde_subset_N hd₂_C hn_t₂⟩ (Or.inr ⟨hn_dom, rfl⟩)

private theorem cuff_node_border_count_le_warp
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    (hΘ : Θ ∈ cuffs π.S)
    (hΘ_bd : Θ ⊆ bd π.S)
    (hΘ_arc : IsOArc Θ) :
    ∀ {n : π.S}, n ∈ π.Γ.N ∩ Θ → (π.borderSet n).ncard ≤ π.warpAt Θ := by
  intro n hn
  obtain ⟨E⟩ := π.Γ.exists_cuffEnumeration hΘ hΘ_arc
  have hn_range : n ∈ Set.range E.node := by rw [E.range_node]; exact hn
  rcases hn_range with ⟨i, rfl⟩
  have hc_range : E.cell i ∈ {d ∈ π.Γ.C | (d ∩ Θ).Nonempty} := by
    rw [← E.range_cell]; exact mem_range_self i
  have hbd_c : (E.cell i ∩ bd π.S).Nonempty :=
    hc_range.2.mono (inter_subset_inter_right _ hΘ_bd)
  have hn_t : E.node i ∈ tilde (E.cell i) := by
    rw [E.cell_tilde i]; exact mem_insert _ _
  exact (π.ncard_borderSet_le_cellWarp hc_range.1 hbd_c hn_t).trans
    (π.cellWarp_le_warpAt hc_range.1 hc_range.2)

private theorem subpath_enters_second_side
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Δ : Set π.S}
    (B₁ : Set α)
    (B₂ : Set α)
    (Q : PathFromTo (π.areaGraph Δ).skeleton B₁ B₂)
    (hst : ¬Q.first = Q.last)
    (hQ_no_inter : ∀ z ∈ Q.walk.support, z ∉ B₁ ∩ B₂)
    (H₁ H₂ Hc : Hypergraph α β)
    (hdisjE_1_2c : Disjoint H₁.edgeSet (H₂ ∪ Hc).edgeSet)
    (w₀ : (H₁ ∪ (H₂ ∪ Hc)).skeleton.Walk Q.first
      Q.last)
    (hw₀_sup : w₀.support = Q.walk.support)
    (hw₀_path : w₀.IsPath)
    (hH₁_boundary : ∀ z ∈ Q.walk.support, z ∈ H₁.vertexSet → z ∈ (H₂
      ∪ Hc).vertexSet ∨ z ∈ B₂ → z ∈ B₁)
    (hint_w₀ : ∀ z ∈ w₀.support, z ≠ Q.first → z ≠ Q.last → z ∉ H₁.vertexSet ∩
      (H₂ ∪ Hc).vertexSet) :
    ∃ w₂c : (H₂ ∪ Hc).skeleton.Walk Q.first Q.last, w₂c.support = Q.walk.support := by
  rcases walk_in_left_or_right_of_internal_disjoint hdisjE_1_2c w₀ hw₀_path hint_w₀ with
    ⟨w₁, hw₁_sup⟩ | ⟨w₂c, hw₂c_sup⟩
  · exfalso
    have ht_H₁ : Q.last ∈ H₁.vertexSet :=
      (walk_endpoints_mem_vertexSet_of_ne w₁ hst).2
    have ht_B₁ : Q.last ∈ B₁ :=
      hH₁_boundary Q.last (SimpleGraph.Walk.end_mem_support Q.walk) ht_H₁
        (Or.inr Q.last_mem)
    exact hQ_no_inter Q.last (SimpleGraph.Walk.end_mem_support Q.walk) ⟨ht_B₁, Q.last_mem⟩
  · exact ⟨w₂c, hw₂c_sup.trans hw₀_sup⟩

private theorem subpath_lies_in_terminal_cell
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Δ : Set π.S}
    (B₁ : Set α)
    (B₂ : Set α)
    (Q : PathFromTo (π.areaGraph Δ).skeleton B₁ B₂)
    (hst : ¬Q.first = Q.last)
    (hQ_no_inter : ∀ z ∈ Q.walk.support, z ∉ B₁ ∩ B₂)
    (H₂ Hc : Hypergraph α β)
    (hdisjE_2_c : Disjoint H₂.edgeSet Hc.edgeSet)
    (hH₂_boundary : ∀ z ∈ Q.walk.support, z ∈ H₂.vertexSet → z ∈ Hc.vertexSet ∨ z ∈ B₁ → z ∈ B₂)
    (w₂c : (H₂ ∪ Hc).skeleton.Walk Q.first Q.last)
    (hw₂c_sup : w₂c.support = Q.walk.support)
    (hw₂c_path : w₂c.IsPath)
    (hint_w₂c : ∀ z ∈ w₂c.support, z ≠ Q.first → z ≠ Q.last → z ∉ H₂.vertexSet ∩
      Hc.vertexSet) :
    ∃ wc : Hc.skeleton.Walk Q.first Q.last, wc.support = Q.walk.support := by
  rcases walk_in_left_or_right_of_internal_disjoint hdisjE_2_c w₂c hw₂c_path hint_w₂c with
    ⟨w₂, hw₂_sup⟩ | ⟨wc, hwc_sup⟩
  · exfalso
    have hs_H₂ : Q.first ∈ H₂.vertexSet :=
      (walk_endpoints_mem_vertexSet_of_ne w₂ hst).1
    have hs_B₂ : Q.first ∈ B₂ :=
      hH₂_boundary Q.first (SimpleGraph.Walk.start_mem_support Q.walk) hs_H₂
        (Or.inr Q.first_mem)
    exact hQ_no_inter Q.first (SimpleGraph.Walk.start_mem_support Q.walk) ⟨Q.first_mem, hs_B₂⟩
  · exact ⟨wc, hwc_sup.trans hw₂c_sup⟩

private theorem single_vertex_path_restricts_to_middle_cell
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    {p : ℕ}
    (hΘ : Θ ∈ cuffs π.S)
    (hn₁ : n₁ ∈ π.Γ.N ∩ Θ)
    (hn₂ : n₂ ∈ π.Γ.N ∩ Θ)
    (hinter_sub : ∀ n ∈ π.Γ.N ∩ discBd Δ, π.borderPlus n₁ ∩ π.borderPlus n₂ ⊆ π.borderPlus n)
    (P : Fin (p + 1) → PathFromTo (π.areaGraph Δ).skeleton (π.borderPlus n₁) (π.borderPlus n₂))
    (m₁ : π.S)
    (m₂ : π.S)
    (c : Set π.S)
    (I₁ : Set π.S)
    (I₂ : Set π.S)
    (hm₁_mem : m₁ ∈ π.Γ.N ∩ (Θ ∩ discBd Δ))
    (hm₂_mem : m₂ ∈ π.Γ.N ∩ (Θ ∩ discBd Δ))
    (hI₁_sub : I₁ ⊆ Θ ∩ discBd Δ)
    (hI₂_sub : I₂ ⊆ Θ ∩ discBd Δ)
    (hord_I : ∀ n ∈ I₁ ∩ π.Γ.N, ∀ n' ∈ I₂ ∩ π.Γ.N, (n ≠ n₁ → n ≠ m₁ → GM19.InOrderOn Θ n₁ n m₁ n')
      ∧ (m₁ ≠ n₁ → n' ≠ n₂ → GM19.InOrderOn Θ n₁ m₁ n' n₂) ∧ (n' ≠ m₂ → n' ≠ n₂ → GM19.InOrderOn Θ
      n m₂ n' n₂) ∧ (n ≠ n₁ → m₂ ≠ n₂ → GM19.InOrderOn Θ n₁ n m₂ n₂))
    (j : Fin (p + 1))
    (Q : PathFromTo (π.areaGraph Δ).skeleton (⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n) (⋃ n ∈ I₂ ∩ π.Γ.N,
      π.borderPlus n))
    (hQ_sub : {z | z ∈ Q.walk.support} ⊆ {z | z ∈ (P j).walk.support})
    (hst : Q.first = Q.last) :
    ∃ Q' : PathFromTo (π.cellGraph c).skeleton (π.borderPlus m₁) (π.borderPlus m₂),
      {z | z ∈ Q'.walk.support} ⊆ {z | z ∈ (P j).walk.support} ∧
        Q'.first ∈ (⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n) ∧
        Q'.last ∈ (⋃ n ∈ I₂ ∩ π.Γ.N, π.borderPlus n) := by
  let B₁ := ⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n
  let B₂ := ⋃ n ∈ I₂ ∩ π.Γ.N, π.borderPlus n
  let s := Q.first
  have hs_B₁₀ : s ∈ B₁ := Q.first_mem
  have hs_B₂₀ : s ∈ B₂ := by
    change Q.first ∈ B₂
    rw [hst]
    exact Q.last_mem
  have hs_B₁ : s ∈ B₁ := hs_B₁₀
  have hs_B₂ : s ∈ B₂ := hs_B₂₀
  rw [mem_iUnion₂] at hs_B₁ hs_B₂
  rcases hs_B₁ with ⟨n, hn_I₁, hsn⟩
  rcases hs_B₂ with ⟨n', hn'_I₂, hsn'⟩
  have hn_Θ : n ∈ π.Γ.N ∩ Θ := ⟨hn_I₁.2, (hI₁_sub hn_I₁.1).1⟩
  have hn'_Θ : n' ∈ π.Γ.N ∩ Θ := ⟨hn'_I₂.2, (hI₂_sub hn'_I₂.1).1⟩
  have hm₁_Θ : m₁ ∈ π.Γ.N ∩ Θ := ⟨hm₁_mem.1, hm₁_mem.2.1⟩
  have hm₂_Θ : m₂ ∈ π.Γ.N ∩ Θ := ⟨hm₂_mem.1, hm₂_mem.2.1⟩
  obtain ⟨hord₁, hord₂, hord₃, hord₄⟩ := hord_I n hn_I₁ n' hn'_I₂
  have hs_m₁ : s ∈ π.borderPlus m₁ := by
    by_contra hnot_m₁
    have hs_n₁ : s ∈ π.borderPlus n₁ := by
      by_cases hnn₁ : n = n₁
      · exact hnn₁ ▸ hsn
      · have hnm₁ : n ≠ m₁ := fun h => hnot_m₁ (h ▸ hsn)
        have hord := inOrderOn_cyclic (hord₁ hnn₁ hnm₁)
        exact (π.p7 Θ hΘ n hn_Θ m₁ hm₁_Θ n' hn'_Θ n₁ hn₁ hord s hsn hsn').resolve_left hnot_m₁
    have hm₁_ne_n₁ : m₁ ≠ n₁ := fun h => hnot_m₁ (h ▸ hs_n₁)
    have hs_n₂ : s ∈ π.borderPlus n₂ := by
      by_cases hn'n₂ : n' = n₂
      · exact hn'n₂ ▸ hsn'
      · have hord := hord₂ hm₁_ne_n₁ hn'n₂
        exact (π.p7 Θ hΘ n₁ hn₁ m₁ hm₁_Θ n' hn'_Θ n₂ hn₂ hord s hs_n₁ hsn').resolve_left hnot_m₁
    exact hnot_m₁ (hinter_sub m₁ ⟨hm₁_mem.1, hm₁_mem.2.2⟩ ⟨hs_n₁, hs_n₂⟩)
  have hs_m₂ : s ∈ π.borderPlus m₂ := by
    by_contra hnot_m₂
    have hs_n₂ : s ∈ π.borderPlus n₂ := by
      by_cases hn'n₂ : n' = n₂
      · exact hn'n₂ ▸ hsn'
      · have hn'm₂ : n' ≠ m₂ := fun h => hnot_m₂ (h ▸ hsn')
        have hord := hord₃ hn'm₂ hn'n₂
        exact (π.p7 Θ hΘ n hn_Θ m₂ hm₂_Θ n' hn'_Θ n₂ hn₂ hord s hsn hsn').resolve_left hnot_m₂
    have hm₂_ne_n₂ : m₂ ≠ n₂ := fun h => hnot_m₂ (h ▸ hs_n₂)
    have hs_n₁ : s ∈ π.borderPlus n₁ := by
      by_cases hnn₁ : n = n₁
      · exact hnn₁ ▸ hsn
      · have hord := inOrderOn_cyclic (hord₄ hnn₁ hm₂_ne_n₂)
        exact (π.p7 Θ hΘ n hn_Θ m₂ hm₂_Θ n₂ hn₂ n₁ hn₁ hord s hsn hs_n₂).resolve_left hnot_m₂
    exact hnot_m₂ (hinter_sub m₂ ⟨hm₂_mem.1, hm₂_mem.2.2⟩ ⟨hs_n₁, hs_n₂⟩)
  refine ⟨⟨s, s, .nil, SimpleGraph.Walk.IsPath.nil, hs_m₁, hs_m₂⟩, ?_, hs_B₁₀, hs_B₂₀⟩
  intro z hz
  exact hQ_sub ((List.mem_singleton.mp hz) ▸ SimpleGraph.Walk.start_mem_support Q.walk)

private theorem path_family_restricts_to_middle_cell
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    {p : ℕ}
    (hΘ : Θ ∈ cuffs π.S)
    (hn₁ : n₁ ∈ π.Γ.N ∩ Θ)
    (hn₂ : n₂ ∈ π.Γ.N ∩ Θ)
    (hinter_sub : ∀ n ∈ π.Γ.N ∩ discBd Δ, π.borderPlus n₁ ∩ π.borderPlus n₂ ⊆ π.borderPlus n)
    (hΘ_bd : Θ ⊆ bd π.S)
    (P : Fin (p + 1) → PathFromTo (π.areaGraph Δ).skeleton (π.borderPlus n₁) (π.borderPlus n₂))
    (P_mark : π.S → Prop)
    (m₁ : π.S)
    (m₂ : π.S)
    (c : Set π.S)
    (I₁ : Set π.S)
    (I₂ : Set π.S)
    (N₁ : Set π.S)
    (N₂ : Set π.S)
    (hm₁_mem : m₁ ∈ π.Γ.N ∩ (Θ ∩ discBd Δ))
    (hm₂_mem : m₂ ∈ π.Γ.N ∩ (Θ ∩ discBd Δ))
    (hm_ne : m₁ ≠ m₂)
    (hP_m₁ : P_mark m₁)
    (hP_m₂ : ¬P_mark m₂)
    (hc_C : c ∈ π.Γ.C)
    (htilde_c : tilde c = {m₁, m₂})
    (hI₁_sub : I₁ ⊆ Θ ∩ discBd Δ)
    (hI₂_sub : I₂ ⊆ Θ ∩ discBd Δ)
    (hdisj_I : Disjoint I₁ I₂)
    (hm₁_I₁ : m₁ ∈ I₁)
    (hm₂_I₂ : m₂ ∈ I₂)
    (hN₁_sub : N₁ ⊆ (π.Γ.N ∩ Δ) \ bd π.S)
    (hN₂_sub : N₂ ⊆ (π.Γ.N ∩ Δ) \ bd π.S)
    (hdisj_N : Disjoint N₁ N₂)
    (hord_I : ∀ n ∈ I₁ ∩ π.Γ.N, ∀ n' ∈ I₂ ∩ π.Γ.N, (n ≠ n₁ → n ≠ m₁ → GM19.InOrderOn Θ n₁ n m₁ n')
      ∧ (m₁ ≠ n₁ → n' ≠ n₂ → GM19.InOrderOn Θ n₁ m₁ n' n₂) ∧ (n' ≠ m₂ → n' ≠ n₂ → GM19.InOrderOn Θ
      n m₂ n' n₂) ∧ (n ≠ n₁ → m₂ ≠ n₂ → GM19.InOrderOn Θ n₁ n m₂ n₂))
    (c₁_end : Set π.S)
    (hc₁_C : c₁_end ∈ π.Γ.C)
    (hc₁_Δ : c₁_end ⊆ Δ)
    (hc₁_bd : (c₁_end ∩ bd π.S).Nonempty)
    (hn₁_c₁ : n₁ ∈ tilde c₁_end)
    (c₂_end : Set π.S)
    (hc₂_C : c₂_end ∈ π.Γ.C)
    (hc₂_Δ : c₂_end ⊆ Δ)
    (hc₂_bd : (c₂_end ∩ bd π.S).Nonempty)
    (hn₂_c₂ : n₂ ∈ tilde c₂_end)
    (hborder_split : ∀ d ∈ π.Γ.C, d ⊆ Δ → (d ∩ bd π.S).Nonempty → d ≠ c → tilde d ⊆ I₁ ∨ tilde d ⊆
      I₂)
    (hint_split : ∀ d ∈ π.Γ.C, d ⊆ Δ → ¬(d ∩ bd π.S).Nonempty → (fun d => {n | n ∈ tilde d ∩
      π.domγ ∧ ∃ l, (fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩
      π.domγ)}.ncard) d l ∧ π.nodeVertex n ∈ (P l).walk.support}) d ⊆ N₁ ∪ I₁ ∨ (fun d => {n | n ∈
      tilde d ∩ π.domγ ∧ ∃ l, (fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex ''
      (tilde d ∩ π.domγ)}.ncard) d l ∧ π.nodeVertex n ∈ (P l).walk.support}) d ⊆ N₂ ∪ I₂)
    (hc_bd : (c ∩ bd π.S).Nonempty)
    (hbp₁_sub_B₁ : π.borderPlus n₁ ⊆ (⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n))
    (hbp₂_sub_B₂ : π.borderPlus n₂ ⊆ (⋃ n ∈ I₂ ∩ π.Γ.N, π.borderPlus n))
    (hbp_m₁_sub_B₁ : π.borderPlus m₁ ⊆ (⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n))
    (hbp_m₂_sub_B₂ : π.borderPlus m₂ ⊆ (⋃ n ∈ I₂ ∩ π.Γ.N, π.borderPlus n)) :
    ∀ j : Fin (p + 1),
      ∃ Q' : PathFromTo (π.cellGraph c).skeleton (π.borderPlus m₁) (π.borderPlus m₂),
        {z | z ∈ Q'.walk.support} ⊆ {z | z ∈ (P j).walk.support} ∧
          Q'.first ∈ ⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n ∧
          Q'.last ∈ ⋃ n ∈ I₂ ∩ π.Γ.N, π.borderPlus n := by
  let activeFor := fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩
    π.domγ)}.ncard
  let e := fun d => {n | n ∈ tilde d ∩ π.domγ ∧ ∃ l, activeFor d l ∧ π.nodeVertex n ∈ (P
    l).walk.support}
  let B₁ := ⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n
  let B₂ := ⋃ n ∈ I₂ ∩ π.Γ.N, π.borderPlus n
  intro j
  let Pj_B : PathFromTo (π.areaGraph Δ).skeleton B₁ B₂ :=
    ⟨(P j).first, (P j).last, (P j).walk, (P j).isPath,
     hbp₁_sub_B₁ (P j).first_mem, hbp₂_sub_B₂ (P j).last_mem⟩
  obtain ⟨Q, hQ_sub, hQ_int, hQ_inter⟩ := exists_minimal_subpath_from_to Pj_B
  by_cases hst : Q.first = Q.last
  · have hSingletonPath :
        ∃ Q' : PathFromTo (π.cellGraph c).skeleton (π.borderPlus m₁) (π.borderPlus m₂),
          {z | z ∈ Q'.walk.support} ⊆ {z | z ∈ (P j).walk.support} ∧
            Q'.first ∈ B₁ ∧ Q'.last ∈ B₂ := by
      exact single_vertex_path_restricts_to_middle_cell (α := α) (β := β) (G := G) π (Θ := Θ) (Δ
        := Δ) (n₁ := n₁) (n₂ := n₂) (p := p) hΘ hn₁ hn₂ hinter_sub P m₁ m₂ c I₁ I₂ hm₁_mem hm₂_mem
        hI₁_sub hI₂_sub hord_I j Q hQ_sub hst
    exact hSingletonPath
  · -- Case 2: `s_j ≠ t_j` (page 180).
    have hQ_no_inter : ∀ z ∈ Q.walk.support, z ∉ B₁ ∩ B₂ := hQ_inter hst
    let I_Δ : Set (Set π.S) := {d ∈ π.Γ.C | d ⊆ Δ}
    -- Every internal cell `d ∈ I_Δ` used by `P j` has `activeFor d j`.
    have hcell_active : ∀ {d : Set π.S}, d ∈ I_Δ → ¬ (d ∩ bd π.S).Nonempty →
        ∀ {x y : α}, x ∈ (P j).walk.support → y ∈ (P j).walk.support → x ≠ y →
        ∀ {e₀ : β}, (π.cellGraph d).Inc e₀ x → (π.cellGraph d).Inc e₀ y →
        activeFor d j := by
      exact interior_cell_active_of_path_edge (α := α) (β := β) (G := G) π (Δ := Δ) (n₁
        := n₁) (n₂ := n₂) (p := p) P c₁_end hc₁_C hc₁_Δ hc₁_bd hn₁_c₁ c₂_end hc₂_C hc₂_Δ hc₂_bd
        hn₂_c₂ j
    -- Partition the active cells of `I_Δ` into `D₁`, `D₂`, and `{c}`.
    let D₁ : Set (Set π.S) :=
      {d ∈ I_Δ | ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₁) ∨
        (¬ (d ∩ bd π.S).Nonempty ∧ activeFor d j ∧ e d ⊆ N₁ ∪ I₁)}
    let D₂ : Set (Set π.S) :=
      {d ∈ I_Δ | ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₂) ∨
        (¬ (d ∩ bd π.S).Nonempty ∧ activeFor d j ∧ e d ⊆ N₂ ∪ I₂)}
    let H₁ := π.cellsUnion D₁
    let H₂ := π.cellsUnion D₂
    let Hc := π.cellGraph c
    have hD₁_sub : D₁ ⊆ π.Γ.C := fun _ hd => hd.1.1
    have hD₂_sub : D₂ ⊆ π.Γ.C := fun _ hd => hd.1.1
    have hdisj_D₁_D₂ : Disjoint D₁ D₂ := by
      exact disjoint_active_cell_sides (α := α) (β := β) (G := G) π (Θ := Θ) (Δ := Δ) (n₁ := n₁)
        (n₂ := n₂) (p := p) hΘ_bd P c I₁ I₂ N₁ N₂ hI₁_sub hI₂_sub hdisj_I hN₁_sub hN₂_sub
        hdisj_N j
    have hc_not_D₁ : c ∉ D₁ := by
      rintro ⟨_, ⟨_, hne_c, _⟩ | ⟨hint, _, _⟩⟩
      · exact hne_c rfl
      · exact hint hc_bd
    have hc_not_D₂ : c ∉ D₂ := by
      rintro ⟨_, ⟨_, hne_c, _⟩ | ⟨hint, _, _⟩⟩
      · exact hne_c rfl
      · exact hint hc_bd
    have hdisjE_1_2c : Disjoint H₁.edgeSet (H₂ ∪ Hc).edgeSet := by
      rw [union_edgeSet]
      refine Disjoint.union_right ?_ ?_
      · rw [Set.disjoint_left]
        intro e₀ he₁ he₂
        change e₀ ∈ ⋃ d ∈ _, _ at he₁ he₂
        rw [mem_iUnion₂] at he₁ he₂
        rcases he₁ with ⟨d₁, ⟨hd₁, hd₁_C⟩, he₁⟩
        rcases he₂ with ⟨d₂, ⟨hd₂, hd₂_C⟩, he₂⟩
        exact Set.disjoint_left.mp
          (π.p1_disjoint d₁ hd₁_C d₂ hd₂_C (fun h => Set.disjoint_left.mp hdisj_D₁_D₂ hd₁
            (h ▸ hd₂)))
          he₁ he₂
      · rw [Set.disjoint_left]
        intro e₀ he₁ hec
        change e₀ ∈ ⋃ d ∈ _, _ at he₁
        rw [mem_iUnion₂] at he₁
        rcases he₁ with ⟨d₁, ⟨hd₁, hd₁_C⟩, he₁⟩
        exact Set.disjoint_left.mp
          (π.p1_disjoint d₁ hd₁_C c hc_C (fun h => hc_not_D₁ (h ▸ hd₁))) he₁ hec
    have hdisjE_2_c : Disjoint H₂.edgeSet Hc.edgeSet := by
      rw [Set.disjoint_left]
      intro e₀ he₂ hec
      change e₀ ∈ ⋃ d ∈ _, _ at he₂
      rw [mem_iUnion₂] at he₂
      rcases he₂ with ⟨d₂, ⟨hd₂, hd₂_C⟩, he₂⟩
      exact Set.disjoint_left.mp
        (π.p1_disjoint d₂ hd₂_C c hc_C (fun h => hc_not_D₂ (h ▸ hd₂))) he₂ hec
    -- Lift `Q.walk` to `(H₁ ∪ (H₂ ∪ Hc)).skeleton`.
    have hQ_lift_all : ∃ w₀ : (H₁ ∪ (H₂ ∪ Hc)).skeleton.Walk Q.first Q.last,
        w₀.support = Q.walk.support := by
      exact path_lifts_to_cell_unions (α := α) (β := β) (G := G) π (Δ := Δ) (n₁ := n₁)
        (n₂ := n₂) (p := p) P m₁ m₂ c I₁ I₂ N₁ N₂ hc_C htilde_c hborder_split
        hint_split hc_bd j Q hQ_sub hcell_active hD₁_sub hD₂_sub hdisj_D₁_D₂ hc_not_D₁
        hc_not_D₂ hdisjE_1_2c hdisjE_2_c
    obtain ⟨w₀, hw₀_sup⟩ := hQ_lift_all
    have hw₀_path : w₀.IsPath := by
      rw [SimpleGraph.Walk.isPath_def, hw₀_sup]
      exact Q.isPath.support_nodup
    -- Any vertex of `Q` in `V(H₁)` that also lies in `V(H₂ ∪ Hc) ∪ B₂` must lie in `B₁`.
    have hH₁_boundary : ∀ z ∈ Q.walk.support, z ∈ H₁.vertexSet →
        (z ∈ (H₂ ∪ Hc).vertexSet ∨ z ∈ B₂) → z ∈ B₁ := by
      exact first_side_path_boundary (α := α) (β := β) (G := G) π (Θ := Θ) (Δ := Δ) (n₁ := n₁)
        (n₂ := n₂) (p := p) hΘ_bd P c I₁ I₂ N₁ N₂ hc_C hI₂_sub hdisj_I hN₁_sub hdisj_N hc_bd j
        Q hQ_sub hdisj_D₁_D₂ hc_not_D₁
    -- Similarly, any vertex of `Q` in `V(H₂)` that also lies in `V(Hc) ∪ B₁` must lie in `B₂`.
    have hH₂_boundary : ∀ z ∈ Q.walk.support, z ∈ H₂.vertexSet →
        (z ∈ Hc.vertexSet ∨ z ∈ B₁) → z ∈ B₂ := by
      exact second_side_path_boundary (α := α) (β := β) (G := G) π (Θ := Θ) (Δ := Δ) (n₁ := n₁)
        (n₂ := n₂) (p := p) hΘ_bd P c I₁ I₂ N₂ hc_C hI₁_sub hdisj_I hN₂_sub hc_bd j Q hQ_sub
        hc_not_D₂
    -- Apply `walk_in_left_or_right_of_internal_disjoint` to `w₀` in `H₁ ∪ (H₂ ∪ Hc)`.
    have hint_w₀ : ∀ z ∈ w₀.support, z ≠ Q.first → z ≠ Q.last →
        z ∉ H₁.vertexSet ∩ (H₂ ∪ Hc).vertexSet := by
      intro z hz hzf hzl ⟨hz₁, hz₂⟩
      exact hQ_int z (hw₀_sup ▸ hz) hzf hzl
        (Or.inl (hH₁_boundary z (hw₀_sup ▸ hz) hz₁ (Or.inl hz₂)))
    have hw_2c : ∃ w₂c : (H₂ ∪ Hc).skeleton.Walk Q.first Q.last,
        w₂c.support = Q.walk.support := by
      exact subpath_enters_second_side (α := α) (β := β) (G := G) π (Δ := Δ) B₁ B₂ Q hst
        hQ_no_inter H₁ H₂ Hc hdisjE_1_2c w₀ hw₀_sup hw₀_path hH₁_boundary hint_w₀
    obtain ⟨w₂c, hw₂c_sup⟩ := hw_2c
    have hw₂c_path : w₂c.IsPath := by
      rw [SimpleGraph.Walk.isPath_def, hw₂c_sup]
      exact Q.isPath.support_nodup
    -- Apply `walk_in_left_or_right_of_internal_disjoint` to `w₂c` in `H₂ ∪ Hc`.
    have hint_w₂c : ∀ z ∈ w₂c.support, z ≠ Q.first → z ≠ Q.last →
        z ∉ H₂.vertexSet ∩ Hc.vertexSet := by
      intro z hz hzf hzl ⟨hz₂, hzc⟩
      exact hQ_int z (hw₂c_sup ▸ hz) hzf hzl
        (Or.inr (hH₂_boundary z (hw₂c_sup ▸ hz) hz₂ (Or.inl hzc)))
    have hwc : ∃ wc : Hc.skeleton.Walk Q.first Q.last, wc.support = Q.walk.support := by
      exact subpath_lies_in_terminal_cell (α := α) (β := β) (G := G) π (Δ := Δ) B₁ B₂ Q hst
        hQ_no_inter H₂ Hc hdisjE_2_c hH₂_boundary w₂c hw₂c_sup hw₂c_path hint_w₂c
    obtain ⟨wc, hwc_sup⟩ := hwc
    have hwc_path : wc.IsPath := by
      rw [SimpleGraph.Walk.isPath_def, hwc_sup]
      exact Q.isPath.support_nodup
    obtain ⟨hs_Hc, ht_Hc⟩ := walk_endpoints_mem_vertexSet_of_ne wc hst
    -- Show `Q.first ∈ π.borderPlus m₁` and `Q.last ∈ π.borderPlus m₂`.
    have hs_m₁ : Q.first ∈ π.borderPlus m₁ := by
      have hs_B₁ := Q.first_mem
      rw [mem_iUnion₂] at hs_B₁
      rcases hs_B₁ with ⟨n, hn_I₁, hsn⟩
      by_cases hnm₁ : n = m₁
      · exact hnm₁ ▸ hsn
      · have hn_bd : n ∈ π.Γ.N ∩ bd π.S := ⟨hn_I₁.2, hΘ_bd (hI₁_sub hn_I₁.1).1⟩
        obtain ⟨d₁, hd₁_C, hd₁_bd, hn_d₁⟩ :=
          exists_border_cell_of_mem_N_inter_bd π.isSurface π.Γ hn_bd
        have hsd₁ : Q.first ∈ (π.cellGraph d₁).vertexSet :=
          π.borderPlus_subset_cellGraph hd₁_C hd₁_bd hn_d₁ hsn
        have hd₁_ne_c : d₁ ≠ c := by
          intro hEq
          have hn_tc : n ∈ ({m₁, m₂} : Set π.S) := htilde_c ▸ hEq ▸ hn_d₁
          rcases hn_tc with rfl | rfl
          · exact hnm₁ rfl
          · exact Set.disjoint_left.mp hdisj_I hn_I₁.1 hm₂_I₂
        obtain ⟨m', hm'_tc, hsm'⟩ :=
          π.p6_borderPlus hc_C hc_bd hs_Hc ⟨d₁, hd₁_C, hd₁_ne_c, hsd₁⟩
        rw [htilde_c] at hm'_tc
        rcases hm'_tc with rfl | rfl
        · exact hsm'
        · exfalso
          exact hQ_no_inter Q.first (SimpleGraph.Walk.start_mem_support Q.walk)
            ⟨Q.first_mem, hbp_m₂_sub_B₂ hsm'⟩
    have ht_m₂ : Q.last ∈ π.borderPlus m₂ := by
      have ht_B₂ := Q.last_mem
      rw [mem_iUnion₂] at ht_B₂
      rcases ht_B₂ with ⟨n', hn'_I₂, htn'⟩
      by_cases hn'm₂ : n' = m₂
      · exact hn'm₂ ▸ htn'
      · have hn'_bd : n' ∈ π.Γ.N ∩ bd π.S := ⟨hn'_I₂.2, hΘ_bd (hI₂_sub hn'_I₂.1).1⟩
        obtain ⟨d₂, hd₂_C, hd₂_bd, hn'_d₂⟩ :=
          exists_border_cell_of_mem_N_inter_bd π.isSurface π.Γ hn'_bd
        have htd₂ : Q.last ∈ (π.cellGraph d₂).vertexSet :=
          π.borderPlus_subset_cellGraph hd₂_C hd₂_bd hn'_d₂ htn'
        have hd₂_ne_c : d₂ ≠ c := by
          intro hEq
          have hn'_tc : n' ∈ ({m₁, m₂} : Set π.S) := htilde_c ▸ hEq ▸ hn'_d₂
          rcases hn'_tc with rfl | rfl
          · exact Set.disjoint_left.mp hdisj_I hm₁_I₁ hn'_I₂.1
          · exact hn'm₂ rfl
        obtain ⟨m', hm'_tc, htm'⟩ :=
          π.p6_borderPlus hc_C hc_bd ht_Hc ⟨d₂, hd₂_C, hd₂_ne_c, htd₂⟩
        rw [htilde_c] at hm'_tc
        rcases hm'_tc with rfl | rfl
        · exfalso
          exact hQ_no_inter Q.last (SimpleGraph.Walk.end_mem_support Q.walk)
            ⟨hbp_m₁_sub_B₁ htm', Q.last_mem⟩
        · exact htm'
    refine ⟨⟨Q.first, Q.last, wc, hwc_path, hs_m₁, ht_m₂⟩, ?_, Q.first_mem, Q.last_mem⟩
    intro z hz
    exact hQ_sub (hwc_sup ▸ hz)

/-- **Graph Minors XVII, (7.3)** (pages 178–179):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a portrayal of a hypergraph $G$. Let
$n_1, n_2$ be distinct nodes bordering a cuff $\Theta$, and let $F \subseteq \Sigma$ be a
$\Gamma$-normal $1$-arc with ... ends $n_1, n_2$ and with $F \cap N(\Gamma) = \{n_1, n_2\}$. Let
$\Delta \subseteq \Sigma$ be a disc with $F \subseteq bd(\Delta) \subseteq F \cup \Theta$,
and for each $n \in N(\Gamma) \cap bd(\Delta)$ let
$\beta(n_1+) \cap \beta(n_2+) \subseteq \beta(n+)$. Let $\pi$ have warp $\le p$ at $\Theta$, and
let $|\beta(n_1+)| = |\beta(n_2+)| = p+1$. Then every linkage in $\alpha(\Delta)$ from
$\beta(n_1+)$ to $\beta(n_2+)$ pairs $\gamma(n_1)$ with $\gamma(n_2)$."

 Note: On page 179, the paper defines
$B_h = \bigcap (\beta(n+) : n \in I_h \cap N(\Gamma))$ ($h = 1, 2$), which is a typographical slip
for $B_h = \bigcup (\beta(n+) : n \in I_h \cap N(\Gamma))$, as the later uses of $B_1$ and $B_2$
in the proof on pages 179 and 180 show. -/
theorem theorem_7_3_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β} (π : Portrayal G)
    {Θ F Δ : Set π.S} {n₁ n₂ : π.S} {p : ℕ}
    (hΘ : Θ ∈ cuffs π.S) (hn₁ : n₁ ∈ π.Γ.N ∩ Θ) (hn₂ : n₂ ∈ π.Γ.N ∩ Θ) (hne : n₁ ≠ n₂)
    (hnorm : π.Γ.IsNormal F) (hF : IsLineWithEnds F n₁ n₂)
    (hFbd : F ∩ bd π.S = {n₁, n₂}) (hFN : F ∩ π.Γ.N = {n₁, n₂})
    (hΔ : IsClosedDisc Δ) (hF_bd : F ⊆ discBd Δ) (hbd_sub : discBd Δ ⊆ F ∪ Θ)
    (hinter_sub : ∀ n ∈ π.Γ.N ∩ discBd Δ,
      π.borderPlus n₁ ∩ π.borderPlus n₂ ⊆ π.borderPlus n)
    (hwarp : π.warpAt Θ ≤ p)
    (hcard₁ : (π.borderPlus n₁).ncard = p + 1)
    (hcard₂ : (π.borderPlus n₂).ncard = p + 1) :
    Portrayal.LinkagePairs (π.areaGraph Δ).skeleton
      (π.borderPlus n₁) (π.borderPlus n₂) (p + 1)
      (π.nodeVertex n₁) (π.nodeVertex n₂) := by
  classical
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hΘ_arc : IsOArc Θ := (GraphMinor.Surface.cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
  have hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S := ⟨hn₁.1, hΘ_bd hn₁.2⟩
  have hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S := ⟨hn₂.1, hΘ_bd hn₂.2⟩
  -- Since |β(n₁+)| = |β(n₂+)| = p + 1 and |β(n₁)|, |β(n₂)| ≤ p, we have n₁, n₂ ∈ dom(γ).
  have hbs_le_warpAt : ∀ {n : π.S}, n ∈ π.Γ.N ∩ Θ → (π.borderSet n).ncard ≤ π.warpAt Θ := by
    exact cuff_node_border_count_le_warp (α := α) (β := β) (G := G) π (Θ := Θ) hΘ hΘ_bd hΘ_arc
  have hbs₁_le : (π.borderSet n₁).ncard ≤ p := (hbs_le_warpAt hn₁).trans hwarp
  have hbs₂_le : (π.borderSet n₂).ncard ≤ p := (hbs_le_warpAt hn₂).trans hwarp
  have hn₁_dom : n₁ ∈ π.domγ := by
    by_contra hn₁_not
    have hbp_eq : π.borderPlus n₁ = π.borderSet n₁ := by
      ext v; simp [Portrayal.borderPlus, hn₁_not]
    rw [hbp_eq] at hcard₁
    omega
  have hn₂_dom : n₂ ∈ π.domγ := by
    by_contra hn₂_not
    have hbp_eq : π.borderPlus n₂ = π.borderSet n₂ := by
      ext v; simp [Portrayal.borderPlus, hn₂_not]
    rw [hbp_eq] at hcard₂
    omega
  intro P hP_disj
  have hinj_first : Function.Injective (fun j => (P j).first) := by
    intro i j hij
    change (P i).first = (P j).first at hij
    by_contra hne_ij
    have hi_mem : (P j).first ∈ {z | z ∈ (P i).walk.support} :=
      hij ▸ SimpleGraph.Walk.start_mem_support (P i).walk
    exact Set.disjoint_left.mp (hP_disj hne_ij) hi_mem
      (SimpleGraph.Walk.start_mem_support (P j).walk)
  have hinj_last : Function.Injective (fun j => (P j).last) := by
    intro i j hij
    change (P i).last = (P j).last at hij
    by_contra hne_ij
    have hi_mem : (P j).last ∈ {z | z ∈ (P i).walk.support} :=
      hij ▸ SimpleGraph.Walk.end_mem_support (P i).walk
    exact Set.disjoint_left.mp (hP_disj hne_ij) hi_mem
      (SimpleGraph.Walk.end_mem_support (P j).walk)
  obtain ⟨j₀, hj₀_first⟩ := mem_range_of_injective_of_ncard_eq
    (π.borderPlus_finite hn₁_bd) hcard₁ (fun j => (P j).first_mem) hinj_first
    (Or.inr ⟨hn₁_dom, rfl⟩)
  refine ⟨j₀, hj₀_first, ?_⟩
  by_contra hj₀_last_ne
  obtain ⟨j₂, hj₂_last⟩ := mem_range_of_injective_of_ncard_eq
    (π.borderPlus_finite hn₂_bd) hcard₂ (fun j => (P j).last_mem) hinj_last
    (Or.inr ⟨hn₂_dom, rfl⟩)
  have hj₀_ne_j₂ : j₀ ≠ j₂ := fun h => hj₀_last_ne (h ▸ hj₂_last)
  have hn₂_not_P₀ : π.nodeVertex n₂ ∉ (P j₀).walk.support := fun hmem =>
    Set.disjoint_left.mp (hP_disj hj₀_ne_j₂) hmem
      (hj₂_last ▸ SimpleGraph.Walk.end_mem_support (P j₂).walk)
  -- Define the active node set `e d` for each cell `d` and the marking predicate `P_mark`.
  let activeFor (d : Set π.S) (l : Fin (p + 1)) : Prop :=
    2 ≤ ({z ∈ (P l).walk.support | z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}).ncard
  let e : Set π.S → Set π.S := fun d =>
    {n ∈ tilde d ∩ π.domγ | ∃ l : Fin (p + 1),
      activeFor d l ∧ π.nodeVertex n ∈ (P l).walk.support}
  let P_mark : π.S → Prop := fun m =>
    m ∈ π.domγ ∧ π.nodeVertex m ∈ (P j₀).walk.support
  have hact_unique : ∀ {d : Set π.S}, d ∈ π.Γ.C → ∀ {l₁ l₂ : Fin (p + 1)},
      activeFor d l₁ → activeFor d l₂ → l₁ = l₂ := by
    exact active_cell_unique_path (α := α) (β := β) (G := G) π (Δ := Δ) (n₁ := n₁) (n₂ :=
      n₂) (p := p) P hP_disj
  have he_props : ∀ d ∈ π.Γ.C, d ⊆ Δ → ¬ (d ∩ bd π.S).Nonempty →
      e d ⊆ tilde d ∧ (e d = ∅ ∨ 2 ≤ (e d).ncard) ∧
      ∀ x ∈ e d, ∀ y ∈ e d, P_mark x → P_mark y := by
    exact active_cell_marked_boundary (α := α) (β := β) (G := G) π (Δ := Δ) (n₁ := n₁)
      (n₂ := n₂) (p := p) P hP_disj j₀ hact_unique
  have hP_n₁ : P_mark n₁ :=
    ⟨hn₁_dom, hj₀_first ▸ SimpleGraph.Walk.start_mem_support (P j₀).walk⟩
  have hP_n₂ : ¬ P_mark n₂ := fun h => hn₂_not_P₀ h.2
  obtain ⟨m₁, m₂, c, I₁, I₂, N₁, N₂,
      hm₁_mem, hm₂_mem, hm_ne, hP_m₁, hP_m₂,
      hc_C, hc_Δ, hc_Θ, htilde_c,
      hI₁_sub, hI₂_sub, hdisj_I,
      hn₁_I₁, hm₁_I₁, hm₂_I₂, hn₂_I₂,
      hN₁_sub, hN₂_sub, hdisj_N,
      hord_I, hborder_split, hint_split,
      ⟨c₁_end, hc₁_C, hc₁_Δ, hc₁_bd, hn₁_c₁⟩,
      ⟨c₂_end, hc₂_C, hc₂_Δ, hc₂_bd, hn₂_c₂⟩⟩ :=
    GraphMinor.GM17.normalIArcDiscRegion π.S π.isSurface π.Γ Θ n₁ n₂ F Δ e P_mark
      hΘ hn₁ hn₂ hne hnorm hF hFbd hFN hΔ hF_bd hbd_sub he_props hP_n₁ hP_n₂
  have hc_bd : (c ∩ bd π.S).Nonempty := hc_Θ.mono (inter_subset_inter_right _ hΘ_bd)
  let B₁ : Set α := ⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n
  let B₂ : Set α := ⋃ n ∈ I₂ ∩ π.Γ.N, π.borderPlus n
  have hbp₁_sub_B₁ : π.borderPlus n₁ ⊆ B₁ :=
    subset_biUnion_of_mem (x := n₁) ⟨hn₁_I₁, hn₁.1⟩
  have hbp₂_sub_B₂ : π.borderPlus n₂ ⊆ B₂ :=
    subset_biUnion_of_mem (x := n₂) ⟨hn₂_I₂, hn₂.1⟩
  have hbp_m₁_sub_B₁ : π.borderPlus m₁ ⊆ B₁ :=
    subset_biUnion_of_mem (x := m₁) ⟨hm₁_I₁, hm₁_mem.1⟩
  have hbp_m₂_sub_B₂ : π.borderPlus m₂ ⊆ B₂ :=
    subset_biUnion_of_mem (x := m₂) ⟨hm₂_I₂, hm₂_mem.1⟩
  -- For each `j`, choose a minimal subpath `Q_j` of `P_j` from `B₁` to `B₂`, and show it lifts
  -- to a path in `(π.cellGraph c).skeleton` from `π.borderPlus m₁` to `π.borderPlus m₂`.
  have hclaim : ∀ j : Fin (p + 1),
      ∃ Q' : PathFromTo (π.cellGraph c).skeleton (π.borderPlus m₁) (π.borderPlus m₂),
        {z | z ∈ Q'.walk.support} ⊆ {z | z ∈ (P j).walk.support} ∧
        Q'.first ∈ B₁ ∧ Q'.last ∈ B₂ := by
    exact path_family_restricts_to_middle_cell (α := α) (β := β) (G := G) π (Θ := Θ) (Δ := Δ) (n₁
      := n₁) (n₂ := n₂) (p := p) hΘ hn₁ hn₂ hinter_sub hΘ_bd P P_mark m₁ m₂ c I₁ I₂ N₁ N₂ hm₁_mem
      hm₂_mem hm_ne hP_m₁ hP_m₂ hc_C htilde_c hI₁_sub hI₂_sub hdisj_I hm₁_I₁ hm₂_I₂ hN₁_sub
      hN₂_sub hdisj_N hord_I c₁_end hc₁_C hc₁_Δ hc₁_bd hn₁_c₁ c₂_end hc₂_C hc₂_Δ hc₂_bd hn₂_c₂
      hborder_split hint_split hc_bd hbp₁_sub_B₁ hbp₂_sub_B₂ hbp_m₁_sub_B₁ hbp_m₂_sub_B₂
  -- Assemble the linkage `{Q'_0, ..., Q'_p}` in `α(c)` from `β(m₁+)` to `β(m₂+)` (page 180).
  let Q' : Fin (p + 1) → PathFromTo (π.cellGraph c).skeleton (π.borderPlus m₁) (π.borderPlus m₂) :=
    fun j => Classical.choose (hclaim j)
  have hQ'_sub : ∀ j, {z | z ∈ (Q' j).walk.support} ⊆ {z | z ∈ (P j).walk.support} :=
    fun j => (Classical.choose_spec (hclaim j)).1
  have hQ'_disj : Pairwise fun i j =>
      Disjoint {z | z ∈ (Q' i).walk.support} {z | z ∈ (Q' j).walk.support} :=
    fun _ _ hij => (hP_disj hij).mono (hQ'_sub _) (hQ'_sub _)
  have hinj_Q'_first : Function.Injective (fun j => (Q' j).first) := by
    intro i j hij
    change (Q' i).first = (Q' j).first at hij
    by_contra hne_ij
    have hi_mem : (Q' j).first ∈ {z | z ∈ (Q' i).walk.support} :=
      hij ▸ SimpleGraph.Walk.start_mem_support (Q' i).walk
    exact Set.disjoint_left.mp (hQ'_disj hne_ij) hi_mem
      (SimpleGraph.Walk.start_mem_support (Q' j).walk)
  have hinj_Q'_last : Function.Injective (fun j => (Q' j).last) := by
    intro i j hij
    change (Q' i).last = (Q' j).last at hij
    by_contra hne_ij
    have hi_mem : (Q' j).last ∈ {z | z ∈ (Q' i).walk.support} :=
      hij ▸ SimpleGraph.Walk.end_mem_support (Q' i).walk
    exact Set.disjoint_left.mp (hQ'_disj hne_ij) hi_mem
      (SimpleGraph.Walk.end_mem_support (Q' j).walk)
  have hm₁_bd : m₁ ∈ π.Γ.N ∩ bd π.S := ⟨hm₁_mem.1, hΘ_bd hm₁_mem.2.1⟩
  have hm₂_bd : m₂ ∈ π.Γ.N ∩ bd π.S := ⟨hm₂_mem.1, hΘ_bd hm₂_mem.2.1⟩
  have hm₁_tc : m₁ ∈ tilde c := htilde_c ▸ mem_insert _ _
  have hm₂_tc : m₂ ∈ tilde c := htilde_c ▸ mem_insert_of_mem _ (mem_singleton _)
  have hcw_le : π.cellWarp c ≤ p := (π.cellWarp_le_warpAt hc_C hc_Θ).trans hwarp
  have hspec_c := π.cellWarp_spec hc_C hc_bd m₁ hm₁_tc m₂ hm₂_tc hm_ne
  have hbp_m₁_le : (π.borderPlus m₁).ncard ≤ π.cellWarp c + 1 :=
    (π.ncard_borderPlus_le hm₁_bd).trans (Nat.add_le_add_right hspec_c.1 1)
  have hbp_m₂_le : (π.borderPlus m₂).ncard ≤ π.cellWarp c + 1 :=
    (π.ncard_borderPlus_le hm₂_bd).trans (Nat.add_le_add_right hspec_c.2.1 1)
  have hbp_m₁_ge : p + 1 ≤ (π.borderPlus m₁).ncard := by
    have hsub : Set.range (fun j => (Q' j).first) ⊆ π.borderPlus m₁ := by
      rintro _ ⟨j, rfl⟩; exact (Q' j).first_mem
    have hcard_r : (Set.range (fun j => (Q' j).first)).ncard = p + 1 := by
      rw [ncard_range_of_injective hinj_Q'_first, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hcard_r ▸ ncard_le_ncard hsub (π.borderPlus_finite hm₁_bd)
  have hbp_m₂_ge : p + 1 ≤ (π.borderPlus m₂).ncard := by
    have hsub : Set.range (fun j => (Q' j).last) ⊆ π.borderPlus m₂ := by
      rintro _ ⟨j, rfl⟩; exact (Q' j).last_mem
    have hcard_r : (Set.range (fun j => (Q' j).last)).ncard = p + 1 := by
      rw [ncard_range_of_injective hinj_Q'_last, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hcard_r ▸ ncard_le_ncard hsub (π.borderPlus_finite hm₂_bd)
  have hcw_eq : π.cellWarp c = p := by omega
  have hlink_c : Portrayal.LinkagePairs (π.cellGraph c).skeleton
      (π.borderPlus m₁) (π.borderPlus m₂) (p + 1) (π.nodeVertex m₁) (π.nodeVertex m₂) := by
    have h1 : (π.borderPlus m₁).ncard = π.cellWarp c + 1 := by omega
    have h2 : (π.borderPlus m₂).ncard = π.cellWarp c + 1 := by omega
    have h0 := hspec_c.2.2 h1 h2
    rwa [hcw_eq] at h0
  have hm₂_dom : m₂ ∈ π.domγ := by
    by_contra hm₂_not
    have hbp_eq : π.borderPlus m₂ = π.borderSet m₂ := by
      ext v; simp [Portrayal.borderPlus, hm₂_not]
    rw [hbp_eq] at hbp_m₂_ge
    have := hspec_c.2.1
    omega
  obtain ⟨j₁, hj₁_first, hj₁_last⟩ := hlink_c Q' hQ'_disj
  have hj₁_eq_j₀ : j₁ = j₀ := by
    by_contra hne_j
    exact Set.disjoint_left.mp (hP_disj hne_j)
      (hQ'_sub j₁ (hj₁_first ▸ SimpleGraph.Walk.start_mem_support (Q' j₁).walk))
      hP_m₁.2
  have hm₂_in_P₀ : π.nodeVertex m₂ ∈ (P j₀).walk.support :=
    hj₁_eq_j₀ ▸ hQ'_sub j₁ (hj₁_last ▸ SimpleGraph.Walk.end_mem_support (Q' j₁).walk)
  exact hP_m₂ ⟨hm₂_dom, hm₂_in_P₀⟩

private lemma isTruer_of_le_of_lt {α : Type u} {β : Type v} {G : Hypergraph α β}
    {π' π : Portrayal G} (hle : ∀ i : Fin 6, π'.truth i ≤ π.truth i)
    (hex : ∃ k : Fin 6, π'.truth k < π.truth k) :
    π'.IsTruer π := by
  classical
  have hex_nat : ∃ n, ∃ hn : n < 6, π'.truth ⟨n, hn⟩ < π.truth ⟨n, hn⟩ := by
    rcases hex with ⟨⟨n, hn⟩, hlt⟩
    exact ⟨n, hn, hlt⟩
  let m := Nat.find hex_nat
  obtain ⟨hm6, hm_lt⟩ := Nat.find_spec hex_nat
  refine ⟨⟨m, hm6⟩, fun i hi => ?_, hm_lt⟩
  apply le_antisymm (hle i)
  by_contra hlt
  exact Nat.find_min hex_nat hi ⟨i.2, lt_of_not_ge hlt⟩

open Classical in
private noncomputable abbrev replaced_cuff_disc_portrayal
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    (Γ' : Painting π.S)
    (hdich : ∀ c ∈ π.Γ.C, c ⊆ Δ ∨ c ⊆ Δᶜ)
    (htilde_I₂ : ∀ c ∈ π.Γ.C, c ⊆ Δᶜ → tilde c ⊆ Γ'.N)
    (hc'_mem : Δ \ {n₁, n₂} ∈ Γ'.C)
    (hC' : Γ'.C = insert (Δ \ {n₁, n₂}) {c | c ∈ π.Γ.C ∧ c ⊆ Δᶜ})
    (hc'_not_I₂ : Δ \ {n₁, n₂} ∉ {c | c ∈ π.Γ.C ∧ c ⊆ Δᶜ})
    (hc'_bd : ((Δ \ {n₁, n₂}) ∩ bd π.S).Nonempty)
    (hN'_sub : Γ'.N ⊆ π.Γ.N)
    (hdisj_I : Disjoint {c ∈ π.Γ.C | c ⊆ Δ} {c ∈ π.Γ.C | c ⊆ Δᶜ})
    (hbp_c'_sub_Δ : ∀ {n : π.S}, n ∈ tilde (Δ \ {n₁, n₂}) →
      π.borderPlus n ⊆ (π.areaGraph Δ).vertexSet)
    (htilde_c'_N' : tilde (Δ \ {n₁, n₂}) ⊆ Γ'.N ∩ bd π.S)
    (hinter_I₁_I₂ : (π.areaGraph Δ).vertexSet ∩
      (π.cellsUnion {c ∈ π.Γ.C | c ⊆ Δᶜ}).vertexSet ⊆
        ⋃ n ∈ tilde (Δ \ {n₁, n₂}), π.borderPlus n) : Portrayal G :=
  let c' := Δ \ {n₁, n₂}
  let I₁ : Set (Set π.S) := {c ∈ π.Γ.C | c ⊆ Δ}
  let I₂ : Set (Set π.S) := {c ∈ π.Γ.C | c ⊆ Δᶜ}
  let cellG : Set π.S → Hypergraph α β := fun c =>
    if c = c' then π.areaGraph Δ else π.cellGraph c
  { S := π.S
    top := π.top
    isSurface := π.isSurface
    connected := π.connected
    Γ := Γ'
    cellGraph := cellG
    borderSet := π.borderSet
    domγ := π.domγ ∩ Γ'.N
    nodeVertex := π.nodeVertex
    cellGraph_le := fun c hc => by
      rw [hC'] at hc
      dsimp only [cellG]
      split_ifs with hcc'
      · exact π.cellsUnion_le I₁
      · exact π.cellGraph_le c (hc.resolve_left hcc').1
    borderSet_subset := fun n hn => π.borderSet_subset n ⟨hN'_sub hn.1, hn.2⟩
    domγ_subset := inter_subset_right
    nodeVertex_mem := fun n hn => π.nodeVertex_mem n hn.1
    nodeVertex_injOn := π.nodeVertex_injOn.mono inter_subset_left
    p1_vertex := fun v hv => by
      rcases π.p1_vertex v hv with ⟨c, hc, hvc⟩
      rcases hdich c hc with hc_in | hc_out
      · refine ⟨c', hc'_mem, ?_⟩
        change v ∈ (if c' = c' then π.areaGraph Δ else π.cellGraph c').vertexSet
        simp only [↓reduceIte]
        exact mem_biUnion ⟨⟨hc, hc_in⟩, hc⟩ hvc
      · refine ⟨c, hC'.symm ▸ mem_insert_of_mem c' ⟨hc, hc_out⟩, ?_⟩
        have hne_c : c ≠ c' := by rintro rfl; exact hc'_not_I₂ ⟨hc, hc_out⟩
        dsimp only [cellG]
        rw [ite_eq_right hne_c]
        exact hvc
    p1_edge := fun e he => by
      rcases π.p1_edge e he with ⟨c, hc, hec⟩
      rcases hdich c hc with hc_in | hc_out
      · refine ⟨c', hc'_mem, ?_⟩
        change e ∈ (if c' = c' then π.areaGraph Δ else π.cellGraph c').edgeSet
        simp only [↓reduceIte]
        exact mem_biUnion ⟨⟨hc, hc_in⟩, hc⟩ hec
      · refine ⟨c, hC'.symm ▸ mem_insert_of_mem c' ⟨hc, hc_out⟩, ?_⟩
        have hne_c : c ≠ c' := by rintro rfl; exact hc'_not_I₂ ⟨hc, hc_out⟩
        dsimp only [cellG]
        rw [ite_eq_right hne_c]
        exact hec
    p1_disjoint := fun c₁ hc₁ c₂ hc₂ hne_c => by
      rw [hC'] at hc₁ hc₂
      dsimp only [cellG]
      split_ifs with h1 h2 h2
      · exact False.elim (hne_c (h1.trans h2.symm))
      · have hc₂' : c₂ ∈ I₂ := hc₂.resolve_left h2
        rw [Set.disjoint_left]
        intro e he₁ he₂
        change e ∈ ⋃ d ∈ _, _ at he₁
        rw [mem_iUnion₂] at he₁
        rcases he₁ with ⟨c₀, hc₀, hec₀⟩
        have hc₀_ne : c₀ ≠ c₂ := fun h => Set.disjoint_left.mp hdisj_I hc₀.1 (h ▸ hc₂')
        exact Set.disjoint_left.mp (π.p1_disjoint c₀ hc₀.2 c₂ hc₂'.1 hc₀_ne) hec₀ he₂
      · have hc₁' : c₁ ∈ I₂ := hc₁.resolve_left h1
        rw [Set.disjoint_left]
        intro e he₁ he₂
        change e ∈ ⋃ d ∈ _, _ at he₂
        rw [mem_iUnion₂] at he₂
        rcases he₂ with ⟨c₀, hc₀, hec₀⟩
        have hc₁_ne : c₁ ≠ c₀ := fun h => Set.disjoint_left.mp hdisj_I hc₀.1 (h ▸ hc₁')
        exact Set.disjoint_left.mp (π.p1_disjoint c₁ hc₁'.1 c₀ hc₀.2 hc₁_ne) he₁ hec₀
      · exact π.p1_disjoint c₁ (hc₁.resolve_left h1).1 c₂ (hc₂.resolve_left h2).1 hne_c
    p2 := fun c hc n hn => by
      rw [hC'] at hc
      dsimp only [cellG]
      split_ifs with hcc'
      · subst hcc'
        exact hbp_c'_sub_Δ hn.1 (Or.inr ⟨hn.2.1, rfl⟩)
      · exact π.p2 c (hc.resolve_left hcc').1 n ⟨hn.1, hn.2.1⟩
    p3_notMem := fun n hn => π.p3_notMem n ⟨hn.1.1, hn.2⟩
    p3_subset := fun c hc hbd n hnt v hv => by
      rw [hC'] at hc
      dsimp only [cellG]
      split_ifs with hcc'
      · subst hcc'
        exact hbp_c'_sub_Δ hnt (Or.inl hv)
      · exact π.p3_subset c (hc.resolve_left hcc').1 hbd n hnt hv
    p4_disjoint := fun Θ₁ hΘ₁ Θ₂ hΘ₂ hne_Θ u₁ hu₁ u₂ hu₂ =>
      π.p4_disjoint Θ₁ hΘ₁ Θ₂ hΘ₂ hne_Θ u₁ ⟨hN'_sub hu₁.1, hu₁.2⟩ u₂ ⟨hN'_sub hu₂.1, hu₂.2⟩
    p4_notMem := fun Θ' hΘ' u₁ hu₁ u₂ hu₂ hnot =>
      π.p4_notMem Θ' hΘ' u₁ ⟨hN'_sub hu₁.1, hu₁.2⟩ u₂ hu₂.1 hnot
    p5 := fun c hc hint v hvc hex => by
      have hne_c : c ≠ c' := fun h => hint (h ▸ hc'_bd)
      have hc_I₂ : c ∈ I₂ := (hC' ▸ hc).resolve_left hne_c
      dsimp only [cellG] at hvc
      rw [ite_eq_right hne_c] at hvc
      rcases hex with ⟨d', hd', hd'_ne, hvd'⟩
      have hex_π : ∃ d₀ ∈ π.Γ.C, d₀ ≠ c ∧ v ∈ (π.cellGraph d₀).vertexSet := by
        dsimp only [cellG] at hvd'
        split_ifs at hvd' with hd'_eq
        · change v ∈ ⋃ d₀ ∈ _, _ at hvd'
          rw [mem_iUnion₂] at hvd'
          rcases hvd' with ⟨d₀, hd₀, hvd₀⟩
          exact ⟨d₀, hd₀.2, fun h => Set.disjoint_left.mp hdisj_I hd₀.1 (h ▸ hc_I₂), hvd₀⟩
        · have hd'_I₂ : d' ∈ I₂ := (hC' ▸ hd').resolve_left hd'_eq
          exact ⟨d', hd'_I₂.1, hd'_ne, hvd'⟩
      obtain ⟨n, ⟨hnt, hndom⟩, hnv⟩ := π.p5 c hc_I₂.1 hint v hvc hex_π
      exact ⟨n, ⟨hnt, hndom, htilde_I₂ c hc_I₂.1 hc_I₂.2 hnt⟩, hnv⟩
    p6 := fun c hc hbd v hvc hex => by
      rcases hex with ⟨d', hd', hd'_ne, hvd'⟩
      by_cases hcc' : c = c'
      · subst hcc'
        dsimp only [cellG] at hvc hvd'
        simp only [↓reduceIte] at hvc
        rw [ite_eq_right hd'_ne] at hvd'
        have hd'_I₂ : d' ∈ I₂ := (hC' ▸ hd').resolve_left hd'_ne
        have hv₂ : v ∈ (π.cellsUnion I₂).vertexSet :=
          mem_biUnion ⟨hd'_I₂, hd'_I₂.1⟩ hvd'
        have hv_in := hinter_I₁_I₂ ⟨hvc, hv₂⟩
        rw [mem_iUnion₂] at hv_in
        rcases hv_in with ⟨n, hnt, hvn⟩
        have hn_N' : n ∈ Γ'.N ∩ bd π.S := htilde_c'_N' hnt
        refine ⟨n, hnt, ?_⟩
        rcases hvn with hv_bs | ⟨hn_dom, hnv⟩
        · exact Or.inl hv_bs
        · exact Or.inr ⟨⟨hn_dom, hn_N'.1⟩, hnv⟩
      · have hc_I₂ : c ∈ I₂ := (hC' ▸ hc).resolve_left hcc'
        dsimp only [cellG] at hvc hvd'
        rw [ite_eq_right hcc'] at hvc
        have hex_π : ∃ d₀ ∈ π.Γ.C, d₀ ≠ c ∧ v ∈ (π.cellGraph d₀).vertexSet := by
          split_ifs at hvd' with hd'_eq
          · change v ∈ ⋃ d₀ ∈ _, _ at hvd'
            rw [mem_iUnion₂] at hvd'
            rcases hvd' with ⟨d₀, hd₀, hvd₀⟩
            exact ⟨d₀, hd₀.2, fun h => Set.disjoint_left.mp hdisj_I hd₀.1 (h ▸ hc_I₂), hvd₀⟩
          · have hd'_I₂ : d' ∈ I₂ := (hC' ▸ hd').resolve_left hd'_eq
            exact ⟨d', hd'_I₂.1, hd'_ne, hvd'⟩
        obtain ⟨n, hnt, hvn⟩ := π.p6 c hc_I₂.1 hbd v hvc hex_π
        have hn_N' : n ∈ Γ'.N := htilde_I₂ c hc_I₂.1 hc_I₂.2 hnt
        refine ⟨n, hnt, ?_⟩
        rcases hvn with hv_bs | ⟨hn_dom, hnv⟩
        · exact Or.inl hv_bs
        · exact Or.inr ⟨⟨hn_dom, hn_N'⟩, hnv⟩
    p7 := fun Θ' hΘ' u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ hord v hv₁ hv₃ => by
      have hv₁' : v ∈ π.borderPlus u₁ :=
        hv₁.imp id (fun ⟨h, hv⟩ => ⟨h.1, hv⟩)
      have hv₃' : v ∈ π.borderPlus u₃ :=
        hv₃.imp id (fun ⟨h, hv⟩ => ⟨h.1, hv⟩)
      rcases π.p7 Θ' hΘ' u₁ ⟨hN'_sub hu₁.1, hu₁.2⟩ u₂ ⟨hN'_sub hu₂.1, hu₂.2⟩
        u₃ ⟨hN'_sub hu₃.1, hu₃.2⟩ u₄ ⟨hN'_sub hu₄.1, hu₄.2⟩ hord v hv₁' hv₃' with h₂ | h₄
      · exact Or.inl (h₂.imp id (fun ⟨h, hv⟩ => ⟨⟨h, hu₂.1⟩, hv⟩))
      · exact Or.inr (h₄.imp id (fun ⟨h, hv⟩ => ⟨⟨h, hu₄.1⟩, hv⟩)) }

private theorem cuff_disc_area_links_ends
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    {θ : ℕ}
    {p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯)
    (π : Portrayal G)
    (hc : π.IsCentral 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p) (hθ : 4 * p + 5 < θ)
    {F : Set π.S}
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    (hnorm : π.Γ.IsNormal F)
    (hF : IsLineWithEnds F n₁ n₂)
    (hFbd : F ∩ bd π.S = {n₁, n₂})
    (hFN : F ∩ π.Γ.N = {n₁, n₂})
    (hΔ : IsClosedDisc Δ)
    (hF_bd : F ⊆ discBd Δ)
    (hbd_sub : discBd Δ ⊆ F ∪ bd π.S)
    (hsmall : IsSmallWrt 𝒯 (π.areaGraph Δ))
    (hne : n₁ ≠ n₂)
    (Θ : Set π.S)
    (hΘ : Θ ∈ cuffs π.S)
    (hbd_Θ : discBd Δ ⊆ F ∪ Θ)
    (hΘ_bd : Θ ⊆ bd π.S)
    (hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S)
    (hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S)
    (hbs_le_q : ∀ {n : π.S}, n ∈ π.Γ.N ∩ Θ → (π.borderSet n).ncard ≤ (π.warpAt Θ))
    (u₁ : π.S)
    (u₂ : π.S)
    (hu_ne : u₁ ≠ u₂)
    (hu₁_pair : u₁ = n₁ ∨ u₁ = n₂)
    (hu₂_pair : u₂ = n₁ ∨ u₂ = n₂)
    (hu₁_Θ : u₁ ∈ π.Γ.N ∩ Θ)
    (hu₂_Θ : u₂ ∈ π.Γ.N ∩ Θ)
    (hu₁_bd : u₁ ∈ π.Γ.N ∩ bd π.S)
    (hu₂_bd : u₂ ∈ π.Γ.N ∩ bd π.S)
    (hcard₁ : (π.borderPlus u₁).ncard = (π.warpAt Θ) + 1)
    (hcard₂ : (π.borderPlus u₂).ncard = (π.warpAt Θ) + 1) :
    Portrayal.LinkagePairs (π.areaGraph Δ).skeleton (π.borderPlus u₁) (π.borderPlus u₂) ((π.warpAt
      Θ) + 1) (π.nodeVertex u₁) (π.nodeVertex u₂) := by
  let q := π.warpAt Θ
  by_cases hq0 : q = 0
  · -- When `q = 0`, `borderSet u₁ = borderSet u₂ = ∅`, so any 1-linkage trivially pairs `γ(u₁)`
    -- and `γ(u₂)`.
    have hbs₁_le : (π.borderSet u₁).ncard ≤ 0 := hq0 ▸ hbs_le_q hu₁_Θ
    have hbs₂_le : (π.borderSet u₂).ncard ≤ 0 := hq0 ▸ hbs_le_q hu₂_Θ
    have hbs₁_emp : π.borderSet u₁ = ∅ :=
      (ncard_eq_zero (hs := π.borderSet_finite hu₁_bd)).mp (Nat.eq_zero_of_le_zero hbs₁_le)
    have hbs₂_emp : π.borderSet u₂ = ∅ :=
      (ncard_eq_zero (hs := π.borderSet_finite hu₂_bd)).mp (Nat.eq_zero_of_le_zero hbs₂_le)
    have hu₁_dom : u₁ ∈ π.domγ := by
      by_contra hnot
      have hbp_eq : π.borderPlus u₁ = π.borderSet u₁ := by
        ext v; simp [Portrayal.borderPlus, hnot]
      rw [hbp_eq, hbs₁_emp, ncard_empty] at hcard₁
      omega
    have hu₂_dom : u₂ ∈ π.domγ := by
      by_contra hnot
      have hbp_eq : π.borderPlus u₂ = π.borderSet u₂ := by
        ext v; simp [Portrayal.borderPlus, hnot]
      rw [hbp_eq, hbs₂_emp, ncard_empty] at hcard₂
      omega
    have hbp₁_eq : π.borderPlus u₁ = {π.nodeVertex u₁} := by
      ext v; simp [Portrayal.borderPlus, hbs₁_emp, hu₁_dom]
    have hbp₂_eq : π.borderPlus u₂ = {π.nodeVertex u₂} := by
      ext v; simp [Portrayal.borderPlus, hbs₂_emp, hu₂_dom]
    intro L _
    have hf0 : (L 0).first = π.nodeVertex u₁ :=
      mem_singleton_iff.mp (hbp₁_eq ▸ (L 0).first_mem)
    have hl0 : (L 0).last = π.nodeVertex u₂ :=
      mem_singleton_iff.mp (hbp₂_eq ▸ (L 0).last_mem)
    exact ⟨0, hf0, hl0⟩
  · -- When `1 ≤ q`, we have `1 ≤ q ≤ π.warp ≤ p`, so `(6.7)` and `(7.3)` apply.
    have hq_le_warp : q ≤ π.warp := π.warpAt_le_warp hΘ
    have hq_le_p : q ≤ p := hq_le_warp.trans hwarp
    have hwarp_ge_1 : 1 ≤ π.warp := by omega
    have hp_ge_1 : 1 ≤ p := by omega
    have hθ_67 : (2 * p + 3) + max 3 (2 * p + 2) < θ := by omega
    have hpair_eq : ({u₁, u₂} : Set π.S) = {n₁, n₂} := by
      rcases hu₁_pair with h1 | h1 <;> rcases hu₂_pair with h2 | h2
      · exact False.elim (hu_ne (h1.trans h2.symm))
      · rw [h1, h2]
      · rw [h1, h2]; exact pair_comm n₂ n₁
      · exact False.elim (hu_ne (h1.trans h2.symm))
    have hF_u : IsLineWithEnds F u₁ u₂ := by
      rcases hu₁_pair with h1 | h1 <;> rcases hu₂_pair with h2 | h2
      · exact False.elim (hu_ne (h1.trans h2.symm))
      · rw [h1, h2]; exact hF
      · rw [h1, h2]; exact isLineWithEnds_symm hF
      · exact False.elim (hu_ne (h1.trans h2.symm))
    have hFbd_u : F ∩ bd π.S = {u₁, u₂} := hFbd.trans hpair_eq.symm
    have hFN_u : F ∩ π.Γ.N = {u₁, u₂} := hFN.trans hpair_eq.symm
    have hFγ_le : 2 * p + 1 ≤ 2 * p + 3 ∧ (F ∩ π.domγ).ncard ≤ (2 * p + 3) - 2 * p - 1 := by
      refine ⟨by omega, ?_⟩
      have hsub_Fγ : F ∩ π.domγ ⊆ {n₁, n₂} :=
        (inter_subset_inter_right F π.domγ_subset).trans hFN.subset
      have hfin_pair : ({n₁, n₂} : Set π.S).Finite := (finite_singleton n₂).insert n₁
      have hle2 : (F ∩ π.domγ).ncard ≤ 2 :=
        (ncard_le_ncard hsub_Fγ hfin_pair).trans (ncard_pair hne).le
      omega
    have hinter_bd : ∀ n ∈ π.Γ.N ∩ discBd Δ,
        π.borderPlus u₁ ∩ π.borderPlus u₂ ⊆ π.borderPlus n := by
      rintro n ⟨hnN, hnbd⟩
      have hnΔ : n ∈ Δ := discBd_subset Δ hnbd
      have hn_bdS : n ∈ bd π.S := by
        rcases hbd_Θ hnbd with hnF | hnΘ
        · have hn_pair : n ∈ ({n₁, n₂} : Set π.S) := hFN ▸ ⟨hnF, hnN⟩
          rcases hn_pair with rfl | rfl <;> [exact hn₁_bd.2; exact hn₂_bd.2]
        · exact hΘ_bd hnΘ
      exact theorem_6_7_proof h𝒯 π hc hwarp hred hθ_67
        hnorm hF_u hFbd_u hFγ_le hΔ hF_bd hbd_sub hsmall
        ⟨⟨hnN, hnΔ⟩, hn_bdS⟩
    exact theorem_7_3_proof π hΘ hu₁_Θ hu₂_Θ hu_ne hnorm hF_u hFbd_u hFN_u
      hΔ hF_bd hbd_Θ hinter_bd le_rfl hcard₁ hcard₂

private theorem single_cell_in_disc_with_two_boundary_nodes
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    (Θ : Set π.S)
    (hΔ_bd : Δ ∩ bd π.S = discBd Δ ∩ Θ)
    (hF' : IsLineWithEnds (discBd Δ ∩ Θ) n₁ n₂)
    (hdich : ∀ c ∈ π.Γ.C, c ⊆ Δ ∨ c ⊆ Δᶜ)
    (hΘ_bd : Θ ⊆ bd π.S)
    (hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S)
    (hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S)
    (hI₁_border : ∀ c ∈ ({c | c ∈ π.Γ.C ∧ c ⊆ Δ}), (c ∩ bd π.S).Nonempty)
    (hΔ_N_pair : Δ ∩ π.Γ.N ⊆ {n₁, n₂}) :
    ({c | c ∈ π.Γ.C ∧ c ⊆ Δ}).ncard = 1 := by
  let F' := discBd Δ ∩ Θ
  let I₁ := {c | c ∈ π.Γ.C ∧ c ⊆ Δ}
  obtain ⟨⟨x₀, hx₀_F', hx₀_ne⟩, hL_pc⟩ := isPathConnected_diff_ends_of_isLineWithEnds hF'
  have hL_sub : F' \ {n₁, n₂} ⊆ bd π.S \ π.Γ.N := by
    rintro x ⟨hxF', hx_ne⟩
    have hxΔ : x ∈ Δ := discBd_subset Δ hxF'.1
    have hxbd : x ∈ bd π.S := hΘ_bd hxF'.2
    exact ⟨hxbd, fun hxN => hx_ne (hΔ_N_pair ⟨hxΔ, hxN⟩)⟩
  have hL_sub_U : F' \ {n₁, n₂} ⊆ π.Γ.U \ π.Γ.N :=
    hL_sub.trans (sdiff_subset_sdiff π.Γ.bd_subset Subset.rfl)
  obtain ⟨c₀, ⟨hc₀_C, hx₀_c₀⟩, _⟩ :=
    π.Γ.exists_border_cell_of_mem_bd (hL_sub ⟨hx₀_F', hx₀_ne⟩)
  have hc₀_Δ : c₀ ⊆ Δ := by
    rcases hdich c₀ hc₀_C with hc₀_in | hc₀_out
    · exact hc₀_in
    · exact False.elim (hc₀_out hx₀_c₀ (discBd_subset Δ hx₀_F'.1))
  have hI₁_eq_singleton : I₁ = {c₀} := by
    ext c
    simp only [mem_singleton_iff]
    refine ⟨fun hc => ?_, fun h => h ▸ ⟨hc₀_C, hc₀_Δ⟩⟩
    obtain ⟨y, hy_c, hy_bd⟩ := hI₁_border c hc
    have hy_F' : y ∈ F' := by
      change y ∈ discBd Δ ∩ Θ
      rw [← hΔ_bd]
      exact ⟨hc.2 hy_c, hy_bd⟩
    have hy_not_N : y ∉ π.Γ.N := (π.Γ.cell_subset_diff hc.1 hy_c).2
    have hy_ne : y ∉ ({n₁, n₂} : Set π.S) := by
      rintro (rfl | rfl)
      · exact hy_not_N hn₁_bd.1
      · exact hy_not_N hn₂_bd.1
    have hy_c₀ : y ∈ c₀ :=
      subset_arcComponent_of_isPathConnected hc₀_C hL_sub_U hL_pc
        ⟨x₀, ⟨hx₀_F', hx₀_ne⟩, hx₀_c₀⟩ ⟨hy_F', hy_ne⟩
    exact π.Γ.cell_eq_of_mem hc.1 hc₀_C hy_c hy_c₀
  change I₁.ncard = 1
  rw [hI₁_eq_singleton, ncard_singleton]

private theorem disc_has_no_internal_cells_or_new_nodes_of_count_eq
    {S : Type} [TopologicalSpace S] (Γ Γ' : Painting S) {Δ : Set S} {n₁ n₂ : S}
    (hC' : Γ'.C = insert (Δ \ {n₁, n₂}) {c ∈ Γ.C | c ⊆ Δᶜ})
    (hc'_bd : ((Δ \ {n₁, n₂}) ∩ bd S).Nonempty)
    (hN'_eq : Γ'.N = Γ.N \ Δ ∪ {n₁, n₂})
    (hdisj_I : Disjoint {c ∈ Γ.C | c ⊆ Δ} {c ∈ Γ.C | c ⊆ Δᶜ})
    (hsub : ∀ i : Fin 6, i.1 < 4 →
      {c ∈ Γ'.C | ¬(c ∩ bd S).Nonempty ∧ (tilde c).ncard = 3 - i.1} ⊆
        {c ∈ Γ.C | ¬(c ∩ bd S).Nonempty ∧ (tilde c).ncard = 3 - i.1})
    (hcells : ∀ i : Fin 6, i.1 < 4 →
      {c ∈ Γ'.C | ¬(c ∩ bd S).Nonempty ∧ (tilde c).ncard = 3 - i.1}.ncard =
        {c ∈ Γ.C | ¬(c ∩ bd S).Nonempty ∧ (tilde c).ncard = 3 - i.1}.ncard)
    (hint_nodes : (Γ'.N \ bd S).ncard = (Γ.N \ bd S).ncard)
    (hbd_nodes : (Γ'.N ∩ bd S).ncard = (Γ.N ∩ bd S).ncard)
    (hN'_sub : Γ'.N ⊆ Γ.N) :
    (∀ c ∈ {c ∈ Γ.C | c ⊆ Δ}, (c ∩ bd S).Nonempty) ∧ Δ ∩ Γ.N ⊆ {n₁, n₂} := by
  constructor
  · intro c ⟨hc, hcΔ⟩
    by_contra hint
    have hcard_le := Γ.ncard_tilde_cell_le hc
    let i : Fin 6 := ⟨3 - (tilde c).ncard, by omega⟩
    have hi : i.1 < 4 := by dsimp [i]; omega
    have hEq := eq_of_subset_of_ncard_le (hsub i hi) (hcells i hi).ge
      (Γ.finite_cells.subset fun _ h => h.1)
    have hc_rhs : c ∈ {d ∈ Γ.C | ¬(d ∩ bd S).Nonempty ∧ (tilde d).ncard = 3 - i.1} :=
      ⟨hc, hint, by dsimp [i]; omega⟩
    have hc' := hEq.symm ▸ hc_rhs
    have hne : c ≠ Δ \ {n₁, n₂} := fun h => hint (h ▸ hc'_bd)
    exact Set.disjoint_left.mp hdisj_I ⟨hc, hcΔ⟩ ((hC' ▸ hc'.1).resolve_left hne)
  · have hint_eq := eq_of_subset_of_ncard_le (sdiff_subset_sdiff hN'_sub Subset.rfl) hint_nodes.ge
      (Γ.finite_N.subset sdiff_subset)
    have hbd_eq := eq_of_subset_of_ncard_le (inter_subset_inter_left (bd S) hN'_sub) hbd_nodes.ge
      (Γ.finite_N.subset inter_subset_left)
    rintro x ⟨hxΔ, hxN⟩
    have hxN' : x ∈ Γ'.N := by
      by_cases hx : x ∈ bd S
      · exact (hbd_eq.symm ▸ (show x ∈ Γ.N ∩ bd S from ⟨hxN, hx⟩)).1
      · exact (hint_eq.symm ▸ (show x ∈ Γ.N \ bd S from ⟨hxN, hx⟩)).1
    rw [hN'_eq] at hxN'
    rcases hxN' with ⟨_, hx⟩ | hx
    · exact (hx hxΔ).elim
    · exact hx

private theorem cuff_disc_area_intersects_outer_cells_at_border
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    (hΔ : IsClosedDisc Δ)
    [T2Space π.S]
    (Γ' : Painting π.S)
    (hN'_eq : Γ'.N = π.Γ.N \ Δ ∪ {n₁, n₂})
    (htilde_I₂ : ∀ c ∈ π.Γ.C, c ⊆ Δᶜ → tilde c ⊆ Γ'.N)
    (htilde_c' : tilde (Δ \ {n₁, n₂}) = {n₁, n₂})
    (hpart : ({c | c ∈ π.Γ.C ∧ c ⊆ Δ}) ∪ ({c | c ∈ π.Γ.C ∧ c ⊆ Δᶜ}) = π.Γ.C)
    (hdisj_I : Disjoint ({c | c ∈ π.Γ.C ∧ c ⊆ Δ}) ({c | c ∈ π.Γ.C ∧ c ⊆ Δᶜ})) :
    (π.areaGraph Δ).vertexSet ∩ (π.cellsUnion ({c | c ∈ π.Γ.C ∧ c ⊆ Δᶜ})).vertexSet ⊆ ⋃ n ∈ tilde
      (Δ \ {n₁, n₂}), π.borderPlus n := by
  let c' := Δ \ {n₁, n₂}
  let I₁ := {c | c ∈ π.Γ.C ∧ c ⊆ Δ}
  let I₂ := {c | c ∈ π.Γ.C ∧ c ⊆ Δᶜ}
  have hv_inter := theorem_2_1_claim_3 π hpart hdisj_I
  have hX_inter : (⋃ c ∈ I₁, tilde c) ∩ (⋃ c ∈ I₂, tilde c) ⊆ tilde c' := by
    rintro n ⟨hX₁, hX₂⟩
    rw [mem_iUnion₂] at hX₁ hX₂
    rcases hX₁ with ⟨c₁, hc₁, hnc₁⟩
    rcases hX₂ with ⟨c₂, hc₂, hnc₂⟩
    have hnΔ : n ∈ Δ := closure_minimal hc₁.2 (isClosed_of_isClosedDisc hΔ) hnc₁.1
    have hnN' : n ∈ Γ'.N := htilde_I₂ c₂ hc₂.1 hc₂.2 hnc₂
    rw [hN'_eq] at hnN'
    rcases hnN' with ⟨_, hn_notΔ⟩ | hn_pair
    · exact False.elim (hn_notΔ hnΔ)
    · exact htilde_c'.symm ▸ hn_pair
  intro v hv
  rcases hv_inter hv with ⟨n, ⟨hX, hn_dom⟩, rfl⟩ | hY
  · exact mem_biUnion (hX_inter hX) (Or.inr ⟨hn_dom, rfl⟩)
  · rw [mem_iUnion₂] at hY
    rcases hY with ⟨n, ⟨hY₁, hY₂⟩, hvn⟩
    have hnX₁ : n ∈ ⋃ c ∈ I₁, tilde c := by
      rw [mem_iUnion₂] at hY₁ ⊢
      rcases hY₁ with ⟨c₁, ⟨hc₁, _⟩, hnc₁⟩
      exact ⟨c₁, hc₁, hnc₁⟩
    have hnX₂ : n ∈ ⋃ c ∈ I₂, tilde c := by
      rw [mem_iUnion₂] at hY₂ ⊢
      rcases hY₂ with ⟨c₂, ⟨hc₂, _⟩, hnc₂⟩
      exact ⟨c₂, hc₂, hnc₂⟩
    exact mem_biUnion (hX_inter ⟨hnX₁, hnX₂⟩) (Or.inl hvn)

private theorem cells_partitioned_by_disc
    {S : Type} [TopologicalSpace S] (Γ : Painting S) {Δ : Set S}
    (hdich : ∀ c ∈ Γ.C, c ⊆ Δ ∨ c ⊆ Δᶜ) :
    {c ∈ Γ.C | c ⊆ Δ} ∪ {c ∈ Γ.C | c ⊆ Δᶜ} = Γ.C ∧
      Disjoint {c ∈ Γ.C | c ⊆ Δ} {c ∈ Γ.C | c ⊆ Δᶜ} := by
  constructor
  · refine Subset.antisymm (union_subset (fun _ h => h.1) (fun _ h => h.1)) fun c hc => ?_
    rcases hdich c hc with hc_in | hc_out
    · exact Or.inl ⟨hc, hc_in⟩
    · exact Or.inr ⟨hc, hc_out⟩
  · rw [Set.disjoint_left]
    intro c hc₁ hc₂
    obtain ⟨x, hx⟩ := Γ.cell_nonempty hc₁.1
    exact hc₂.2 hx (hc₁.2 hx)

/-- **Graph Minors XVII, (7.4)** (page 180):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a $(2p+3)$-redundant $\mathcal{T}$-central
portrayal of a hypergraph $G$, with warp $\le p$, and let $ord(\mathcal{T}) > 4p+5$. Let $F
\subseteq \Sigma$ be a $\Gamma$-normal $1$-arc with $|F \cap N(\Gamma)| = 2$. Let $\Delta \subseteq
\Sigma$ be a disc with $F \subseteq bd(\Delta) \subseteq F \cup bd(\Sigma)$, such that
$\alpha(\Delta)$ is small. Define $\Gamma' = (U(\Gamma) \cup \Delta, N(\Gamma) \cap \overline{\Sigma
- \Delta})$ and let $c'$ be the cell $\Delta - (F \cap N(\Gamma))$. Define
$$ \begin{aligned} \alpha'(c') &= \alpha(\Delta) \\ \alpha'(c) &= \alpha(c) \quad (c \in C(\Gamma')
- \{c'\}) \\ \beta' &= \beta \mid (N(\Gamma') \cap bd(\Sigma)) \\ \gamma' &= \gamma \mid N(\Gamma').
\end{aligned} $$
Then $\pi' = (\Sigma, \Gamma', \alpha', \beta', \gamma')$ is a $\mathcal{T}$-central portrayal of
$G$ resembling $\pi$."

Furthermore, either $\pi'$ is truer than $\pi$, or $\Delta \cap N(\Gamma) \subseteq F$ and $\Delta$
includes exactly one cell of $\Gamma$ (used in `(8.3)`). -/
theorem theorem_7_4_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯)
    (π : Portrayal G)
    (hc : π.IsCentral 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    {F Δ : Set π.S} {n₁ n₂ : π.S}
    (hnorm : π.Γ.IsNormal F) (hF : IsLineWithEnds F n₁ n₂)
    (hFbd : F ∩ bd π.S = {n₁, n₂}) (hFN : F ∩ π.Γ.N = {n₁, n₂})
    (hΔ : IsClosedDisc Δ) (hF_bd : F ⊆ discBd Δ) (hbd_sub : discBd Δ ⊆ F ∪ bd π.S)
    (hsmall : IsSmallWrt 𝒯 (π.areaGraph Δ)) :
    ∃ π' : Portrayal G,
      π'.IsCentral 𝒯 ∧
      π'.Resembles π ∧
      (π'.IsTruer π ∨ (Δ ∩ π.Γ.N ⊆ F ∧ {c ∈ π.Γ.C | c ⊆ Δ}.ncard = 1)) := by
  classical
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have hne : n₁ ≠ n₂ := ne_of_isLineWithEnds hF
  obtain ⟨Γ', Θ, F'',
      hU', hN'_cl, hN'_eq, hΘ, hn₁_Θ, hn₂_Θ, hbd_Θ, hΔ_bd, hF', hF''_line, hF''_boundary,
      hF''_pair, _, hdich, htilde_I₂,
      hc'_mem, hc'_Θ, htilde_c', hC', hc'_not_I₂,
      ⟨c₁_end, hc₁_C, hc₁_Δ, hc₁_bd, hn₁_c₁⟩,
      ⟨c₂_end, hc₂_C, hc₂_Δ, hc₂_bd, hn₂_c₂⟩⟩ :=
    GraphMinor.GM17.normalIArcReplaceDisc π.S π.isSurface π.Γ n₁ n₂ F Δ hnorm hF hFbd hFN hΔ hF_bd
      hbd_sub
  let c' := Δ \ {n₁, n₂}
  let F' := discBd Δ ∩ Θ
  let I₁ : Set (Set π.S) := {c ∈ π.Γ.C | c ⊆ Δ}
  let I₂ : Set (Set π.S) := {c ∈ π.Γ.C | c ⊆ Δᶜ}
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hc'_bd : (c' ∩ bd π.S).Nonempty := hc'_Θ.mono (inter_subset_inter_right _ hΘ_bd)
  have hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S := ⟨hn₁_Θ.1, hΘ_bd hn₁_Θ.2⟩
  have hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S := ⟨hn₂_Θ.1, hΘ_bd hn₂_Θ.2⟩
  have hN'_sub : Γ'.N ⊆ π.Γ.N := hN'_cl ▸ inter_subset_left
  have hn₁_N' : n₁ ∈ Γ'.N ∩ bd π.S := ⟨hN'_eq ▸ Or.inr (mem_insert _ _), hn₁_bd.2⟩
  have hn₂_N' : n₂ ∈ Γ'.N ∩ bd π.S := ⟨hN'_eq ▸ Or.inr (mem_insert_of_mem _ rfl), hn₂_bd.2⟩
  obtain ⟨hpart, hdisj_I⟩ := cells_partitioned_by_disc π.Γ hdich
  have hbp₁_sub_Δ : π.borderPlus n₁ ⊆ (π.areaGraph Δ).vertexSet :=
    (π.borderPlus_subset_cellGraph hc₁_C hc₁_bd hn₁_c₁).trans
      (fun _ hv => mem_biUnion ⟨⟨hc₁_C, hc₁_Δ⟩, hc₁_C⟩ hv)
  have hbp₂_sub_Δ : π.borderPlus n₂ ⊆ (π.areaGraph Δ).vertexSet :=
    (π.borderPlus_subset_cellGraph hc₂_C hc₂_bd hn₂_c₂).trans
      (fun _ hv => mem_biUnion ⟨⟨hc₂_C, hc₂_Δ⟩, hc₂_C⟩ hv)
  have hbp_c'_sub_Δ : ∀ {n : π.S}, n ∈ tilde c' → π.borderPlus n ⊆ (π.areaGraph Δ).vertexSet := by
    intro n hn
    change n ∈ tilde (Δ \ {n₁, n₂}) at hn
    rw [htilde_c'] at hn
    rcases hn with rfl | rfl
    · exact hbp₁_sub_Δ
    · exact hbp₂_sub_Δ
  have htilde_c'_N' : tilde c' ⊆ Γ'.N ∩ bd π.S := by
    intro x hx
    change x ∈ tilde (Δ \ {n₁, n₂}) at hx
    rw [htilde_c'] at hx
    rcases hx with rfl | rfl
    · exact hn₁_N'
    · exact hn₂_N'
  -- By `(2.1)` (`theorem_2_1_claim_3`), `V(α(Δ)) ∩ V(α(I₂)) ⊆ β(n₁+) ∪ β(n₂+)`.
  have hinter_I₁_I₂ : (π.areaGraph Δ).vertexSet ∩ (π.cellsUnion I₂).vertexSet ⊆
      ⋃ n ∈ tilde c', π.borderPlus n := by
    exact cuff_disc_area_intersects_outer_cells_at_border (α := α) (β := β) (G := G) π (Δ := Δ)
      (n₁ := n₁) (n₂ := n₂) hΔ Γ' hN'_eq htilde_I₂ htilde_c' hpart hdisj_I
  let cellG : Set π.S → Hypergraph α β := fun c =>
    if c = c' then π.areaGraph Δ else π.cellGraph c
  let π' : Portrayal G :=
    replaced_cuff_disc_portrayal (α := α) (β := β) (G := G) π (Δ := Δ) (n₁ := n₁) (n₂ := n₂) Γ'
      hdich htilde_I₂ hc'_mem hC' hc'_not_I₂ hc'_bd hN'_sub hdisj_I hbp_c'_sub_Δ
      htilde_c'_N' hinter_I₁_I₂
  have hbp'_eq : ∀ {n : π.S}, n ∈ Γ'.N → π'.borderPlus n = π.borderPlus n := by
    intro n hn
    ext v
    change (v ∈ π.borderSet n ∨ (n ∈ π.domγ ∩ Γ'.N ∧ v = π.nodeVertex n)) ↔
      (v ∈ π.borderSet n ∨ (n ∈ π.domγ ∧ v = π.nodeVertex n))
    exact or_congr_right ⟨fun ⟨h, hv⟩ => ⟨h.1, hv⟩, fun ⟨h, hv⟩ => ⟨⟨h, hn⟩, hv⟩⟩
  -- `π'` is `𝒯`-central.
  have hπ'_central : π'.IsCentral 𝒯 := by
    intro c hc_mem
    rw [hC'] at hc_mem
    change ∃ B, (cellG c, B) ∈ 𝒯
    dsimp only [cellG]
    split_ifs with hcc'
    · exact hsmall
    · exact hc c (hc_mem.resolve_left hcc').1
  -- For every border cell `c ∈ I₂`, `π'.cellWarp c = π.cellWarp c`.
  have hcw_I₂ : ∀ {c : Set π.S}, c ∈ I₂ → (c ∩ bd π.S).Nonempty →
      π'.cellWarp c = π.cellWarp c := by
    intro c hc_I₂ _
    have hne_c : c ≠ c' := by rintro rfl; exact hc'_not_I₂ hc_I₂
    have hcg : π'.cellGraph c = π.cellGraph c := by
      change cellG c = π.cellGraph c
      dsimp only [cellG]
      exact ite_eq_right hne_c
    have hnt_N' : ∀ {n : π.S}, n ∈ tilde c → n ∈ Γ'.N :=
      fun hn => htilde_I₂ c hc_I₂.1 hc_I₂.2 hn
    have hiff : ∀ q : ℕ, π'.CellWarpLE c q ↔ π.CellWarpLE c q := by
      intro q
      simp only [Portrayal.CellWarpLE, hcg]
      refine forall₂_congr fun u₁ hu₁ => forall₂_congr fun u₂ hu₂ =>
        forall_congr' fun _ => ?_
      rw [hbp'_eq (hnt_N' hu₁), hbp'_eq (hnt_N' hu₂)]
    change sInf {p | π'.CellWarpLE c p} = sInf {p | π.CellWarpLE c p}
    congr 1
    ext p
    exact hiff p
  -- Bound the warp of `c'` in `π'` by `q = π.warpAt Θ`.
  let q := π.warpAt Θ
  have hΘ_arc : IsOArc Θ := (GraphMinor.Surface.cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
  have hbs_le_q : ∀ {n : π.S}, n ∈ π.Γ.N ∩ Θ → (π.borderSet n).ncard ≤ q :=
    fun hn => cuff_node_border_count_le_warp π hΘ hΘ_bd hΘ_arc hn
  have hcw_c' : π'.cellWarp c' ≤ q := by
    apply csInf_le (OrderBot.bddBelow _)
    intro u₁ hu₁ u₂ hu₂ hu_ne
    have hu₁_pair : u₁ = n₁ ∨ u₁ = n₂ := by
      change u₁ ∈ tilde (Δ \ {n₁, n₂}) at hu₁
      rw [htilde_c'] at hu₁
      exact hu₁
    have hu₂_pair : u₂ = n₁ ∨ u₂ = n₂ := by
      change u₂ ∈ tilde (Δ \ {n₁, n₂}) at hu₂
      rw [htilde_c'] at hu₂
      exact hu₂
    have hu₁_N' : u₁ ∈ Γ'.N := (htilde_c'_N' hu₁).1
    have hu₂_N' : u₂ ∈ Γ'.N := (htilde_c'_N' hu₂).1
    have hcg_c' : π'.cellGraph c' = π.areaGraph Δ := by
      change cellG c' = π.areaGraph Δ
      simp [cellG]
    rw [hbp'_eq hu₁_N', hbp'_eq hu₂_N', hcg_c']
    clear hu₁ hu₂ hu₁_N' hu₂_N'
    have hu₁_Θ : u₁ ∈ π.Γ.N ∩ Θ := by
      rcases hu₁_pair with h | h <;> rw [h] <;> assumption
    have hu₂_Θ : u₂ ∈ π.Γ.N ∩ Θ := by
      rcases hu₂_pair with h | h <;> rw [h] <;> assumption
    have hu₁_bd : u₁ ∈ π.Γ.N ∩ bd π.S := ⟨hu₁_Θ.1, hΘ_bd hu₁_Θ.2⟩
    have hu₂_bd : u₂ ∈ π.Γ.N ∩ bd π.S := ⟨hu₂_Θ.1, hΘ_bd hu₂_Θ.2⟩
    refine ⟨hbs_le_q hu₁_Θ, hbs_le_q hu₂_Θ, fun hcard₁ hcard₂ => ?_⟩
    have hcw_linkage : Portrayal.LinkagePairs (π.areaGraph Δ).skeleton (π.borderPlus u₁)
        (π.borderPlus u₂) (q + 1) (π.nodeVertex u₁) (π.nodeVertex u₂) := by
      exact cuff_disc_area_links_ends (α := α) (β := β) (G := G) (𝒯 := 𝒯) (θ := θ) (p := p) h𝒯 π
        hc hred hwarp hθ (F := F) (Δ := Δ) (n₁ := n₁) (n₂ := n₂) hnorm hF hFbd hFN hΔ hF_bd hbd_sub
        hsmall hne Θ hΘ hbd_Θ hΘ_bd hn₁_bd hn₂_bd hbs_le_q u₁ u₂ hu_ne hu₁_pair hu₂_pair hu₁_Θ
        hu₂_Θ hu₁_bd hu₂_bd hcard₁ hcard₂
    exact hcw_linkage
  -- Show `π'.warpAt Θ' ≤ π.warpAt Θ'` for every cuff `Θ' ∈ cuffs π.S`.
  have hwarpAt_le : ∀ Θ' ∈ cuffs π.S, π'.warpAt Θ' ≤ π.warpAt Θ' := by
    intro Θ' hΘ'
    apply csSup_le'
    rintro r ⟨c, hc_mem, hc_Θ', rfl⟩
    rw [hC'] at hc_mem
    rcases hc_mem with rfl | hc_I₂
    · have hΘ'_eq : Θ' = Θ :=
        (Γ'.border_cell_subset_cuff hc'_mem hΘ hc'_Θ).2.2.2.2 Θ' hΘ' hc_Θ'
      exact hΘ'_eq ▸ hcw_c'
    · have hΘ'_bd : Θ' ⊆ bd π.S := by
        rcases hΘ' with ⟨x₀, _, rfl⟩
        exact connectedComponentIn_subset (bd π.S) x₀
      have hbd_c : (c ∩ bd π.S).Nonempty := hc_Θ'.mono (inter_subset_inter_right _ hΘ'_bd)
      rw [hcw_I₂ hc_I₂ hbd_c]
      exact π.cellWarp_le_warpAt hc_I₂.1 hc_Θ'
  -- Since `π` is `0`-redundant, `π'` cannot be simpler than `π`, so `π'.Resembles π`.
  have hzero_red : π.IsZeroRedundant 𝒯 := hred.isZeroRedundant h𝒯
  have hwarpAt_eq : ∀ Θ' ∈ cuffs π.S, π'.warpAt Θ' = π.warpAt Θ' := by
    intro Θ' hΘ'
    refine le_antisymm (hwarpAt_le Θ' hΘ') ?_
    by_contra hlt
    have hlt' : π'.warpAt Θ' < π.warpAt Θ' := lt_of_not_ge hlt
    have hsimpler : π'.IsSimpler π := by
      right
      refine ⟨Homeomorph.refl π.S, ?_, Θ', hΘ', ?_⟩
      · intro Θ'' hΘ''
        rw [Homeomorph.refl_apply, image_id]
        exact hwarpAt_le Θ'' hΘ''
      · rw [Homeomorph.refl_apply, image_id]
        exact hlt'
    exact hzero_red π' hπ'_central hsimpler
  have hπ'_resembles : π'.Resembles π := by
    refine ⟨Homeomorph.refl π.S, fun Θ' hΘ' => ?_⟩
    rw [Homeomorph.refl_apply, image_id]
    exact hwarpAt_eq Θ' hΘ'
  refine ⟨π', hπ'_central, hπ'_resembles, ?_⟩
  -- Compare `π'.truth` and `π.truth`.
  have htruth_sub_lt4 : ∀ i : Fin 6, i.1 < 4 →
      {c ∈ Γ'.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - i.1} ⊆
      {c ∈ π.Γ.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - i.1} := by
    intro i _ c ⟨hc_mem, hint, hcard_c⟩
    have hne_c : c ≠ c' := fun h => hint (h ▸ hc'_bd)
    exact ⟨((hC' ▸ hc_mem).resolve_left hne_c).1, hint, hcard_c⟩
  have htruth_le : ∀ i : Fin 6, π'.truth i ≤ π.truth i := by
    intro i
    simp only [Portrayal.truth]
    split_ifs with h4 h5
    · exact ncard_le_ncard (htruth_sub_lt4 i h4) (π.Γ.finite_cells.subset fun _ h => h.1)
    · exact ncard_le_ncard (sdiff_subset_sdiff hN'_sub Subset.rfl) (π.Γ.finite_N.subset
        sdiff_subset)
    · exact ncard_le_ncard (inter_subset_inter_left _ hN'_sub) (π.Γ.finite_N.subset
        inter_subset_left)
  by_cases hex_lt : ∃ k : Fin 6, π'.truth k < π.truth k
  · exact Or.inl (isTruer_of_le_of_lt htruth_le hex_lt)
  · right
    have htruth_eq : ∀ i : Fin 6, π'.truth i = π.truth i := by
      intro i
      refine le_antisymm (htruth_le i) ?_
      by_contra hlt
      exact hex_lt ⟨i, lt_of_not_ge hlt⟩
    -- Every cell `c ∈ I₁` must be a border cell.
    obtain ⟨hI₁_border, hΔ_N_pair⟩ :=
      disc_has_no_internal_cells_or_new_nodes_of_count_eq π.Γ Γ' hC' hc'_bd hN'_eq hdisj_I
        htruth_sub_lt4
        (fun i hi => by
          have htr := htruth_eq i
          simpa only [Portrayal.truth, hi, ↓reduceIte] using htr)
        (by simpa [Portrayal.truth] using htruth_eq ⟨4, by decide⟩)
        (by simpa [Portrayal.truth] using htruth_eq ⟨5, by decide⟩) hN'_sub
    have hΔ_N_F : Δ ∩ π.Γ.N ⊆ F := hΔ_N_pair.trans (hFN ▸ inter_subset_left)
    refine ⟨hΔ_N_F, ?_⟩
    -- Since `(F' \ {n₁, n₂})` is nonempty and path-connected in `bd S \ N`, `I₁` has a unique cell.
    have hSingleBorderCell : I₁.ncard = 1 := by
      exact single_cell_in_disc_with_two_boundary_nodes π Θ hΔ_bd hF' hdich hΘ_bd hn₁_bd hn₂_bd
        hI₁_border hΔ_N_pair
    exact hSingleBorderCell

end Theorem73And74

end GraphMinor.GM17
