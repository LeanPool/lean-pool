/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hall
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto
/-!

Imported from [jtraverso/konig-edge-colouring](https://github.com/jtraverso/konig-edge-colouring/blob/7c60f7efb69c1747aaf39e5dfa7a89d907cd84ef/Konig/Egervary.lean), registered as PALOMAR-2026-10-15-000019. The original proof is retained; module paths and imports are adapted for this collection.

# The Kőnig–Egerváry theorem

* `card_matching_le_card_vertexCover`: in every finite graph, a matching has at most as many edges
  as a vertex cover has vertices (each matching edge needs its own cover vertex).
* `exists_matching_card_eq_vertexCover`: **Kőnig–Egerváry (1931).** In a finite bipartite graph
  there are a matching and a vertex cover of the same size; hence the maximum size of a matching
  equals the minimum size of a vertex cover.
-/

@[expose] public section

open SimpleGraph

namespace Konig.Egervary

/-- **Weak duality.** A matching has at most as many edges as a vertex cover has vertices. -/
theorem card_matching_le_card_vertexCover {V : Type*} [Finite V] {G : SimpleGraph V}
    {M : G.Subgraph} (hM : M.IsMatching) {C : Set V} (hC : G.IsVertexCover C) :
    M.edgeSet.ncard ≤ C.ncard := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · have : M.edgeSet = ∅ := Set.eq_empty_of_forall_notMem fun e => by
      induction e using Sym2.ind with
      | _ a b => exact isEmptyElim a
    simp [this]
  have hex : ∀ e ∈ M.edgeSet, ∃ v ∈ C, v ∈ e := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [Subgraph.mem_edgeSet] at he
      rcases hC (M.adj_sub he) with h | h
      · exact ⟨a, h, Sym2.mem_mk_left a b⟩
      · exact ⟨b, h, Sym2.mem_mk_right a b⟩
  choose! f hfC hfe using hex
  refine Set.ncard_le_ncard_of_injOn f hfC ?_ (Set.toFinite C)
  intro e₁ he₁ e₂ he₂ heq
  obtain ⟨w₁, h₁⟩ := Sym2.mem_iff_exists.1 (hfe e₁ he₁)
  obtain ⟨w₂, h₂⟩ := Sym2.mem_iff_exists.1 (hfe e₂ he₂)
  have ha₁ : M.Adj (f e₁) w₁ := by rw [← Subgraph.mem_edgeSet, ← h₁]; exact he₁
  have ha₂ : M.Adj (f e₁) w₂ := by rw [heq, ← Subgraph.mem_edgeSet, ← h₂]; exact he₂
  rw [h₁, h₂, ← heq, hM.eq_of_adj_left ha₁ ha₂]

/-- **Kőnig–Egerváry (1931).** A finite bipartite graph has a matching and a vertex cover of the
same size. -/
theorem exists_matching_card_eq_vertexCover {V : Type*} [Finite V] (G : SimpleGraph V)
    (h : G.Colorable 2) :
    ∃ (M : G.Subgraph) (C : Set V), M.IsMatching ∧ G.IsVertexCover C ∧
      M.edgeSet.ncard = C.ncard := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨col⟩ := h
  have hcol : ∀ a b, G.Adj a b → (col a = 0 ↔ col b ≠ 0) := by
    intro a b hab
    have key : ∀ i j : Fin 2, i ≠ j → (i = 0 ↔ j ≠ 0) := by decide
    exact key _ _ (col.valid hab)
  set L : Finset V := Finset.univ.filter (fun x => col x = 0) with hL
  set N : Finset V → Finset V :=
    fun S => Finset.univ.filter (fun y => ∃ x ∈ S, G.Adj x y) with hN
  have hNR : ∀ S ⊆ L, ∀ y ∈ N S, y ∉ L := by
    intro S hS y hy hyL
    simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    have hx0 : col x = 0 := (Finset.mem_filter.1 (hS hx)).2
    have hy0 : col y = 0 := (Finset.mem_filter.1 hyL).2
    exact ((hcol x y hxy).1 hx0) hy0
  obtain ⟨S₀, hS₀L, hmax⟩ := Finset.exists_max_image L.powerset
    (fun S => (S.card : ℤ) - (N S).card) ⟨∅, Finset.empty_mem_powerset L⟩
  rw [Finset.mem_powerset] at hS₀L
  have hmax' : ∀ T ⊆ L, (T.card : ℤ) - (N T).card ≤ (S₀.card : ℤ) - (N S₀).card :=
    fun T hT => hmax T (Finset.mem_powerset.2 hT)
  have hNS₀ : (N S₀).card ≤ S₀.card := by
    have := hmax' ∅ (Finset.empty_subset _)
    have hN0 : N ∅ = ∅ := by simp [hN]
    rw [hN0] at this
    simp at this
    omega
  set d := S₀.card - (N S₀).card with hd
  let t : L → Finset (V ⊕ Fin d) :=
    fun x => (Finset.univ.filter (fun y => G.Adj x y)).disjSum Finset.univ
  have hall : ∀ s : Finset L, s.card ≤ (s.biUnion t).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · simp
    set T : Finset V := s.map (Function.Embedding.subtype _) with hT
    have hTL : T ⊆ L := by
      intro x hx
      rw [hT, Finset.mem_map] at hx
      obtain ⟨x', -, rfl⟩ := hx
      exact x'.2
    have h1 := hmax' T hTL
    have hTc : T.card = s.card := Finset.card_map _
    have h2 : (N T).disjSum (Finset.univ : Finset (Fin d)) ⊆ s.biUnion t := by
      intro z hz
      rw [Finset.mem_biUnion]
      rcases z with y | i
      · rw [Finset.inl_mem_disjSum] at hz
        simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        obtain ⟨x, hx, hxy⟩ := hz
        rw [hT, Finset.mem_map] at hx
        obtain ⟨x', hx', rfl⟩ := hx
        exact ⟨x', hx', by simpa [t] using hxy⟩
      · exact ⟨x₀, hx₀, by simp [t]⟩
    have := Finset.card_le_card h2
    rw [Finset.card_disjSum, Finset.card_univ, Fintype.card_fin] at this
    omega
  obtain ⟨f, hfinj, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  set g : V → V := fun x => if h : x ∈ L then Sum.elim id (fun _ => x) (f ⟨x, h⟩) else x with hg
  set L' : Finset V := L.filter (fun x => ∀ h : x ∈ L, ∃ y, f ⟨x, h⟩ = Sum.inl y) with hL'
  have hL'L : ∀ {x}, x ∈ L' → x ∈ L := fun hx => (Finset.mem_filter.1 hx).1
  have hgf : ∀ x (hx : x ∈ L'), f ⟨x, hL'L hx⟩ = Sum.inl (g x) := by
    intro x hx
    obtain ⟨y, hy⟩ := (Finset.mem_filter.1 hx).2 (hL'L hx)
    simp [hg, hL'L hx, hy]
  have hgadj : ∀ x ∈ L', G.Adj x (g x) := by
    intro x hx
    have := hft ⟨x, hL'L hx⟩
    rw [hgf x hx] at this
    simpa [t] using this
  have hgR : ∀ x ∈ L', g x ∉ L := by
    intro x hx hgx
    have hx0 : col x = 0 := (Finset.mem_filter.1 (hL'L hx)).2
    exact (hcol x (g x) (hgadj x hx)).1 hx0 (Finset.mem_filter.1 hgx).2
  have hginj : ∀ x ∈ L', ∀ y ∈ L', g x = g y → x = y := by
    intro x hx y hy hxy
    have := hfinj ((hgf x hx).trans ((congrArg Sum.inl hxy).trans (hgf y hy).symm))
    exact congrArg Subtype.val this
  have hL'card : L.card - d ≤ L'.card := by
    have h1 : (L \ L').card ≤ d := by
      have := Finset.card_le_card_of_injOn
        (fun x => if h : x ∈ L then f ⟨x, h⟩ else Sum.inl x)
        (s := L \ L') (t := (Finset.univ : Finset (Fin d)).image Sum.inr) (by
          intro a ha
          rw [Finset.mem_coe, Finset.mem_sdiff] at ha
          have haL := ha.1
          simp only [hL', Finset.mem_filter, not_and, not_forall, not_exists] at ha
          obtain ⟨_, hne⟩ := ha.2 haL
          simp only [haL, dite_true, Finset.coe_image, Finset.coe_univ, Set.image_univ,
            Set.mem_range]
          rcases hfa : f ⟨a, haL⟩ with y | i
          · exact absurd hfa (hne y)
          · exact ⟨i, rfl⟩) (by
          intro a ha b hb hab
          have haL := (Finset.mem_sdiff.1 ha).1
          have hbL := (Finset.mem_sdiff.1 hb).1
          simp only [haL, hbL, dite_true] at hab
          exact congrArg Subtype.val (hfinj hab))
      rw [Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ,
        Fintype.card_fin] at this
      exact this
    have h2 : (L \ L').card = L.card - L'.card :=
      Finset.card_sdiff_of_subset (Finset.filter_subset _ _)
    have h3 : L'.card ≤ L.card := Finset.card_le_card (Finset.filter_subset _ _)
    omega
  let M : G.Subgraph :=
    { verts := (L' : Set V) ∪ (L'.image g : Set V)
      Adj := fun v w => (v ∈ L' ∧ g v = w) ∨ (w ∈ L' ∧ g w = v)
      adj_sub := by
        rintro v w (⟨hv, rfl⟩ | ⟨hw, rfl⟩)
        · exact hgadj v hv
        · exact (hgadj w hw).symm
      edge_vert := by
        rintro v w (⟨hv, rfl⟩ | ⟨hw, rfl⟩)
        · exact Or.inl hv
        · exact Or.inr (by simpa using ⟨w, hw, rfl⟩)
      symm := ⟨fun _ _ h => h.symm⟩ }
  have hM : M.IsMatching := by
    intro v hv
    rcases hv with hv | hv
    · refine ⟨g v, Or.inl ⟨hv, rfl⟩, ?_⟩
      rintro w (⟨-, rfl⟩ | ⟨hw, rfl⟩)
      · rfl
      · exact absurd (hL'L hv) (hgR w hw)
    · obtain ⟨u, hu, rfl⟩ : ∃ u ∈ L', g u = v := by simpa using hv
      refine ⟨u, Or.inr ⟨hu, rfl⟩, ?_⟩
      rintro w (⟨hgu, -⟩ | ⟨hw, hwu⟩)
      · exact absurd (hL'L hgu) (hgR u hu)
      · exact hginj w hw u hu hwu
  have hMcard : L'.card ≤ M.edgeSet.ncard := by
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn (fun x => s(x, g x)) ?_ ?_ (Set.toFinite _)
    · intro x hx
      exact (Subgraph.mem_edgeSet (G' := M)).2 (Or.inl ⟨hx, rfl⟩)
    · intro x hx y hy hxy
      rcases Sym2.eq_iff.1 hxy with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact h1
      · exact absurd (h1 ▸ hL'L hx) (hgR y hy)
  set C : Finset V := (L \ S₀) ∪ N S₀ with hC
  have hcov1 : ∀ v w, G.Adj v w → col v = 0 → v ∈ C ∨ w ∈ C := by
    intro v w hvw hv
    by_cases hvS : v ∈ S₀
    · right
      refine Finset.mem_union_right _ ?_
      simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨v, hvS, hvw⟩
    · left
      exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨by simp [hL, hv], hvS⟩)
  have hCcov : G.IsVertexCover (C : Set V) := by
    intro v w hvw
    by_cases hv : col v = 0
    · exact hcov1 v w hvw hv
    · have hw : col w = 0 := by
        by_contra hw
        exact hv ((hcol v w hvw).2 hw)
      exact (hcov1 w v hvw.symm hw).symm
  have hCcard : C.card = L.card - S₀.card + (N S₀).card := by
    rw [hC, Finset.card_union_of_disjoint, Finset.card_sdiff_of_subset hS₀L]
    rw [Finset.disjoint_left]
    intro y hy hyN
    exact hNR S₀ hS₀L y hyN (Finset.mem_sdiff.1 hy).1
  have hS₀c : S₀.card ≤ L.card := Finset.card_le_card hS₀L
  refine ⟨M, C, hM, hCcov, le_antisymm (card_matching_le_card_vertexCover hM hCcov) ?_⟩
  rw [Set.ncard_coe_finset, hCcard]
  omega

end Konig.Egervary
