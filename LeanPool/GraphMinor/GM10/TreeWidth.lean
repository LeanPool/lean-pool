/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.TreeWidthClaims
public import LeanPool.GraphMinor.GM10.Statements
import LeanPool.GraphMinor.GM10.BranchWidth

/-!
# Branch-Width and Tree-Width: Graph Minors X, Section 5 (Part 3)

This file completes the formalization of Section 5 of Robertson and Seymour, *Graph Minors. X.
Obstructions to tree-decomposition*, J. Combin. Theory Ser. B 52 (1991) 153–190 (pages 168–170):
- Suppression of degree-2 vertices in a tree (`suppressVertex`) and the first inequality of
  **(5.1)** (`branchWidth_le_treeWidthPlusOne`).
- **(5.1)** (`theorem_5_1`): for every hypergraph `G`, `max(β(G), γ(G)) ≤ ω(G) + 1`, and either
  `γ(G) = 0`, `V(G) ≠ ∅`, `β(G) = 0`, `ω(G) = 0` or `ω(G) + 1 ≤ (3/2) max(β(G), γ(G))`.
- **(5.2)** (`theorem_5_2`): for every hypergraph `G`, `θ(G) ≤ ω(G) + 1 ≤ (3/2) θ(G)`.
-/

public section

namespace GraphMinor.GM10

open SimpleGraph Hypergraph

variable {α β ι : Type*}

/-! ## Suppression of degree-2 vertices in a tree -/

/-- Suppress a vertex `t₀` of `T` with neighbors `w₁, w₂` by deleting `t₀` and joining `w₁` and
`w₂` (if distinct) (Graph Minors X, Section 5, proof of (5.1), page 169). -/
@[expose] def suppressVertex (T : SimpleGraph ι) (t₀ w₁ w₂ : ι) : SimpleGraph ({t₀}ᶜ : Set ι) where
  Adj a b := a.1 ≠ b.1 ∧ (T.Adj a.1 b.1 ∨ (a.1 = w₁ ∧ b.1 = w₂) ∨ (a.1 = w₂ ∧ b.1 = w₁))
  symm := ⟨by
    rintro a b ⟨hne, h | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact ⟨hne.symm, Or.inl h.symm⟩
    · exact ⟨hne.symm, Or.inr (Or.inr ⟨h2, h1⟩)⟩
    · exact ⟨hne.symm, Or.inr (Or.inl ⟨h2, h1⟩)⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- If `T.Adj t₀ w₁`, `T.Adj t₀ w₂`, and `w₁ ≠ w₂` in a tree `T`, then `¬ T.Adj w₁ w₂`. -/
theorem not_adj_of_common_neighbor_in_tree {T : SimpleGraph ι} (hT : T.IsTree)
    {t₀ w₁ w₂ : ι} (hadj₁ : T.Adj t₀ w₁) (hadj₂ : T.Adj t₀ w₂) (hw12 : w₁ ≠ w₂) :
    ¬ T.Adj w₁ w₂ := by
  intro hadj12
  have hp1 : (Walk.cons hadj12 Walk.nil).IsPath := by
    rw [Walk.isPath_def]
    simp [hadj12.ne]
  have hp2 : (Walk.cons hadj₁.symm (Walk.cons hadj₂ Walk.nil)).IsPath := by
    rw [Walk.isPath_def]
    simp [hadj₁.ne.symm, hw12, hadj₂.ne]
  have heq : (⟨Walk.cons hadj12 Walk.nil, hp1⟩ : T.Path w₁ w₂) =
      ⟨Walk.cons hadj₁.symm (Walk.cons hadj₂ Walk.nil), hp2⟩ :=
    @Subsingleton.elim _ (hT.isAcyclic.subsingleton_path w₁ w₂) _ _
  have hlen := congrArg (fun p : T.Path w₁ w₂ ↦ p.1.length) heq
  simp at hlen

/-- If `T.neighborSet t₀ = {w₁, w₂}`, then every walk `p : T.Walk u v` with `u ≠ t₀` and `v ≠ t₀`
compresses to a walk in `suppressVertex T t₀ w₁ w₂` from `⟨u, hu⟩` to `⟨v, hv⟩` whose support is
contained in `p.support`. -/
theorem exists_walk_suppressVertex {T : SimpleGraph ι} {t₀ w₁ w₂ : ι}
    (hadj_iff : ∀ y, T.Adj t₀ y ↔ y = w₁ ∨ y = w₂)
    {u v : ι} (p : T.Walk u v) :
    ∀ (hu : u ≠ t₀) (hv : v ≠ t₀),
      ∃ w : (suppressVertex T t₀ w₁ w₂).Walk ⟨u, hu⟩ ⟨v, hv⟩,
        ∀ z ∈ w.support, z.1 ∈ p.support := by
  suffices ∀ (n : ℕ) {u v : ι} (p : T.Walk u v), p.length = n →
      ∀ (hu : u ≠ t₀) (hv : v ≠ t₀),
        ∃ w : (suppressVertex T t₀ w₁ w₂).Walk ⟨u, hu⟩ ⟨v, hv⟩,
          ∀ z ∈ w.support, z.1 ∈ p.support from
    this p.length p rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro u v p hlen hu hv
    cases p with
    | nil =>
      refine ⟨Walk.nil, fun z hz ↦ ?_⟩
      rw [Walk.support_nil, List.mem_singleton] at hz
      subst hz
      exact List.mem_singleton.2 rfl
    | @cons _ b c hadj q =>
      by_cases hb : b = t₀
      · subst hb
        cases q with
        | nil => exact (hv rfl).elim
        | @cons _ d _ hadj2 q' =>
          have hlt : q'.length < n := by
            rw [← hlen]
            simp
          by_cases had : u = d
          · subst had
            obtain ⟨wq', hwq'⟩ := ih q'.length hlt q' rfl hu hv
            refine ⟨wq', fun z hz ↦ ?_⟩
            exact List.mem_cons_of_mem u (List.mem_cons_of_mem b (hwq' z hz))
          · have hd_ne : d ≠ b := hadj2.ne.symm
            obtain ⟨wq', hwq'⟩ := ih q'.length hlt q' rfl hd_ne hv
            have ha_w : u = w₁ ∨ u = w₂ := (hadj_iff u).1 hadj.symm
            have hd_w : d = w₁ ∨ d = w₂ := (hadj_iff d).1 hadj2
            have hadj_supp : (suppressVertex T b w₁ w₂).Adj ⟨u, hu⟩ ⟨d, hd_ne⟩ := by
              refine ⟨had, Or.inr ?_⟩
              rcases ha_w with rfl | rfl <;> rcases hd_w with rfl | rfl
              · exact (had rfl).elim
              · exact Or.inl ⟨rfl, rfl⟩
              · exact Or.inr ⟨rfl, rfl⟩
              · exact (had rfl).elim
            refine ⟨Walk.cons hadj_supp wq', fun z hz ↦ ?_⟩
            rw [Walk.support_cons, List.mem_cons] at hz
            rcases hz with rfl | hz
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem u (List.mem_cons_of_mem b (hwq' z hz))
      · have hlt : q.length < n := by
          rw [← hlen]
          simp
        obtain ⟨wq, hwq⟩ := ih q.length hlt q rfl hb hv
        have hadj_supp : (suppressVertex T t₀ w₁ w₂).Adj ⟨u, hu⟩ ⟨b, hb⟩ :=
          ⟨hadj.ne, Or.inl hadj⟩
        refine ⟨Walk.cons hadj_supp wq, fun z hz ↦ ?_⟩
        rw [Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem u (hwq z hz)

/-- In `suppressVertex T t₀ w₁ w₂`, `OnTreePath` implies `OnTreePath` in `T`. -/
theorem onTreePath_of_suppressVertex {T : SimpleGraph ι} {t₀ w₁ w₂ : ι}
    (hadj_iff : ∀ y, T.Adj t₀ y ↔ y = w₁ ∨ y = w₂)
    {a b c : ({t₀}ᶜ : Set ι)} (hp : OnTreePath (suppressVertex T t₀ w₁ w₂) a b c) :
    OnTreePath T a.1 b.1 c.1 := by
  intro p _
  obtain ⟨w, hw⟩ := exists_walk_suppressVertex hadj_iff p a.2 b.2
  exact hw c (mem_support_of_onTreePath hp w)

/-- Suppressing a degree-2 vertex `t₀` in a tree `T` with neighbors `w₁, w₂` preserves the degree
of every remaining vertex `x : {t₀}ᶜ`. -/
theorem degree_suppressVertex [Fintype ι] {T : SimpleGraph ι} (hT : T.IsTree) {t₀ w₁ w₂ : ι}
    [Fintype ({t₀}ᶜ : Set ι)]
    [DecidableRel (suppressVertex T t₀ w₁ w₂).Adj] [DecidableRel T.Adj]
    (hadj₁ : T.Adj t₀ w₁) (hadj₂ : T.Adj t₀ w₂) (hw12 : w₁ ≠ w₂)
    (hadj_iff : ∀ y, T.Adj t₀ y ↔ y = w₁ ∨ y = w₂) (x : ({t₀}ᶜ : Set ι)) :
    (suppressVertex T t₀ w₁ w₂).degree x = T.degree x.1 := by
  classical
  let T' := suppressVertex T t₀ w₁ w₂
  have hnot_adj12 : ¬ T.Adj w₁ w₂ := not_adj_of_common_neighbor_in_tree hT hadj₁ hadj₂ hw12
  rw [← ncard_neighborSet, ← ncard_neighborSet]
  let g : ({t₀}ᶜ : Set ι) → ι := fun y ↦ if T.Adj x.1 y.1 then y.1 else t₀
  have hbij : Set.BijOn g (T'.neighborSet x) (T.neighborSet x.1) := by
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      dsimp only [g]
      split_ifs with hxy
      · exact hxy
      · rcases hy.2 with hxy' | ⟨hx1, _⟩ | ⟨hx2, _⟩
        · exact (hxy hxy').elim
        · rw [hx1]; exact hadj₁.symm
        · rw [hx2]; exact hadj₂.symm
    · intro y₁ hy₁ y₂ hy₂ heq
      dsimp only [g] at heq
      split_ifs at heq with h1 h2 h2
      · exact Subtype.ext heq
      · exact (y₁.2 heq).elim
      · exact (y₂.2 heq.symm).elim
      · rcases hy₁.2 with h1' | ⟨hxw₁, hy₁w₂⟩ | ⟨hxw₂, hy₁w₁⟩
        · exact (h1 h1').elim
        · rcases hy₂.2 with h2' | ⟨_, hy₂w₂⟩ | ⟨hxw₂, _⟩
          · exact (h2 h2').elim
          · exact Subtype.ext (hy₁w₂.trans hy₂w₂.symm)
          · exact (hw12 (hxw₁.symm.trans hxw₂)).elim
        · rcases hy₂.2 with h2' | ⟨hxw₁, _⟩ | ⟨_, hy₂w₁⟩
          · exact (h2 h2').elim
          · exact (hw12 (hxw₁.symm.trans hxw₂)).elim
          · exact Subtype.ext (hy₁w₁.trans hy₂w₁.symm)
    · intro z hz
      have hxz : T.Adj x.1 z := hz
      by_cases hzt₀ : z = t₀
      · subst hzt₀
        rcases (hadj_iff x.1).1 hxz.symm with hxw₁ | hxw₂
        · refine ⟨⟨w₂, hadj₂.ne.symm⟩, ⟨by change x.1 ≠ w₂; rw [hxw₁]; exact hw12,
            Or.inr (Or.inl ⟨hxw₁, rfl⟩)⟩, ?_⟩
          dsimp only [g]
          have hnot : ¬ T.Adj x.1 w₂ := by rwa [hxw₁]
          exact ite_eq_right_iff.2 fun h ↦ (hnot h).elim
        · refine ⟨⟨w₁, hadj₁.ne.symm⟩, ⟨by change x.1 ≠ w₁; rw [hxw₂]; exact hw12.symm,
            Or.inr (Or.inr ⟨hxw₂, rfl⟩)⟩, ?_⟩
          dsimp only [g]
          have hnot : ¬ T.Adj x.1 w₁ := by
            rw [hxw₂]
            exact fun h ↦ hnot_adj12 h.symm
          exact ite_eq_right_iff.2 fun h ↦ (hnot h).elim
      · refine ⟨⟨z, hzt₀⟩, ⟨hxz.ne, Or.inl hxz⟩, ?_⟩
        dsimp only [g]
        exact ite_eq_left_iff.2 fun h ↦ (h hxz).elim
  rw [← hbij.image_eq, hbij.injOn.ncard_image]

/-- Suppressing a degree-2 vertex `t₀` in a tree `T` produces a tree. -/
theorem isTree_suppressVertex [Finite ι] {T : SimpleGraph ι} (hT : T.IsTree) {t₀ w₁ w₂ : ι}
    (hadj₁ : T.Adj t₀ w₁) (hadj₂ : T.Adj t₀ w₂) (hw12 : w₁ ≠ w₂)
    (hadj_iff : ∀ y, T.Adj t₀ y ↔ y = w₁ ∨ y = w₂) :
    (suppressVertex T t₀ w₁ w₂).IsTree := by
  classical
  let fintypeVertices := Fintype.ofFinite ι
  let fintypeComplement := Fintype.ofFinite ({t₀}ᶜ : Set ι)
  let T' := suppressVertex T t₀ w₁ w₂
  have hconn : T'.Connected := by
    have : Nonempty ({t₀}ᶜ : Set ι) := ⟨⟨w₁, hadj₁.ne.symm⟩⟩
    refine Connected.mk fun a b ↦ ?_
    obtain ⟨p⟩ := hT.connected a.1 b.1
    obtain ⟨w, _⟩ := exists_walk_suppressVertex hadj_iff p a.2 b.2
    exact ⟨w⟩
  have hdeg_t₀ : T.degree t₀ = 2 := by
    rw [← ncard_neighborSet]
    have hset : T.neighborSet t₀ = {w₁, w₂} := by
      ext y
      exact hadj_iff y
    rw [hset, Set.ncard_pair hw12]
  have hsum_compl : ∑ x : ({t₀}ᶜ : Set ι), T'.degree x =
      ∑ x ∈ Finset.univ.erase t₀, T.degree x := by
    have h1 : ∑ x : ({t₀}ᶜ : Set ι), T'.degree x =
        ∑ x : ({t₀}ᶜ : Set ι), T.degree x.1 :=
      Finset.sum_congr rfl fun x _ ↦ degree_suppressVertex hT hadj₁ hadj₂ hw12 hadj_iff x
    rw [h1]
    refine Finset.sum_bij (fun (x : ({t₀}ᶜ : Set ι)) _ ↦ x.1) ?_ ?_ ?_ ?_
    · intro x _
      exact Finset.mem_erase.2 ⟨x.2, Finset.mem_univ _⟩
    · intro x₁ _ x₂ _ h
      exact Subtype.ext h
    · intro y hy
      exact ⟨⟨y, (Finset.mem_erase.1 hy).1⟩, Finset.mem_univ _, rfl⟩
    · intros
      rfl
  have hsum_all : ∑ x : ι, T.degree x =
      T.degree t₀ + ∑ x ∈ Finset.univ.erase t₀, T.degree x :=
    (Finset.add_sum_erase (Finset.univ : Finset ι) (fun x ↦ T.degree x)
      (Finset.mem_univ t₀)).symm
  have htwice' := T'.sum_degrees_eq_twice_card_edges
  have htwice := T.sum_degrees_eq_twice_card_edges
  have hedge : Nat.card T'.edgeSet + 1 = Nat.card T.edgeSet := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← T'.edgeFinset_card,
      ← T.edgeFinset_card]
    omega
  have hcardT : Nat.card T.edgeSet + 1 = Nat.card ι :=
    (isTree_iff_connected_and_card.1 hT).2
  have hcard_compl : Nat.card ({t₀}ᶜ : Set ι) + 1 = Nat.card ι := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_of_subtype
      (Finset.univ.erase t₀) (fun x ↦ by simp [Finset.mem_erase]),
      Finset.card_erase_of_mem (Finset.mem_univ t₀), Finset.card_univ]
    have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨t₀⟩
    omega
  refine isTree_iff_connected_and_card.2 ⟨hconn, ?_⟩
  have hgoal : Nat.card T'.edgeSet + 1 = Nat.card ({t₀}ᶜ : Set ι) := by
    omega
  exact hgoal

/-- Single step of suppressing a degree-2 vertex `t₀` in a tree-decomposition `(T, τ)` of a
hypergraph `G` with no isolated vertices. -/
theorem suppressVertex_isTreeDecomposition [Fintype ι] {G : Hypergraph α β}
    (hno_iso : ∀ v ∈ G.vertexSet, ∃ e, G.Inc e v)
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (h : IsTreeDecomposition G T τ)
    {t₀ w₁ w₂ : ι} [Fintype ({t₀}ᶜ : Set ι)]
    (hadj₁ : T.Adj t₀ w₁) (hadj₂ : T.Adj t₀ w₂) (hw12 : w₁ ≠ w₂)
    (hadj_iff : ∀ y, T.Adj t₀ y ↔ y = w₁ ∨ y = w₂)
    (hc1 : ∀ e ∈ G.edgeSet, ∃ t ∈ leafSet T, τ t = edgeHypergraph G e) :
    IsTreeDecomposition G (suppressVertex T t₀ w₁ w₂) (fun x ↦ τ x.1) ∧
      treeDecompWidthPlusOne (fun (x : ({t₀}ᶜ : Set ι)) ↦ τ x.1) ≤ treeDecompWidthPlusOne τ := by
  have ht₀_not_leaf : t₀ ∉ leafSet T := by
    classical
    unfold leafSet IsLeaf
    rw [Set.mem_ofPred_eq, ← ncard_neighborSet]
    have hset : T.neighborSet t₀ = {w₁, w₂} := by ext y; exact hadj_iff y
    rw [hset, Set.ncard_pair hw12]
    omega
  have hc1' : ∀ e ∈ G.edgeSet, ∃ x : ({t₀}ᶜ : Set ι), τ x.1 = edgeHypergraph G e := by
    intro e heG
    obtain ⟨t, ht_leaf, hτ_t⟩ := hc1 e heG
    have ht_ne : t ≠ t₀ := fun h ↦ ht₀_not_leaf (h ▸ ht_leaf)
    exact ⟨⟨t, ht_ne⟩, hτ_t⟩
  have hT' : (suppressVertex T t₀ w₁ w₂).IsTree :=
    isTree_suppressVertex h.isTree hadj₁ hadj₂ hw12 hadj_iff
  have : Nonempty ({t₀}ᶜ : Set ι) := hT'.connected.nonempty
  refine ⟨⟨hT', fun x ↦ h.le x.1, ?_, ?_, ?_⟩, ?_⟩
  · ext x
    · simp only [Hypergraph.biUnion, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
      constructor
      · rintro ⟨a, hx⟩
        exact (h.le a.1).vertexSet_subset hx
      · intro hxG
        obtain ⟨e, hinc⟩ := hno_iso x hxG
        obtain ⟨a, hτ_a⟩ := hc1' e (G.edge_mem_of_inc hinc)
        refine ⟨a, ?_⟩
        rw [hτ_a]
        exact hinc
    · simp only [Hypergraph.biUnion, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
      constructor
      · rintro ⟨a, hx⟩
        exact (h.le a.1).edgeSet_subset hx
      · intro heG
        obtain ⟨a, hτ_a⟩ := hc1' x heG
        refine ⟨a, ?_⟩
        rw [hτ_a]
        exact Set.mem_singleton x
    · simp only [Hypergraph.biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, hinc⟩
        exact inc_of_le (h.le a.1) hinc
      · intro hincG
        obtain ⟨a, hτ_a⟩ := hc1' x (G.edge_mem_of_inc hincG)
        refine ⟨a, ?_⟩
        rw [hτ_a]
        exact ⟨rfl, hincG⟩
  · intro x y hne
    exact h.edgeSet_inter_eq (fun heq ↦ hne (Subtype.ext heq))
  · intro a c b hp
    exact h.inter_le (onTreePath_of_suppressVertex hadj_iff hp)
  · rw [treeDecompWidthPlusOne_le_iff]
    intro x
    exact ncard_vertexSet_le_treeDecompWidthPlusOne τ x.1

/-- Leaves of `suppressVertex T t₀ w₁ w₂` are exactly `{x : {t₀}ᶜ | x.1 ∈ leafSet T}`. -/
theorem mem_leafSet_suppressVertex_iff [Fintype ι] {T : SimpleGraph ι} (hT : T.IsTree)
    {t₀ w₁ w₂ : ι} [Fintype ({t₀}ᶜ : Set ι)]
    (hadj₁ : T.Adj t₀ w₁) (hadj₂ : T.Adj t₀ w₂) (hw12 : w₁ ≠ w₂)
    (hadj_iff : ∀ y, T.Adj t₀ y ↔ y = w₁ ∨ y = w₂) (x : ({t₀}ᶜ : Set ι)) :
    x ∈ leafSet (suppressVertex T t₀ w₁ w₂) ↔ x.1 ∈ leafSet T := by
  classical
  unfold leafSet IsLeaf
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq,
    degree_suppressVertex hT hadj₁ hadj₂ hw12 hadj_iff x]

/-- Suppressing all degree-2 vertices in a tree-decomposition satisfying Claims (1)–(3) of `(5.1)`
when `2 ≤ |E(G)|` and `G` has no isolated vertices yields a tree-decomposition whose underlying
tree is ternary (`IsTernaryTree`). -/
theorem exists_ternary_treeDecomposition [Fintype ι] {G : Hypergraph α β}
    (hno_iso : ∀ v ∈ G.vertexSet, ∃ e, G.Inc e v) (hcardE : 2 ≤ G.edgeSet.ncard)
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (h : IsTreeDecomposition G T τ)
    (hc1 : ∀ e ∈ G.edgeSet, ∃ t ∈ leafSet T, τ t = edgeHypergraph G e)
    (hc2 : ∀ t ∈ leafSet T, ∃ e ∈ G.edgeSet, τ t = edgeHypergraph G e)
    (hdeg3 : ∀ t : ι, by classical exact T.degree t ≤ 3) :
    ∃ (ι' : Type) (_ : Fintype ι') (T' : SimpleGraph ι') (τ' : ι' → Hypergraph α β),
      IsTreeDecomposition G T' τ' ∧
      treeDecompWidthPlusOne τ' ≤ treeDecompWidthPlusOne τ ∧
      IsTernaryTree T' ∧
      (∀ e ∈ G.edgeSet, ∃ t ∈ leafSet T', τ' t = edgeHypergraph G e) ∧
      (∀ t ∈ leafSet T', ∃ e ∈ G.edgeSet, τ' t = edgeHypergraph G e) := by
  classical
  have hmain : ∀ (n : ℕ) (ι₀ : Type) [Fintype ι₀] (T₀ : SimpleGraph ι₀)
      (τ₀ : ι₀ → Hypergraph α β),
      IsTreeDecomposition G T₀ τ₀ →
      (∀ e ∈ G.edgeSet, ∃ t ∈ leafSet T₀, τ₀ t = edgeHypergraph G e) →
      (∀ t ∈ leafSet T₀, ∃ e ∈ G.edgeSet, τ₀ t = edgeHypergraph G e) →
      (∀ t : ι₀, T₀.degree t ≤ 3) →
      Fintype.card ι₀ = n →
      ∃ (ι' : Type) (_ : Fintype ι') (T' : SimpleGraph ι') (τ' : ι' → Hypergraph α β),
        IsTreeDecomposition G T' τ' ∧
        treeDecompWidthPlusOne τ' ≤ treeDecompWidthPlusOne τ₀ ∧
        IsTernaryTree T' ∧
        (∀ e ∈ G.edgeSet, ∃ t ∈ leafSet T', τ' t = edgeHypergraph G e) ∧
        (∀ t ∈ leafSet T', ∃ e ∈ G.edgeSet, τ' t = edgeHypergraph G e) := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro ι₀ _ T₀ τ₀ h₀ h1 h2 hd3 hcard
      by_cases hex2 : ∃ t₀ : ι₀, T₀.degree t₀ = 2
      · obtain ⟨t₀, ht₀_deg⟩ := hex2
        have hcard2 : (T₀.neighborFinset t₀).card = 2 := by
          rw [card_neighborFinset_eq_degree, ht₀_deg]
        obtain ⟨w₁, w₂, hw12, hfin_eq⟩ := Finset.card_eq_two.1 hcard2
        have hadj_iff : ∀ y, T₀.Adj t₀ y ↔ y = w₁ ∨ y = w₂ := by
          intro y
          rw [← mem_neighborFinset, hfin_eq, Finset.mem_insert, Finset.mem_singleton]
        have hadj₁ : T₀.Adj t₀ w₁ := (hadj_iff w₁).2 (Or.inl rfl)
        have hadj₂ : T₀.Adj t₀ w₂ := (hadj_iff w₂).2 (Or.inr rfl)
        have ht₀_not_leaf : t₀ ∉ leafSet T₀ := by
          unfold leafSet IsLeaf
          rw [Set.mem_ofPred_eq]
          omega
        let S : Set ι₀ := {t₀}ᶜ
        let T₁ := suppressVertex T₀ t₀ w₁ w₂
        let τ₁ : S → Hypergraph α β := fun x ↦ τ₀ x.1
        obtain ⟨h₁, hw₁⟩ :=
          suppressVertex_isTreeDecomposition hno_iso h₀ hadj₁ hadj₂ hw12 hadj_iff h1
        have hleaf_iff :=
          mem_leafSet_suppressVertex_iff h₀.isTree hadj₁ hadj₂ hw12 hadj_iff
        have h1' : ∀ e ∈ G.edgeSet, ∃ x ∈ leafSet T₁, τ₁ x = edgeHypergraph G e := by
          intro e heG
          obtain ⟨t, ht_leaf, hτ_t⟩ := h1 e heG
          have ht_ne : t ≠ t₀ := fun h ↦ ht₀_not_leaf (h ▸ ht_leaf)
          exact ⟨⟨t, ht_ne⟩, (hleaf_iff ⟨t, ht_ne⟩).2 ht_leaf, hτ_t⟩
        have h2' : ∀ x ∈ leafSet T₁, ∃ e ∈ G.edgeSet, τ₁ x = edgeHypergraph G e := by
          intro x hx_leaf
          exact h2 x.1 ((hleaf_iff x).1 hx_leaf)
        have hd3' : ∀ x : S, T₁.degree x ≤ 3 := by
          intro x
          rw [degree_suppressVertex h₀.isTree hadj₁ hadj₂ hw12 hadj_iff x]
          exact hd3 x.1
        have hlt : Fintype.card S < n := by
          rw [← hcard]
          exact Fintype.card_lt_of_injective_of_notMem Subtype.val Subtype.val_injective
            (by rintro ⟨⟨x, hx⟩, rfl⟩; exact hx rfl)
        obtain ⟨ι', hfin', T', τ', h', hw', htern', hc1', hc2'⟩ :=
          ih (Fintype.card S) hlt S T₁ τ₁ h₁ h1' h2' hd3' rfl
        exact ⟨ι', hfin', T', τ', h', hw'.trans hw₁, htern', hc1', hc2'⟩
      · push Not at hex2
        have htern : IsTernaryTree T₀ := by
          refine ⟨h₀.isTree, fun v ↦ ?_⟩
          obtain ⟨e₁, he₁, e₂, he₂, he12⟩ :=
            (Set.one_lt_ncard G.edgeSet_finite).1 (by omega : 1 < G.edgeSet.ncard)
          obtain ⟨t₁, _, hτ₁⟩ := h1 e₁ he₁
          obtain ⟨t₂, _, hτ₂⟩ := h1 e₂ he₂
          have ht12 : t₁ ≠ t₂ := by
            rintro rfl
            have hmem : e₁ ∈ (edgeHypergraph G e₂).edgeSet := by
              rw [← hτ₂, hτ₁]
              exact Set.mem_singleton e₁
            exact he12 (Set.mem_singleton_iff.1 hmem)
          have hne_v : ∃ u : ι₀, v ≠ u := by
            by_cases hvt₁ : v = t₁
            · exact ⟨t₂, hvt₁ ▸ ht12⟩
            · exact ⟨t₁, hvt₁⟩
          obtain ⟨u, hvu⟩ := hne_v
          have hdeg_pos : 1 ≤ T₀.degree v := by
            obtain ⟨p, _⟩ := h₀.isTree.connected.exists_isPath v u
            cases p with
            | nil => exact (hvu rfl).elim
            | @cons _ w _ hadj _ =>
              rw [← card_neighborFinset_eq_degree]
              exact Finset.card_pos.2 ⟨w, (mem_neighborFinset T₀ v w).2 hadj⟩
          have hle3 := hd3 v
          have hne2 := hex2 v
          omega
        exact ⟨ι₀, inferInstance, T₀, τ₀, h₀, le_rfl, htern, h1, h2⟩
  let eFin := Fintype.equivFin ι
  have hc1_fin : ∀ e ∈ G.edgeSet, ∃ t ∈ leafSet (T.map eFin.toEmbedding),
      (τ ∘ eFin.symm) t = edgeHypergraph G e := by
    intro e heG
    obtain ⟨t, ht_leaf, hτ_t⟩ := hc1 e heG
    refine ⟨eFin t, (isLeaf_map eFin t).2 ht_leaf, ?_⟩
    simpa using hτ_t
  have hc2_fin : ∀ t ∈ leafSet (T.map eFin.toEmbedding),
      ∃ e ∈ G.edgeSet, (τ ∘ eFin.symm) t = edgeHypergraph G e := by
    intro t ht_leaf
    obtain ⟨x, rfl⟩ := eFin.surjective t
    rw [leafSet, Set.mem_ofPred_eq, isLeaf_map] at ht_leaf
    simpa using hc2 x ht_leaf
  have hd3_fin : ∀ t : Fin (Fintype.card ι), (T.map eFin.toEmbedding).degree t ≤ 3 := by
    intro t
    obtain ⟨x, rfl⟩ := eFin.surjective t
    rw [degree_map_equiv T eFin x (inst₂ := by classical infer_instance)]
    exact hdeg3 x
  obtain ⟨ι', hfin', T', τ', h', hw', htern', hc1', hc2'⟩ :=
    hmain _ (Fin (Fintype.card ι)) (T.map eFin.toEmbedding) (τ ∘ eFin.symm)
      (h.relabel eFin) hc1_fin hc2_fin (fun t ↦ by convert hd3_fin t) rfl
  rw [treeDecompWidthPlusOne_comp_equiv] at hw'
  exact ⟨ι', hfin', T', τ', h', hw', htern', hc1', hc2'⟩

/-! ## First inequality of (5.1) and main theorems (5.1) and (5.2) -/

/-- From a ternary tree-decomposition `(T, τ)` satisfying Claims (1) and (2) of `(5.1)`, we obtain
a branch-decomposition `(T, σ)` of `G` with `branchDecompWidth G T σ ≤ treeDecompWidthPlusOne τ`
(Graph Minors X, Section 5, proof of (5.1), page 169). -/
theorem exists_branchDecomposition_le_treeDecompWidthPlusOne [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (h : IsTreeDecomposition G T τ)
    (htern : IsTernaryTree T)
    (hc1 : ∀ e ∈ G.edgeSet, ∃ t ∈ leafSet T, τ t = edgeHypergraph G e)
    (hc2 : ∀ t ∈ leafSet T, ∃ e ∈ G.edgeSet, τ t = edgeHypergraph G e) :
    ∃ σ : ι → β, IsBranchDecomposition G T σ ∧
      branchDecompWidth G T σ ≤ treeDecompWidthPlusOne τ := by
  classical
  by_cases hE : G.edgeSet.Nonempty
  · obtain ⟨e_def, _⟩ := hE
    let σ (t : ι) : β := if ht : t ∈ leafSet T then (hc2 t ht).choose else e_def
    have hσ_mem : ∀ t ∈ leafSet T, σ t ∈ G.edgeSet := by
      intro t ht
      simp only [σ, ht, ↓reduceDIte]
      exact (hc2 t ht).choose_spec.1
    have hσ_eq : ∀ t ∈ leafSet T, τ t = edgeHypergraph G (σ t) := by
      intro t ht
      simp only [σ, ht, ↓reduceDIte]
      exact (hc2 t ht).choose_spec.2
    have hbij : Set.BijOn σ (leafSet T) G.edgeSet := by
      refine ⟨hσ_mem, ?_, ?_⟩
      · intro t₁ ht₁ t₂ ht₂ hσ12
        have he1 : σ t₁ ∈ (τ t₁).edgeSet := by
          rw [hσ_eq t₁ ht₁]
          exact Set.mem_singleton _
        have he2 : σ t₁ ∈ (τ t₂).edgeSet := by
          rw [hσ12, hσ_eq t₂ ht₂]
          exact Set.mem_singleton _
        exact h.eq_of_edge_mem he1 he2
      · intro e heG
        obtain ⟨t, ht_leaf, hτ_t⟩ := hc1 e heG
        refine ⟨t, ht_leaf, ?_⟩
        have he_mem : σ t ∈ (edgeHypergraph G e).edgeSet := by
          rw [← hτ_t, hσ_eq t ht_leaf]
          exact Set.mem_singleton _
        exact Set.mem_singleton_iff.1 he_mem
    refine ⟨σ, ⟨htern, hbij⟩, ?_⟩
    rw [branchDecompWidth_le_iff]
    intro e he
    induction e using Sym2.ind with
    | _ u w =>
      have hadj : T.Adj u w := T.mem_edgeSet.1 he
      have hsub : {v ∈ G.vertexSet | ∃ t₁ ∈ leafSet T, ∃ t₂ ∈ leafSet T,
          ¬ (T.deleteEdges {s(u, w)}).Reachable t₁ t₂ ∧ G.Inc (σ t₁) v ∧ G.Inc (σ t₂) v} ⊆
          (τ u).vertexSet := by
        rintro v ⟨_, t₁, ht₁, t₂, ht₂, hnot_reach, hinc₁, hinc₂⟩
        have hv₁ : v ∈ (τ t₁).vertexSet := by
          rw [hσ_eq t₁ ht₁]
          exact hinc₁
        have hv₂ : v ∈ (τ t₂).vertexSet := by
          rw [hσ_eq t₂ ht₂]
          exact hinc₂
        rw [not_reachable_deleteEdges_iff_treeComponent h.isTree hadj] at hnot_reach
        rcases hnot_reach with ⟨hc1_u, hc2_w⟩ | ⟨hc1_w, hc2_u⟩
        · have hp : OnTreePath T t₁ t₂ u :=
            onTreePath_of_mem_treeComponent h.isTree hadj hc1_u hc2_w
          exact (h.inter_le hp).vertexSet_subset ⟨hv₁, hv₂⟩
        · have hp : OnTreePath T t₂ t₁ u :=
            onTreePath_of_mem_treeComponent h.isTree hadj hc2_u hc1_w
          exact (h.inter_le hp).vertexSet_subset ⟨hv₂, hv₁⟩
      exact (Set.ncard_le_ncard hsub (τ u).vertexSet_finite).trans
        (ncard_vertexSet_le_treeDecompWidthPlusOne τ u)
  · rw [Set.not_nonempty_iff_eq_empty] at hE
    have h2 : 2 ≤ (leafSet T).ncard := htern.two_le_ncard_leafSet
    obtain ⟨t, ht_leaf⟩ : (leafSet T).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨e, heG, _⟩ := hc2 t ht_leaf
    rw [hE] at heG
    exact heG.elim

/-- First inequality of **(5.1)** (Graph Minors X, Section 5, (5.1), pages 168–169):
For every hypergraph `G`, `branchWidth G ≤ treeWidthPlusOne G` (`β(G) ≤ ω(G) + 1`). -/
theorem branchWidth_le_treeWidthPlusOne (G : Hypergraph α β) :
    branchWidth G ≤ treeWidthPlusOne G := by
  by_cases hcard : G.edgeSet.ncard ≤ 1
  · rw [branchWidth_eq_zero_of_ncard_edgeSet_le_one hcard]
    exact Nat.zero_le _
  · push Not at hcard
    let H := G.deleteVertices (isoSet G)
    have hiso : ∀ v ∈ isoSet G, ∀ e, ¬ G.Inc e v := by
      intro v hv
      exact (Set.mem_sep_iff.1 hv).2
    have hbwH : branchWidth H = branchWidth G := branchWidth_deleteVertices_of_isolated hiso
    have htwH : treeWidthPlusOne H ≤ treeWidthPlusOne G :=
      treeWidthPlusOne_deleteVertices_le_of_isolated hiso
    have hcardH : 2 ≤ H.edgeSet.ncard := by
      rw [deleteVertices_edgeSet_of_isolated hiso]
      exact hcard
    have hEH : H.edgeSet.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    have hno_isoH : ∀ v ∈ H.vertexSet, ∃ e, H.Inc e v :=
      fun _ hv ↦ exists_inc_deleteVertices_isoSet hv
    obtain ⟨ι₀, _, T₀, τ₀, h₀, hw₀⟩ := exists_treeDecomposition_eq_treeWidthPlusOne H
    obtain ⟨ι₁, _, T₁, τ₁, h₁, hw₁, hc1₁, _⟩ := theorem_5_1_claim_1 h₀
    obtain ⟨ι₂, _, T₂, τ₂, h₂, hw₂, hc1₂, hc2₂, hnl₂⟩ :=
      theorem_5_1_claim_2 hno_isoH hEH h₁ hc1₁
    obtain ⟨ι₃, _, T₃, τ₃, h₃, hw₃, hc1₃, hc2₃, _, hd3₃⟩ :=
      theorem_5_1_claim_3 h₂ hc1₂ hc2₂ hnl₂
    obtain ⟨ι₄, _, T₄, τ₄, h₄, hw₄, htern₄, hc1₄, hc2₄⟩ :=
      exists_ternary_treeDecomposition hno_isoH hcardH h₃ hc1₃ hc2₃ hd3₃
    obtain ⟨σ, hbd, hw_bd⟩ :=
      exists_branchDecomposition_le_treeDecompWidthPlusOne h₄ htern₄ hc1₄ hc2₄
    have hbw_le : branchWidth H ≤ branchDecompWidth H T₄ σ :=
      branchWidth_le_of_isBranchDecomposition hbd
    rw [← hbwH]
    exact hbw_le.trans (hw_bd.trans (hw₄.trans (hw₃.trans (hw₂.trans (hw₁.trans
      (hw₀.trans_le htwH))))))

/-- **Graph Minors X, (5.1)** (page 168):
"(5.1) *For any hypergraph $G$, $\max(\beta(G), \gamma(G)) \le \omega(G) + 1 \le
\max(\lfloor(3/2) \beta(G)\rfloor, \gamma(G), 1)$.*" -/
theorem theorem_5_1_proof (G : Hypergraph α β) :
    max (branchWidth G) (maxEdgeSize G) ≤ treeWidthPlusOne G ∧
      treeWidthPlusOne G ≤ max (max (3 * branchWidth G / 2) (maxEdgeSize G)) 1 :=
  ⟨max_le (branchWidth_le_treeWidthPlusOne G) (maxEdgeSize_le_treeWidthPlusOne G),
    treeWidthPlusOne_le_max_branchWidth_maxEdgeSize G⟩

/-- **Graph Minors X, (5.2)** (page 169):
"For any hypergraph $G$, $\theta(G) \le \omega(G) + 1 \le (3/2) \theta(G)$." -/
theorem theorem_5_2_proof (G : Hypergraph α β) :
    tangleNumber G ≤ treeWidthPlusOne G ∧ 2 * treeWidthPlusOne G ≤ 3 * tangleNumber G := by
  by_cases hcase : maxEdgeSize G = 0 ∧ G.vertexSet.Nonempty
  · obtain ⟨hγ, hV⟩ := hcase
    obtain ⟨_, htw⟩ := branchWidth_and_treeWidthPlusOne_of_maxEdgeSize_eq_zero hγ hV
    have hθ1 : tangleNumber G = 1 := tangleNumber_eq_one_of_maxEdgeSize_eq_zero hγ hV
    rw [htw, hθ1]
    omega
  · have h43 := theorem_4_3_proof G hcase
    have hle : tangleNumber G ≤ treeWidthPlusOne G := by
      rw [← h43]
      exact (theorem_5_1_proof G).1
    have hle2 : 2 * treeWidthPlusOne G ≤ 3 * tangleNumber G := by
      rw [← h43]
      by_cases hγ : maxEdgeSize G = 0
      · have hV : G.vertexSet = ∅ :=
          Set.not_nonempty_iff_eq_empty.1 fun hne ↦ hcase ⟨hγ, hne⟩
        exact two_mul_treeWidthPlusOne_le_three_mul_max (Or.inr hV)
      · exact two_mul_treeWidthPlusOne_le_three_mul_max
          (Or.inl (Nat.one_le_iff_ne_zero.2 hγ))
    exact ⟨hle, hle2⟩

/-- Proof of `Theorem43Statement` (Graph Minors X, (4.3)). -/
theorem theorem_4_3_statement : Theorem43Statement :=
  fun G h ↦ theorem_4_3_proof G h

/-- Proof of `Theorem45Statement` (Graph Minors X, (4.5)). -/
theorem theorem_4_5_statement : Theorem45Statement := by
  intro α β G θ 𝒯 hθ hsep_ord hax1 hi hii
  refine theorem_4_5_proof hθ (fun _ _ h ↦ (hsep_ord h).1) (fun _ _ h ↦ (hsep_ord h).2) hax1 hi ?_
  rintro ⟨A₁, A₂, A₃, h1, h2, h3, hd12, hd13, hd23, hU, hm1, hm2, hm3⟩
  exact hii ⟨A₁, A₂, A₃, h1, h2, h3, hd12, hd23, hd13, hU, hm1, hm2, hm3⟩

/-- Proof of `Theorem51Statement` (Graph Minors X, (5.1)). -/
theorem theorem_5_1_statement : Theorem51Statement :=
  fun G ↦ theorem_5_1_proof G

/-- Proof of `Theorem52Statement` (Graph Minors X, (5.2)). -/
theorem theorem_5_2_statement : Theorem52Statement :=
  fun G ↦ theorem_5_2_proof G

end GraphMinor.GM10
