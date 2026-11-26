/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.RST94.Section2

/-!
# Section 3 of "Quickly excluding a planar graph": the lemma (3.1)

Robertson, Seymour and Thomas, J. Combin. Theory Ser. B 62 (1994), (3.1), pages 330–332. Paths are
`PathFromTo` of the
skeleton of `G`, and the vertex set of a path is `pathV`.

The paper phrases (3.1) with a tangle of order `6k`. The proof uses only that one side of a
separation of order `< 6k`
holds few vertices of `Z`, so we use `min_le_order` for that. The lemmas here are not used outside
this file, except for
`theorem_3_1` and `exists_lift`.
-/

@[expose] public section

namespace GraphMinor.RST94

open Hypergraph GM10 Set

variable {α β : Type*} {G H A B C D : Hypergraph α β}

/-- An edge of a graph has at most two ends. -/
theorem end_eq_or (hG : G.IsGraph) {e : β} {w x v : α} (hw : G.Inc e w) (hx : G.Inc e x)
  (hwx : w ≠ x)
    (hv : G.Inc e v) : v = w ∨ v = x := by
  classical
  by_contra hcon
  push Not at hcon
  have he := G.edge_mem_of_inc hw
  have hf : (G.ends e).Finite := G.vertexSet_finite.subset fun _ h => G.vertex_mem_of_inc h
  have h₂ := (hG e he).2
  have hs : ({v, w, x} : Set α) ⊆ G.ends e := by
    rintro y (rfl | rfl | rfl)
    · exact hv
    · exact hw
    · exact hx
  have h₃ : ({v, w, x} : Set α).ncard = 3 := ncard_eq_three.2 ⟨v, w, x, hcon.1, hcon.2, hwx, rfl⟩
  have := ncard_le_ncard hs hf
  omega

/-- Lifting a separation of `G \ W` to a separation of `G` with `W` on both sides. -/
theorem exists_lift (hG : G.IsGraph) {W : Set α} (hW : W ⊆ G.vertexSet) {A' B' : Hypergraph α β}
    (hs : (G.deleteVertices W).IsSeparation A' B') :
    ∃ A B : Hypergraph α β, G.IsSeparation A B ∧ A.vertexSet = A'.vertexSet ∪ W ∧ B.vertexSet
      = B'.vertexSet ∪ W ∧
      A'.edgeSet ⊆ A.edgeSet ∧ B'.edgeSet ⊆ B.edgeSet := by
  classical
  have hDG := deleteVertices_le G W
  have hA' : A' ≤ G := hs.left_le.trans hDG
  have hB' : B' ≤ G := hs.right_le.trans hDG
  let F₁ : Set β := {e | e ∈ G.edgeSet ∧ e ∉ (G.deleteVertices W).edgeSet ∧ ∀ v, G.Inc e v
    → v ∈ A'.vertexSet ∪ W}
  let F₂ : Set β := {e | e ∈ G.edgeSet ∧ e ∉ (G.deleteVertices W).edgeSet ∧ ¬ ∀ v, G.Inc e v
    → v ∈ A'.vertexSet ∪ W}
  let A := subOf G (A'.vertexSet ∪ W) (A'.edgeSet ∪ F₁) (union_subset hA'.vertexSet_subset hW) (by
    rintro e (he | he)
    · exact ⟨hA'.edgeSet_subset he, fun v hv => Or.inl (end_mem hA' he hv)⟩
    · exact ⟨he.1, he.2.2⟩)
  let B := subOf G (B'.vertexSet ∪ W) (B'.edgeSet ∪ F₂) (union_subset hB'.vertexSet_subset hW) (by
    rintro e (he | ⟨heG, hn, hc⟩)
    · exact ⟨hB'.edgeSet_subset he, fun v hv => Or.inl (end_mem hB' he hv)⟩
    · refine ⟨heG, fun v hv => ?_⟩
      -- The edge has an end in `W`, and an end `x` outside `V(A') ∪ W`, so these are all its ends.
      have hw : ∃ w ∈ W, G.Inc e w := by
        by_contra hno
        push Not at hno
        exact hn ⟨heG, hno⟩
      obtain ⟨w, hwW, hwi⟩ := hw
      push Not at hc
      obtain ⟨x, hxi, hx⟩ := hc
      have hxW : x ∉ W := fun h => hx (Or.inr h)
      have hne : w ≠ x := fun h => hxW (h ▸ hwW)
      rcases end_eq_or hG hwi hxi hne hv with rfl | rfl
      · exact Or.inr hwW
      · refine Or.inl ((mem_V_or hs ?_).resolve_left fun h => hx (Or.inl h))
        exact ⟨G.vertex_mem_of_inc hxi, hxW⟩)
  have hsep : G.IsSeparation A B := by
    refine sep_of_sets subOf_le subOf_le (fun v hv => ?_) (fun e he => ?_) ?_
    · by_cases hvW : v ∈ W
      · exact Or.inl (Or.inr hvW)
      · exact (mem_V_or hs ⟨hv, hvW⟩).imp Or.inl Or.inl
    · by_cases hed : e ∈ (G.deleteVertices W).edgeSet
      · exact (mem_E_or hs hed).imp Or.inl Or.inl
      · by_cases hc : ∀ v, G.Inc e v → v ∈ A'.vertexSet ∪ W
        · exact Or.inl (Or.inr ⟨he, hed, hc⟩)
        · exact Or.inr (Or.inr ⟨he, hed, hc⟩)
    · rintro e (he | he) (he' | he')
      · exact hs.notMem_edgeSet_right he he'
      · exact he'.2.1 (hs.left_le.edgeSet_subset he)
      · exact he.2.1 (hs.right_le.edgeSet_subset he')
      · exact he'.2.2 he.2.2
  exact ⟨A, B, hsep, rfl, rfl, fun e he => Or.inl he, fun e he => Or.inl he⟩

/-- A connected set that meets `V(A) \ V(B)` and `V(B) \ V(A)` meets `V(A ∩ B)`. -/
theorem Conn.meets_sep (hs : G.IsSeparation A B) {X : Set α} (hX : Conn G X) {a b : α} (ha : a ∈ X)
  (hb : b ∈ X)
    (haA : a ∈ A.vertexSet) (hbB : b ∈ B.vertexSet) : ∃ x ∈ X, x ∈ (A ∩ B).vertexSet := by
  obtain ⟨w, hw⟩ := hX.2 a ha b hb
  induction w with
  | nil => exact ⟨_, ha, haA, hbB⟩
  | @cons u v t hadj p ih =>
    have hu := hw u (by simp)
    have hrest : ∀ z ∈ p.support, z ∈ X := fun z hz => hw z (by simp [hz])
    by_cases hvA : v ∈ A.vertexSet
    · exact ih (hrest v p.start_mem_support) hb hvA hbB hrest
    · -- The edge from `u` to `v` is not in `A`, so it is in `B`.
      obtain ⟨-, e, h₁, h₂⟩ := hadj
      have heG := G.edge_mem_of_inc h₁
      have heB : e ∈ B.edgeSet := (mem_E_or hs heG).resolve_left fun he => hvA
        (end_mem hs.left_le he h₂)
      exact ⟨u, hu, haA, end_mem hs.right_le heB h₁⟩

/-- A separation with `X ⊆ V(A)`, `Y ⊆ V(B)` has order at least the number of disjoint paths from
`X` to `Y`. -/
theorem le_order_of_paths (hs : G.IsSeparation A B) {X Y : Set α} {k : ℕ} (hX : X ⊆ A.vertexSet)
  (hY : Y ⊆ B.vertexSet)
    (hp : HasDisjointPaths G.skeleton X Y k) : k ≤ separationOrder A B :=
  (menger G X Y (hX.trans hs.left_le.vertexSet_subset) (hY.trans hs.right_le.vertexSet_subset) k).2
    hp A B hs hX hY

variable {Z : Set α} {k : ℕ}

/-- `Z` is *linked* in `G`: the hypothesis of (3.1). -/
def Linked (G : Hypergraph α β) (Z : Set α) : Prop :=
  ∀ X Y : Set α, X ⊆ Z → Y ⊆ Z → X.ncard = Y.ncard → HasDisjointPaths G.skeleton X Y X.ncard

/-- In (3.1): one side of a separation has at most as many vertices of `Z` as the order of the
separation. This is what
makes the paper's set of separations a tangle. -/
theorem min_le_order (hZ : Z.Finite) (hl : Linked G Z) (hs : G.IsSeparation A B) :
    (A.vertexSet ∩ Z).ncard ≤ separationOrder A B ∨ (B.vertexSet ∩ Z).ncard ≤ separationOrder A B
      := by
  have hA : (A.vertexSet ∩ Z).Finite := hZ.subset inter_subset_right
  have hB : (B.vertexSet ∩ Z).Finite := hZ.subset inter_subset_right
  rcases le_total (A.vertexSet ∩ Z).ncard (B.vertexSet ∩ Z).ncard with h | h
  · obtain ⟨Y, hY, hc⟩ := exists_subset_card_eq h
    exact Or.inl (le_order_of_paths hs inter_subset_left (hY.trans inter_subset_left)
      (hl _ _ inter_subset_right (hY.trans inter_subset_right) hc.symm))
  · obtain ⟨X, hX, hc⟩ := exists_subset_card_eq h
    have := le_order_of_paths hs (hX.trans inter_subset_left) inter_subset_left
      (hl _ _ (hX.trans inter_subset_right) inter_subset_right hc)
    exact Or.inr (hc ▸ this)

/-- The vertex set `V(P)` of a path. -/
def pathV {K : SimpleGraph α} {X Y : Set α} (p : PathFromTo K X Y) : Set α
  := {x | x ∈ p.walk.support}

/-- A vertex set is *light* if a separation of order at most `5k` holds it on the side with few
vertices of `Z`. Light is
the paper's `rk_𝒯(V(P)) ≤ 5k` for the tangle in the proof of (3.1). -/
def Light (G : Hypergraph α β) (Z : Set α) (k : ℕ) (W : Set α) : Prop :=
  ∃ C D, G.IsSeparation C D ∧ W ⊆ C.vertexSet ∧ separationOrder C D ≤ 5 * k ∧
    (C.vertexSet ∩ Z).ncard ≤ separationOrder C D

/-- The conclusion of (3.1) for the vertex set `W` of `P`. -/
def Good (G : Hypergraph α β) (Z : Set α) (k : ℕ) (W : Set α) : Prop :=
  ∀ A B, (G.deleteVertices W).IsSeparation A B → separationOrder A B < k →
    ¬ (6 * k ≤ (A.vertexSet ∩ Z).ncard ∧ 6 * k ≤ (B.vertexSet ∩ Z).ncard)

/-- The end of the proof of (1) in (3.1). -/
private theorem light_aux (hZ : Z.Finite) (hl : Linked G Z) (_hk : 1 ≤ k) (hs : G.IsSeparation A B)
    (hCD : G.IsSeparation C D) {W : Set α} (hWC : W ⊆ C.vertexSet)
    (ho : separationOrder C D ≤ 5 * k) (hR : ((A ∩ B).vertexSet \ W).ncard < k)
    (hAD : 13 * k ≤ 2 * (A.vertexSet ∩ D.vertexSet ∩ Z).ncard) (hBZ : 6 * k + 2 ≤
      (B.vertexSet ∩ Z).ncard) : False := by
  have hs₁ : G.IsSeparation (A ∩ D) (B ∪ C) := (hs.symm.union_inter hCD).symm
  have hsub : ((A ∩ D) ∩ (B ∪ C)).vertexSet ⊆ (C ∩ D).vertexSet ∪ ((A ∩ B).vertexSet \ W) := by
    rintro x ⟨⟨hxA, hxD⟩, hx | hx⟩
    · by_cases hxC : x ∈ C.vertexSet
      · exact Or.inl ⟨hxC, hxD⟩
      · exact Or.inr ⟨⟨hxA, hx⟩, fun h => hxC (hWC h)⟩
    · exact Or.inl ⟨hx, hxD⟩
  have hfin : ((A ∩ B).vertexSet \ W).Finite := (A ∩ B).vertexSet_finite.sdiff
  have ho₁ : separationOrder (A ∩ D) (B ∪ C) ≤ separationOrder C D + ((A ∩ B).vertexSet \ W).ncard
    :=
    (ncard_le_ncard hsub ((C ∩ D).vertexSet_finite.union hfin)).trans (ncard_union_le _ _)
  rcases min_le_order hZ hl hs₁ with h | h
  · have : (A.vertexSet ∩ D.vertexSet ∩ Z).ncard ≤ ((A ∩ D).vertexSet ∩ Z).ncard := le_of_eq rfl
    omega
  · have : (B.vertexSet ∩ Z).ncard ≤ ((B ∪ C).vertexSet ∩ Z).ncard :=
      ncard_le_ncard (fun x hx => ⟨Or.inl hx.1, hx.2⟩) (hZ.subset inter_subset_right)
    omega

/-- If `P` does not satisfy (3.1), there is a separation `(A, B)` of `G` with `V(P) ⊆ V(A ∩ B)`,
`|V(A ∩ B) - V(P)| < k` and
`|V(A) ∩ Z|, |V(B) ∩ Z| ≥ 6k + 2`. These are the first lines of the proofs of (1) and of (3.1). -/
theorem exists_sep_of_not_good (hG : G.IsGraph) (hZf : Z.Finite) {W : Set α}
  (hW : W ⊆ G.vertexSet) {s t : α}
    (hst : s ≠ t) (hs : s ∈ Z ∩ W) (ht : t ∈ Z ∩ W) (hg : ¬ Good G Z k W) :
    ∃ A B A' B', G.IsSeparation A B ∧ W ⊆ A.vertexSet ∧ W ⊆ B.vertexSet ∧
      ((A ∩ B).vertexSet \ W).ncard < k ∧
      6 * k + 2 ≤ (A.vertexSet ∩ Z).ncard ∧ 6 * k + 2 ≤ (B.vertexSet ∩ Z).ncard ∧
      (G.deleteVertices W).IsSeparation A' B' ∧ A.vertexSet = A'.vertexSet ∪ W ∧ B.vertexSet
        = B'.vertexSet ∪ W ∧
      separationOrder A' B' < k := by
  unfold Good at hg
  push Not at hg
  obtain ⟨A', B', hs', ho, hA6, hB6⟩ := hg
  obtain ⟨A, B, hsep, hVA, hVB, -, -⟩ := exists_lift hG hW hs'
  have hnotW : ∀ {X : Hypergraph α β}, X ≤ G.deleteVertices W → ∀ x ∈ X.vertexSet, x ∉ W
    := fun h x hx =>
    (h.vertexSet_subset hx).2
  have hplus : ∀ {X X₁ : Hypergraph α β}, X ≤ G.deleteVertices W → X₁.vertexSet = X.vertexSet ∪ W →
      (X.vertexSet ∩ Z).ncard + 2 ≤ (X₁.vertexSet ∩ Z).ncard := fun {X X₁} h hV => by
    have hsub : (X.vertexSet ∩ Z) ∪ {s, t} ⊆ X₁.vertexSet ∩ Z := by
      rintro x (hx | rfl | rfl)
      · exact ⟨hV ▸ Or.inl hx.1, hx.2⟩
      · exact ⟨hV ▸ Or.inr hs.2, hs.1⟩
      · exact ⟨hV ▸ Or.inr ht.2, ht.1⟩
    have hdis : Disjoint (X.vertexSet ∩ Z) {s, t} := by
      refine disjoint_left.2 fun x hx hx' => hnotW h x hx.1 ?_
      rcases hx' with rfl | rfl
      · exact hs.2
      · exact ht.2
    have := ncard_le_ncard hsub (hZf.subset inter_subset_right)
    rw [ncard_union_eq hdis (hZf.subset inter_subset_right) (toFinite _), ncard_pair hst] at this
    exact this
  have hAZ := hplus hs'.left_le hVA
  have hBZ := hplus hs'.right_le hVB
  have hR : ((A ∩ B).vertexSet \ W).ncard < k := by
    have hsub : (A ∩ B).vertexSet \ W ⊆ (A' ∩ B').vertexSet := by
      rintro x ⟨⟨h₁, h₂⟩, hxW⟩
      rw [hVA] at h₁
      rw [hVB] at h₂
      exact ⟨h₁.resolve_right hxW, h₂.resolve_right hxW⟩
    exact (ncard_le_ncard hsub (A' ∩ B').vertexSet_finite).trans_lt ho
  exact ⟨A, B, A', B', hsep, hVA ▸ subset_union_right, hVB ▸ subset_union_right, hR, by omega, by
    omega, hs', hVA, hVB, ho⟩

/-- **(1)** in the proof of (3.1) (page 331). -/
theorem good_of_light (hG : G.IsGraph) (hZsub : Z ⊆ G.vertexSet) (hZf : Z.Finite) (hZc : Z.ncard
  = 18 * k)
    (hl : Linked G Z) (hk : 1 ≤ k) {W : Set α} (hW : W ⊆ G.vertexSet) {s t : α} (hst : s ≠ t)
      (hs : s ∈ Z ∩ W)
    (ht : t ∈ Z ∩ W) (hL : Light G Z k W) : Good G Z k W := by
  by_contra hg
  obtain ⟨A, B, -, -, hsep, -, -, hR, hAZ, hBZ, -⟩ := exists_sep_of_not_good hG hZf hW hst hs ht hg
  obtain ⟨C, D, hCD, hWC, hoC, hCZ⟩ := hL
  have hcov : Z ⊆ (C.vertexSet ∩ Z) ∪ (D.vertexSet ∩ Z) := fun x hx =>
    (mem_V_or hCD (hZsub hx)).imp (fun h => ⟨h, hx⟩) fun h => ⟨h, hx⟩
  have hfin : ∀ X : Set α, (X ∩ Z).Finite := fun X => hZf.subset inter_subset_right
  have h₁ := (ncard_le_ncard hcov ((hfin _).union (hfin _))).trans (ncard_union_le _ _)
  have hcov₂ : D.vertexSet ∩ Z ⊆ (A.vertexSet ∩ D.vertexSet ∩ Z) ∪ (B.vertexSet ∩ D.vertexSet ∩ Z)
    := fun x hx =>
    (mem_V_or hsep (hZsub hx.2)).imp (fun h => ⟨⟨h, hx.1⟩, hx.2⟩) fun h => ⟨⟨h, hx.1⟩, hx.2⟩
  have h₂ := (ncard_le_ncard hcov₂ ((hfin _).union (hfin _))).trans (ncard_union_le _ _)
  by_cases hcase : 13 * k ≤ 2 * (A.vertexSet ∩ D.vertexSet ∩ Z).ncard
  · exact light_aux hZf hl hk hsep hCD hWC hoC hR hcase (by omega)
  · exact light_aux hZf hl hk hsep.symm hCD hWC hoC
      (by rw [GM10.inter_comm]; exact hR) (by omega) (by omega)

end GraphMinor.RST94
