/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.RST94.Basic
public import LeanPool.GraphMinor.RST94.Rado

/-!
# Section 2 of "Quickly excluding a planar graph": tangles

Robertson, Seymour and Thomas, J. Combin. Theory Ser. B 62 (1994), Section 2, pages 326–330.

The paper's rank `rk_𝒯` is `GM10.tangleRank`, and its free sets are `GM10.IsFreeSet`. Its (2.4) is
(12.1), (12.2) of Graph
Minors X, and its (2.8) is `GM10.theorem_2_9`. This file proves (2.5), (2.6), (2.7), (2.9), (2.10),
(2.11), (2.12).
-/

@[expose] public section

namespace GraphMinor.RST94

open Hypergraph GM10 Set

variable {α β : Type*} {G H A B C D : Hypergraph α β} {θ θ' : ℕ}
  {T T' : Set (Hypergraph α β × Hypergraph α β)}

/-- The set of all separations `(A, B)` of `G` of order `< θ'` with `(A ∩ H, B ∩ H) ∈ T'` (page
327): the tangle in `G`
induced by a tangle `T'` in a subgraph `H`. -/
abbrev inducedTangle (G H : Hypergraph α β) (T' : Set (Hypergraph α β × Hypergraph α β)) (θ' : ℕ) :
    Set (Hypergraph α β × Hypergraph α β) :=
  GM10.inducedTangleFromSubgraph G H θ' T'

/-- **(2.5)** (page 327): the induced set is a tangle in `G` of order `ord(T')`. -/
theorem isTangle_inducedTangle (hH : H ≤ G) (hT' : IsTangle H θ' T') : IsTangle G θ'
  (inducedTangle G H T' θ') :=
  GM10.isTangle_inducedTangleFromSubgraph hH hT'

/-- `T'`, a tangle of order `θ'` in `H`, is *conformal* with the tangle `T` in `G` of order `θ`
(page 327): the tangle
in `G` induced by `T'` is a subset of `T`. The paper reads `ord(T') ≤ ord(T)` as part of this, see
the proof of (2.6). -/
def Conformal (G H : Hypergraph α β) (T T' : Set (Hypergraph α β × Hypergraph α β))
  (θ θ' : ℕ) : Prop :=
  θ' ≤ θ ∧ inducedTangle G H T' θ' ⊆ T

/-- At most one of `(A, B)`, `(B, A)` is in a tangle, by the second axiom. -/
theorem not_mem_swap (hT : IsTangle G θ T) (h : (A, B) ∈ T) : (B, A) ∉ T := fun h' =>
  hT.axiom2 h h' h (by
    rw [GM10.union_assoc, GM10.union_comm B A, ← GM10.union_assoc, GM10.union_self]
    exact (hT.isSeparation h).union_eq)

/-- **(2.6)** (page 327). -/
theorem conformal_iff (hH : H ≤ G) (hT : IsTangle G θ T) (hT' : IsTangle H θ' T') :
    Conformal G H T T' θ θ' ↔ θ' ≤ θ ∧ ∀ A B, (A, B) ∈ T → separationOrder A B < θ' →
      (A ∩ H, B ∩ H) ∈ T' := by
  have hsep := fun {A B} (h : (A, B) ∈ T) => (hT.isSeparation h).restrict hH
  refine and_congr_right fun hle => ⟨fun h A B hAB ho => ?_, fun h p hp => ?_⟩
  · have hs := hT.isSeparation hAB
    rcases hT'.axiom1 (hs.restrict hH) ((order_restrict_le A B H).trans_lt ho) with h₁ | h₁
    · exact h₁
    · have : (B, A) ∈ T := h ⟨hs.symm, by rwa [separationOrder_comm], h₁⟩
      exact absurd hAB (not_mem_swap hT this)
  · obtain ⟨hs, ho, hm⟩ := hp
    rcases hT.axiom1 hs (ho.trans_le hle) with h₁ | h₁
    · exact h₁
    · have h₂ : (p.2 ∩ H, p.1 ∩ H) ∈ T' := h _ _ h₁ (by rwa [separationOrder_comm])
      exact absurd hm (not_mem_swap hT' h₂)

/-- Conformality is transitive. -/
theorem Conformal.trans {H₂ : Hypergraph α β} {T₂ : Set (Hypergraph α β × Hypergraph α β)} {θ₂ : ℕ}
    (hH : H ≤ G) (hH₂ : H₂ ≤ H) (hT : IsTangle G θ T) (hT' : IsTangle H θ' T')
      (hT₂ : IsTangle H₂ θ₂ T₂)
    (h : Conformal G H T T' θ θ') (h₂ : Conformal H H₂ T' T₂ θ' θ₂) : Conformal G H₂ T T₂ θ θ₂ := by
  obtain ⟨hle, hc⟩ := (conformal_iff hH hT hT').1 h
  obtain ⟨hle₂, hc₂⟩ := (conformal_iff hH₂ hT' hT₂).1 h₂
  refine (conformal_iff (hH₂.trans hH) hT hT₂).2 ⟨hle₂.trans hle, fun A B hAB ho => ?_⟩
  have hs := hT.isSeparation hAB
  have := hc₂ _ _ (hc A B hAB (ho.trans_le hle₂)) ((order_restrict_le A B H).trans_lt ho)
  rwa [inter_inter_of_le hs.left_le hH hH₂, inter_inter_of_le hs.right_le hH hH₂] at this

/-- A tangle is conformal with its truncations in the sense that a tangle with the same separations
of small order
inside `T` stays conformal. A tangle `T₀` in `G` with `T₀ ⊆ T` is conformal with `T`. -/
theorem conformal_of_subset (_hT₀ : IsTangle G θ' T') (hle : θ' ≤ θ) (h : T' ⊆ T) : Conformal G G T
  T' θ θ' := by
  refine ⟨hle, fun p hp => h ?_⟩
  have := hp.2.2
  rwa [inter_eq_left_of_le hp.1.left_le, inter_eq_left_of_le hp.1.right_le] at this

/-- **(2.7)** (page 328). -/
theorem rank_le_of_conformal (hH : H ≤ G) (hT : IsTangle G θ T) (hT' : IsTangle H θ' T')
    (hc : Conformal G H T T' θ θ') {X : Set α} (hX₀ : X ⊆ H.vertexSet) : tangleRank T' θ' X
      ≤ tangleRank T θ X := by
  obtain ⟨hle, hm⟩ := (conformal_iff hH hT hT').1 hc
  by_contra hlt
  push Not at hlt
  have h₁ : tangleRank T θ X < θ' := hlt.trans_le (tangleRank_le_order hT' X)
  obtain ⟨A, B, hAB, hX, ho⟩ := exists_mem_of_tangleRank_lt (h₁.trans_le hle)
  have hX' : X ⊆ (A ∩ H).vertexSet := subset_inter hX hX₀
  have := tangleRank_le_separationOrder (θ := θ') (hm A B hAB (ho ▸ h₁)) hX'
  have := order_restrict_le A B H
  omega

/-- The rank is at least `g` exactly when no separation of `T` of order below `g` holds `X` on its
small side. -/
theorem le_rank_iff {X : Set α} {g : ℕ} (hg : g ≤ θ) :
    g ≤ tangleRank T θ X ↔ ∀ A B, (A, B) ∈ T → X ⊆ A.vertexSet → g ≤ separationOrder A B := by
  constructor
  · intro h A B hAB hX
    exact h.trans (tangleRank_le_separationOrder hAB hX)
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨A, B, hAB, hX, ho⟩ := exists_mem_of_tangleRank_lt (hlt.trans_le hg)
    have := h A B hAB hX
    omega

/-- `A ∩ (G \ Z)` for a subgraph `A` of `G` is `A⁺ \ Z`, where `A⁺` is `A` with `Z` added. -/
theorem deleteVertices_addVerts (hA : A ≤ G) {Z : Set α} (hZ : Z ⊆ G.vertexSet) :
    (addVerts G A hA Z hZ).deleteVertices Z = A ∩ G.deleteVertices Z := by
  refine sub_ext (G := G) ((deleteVertices_le _ _).trans addVerts_le) (inter_le hA
    (deleteVertices_le _ _)) ?_ ?_
  · ext v
    constructor
    · rintro ⟨h | h, h'⟩
      · exact ⟨h, hA.vertexSet_subset h, h'⟩
      · exact absurd h h'
    · exact fun h => ⟨Or.inl h.1, h.2.2⟩
  · ext e
    constructor
    · rintro ⟨he, h⟩
      refine ⟨he, hA.edgeSet_subset he, fun v hv hi => h v hv ⟨he, hi⟩⟩
    · rintro ⟨he, -, h⟩
      exact ⟨he, fun v hv hi => h v hv hi.2⟩

/-- **(2.9)** (page 328): `T \ Z` is conformal with `T`. The first assertion of (2.9) is (8.5) of
Graph Minors X,
`GM10.theorem_8_5_proof`. -/
theorem conformal_deleteVertices (hG : G.IsGraph) (hT : IsTangle G θ T) {Z : Set α}
  (hZ : Z ⊆ G.vertexSet)
    (hlt : Z.ncard < θ) :
    Conformal G (G.deleteVertices Z) T (deleteVerticesTangle G Z T θ) θ (θ - Z.ncard) := by
  refine (conformal_iff (deleteVertices_le _ _) hT (GraphMinor.GM10.theorem_8_5_proof hG hT hZ
    hlt)).2 ⟨by omega, fun A B hAB ho => ?_⟩
  have hs := hT.isSeparation hAB
  have hs₁ := isSeparation_addVerts hs hZ
  have ho₁ := order_addVerts_le hs hZ
  have hm := GraphMinor.GM10.theorem_2_9_proof hT hAB hs₁ (by omega) (Or.inl fun v hv => Or.inl hv)
  refine ⟨hs.restrict (deleteVertices_le _ _), (order_restrict_le A B _).trans_lt ho, ⟨_, _⟩, hm,
    ?_,
    deleteVertices_addVerts hs.left_le hZ, deleteVertices_addVerts hs.right_le hZ⟩
  exact fun v hv => ⟨Or.inr hv, Or.inr hv⟩

/-- Moving a set `F` of edges of `B`, with all ends in `V(A)`, from `B` to `A` keeps a separation in
`T`, by (2.8). -/
theorem exists_move (hT : IsTangle G θ T) (hAB : (A, B) ∈ T) {F : Set β}
    (hF : ∀ e ∈ F, e ∈ B.edgeSet ∧ ∀ v, G.Inc e v → v ∈ A.vertexSet) :
    ∃ A₁ B₁ : Hypergraph α β, (A₁, B₁) ∈ T ∧ A₁.vertexSet = A.vertexSet ∧ A₁.edgeSet
      = A.edgeSet ∪ F ∧
      B₁.vertexSet = B.vertexSet ∧ B₁.edgeSet = B.edgeSet \ F := by
  have hs := hT.isSeparation hAB
  have hA := hs.left_le
  have hB := hs.right_le
  let A₁ := subOf G A.vertexSet (A.edgeSet ∪ F) hA.vertexSet_subset (by
    rintro e (he | he)
    · exact ⟨hA.edgeSet_subset he, fun v hv => end_mem hA he hv⟩
    · exact ⟨hB.edgeSet_subset (hF e he).1, (hF e he).2⟩)
  let B₁ := subOf G B.vertexSet (B.edgeSet \ F) hB.vertexSet_subset
    fun e he => ⟨hB.edgeSet_subset he.1, fun v hv => end_mem hB he.1 hv⟩
  have hs₁ : G.IsSeparation A₁ B₁ := by
    refine sep_of_sets subOf_le subOf_le (fun v hv => mem_V_or hs hv) (fun e he => ?_) ?_
    · by_cases heF : e ∈ F
      · exact Or.inl (Or.inr heF)
      · exact (mem_E_or hs he).imp Or.inl fun h => ⟨h, heF⟩
    · rintro e (he | he) he'
      · exact hs.notMem_edgeSet_right he he'.1
      · exact he'.2 he
  have ho : separationOrder A₁ B₁ = separationOrder A B := rfl
  exact ⟨A₁, B₁, GraphMinor.GM10.theorem_2_9_proof hT hAB hs₁ (lt_of_eq_of_lt ho (hT.order_lt hAB))
    (Or.inl subset_rfl), rfl, rfl, rfl, rfl⟩

/-- Deleting from `B` vertices of `A` with no edge of `B` at them keeps a separation in `T`, by
(2.8). -/
theorem exists_trim (hT : IsTangle G θ T) (hAB : (A, B) ∈ T) {W : Set α} (hW : W ⊆ A.vertexSet)
    (hno : ∀ e ∈ B.edgeSet, ∀ w ∈ W, ¬ G.Inc e w) :
    ∃ B₁ : Hypergraph α β, (A, B₁) ∈ T ∧ B₁.vertexSet = B.vertexSet \ W ∧ B₁.edgeSet = B.edgeSet
      := by
  have hs := hT.isSeparation hAB
  have hB := hs.right_le
  let B₁ := subOf G (B.vertexSet \ W) B.edgeSet (sdiff_subset.trans hB.vertexSet_subset)
    fun e he => ⟨hB.edgeSet_subset he, fun v hv => ⟨end_mem hB he hv, fun hw => hno e he v hw hv⟩⟩
  have hs₁ : G.IsSeparation A B₁ := by
    refine sep_of_sets hs.left_le subOf_le (fun v hv => ?_) (fun e he => mem_E_or hs he)
      fun e he he' => hs.notMem_edgeSet_right he he'
    by_cases hvW : v ∈ W
    · exact Or.inl (hW hvW)
    · exact (mem_V_or hs hv).imp id fun h => ⟨h, hvW⟩
  have ho : separationOrder A B₁ ≤ separationOrder A B :=
    ncard_le_ncard (fun v hv => ⟨hv.1, hv.2.1⟩) (A ∩ B).vertexSet_finite
  exact ⟨B₁, GraphMinor.GM10.theorem_2_9_proof hT hAB hs₁ (ho.trans_lt (hT.order_lt hAB)) (Or.inr
    (Or.inl subset_rfl)), rfl, rfl⟩

/-- **(2.10)** (page 329). -/
theorem theorem_2_10 {ι : Type*} [Fintype ι] (hG : G.IsGraph) (hT : IsTangle G θ T) (z : ι → α)
    (hz : Function.Injective z) (hfree : IsFreeSet G T θ (range z)) (hord : 2 * Fintype.card ι
      ≤ θ) :
    ∃ y : ι → α, Function.Injective y ∧ (∀ i, y i ∈ (G.deleteVertices (range z)).vertexSet) ∧
      (∀ i, G.skeleton.Adj (z i) (y i)) ∧
      IsFreeSet (G.deleteVertices (range z)) (deleteVerticesTangle G (range z) T θ) (θ -
        (range z).ncard) (range y) := by
  classical
  have hk : (range z).ncard = Fintype.card ι := by
    rw [← image_univ, ncard_image_of_injective _ hz, ncard_univ, Nat.card_eq_fintype_card]
  have hθ := hT.one_le
  have hlt : (range z).ncard < θ := by omega
  have hZ := hfree.1
  have hT' := GraphMinor.GM10.theorem_8_5_proof hG hT hZ hlt
  set Z := range z with hZdef
  let Y : ι → Set α := fun i => {y | y ∈ (G.deleteVertices Z).vertexSet ∧ G.skeleton.Adj (z i) y}
  have hY : ∀ i, Y i ⊆ (G.deleteVertices Z).vertexSet := fun i y hy => hy.1
  have hclaim : ∀ I : Finset ι, I.card ≤ tangleRank (deleteVerticesTangle G Z T θ) (θ - Z.ncard)
    (unionOver Y I) := by
    intro I
    have hI : I.card ≤ Fintype.card ι := Finset.card_le_univ I
    refine (le_rank_iff (by omega)).2 fun A' B' hm hU => ?_
    by_contra hcon
    push Not at hcon
    obtain ⟨hs', ho', ⟨A, B⟩, hAB, hZAB, hA', hB'⟩ := hm
    simp only at hZAB hA' hB'
    have hZA : Z ⊆ A.vertexSet := fun v hv => (hZAB hv).1
    let Zi : Set α := z '' I
    have hZi : Zi ⊆ Z := image_subset_range _ _
    let F : Set β := {e | e ∈ B.edgeSet ∧ ∃ w ∈ Zi, G.Inc e w}
    have hs := hT.isSeparation hAB
    have hF : ∀ e ∈ F, e ∈ B.edgeSet ∧ ∀ v, G.Inc e v → v ∈ A.vertexSet := by
      rintro e ⟨he, w, ⟨i, hi, rfl⟩, hw⟩
      refine ⟨he, fun v hv => ?_⟩
      by_cases hvZ : v ∈ Z
      · exact hZA hvZ
      · have hne : z i ≠ v := fun h => hvZ (h ▸ mem_range_self i)
        have hmem : v ∈ unionOver Y I := mem_iUnion₂.2 ⟨i, hi, ⟨G.vertex_mem_of_inc hv, hvZ⟩, hne,
          e, hw, hv⟩
        have := hU hmem
        rw [← hA'] at this
        exact this.1
    obtain ⟨A₁, B₁, hm₁, hVA, hEA, hVB, hEB⟩ := exists_move hT hAB hF
    have hno : ∀ e ∈ B₁.edgeSet, ∀ w ∈ Zi, ¬ G.Inc e w := by
      intro e he w hw hi
      rw [hEB] at he
      exact he.2 ⟨he.1, w, hw, hi⟩
    obtain ⟨B₂, hm₂, hVB₂, -⟩ := exists_trim hT hm₁ (hVA ▸ hZi.trans hZA) hno
    have hle := hfree.2.2 hm₂ (hVA ▸ hZA)
    have hsub : (A₁ ∩ B₂).vertexSet ⊆ (A' ∩ B').vertexSet ∪ (Z \ Zi) := by
      rintro v ⟨hv₁, hv₂⟩
      rw [hVB₂, hVB] at hv₂
      rw [hVA] at hv₁
      by_cases hvZ : v ∈ Z
      · exact Or.inr ⟨hvZ, hv₂.2⟩
      · refine Or.inl ⟨?_, ?_⟩
        · rw [← hA']
          exact ⟨hv₁, hvZ⟩
        · rw [← hB']
          exact ⟨hv₂.1, hvZ⟩
    have hZf : Z.Finite := finite_range z
    have hcard : separationOrder A₁ B₂ ≤ separationOrder A' B' + (Z \ Zi).ncard :=
      (ncard_le_ncard hsub ((A' ∩ B').vertexSet_finite.union hZf.sdiff)).trans (ncard_union_le _ _)
    have hdiff : (Z \ Zi).ncard = Z.ncard - Zi.ncard := ncard_sdiff hZi (hZf.subset hZi)
    have hZic : Zi.ncard = I.card := by
      have : Zi = ((I.image z : Finset α) : Set α) := by simp [Zi]
      rw [this, ncard_coe_finset, Finset.card_image_of_injective _ hz]
    have hZle : Zi.ncard ≤ Z.ncard := ncard_le_ncard hZi hZf
    omega
  obtain ⟨y, hy, hinj, hrk⟩ := rado (G.deleteVertices Z).vertexSet_finite
    (GraphMinor.GM10.theorem_12_1_proof _ hT') Y hY hclaim
  refine ⟨y, hinj, fun i => (hy i).1, fun i => (hy i).2, (isFreeSet_iff_tangleRank_eq hT').2 ?_⟩
  refine ⟨?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact (hy i).1
  · rw [hrk, ← image_univ, ncard_image_of_injective _ hinj, ncard_univ, Nat.card_eq_fintype_card]

/-- The tangle `{(A ∩ D, B ∩ D) : (A, B) ∈ T}` in `D`, of (2.11). -/
def restrictTangle (T : Set (Hypergraph α β × Hypergraph α β)) (D : Hypergraph α β) :
    Set (Hypergraph α β × Hypergraph α β) :=
  {p | ∃ A B, (A, B) ∈ T ∧ p = (A ∩ D, B ∩ D)}

section S211

variable (hT : IsTangle G θ T) (hCD : (C, D) ∈ T) (h0 : separationOrder C D = 0)

include hT hCD h0

omit hT hCD in
/-- `C` and `D` have no common vertex. -/
theorem inter_empty : (C ∩ D).vertexSet = ∅ :=
  (ncard_eq_zero (C ∩ D).vertexSet_finite).1 h0

/-- In the proof of (2.11): `(A ∪ C, B ∩ D) ∈ T` for `(A, B) ∈ T`. -/
theorem union_inter_mem (hAB : (A, B) ∈ T) : (A ∪ C, B ∩ D) ∈ T := by
  have hs := hT.isSeparation hAB
  have hs' := hT.isSeparation hCD
  have hs₁ := hs.union_inter hs'
  have ho : separationOrder (A ∪ C) (B ∩ D) ≤ separationOrder A B := by
    refine ncard_le_ncard ?_ (A ∩ B).vertexSet_finite
    rintro v ⟨hv | hv, hv₁, hv₂⟩
    · exact ⟨hv, hv₁⟩
    · have : v ∈ (C ∩ D).vertexSet := ⟨hv, hv₂⟩
      rw [inter_empty h0] at this
      exact this.elim
  have ho' := ho.trans_lt (hT.order_lt hAB)
  rcases hT.axiom1 hs₁ ho' with h | h
  · exact h
  · exfalso
    refine hT.axiom2 hAB hCD h ?_
    refine sub_ext (G := G) (union_le (union_le hs.left_le hs'.left_le) hs₁.right_le) le_rfl ?_ ?_
    · refine subset_antisymm (union_subset (union_subset hs.left_le.vertexSet_subset
      hs'.left_le.vertexSet_subset)
        hs₁.right_le.vertexSet_subset) fun v hv => ?_
      rcases mem_V_or hs hv with h₁ | h₁
      · exact Or.inl (Or.inl h₁)
      · rcases mem_V_or hs' hv with h₂ | h₂
        · exact Or.inl (Or.inr h₂)
        · exact Or.inr ⟨h₁, h₂⟩
    · refine subset_antisymm (union_subset (union_subset hs.left_le.edgeSet_subset
      hs'.left_le.edgeSet_subset)
        hs₁.right_le.edgeSet_subset) fun v hv => ?_
      rcases mem_E_or hs hv with h₁ | h₁
      · exact Or.inl (Or.inl h₁)
      · rcases mem_E_or hs' hv with h₂ | h₂
        · exact Or.inl (Or.inr h₂)
        · exact Or.inr ⟨h₁, h₂⟩

/-- **(2.11)** (page 329), the tangle. -/
theorem isTangle_restrictTangle : IsTangle D θ (restrictTangle T D) where
  one_le := hT.one_le
  isSeparation := by
    rintro _ _ ⟨A, B, hAB, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact (hT.isSeparation hAB).restrict (hT.isSeparation hCD).right_le
  order_lt := by
    rintro _ _ ⟨A, B, hAB, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact (order_restrict_le A B D).trans_lt (hT.order_lt hAB)
  axiom1 A' B' hs ho := by
    have hs' := hT.isSeparation hCD
    have hD := hs'.right_le
    have hemp := inter_empty h0
    have hA'G : A' ≤ G := hs.left_le.trans hD
    have hB'G : B' ≤ G := hs.right_le.trans hD
    have hAC : A' ∪ C ≤ G := union_le hA'G hs'.left_le
    have hs₁ : G.IsSeparation (A' ∪ C) B' := by
      refine sep_of_sets hAC hB'G (fun v hv => ?_) (fun e he => ?_) ?_
      · rcases mem_V_or hs' hv with h | h
        · exact Or.inl (Or.inr h)
        · exact (mem_V_or hs h).imp Or.inl id
      · rcases mem_E_or hs' he with h | h
        · exact Or.inl (Or.inr h)
        · exact (mem_E_or hs h).imp Or.inl id
      · rintro e (he | he) he'
        · exact hs.notMem_edgeSet_right he he'
        · exact hs'.notMem_edgeSet_right he (hs.right_le.edgeSet_subset he')
    have ho₁ : separationOrder (A' ∪ C) B' ≤ separationOrder A' B' := by
      refine ncard_le_ncard ?_ (A' ∩ B').vertexSet_finite
      rintro v ⟨hv | hv, hv'⟩
      · exact ⟨hv, hv'⟩
      · have : v ∈ (C ∩ D).vertexSet := ⟨hv, hs.right_le.vertexSet_subset hv'⟩
        rw [hemp] at this
        exact this.elim
    have hA'eq : (A' ∪ C) ∩ D = A' := by
      refine sub_ext (G := G) (inter_le hAC hD) hA'G ?_ ?_
      · refine subset_antisymm ?_ fun v hv => ⟨Or.inl hv, hs.left_le.vertexSet_subset hv⟩
        rintro v ⟨hv | hv, hv'⟩
        · exact hv
        · have : v ∈ (C ∩ D).vertexSet := ⟨hv, hv'⟩
          rw [hemp] at this
          exact this.elim
      · refine subset_antisymm ?_ fun v hv => ⟨Or.inl hv, hs.left_le.edgeSet_subset hv⟩
        rintro e ⟨he | he, he'⟩
        · exact he
        · exact absurd he' (hs'.notMem_edgeSet_right he)
    have hB'eq : B' ∩ D = B' := inter_eq_left_of_le hs.right_le
    rcases hT.axiom1 hs₁ (ho₁.trans_lt ho) with h | h
    · exact Or.inl ⟨_, _, h, by rw [hA'eq, hB'eq]⟩
    · exact Or.inr ⟨_, _, h, by rw [hA'eq, hB'eq]⟩
  axiom2 := by
    rintro _ _ _ _ _ _ ⟨A₁, B₁, h₁, e₁⟩ ⟨A₂, B₂, h₂, e₂⟩ ⟨A₃, B₃, h₃, e₃⟩ heq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e₁
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e₃
    have m₁ := union_inter_mem hT hCD h0 h₁
    have m₂ := union_inter_mem hT hCD h0 h₂
    have m₃ := union_inter_mem hT hCD h0 h₃
    have hs' := hT.isSeparation hCD
    refine hT.axiom2 m₁ m₂ m₃ (sub_ext (G := G) (union_le (union_le (hT.isSeparation m₁).left_le
      (hT.isSeparation m₂).left_le) (hT.isSeparation m₃).left_le) le_rfl ?_ ?_)
    · refine subset_antisymm (union_subset (union_subset (hT.isSeparation
      m₁).left_le.vertexSet_subset
        (hT.isSeparation m₂).left_le.vertexSet_subset) (hT.isSeparation
          m₃).left_le.vertexSet_subset) fun v hv => ?_
      rcases mem_V_or hs' hv with h | h
      · exact Or.inl (Or.inl (Or.inr h))
      · have : v ∈ ((A₁ ∩ D) ∪ (A₂ ∩ D) ∪ (A₃ ∩ D)).vertexSet := by rw [heq]; exact h
        rcases this with (h | h) | h
        · exact Or.inl (Or.inl (Or.inl h.1))
        · exact Or.inl (Or.inr (Or.inl h.1))
        · exact Or.inr (Or.inl h.1)
    · refine subset_antisymm (union_subset (union_subset (hT.isSeparation m₁).left_le.edgeSet_subset
        (hT.isSeparation m₂).left_le.edgeSet_subset) (hT.isSeparation m₃).left_le.edgeSet_subset)
          fun v hv => ?_
      rcases mem_E_or hs' hv with h | h
      · exact Or.inl (Or.inl (Or.inr h))
      · have : v ∈ ((A₁ ∩ D) ∪ (A₂ ∩ D) ∪ (A₃ ∩ D)).edgeSet := by rw [heq]; exact h
        rcases this with (h | h) | h
        · exact Or.inl (Or.inl (Or.inl h.1))
        · exact Or.inl (Or.inr (Or.inl h.1))
        · exact Or.inr (Or.inl h.1)
  axiom3 := by
    rintro _ _ ⟨A, B, hAB, heq⟩ hV
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    have m := union_inter_mem hT hCD h0 hAB
    have hs' := hT.isSeparation hCD
    refine hT.axiom3 m (subset_antisymm (hT.isSeparation m).left_le.vertexSet_subset fun v hv => ?_)
    rcases mem_V_or hs' hv with h | h
    · exact Or.inr h
    · have : v ∈ (A ∩ D).vertexSet := by rw [hV]; exact h
      exact Or.inl this.1

/-- **(2.11)** (page 329): it is conformal with `T`. -/
theorem conformal_restrictTangle : Conformal G D T (restrictTangle T D) θ θ :=
  (conformal_iff (hT.isSeparation hCD).right_le hT (isTangle_restrictTangle hT hCD h0)).2
    ⟨le_rfl, fun A B hAB _ => ⟨A, B, hAB, rfl⟩⟩

end S211

/-- **(2.12)** (page 330): the paper's component `C` of `G \ Z`, given as a connected set of
vertices outside `Z`. -/
theorem theorem_2_12 (hT : IsTangle G θ T) {Z : Set α} (hfree : IsFreeSet G T θ Z)
  (hlt : Z.ncard < θ) :
    ∃ C : Set α, Conn G C ∧ C ⊆ G.vertexSet ∧ Disjoint C Z ∧ ∀ v ∈ Z, ∃ y ∈ C, G.skeleton.Adj v y
      := by
  classical
  have hZ := hfree.1
  -- Choose `(A, B) ∈ T` with `V(A ∩ B) = Z` and with `B` minimal.
  let P : Hypergraph α β × Hypergraph α β → Prop := fun p => p ∈ T ∧ (p.1 ∩ p.2).vertexSet = Z
  have hex : ∃ p, P p := by
    let K := subOf G Z ∅ hZ (fun _ he => he.elim)
    have hK : K ≤ G := subOf_le
    have hs : G.IsSeparation K G := sep_of_sets hK le_rfl (fun _ h => Or.inr h) (fun _ h
      => Or.inr h)
      fun _ he => he.elim
    have hV : (K ∩ G).vertexSet = Z := subset_antisymm (fun _ h => h.1) fun v hv => ⟨hv, hZ hv⟩
    have ho : separationOrder K G < θ := by
      unfold separationOrder
      rwa [hV]
    rcases hT.axiom1 hs ho with h | h
    · exact ⟨(K, G), h, hV⟩
    · exact absurd rfl (hT.axiom3 h)
  obtain ⟨⟨A, B⟩, ⟨hAB, hZeq⟩, hmin⟩ := exists_min_measure (fun p : Hypergraph α β × Hypergraph α β
    => size p.2) hex
  simp only at hZeq hmin
  have hs := hT.isSeparation hAB
  have hZA : Z ⊆ A.vertexSet := fun v hv => (hZeq ▸ hv : v ∈ (A ∩ B).vertexSet).1
  have hZB : Z ⊆ B.vertexSet := fun v hv => (hZeq ▸ hv : v ∈ (A ∩ B).vertexSet).2
  have hord : separationOrder A B = Z.ncard := by
    unfold separationOrder
    rw [hZeq]
  -- Each edge of `B` has an end outside `Z`.
  have hend : ∀ e ∈ B.edgeSet, ∃ y, G.Inc e y ∧ y ∉ Z := by
    intro e he
    by_contra hcon
    push Not at hcon
    obtain ⟨A₁, B₁, hm, hVA, hEA, hVB, hEB⟩ := exists_move (F := {e}) hT hAB (by
      rintro f rfl
      exact ⟨he, fun v hv => hZA (hcon v hv)⟩)
    have hs₁ := hT.isSeparation hm
    have hle : B₁ ≤ B := le_of_sets hs₁.right_le hs.right_le hVB.subset (hEB ▸ sdiff_subset)
    have hne : B₁ ≠ B := fun h => (hEB ▸ h ▸ he : e ∈ B.edgeSet \ {e}).2 rfl
    have := hmin (A₁, B₁) ⟨hm, by
      change A₁.vertexSet ∩ B₁.vertexSet = Z
      rw [hVA, hVB]
      exact hZeq⟩
    simp only at this
    exact absurd (size_lt_of_lt hle hne) (by omega)
  let C : Set α := B.vertexSet \ Z
  have hCne : C.Nonempty := by
    by_contra hcon
    have hsub : B.vertexSet ⊆ Z := fun v hv => by
      by_contra hvZ
      exact hcon ⟨v, hv, hvZ⟩
    refine hT.axiom3 hAB (subset_antisymm hs.left_le.vertexSet_subset fun v hv => ?_)
    exact (mem_V_or hs hv).elim id fun h => hZA (hsub h)
  have hCconn : Conn G C := by
    by_contra hcon
    obtain ⟨X₁, X₂, hX₁, hX₂, hun, hdis, hno⟩ := exists_split_of_not_conn hCne hcon
    have hsubB : ∀ {X}, X ∪ Z ⊆ B.vertexSet ∨ X ⊆ C → X ∪ Z ⊆ G.vertexSet := fun {X} h => by
      rcases h with h | h
      · exact h.trans hs.right_le.vertexSet_subset
      · exact union_subset (h.trans fun v hv => hs.right_le.vertexSet_subset hv.1) hZ
    have hX₁C : X₁ ⊆ C := fun v hv => hun ▸ Or.inl hv
    have hX₂C : X₂ ⊆ C := fun v hv => hun ▸ Or.inr hv
    have hsplit : ∀ v, v ∈ B.vertexSet → v ∈ X₁ ∨ v ∈ X₂ ∨ v ∈ Z := fun v hv => by
      by_cases hvZ : v ∈ Z
      · exact Or.inr (Or.inr hvZ)
      · have : v ∈ C := ⟨hv, hvZ⟩
        rw [← hun] at this
        exact this.elim Or.inl (fun h => Or.inr (Or.inl h))
    let F₁ : Set β := {e | e ∈ B.edgeSet ∧ ∃ y ∈ X₁, G.Inc e y}
    let F₂ : Set β := {e | e ∈ B.edgeSet ∧ ¬ ∃ y ∈ X₁, G.Inc e y}
    let B₁ := subOf G (X₁ ∪ Z) F₁ (hsubB (Or.inr hX₁C)) (by
      rintro e ⟨he, y, hy, hi⟩
      refine ⟨hs.right_le.edgeSet_subset he, fun v hv => ?_⟩
      rcases hsplit v (end_mem hs.right_le he hv) with h | h | h
      · exact Or.inl h
      · exact (hno y hy v h ⟨fun e' => disjoint_left.1 hdis hy (e' ▸ h), e, hi, hv⟩).elim
      · exact Or.inr h)
    let B₂ := subOf G (X₂ ∪ Z) F₂ (hsubB (Or.inr hX₂C)) (by
      rintro e ⟨he, hn⟩
      refine ⟨hs.right_le.edgeSet_subset he, fun v hv => ?_⟩
      rcases hsplit v (end_mem hs.right_le he hv) with h | h | h
      · exact (hn ⟨v, h, hv⟩).elim
      · exact Or.inl h
      · exact Or.inr h)
    have hB₁ : B₁ ≤ G := subOf_le
    have hB₂ : B₂ ≤ G := subOf_le
    have hB₁B : B₁ ≤ B := le_of_sets hB₁ hs.right_le
      (union_subset (hX₁C.trans fun _ h => h.1) hZB) fun _ h => h.1
    have hB₂B : B₂ ≤ B := le_of_sets hB₂ hs.right_le
      (union_subset (hX₂C.trans fun _ h => h.1) hZB) fun _ h => h.1
    have hcover : ∀ e ∈ G.edgeSet, e ∉ A.edgeSet → e ∈ F₁ ∨ e ∈ F₂ := fun e he heA => by
      have heB := (mem_E_or hs he).resolve_left heA
      by_cases h : ∃ y ∈ X₁, G.Inc e y
      · exact Or.inl ⟨heB, h⟩
      · exact Or.inr ⟨heB, h⟩
    have hcoverV : ∀ v ∈ G.vertexSet, v ∉ A.vertexSet → v ∈ X₁ ∨ v ∈ X₂ := fun v hv hvA => by
      have hvB := (mem_V_or hs hv).resolve_left hvA
      rcases hsplit v hvB with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (hZA h) hvA
    have hXA : ∀ {X}, X ⊆ C → ∀ v ∈ X, v ∉ A.vertexSet := fun {X} h v hv hvA =>
      (h hv).2 (hZeq ▸ ⟨hvA, (h hv).1⟩)
    -- `(A ∪ B₁, B₂)` and `(A ∪ B₂, B₁)` are separations of order `|Z|`, with smaller right side
    -- than `B`.
    have hs₁ : G.IsSeparation (A ∪ B₁) B₂ := by
      refine sep_of_sets (union_le hs.left_le hB₁) hB₂ (fun v hv => ?_) (fun e he => ?_) ?_
      · by_cases hvA : v ∈ A.vertexSet
        · exact Or.inl (Or.inl hvA)
        · exact (hcoverV v hv hvA).elim (fun h => Or.inl (Or.inr (Or.inl h)))
            (fun h => Or.inr (Or.inl h))
      · by_cases heA : e ∈ A.edgeSet
        · exact Or.inl (Or.inl heA)
        · exact (hcover e he heA).elim (fun h => Or.inl (Or.inr h)) Or.inr
      · rintro e (he | he) he'
        · exact hs.notMem_edgeSet_right he he'.1
        · exact he'.2 he.2
    have hs₂ : G.IsSeparation (A ∪ B₂) B₁ := by
      refine sep_of_sets (union_le hs.left_le hB₂) hB₁ (fun v hv => ?_) (fun e he => ?_) ?_
      · by_cases hvA : v ∈ A.vertexSet
        · exact Or.inl (Or.inl hvA)
        · exact (hcoverV v hv hvA).elim (fun h => Or.inr (Or.inl h)) fun h => Or.inl (Or.inr
          (Or.inl h))
      · by_cases heA : e ∈ A.edgeSet
        · exact Or.inl (Or.inl heA)
        · exact (hcover e he heA).elim Or.inr fun h => Or.inl (Or.inr h)
      · rintro e (he | he) he'
        · exact hs.notMem_edgeSet_right he he'.1
        · exact he.2 he'.2
    have hV₁ : ((A ∪ B₁) ∩ B₂).vertexSet = Z := by
      refine subset_antisymm ?_ fun v hv => ⟨Or.inl (hZA hv), Or.inr hv⟩
      rintro v ⟨hv | hv | hv, hv' | hv'⟩
      · exact absurd hv (hXA hX₂C v hv')
      · exact hv'
      · exact absurd hv' (disjoint_left.1 hdis hv)
      · exact hv'
      · exact hv
      · exact hv
    have hV₂ : ((A ∪ B₂) ∩ B₁).vertexSet = Z := by
      refine subset_antisymm ?_ fun v hv => ⟨Or.inl (hZA hv), Or.inr hv⟩
      rintro v ⟨hv | hv | hv, hv' | hv'⟩
      · exact absurd hv (hXA hX₁C v hv')
      · exact hv'
      · exact absurd hv (disjoint_left.1 hdis hv')
      · exact hv'
      · exact hv
      · exact hv
    have ho₁ : separationOrder (A ∪ B₁) B₂ < θ := by
      unfold separationOrder
      rwa [hV₁]
    have ho₂ : separationOrder (A ∪ B₂) B₁ < θ := by
      unfold separationOrder
      rwa [hV₂]
    have hne₁ : B₁ ≠ B := fun h => by
      obtain ⟨y, hy⟩ := hX₂
      have : y ∈ B₁.vertexSet := h ▸ (hX₂C hy).1
      rcases this with h' | h'
      · exact disjoint_left.1 hdis h' hy
      · exact (hX₂C hy).2 h'
    have hne₂ : B₂ ≠ B := fun h => by
      obtain ⟨y, hy⟩ := hX₁
      have : y ∈ B₂.vertexSet := h ▸ (hX₁C hy).1
      rcases this with h' | h'
      · exact disjoint_left.1 hdis hy h'
      · exact (hX₁C hy).2 h'
    have hn₁ : (A ∪ B₁, B₂) ∉ T := fun hm => by
      have := hmin (A ∪ B₁, B₂) ⟨hm, hV₁⟩
      exact absurd (size_lt_of_lt hB₂B hne₂) (by simp only at this; omega)
    have hn₂ : (A ∪ B₂, B₁) ∉ T := fun hm => by
      have := hmin (A ∪ B₂, B₁) ⟨hm, hV₂⟩
      exact absurd (size_lt_of_lt hB₁B hne₁) (by simp only at this; omega)
    have hm₁ := (hT.axiom1 hs₁ ho₁).resolve_left hn₁
    have hm₂ := (hT.axiom1 hs₂ ho₂).resolve_left hn₂
    refine hT.axiom2 hAB hm₁ hm₂ ?_
    rw [← hs₁.union_eq, GM10.union_assoc, GM10.union_comm B₂ B₁, ← GM10.union_assoc]
  refine ⟨C, hCconn, fun v hv => hs.right_le.vertexSet_subset hv.1, disjoint_sdiff_left, fun v hv
    => ?_⟩
  by_contra hcon
  push Not at hcon
  have hno : ∀ e ∈ B.edgeSet, ∀ w ∈ ({v} : Set α), ¬ G.Inc e w := by
    rintro e he w rfl hi
    obtain ⟨y, hy, hyZ⟩ := hend e he
    have hyC : y ∈ C := ⟨end_mem hs.right_le he hy, hyZ⟩
    exact hcon y hyC ⟨fun h => hyZ (h ▸ hv), e, hi, hy⟩
  obtain ⟨B₁, hm, hVB, -⟩ := exists_trim hT hAB (W := {v}) (singleton_subset_iff.2 (hZA hv)) hno
  have hle := hfree.2.2 hm hZA
  have hsub : (A ∩ B₁).vertexSet ⊆ Z \ {v} := by
    rintro x ⟨h₁, h₂⟩
    rw [hVB] at h₂
    exact ⟨hZeq ▸ ⟨h₁, h₂.1⟩, h₂.2⟩
  have hfZ : Z.Finite := G.vertexSet_finite.subset hZ
  have := ncard_le_ncard hsub hfZ.sdiff
  have h₃ := ncard_sdiff_singleton_lt_of_mem hv hfZ
  unfold separationOrder at hle
  omega

end GraphMinor.RST94
