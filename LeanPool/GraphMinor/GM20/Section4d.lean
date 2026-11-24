/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section4c

/-!
# Graph Minors XX, Section 4, (4.9)

This file proves (4.9): if deleting at most `θ` vertices from each member of `𝓕₂` gives a member of
a
well-behaved set `𝓕₁`, then `𝓕₂` is well-behaved. By induction on `θ` it suffices to take one vertex
`v`. The edges at `v` then carry codes as in (4.7), and `simulated_of_vertexStep` applies.

The encoding of the paper records nothing about roots, but `v` may be a root, and an expansion must
preserve its position. We fix this as follows. Members of `𝓕₁` have boundedly many roots, so `𝓕₂`
splits into finitely many sets according to the position of `v` in `π(G₂)`, and we treat each set
separately (`wellBehaved_oneSlash`).
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v}

theorem Patch.ext_of {Δ Δ' : Patch α} (h : Δ.verts = Δ'.verts) (h' : Δ.groupings = Δ'.groupings) :
    Δ = Δ' := by
  cases Δ
  cases Δ'
  cases h
  cases h'
  rfl

theorem emptySubgraph_sup (X Y : Set α) :
    (emptySubgraph X ⊔ emptySubgraph Y : (⊤ : SimpleGraph α).Subgraph) = emptySubgraph (X ∪ Y) := by
  apply SimpleGraph.Subgraph.ext
  · rfl
  · funext a b
    simp

theorem patchSlash_of_disjoint {Δ : Patch α} {W : Set α} (h : Disjoint W Δ.verts) :
    patchSlash Δ W = Δ := by
  have hV : Δ.verts \ W = Δ.verts := h.symm.sdiff_eq_left
  have hI : W ∩ Δ.verts = ∅ := h.inter_eq
  refine Patch.ext_of hV ?_
  ext K
  constructor
  · rintro ⟨-, -, hK⟩
    rw [hI, sup_emptySubgraph_empty] at hK
    exact hK
  · intro hK
    refine ⟨by rw [hV]; exact Δ.isGrouping K hK, by rw [hV]; exact Δ.verts_eq K hK, ?_⟩
    rw [hI, sup_emptySubgraph_empty]
    exact hK

theorem marchSlash_of_disjoint {π : List α} {W : Set α} (h : ∀ x ∈ π, x ∉ W) :
    marchSlash π W = π := by
  classical
  simpa [marchSlash] using h

theorem marchSlash_marchSlash (π : List α) (W₁ W₂ : Set α) :
    marchSlash (marchSlash π W₁) W₂ = marchSlash π (W₁ ∪ W₂) := by
  classical
  simp only [marchSlash, List.filter_filter]
  apply List.filter_congr
  intro x _
  by_cases h₁ : x ∈ W₁ <;> by_cases h₂ : x ∈ W₂ <;> simp [h₁, h₂]

theorem patchSlash_patchSlash (Δ : Patch α) (W₁ W₂ : Set α) :
    patchSlash (patchSlash Δ W₁) W₂ = patchSlash Δ (W₁ ∪ W₂) := by
  have hV : (Δ.verts \ W₁) \ W₂ = Δ.verts \ (W₁ ∪ W₂) := by
    ext x
    simp [not_or, and_assoc]
  have hI : (W₂ ∩ (Δ.verts \ W₁)) ∪ (W₁ ∩ Δ.verts) = (W₁ ∪ W₂) ∩ Δ.verts := by
    ext x
    by_cases h₁ : x ∈ W₁ <;> simp [h₁, and_comm]
  have hsup : ∀ K : (⊤ : SimpleGraph α).Subgraph,
      K ⊔ emptySubgraph (W₂ ∩ (Δ.verts \ W₁)) ⊔ emptySubgraph (W₁ ∩ Δ.verts) =
        K ⊔ emptySubgraph ((W₁ ∪ W₂) ∩ Δ.verts) := fun K ↦ by
    rw [sup_assoc, emptySubgraph_sup, hI]
  refine Patch.ext_of hV ?_
  ext K
  change (IsGrouping ((Δ.verts \ W₁) \ W₂) K ∧ K.verts = (Δ.verts \ W₁) \ W₂ ∧
      K ⊔ emptySubgraph (W₂ ∩ (Δ.verts \ W₁)) ∈ patchSlash Δ W₁) ↔
    (IsGrouping (Δ.verts \ (W₁ ∪ W₂)) K ∧ K.verts = Δ.verts \ (W₁ ∪ W₂) ∧
      K ⊔ emptySubgraph ((W₁ ∪ W₂) ∩ Δ.verts) ∈ Δ)
  rw [hV]
  constructor
  · rintro ⟨h₁, h₂, -, -, h₃⟩
    exact ⟨h₁, h₂, (hsup K) ▸ h₃⟩
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨h₁, h₂, ?_, ?_, (hsup K).symm ▸ h₃⟩
    · apply isGrouping_sup_emptySubgraph
      rwa [hV]
    · ext x
      simp only [SimpleGraph.Subgraph.verts_sup, emptySubgraph_verts, h₂, ← hV]
      by_cases hx : x ∈ W₂ <;> simp [hx]

theorem RootedHypergraph.ext_of {G G' : RootedHypergraph α β} (hV : G.vertexSet = G'.vertexSet)
    (hE : G.edgeSet = G'.edgeSet) (hI : G.Inc = G'.Inc) (hr : G.roots = G'.roots) : G = G' := by
  obtain ⟨⟨_, _, _, _, _, _, _⟩, _, _, _⟩ := G
  obtain ⟨⟨_, _, _, _, _, _, _⟩, _, _, _⟩ := G'
  cases hV
  cases hE
  cases hI
  cases hr
  rfl

theorem IsCompletionOf.refl {Ω : Type*} (P : Patchwork Ω α β) : IsCompletionOf P P :=
  ⟨rfl, rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

theorem IsCompletionOf.slash {Ω Ω' : Type*} {P : Patchwork Ω α β} {Q : Patchwork Ω' α β}
    (h : IsCompletionOf P Q) (W : Set α) : IsCompletionOf (P.slash W) (Q.slash W) where
  G_eq := by
    change Q.G.slash W = P.G.slash W
    rw [h.G_eq]
  dom_eq := h.dom_eq
  μ_eq _ he := congrArg (marchSlash · W) (h.μ_eq he)
  Δ_eq _ he := congrArg (patchSlash · W) (h.Δ_eq he)

theorem slash_slash {Ω : Type*} (P : Patchwork Ω α β) (W₁ W₂ : Set α) :
    IsCompletionOf ((P.slash W₁).slash W₂) (P.slash (W₁ ∪ W₂)) where
  G_eq := by
    refine RootedHypergraph.ext_of ?_ rfl ?_ (marchSlash_marchSlash _ _ _).symm
    · change P.G.vertexSet \ (W₁ ∪ W₂) = (P.G.vertexSet \ W₁) \ W₂
      ext x
      simp [not_or, and_assoc]
    · funext e x
      apply propext
      change (P.G.Inc e x ∧ x ∉ W₁ ∪ W₂) ↔ ((P.G.Inc e x ∧ x ∉ W₁) ∧ x ∉ W₂)
      simp [not_or, and_assoc]
  dom_eq := rfl
  μ_eq _ _ := (marchSlash_marchSlash _ _ _).symm
  Δ_eq _ _ := (patchSlash_patchSlash _ _ _).symm

theorem slash_empty {Ω : Type*} (P : Patchwork Ω α β) : IsCompletionOf (P.slash ∅) P where
  G_eq := by
    refine RootedHypergraph.ext_of ?_ rfl ?_ (marchSlash_of_disjoint fun _ _ ↦ id).symm
    · exact (Set.sdiff_empty).symm
    · funext e x
      apply propext
      exact ⟨fun h ↦ ⟨h, id⟩, fun h ↦ h.1⟩
  dom_eq := rfl
  μ_eq _ _ := (marchSlash_of_disjoint fun _ _ ↦ id).symm
  Δ_eq _ _ := (patchSlash_of_disjoint (Set.empty_disjoint _)).symm

theorem WellBehaved.completions {𝓕 : Set (UnlabeledPatchwork α β)} (h : WellBehaved 𝓕) :
    WellBehaved (completions Unit 𝓕) := by
  intro Ω _ hΩ Q hQ
  refine h Ω hΩ Q fun i ↦ ?_
  obtain ⟨P, ⟨P₁, hP₁, hc⟩, hc'⟩ := hQ i
  exact ⟨P₁, hP₁, hc.trans hc'⟩

theorem marchSlash_eq_eraseIdx {r : List α} {v : α} {p : ℕ} (hr : r.Nodup)
    (hp : r[p]? = some v) : marchSlash r {v} = r.eraseIdx p := by
  classical
  obtain ⟨hl, rfl⟩ := List.getElem?_eq_some_iff.mp hp
  rw [← hr.erase_getElem p hl, hr.erase_eq_filter]
  simp only [marchSlash]
  apply List.filter_congr
  intro x _
  by_cases hx : x = r[p] <;> simp [hx]

/-- The numbers of roots and the positions of roots compare well between `r` and `r'` when `v` and
`v'` have the same position in them. -/
theorem roots_transfer {r r' : List α} {v v' : α} {p K : ℕ} (nd : r.Nodup) (nd' : r'.Nodup)
    {η : α → Set α} (hr : r.length ≤ K) (hr' : r'.length ≤ K)
    (hpos : r[p]? = some v ∨ (p = K ∧ v ∉ r)) (hpos' : r'[p]? = some v' ∨ (p = K ∧ v' ∉ r'))
    (hlen : (marchSlash r {v}).length = (marchSlash r' {v'}).length)
    (hmem : ∀ (i : ℕ) (hi : i < (marchSlash r {v}).length)
      (hi' : i < (marchSlash r' {v'}).length), (marchSlash r' {v'})[i] ∈ η (marchSlash r {v})[i]) :
    r.length = r'.length ∧ ∀ (i : ℕ) (hi : i < r.length) (hi' : i < r'.length),
      r'[i] ∈ addVertex η v v' r[i] := by
  have hbig : ∀ {s : List α} {x}, s.length ≤ K → p = K → s[p]? = some x → False := by
    intro s x hs hp h
    have := (List.getElem?_eq_some_iff.mp h).1
    omega
  rcases hpos with hp | ⟨hK, hv⟩ <;> rcases hpos' with hp' | ⟨hK', hv'⟩
  · have hl := (List.getElem?_eq_some_iff.mp hp).1
    have hl' := (List.getElem?_eq_some_iff.mp hp').1
    rw [marchSlash_eq_eraseIdx nd hp, marchSlash_eq_eraseIdx nd' hp'] at hmem hlen
    rw [List.length_eraseIdx_of_lt hl, List.length_eraseIdx_of_lt hl'] at hlen
    have hL : r.length = r'.length := by omega
    refine ⟨hL, fun i hi hi' ↦ ?_⟩
    have hv : r[p] = v := (List.getElem?_eq_some_iff.mp hp).2
    have hv' : r'[p] = v' := (List.getElem?_eq_some_iff.mp hp').2
    rcases lt_trichotomy i p with hip | rfl | hip
    · have := hmem i (by rw [List.length_eraseIdx_of_lt hl]; omega)
        (by rw [List.length_eraseIdx_of_lt hl']; omega)
      simp only [List.getElem_eraseIdx, hip] at this
      rw [addVertex_of_ne fun h ↦ hip.ne ((nd.getElem_inj_iff).mp (h.trans hv.symm))]
      exact this
    · rw [hv, hv', addVertex_self]
      rfl
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have := hmem j (by rw [List.length_eraseIdx_of_lt hl]; omega)
        (by rw [List.length_eraseIdx_of_lt hl']; omega)
      have hnot : ¬ j < p := by omega
      simp only [List.getElem_eraseIdx, hnot] at this
      rw [addVertex_of_ne fun h ↦ hip.ne' ((nd.getElem_inj_iff).mp (h.trans hv.symm))]
      exact this
  · exact (hbig hr hK' hp).elim
  · exact (hbig hr' hK hp').elim
  · have e₁ : marchSlash r {v} = r :=
      marchSlash_of_disjoint fun x hx (h : x = v) ↦ hv (h ▸ hx)
    have e₂ : marchSlash r' {v'} = r' :=
      marchSlash_of_disjoint fun x hx (h : x = v') ↦ hv' (h ▸ hx)
    simp only [e₁, e₂] at hmem hlen
    refine ⟨hlen, fun i hi hi' ↦ ?_⟩
    rw [addVertex_of_ne fun h ↦ hv (by rw [← h]; exact List.getElem_mem hi)]
    exact hmem i hi hi'

/-- `Q` arises from `Q / {v}` by a `VertexStep` in which `A` is the set of edges at `v`. -/
theorem vertexStep_slash {Ω Ω' : Type*} (Q : Patchwork Ω α β) (φ : β → Ω') {v : α}
    (hv : v ∈ Q.G.vertexSet) (hdom : Q.dom = Q.G.edgeSet) {k : ℕ}
    (hk : ∀ e ∈ Q.dom, (marchSlash (Q.μ e) {v}).length + 1 ≤ k) :
    VertexStep Q ((Q.slash {v}).relabel φ) v {e | Q.G.Inc e v} k where
  v_notMem h := h.2 rfl
  vertexSet_eq := by
    change _ = (Q.G.vertexSet \ {v}) ∪ {v}
    rw [Set.sdiff_union_self, Set.union_eq_self_of_subset_right (singleton_subset_iff.mpr hv)]
  edgeSet_eq := rfl
  dom_eq := rfl
  A_subset e he := hdom.symm ▸ Q.G.edge_mem_of_inc he
  ends_ne e _ he := by
    ext x
    refine ⟨fun hx ↦ ⟨hx, fun h ↦ he ?_⟩, fun hx ↦ hx.1⟩
    have h' : x = v := h
    exact h' ▸ hx
  μ_ne e he hne := (marchSlash_of_disjoint fun x hx (h : x = v) ↦ hne (by
    have h₁ : x ∈ {x | x ∈ Q.μ e} := hx
    rw [Q.μ_set e he, h] at h₁
    exact h₁)).symm
  Δ_ne e he hne := (patchSlash_of_disjoint (by
    rw [Q.Δ_verts e he]
    exact Set.disjoint_singleton_left.mpr hne)).symm
  μ_subset e _ x hx := by
    change x ∈ marchSlash (Q.μ e) {v} ++ [v]
    by_cases hxv : x = v
    · simp [hxv]
    · exact List.mem_append_left _ (mem_marchSlash.mpr ⟨hx, hxv⟩)
  length_le e he := by
    have := hk e (hdom.symm ▸ Q.G.edge_mem_of_inc he)
    change (marchSlash (Q.μ e) {v} ++ [v]).length ≤ k
    simpa using this

theorem length_le_of_marchSlash {r : List α} (nd : r.Nodup) (v : α) :
    r.length ≤ (marchSlash r {v}).length + 1 := by
  by_cases hv : v ∈ r
  · obtain ⟨p, hl, rfl⟩ := List.getElem_of_mem hv
    rw [marchSlash_eq_eraseIdx nd (List.getElem?_eq_some_iff.mpr ⟨hl, rfl⟩),
      List.length_eraseIdx_of_lt hl]
    omega
  · rw [marchSlash_of_disjoint (W := {v}) fun x hx (h : x = v) ↦ hv (h ▸ hx)]
    omega

/-- The members of `𝓕₂` in the one-vertex case of (4.9) in which the vertex `v` is at position `p`
of
the roots, or is not a root if `p = K`. -/
def oneSlash (𝓕 : Set (UnlabeledPatchwork α β)) (p K : ℕ) : Set (UnlabeledPatchwork α β) :=
  {P₂ | P₂.dom = P₂.G.edgeSet ∧ ∃ v ∈ P₂.G.vertexSet, P₂.slash {v} ∈ completions Unit 𝓕 ∧
    (P₂.G.roots[p]? = some v ∨ (p = K ∧ v ∉ P₂.G.roots))}

/-- The proof of the one-vertex case of (4.9), for a fixed position of `v`. -/
theorem wellBehaved_oneSlash {𝓕 : Set (UnlabeledPatchwork α β)} (h : WellBehaved 𝓕) (p K : ℕ)
    (hK : ∀ P ∈ 𝓕, P.G.roots.length + 1 ≤ K) : WellBehaved (oneSlash 𝓕 p K) := by
  classical
  obtain ⟨N, hN⟩ := theorem_4_1_proof h
  refine wellBehaved_of_encoding h fun Ω₂ _ hΩ₂ ↦
    ⟨StepLabel Ω₂ (N + 1), inferInstance, wqo_stepLabel hΩ₂ _, fun Q S ↦ Q.dom = Q.G.edgeSet ∧
      ∃ v ∈ Q.G.vertexSet, (Q.G.roots[p]? = some v ∨ (p = K ∧ v ∉ Q.G.roots)) ∧
        Q.G.roots.length ≤ K ∧ (∀ e ∈ Q.dom, (marchSlash (Q.μ e) {v}).length + 1 ≤ N + 1) ∧
        S = (Q.slash {v}).relabel
          (stepLabel Q (Q.slash {v}) v {e | Q.G.Inc e v} (N + 1)), ?_, ?_⟩
  · rintro Q ⟨P₂, ⟨hdom, v, hv, ⟨P₁, hP₁, hc⟩, hpos⟩, hQ⟩
    have hc' : IsCompletionOf P₁ (Q.slash {v}) := hc.trans (hQ.slash _)
    have hr : Q.G.roots = P₂.G.roots := congrArg (·.roots) hQ.G_eq
    have hE : Q.G.edgeSet = P₂.G.edgeSet := hQ.sameBase.edgeSet_eq
    have hV : Q.G.vertexSet = P₂.G.vertexSet := hQ.sameBase.vertexSet_eq
    refine ⟨_, ⟨P₁, hP₁, hc'.trans (isCompletionOf_relabel _ _)⟩, hQ.dom_eq.trans
      (hdom.trans hE.symm),
      v, hV ▸ hv, hr ▸ hpos, ?_, ?_, rfl⟩
    · have h₁ := length_le_of_marchSlash Q.G.roots_nodup v
      have h₂ : (Q.slash {v}).G.roots = P₁.G.roots := congrArg (·.roots) hc'.G_eq
      have h₃ := hK P₁ hP₁
      rw [← h₂] at h₃
      exact h₁.trans h₃
    · intro e he
      have hd : e ∈ P₁.dom := by
        have : (Q.slash {v}).dom = P₁.dom := hc'.dom_eq
        rw [← this]
        exact he
      have h₂ : (Q.slash {v}).μ e = P₁.μ e := hc'.μ_eq hd
      have h₃ := hN P₁ hP₁ e hd
      rw [← h₂] at h₃
      exact Nat.succ_le_succ h₃
  · rintro Q - Q' - S S' ⟨hdom, v, hv, hpos, hlen, hb, rfl⟩ ⟨hdom', v', hv', hpos', hlen', hb', rfl⟩
      ⟨ηv, ηe, hη⟩
    have hl : ∀ e ∈ Q.G.edgeSet, _ := fun e he ↦ stepLabel_le (hη.1.φ_le e he)
    obtain ⟨hL, hm⟩ := roots_transfer Q.G.roots_nodup Q'.G.roots_nodup hlen hlen' hpos hpos'
      hη.1.roots_length hη.1.roots_mem
    refine simulated_of_vertexStep (vertexStep_slash Q _ hv hdom hb)
      (vertexStep_slash Q' _ hv' hdom' hb') hη (fun e he ↦ (hl e he).1) ?_
      (fun e he ↦ (hl e he).2.1) hL hm ?_
    · intro e he
      exact (hl e (Q.G.edge_mem_of_inc he)).2.2 he
    · rintro e ⟨he, -⟩ δ ⟨-, -, hδ⟩
      rw [Q'.Δ_verts e he] at hδ
      exact hδ

/-- The members of `𝓕₂` in the proof of (4.9) with `|W|` exactly `n`. -/
def slashSet (𝓕 : Set (UnlabeledPatchwork α β)) (n : ℕ) : Set (UnlabeledPatchwork α β) :=
  {P₂ | P₂.dom = P₂.G.edgeSet ∧ ∃ W : Set α, W.Finite ∧ W.ncard = n ∧ W ⊆ P₂.G.vertexSet ∧
    P₂.slash W ∈ completions Unit 𝓕}

/-- Graph Minors XX, (4.9) (page 333): "Let $\mathcal{F}_1$ be a well-behaved set of patchworks, let
$\theta \ge 0$, and let
$\mathcal{F}_2$ be the set of all patchworks $P_2 = (G_2, \mu_2, \Delta_2)$ such that
$dom(\mu_2) = E(G_2)$ and there exists $W \subseteq V(G_2)$ with $|W| \le \theta$ and $P_2/W
\in \mathcal{F}_1$. Then $\mathcal{F}_2$ is well-behaved." -/
theorem theorem_4_9_proof {𝓕₁ : Set (UnlabeledPatchwork α β)} (h : WellBehaved 𝓕₁) (θ : ℕ) :
    WellBehaved {P₂ | P₂.dom = P₂.G.edgeSet ∧ ∃ W : Set α, W.Finite ∧ W.ncard ≤ θ ∧
      W ⊆ P₂.G.vertexSet ∧ P₂.slash W ∈ completions Unit 𝓕₁} := by
  have hn : ∀ n, WellBehaved (slashSet 𝓕₁ n) := by
    intro n
    induction n with
    | zero =>
      refine h.completions.mono ?_
      rintro P₂ ⟨-, W, hW, hc, -, P₁, hP₁, hc'⟩
      have hW0 : W = ∅ := (Set.ncard_eq_zero hW).mp hc
      subst hW0
      exact ⟨P₁, hP₁, hc'.trans (slash_empty P₂)⟩
    | succ n ih =>
      -- `K` bounds the number of roots, and we split according to the position of `v`.
      obtain ⟨K₀, hK₀⟩ := ih.completions.exists_roots_le
      refine (WellBehaved.iUnion_lt (𝓕 := fun p ↦ oneSlash (slashSet 𝓕₁ n) p (K₀ + 1)) (K₀ + 2)
        fun p _ ↦ wellBehaved_oneSlash ih p _ fun P hP ↦ ?_).mono ?_
      · exact Nat.succ_le_succ (hK₀ P ⟨P, hP, IsCompletionOf.refl P⟩)
      · rintro P₂ ⟨hdom, W, hW, hc, hsub, P₁, hP₁, hc'⟩
        obtain ⟨v, hvW⟩ : W.Nonempty := by
          rw [← Set.ncard_pos hW, hc]
          omega
        have hmem : P₂.slash {v} ∈ slashSet 𝓕₁ n := by
          refine ⟨hdom, W \ {v}, hW.subset sdiff_subset, ?_, ?_, P₁, hP₁, ?_⟩
          · rw [Set.ncard_sdiff (singleton_subset_iff.mpr hvW) (Set.finite_singleton v), hc,
            Set.ncard_singleton]
            rfl
          · exact fun x hx ↦ ⟨hsub hx.1, hx.2⟩
          · have e : ({v} : Set α) ∪ W \ {v} = W := by
              rw [Set.union_sdiff_self, Set.union_eq_self_of_subset_left
                (singleton_subset_iff.mpr hvW)]
            have := (slash_slash P₂ {v} (W \ {v})).symm
            rw [e] at this
            exact hc'.trans this
        have hslash : P₂.slash {v} ∈ completions Unit (slashSet 𝓕₁ n) :=
          ⟨_, hmem, IsCompletionOf.refl _⟩
        have hlen : P₂.G.roots.length ≤ K₀ + 1 := by
          have h₁ := length_le_of_marchSlash P₂.G.roots_nodup v
          have h₂ := hK₀ _ hslash
          exact h₁.trans (Nat.succ_le_succ h₂)
        have hv : v ∈ P₂.G.vertexSet := hsub hvW
        simp only [mem_iUnion, exists_prop]
        by_cases hroot : v ∈ P₂.G.roots
        · obtain ⟨p, hp, hpv⟩ := List.getElem_of_mem hroot
          exact ⟨p, by omega, hdom, v, hv, hslash,
            Or.inl (List.getElem?_eq_some_iff.mpr ⟨hp, hpv⟩)⟩
        · exact ⟨K₀ + 1, by omega, hdom, v, hv, hslash, Or.inr ⟨rfl, hroot⟩⟩
  refine (WellBehaved.iUnion_lt (𝓕 := slashSet 𝓕₁) (θ + 1) fun i _ ↦ hn i).mono ?_
  rintro P₂ ⟨hdom, W, hW, hc, hsub, hmem⟩
  simp only [mem_iUnion, exists_prop]
  exact ⟨W.ncard, Nat.lt_succ_of_le hc, hdom, W, hW, rfl, hsub, hmem⟩

end GraphMinor.GM20
