/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section6b
public import LeanPool.GraphMinor.GM10.Section6

/-!
# Graph Minors XX, Section 6, (6.2)

Let `𝒯` have order `θ₀` and let the rooted location `ℒ` have order below `θ`. When `ℒ/W` is linked
to `𝒯/W` and the tie-breaker is edge-based, `ℒ` isolates `𝒯` at threshold `θ` modulo `W ∪ {f}`.
Uncrossing a member `(A, B)` of `ℒ⁻` with a distinction `(C, D)` keeps the order by linkage.
The tie-breaker then forces `B ⊆ D` and `C ⊆ A`.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v}

theorem isTieBreaker_of_isDefinedBy {G : Hypergraph α β}
    {lam : Hypergraph α β × Hypergraph α β → ℝ ×ₗ ℝ ×ₗ ℝ} {f : β} {v : α ⊕ β → ℝ}
    (h : IsDefinedBy G lam f v) : IsTieBreaker G lam := by
  obtain ⟨hf, hv, heq⟩ := h
  have hT := theorem_6_1_proof hf hv
  refine ⟨fun A B C D h₁ h₂ ↦ ?_, fun A B C D h₁ h₂ ↦ ?_, fun A B C D h₁ h₂ hlt ↦ ?_⟩
  · rw [heq A B h₁, heq C D h₂]
    exact hT.axiom1 h₁ h₂
  · have h₃ : G.IsSeparation (A ∪ C) (B ∩ D) := h₁.union_inter h₂
    have h₄ : G.IsSeparation (A ∩ C) (B ∪ D) := (h₁.symm.union_inter h₂.symm).symm
    rw [heq A B h₁, heq C D h₂, heq _ _ h₃, heq _ _ h₄]
    exact hT.axiom2 h₁ h₂
  · rw [heq A B h₁, heq C D h₂]
    exact hT.axiom3 h₁ h₂ hlt

/-- Three subhypergraphs covering `G` have union `G`. -/
theorem union3_eq {G X Y Z : Hypergraph α β} (hX : X ≤ G) (hY : Y ≤ G) (hZ : Z ≤ G)
    (hV : ∀ x ∈ G.vertexSet, x ∈ X.vertexSet ∨ x ∈ Y.vertexSet ∨ x ∈ Z.vertexSet)
    (hE : ∀ e ∈ G.edgeSet, e ∈ X.edgeSet ∨ e ∈ Y.edgeSet ∨ e ∈ Z.edgeSet) : X ∪ Y ∪ Z = G := by
  refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq (union_le (union_le hX hY) hZ) le_rfl ?_ ?_
  · refine subset_antisymm (union_le (union_le hX hY) hZ).vertexSet_subset fun x hx ↦ ?_
    rcases hV x hx with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · refine subset_antisymm (union_le (union_le hX hY) hZ).edgeSet_subset fun x hx ↦ ?_
    rcases hE x hx with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

theorem quotient_le {A B : Hypergraph α β} (h : A ≤ B) (W : Set α) :
    quotientVertices A W ≤ quotientVertices B W := by
  refine ⟨fun v hv ↦ ⟨h.vertexSet_subset hv.1, hv.2⟩, h.edgeSet_subset, fun e he ↦ ?_⟩
  ext v
  have h₁ : (v ∈ B.ends e) ↔ v ∈ A.ends e := by rw [h.ends_eq e he]
  exact and_congr_left fun _ ↦ h₁

theorem eq_of_quotient_eq {G A B : Hypergraph α β} (hA : A ≤ G) (hB : B ≤ G) {W : Set α}
    (hWA : W ⊆ A.vertexSet) (hWB : W ⊆ B.vertexSet)
    (h : quotientVertices A W = quotientVertices B W) : A = B := by
  have hV : ∀ {x}, x ∉ W → (x ∈ A.vertexSet ↔ x ∈ B.vertexSet) := fun {x} hx ↦ by
    have h₁ : (quotientVertices A W).vertexSet = (quotientVertices B W).vertexSet := by rw [h]
    exact ⟨fun h' ↦ (h₁ ▸ (⟨h', hx⟩ : x ∈ (quotientVertices A W).vertexSet) :
        x ∈ (quotientVertices B W).vertexSet).1,
      fun h' ↦ (h₁.symm ▸ (⟨h', hx⟩ : x ∈ (quotientVertices B W).vertexSet) :
        x ∈ (quotientVertices A W).vertexSet).1⟩
  refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq hA hB ?_ ?_
  · ext x
    by_cases hx : x ∈ W
    · exact ⟨fun _ ↦ hWB hx, fun _ ↦ hWA hx⟩
    · exact hV hx
  · have h₁ : (quotientVertices A W).edgeSet = (quotientVertices B W).edgeSet := by rw [h]
    exact h₁

theorem mem_slash_rootSet {A : RootedHypergraph α β} {W : Set α} {v : α} :
    v ∈ (A.slash W).rootSet ↔ v ∈ A.rootSet ∧ v ∉ W :=
  mem_marchSlash

/-- `(G/W) \ (A/W) = (G \ A)/W`. -/
theorem complementHypergraph_slash {G A : RootedHypergraph α β} {W : Set α}
    (hc : IsComplemented G A) (hcW : IsComplemented (G.slash W) (A.slash W)) :
    complementHypergraph (G.slash W) (A.slash W) = quotientVertices (complementHypergraph G A) W
      := by
  have hle : quotientVertices (complementHypergraph G A) W ≤ quotientVertices G.toHypergraph W :=
    quotient_le (complementHypergraph_le hc) W
  refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq (complementHypergraph_le hcW) hle ?_ rfl
  ext v
  constructor
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact ⟨Or.inl ⟨h₁.1, fun h ↦ h₂ ⟨h, h₁.2⟩⟩, h₁.2⟩
    · exact ⟨Or.inr ⟨h₁.1, (mem_slash_rootSet.mp h₂).1⟩, h₁.2⟩
  · rintro ⟨⟨h₁, h₂⟩ | ⟨h₁, h₂⟩, h₃⟩
    · exact Or.inl ⟨⟨h₁, h₃⟩, fun h ↦ h₂ h.1⟩
    · exact Or.inr ⟨⟨h₁, h₃⟩, mem_slash_rootSet.mpr ⟨h₂, h₃⟩⟩

/-- `A/W` is complemented in `G/W`. -/
theorem isComplemented_slash {G A : RootedHypergraph α β} (W : Set α)
    (hc : IsComplemented G A) : IsComplemented (G.slash W) (A.slash W) := by
  refine ⟨quotient_le hc.le W, fun v hv hr ↦ ?_, fun v e hv he hinc ↦ ?_⟩
  · exact mem_slash_rootSet.mpr ⟨hc.roots_mem hv.1 (mem_slash_rootSet.mp hr).1, hv.2⟩
  · exact mem_slash_rootSet.mpr ⟨hc.inc_diff_mem hv.1 he hinc.1, hv.2⟩

variable {G : RootedHypergraph α β} {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {W : Set α}
  {ℒ : Set (RootedHypergraph α β)}

/-- What linkage of `ℒ/W` to `𝒯/W` gives for `A ∈ ℒ`. -/
theorem linked_mem {θ₀ : ℕ} (h𝒯 : IsTangle G.toHypergraph θ₀ 𝒯) (hloc : IsRootedLocation G ℒ)
    (hW : ∀ A ∈ ℒ, W ⊆ A.rootSet)
    (hlink : IsLinkedTo (G.slash W) (quotientTangle G.toHypergraph 𝒯 W) (locationSlash ℒ W))
    {A} (hA : A ∈ ℒ) : (A.toHypergraph, complementHypergraph G A) ∈ 𝒯 := by
  have hc := hloc.isComplemented hA
  have hmem := hlink.1 ⟨A.slash W, ⟨A, hA, rfl⟩, rfl⟩
  obtain ⟨-, p, hp, hWp, h₁, h₂⟩ := hmem
  have hsep := h𝒯.isSeparation hp
  simp only at h₁ h₂
  rw [complementHypergraph_slash hc (isComplemented_slash W hc)] at h₂
  have hAeq := eq_of_quotient_eq hsep.left_le hc.le (fun _ h ↦ (hWp h).1)
    (fun _ h ↦ A.roots_subset _ (hW A hA h)) h₁
  have hBeq := eq_of_quotient_eq hsep.right_le (complementHypergraph_le hc) (fun _ h ↦ (hWp h).2)
    (fun _ h ↦ Or.inr ⟨hc.le.vertexSet_subset (A.roots_subset _ (hW A hA h)), hW A hA h⟩) h₂
  rw [← hAeq, ← hBeq]
  exact hp

/-- The order of `(A⁻, (G \ A)⁻)` is at most that of any `(A', B') ∈ 𝒯` between it and `G` with
`W ⊆ V(A' ∩ B')`. -/
theorem linked_order {θ₀ : ℕ} (h𝒯 : IsTangle G.toHypergraph θ₀ 𝒯) (hloc : IsRootedLocation G ℒ)
    (hW : ∀ A ∈ ℒ, W ⊆ A.rootSet)
    (hlink : IsLinkedTo (G.slash W) (quotientTangle G.toHypergraph 𝒯 W) (locationSlash ℒ W))
    {A} (hA : A ∈ ℒ) {A' B' : Hypergraph α β} (hmem : (A', B') ∈ 𝒯)
    (hWp : W ⊆ (A' ∩ B').vertexSet) (h₁ : A.toHypergraph ≤ A')
    (h₂ : B' ≤ complementHypergraph G A) :
    separationOrder A.toHypergraph (complementHypergraph G A) ≤ separationOrder A' B' := by
  have hc := hloc.isComplemented hA
  have hsep := h𝒯.isSeparation hmem
  have hA' : A.slash W ∈ locationSlash ℒ W := ⟨A, hA, rfl⟩
  have hq : (quotientVertices A' W, quotientVertices B' W) ∈
      quotientTangle G.toHypergraph 𝒯 W :=
    ⟨GraphMinor.GM10.IsSeparation.quotientVertices hsep W, (A', B'), hmem, hWp, rfl, rfl⟩
  have hbound := hlink.2 hA' hq (quotient_le h₁ W) (by
    rw [complementHypergraph_slash hc (isComplemented_slash W hc)]
    exact quotient_le h₂ W)
  rw [separationOrder_quotientVertices] at hbound
  have hfW : W.Finite := (A' ∩ B').vertexSet_finite.subset hWp
  have hroot : (A.slash W).rootSet = A.rootSet \ W := by
    ext v
    exact mem_slash_rootSet
  rw [hroot, Set.ncard_sdiff (hW A hA) hfW, Set.ncard_sdiff hWp hfW] at hbound
  have h₃ : W.ncard ≤ A.rootSet.ncard := Set.ncard_le_ncard (hW A hA) (List.finite_toSet _)
  have h₄ : W.ncard ≤ (A' ∩ B').vertexSet.ncard :=
    Set.ncard_le_ncard hWp (A' ∩ B').vertexSet_finite
  have h₅ := separationOrder_complement_le (G := G) (A := A)
  change _ ≤ (A' ∩ B').vertexSet.ncard
  omega

/-- Graph Minors XX, (6.2) (page 344): "Let $G$ be a rooted hypergraph, and let $\mathcal{T}$ be a
tangle in $G$ of order $\theta \ge 1$.
Let $\lambda$ be an edge-based tie-breaker in $G$ defined by $f, v$ say. Let $\mathcal{L}$
be a rooted location in $G$ with order $< \theta$, and let $W \subseteq V(G)$ be such that
$W \subseteq \bar{\pi}(A)$ for all $A \in \mathcal{L}$. Let $\mathcal{L}/W$ be linked to
$\mathcal{T}/W$. Then $\mathcal{L}$ $\theta$-isolates $\mathcal{T}$ modulo $W \cup \{f\}$."
The Lean theorem takes the order `θ₀` of `𝒯` and the isolation threshold `θ` independently.
The location has order below `θ`, and setting `θ₀ = θ` gives the printed case. -/
theorem theorem_6_2_proof {θ₀ θ : ℕ} (h𝒯 : IsTangle G.toHypergraph θ₀ 𝒯)
    {lam : Hypergraph α β × Hypergraph α β → ℝ ×ₗ ℝ ×ₗ ℝ} {f : β} {v : α ⊕ β → ℝ}
    (hlam : IsDefinedBy G.toHypergraph lam f v) (hloc : IsRootedLocation G ℒ)
    (hord : ∀ A ∈ ℒ, A.rootSet.ncard < θ) (hW : ∀ A ∈ ℒ, W ⊆ A.rootSet)
    (hlink : IsLinkedTo (G.slash W) (quotientTangle G.toHypergraph 𝒯 W) (locationSlash ℒ W)) :
    IsolatesModulo lam 𝒯 (Sum.inl '' W ∪ {Sum.inr f}) θ G ℒ := by
  have hTB := isTieBreaker_of_isDefinedBy hlam
  have hmemA := fun {A} hA ↦ linked_mem (A := A) h𝒯 hloc hW hlink hA
  refine ⟨hloc, fun A hA ↦ hord A hA, ?_, ?_⟩
  · rintro _ ⟨A, hA, rfl⟩
    exact hmemA hA
  intro A hA θ' 𝒯' h𝒯' hθ' hBA C D hd
  by_cases hsub : (Sum.inl '' W ∪ {Sum.inr f} : Set (α ⊕ β)) ⊆ zSet D
  swap
  · exact Or.inr hsub
  refine Or.inl ?_
  have hc := hloc.isComplemented hA
  set B := complementHypergraph G A with hB
  have hsepAB : G.toHypergraph.IsSeparation A.toHypergraph B := isSeparation_complement hc
  have hAT := hmemA hA
  have hsepCD : G.toHypergraph.IsSeparation C D := h𝒯.isSeparation hd.1.1
  have hfD : f ∈ D.edgeSet := by
    rcases hsub (Or.inr rfl) with ⟨_, _, h⟩ | ⟨e, he, h⟩
    · exact absurd h (by simp)
    · exact Sum.inr_injective h ▸ he
  have hWD : W ⊆ D.vertexSet := by
    intro x hx
    rcases hsub (Or.inl ⟨x, hx, rfl⟩) with ⟨y, hy, h⟩ | ⟨_, _, h⟩
    · exact Sum.inl_injective h ▸ hy
    · exact absurd h (by simp)
  have hordAB : separationOrder A.toHypergraph B < θ :=
    separationOrder_complement_le.trans_lt (hord A hA)
  have hordCD : separationOrder C D < θ :=
    (order_le_of_distinction hTB h𝒯 h𝒯' hd hAT hBA).trans_lt hordAB
  have hordCD₀ : separationOrder C D < θ₀ := h𝒯.order_lt hd.1.1
  have hordAB₀ : separationOrder A.toHypergraph B < θ₀ := h𝒯.order_lt hAT
  have h₃ : G.toHypergraph.IsSeparation (A.toHypergraph ∪ C) (B ∩ D) := hsepAB.union_inter hsepCD
  have h₄ : G.toHypergraph.IsSeparation (A.toHypergraph ∩ C) (B ∪ D) :=
    (hsepAB.symm.union_inter hsepCD.symm).symm
  -- Subproof (1).
  have hone : lam (C, D) ≤ lam (A.toHypergraph ∩ C, B ∪ D) := by
    by_cases hle : separationOrder (A.toHypergraph ∩ C) (B ∪ D) ≤ separationOrder C D
    · have h₅ : (A.toHypergraph ∩ C, B ∪ D) ∈ 𝒯 := by
        rcases h𝒯.axiom1 h₄ (hle.trans_lt hordCD₀) with h | h
        · exact h
        · exact (not_le_of_mem_tangle h𝒯 h hAT
            (le_union_left hsepAB.right_le hsepCD.right_le)).elim
      have h₆ : (B ∪ D, A.toHypergraph ∩ C) ∈ 𝒯' := by
        rcases h𝒯'.axiom1 h₄ (hle.trans_lt (hordCD.trans_le hθ')) with h | h
        · exfalso
          refine h𝒯'.axiom2 h hBA hd.1.2 (union3_eq (inter_le hsepAB.left_le hsepCD.left_le)
            hsepAB.right_le hsepCD.right_le (fun x hx ↦ ?_) fun e he ↦ ?_)
          · rw [← hsepAB.vertexSet_union] at hx
            have hx' := hx
            rw [hsepAB.vertexSet_union, ← hsepCD.vertexSet_union] at hx'
            rcases hx with h₁ | h₁
            · rcases hx' with h₂ | h₂
              · exact Or.inl ⟨h₁, h₂⟩
              · exact Or.inr (Or.inr h₂)
            · exact Or.inr (Or.inl h₁)
          · rw [← hsepAB.edgeSet_union] at he
            have he' := he
            rw [hsepAB.edgeSet_union, ← hsepCD.edgeSet_union] at he'
            rcases he with h₁ | h₁
            · rcases he' with h₂ | h₂
              · exact Or.inl ⟨h₁, h₂⟩
              · exact Or.inr (Or.inr h₂)
            · exact Or.inr (Or.inl h₁)
        · exact h
      exact hd.2 ⟨h₅, h₆⟩
    · exact (hTB.axiom3 hsepCD h₄ (not_le.mp hle)).le
  have hlam₃ : lam (A.toHypergraph ∪ C, B ∩ D) ≤ lam (A.toHypergraph, B) := by
    rcases hTB.axiom2 hsepAB hsepCD with h | h
    · exact h
    · exact absurd h (not_lt.mpr hone)
  have hordU : separationOrder (A.toHypergraph ∪ C) (B ∩ D) ≤ separationOrder A.toHypergraph B :=
    order_le_of_lam_le hTB h₃ hsepAB hlam₃
  have hmemU : (A.toHypergraph ∪ C, B ∩ D) ∈ 𝒯 := by
    rcases h𝒯.axiom1 h₃ (hordU.trans_lt hordAB₀) with h | h
    · exact h
    · exfalso
      refine h𝒯.axiom2 hAT hd.1.1 h (union3_eq hsepAB.left_le hsepCD.left_le
        (inter_le hsepAB.right_le hsepCD.right_le) (fun x hx ↦ ?_) fun e he ↦ ?_)
      · have hx' := hx
        rw [← hsepCD.vertexSet_union] at hx'
        rw [← hsepAB.vertexSet_union] at hx
        rcases hx with h₁ | h₁
        · exact Or.inl h₁
        · rcases hx' with h₂ | h₂
          · exact Or.inr (Or.inl h₂)
          · exact Or.inr (Or.inr ⟨h₁, h₂⟩)
      · have he' := he
        rw [← hsepCD.edgeSet_union] at he'
        rw [← hsepAB.edgeSet_union] at he
        rcases he with h₁ | h₁
        · exact Or.inl h₁
        · rcases he' with h₂ | h₂
          · exact Or.inr (Or.inl h₂)
          · exact Or.inr (Or.inr ⟨h₁, h₂⟩)
  have hWU : W ⊆ ((A.toHypergraph ∪ C) ∩ (B ∩ D)).vertexSet := fun x hx ↦
    ⟨Or.inl (A.roots_subset x (hW A hA hx)),
      Or.inr ⟨hc.le.vertexSet_subset (A.roots_subset x (hW A hA hx)), hW A hA hx⟩, hWD hx⟩
  have hordL : separationOrder A.toHypergraph B ≤
      separationOrder (A.toHypergraph ∪ C) (B ∩ D) := linked_order h𝒯 hloc hW hlink hA hmemU hWU
    (le_union_left hsepAB.left_le hsepCD.left_le) (inter_le_left hsepAB.right_le hsepCD.right_le)
  have hsum := order_add_order hsepAB hsepCD
  have hordI : separationOrder C D = separationOrder (A.toHypergraph ∩ C) (B ∪ D) := by omega
  have hfC : f ∉ C.edgeSet := IsSeparation.not_mem_of_mem hsepCD.symm hfD
  have hfI : f ∉ (A.toHypergraph ∩ C).edgeSet := fun h ↦ hfC h.2
  have htr : edgeBasedTriple G.toHypergraph v D C ≤
      edgeBasedTriple G.toHypergraph v (B ∪ D) (A.toHypergraph ∩ C) := by
    have := hone
    rw [hlam.2.2 _ _ hsepCD, hlam.2.2 _ _ h₄, edgeBasedLam_of_notMem hfC,
      edgeBasedLam_of_notMem hfI] at this
    exact this
  have heq := tie_step hlam.2.1 h₄.right_le
    (zSet_mono (le_union_right hsepAB.right_le hsepCD.right_le))
    (inter_le_right hsepAB.left_le hsepCD.left_le)
    (by rw [separationOrder_comm D C, separationOrder_comm (B ∪ D) _]; exact hordI) htr
  obtain ⟨h₅, h₆⟩ := eq_of_triple_eq hlam.2.1 hsepCD.symm h₄.symm heq
  have hCA : C ≤ A.toHypergraph := by
    rw [h₆]
    exact inter_le_left hsepAB.left_le hsepCD.left_le
  have hBD : B ≤ D := by
    rw [h₅]
    exact le_union_left hsepAB.right_le hsepCD.right_le
  exact ⟨hCA, hBD⟩

end GraphMinor.GM20
