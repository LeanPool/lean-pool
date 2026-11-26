/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.TangleLemmas
public import LeanPool.GraphMinor.GM11.Section7b

/-!
# Graph Minors XII, Section 7: deletion

`theorem_7_1` is (7.1) of the paper: a member `(A', B')` of order `1` of a tangle `𝒯` restricts `𝒯`
to
a tangle in `B'` of the same order. The proof is the paper's.
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Hypergraph GraphMinor.GM10

variable {α β : Type*} {G A' B' : Hypergraph α β} {θ : ℕ}
  {𝒯 : Set (Hypergraph α β × Hypergraph α β)}

/-- The set `𝒯' = {(A ∩ B', B ∩ B') : (A, B) ∈ 𝒯}` of Graph Minors XII, (7.1) (page 259). -/
def restrictTangle (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (B' : Hypergraph α β) :
    Set (Hypergraph α β × Hypergraph α β) :=
  {p | ∃ A B : Hypergraph α β, (A, B) ∈ 𝒯 ∧ p = (A ∩ B', B ∩ B')}

private theorem restricted_tangle_covers_no_triple
    {α : Type*}
    {β : Type*}
    {G : Hypergraph α β}
    {A' : Hypergraph α β}
    {B' : Hypergraph α β}
    {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (hT : IsTangle G θ 𝒯)
    (hm : (A', B') ∈ 𝒯)
    (hsep' : G.IsSeparation A' B')
    (hAG : A' ≤ G)
    (hBG : B' ≤ G)
    (v : α)
    (hv : (A' ∩ B').vertexSet = {v})
    (hvA : v ∈ A'.vertexSet)
    (hvB : v ∈ B'.vertexSet)
    (hvv : ∀ x ∈ A'.vertexSet, x ∈ B'.vertexSet → x = v)
    (hV : A'.vertexSet ∪ B'.vertexSet = G.vertexSet)
    (hE : A'.edgeSet ∪ B'.edgeSet = G.edgeSet)
    (key : ∀ {A B : Hypergraph α β}, B'.IsSeparation A B → A.separationOrder B < θ → v ∈
      A.vertexSet → (A, B) ∈ restrictTangle 𝒯 B' ∨ (B, A) ∈ restrictTangle 𝒯 B') :
    ∀ {A₁ B₁ A₂ B₂ A₃ B₃ : Hypergraph α β}, (A₁, B₁) ∈ 𝒯 → (A₂, B₂) ∈ 𝒯 → (A₃, B₃) ∈ 𝒯 →
      B'.vertexSet ⊆ A₁.vertexSet ∪ A₂.vertexSet ∪ A₃.vertexSet → B'.edgeSet ⊆ A₁.edgeSet ∪
      A₂.edgeSet ∪ A₃.edgeSet → v ∈ A₁.vertexSet → False := by
  intro A₁ B₁ A₂ B₂ A₃ B₃ h₁ h₂ h₃ hcV hcE hv₁
  have s₁ := hT.isSeparation h₁
  have s₂ := hT.isSeparation h₂
  have s₃ := hT.isSeparation h₃
  have hsep := hsep'.union_inter s₁
  have hUl : A' ∪ A₁ ≤ G := hsep.left_le
  have hord : separationOrder (A' ∪ A₁) (B' ∩ B₁) < θ := by
    refine lt_of_le_of_lt (ncard_le_ncard ?_ (A₁ ∩ B₁).vertexSet_finite) (hT.order_lt h₁)
    rintro x ⟨h | h, h'⟩
    · have := hvv x h h'.1
      subst this
      exact ⟨hv₁, h'.2⟩
    · exact ⟨h, h'.2⟩
  have hmem₁ : (A' ∪ A₁, B' ∩ B₁) ∈ 𝒯 := by
    refine (hT.axiom1 hsep hord).resolve_right fun h => ?_
    refine hT.axiom2 hm h₁ h ?_
    refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq
      (union_le (union_le hAG s₁.left_le) hsep.right_le) le_rfl ?_ ?_
    · refine subset_antisymm (union_subset (union_subset hAG.vertexSet_subset
        s₁.left_le.vertexSet_subset) hsep.right_le.vertexSet_subset) fun x hx => ?_
      rw [← hV] at hx
      rcases hx with h' | h'
      · exact Or.inl (Or.inl h')
      · have : x ∈ A₁.vertexSet ∪ B₁.vertexSet := by
          rw [s₁.vertexSet_union]
          exact hBG.vertexSet_subset h'
        rcases this with h'' | h''
        · exact Or.inl (Or.inr h'')
        · exact Or.inr ⟨h', h''⟩
    · refine subset_antisymm (union_subset (union_subset hAG.edgeSet_subset
        s₁.left_le.edgeSet_subset) hsep.right_le.edgeSet_subset) fun x hx => ?_
      rw [← hE] at hx
      rcases hx with h' | h'
      · exact Or.inl (Or.inl h')
      · have : x ∈ A₁.edgeSet ∪ B₁.edgeSet := by
          rw [s₁.edgeSet_union]
          exact hBG.edgeSet_subset h'
        rcases this with h'' | h''
        · exact Or.inl (Or.inr h'')
        · exact Or.inr ⟨h', h''⟩
  refine hT.axiom2 hmem₁ h₂ h₃ ?_
  refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq
    (union_le (union_le hUl s₂.left_le) s₃.left_le) le_rfl ?_ ?_
  · refine subset_antisymm (union_subset (union_subset hUl.vertexSet_subset
      s₂.left_le.vertexSet_subset) s₃.left_le.vertexSet_subset) fun x hx => ?_
    rw [← hV] at hx
    rcases hx with h' | h'
    · exact Or.inl (Or.inl (Or.inl h'))
    · rcases hcV h' with (h'' | h'') | h''
      · exact Or.inl (Or.inl (Or.inr h''))
      · exact Or.inl (Or.inr h'')
      · exact Or.inr h''
  · refine subset_antisymm (union_subset (union_subset hUl.edgeSet_subset
      s₂.left_le.edgeSet_subset) s₃.left_le.edgeSet_subset) fun x hx => ?_
    rw [← hE] at hx
    rcases hx with h' | h'
    · exact Or.inl (Or.inl (Or.inl h'))
    · rcases hcE h' with (h'' | h'') | h''
      · exact Or.inl (Or.inl (Or.inr h''))
      · exact Or.inl (Or.inr h'')
      · exact Or.inr h''

/-- **(7.1)** of Graph Minors XII (page 267): "Let* $\mathscr{T}$ *be a tangle of order* $\theta \ge
1$ *in a graph* $G$, *and let* $(A',
B') \in \mathscr{T}$ *have order* $1$. *Let* $$\mathscr{T}' = \{(A \cap B', B \cap B') : (A,
B) \in \mathscr{T}\};$$ *then* $\mathscr{T}'$ *is a tangle in* $B'$ *of order* $\theta$." The proof
works for hypergraphs. -/
theorem theorem_7_1_proof (hT : IsTangle G θ 𝒯) (hm : (A', B') ∈ 𝒯) (h1 : separationOrder A' B'
  = 1) :
    IsTangle B' θ (restrictTangle 𝒯 B') := by
  have hsep' : G.IsSeparation A' B' := hT.isSeparation hm
  have hAG : A' ≤ G := hsep'.left_le
  have hBG : B' ≤ G := hsep'.right_le
  obtain ⟨v, hv⟩ := ncard_eq_one.mp h1
  have hvA : v ∈ A'.vertexSet := by
    have : v ∈ (A' ∩ B').vertexSet := by rw [hv]; rfl
    exact this.1
  have hvB : v ∈ B'.vertexSet := by
    have : v ∈ (A' ∩ B').vertexSet := by rw [hv]; rfl
    exact this.2
  have hvv : ∀ x, x ∈ A'.vertexSet → x ∈ B'.vertexSet → x = v := fun x h₁ h₂ => by
    have : x ∈ (A' ∩ B').vertexSet := ⟨h₁, h₂⟩
    rwa [hv] at this
  have hee : ∀ e, e ∈ A'.edgeSet → e ∈ B'.edgeSet → False := fun e h₁ h₂ => by
    have : e ∈ (A' ∩ B').edgeSet := ⟨h₁, h₂⟩
    rw [hsep'.edgeSet_inter_eq] at this
    exact this
  have hV : A'.vertexSet ∪ B'.vertexSet = G.vertexSet := hsep'.vertexSet_union
  have hE : A'.edgeSet ∪ B'.edgeSet = G.edgeSet := hsep'.edgeSet_union
  -- Members of `𝒯'` are separations of `B'` of order `< θ`.
  have hmem : ∀ {A B}, (A, B) ∈ 𝒯 → B'.IsSeparation (A ∩ B') (B ∩ B') ∧
      separationOrder (A ∩ B') (B ∩ B') < θ := by
    intro A B hAB
    have hs := hT.isSeparation hAB
    have hAl : A ∩ B' ≤ B' := inter_le_right hs.left_le hBG
    have hBl : B ∩ B' ≤ B' := inter_le_right hs.right_le hBG
    refine ⟨(isSeparation_iff_of_le hAl hBl).mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · ext x
      constructor
      · rintro (h | h) <;> exact h.2
      · intro hx
        have : x ∈ A.vertexSet ∪ B.vertexSet := by
          rw [hs.vertexSet_union]
          exact hBG.vertexSet_subset hx
        rcases this with h | h
        · exact Or.inl ⟨h, hx⟩
        · exact Or.inr ⟨h, hx⟩
    · ext x
      constructor
      · rintro (h | h) <;> exact h.2
      · intro hx
        have : x ∈ A.edgeSet ∪ B.edgeSet := by
          rw [hs.edgeSet_union]
          exact hBG.edgeSet_subset hx
        rcases this with h | h
        · exact Or.inl ⟨h, hx⟩
        · exact Or.inr ⟨h, hx⟩
    · ext x
      constructor
      · rintro ⟨⟨h₁, -⟩, h₂, -⟩
        have : x ∈ (A ∩ B).edgeSet := ⟨h₁, h₂⟩
        rw [hs.edgeSet_inter_eq] at this
        exact this
      · exact fun h => h.elim
    · refine lt_of_le_of_lt (ncard_le_ncard ?_ (A ∩ B).vertexSet_finite) (hT.order_lt hAB)
      exact fun x hx => ⟨hx.1.1, hx.2.1⟩
  -- The first axiom, when `v` is in `A`.
  have key : ∀ {A B : Hypergraph α β}, B'.IsSeparation A B → separationOrder A B < θ →
      v ∈ A.vertexSet → (A, B) ∈ restrictTangle 𝒯 B' ∨ (B, A) ∈ restrictTangle 𝒯 B' := by
    intro A B hs ho hvA'
    have hAB' : A ≤ B' := hs.left_le
    have hBB' : B ≤ B' := hs.right_le
    have hUn : A ∪ A' ≤ G := union_le (hAB'.trans hBG) hAG
    have hBg : B ≤ G := hBB'.trans hBG
    have hsG : G.IsSeparation (A ∪ A') B := by
      refine (isSeparation_iff_of_le hUn hBg).mpr ⟨?_, ?_, ?_⟩
      · rw [← hV, ← hs.vertexSet_union]
        exact (union_right_comm _ _ _).trans (union_comm _ _)
      · rw [← hE, ← hs.edgeSet_union]
        exact (union_right_comm _ _ _).trans (union_comm _ _)
      · ext e
        constructor
        · rintro ⟨h | h, h'⟩
          · have : e ∈ (A ∩ B).edgeSet := ⟨h, h'⟩
            rw [hs.edgeSet_inter_eq] at this
            exact this
          · exact (hee e h (hBB'.edgeSet_subset h')).elim
        · exact fun h => h.elim
    have hoG : separationOrder (A ∪ A') B < θ := by
      refine lt_of_le_of_lt (ncard_le_ncard ?_ (A ∩ B).vertexSet_finite) ho
      rintro x ⟨h | h, h'⟩
      · exact ⟨h, h'⟩
      · have := hvv x h (hBB'.vertexSet_subset h')
        subst this
        exact ⟨hvA', h'⟩
    have e₁ : (A ∪ A') ∩ B' = A := by
      refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq (inter_le_right hUn hBG) hAB' ?_ ?_
      · ext x
        constructor
        · rintro ⟨h | h, h'⟩
          · exact h
          · exact hvv x h h' ▸ hvA'
        · exact fun h => ⟨Or.inl h, hAB'.vertexSet_subset h⟩
      · ext e
        constructor
        · rintro ⟨h | h, h'⟩
          · exact h
          · exact (hee e h h').elim
        · exact fun h => ⟨Or.inl h, hAB'.edgeSet_subset h⟩
    have e₂ : B ∩ B' = B := by
      refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq (inter_le_right hBg hBG) hBB' ?_ ?_
      · exact inter_eq_left.mpr hBB'.vertexSet_subset
      · exact inter_eq_left.mpr hBB'.edgeSet_subset
    rcases hT.axiom1 hsG hoG with h | h
    · exact Or.inl ⟨_, _, h, by rw [e₁, e₂]⟩
    · exact Or.inr ⟨_, _, h, by rw [e₁, e₂]⟩
  -- The second axiom, when `v` is in `A₁`.
  have hcover : ∀ {A₁ B₁ A₂ B₂ A₃ B₃ : Hypergraph α β}, (A₁, B₁) ∈ 𝒯 → (A₂, B₂) ∈ 𝒯 → (A₃, B₃) ∈ 𝒯 →
      B'.vertexSet ⊆ A₁.vertexSet ∪ A₂.vertexSet ∪ A₃.vertexSet →
      B'.edgeSet ⊆ A₁.edgeSet ∪ A₂.edgeSet ∪ A₃.edgeSet → v ∈ A₁.vertexSet → False := by
    exact restricted_tangle_covers_no_triple (α := α) (β := β) (G := G) (A' := A') (B' := B') (θ
      := θ) (𝒯 := 𝒯) hT hm hsep' hAG hBG v hv hvA hvB hvv hV hE key
  refine ⟨hT.one_le, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ _ ⟨A, B, hAB, heq⟩
    rw [Prod.mk.injEq] at heq
    rw [heq.1, heq.2]
    exact (hmem hAB).1
  · rintro _ _ ⟨A, B, hAB, heq⟩
    rw [Prod.mk.injEq] at heq
    rw [heq.1, heq.2]
    exact (hmem hAB).2
  · intro A B hs ho
    have : v ∈ A.vertexSet ∪ B.vertexSet := by
      rw [hs.vertexSet_union]
      exact hvB
    rcases this with h | h
    · exact key hs ho h
    · exact (key hs.symm (by rwa [separationOrder_comm]) h).symm
  · rintro _ _ _ _ _ _ ⟨A₁, B₁, h₁, he₁⟩ ⟨A₂, B₂, h₂, he₂⟩ ⟨A₃, B₃, h₃, he₃⟩ hun
    rw [Prod.mk.injEq] at he₁ he₂ he₃
    rw [he₁.1, he₂.1, he₃.1] at hun
    have hcV : B'.vertexSet ⊆ A₁.vertexSet ∪ A₂.vertexSet ∪ A₃.vertexSet := by
      intro x hx
      rw [← hun] at hx
      rcases hx with (h | h) | h
      · exact Or.inl (Or.inl h.1)
      · exact Or.inl (Or.inr h.1)
      · exact Or.inr h.1
    have hcE : B'.edgeSet ⊆ A₁.edgeSet ∪ A₂.edgeSet ∪ A₃.edgeSet := by
      intro x hx
      rw [← hun] at hx
      rcases hx with (h | h) | h
      · exact Or.inl (Or.inl h.1)
      · exact Or.inl (Or.inr h.1)
      · exact Or.inr h.1
    rcases hcV hvB with (h | h) | h
    · exact hcover h₁ h₂ h₃ hcV hcE h
    · refine hcover h₂ h₁ h₃ ?_ ?_ h
      · exact hcV.trans fun x hx => by
          rcases hx with (h | h) | h
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
      · exact hcE.trans fun x hx => by
          rcases hx with (h | h) | h
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
    · refine hcover h₃ h₁ h₂ ?_ ?_ h
      · exact hcV.trans fun x hx => by
          rcases hx with (h | h) | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
          · exact Or.inl (Or.inl h)
      · exact hcE.trans fun x hx => by
          rcases hx with (h | h) | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
          · exact Or.inl (Or.inl h)
  · rintro _ _ ⟨A, B, hAB, heq⟩ hAeq
    rw [Prod.mk.injEq] at heq
    rw [heq.1] at hAeq
    have hsub : B'.vertexSet ⊆ A.vertexSet := fun x hx => by
      rw [← hAeq] at hx
      exact hx.1
    have hs := hT.isSeparation hAB
    have hord : separationOrder B A < θ := by
      rw [separationOrder_comm]
      exact hT.order_lt hAB
    have hBA := GraphMinor.GM10.theorem_2_9_proof hT hm hs.symm hord (Or.inl hsub)
    refine hT.axiom2 hAB hBA hBA ?_
    rw [GM10.union_assoc, GM10.union_self, hs.union_eq]

end GraphMinor.GM12
