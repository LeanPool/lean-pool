/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section5f

/-!
# Graph Minors XX, Section 5, (5.4)

Now each member of `ℒ` is cut along the separations of `ℳ(𝒯, W, θ)`, using `(A_i : 1 ≤ i ≤ k)` and
`A_0 = G⁻ ∩ B_1 ∩ ⋯ ∩ B_k`. The new location is still `W`-suitable, and its members each lie on one
side of each member of `ℳ(𝒯, W, θ)`. The heart of the old location is a condensation of the new
heart, so (4.10) applies.

We ask for `β` to be infinite, since the new location may have more members than the old one and the
new heart needs one new edge for each.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v w

variable {α : Type u} {β : Type v}

/-- The hypergraph `A_0 = G⁻ ∩ B_1 ∩ ⋯ ∩ B_k`, for `ℳ = {(A_i, B_i)}`. -/
def commonPart (G : Hypergraph α β) (ℳ : Set (Hypergraph α β × Hypergraph α β)) :
    Hypergraph α β where
  vertexSet := {v ∈ G.vertexSet | ∀ p ∈ ℳ, v ∈ p.2.vertexSet}
  edgeSet := {e ∈ G.edgeSet | ∀ p ∈ ℳ, e ∈ p.2.edgeSet}
  Inc e v := e ∈ {e ∈ G.edgeSet | ∀ p ∈ ℳ, e ∈ p.2.edgeSet} ∧ G.Inc e v ∧
    v ∈ {v ∈ G.vertexSet | ∀ p ∈ ℳ, v ∈ p.2.vertexSet}
  vertex_mem_of_inc _ _ h := h.2.2
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := G.vertexSet_finite.subset fun _ h ↦ h.1
  edgeSet_finite := G.edgeSet_finite.subset fun _ h ↦ h.1

section

variable {G : Hypergraph α β} {ℳ : Set (Hypergraph α β × Hypergraph α β)}

theorem commonPart_le (h : ∀ p ∈ ℳ, p.2 ≤ G) : commonPart G ℳ ≤ G := by
  refine ⟨fun _ hv ↦ hv.1, fun _ he ↦ he.1, fun e he ↦ ?_⟩
  ext v
  constructor
  · intro hinc
    refine ⟨he, hinc, G.vertex_mem_of_inc hinc, fun p hp ↦ ?_⟩
    have h₁ : v ∈ G.ends e := hinc
    rw [(h p hp).ends_eq e (he.2 p hp)] at h₁
    exact p.2.vertex_mem_of_inc h₁
  · exact fun h' ↦ h'.2.1

theorem le_commonPart {X : Hypergraph α β} (h : ∀ p ∈ ℳ, p.2 ≤ G) (hX : X ≤ G)
    (hle : ∀ p ∈ ℳ, X ≤ p.2) : X ≤ commonPart G ℳ := by
  rw [le_iff_of_le hX (commonPart_le h)]
  exact ⟨fun v hv ↦ ⟨hX.vertexSet_subset hv, fun p hp ↦ (hle p hp).vertexSet_subset hv⟩,
    fun e he ↦ ⟨hX.edgeSet_subset he, fun p hp ↦ (hle p hp).edgeSet_subset he⟩⟩

end

/-- The family `(A_i : 0 ≤ i ≤ k)`. -/
def splitParts (G : Hypergraph α β) (ℳ : Set (Hypergraph α β × Hypergraph α β)) :
    Option ℳ → Hypergraph α β
  | none => commonPart G ℳ
  | some p => p.1.1

theorem IsSeparation.not_mem_of_mem {G A B : Hypergraph α β} (h : G.IsSeparation A B) {e : β}
    (he : e ∈ A.edgeSet) : e ∉ B.edgeSet := fun he' ↦ by
  have : e ∈ (A ∩ B).edgeSet := ⟨he, he'⟩
  rw [h.edgeSet_inter_eq] at this
  exact this

variable {Λ : Type*} [LinearOrder Λ] {lam : Hypergraph α β × Hypergraph α β → Λ}
  {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {W : Set (α ⊕ β)} {θ θ₀ : ℕ}
  {G : RootedHypergraph α β} {ℒ : Set (RootedHypergraph α β)}

/-- The sets `InM` of (5.4) give a `SplitFamily`. -/
theorem splitFamily_splitParts (hTB : IsTieBreaker G.toHypergraph lam)
    (h𝒯 : IsTangle G.toHypergraph θ₀ 𝒯)
    (hV : ∀ ⦃A B⦄, InM lam G.toHypergraph 𝒯 W θ A B → ∀ C ∈ ℒ,
      (A ∩ B).vertexSet ∩ C.vertexSet ⊆ C.rootSet) :
    SplitFamily G ℒ (splitParts G.toHypergraph
      {p | InM lam G.toHypergraph 𝒯 W θ p.1 p.2}) := by
  classical
  set ℳ : Set (Hypergraph α β × Hypergraph α β) := {p | InM lam G.toHypergraph 𝒯 W θ p.1 p.2}
    with hℳ
  have hsep : ∀ p ∈ ℳ, G.toHypergraph.IsSeparation p.1 p.2 := fun p hp ↦ h𝒯.isSeparation hp.1.1
  have hBle : ∀ p ∈ ℳ, p.2 ≤ G.toHypergraph := fun p hp ↦ (hsep p hp).right_le
  have hle52 : ∀ p ∈ ℳ, ∀ q ∈ ℳ, p ≠ q → p.1 ≤ q.2 := fun p hp q hq hne ↦
    theorem_5_2_proof hTB h𝒯 hp hq hne
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro (_ | ⟨p, hp⟩)
    · exact commonPart_le hBle
    · exact (hsep p hp).left_le
  · intro v hv
    by_cases h : ∀ p ∈ ℳ, v ∈ p.2.vertexSet
    · exact ⟨none, hv, h⟩
    · push Not at h
      obtain ⟨p, hp, hvp⟩ := h
      have h₁ : v ∈ p.1.vertexSet ∪ p.2.vertexSet := by
        rw [(hsep p hp).vertexSet_union]
        exact hv
      exact ⟨some ⟨p, hp⟩, h₁.resolve_right hvp⟩
  · intro e he
    by_cases h : ∀ p ∈ ℳ, e ∈ p.2.edgeSet
    · exact ⟨none, he, h⟩
    · push Not at h
      obtain ⟨p, hp, hep⟩ := h
      have h₁ : e ∈ p.1.edgeSet ∪ p.2.edgeSet := by
        rw [(hsep p hp).edgeSet_union]
        exact he
      exact ⟨some ⟨p, hp⟩, h₁.resolve_right hep⟩
  · rintro (_ | ⟨p, hp⟩) (_ | ⟨q, hq⟩) hij e he he'
    · exact hij rfl
    · exact IsSeparation.not_mem_of_mem (hsep q hq) he' (he.2 q hq)
    · exact IsSeparation.not_mem_of_mem (hsep p hp) he (he'.2 p hp)
    · have hpq : p ≠ q := fun h ↦ hij (by subst h; rfl)
      exact IsSeparation.not_mem_of_mem (hsep q hq) he'
        ((hle52 p hp q hq hpq).edgeSet_subset he)
  · rintro C hC (_ | ⟨p, hp⟩) (_ | ⟨q, hq⟩) hij v hvC hv hv'
    · exact absurd rfl hij
    · exact hV (A := q.1) (B := q.2) hq C hC ⟨⟨hv', hv.2 q hq⟩, hvC⟩
    · exact hV (A := p.1) (B := p.2) hp C hC ⟨⟨hv, hv'.2 p hp⟩, hvC⟩
    · have hpq : p ≠ q := fun h ↦ hij (by subst h; rfl)
      exact hV (A := q.1) (B := q.2) hq C hC
        ⟨⟨hv', (hle52 p hp q hq hpq).vertexSet_subset hv⟩, hvC⟩

/-- `ℒ'` lies in `𝒯` and is `W`-suitable, in the proof of (5.4). -/
theorem isSuitable_splitSet (hTB : IsTieBreaker G.toHypergraph lam)
    (h𝒯 : IsTangle G.toHypergraph θ₀ 𝒯) (hθ₀ : θ ^ 2 ≤ θ₀)
    (hS : IsSuitable lam 𝒯 W θ G ℒ)
    (hV : ∀ ⦃A B⦄, InM lam G.toHypergraph 𝒯 W θ A B → ∀ C ∈ ℒ,
      (A ∩ B).vertexSet ∩ C.vertexSet ⊆ C.rootSet)
    (hno : ∀ ⦃A B⦄, InM lam G.toHypergraph 𝒯 W θ A B → ∀ C ∈ ℒ,
      ¬ (A ≤ C.toHypergraph ∧ complementHypergraph G C ≤ B)) :
    IsSuitable lam 𝒯 W θ G (splitSet ℒ (splitParts G.toHypergraph
      {p | InM lam G.toHypergraph 𝒯 W θ p.1 p.2})) := by
  classical
  have hF := splitFamily_splitParts hTB h𝒯 hV
  set ℳ : Set (Hypergraph α β × Hypergraph α β) := {p | InM lam G.toHypergraph 𝒯 W θ p.1 p.2}
    with hℳ
  have hloc := hS.isRootedLocation
  have hcomp : ∀ {C}, C ∈ ℒ → ∀ i, IsComplemented G (piece C (splitParts G.toHypergraph ℳ i)) :=
    fun hC i ↦ isComplemented_piece hF hloc hC i
  have hsep : ∀ p ∈ ℳ, G.toHypergraph.IsSeparation p.1 p.2 := fun p hp ↦ h𝒯.isSeparation hp.1.1
  have hBle : ∀ p ∈ ℳ, p.2 ≤ G.toHypergraph := fun p hp ↦ (hsep p hp).right_le
  have hordC : ∀ {X}, X ∈ ℒ →
      separationOrder X.toHypergraph (complementHypergraph G X) < θ ^ 2 := fun hX ↦
    separationOrder_complement_le.trans_lt (hS.order_lt hX)
  refine
  { isRootedLocation := isRootedLocation_splitSet hF hloc
    fine := isFine_splitSet hF hS.fine
    subset := ?_
    order_lt := ?_
    distinction := ?_ }
  · rintro _ ⟨_, ⟨C, hC, i, rfl⟩, rfl⟩
    have hCT : (C.toHypergraph, complementHypergraph G C) ∈ 𝒯 := hS.subset ⟨C, hC, rfl⟩
    have hL := hcomp hC i
    have hc := hloc.isComplemented hC
    have hlt : separationOrder (piece C (splitParts G.toHypergraph ℳ i)).toHypergraph
        (complementHypergraph G (piece C (splitParts G.toHypergraph ℳ i))) < θ₀ :=
      separationOrder_complement_le.trans_lt
        (((ncard_piece_rootSet_le _ _).trans_lt (hS.order_lt hC)).trans_le hθ₀)
    rcases h𝒯.axiom1 (isSeparation_complement hL) hlt with h | h
    · exact h
    · exact (not_le_of_mem_tangle h𝒯 h hCT (complementHypergraph_le_piece hc hL)).elim
  · rintro _ ⟨C, hC, i, rfl⟩
    exact (ncard_piece_rootSet_le _ _).trans_lt (hS.order_lt hC)
  · rintro θ' 𝒯' h𝒯' hθ' C' D' ⟨_, ⟨C, hC, h, rfl⟩, heq⟩ hD a b hd
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    have hL := hcomp hC h
    have hc := hloc.isComplemented hC
    have hDC : (complementHypergraph G C, C.toHypergraph) ∈ 𝒯' :=
      mem_tangle_of_le h𝒯' (isSeparation_complement hc) ((hordC hC).trans_le hθ') hD
        (complementHypergraph_le_piece hc hL)
    by_cases hstar : ∃ A' B', InM lam G.toHypergraph 𝒯 W θ A' B' ∧ a ≤ A' ∧ B' ≤ b
    · exact Or.inr hstar
    obtain ⟨hac, hcb⟩ : a ≤ C.toHypergraph ∧ complementHypergraph G C ≤ b := by
      rcases hS.distinction h𝒯' hθ' ⟨C, hC, rfl⟩ hDC hd with h' | h'
      · exact h'
      · exact absurd h' hstar
    have hside : ∀ p ∈ ℳ, a ≤ p.2 ∧ p.1 ≤ b := by
      intro p hp
      rcases theorem_5_1_proof hTB h𝒯 h𝒯' (C := p.1) (D := p.2) hp hd with h' | h' | h'
      · exact absurd ⟨p.1, p.2, hp, h'⟩ hstar
      · exact h'
      · exact absurd ⟨h'.1.trans hac, hcb.trans h'.2⟩ (hno (A := p.1) (B := p.2) hp C hC)
    have haG : a ≤ G.toHypergraph := (h𝒯.isSeparation hd.1.1).left_le
    have hbG : b ≤ G.toHypergraph := (h𝒯.isSeparation hd.1.1).right_le
    -- The piece is not inside `b`, so it is the piece of `A_0`.
    have hnotb : ¬ (piece C (splitParts G.toHypergraph ℳ h)).toHypergraph ≤ b := fun hle ↦
      not_le_of_mem_tangle h𝒯' hd.1.2 hD hle
    rcases h with _ | ⟨p, hp⟩
    · refine Or.inl ⟨?_, ?_⟩
      · have ha₀ := le_commonPart hBle haG fun p hp ↦ (hside p hp).1
        exact (le_iff_of_le haG (inter_le hc.le (commonPart_le hBle))).mpr
          ⟨fun v hv ↦ ⟨hac.vertexSet_subset hv, ha₀.vertexSet_subset hv⟩,
            fun e he ↦ ⟨hac.edgeSet_subset he, ha₀.edgeSet_subset he⟩⟩
      · rw [le_iff_of_le (complementHypergraph_le hL) hbG]
        refine ⟨?_, ?_⟩
        · rintro v (⟨hvG, hv⟩ | ⟨hvG, hv⟩)
          · by_cases hvC : v ∈ C.vertexSet
            · have hv₀ : v ∉ (commonPart G.toHypergraph ℳ).vertexSet := fun h' ↦ hv ⟨hvC, h'⟩
              have : ¬ ∀ p ∈ ℳ, v ∈ p.2.vertexSet := fun h' ↦ hv₀ ⟨hvG, h'⟩
              push Not at this
              obtain ⟨p, hp, hvp⟩ := this
              have h₁ : v ∈ p.1.vertexSet ∪ p.2.vertexSet := by
                rw [(hsep p hp).vertexSet_union]
                exact hvG
              exact (hside p hp).2.vertexSet_subset (h₁.resolve_right hvp)
            · exact hcb.vertexSet_subset (Or.inl ⟨hvG, hvC⟩)
          · exact hcb.vertexSet_subset (Or.inr ⟨hvG, (mem_piece_rootSet.mp hv).1⟩)
        · rintro e ⟨heG, he⟩
          by_cases heC : e ∈ C.edgeSet
          · have he₀ : e ∉ (commonPart G.toHypergraph ℳ).edgeSet := fun h' ↦ he ⟨heC, h'⟩
            have : ¬ ∀ p ∈ ℳ, e ∈ p.2.edgeSet := fun h' ↦ he₀ ⟨heG, h'⟩
            push Not at this
            obtain ⟨p, hp, hep⟩ := this
            have h₁ : e ∈ p.1.edgeSet ∪ p.2.edgeSet := by
              rw [(hsep p hp).edgeSet_union]
              exact heG
            exact (hside p hp).2.edgeSet_subset (h₁.resolve_right hep)
          · exact hcb.edgeSet_subset ⟨heG, heC⟩
    · exact absurd ((inter_le_right hc.le (hsep p hp).left_le).trans (hside p hp).2) hnotb

/-- Graph Minors XX, (5.4) (page 339):
"**5.4.** *Let $\mathcal{F}$ be a well-behaved set of patchworks, and let $\theta \ge 1$. Then there
is a well-behaved set of patchworks $\mathcal{F}'$ with the following property. Let $P = (G, \mu,
\Delta)$ be a patchwork, let $\lambda$ be a tie-breaker in $G$, let $\mathcal{T}$ be a tangle in $G$
of order $\ge \theta^2$, and let $W \subseteq Z(G)$ with $|W| \le \theta$. Suppose that:*
* *$P$ is removable,*
* *$\mathcal{L}$ is a $W$-suitable rooted location in $G$, such that $\mathcal{F}$ contains a heart
  of $(P, \mathcal{L})$,*
* *for each $(A^*, B^*) \in \mathcal{M}(\mathcal{T}, W, \theta)$,*
  * *$V(A^* \cap B^*) \cap V(C) \subseteq \bar{\pi}(C)$ for each $C \in \mathcal{L}$, and*
  * *there is no $(C, D) \in \mathcal{L}^-$ with $A^* \subseteq C$ and $D \subseteq B^*$.*
*Then there is a $W$-suitable rooted location $\mathcal{L}'$ in $G$ such that $\mathcal{F}'$
contains a heart of $(P, \mathcal{L}')$, and for each $C \in \mathcal{L}'$ and each $(A^*, B^*) \in
\mathcal{M}(\mathcal{T}, W, \theta)$, either $C^- \subseteq A^*$ and $B^* \subseteq (G \setminus
C)^-$, or $C^- \subseteq B^*$ and $A^* \subseteq (G \setminus C)^-$.*"

Lean uses an infinite ambient edge type to provide fresh edge labels. Under the remaining
hypotheses, the Lean statement applies to every natural number `θ` and every `W`, including
the printed case `1 ≤ θ`, `W ⊆ zSet P.G.toHypergraph` and `W.ncard ≤ θ`. -/
theorem theorem_5_4_proof [Infinite β] {𝓕 : Set (UnlabeledPatchwork α β)} (h𝓕 : WellBehaved 𝓕)
  (θ : ℕ) :
    ∃ 𝓕' : Set (UnlabeledPatchwork α β), WellBehaved 𝓕' ∧
      ∀ (P : UnlabeledPatchwork α β) (Λ : Type w) [LinearOrder Λ]
        (lam : Hypergraph α β × Hypergraph α β → Λ) (𝒯 : Set (Hypergraph α β × Hypergraph α β))
        (θ₀ : ℕ) (W : Set (α ⊕ β)) (ℒ : Set (RootedHypergraph α β)),
        IsTieBreaker P.G.toHypergraph lam → IsTangle P.G.toHypergraph θ₀ 𝒯 → θ ^ 2 ≤ θ₀ →
        P.IsRemovable → IsSuitable lam 𝒯 W θ P.G ℒ → (∃ Q ∈ 𝓕, HasPatchworkHeart P ℒ Q) →
        (∀ ⦃A B⦄, InM lam P.G.toHypergraph 𝒯 W θ A B →
          (∀ C ∈ ℒ, (A ∩ B).vertexSet ∩ C.vertexSet ⊆ C.rootSet) ∧
          ∀ C ∈ ℒ, ¬ (A ≤ C.toHypergraph ∧ complementHypergraph P.G C ≤ B)) →
        ∃ ℒ' : Set (RootedHypergraph α β), IsSuitable lam 𝒯 W θ P.G ℒ' ∧
          (∃ Q ∈ 𝓕', HasPatchworkHeart P ℒ' Q) ∧
          ∀ C ∈ ℒ', ∀ ⦃A B⦄, InM lam P.G.toHypergraph 𝒯 W θ A B →
            (C.toHypergraph ≤ A ∧ B ≤ complementHypergraph P.G C) ∨
            (C.toHypergraph ≤ B ∧ A ≤ complementHypergraph P.G C) := by
  classical
  have hrem : WellBehaved {P ∈ 𝓕 | P.IsRemovable} := h𝓕.mono fun _ h ↦ h.1
  refine ⟨{P₂ | ∃ P₁ ∈ {P ∈ 𝓕 | P.IsRemovable}, IsCondensation P₁ P₂},
    theorem_4_10_proof hrem (fun _ h ↦ h.2) (fun _ h ↦ h), ?_⟩
  intro P Λ _ lam 𝒯 θ₀ W ℒ hTB h𝒯 hθ₀ hremP hS hheart hM
  obtain ⟨Q, hQ, e, hQe⟩ := hheart
  have hV : ∀ ⦃A B⦄, InM lam P.G.toHypergraph 𝒯 W θ A B → ∀ C ∈ ℒ,
      (A ∩ B).vertexSet ∩ C.vertexSet ⊆ C.rootSet := fun _ _ h ↦ (hM h).1
  have hF := splitFamily_splitParts hTB h𝒯 hV
  have hfinM := finite_inM (lam := lam) (W := W) (θ := θ) h𝒯
  have : Finite {p : Hypergraph α β × Hypergraph α β |
      InM lam P.G.toHypergraph 𝒯 W θ p.1 p.2} := hfinM
  obtain ⟨Q', hQ', hcond⟩ := exists_condensation hF hS.fine hQe
  refine ⟨_, isSuitable_splitSet hTB h𝒯 hθ₀ hS hV (fun _ _ h ↦ (hM h).2),
    ⟨Q', ⟨Q, ⟨hQ, heart_isRemovable hremP hS.fine hQe⟩, hcond⟩, hQ'⟩, ?_⟩
  have hloc := hS.isRootedLocation
  rintro _ ⟨C, hC, i, rfl⟩ A B hAB
  have hc := hloc.isComplemented hC
  have hL := isComplemented_piece hF hloc hC i
  have hsep : P.G.toHypergraph.IsSeparation A B := h𝒯.isSeparation hAB.1.1
  have hle52 : ∀ {A' B'}, InM lam P.G.toHypergraph 𝒯 W θ A' B' → (A', B') ≠ (A, B) → A' ≤ B :=
    fun h hne ↦ theorem_5_2_proof hTB h𝒯 h hAB hne
  by_cases hi : i = some ⟨(A, B), hAB⟩
  · subst hi
    refine Or.inl ⟨inter_le_right hc.le hsep.left_le, ?_⟩
    refine le_complementHypergraph_piece hL hsep.right_le ?_ ?_
    · exact fun e he he' ↦ IsSeparation.not_mem_of_mem hsep he'.2 he
    · exact fun v hv hv' ↦ (hM hAB).1 C hC ⟨⟨hv'.2, hv⟩, hv'.1⟩
  · have hAi : (splitParts P.G.toHypergraph {p | InM lam P.G.toHypergraph 𝒯 W θ p.1 p.2} i) ≤ B
    := by
      rcases i with _ | ⟨⟨A', B'⟩, hp⟩
      · have hBle : ∀ p ∈ {p : Hypergraph α β × Hypergraph α β |
            InM lam P.G.toHypergraph 𝒯 W θ p.1 p.2}, p.2 ≤ P.G.toHypergraph := fun p hp ↦
          (h𝒯.isSeparation hp.1.1).right_le
        exact (le_iff_of_le (commonPart_le hBle) hsep.right_le).mpr
          ⟨fun v hv ↦ hv.2 (A, B) hAB, fun e he ↦ he.2 (A, B) hAB⟩
      · refine hle52 hp fun h ↦ hi ?_
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        rfl
    have hLB : (piece C (splitParts P.G.toHypergraph
        {p | InM lam P.G.toHypergraph 𝒯 W θ p.1 p.2} i)).toHypergraph ≤ B :=
      (inter_le_right hc.le (hF.le i)).trans hAi
    refine Or.inr ⟨hLB, ?_⟩
    refine le_complementHypergraph_piece hL hsep.left_le ?_ ?_
    · exact fun e he he' ↦ IsSeparation.not_mem_of_mem hsep he (hLB.edgeSet_subset he')
    · exact fun v hv hv' ↦ (hM hAB).1 C hC ⟨⟨hv, hLB.vertexSet_subset hv'⟩, hv'.1⟩

end GraphMinor.GM20
