/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section5c

/-!
# Graph Minors XX, Section 5, (5.3)

We start with a fine rooted location which `θ`-isolates `𝒯` modulo `W`, and we want one which is
`W'`-suitable, for some `W' ⊆ W`. We take `W'` minimal, and we make each vertex of the separators of
`ℳ(𝒯, W', θ)` into a root. There are at most `θ (θ - 1)` such vertices, so the new heart is reached
from the old one by few 1-vertex extensions, and (4.8) applies.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v w

variable {α : Type u} {β : Type v}

section Addroots

variable {G : RootedHypergraph α β} {C : RootedHypergraph α β} {l : List α} (hl : l.Nodup)

theorem complementHypergraph_le_addRoots (hC : IsComplemented G C) :
    complementHypergraph G C ≤ complementHypergraph G (addRoots hl C) := by
  rw [le_iff_of_le (complementHypergraph_le hC)
    (complementHypergraph_le (isComplemented_addRoots hl C hC))]
  refine ⟨?_, subset_rfl⟩
  rintro v (h | h)
  · exact Or.inl h
  · exact Or.inr ⟨h.1, (mem_addRoots_rootSet hl C).mpr (Or.inl h.2)⟩

theorem mem_of_mem_complement_addRoots {v : α}
    (h : v ∈ (complementHypergraph G (addRoots hl C)).vertexSet) :
    v ∈ (complementHypergraph G C).vertexSet ∨ (v ∈ l ∧ v ∈ C.vertexSet ∧ v ∉ C.rootSet) := by
  rcases h with h | ⟨h₁, h₂⟩
  · exact Or.inl (Or.inl h)
  · rcases (mem_addRoots_rootSet hl C).mp h₂ with h₃ | ⟨h₃, h₄⟩
    · exact Or.inl (Or.inr ⟨h₁, h₃⟩)
    · by_cases hr : v ∈ C.rootSet
      · exact Or.inl (Or.inr ⟨h₁, hr⟩)
      · exact Or.inr ⟨h₃, h₄, hr⟩

end Addroots

section Tangle

variable {Λ : Type*} [LinearOrder Λ] {lam : Hypergraph α β × Hypergraph α β → Λ}
  {G : RootedHypergraph α β} {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {W : Set
    (α ⊕ β)} {θ θ₀ : ℕ}
  {ℒ : Set (RootedHypergraph α β)}

/-- The order of a distinction is at most the order of any separation which distinguishes. -/
theorem order_le_of_distinction {θ₁ θ₂ : ℕ} {𝒯' : Set (Hypergraph α β × Hypergraph α β)}
    (hTB : IsTieBreaker G.toHypergraph lam) (h𝒯 : IsTangle G.toHypergraph θ₁ 𝒯)
    (_h𝒯' : IsTangle G.toHypergraph θ₂ 𝒯') {A B C D : Hypergraph α β}
    (hd : IsDistinction lam 𝒯 𝒯' A B) (hC : (C, D) ∈ 𝒯) (hD : (D, C) ∈ 𝒯') :
    separationOrder A B ≤ separationOrder C D :=
  order_le_of_lam_le hTB (h𝒯.isSeparation hd.1.1) (h𝒯.isSeparation hC) (hd.2 ⟨hC, hD⟩)

/-- Subproof (1) of (5.3): if `W'` is minimal such that `ℒ` `θ`-isolates `𝒯` modulo `W'`, then for
each `(A, B) ∈ ℳ(𝒯, W', θ)` there is no `(C, D) ∈ ℒ⁻` with `A ⊆ C` and `D ⊆ B`. -/
theorem no_location_above (hTB : IsTieBreaker G.toHypergraph lam)
    (h𝒯 : IsTangle G.toHypergraph θ₀ 𝒯) (hW : W ⊆ zSet G.toHypergraph)
    (hiso : IsolatesModulo lam 𝒯 W θ G ℒ)
    (hmin : ∀ z ∈ W, ¬ IsolatesModulo lam 𝒯 (W \ {z}) θ G ℒ)
    {A B : Hypergraph α β} (hM : InM lam G.toHypergraph 𝒯 W θ A B)
    {C₀ : RootedHypergraph α β} (hC₀ : C₀ ∈ ℒ)
    (hAC : A ≤ C₀.toHypergraph) (hDB : complementHypergraph G C₀ ≤ B) : False := by
  obtain ⟨z, hzW, hzB⟩ := not_subset.mp hM.1.2.2.1
  have hnot : ¬ ∀ ⦃A : RootedHypergraph α β⦄, A ∈ ℒ → ∀ ⦃θ' : ℕ⦄
      ⦃𝒯' : Set (Hypergraph α β × Hypergraph α β)⦄, IsTangle G.toHypergraph θ' 𝒯' → θ ≤ θ' →
      (complementHypergraph G A, A.toHypergraph) ∈ 𝒯' → ∀ ⦃C D⦄, IsDistinction lam 𝒯 𝒯' C D →
      (C ≤ A.toHypergraph ∧ complementHypergraph G A ≤ D) ∨ ¬ (W \ {z}) ⊆ zSet D := fun h ↦
    hmin z hzW ⟨hiso.isRootedLocation, hiso.order_lt, hiso.subset, h⟩
  push Not at hnot
  obtain ⟨C', hC', θ'', 𝒯'', h𝒯'', hθ'', hmem, A', B', hd, hne, hsub⟩ := hnot
  -- `(A', B')` misses `z`, since `ℒ` does `θ`-isolate `𝒯` modulo `W`.
  have hzB' : z ∉ zSet B' := by
    intro hz
    rcases hiso.distinction hC' h𝒯'' hθ'' hmem hd with h | h
    · exact hne h.1 h.2
    · refine h fun y hy ↦ ?_
      by_cases hyz : y = z
      · exact hyz ▸ hz
      · exact hsub ⟨hy, hyz⟩
  have hloc := hiso.isRootedLocation
  have hsep₁ := isSeparation_complement (hloc.isComplemented hC₀)
  have hsep₂ := isSeparation_complement (hloc.isComplemented hC')
  have hmemC : (C₀.toHypergraph, complementHypergraph G C₀) ∈ 𝒯 :=
    hiso.subset ⟨C₀, hC₀, rfl⟩
  have hmemC' : (C'.toHypergraph, complementHypergraph G C') ∈ 𝒯 :=
    hiso.subset ⟨C', hC', rfl⟩
  have hordC : ∀ {X}, X ∈ ℒ →
      separationOrder X.toHypergraph (complementHypergraph G X) < θ := fun hX ↦
    separationOrder_complement_le.trans_lt (hiso.order_lt hX)
  have hlt' : separationOrder A' B' < θ :=
    (order_le_of_distinction hTB h𝒯 h𝒯'' hd hmemC' hmem).trans_lt (hordC hC')
  obtain ⟨hA'B', hB'A'⟩ := hd.1
  have hzG : z ∈ zSet G.toHypergraph := hW hzW
  have hle : A' ≤ A ∧ B ≤ B' := by
    rcases theorem_5_1_proof hTB h𝒯 h𝒯'' hM hd with h | ⟨-, h⟩ | h
    · exact h
    · -- Here `A ⊆ B'`, and then `A ∪ B = G` puts `z` in `Z(B)` or in `Z(B')`.
      have hsep : G.toHypergraph.IsSeparation A B := h𝒯.isSeparation hM.1.1
      rcases mem_zSet_of_separation hsep hzG with h₁ | h₁
      · exact absurd (zSet_mono h h₁) hzB'
      · exact absurd h₁ hzB
    · -- Here the third condition of `ℳ(𝒯, W, θ)` gives `(A', B') = (A, B)`.
      by_cases heq : (A', B') = (A, B)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        exact ⟨le_rfl, le_rfl⟩
      · have hpre : InMPre lam G.toHypergraph 𝒯 W θ A' B' :=
          ⟨hA'B', hlt', fun h' ↦ hzB' (h' hzW), θ'', 𝒯'', h𝒯'', hd⟩
        exact absurd h (hM.2 hpre heq)
  have hA'C : A' ≤ C₀.toHypergraph := hle.1.trans hAC
  have hDB' : complementHypergraph G C₀ ≤ B' := hDB.trans hle.2
  have hneC : C' ≠ C₀ := by
    rintro rfl
    exact hne hA'C hDB'
  have hDC : (complementHypergraph G C₀, C₀.toHypergraph) ∈ 𝒯'' :=
    mem_tangle_of_le h𝒯'' hsep₁ ((hordC hC₀).trans_le hθ'') hB'A' hDB'
  have hle' := hloc.le_complement hC' hC₀ hneC
  rw [complement_toHypergraph] at hle'
  exact not_le_of_mem_tangle h𝒯'' hDC hmem hle'

/-- The set `X` of the proof of (5.3): the union of the separators of `ℳ(𝒯, W, θ)`. -/
def separatorSet (lam : Hypergraph α β × Hypergraph α β → Λ) (G : Hypergraph α β)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (W : Set (α ⊕ β)) (θ : ℕ) : Set α :=
  ⋃ p ∈ {p : Hypergraph α β × Hypergraph α β | InM lam G 𝒯 W θ p.1 p.2}, (p.1 ∩ p.2).vertexSet

theorem finite_zSet (G : Hypergraph α β) : (zSet G).Finite :=
  (G.vertexSet_finite.image _).union (G.edgeSet_finite.image _)

/-- `X` has at most `|W| (θ - 1)` members, by (5.2). -/
theorem separatorSet_finite_ncard {G : Hypergraph α β} (hTB : IsTieBreaker G lam)
    (h𝒯 : IsTangle G θ₀ 𝒯) (hW : W ⊆ zSet G) :
    (separatorSet lam G 𝒯 W θ).Finite ∧
      (separatorSet lam G 𝒯 W θ).ncard ≤ W.ncard * (θ - 1) := by
  classical
  have hfin := finite_inM (lam := lam) (W := W) (θ := θ) h𝒯
  have hsep : ∀ p ∈ hfin.toFinset, ((p.1 ∩ p.2).vertexSet).Finite := fun p _ ↦
    (p.1 ∩ p.2).vertexSet_finite
  let F : Finset α := hfin.toFinset.biUnion fun p ↦ (p.1 ∩ p.2).vertexSet_finite.toFinset
  have hF : (F : Set α) = separatorSet lam G 𝒯 W θ := by
    ext v
    simp [F, separatorSet]
  rw [← hF]
  refine ⟨F.finite_toSet, ?_⟩
  rw [Set.ncard_coe_finset]
  calc F.card ≤ hfin.toFinset.card * (θ - 1) := by
        refine Finset.card_biUnion_le_card_mul _ _ _ fun p hp ↦ ?_
        have hp' : InM lam G 𝒯 W θ p.1 p.2 := hfin.mem_toFinset.mp hp
        have hlt : separationOrder p.1 p.2 < θ := hp'.1.2.1
        have : ((p.1 ∩ p.2).vertexSet_finite.toFinset).card = separationOrder p.1 p.2 := by
          rw [separationOrder, Set.ncard_eq_toFinset_card _ (p.1 ∩ p.2).vertexSet_finite]
        omega
    _ ≤ W.ncard * (θ - 1) := by
        refine Nat.mul_le_mul_right _ ?_
        rw [← Set.ncard_eq_toFinset_card _ hfin]
        exact theorem_5_2_card hTB h𝒯 ((finite_zSet G).subset hW) hW

end Tangle

section Heart

variable {P : UnlabeledPatchwork α β} {ℒ : Set (RootedHypergraph α β)}
  {Q : UnlabeledPatchwork α β} {e : RootedHypergraph α β → β}

theorem _root_.GraphMinor.GM18.IsPatchworkHeart.edgeSet_eq_image (h : IsPatchworkHeart P ℒ e Q)
  (hfine : IsFine P.G ℒ) :
    Q.G.edgeSet = e '' ℒ := by
  rw [h.edgeSet_eq, core_edgeSet_eq_empty hfine, Set.empty_union]

theorem _root_.GraphMinor.GM18.IsPatchworkHeart.dom_eq_image (h : IsPatchworkHeart P ℒ e Q)
  (hfine : IsFine P.G ℒ) :
    Q.dom = e '' ℒ := by
  rw [h.dom_eq, core_edgeSet_eq_empty hfine, Set.empty_inter, Set.empty_union]

theorem _root_.GraphMinor.GM18.IsPatchworkHeart.inc_iff (h : IsPatchworkHeart P ℒ e Q)
  (hfine : IsFine P.G ℒ) {g : β}
    {v : α} : Q.G.Inc g v ↔ ∃ C ∈ ℒ, e C = g ∧ v ∈ C.rootSet := by
  constructor
  · intro hinc
    have hg := Q.G.edge_mem_of_inc hinc
    rw [h.edgeSet_eq_image hfine] at hg
    obtain ⟨C, hC, rfl⟩ := hg
    have hv : v ∈ Q.G.ends (e C) := hinc
    rw [h.ends_newEdge hC] at hv
    exact ⟨C, hC, rfl, hv⟩
  · rintro ⟨C, hC, rfl, hv⟩
    have hv' : v ∈ Q.G.ends (e C) := by
      rw [h.ends_newEdge hC]
      exact hv
    exact hv'

theorem _root_.GraphMinor.GM18.IsPatchworkHeart.finite (h : IsPatchworkHeart P ℒ e Q)
  (hfine : IsFine P.G ℒ) :
    ℒ.Finite := by
  refine Set.Finite.of_finite_image ?_ h.injOn_newEdge
  rw [← h.edgeSet_eq_image hfine]
  exact Q.G.edgeSet_finite

/-- Replacing each `C ∈ ℒ` by `addRoots hl C` moves a heart along a chain of 1-vertex extensions. -/
theorem heart_addRoots {l : List α} (hl : l.Nodup) (hfine : IsFine P.G ℒ)
    (h : IsPatchworkHeart P ℒ e Q) (hfine' : IsFine P.G (addRoots hl '' ℒ)) :
    ∃ Q', HasPatchworkHeart P (addRoots hl '' ℒ) Q' ∧
      ChainData Q Q' {v | v ∈ P.G.vertexSet ∧ v ∈ l ∧ v ∉ (rootedLocationCore P.G ℒ).vertexSet}
        := by
  classical
  have hloc := h.isRootedLocation
  have : Nonempty (RootedHypergraph α β) := ⟨P.G⟩
  have hinj := injOn_addRoots hl hloc
  set f := addRoots (β := β) hl with hf
  let e' : RootedHypergraph α β → β := fun C ↦ e (Function.invFunOn f ℒ C)
  have hinv : ∀ {C}, C ∈ ℒ → Function.invFunOn f ℒ (f C) = C := fun hC ↦
    hinj (Function.invFunOn_mem ⟨_, hC, rfl⟩) hC (Function.invFunOn_eq ⟨_, hC, rfl⟩)
  have he' : ∀ {C}, C ∈ ℒ → e' (f C) = e C := fun hC ↦ congrArg e (hinv hC)
  have hinj' : InjOn e' (f '' ℒ) := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ heq
    rw [he' hA, he' hB] at heq
    rw [h.injOn_newEdge hA hB heq]
  have hfin := h.finite hfine
  obtain ⟨Q', hQ'⟩ := exists_heart (isRootedLocation_addRoots hl hloc) hfine' (hfin.image f) hinj'
  refine ⟨Q', ⟨e', hQ'⟩, ?_⟩
  have himage : e' '' (f '' ℒ) = e '' ℒ := by
    ext g
    constructor
    · rintro ⟨_, ⟨C, hC, rfl⟩, rfl⟩
      exact ⟨C, hC, (he' hC).symm⟩
    · rintro ⟨C, hC, rfl⟩
      exact ⟨f C, ⟨C, hC, rfl⟩, he' hC⟩
  have hinc' : ∀ {g v}, Q'.G.Inc g v ↔ ∃ C ∈ ℒ, e C = g ∧ v ∈ (f C).rootSet := by
    intro g v
    rw [hQ'.inc_iff hfine']
    constructor
    · rintro ⟨_, ⟨C, hC, rfl⟩, h₁, h₂⟩
      exact ⟨C, hC, (he' hC).symm.trans h₁, h₂⟩
    · rintro ⟨C, hC, h₁, h₂⟩
      exact ⟨f C, ⟨C, hC, rfl⟩, (he' hC).trans h₁, h₂⟩
  have hsame : ∀ {C}, C ∈ ℒ → Q'.G.ends (e C) = Q.G.ends (e C) → f C = C := by
    intro C hC hends
    refine addRoots_eq hl C fun x hxl hxV ↦ ?_
    have h₁ : x ∈ Q'.G.ends (e C) := hinc'.mpr
      ⟨C, hC, rfl, (mem_addRoots_rootSet hl C).mpr (Or.inr ⟨hxl, hxV⟩)⟩
    rw [hends] at h₁
    obtain ⟨C', hC', h₂, h₃⟩ := (h.inc_iff hfine).mp h₁
    exact h.injOn_newEdge hC' hC h₂ ▸ h₃
  refine
  { roots_eq := hQ'.roots_eq.trans h.roots_eq.symm
    edgeSet_eq := by
      rw [hQ'.edgeSet_eq_image hfine', h.edgeSet_eq_image hfine, himage]
    dom_eq := by
      rw [hQ'.dom_eq_image hfine', h.dom_eq_image hfine, himage]
    vertexSet_eq := ?_
    disjoint := ?_
    inc_iff := ?_
    exists_edge := ?_
    same_of_ends := ?_
    sameΔ_of_ends := ?_ }
  · rw [hQ'.vertexSet_eq, h.vertexSet_eq]
    ext v
    rw [mem_core_iff, mem_union, mem_core_iff]
    constructor
    · rintro ⟨hv, hall⟩
      by_cases hc : ∀ A ∈ ℒ, v ∈ A.vertexSet → v ∈ A.rootSet
      · exact Or.inl ⟨hv, hc⟩
      · refine Or.inr ⟨hv, ?_, fun h' ↦ hc (mem_core_iff.mp h').2⟩
        push Not at hc
        obtain ⟨C, hC, h₁, h₂⟩ := hc
        rcases (mem_addRoots_rootSet hl C).mp (hall (f C) ⟨C, hC, rfl⟩ h₁) with h₃ | h₃
        · exact absurd h₃ h₂
        · exact h₃.1
    · rintro (⟨hv, hall⟩ | ⟨hv, hl', -⟩)
      · refine ⟨hv, ?_⟩
        rintro _ ⟨C, hC, rfl⟩ hvC
        exact (mem_addRoots_rootSet hl C).mpr (Or.inl (hall C hC hvC))
      · refine ⟨hv, ?_⟩
        rintro _ ⟨C, hC, rfl⟩ hvC
        exact (mem_addRoots_rootSet hl C).mpr (Or.inr ⟨hl', hvC⟩)
  · rw [Set.disjoint_left, h.vertexSet_eq]
    exact fun x hx hx' ↦ hx.2.2 hx'
  · intro g v hv
    rw [h.vertexSet_eq] at hv
    rw [h.inc_iff hfine, hinc']
    constructor
    · rintro ⟨C, hC, h₁, h₂⟩
      exact ⟨C, hC, h₁, (mem_addRoots_rootSet hl C).mpr (Or.inl h₂)⟩
    · rintro ⟨C, hC, h₁, h₂⟩
      refine ⟨C, hC, h₁, ?_⟩
      rcases (mem_addRoots_rootSet hl C).mp h₂ with h₃ | h₃
      · exact h₃
      · exact (mem_core_iff.mp hv).2 C hC h₃.2
  · rintro x ⟨hxG, hxl, hxc⟩
    have hc : ¬ ∀ A ∈ ℒ, x ∈ A.vertexSet → x ∈ A.rootSet := fun h' ↦
      hxc (mem_core_iff.mpr ⟨hxG, h'⟩)
    push Not at hc
    obtain ⟨C, hC, h₁, h₂⟩ := hc
    refine ⟨e C, ?_, hinc'.mpr ⟨C, hC, rfl, (mem_addRoots_rootSet hl C).mpr (Or.inr ⟨hxl, h₁⟩)⟩,
      ?_⟩
    · rw [h.dom_eq_image hfine]
      exact ⟨C, hC, rfl⟩
    · intro g hg
      obtain ⟨C', hC', rfl, h₃⟩ := hinc'.mp hg
      by_cases hCC : C' = C
      · rw [hCC]
      · exfalso
        have hxC' : x ∈ C'.vertexSet := by
          rcases (mem_addRoots_rootSet hl C').mp h₃ with h₄ | h₄
          · exact C'.roots_subset x h₄
          · exact h₄.2
        rcases (hloc.le_complement hC' hC hCC).vertexSet_subset hxC' with h₄ | h₄
        · exact h₄.2 h₁
        · exact h₂ h₄
  · intro g hg hends hd
    rw [h.edgeSet_eq_image hfine] at hg
    obtain ⟨C, hC, rfl⟩ := hg
    have hs := hsame hC hends
    have hfC : f C ∈ f '' ℒ := ⟨C, hC, rfl⟩
    rw [← he' hC, hQ'.μ_newEdge hfC, he' hC, h.μ_newEdge hC, hs]
  · intro g hg hends
    rw [h.edgeSet_eq_image hfine] at hg
    obtain ⟨C, hC, rfl⟩ := hg
    have hs := hsame hC hends
    have hfC : f C ∈ f '' ℒ := ⟨C, hC, rfl⟩
    rw [← he' hC, hQ'.Δ_newEdge hfC, he' hC, h.Δ_newEdge hC, hs]

end Heart

variable {ℒ : Set (RootedHypergraph α β)}

/-- A vertex of a separator of `ℳ(𝒯, W, θ)`. The set `X` of (5.3) as a list. -/
theorem mem_separatorSet_iff {Λ : Type*} [LinearOrder Λ]
    {lam : Hypergraph α β × Hypergraph α β → Λ} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {W : Set (α ⊕ β)} {θ : ℕ} {v : α} :
    v ∈ separatorSet lam G 𝒯 W θ ↔ ∃ A B, InM lam G 𝒯 W θ A B ∧ v ∈ (A ∩ B).vertexSet := by
  simp only [separatorSet, mem_iUnion, exists_prop, Prod.exists, mem_ofPred_eq]

/-- Graph Minors XX, (5.3) (page 337): "Let $\mathcal{F}$ be a well-behaved set of patchworks and
let $\theta \ge 1$. Then there is
a well-behaved set of patchworks $\mathcal{F}'$ with the following property. Let $P = (G,
\mu, \Delta)$ be a patchwork, let $\lambda$ be a tie-breaker in $G$, let $\mathcal{T}$ be a
tangle in $G$ of order $\ge \theta^2$, let $W \subseteq Z(G)$ with $|W| \le \theta$, let
$\mathcal{L}$ be a fine rooted location in $G$ that $\theta$-isolates $\mathcal{T}$ modulo
$W$, and let $\mathcal{F}$ contain a heart of $(P, \mathcal{L})$. Then there is a rooted
location $\mathcal{L}'$ in $G$ and $W' \subseteq W$ such that* * *$\mathcal{L}'$ is
$W'$-suitable and $\mathcal{F}'$ contains a heart of $(P, \mathcal{L}')$,* * *for each $(A,
B) \in \mathcal{M}(\mathcal{T}, W', \theta)$,* * *$V(A \cap B) \cap V(C) \subseteq
\bar{\pi}(C)$ for each $C \in \mathcal{L}'$, and* * *there is no $(C, D) \in \mathcal{L}'^-$
with $A \subseteq C$ and $D \subseteq B$." -/
theorem theorem_5_3_proof {𝓕 : Set (UnlabeledPatchwork α β)} (h𝓕 : WellBehaved 𝓕) {θ : ℕ} (hθ : 1
  ≤ θ) :
    ∃ 𝓕' : Set (UnlabeledPatchwork α β), WellBehaved 𝓕' ∧
      ∀ (P : UnlabeledPatchwork α β) (Λ : Type w) [LinearOrder Λ]
        (lam : Hypergraph α β × Hypergraph α β → Λ) (𝒯 : Set (Hypergraph α β × Hypergraph α β))
        (θ₀ : ℕ) (W : Set (α ⊕ β)) (ℒ : Set (RootedHypergraph α β)),
        IsTieBreaker P.G.toHypergraph lam → IsTangle P.G.toHypergraph θ₀ 𝒯 → θ ^ 2 ≤ θ₀ →
        W ⊆ zSet P.G.toHypergraph → W.ncard ≤ θ → IsFine P.G ℒ →
        IsolatesModulo lam 𝒯 W θ P.G ℒ → (∃ Q ∈ 𝓕, HasPatchworkHeart P ℒ Q) →
        ∃ (ℒ' : Set (RootedHypergraph α β)) (W' : Set (α ⊕ β)), W' ⊆ W ∧
          IsSuitable lam 𝒯 W' θ P.G ℒ' ∧ (∃ Q ∈ 𝓕', HasPatchworkHeart P ℒ' Q) ∧
          ∀ ⦃A B⦄, InM lam P.G.toHypergraph 𝒯 W' θ A B →
            (∀ C ∈ ℒ', (A ∩ B).vertexSet ∩ C.vertexSet ⊆ C.rootSet) ∧
            ∀ C ∈ ℒ', ¬ (A ≤ C.toHypergraph ∧ complementHypergraph P.G C ≤ B) := by
  classical
  refine ⟨chainSet 𝓕 (θ ^ 2), wellBehaved_chainSet h𝓕 _, ?_⟩
  intro P Λ _ lam 𝒯 θ₀ W ℒ hTB h𝒯 hθ₀ hWG hWθ hfine hiso hheart
  obtain ⟨Q₀, hQ₀, e, hQ₀e⟩ := hheart
  have hloc := hiso.isRootedLocation
  -- Choose `W'` minimal.
  have hWfin : W.Finite := (finite_zSet _).subset hWG
  have hSfin : {W' | W' ⊆ W ∧ IsolatesModulo lam 𝒯 W' θ P.G ℒ}.Finite :=
    hWfin.finite_subsets.subset fun _ h ↦ h.1
  obtain ⟨W', -, hmin⟩ := hSfin.exists_le_minimal (a := W) ⟨subset_rfl, hiso⟩
  obtain ⟨⟨hW'W, hiso'⟩, hmin'⟩ := hmin
  have hW'G : W' ⊆ zSet P.G.toHypergraph := hW'W.trans hWG
  have hno : ∀ z ∈ W', ¬ IsolatesModulo lam 𝒯 (W' \ {z}) θ P.G ℒ := by
    intro z hz hI
    have hle := hmin' (y := W' \ {z}) ⟨sdiff_subset.trans hW'W, hI⟩ sdiff_subset
    exact (hle hz).2 rfl
  obtain ⟨hXfin, hXcard⟩ := separatorSet_finite_ncard (lam := lam) (W := W') (θ := θ) hTB h𝒯 hW'G
  set X := separatorSet lam P.G.toHypergraph 𝒯 W' θ with hX
  have hW'θ : W'.ncard ≤ θ := (Set.ncard_le_ncard hW'W hWfin).trans hWθ
  have hXθ : X.ncard ≤ θ * (θ - 1) :=
    hXcard.trans (Nat.mul_le_mul_right _ hW'θ)
  have hsq : θ * (θ - 1) + θ = θ ^ 2 := by
    obtain ⟨t, rfl⟩ : ∃ t, θ = t + 1 := ⟨θ - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  let l : List α := hXfin.toFinset.toList
  have hl : l.Nodup := Finset.nodup_toList _
  have hlX : ∀ {v}, v ∈ l ↔ v ∈ X := fun {v} ↦ by simp [l]
  set f := addRoots (β := β) hl with hf
  have hC : ∀ {C}, C ∈ ℒ → IsComplemented P.G C := fun hC ↦ hloc.isComplemented hC
  have hfine' : IsFine P.G (f '' ℒ) := by
    refine ⟨fun v hv ↦ ?_, fun e he ↦ ?_⟩
    · obtain ⟨C, hC, hvC⟩ := hfine.1 v hv
      exact ⟨f C, ⟨C, hC, rfl⟩, hvC⟩
    · obtain ⟨C, hC, heC⟩ := hfine.2 e he
      exact ⟨f C, ⟨C, hC, rfl⟩, heC⟩
  obtain ⟨Q', hQ'heart, hchain⟩ := heart_addRoots hl hfine hQ₀e hfine'
  have hsub : {v | v ∈ P.G.vertexSet ∧ v ∈ l ∧
      v ∉ (rootedLocationCore P.G ℒ).vertexSet} ⊆ X := fun _ hv ↦ hlX.mp hv.2.1
  have hmem := mem_chain (𝓕 := 𝓕) (k := θ ^ 2) ⟨Q₀, hQ₀, IsCompletionOf.refl _⟩ hchain
    (hXfin.subset hsub) ((Set.ncard_le_ncard hsub hXfin).trans (by nlinarith))
  have hordC : ∀ {X : RootedHypergraph α β}, X ∈ ℒ →
      separationOrder X.toHypergraph (complementHypergraph P.G X) < θ := fun hX ↦
    separationOrder_complement_le.trans_lt (hiso.order_lt hX)
  have hθθ : θ ≤ θ ^ 2 := Nat.le_self_pow two_ne_zero _
  have hroots : ∀ {C}, C ∈ ℒ → (f C).rootSet.ncard < θ ^ 2 := by
    intro C hCℒ
    have hsub : (f C).rootSet ⊆ C.rootSet ∪ X := by
      intro v hv
      rcases (mem_addRoots_rootSet hl C).mp hv with h | h
      · exact Or.inl h
      · exact Or.inr (hlX.mp h.1)
    have h₁ := Set.ncard_le_ncard hsub ((List.finite_toSet _).union hXfin)
    have h₂ := Set.ncard_union_le C.rootSet X
    have h₃ := hiso.order_lt hCℒ
    omega
  refine ⟨f '' ℒ, W', hW'W, ?_, ⟨Q', hmem, hQ'heart⟩, ?_⟩
  · refine
    { isRootedLocation := isRootedLocation_addRoots hl hloc
      fine := hfine'
      subset := ?_
      order_lt := ?_
      distinction := ?_ }
    · rintro _ ⟨_, ⟨C, hCℒ, rfl⟩, rfl⟩
      have hCT : (C.toHypergraph, complementHypergraph P.G C) ∈ 𝒯 := hiso.subset ⟨C, hCℒ, rfl⟩
      have hc : IsComplemented P.G (f C) := isComplemented_addRoots hl C (hC hCℒ)
      rcases h𝒯.axiom1 (isSeparation_complement hc)
        (separationOrder_complement_le.trans_lt ((hroots hCℒ).trans_le hθ₀)) with h | h
      · exact h
      · exact (not_le_of_mem_tangle h𝒯 h hCT
          (complementHypergraph_le_addRoots hl (hC hCℒ))).elim
    · rintro _ ⟨C, hCℒ, rfl⟩
      exact hroots hCℒ
    · rintro θ' 𝒯' h𝒯' hθ' C' D' ⟨_, ⟨C, hCℒ, rfl⟩, heq⟩ hD A B hd
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      by_cases h3 : ∃ A' B', InM lam P.G.toHypergraph 𝒯 W' θ A' B' ∧ A ≤ A' ∧ B' ≤ B
      · exact Or.inr h3
      refine Or.inl ?_
      have hCT : (C.toHypergraph, complementHypergraph P.G C) ∈ 𝒯 := hiso.subset ⟨C, hCℒ, rfl⟩
      have hDC : (complementHypergraph P.G C, C.toHypergraph) ∈ 𝒯' :=
        mem_tangle_of_le h𝒯' (isSeparation_complement (hC hCℒ))
          ((hordC hCℒ).trans_le (hθθ.trans hθ')) hD
          (complementHypergraph_le_addRoots hl (hC hCℒ))
      have hlt : separationOrder A B < θ :=
        (order_le_of_distinction hTB h𝒯 h𝒯' hd hCT hDC).trans_lt (hordC hCℒ)
      have hW'B : W' ⊆ zSet B := by
        by_contra hn
        obtain ⟨A', B', h₁, h₂, h₃⟩ := exists_inM_above h𝒯
          (show InMPre lam P.G.toHypergraph 𝒯 W' θ A B from
            ⟨hd.1.1, hlt, hn, θ', 𝒯', h𝒯', hd⟩)
        exact h3 ⟨A', B', h₁, h₂, h₃⟩
      obtain ⟨h₁, h₂⟩ : A ≤ C.toHypergraph ∧ complementHypergraph P.G C ≤ B := by
        rcases hiso'.distinction hCℒ h𝒯' (hθθ.trans hθ') hDC hd with h | h
        · exact h
        · exact absurd hW'B h
      refine ⟨h₁, ?_⟩
      have hBG : B ≤ P.G.toHypergraph := (h𝒯.isSeparation hd.1.1).right_le
      rw [le_iff_of_le (complementHypergraph_le (isComplemented_addRoots hl C (hC hCℒ))) hBG]
      refine ⟨fun v hv ↦ ?_, h₂.edgeSet_subset⟩
      rcases mem_of_mem_complement_addRoots hl hv with h | ⟨hvl, -, -⟩
      · exact h₂.vertexSet_subset h
      · obtain ⟨A', B', hM, hvs⟩ := mem_separatorSet_iff.mp (hlX.mp hvl)
        rcases theorem_5_1_of_lt hTB h𝒯 h𝒯' hM hd hlt with h | h
        · exact absurd ⟨A', B', hM, h⟩ h3
        · exact h.2.vertexSet_subset hvs.1
  · intro A B hM
    refine ⟨?_, ?_⟩
    · rintro _ ⟨C, hCℒ, rfl⟩ v ⟨hv, hvC⟩
      exact (mem_addRoots_rootSet hl C).mpr
        (Or.inr ⟨hlX.mpr (mem_separatorSet_iff.mpr ⟨A, B, hM, hv⟩), hvC⟩)
    · rintro _ ⟨C, hCℒ, rfl⟩ ⟨h₁, h₂⟩
      exact no_location_above hTB h𝒯 hW'G hiso' hno hM hCℒ h₁
        ((complementHypergraph_le_addRoots hl (hC hCℒ)).trans h₂)

end GraphMinor.GM20
