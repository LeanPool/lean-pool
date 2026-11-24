/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section5k

/-!
# Graph Minors XX, Section 6, (6.1)

The edge-based tie-breaker compares a separation first by its order, then by the weight of what lies
outside the side `A` with `f ∈ E(A)`, and last by the weight of the separator. The file first
collects the facts about weights: they grow with the set, and they are injective on subsets of
`Z(G)` by rational independence. Then the three axioms are checked as in the paper.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v}

section Weight

variable {G : Hypergraph α β} {v : α ⊕ β → ℝ}

open Classical in
theorem weight_eq_sum (G : Hypergraph α β) (v : α ⊕ β → ℝ) (X : Set (α ⊕ β)) :
    weight G v X = ∑ x ∈ (finite_zSet G).toFinset, if x ∈ X then v x else 0 := by
  have hfin : (X ∩ zSet G).Finite := (finite_zSet G).subset inter_subset_right
  rw [weight, finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext x
  simp [and_comm]

theorem weight_le (hv : ∀ x ∈ zSet G, 0 < v x) {X Y : Set (α ⊕ β)} (h : X ∩ zSet G ⊆ Y) :
    weight G v X ≤ weight G v Y := by
  classical
  rw [weight_eq_sum, weight_eq_sum]
  refine Finset.sum_le_sum fun x hx ↦ ?_
  have hxZ : x ∈ zSet G := (finite_zSet G).mem_toFinset.mp hx
  by_cases hX : x ∈ X
  · rw [ite_eq_left hX, ite_eq_left (h ⟨hX, hxZ⟩)]
  · rw [ite_eq_right hX]
    split_ifs
    · exact (hv x hxZ).le
    · exact le_rfl

/-- If `X ⊆ Y` and `Y` weighs no more than `X`, then `Y` has no more members of `Z(G)` than `X`. -/
theorem subset_of_weight_le (hv : ∀ x ∈ zSet G, 0 < v x) {X Y : Set (α ⊕ β)} (h : X ∩ zSet G ⊆ Y)
    (hw : weight G v Y ≤ weight G v X) : Y ∩ zSet G ⊆ X := by
  classical
  by_contra hn
  obtain ⟨x, ⟨hxY, hxZ⟩, hxX⟩ := not_subset.mp hn
  rw [weight_eq_sum, weight_eq_sum] at hw
  refine absurd hw (not_le.mpr (Finset.sum_lt_sum (fun y hy ↦ ?_) ⟨x, ?_, ?_⟩))
  · have hyZ : y ∈ zSet G := (finite_zSet G).mem_toFinset.mp hy
    by_cases hX : y ∈ X
    · rw [ite_eq_left hX, ite_eq_left (h ⟨hX, hyZ⟩)]
    · rw [ite_eq_right hX]
      split_ifs
      · exact (hv y hyZ).le
      · exact le_rfl
  · exact (finite_zSet G).mem_toFinset.mpr hxZ
  · rw [ite_eq_right hxX, ite_eq_left hxY]
    exact hv x hxZ

/-- Rational independence: the weight is injective on subsets of `Z(G)`. -/
theorem eq_of_weight_eq (hv : IsIndependentWeight G v) {X Y : Set (α ⊕ β)} (hX : X ⊆ zSet G)
    (hY : Y ⊆ zSet G) (h : weight G v X = weight G v Y) : X = Y := by
  classical
  have : Fintype (zSet G) := (finite_zSet G).fintype
  let g : zSet G → ℚ := fun x ↦ (if x.1 ∈ X then 1 else 0) - (if x.1 ∈ Y then 1 else 0)
  have hsum : ∑ x : zSet G, g x • v x.1 = 0 := by
    rw [weight_eq_sum, weight_eq_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib,
      Finset.sum_subtype (finite_zSet G).toFinset (p := (· ∈ zSet G))
        (fun x ↦ (finite_zSet G).mem_toFinset)] at h
    focus rw [← h]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp only [g, Rat.smul_def]
    by_cases h₁ : x.1 ∈ X <;> by_cases h₂ : x.1 ∈ Y <;> simp [h₁, h₂]
  have hg := linearIndependent_iff'.mp hv.2 Finset.univ g hsum
  have hiff : ∀ x (hx : x ∈ zSet G), x ∈ X ↔ x ∈ Y := by
    intro x hx
    have h₀ := hg ⟨x, hx⟩ (Finset.mem_univ _)
    simp only [g] at h₀
    by_cases h₁ : x ∈ X <;> by_cases h₂ : x ∈ Y <;> simp_all
  ext x
  exact ⟨fun h ↦ (hiff x (hX h)).mp h, fun h ↦ (hiff x (hY h)).mpr h⟩

end Weight

section Tie

variable {G A B C D : Hypergraph α β}

theorem le_of_zSet_subset (hA : A ≤ G) (hB : B ≤ G) (h : zSet A ⊆ zSet B) : A ≤ B := by
  rw [le_iff_of_le hA hB]
  refine ⟨fun x hx ↦ ?_, fun e he ↦ ?_⟩
  · rcases h (Or.inl ⟨x, hx, rfl⟩) with ⟨y, hy, hxy⟩ | ⟨y, _, hxy⟩
    · exact Sum.inl_injective hxy ▸ hy
    · exact absurd hxy (by simp)
  · rcases h (Or.inr ⟨e, he, rfl⟩) with ⟨y, _, hxy⟩ | ⟨y, hy, hxy⟩
    · exact absurd hxy (by simp)
    · exact Sum.inr_injective hxy ▸ hy

theorem zSet_subset (h : A ≤ G) : zSet A ⊆ zSet G := zSet_mono h

/-- The sum of the orders of `(A ∪ C, B ∩ D)` and `(A ∩ C, B ∪ D)` equals the sum of the orders of
`(A, B)` and `(C, D)`. -/
theorem order_add_order (h₁ : G.IsSeparation A B) (h₂ : G.IsSeparation C D) :
    separationOrder (A ∪ C) (B ∩ D) + separationOrder (A ∩ C) (B ∪ D) =
      separationOrder A B + separationOrder C D := by
  set X := ((A ∪ C) ∩ (B ∩ D)).vertexSet with hX
  set Y := ((A ∩ C) ∩ (B ∪ D)).vertexSet with hY
  set U := (A ∩ B).vertexSet with hU
  set W := (C ∩ D).vertexSet with hW
  have hUW : X ∪ Y = U ∪ W := by
    ext v
    constructor
    · rintro (⟨h | h, h₃, h₄⟩ | ⟨⟨h₃, h₄⟩, h | h⟩)
      · exact Or.inl ⟨h, h₃⟩
      · exact Or.inr ⟨h, h₄⟩
      · exact Or.inl ⟨h₃, h⟩
      · exact Or.inr ⟨h₄, h⟩
    · rintro (⟨h₃, h₄⟩ | ⟨h₃, h₄⟩)
      · by_cases hd : v ∈ D.vertexSet
        · exact Or.inl ⟨Or.inl h₃, h₄, hd⟩
        · have hvG : v ∈ C.vertexSet ∪ D.vertexSet := by
            rw [h₂.vertexSet_union, ← h₁.vertexSet_union]
            exact Or.inl h₃
          exact Or.inr ⟨⟨h₃, hvG.resolve_right hd⟩, Or.inl h₄⟩
      · by_cases hd : v ∈ B.vertexSet
        · exact Or.inl ⟨Or.inr h₃, hd, h₄⟩
        · have hvG : v ∈ A.vertexSet ∪ B.vertexSet := by
            rw [h₁.vertexSet_union, ← h₂.vertexSet_union]
            exact Or.inl h₃
          exact Or.inr ⟨⟨hvG.resolve_right hd, h₃⟩, Or.inr h₄⟩
  have hIJ : X ∩ Y = U ∩ W := by
    ext v
    constructor
    · rintro ⟨⟨-, h₃, h₄⟩, ⟨h₅, h₆⟩, -⟩
      exact ⟨⟨h₅, h₃⟩, h₆, h₄⟩
    · rintro ⟨⟨h₃, h₄⟩, h₅, h₆⟩
      exact ⟨⟨Or.inl h₃, h₄, h₆⟩, ⟨h₃, h₅⟩, Or.inl h₄⟩
  have hfX : X.Finite := ((A ∪ C) ∩ (B ∩ D)).vertexSet_finite
  have hfY : Y.Finite := ((A ∩ C) ∩ (B ∪ D)).vertexSet_finite
  have hfU : U.Finite := (A ∩ B).vertexSet_finite
  have hfW : W.Finite := (C ∩ D).vertexSet_finite
  have e₁ := Set.ncard_union_add_ncard_inter X Y hfX hfY
  have e₂ := Set.ncard_union_add_ncard_inter U W hfU hfW
  rw [hUW, hIJ] at e₁
  change X.ncard + Y.ncard = U.ncard + W.ncard
  omega

/-- Comparing triples: equal first terms pass to the second. -/
theorem lex_snd_le {a a' b b' c c' : ℝ} (h : toLex (a, toLex (b, c)) ≤ toLex (a', toLex (b', c')))
    (ha : a = a') : b ≤ b' := by
  subst ha
  have h₁ := Prod.Lex.toLex_le_toLex.mp h
  rcases h₁ with h₁ | ⟨-, h₁⟩
  · exact absurd h₁ (lt_irrefl _)
  · rcases Prod.Lex.toLex_le_toLex.mp h₁ with h₂ | ⟨h₂, -⟩
    · exact h₂.le
    · exact h₂.le

theorem lex_thd_le {a a' b b' c c' : ℝ} (h : toLex (a, toLex (b, c)) ≤ toLex (a', toLex (b', c')))
    (ha : a = a') (hb : b = b') : c ≤ c' := by
  subst ha
  subst hb
  have h₁ := Prod.Lex.toLex_le_toLex.mp h
  rcases h₁ with h₁ | ⟨-, h₁⟩
  · exact absurd h₁ (lt_irrefl _)
  · rcases Prod.Lex.toLex_le_toLex.mp h₁ with h₂ | ⟨-, h₂⟩
    · exact absurd h₂ (lt_irrefl _)
    · exact h₂

theorem lex_fst_le {a a' b b' c c' : ℝ} (h : toLex (a, toLex (b, c)) ≤ toLex (a', toLex (b', c'))) :
    a ≤ a' := by
  rcases Prod.Lex.toLex_le_toLex.mp h with h₁ | ⟨h₁, -⟩
  · exact h₁.le
  · exact h₁.le

variable {v : α ⊕ β → ℝ} {f : β}

theorem edgeBasedLam_of_mem (hf : f ∈ A.edgeSet) : edgeBasedLam G f v (A, B)
  = edgeBasedTriple G v A B := by
  simp [edgeBasedLam, hf]

theorem edgeBasedLam_of_notMem (hf : f ∉ A.edgeSet) :
    edgeBasedLam G f v (A, B) = edgeBasedTriple G v B A := by
  simp [edgeBasedLam, hf]

theorem mem_or_mem (h : G.IsSeparation A B) (hf : f ∈ G.edgeSet) :
    f ∈ A.edgeSet ∨ f ∈ B.edgeSet := by
  rw [← h.edgeSet_union] at hf
  exact hf

theorem zSet_sdiff_antitone {X Y : Hypergraph α β} (h : zSet X ⊆ zSet Y) :
    (zSet G \ zSet Y) ∩ zSet G ⊆ zSet G \ zSet X := fun _ hz ↦ ⟨hz.1.1, fun h' ↦ hz.1.2 (h h')⟩

/-- `u(X)` determines `Z(X)` for `X` on one side of `Y`. -/
theorem zSet_subset_of_le_weight (hv : ∀ x ∈ zSet G, 0 < v x) {X Y : Hypergraph α β}
    (hY : Y ≤ G) (hXY : zSet X ⊆ zSet Y)
    (h : weight G v (zSet G \ zSet X) ≤ weight G v (zSet G \ zSet Y)) :
    zSet Y ⊆ zSet X := by
  have hs := subset_of_weight_le hv (zSet_sdiff_antitone hXY) h
  intro z hz
  by_contra hzX
  exact (hs ⟨⟨zSet_mono hY hz, hzX⟩, zSet_mono hY hz⟩).2 hz

/-- The triple determines the separation, when `(A, B)` and `(C, D)` are separations. -/
theorem eq_of_triple_eq (hv : IsIndependentWeight G v) (h₁ : G.IsSeparation A B)
    (h₂ : G.IsSeparation C D)
    (h : edgeBasedTriple G v A B = edgeBasedTriple G v C D) : A = C ∧ B = D := by
  have h' := congrArg (fun t ↦ (ofLex t).2) h
  have h₃ : weight G v (zSet G \ zSet A) = weight G v (zSet G \ zSet C) :=
    congrArg (fun t ↦ (ofLex t).1) h'
  have h₄ : weight G v (Sum.inl '' (A ∩ B).vertexSet) = weight G v (Sum.inl '' (C ∩ D).vertexSet) :=
    congrArg (fun t ↦ (ofLex t).2) h'
  have hZ := eq_of_weight_eq hv sdiff_subset sdiff_subset h₃
  have hAZ : zSet A ⊆ zSet C := fun z hz ↦ by
    by_contra hn
    have : z ∈ zSet G \ zSet C := ⟨zSet_mono h₁.left_le hz, hn⟩
    rw [← hZ] at this
    exact this.2 hz
  have hCZ : zSet C ⊆ zSet A := fun z hz ↦ by
    by_contra hn
    have : z ∈ zSet G \ zSet A := ⟨zSet_mono h₂.left_le hz, hn⟩
    rw [hZ] at this
    exact this.2 hz
  have hAC : A = C := le_antisymm (le_of_zSet_subset h₁.left_le h₂.left_le hAZ)
    (le_of_zSet_subset h₂.left_le h₁.left_le hCZ)
  subst hAC
  have hsub : ∀ {X Y : Set α}, X ⊆ G.vertexSet → Y ⊆ G.vertexSet →
      weight G v (Sum.inl '' X) = weight G v (Sum.inl '' Y) → X = Y := by
    intro X Y hX hY hw
    have := eq_of_weight_eq hv (X := Sum.inl '' X) (Y := Sum.inl '' Y)
      (image_subset_iff.mpr fun x hx ↦ Or.inl ⟨x, hX hx, rfl⟩)
      (image_subset_iff.mpr fun x hx ↦ Or.inl ⟨x, hY hx, rfl⟩) hw
    exact (Sum.inl_injective.image_injective) this
  have hAB : A.vertexSet ∩ B.vertexSet ⊆ G.vertexSet :=
    Set.inter_subset_left.trans h₁.left_le.vertexSet_subset
  have hAD : A.vertexSet ∩ D.vertexSet ⊆ G.vertexSet :=
    Set.inter_subset_left.trans h₂.left_le.vertexSet_subset
  have hV := hsub hAB hAD h₄
  refine ⟨rfl, eq_of_le_of_vertexSet_eq_of_edgeSet_eq h₁.right_le h₂.right_le ?_ ?_⟩
  · ext x
    constructor
    · intro hx
      have hxG := h₁.right_le.vertexSet_subset hx
      rw [← h₂.vertexSet_union] at hxG
      rcases hxG with h' | h'
      · have : x ∈ A.vertexSet ∩ B.vertexSet := ⟨h', hx⟩
        rw [hV] at this
        exact this.2
      · exact h'
    · intro hx
      have hxG := h₂.right_le.vertexSet_subset hx
      rw [← h₁.vertexSet_union] at hxG
      rcases hxG with h' | h'
      · have : x ∈ A.vertexSet ∩ D.vertexSet := ⟨h', hx⟩
        rw [← hV] at this
        exact this.2
      · exact h'
  · ext e
    constructor
    · intro he
      have heG := h₁.right_le.edgeSet_subset he
      rw [← h₂.edgeSet_union] at heG
      exact heG.resolve_left fun h' ↦ IsSeparation.not_mem_of_mem h₁ h' he
    · intro he
      have heG := h₂.right_le.edgeSet_subset he
      rw [← h₁.edgeSet_union] at heG
      exact heG.resolve_left fun h' ↦ IsSeparation.not_mem_of_mem h₂ h' he

/-- The first axiom. -/
theorem edgeBased_axiom1 (hf : f ∈ G.edgeSet) (hv : IsIndependentWeight G v) :
    TieBreakerAxiom1 G (edgeBasedLam G f v) := by
  intro A B C D h₁ h₂
  have hnot : ∀ {X Y}, G.IsSeparation X Y → f ∈ X.edgeSet → f ∉ Y.edgeSet := fun h hX ↦
    IsSeparation.not_mem_of_mem h hX
  constructor
  · intro h
    rcases mem_or_mem h₁ hf with ha | ha <;> rcases mem_or_mem h₂ hf with hc | hc
    · rw [edgeBasedLam_of_mem ha, edgeBasedLam_of_mem hc] at h
      exact Or.inl (eq_of_triple_eq hv h₁ h₂ h)
    · rw [edgeBasedLam_of_mem ha, edgeBasedLam_of_notMem (hnot h₂.symm hc)] at h
      exact Or.inr (eq_of_triple_eq hv h₁ h₂.symm h)
    · rw [edgeBasedLam_of_notMem (hnot h₁.symm ha), edgeBasedLam_of_mem hc] at h
      obtain ⟨h₃, h₄⟩ := eq_of_triple_eq hv h₁.symm h₂ h
      exact Or.inr ⟨h₄, h₃⟩
    · rw [edgeBasedLam_of_notMem (hnot h₁.symm ha), edgeBasedLam_of_notMem (hnot h₂.symm hc)] at h
      obtain ⟨h₃, h₄⟩ := eq_of_triple_eq hv h₁.symm h₂.symm h
      exact Or.inl ⟨h₄, h₃⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · rcases mem_or_mem h₁ hf with ha | ha
      · rw [edgeBasedLam_of_mem ha, edgeBasedLam_of_notMem (hnot h₁ ha)]
      · rw [edgeBasedLam_of_notMem (hnot h₁.symm ha), edgeBasedLam_of_mem ha]

end Tie

end GraphMinor.GM20
