/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section4i
public import LeanPool.GraphMinor.GM10.Section9
public import LeanPool.GraphMinor.GM10.Section10

/-!
# Graph Minors XX, Section 5, (5.1) and (5.2)

These two results describe the set `ℳ(𝒯, W, θ)`. Distinctions of tangles do not cross, by (9.4) and
(10.2) of Graph Minors X, and this gives (5.1). Members of `ℳ(𝒯, W, θ)` are then nearly disjoint,
and
each misses its own member of `W`, which gives (5.2).
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph

universe u v

variable {α : Type u} {β : Type v} {Λ : Type*} [LinearOrder Λ]
  {lam : Hypergraph α β × Hypergraph α β → Λ} {G : Hypergraph α β}
  {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {W : Set (α ⊕ β)} {θ : ℕ}

theorem zSet_mono {A B : Hypergraph α β} (h : A ≤ B) : zSet A ⊆ zSet B :=
  union_subset_union (image_mono h.vertexSet_subset) (image_mono h.edgeSet_subset)

theorem mem_zSet_of_separation {A B : Hypergraph α β} (h : G.IsSeparation A B) {z : α ⊕ β}
    (hz : z ∈ zSet G) : z ∈ zSet A ∨ z ∈ zSet B := by
  rcases hz with ⟨v, hv, rfl⟩ | ⟨e, he, rfl⟩
  · rw [← h.vertexSet_union] at hv
    exact hv.imp (fun h ↦ Or.inl ⟨v, h, rfl⟩) fun h ↦ Or.inl ⟨v, h, rfl⟩
  · rw [← h.edgeSet_union] at he
    exact he.imp (fun h ↦ Or.inr ⟨e, h, rfl⟩) fun h ↦ Or.inr ⟨e, h, rfl⟩

/-- `(A, B)` and `(C, D)` of a tangle cannot have `D ⊆ A`, because then `A ∪ C = G`, contrary to the
second tangle axiom. -/
theorem not_le_of_mem_tangle {θ₀ : ℕ} (h𝒯 : IsTangle G θ₀ 𝒯) {A B C D : Hypergraph α β}
    (hAB : (A, B) ∈ 𝒯) (hCD : (C, D) ∈ 𝒯) (hDA : D ≤ A) : False := by
  have hsep := h𝒯.isSeparation hAB
  have hsep' := h𝒯.isSeparation hCD
  refine h𝒯.axiom2 hAB hCD hCD ?_
  have hu : A ∪ C = G := by
    refine le_antisymm (union_le hsep.left_le hsep'.left_le) ?_
    rw [← hsep'.union_eq]
    have h₁ : C ≤ A ∪ C := le_union_right hsep.left_le hsep'.left_le
    have h₂ : A ≤ A ∪ C := le_union_left hsep.left_le hsep'.left_le
    exact union_le h₁ (hDA.trans h₂)
  rw [hu]
  have h₁ : G ∪ C = G := le_antisymm (union_le le_rfl hsep'.left_le)
    (le_union_left le_rfl hsep'.left_le)
  exact h₁

/-- Graph Minors XX, (5.1) (page 336), first part: "Let $(C, D) \in \mathcal{M}(\mathcal{T}, W,
\theta)$, and let $(A, B)$ be the $(\mathcal{T},
\mathcal{T}')$-distinction for some tangle $\mathcal{T}'$. Then either $A \subseteq C$ and
$D \subseteq B$, or $A \subseteq D$ and $C \subseteq B$, or $C \subseteq A$ and $B \subseteq
D$" -/
theorem theorem_5_1_proof {θ₀ θ' : ℕ} {𝒯' : Set (Hypergraph α β × Hypergraph α β)}
    (hTB : IsTieBreaker G lam) (h𝒯 : IsTangle G θ₀ 𝒯) (h𝒯' : IsTangle G θ' 𝒯')
    {A B C D : Hypergraph α β} (hM : InM lam G 𝒯 W θ C D) (hAB : IsDistinction lam 𝒯 𝒯' A B) :
    (A ≤ C ∧ D ≤ B) ∨ (A ≤ D ∧ C ≤ B) ∨ (C ≤ A ∧ B ≤ D) := by
  obtain ⟨hCD, -, -, θ'', 𝒯'', h𝒯'', hdist⟩ := hM.1
  have h₁ := GraphMinor.GM10.theorem_10_2_proof G lam θ₀ θ' 𝒯 𝒯' A B hTB h𝒯 h𝒯' hAB
  have h₂ := GraphMinor.GM10.theorem_10_2_proof G lam θ₀ θ'' 𝒯 𝒯'' C D hTB h𝒯 h𝒯'' hdist
  have hnc := GraphMinor.GM10.theorem_9_4_proof hTB h₁ h₂
  rw [SeparationsCross, not_not] at hnc
  rcases hnc with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact (not_le_of_mem_tangle h𝒯 hAB.1.1 hCD h.2).elim
  · exact Or.inr (Or.inr ⟨h.2, h.1⟩)

/-- Graph Minors XX, (5.1) (page 336), second part: "if $(A, B)$ has order $< \theta$ then one of
the first two alternatives holds." -/
theorem theorem_5_1_of_lt {θ₀ θ' : ℕ} {𝒯' : Set (Hypergraph α β × Hypergraph α β)}
    (hTB : IsTieBreaker G lam) (h𝒯 : IsTangle G θ₀ 𝒯) (h𝒯' : IsTangle G θ' 𝒯')
    {A B C D : Hypergraph α β} (hM : InM lam G 𝒯 W θ C D) (hAB : IsDistinction lam 𝒯 𝒯' A B)
    (hlt : separationOrder A B < θ) : (A ≤ C ∧ D ≤ B) ∨ (A ≤ D ∧ C ≤ B) := by
  rcases theorem_5_1_proof hTB h𝒯 h𝒯' hM hAB with h | h | ⟨hCA, hBD⟩
  · exact Or.inl h
  · exact Or.inr h
  · obtain ⟨⟨-, -, hW, -⟩, hmax⟩ := hM
    have hpre : InMPre lam G 𝒯 W θ A B :=
      ⟨hAB.1.1, hlt, fun h ↦ hW (h.trans (zSet_mono hBD)), θ', 𝒯', h𝒯', hAB⟩
    by_cases heq : (A, B) = (C, D)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact Or.inl ⟨le_rfl, le_rfl⟩
    · exact absurd ⟨hCA, hBD⟩ (hmax hpre heq)

/-- Graph Minors XX, (5.2) (page 337), first part: "If $(A, B), (A', B') \in
\mathcal{M}(\mathcal{T}, W, \theta)$ are distinct then $A \subseteq
B'$" -/
theorem theorem_5_2_proof {θ₀ : ℕ} (hTB : IsTieBreaker G lam) (h𝒯 : IsTangle G θ₀ 𝒯)
    {A B A' B' : Hypergraph α β} (hM : InM lam G 𝒯 W θ A B) (hM' : InM lam G 𝒯 W θ A' B')
    (hne : (A, B) ≠ (A', B')) : A ≤ B' := by
  obtain ⟨⟨-, hlt, -, θ₁, 𝒯₁, h𝒯₁, hd⟩, -⟩ := id hM
  obtain ⟨⟨-, hlt', -, θ₂, 𝒯₂, h𝒯₂, hd'⟩, -⟩ := id hM'
  rcases theorem_5_1_of_lt hTB h𝒯 h𝒯₁ hM' hd hlt with h | h
  · rcases theorem_5_1_of_lt hTB h𝒯 h𝒯₂ hM hd' hlt' with h' | h'
    · exact absurd (by rw [le_antisymm h.1 h'.1, le_antisymm h'.2 h.2]) hne
    · exact h'.2
  · exact h.1

/-- Graph Minors XX, (5.2) (page 337), second part: "`ℳ(𝒯, W, θ)` has cardinality `≤ |W|`." -/
theorem theorem_5_2_card {θ₀ : ℕ} (hTB : IsTieBreaker G lam) (h𝒯 : IsTangle G θ₀ 𝒯)
    (hW : W.Finite) (hWG : W ⊆ zSet G) :
    {p : Hypergraph α β × Hypergraph α β | InM lam G 𝒯 W θ p.1 p.2}.ncard ≤ W.ncard := by
  classical
  have hz : ∀ p : Hypergraph α β × Hypergraph α β, InM lam G 𝒯 W θ p.1 p.2 →
      ∃ z ∈ W, z ∉ zSet p.2 := fun p hp ↦ not_subset.mp hp.1.2.2.1
  obtain hemp | ⟨p₀, hp₀⟩ := Set.eq_empty_or_nonempty
    {p : Hypergraph α β × Hypergraph α β | InM lam G 𝒯 W θ p.1 p.2}
  · rw [hemp, Set.ncard_empty]
    exact Nat.zero_le _
  have hne : Nonempty (α ⊕ β) := ⟨(hz p₀ hp₀).choose⟩
  choose! z hzW hzB using hz
  refine Set.ncard_le_ncard_of_injOn z (fun p hp ↦ hzW p hp) ?_ hW
  rintro ⟨A, B⟩ hp ⟨A', B'⟩ hp' heq
  by_contra hne
  have hle := theorem_5_2_proof hTB h𝒯 hp hp' hne
  have hsep : G.IsSeparation A B := h𝒯.isSeparation hp.1.1
  have h₁ := hzB _ hp
  have h₂ := hzB _ hp'
  rcases mem_zSet_of_separation hsep (hWG (hzW _ hp)) with h | h
  · refine h₂ ?_
    rw [← heq]
    exact zSet_mono hle h
  · exact h₁ h

end GraphMinor.GM20
