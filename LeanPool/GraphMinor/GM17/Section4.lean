/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section2
public import LeanPool.GraphMinor.GM10.Section6

import LeanPool.GraphMinor.Surface.Cuffs

/-!
# Section 4 of Graph Minors XVII: Tangles and Portrayals

This file formalizes Section 4 (pages 168–170) of N. Robertson and P. D. Seymour,
*Graph Minors. XVII. Taming a vortex*, J. Combin. Theory Ser. B 77 (1999) 162–210:
- Basic properties of `attachments`, `complSubhypergraph`, and `IsSmallWrt`.
- **Graph Minors XVII, (4.1)** (`theorem_4_1_i`, `theorem_4_1_ii`, `theorem_4_1`, page 169):
  elementary properties of small subhypergraphs relative to a tangle $\mathcal{T}$.
- **Graph Minors XVII, (4.2)** (`theorem_4_2`, page 169): the quotient tangle $\mathcal{T} / Z$
  in $G / Z$ has order $\operatorname{ord}(\mathcal{T}) - |Z|$.
- **Graph Minors XVII, (4.3)** (`theorem_4_3`, pages 169–170), with its subproof claims (1), (2),
  and (3): a $\mathcal{T}$-central portrayal of warp $\le p$ has no small subhypergraph $A \le G$
  with $< \theta - 2p$ attachments containing $\gamma(\operatorname{dom}(\gamma))$.
-/

public section

namespace GraphMinor.GM17

open Set Function Topology
open GraphMinor.Surface
open GraphMinor.GM10
open GraphMinor.Hypergraph

universe u v

/-! ## 1. Attachments, Complementary Subhypergraphs, and Small Subhypergraphs -/

section Attachments

variable {α : Type u} {β : Type v} {G A A₁ A₂ B : Hypergraph α β}

theorem mem_attachments_iff {v : α} :
    v ∈ attachments G A ↔ v ∈ A.vertexSet ∧ ∃ e ∈ G.edgeSet \ A.edgeSet, G.Inc e v :=
  Iff.rfl

theorem attachments_subset_vertexSet : attachments G A ⊆ A.vertexSet :=
  fun _ h => h.1

theorem attachments_finite : (attachments G A).Finite :=
  A.vertexSet_finite.subset attachments_subset_vertexSet

@[simp]
theorem complSubhypergraph_vertexSet (G A : Hypergraph α β) :
    (complSubhypergraph G A).vertexSet = (G.vertexSet \ A.vertexSet) ∪ attachments G A :=
  rfl

@[simp]
theorem complSubhypergraph_edgeSet (G A : Hypergraph α β) :
    (complSubhypergraph G A).edgeSet = G.edgeSet \ A.edgeSet :=
  rfl

@[simp]
theorem complSubhypergraph_inc (G A : Hypergraph α β) (e : β) (v : α) :
    (complSubhypergraph G A).Inc e v ↔ e ∈ G.edgeSet \ A.edgeSet ∧ G.Inc e v :=
  Iff.rfl

theorem complSubhypergraph_le (hA : A ≤ G) : complSubhypergraph G A ≤ G where
  vertexSet_subset :=
    union_subset sdiff_subset (attachments_subset_vertexSet.trans hA.vertexSet_subset)
  edgeSet_subset := sdiff_subset
  ends_eq e he := by
    ext v
    simp only [Hypergraph.ends, mem_ofPred_eq, complSubhypergraph_inc]
    exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩

theorem isSeparation_complSubhypergraph (hA : A ≤ G) :
    G.IsSeparation A (complSubhypergraph G A) := by
  rw [isSeparation_iff_of_le hA (complSubhypergraph_le hA)]
  refine ⟨?_, ?_, ?_⟩
  · ext v
    simp only [complSubhypergraph_vertexSet, mem_union, mem_sdiff]
    constructor
    · rintro (hvA | ⟨hvG, _⟩ | hvAtt)
      · exact hA.vertexSet_subset hvA
      · exact hvG
      · exact hA.vertexSet_subset hvAtt.1
    · intro hvG
      by_cases hvA : v ∈ A.vertexSet
      · exact Or.inl hvA
      · exact Or.inr (Or.inl ⟨hvG, hvA⟩)
  · ext e
    simp only [complSubhypergraph_edgeSet, mem_union, mem_sdiff]
    constructor
    · rintro (heA | ⟨heG, _⟩)
      · exact hA.edgeSet_subset heA
      · exact heG
    · intro heG
      by_cases heA : e ∈ A.edgeSet
      · exact Or.inl heA
      · exact Or.inr ⟨heG, heA⟩
  · exact inter_sdiff_self A.edgeSet G.edgeSet

theorem inter_complSubhypergraph_vertexSet (G A : Hypergraph α β) :
    (A ∩ complSubhypergraph G A).vertexSet = attachments G A := by
  ext v
  simp only [inter_vertexSet, complSubhypergraph_vertexSet, mem_inter_iff, mem_union, mem_sdiff]
  constructor
  · rintro ⟨hvA, ⟨_, hnot⟩ | hvAtt⟩
    · exact (hnot hvA).elim
    · exact hvAtt
  · intro hvAtt
    exact ⟨hvAtt.1, Or.inr hvAtt⟩

theorem separationOrder_complSubhypergraph (G A : Hypergraph α β) :
    separationOrder A (complSubhypergraph G A) = (attachments G A).ncard := by
  rw [separationOrder, inter_complSubhypergraph_vertexSet]

theorem attachments_subset_inter_of_isSeparation (hsep : G.IsSeparation A B) :
    attachments G A ⊆ (A ∩ B).vertexSet := by
  rintro v ⟨hvA, e, ⟨heG, heA⟩, hinc⟩
  have heAB : e ∈ A.edgeSet ∪ B.edgeSet := by rwa [hsep.edgeSet_union]
  have heB : e ∈ B.edgeSet := heAB.resolve_left heA
  have hincB : B.Inc e v := (inc_iff_of_le hsep.right_le heB).2 hinc
  exact ⟨hvA, B.vertex_mem_of_inc hincB⟩

theorem ncard_attachments_le_separationOrder (hsep : G.IsSeparation A B) :
    (attachments G A).ncard ≤ separationOrder A B :=
  ncard_le_ncard (attachments_subset_inter_of_isSeparation hsep) (A ∩ B).vertexSet_finite

theorem attachments_union_subset :
    attachments G (A₁ ∪ A₂) ⊆ attachments G A₁ ∪ attachments G A₂ := by
  rintro v ⟨hv₁ | hv₂, e, ⟨heG, heU⟩, hinc⟩
  · exact Or.inl ⟨hv₁, e, ⟨heG, fun he₁ => heU (Or.inl he₁)⟩, hinc⟩
  · exact Or.inr ⟨hv₂, e, ⟨heG, fun he₂ => heU (Or.inr he₂)⟩, hinc⟩

theorem Portrayal.attachments_cellGraph_subset_otherVertices (π : Portrayal G)
    {c : Set π.S} (_hc : c ∈ π.Γ.C) :
    attachments G (π.cellGraph c) ⊆ (π.cellGraph c).vertexSet ∩ π.otherVertices c := by
  rintro v ⟨hvc, e, ⟨heG, henot⟩, hinc⟩
  obtain ⟨c', hc', hec'⟩ := π.p1_edge e heG
  have hne : c' ≠ c := fun h => henot (h ▸ hec')
  have hinc' : (π.cellGraph c').Inc e v :=
    (inc_iff_of_le (π.cellGraph_le c' hc') hec').2 hinc
  exact ⟨hvc, c', hc', hne, (π.cellGraph c').vertex_mem_of_inc hinc'⟩

theorem IsSmallWrt.le_G {θ : ℕ} {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : IsTangle G θ 𝒯) (h : IsSmallWrt 𝒯 A) : A ≤ G := by
  rcases h with ⟨B, hAB⟩
  exact (h𝒯.isSeparation hAB).left_le

theorem IsSmallWrt.vertexSet_ne {θ : ℕ} {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : IsTangle G θ 𝒯) (h : IsSmallWrt 𝒯 A) : A.vertexSet ≠ G.vertexSet := by
  rcases h with ⟨B, hAB⟩
  exact h𝒯.axiom3 hAB

theorem IsSmallWrt.ne_G {θ : ℕ} {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : IsTangle G θ 𝒯) (h : IsSmallWrt 𝒯 A) : A ≠ G :=
  fun heq => h.vertexSet_ne h𝒯 (congrArg Hypergraph.vertexSet heq)

theorem IsSmallWrt.ncard_attachments_lt {θ : ℕ} {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : IsTangle G θ 𝒯) (h : IsSmallWrt 𝒯 A) : (attachments G A).ncard < θ := by
  rcases h with ⟨B, hAB⟩
  exact (ncard_attachments_le_separationOrder (h𝒯.isSeparation hAB)).trans_lt (h𝒯.order_lt hAB)

end Attachments

/-! ## 2. Graph Minors XVII, (4.1) and (4.2) (Page 169) -/

/-- **Graph Minors XVII, (4.1)(i)** (page 169):
If $A \subseteq G$ is small relative to a tangle $\mathcal{T}$ of order $\theta$ in $G$, then
$(A, B) \in \mathcal{T}$ for every $B \subseteq G$ such that $(A, B)$ is a separation of $G$ of
order $< \theta$. -/
theorem theorem_4_1_i {α : Type u} {β : Type v} {G A B : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    (hA : IsSmallWrt 𝒯 A) (hsep : G.IsSeparation A B) (hord : separationOrder A B < θ) :
    (A, B) ∈ 𝒯 := by
  rcases hA with ⟨B₀, hAB₀⟩
  exact GM10.theorem_2_9_proof h𝒯 hAB₀ hsep hord (Or.inr (Or.inl Subset.rfl))

/-- **Graph Minors XVII, (4.1)(ii)** (page 169):
If $A_1, A_2 \subseteq G$ are small relative to a tangle $\mathcal{T}$ of order $\theta$ in $G$,
and $A \subseteq A_1 \cup A_2$ has $< \theta$ attachments in $G$, then $A$ is small relative to
$\mathcal{T}$. -/
theorem theorem_4_1_ii {α : Type u} {β : Type v} {G A A₁ A₂ : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    (hA₁ : IsSmallWrt 𝒯 A₁) (hA₂ : IsSmallWrt 𝒯 A₂)
    (hA : A ≤ A₁ ∪ A₂) (hatt : (attachments G A).ncard < θ) :
    IsSmallWrt 𝒯 A := by
  have hA₁_le : A₁ ≤ G := hA₁.le_G h𝒯
  have hA₂_le : A₂ ≤ G := hA₂.le_G h𝒯
  have hA_le : A ≤ G := hA.trans (union_le hA₁_le hA₂_le)
  let B := complSubhypergraph G A
  have hsep : G.IsSeparation A B := isSeparation_complSubhypergraph hA_le
  have hord : separationOrder A B < θ := by
    rwa [separationOrder_complSubhypergraph]
  refine ⟨B, ?_⟩
  rcases h𝒯.axiom1 hsep hord with hAB | hBA
  · exact hAB
  · exfalso
    rcases hA₁ with ⟨B₁, hAB₁⟩
    rcases hA₂ with ⟨B₂, hAB₂⟩
    apply h𝒯.axiom2 hBA hAB₁ hAB₂
    have hU_le : B ∪ A₁ ∪ A₂ ≤ G := union_le (union_le hsep.right_le hA₁_le) hA₂_le
    apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq hU_le le_rfl
    · refine Subset.antisymm hU_le.vertexSet_subset ?_
      rw [← hsep.vertexSet_union]
      rintro v (hvA | hvB)
      · rcases hA.vertexSet_subset hvA with hv₁ | hv₂
        · exact Or.inl (Or.inr hv₁)
        · exact Or.inr hv₂
      · exact Or.inl (Or.inl hvB)
    · refine Subset.antisymm hU_le.edgeSet_subset ?_
      rw [← hsep.edgeSet_union]
      rintro e (heA | heB)
      · rcases hA.edgeSet_subset heA with he₁ | he₂
        · exact Or.inl (Or.inr he₁)
        · exact Or.inr he₂
      · exact Or.inl (Or.inl heB)

/-- **Graph Minors XVII, (4.1)** (page 169):
(i) If $A \subseteq G$ is small then $(A, B) \in \mathcal{T}$ for every $B \subseteq G$ such that
$(A, B)$ is a separation of $G$ of order $< \operatorname{ord}(\mathcal{T})$.
(ii) If $A_1, A_2 \subseteq G$ are small and $A \subseteq A_1 \cup A_2$ has
$< \operatorname{ord}(\mathcal{T})$ attachments in $G$ then $A$ is small. -/
theorem theorem_4_1_proof {α : Type u} {β : Type v} {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) :
    (∀ A B, IsSmallWrt 𝒯 A → G.IsSeparation A B → separationOrder A B < θ → (A, B) ∈ 𝒯) ∧
    (∀ A A₁ A₂, IsSmallWrt 𝒯 A₁ → IsSmallWrt 𝒯 A₂ → A ≤ A₁ ∪ A₂ →
      (attachments G A).ncard < θ → IsSmallWrt 𝒯 A) :=
  ⟨fun _ _ hA hsep hord => theorem_4_1_i h𝒯 hA hsep hord,
   fun _ _ _ hA₁ hA₂ hA hatt => theorem_4_1_ii h𝒯 hA₁ hA₂ hA hatt⟩

theorem IsSmallWrt.mono {α : Type u} {β : Type v} {G A A₁ : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    (hA₁ : IsSmallWrt 𝒯 A₁) (hA : A ≤ A₁) (hatt : (attachments G A).ncard < θ) :
    IsSmallWrt 𝒯 A := by
  have hle : A ≤ A₁ ∪ A₁ := by rw [GM10.union_self]; exact hA
  exact theorem_4_1_ii h𝒯 hA₁ hA₁ hle hatt

theorem IsSmallWrt.union {α : Type u} {β : Type v} {G A₁ A₂ : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    (hA₁ : IsSmallWrt 𝒯 A₁) (hA₂ : IsSmallWrt 𝒯 A₂)
    (hatt : (attachments G (A₁ ∪ A₂)).ncard < θ) :
    IsSmallWrt 𝒯 (A₁ ∪ A₂) :=
  theorem_4_1_ii h𝒯 hA₁ hA₂ le_rfl hatt

/-- **Graph Minors XVII, (4.2)** (page 169):
If $\mathcal{T}$ is a tangle in a hypergraph $G$, and $Z \subseteq V(G)$ with
$|Z| < \operatorname{ord}(\mathcal{T})$, then $\mathcal{T} / Z$ is a tangle in $G / Z$ of order
$\operatorname{ord}(\mathcal{T}) - |Z|$.
(Proved in Graph Minors X, Theorem (6.2).) -/
theorem theorem_4_2_proof {α : Type u} {β : Type v} {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {Z : Set α} (hZ : Z ⊆ G.vertexSet) (hZ_lt : Z.ncard < θ) :
    IsTangle (quotientVertices G Z) (θ - Z.ncard) (quotientTangle G 𝒯 Z) :=
  GM10.theorem_6_2_proof h𝒯 hZ hZ_lt

/-! ## 3. Graph Minors XVII, (4.3) (Pages 169–170) -/

/-- Attachment inclusion in Claim (1) of **Graph Minors XVII, (4.3)** (page 169):
For any internal cell $c \in C(\Gamma)$ and any subhypergraph $A \le G$ with
$\gamma(\operatorname{dom}(\gamma)) \subseteq V(A)$, every attachment of $A \cup \alpha(c)$ in $G$
is an attachment of $A$ in $G$. -/
theorem theorem_4_3_claim_1_attachments {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) {A : Hypergraph α β}
    (hdom : ∀ n ∈ π.domγ, π.nodeVertex n ∈ A.vertexSet)
    {c : Set π.S} (hc : c ∈ π.Γ.C) (hint : ¬ (c ∩ bd π.S).Nonempty) :
    attachments G (A ∪ π.cellGraph c) ⊆ attachments G A := by
  rintro v ⟨hvU, e, ⟨heG, henotU⟩, hinc⟩
  have henotA : e ∉ A.edgeSet := fun heA => henotU (Or.inl heA)
  have henotC : e ∉ (π.cellGraph c).edgeSet := fun heC => henotU (Or.inr heC)
  rcases hvU with hvA | hvC
  · exact ⟨hvA, e, ⟨heG, henotA⟩, hinc⟩
  · have hvo : v ∈ π.otherVertices c :=
      (π.attachments_cellGraph_subset_otherVertices hc ⟨hvC, e, ⟨heG, henotC⟩, hinc⟩).2
    obtain ⟨n, hn, rfl⟩ := π.p5 c hc hint v hvC hvo
    exact ⟨hdom n hn.2, e, ⟨heG, henotA⟩, hinc⟩

/-- Claim (1) in the proof of **Graph Minors XVII, (4.3)** (page 169):
For a maximal small subhypergraph $A \le G$ with $< \theta - 2p$ attachments and
$\gamma(\operatorname{dom}(\gamma)) \subseteq V(A)$, every internal cell $c \in C(\Gamma)$ satisfies
$\alpha(c) \le A$. -/
theorem theorem_4_3_claim_1 {α : Type u} {β : Type v} {G : Hypergraph α β} {θ p : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    (π : Portrayal G) (hcentral : π.IsCentral 𝒯)
    {A : Hypergraph α β} (hAsmall : IsSmallWrt 𝒯 A)
    (hatt : (attachments G A).ncard < θ - 2 * p)
    (hdom : ∀ n ∈ π.domγ, π.nodeVertex n ∈ A.vertexSet)
    (hmax : ∀ A' : Hypergraph α β, A ≤ A' → IsSmallWrt 𝒯 A' →
      (attachments G A').ncard < θ - 2 * p →
      (∀ n ∈ π.domγ, π.nodeVertex n ∈ A'.vertexSet) → A' = A)
    {c : Set π.S} (hc : c ∈ π.Γ.C) (hint : ¬ (c ∩ bd π.S).Nonempty) :
    π.cellGraph c ≤ A := by
  let A' := A ∪ π.cellGraph c
  have hA_le : A ≤ G := hAsmall.le_G h𝒯
  have hc_le : π.cellGraph c ≤ G := π.cellGraph_le c hc
  have hle_A' : A ≤ A' := le_union_left hA_le hc_le
  have hatt_sub : attachments G A' ⊆ attachments G A :=
    theorem_4_3_claim_1_attachments π hdom hc hint
  have hatt_A' : (attachments G A').ncard < θ - 2 * p :=
    (ncard_le_ncard hatt_sub attachments_finite).trans_lt hatt
  have hatt_lt_θ : (attachments G A').ncard < θ := by omega
  have hsmall_A' : IsSmallWrt 𝒯 A' := hAsmall.union h𝒯 (hcentral c hc) hatt_lt_θ
  have hdom_A' : ∀ n ∈ π.domγ, π.nodeVertex n ∈ A'.vertexSet :=
    fun n hn => Or.inl (hdom n hn)
  have heq : A' = A := hmax A' hle_A' hsmall_A' hatt_A' hdom_A'
  rw [← heq]
  exact le_union_right hA_le hc_le

/-- The partial union $X_j = A \cup \alpha(c_1) \cup \dots \cup \alpha(c_j)$ along a cuff
enumeration `E` in the proof of **Graph Minors XVII, (4.3)** (page 170). -/
def cuffPrefixUnion {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) {Θ : Set π.S} {k : ℕ} (E : π.Γ.CuffEnumeration Θ k)
    (A : Hypergraph α β) (j : ℕ) : Hypergraph α β :=
  A ∪ π.cellsUnion {c | ∃ i : Fin k, i.1 < j ∧ E.cell i = c}

theorem cuffPrefixUnion_zero {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) {Θ : Set π.S} {k : ℕ} (E : π.Γ.CuffEnumeration Θ k)
    {A : Hypergraph α β} (hA : A ≤ G) :
    cuffPrefixUnion π E A 0 = A := by
  have hle : cuffPrefixUnion π E A 0 ≤ G :=
    union_le hA (π.cellsUnion_le _)
  apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle hA
  · ext v
    simp only [cuffPrefixUnion, union_vertexSet, Portrayal.cellsUnion, mem_union, mem_iUnion,
      mem_inter_iff, mem_ofPred_eq, Nat.not_lt_zero, false_and, exists_false, iUnion_false,
      mem_empty_iff_false, or_false]
  · ext e
    simp only [cuffPrefixUnion, union_edgeSet, Portrayal.cellsUnion, mem_union, mem_iUnion,
      mem_inter_iff, mem_ofPred_eq, Nat.not_lt_zero, false_and, exists_false, iUnion_false,
      mem_empty_iff_false, or_false]

theorem cuffPrefixUnion_succ {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) {Θ : Set π.S} {k : ℕ} (E : π.Γ.CuffEnumeration Θ k)
    {A : Hypergraph α β} (hA : A ≤ G) {j : ℕ} (hj : j < k) :
    cuffPrefixUnion π E A (j + 1) =
      cuffPrefixUnion π E A j ∪ π.cellGraph (E.cell ⟨j, hj⟩) := by
  have hcell_mem : E.cell ⟨j, hj⟩ ∈ π.Γ.C := by
    have h : E.cell ⟨j, hj⟩ ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} := by
      rw [← E.range_cell]; exact mem_range_self _
    exact h.1
  have h1 : cuffPrefixUnion π E A (j + 1) ≤ G :=
    union_le hA (π.cellsUnion_le _)
  have h2 : cuffPrefixUnion π E A j ∪ π.cellGraph (E.cell ⟨j, hj⟩) ≤ G :=
    union_le (union_le hA (π.cellsUnion_le _)) (π.cellGraph_le _ hcell_mem)
  apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq h1 h2
  · ext v
    simp only [cuffPrefixUnion, union_vertexSet, Portrayal.cellsUnion, mem_union, mem_iUnion,
      mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro (hvA | ⟨c, ⟨⟨i, hi, rfl⟩, hcC⟩, hvc⟩)
      · exact Or.inl (Or.inl hvA)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
        · exact Or.inl (Or.inr ⟨E.cell i, ⟨⟨i, hlt, rfl⟩, hcC⟩, hvc⟩)
        · have hi_eq : i = ⟨j, hj⟩ := Fin.ext heq
          exact Or.inr (hi_eq ▸ hvc)
    · rintro ((hvA | ⟨c, ⟨⟨i, hi, rfl⟩, hcC⟩, hvc⟩) | hvc)
      · exact Or.inl hvA
      · exact Or.inr ⟨E.cell i, ⟨⟨i, Nat.lt_succ_of_lt hi, rfl⟩, hcC⟩, hvc⟩
      · exact Or.inr ⟨E.cell ⟨j, hj⟩, ⟨⟨⟨j, hj⟩, Nat.lt_succ_self j, rfl⟩, hcell_mem⟩, hvc⟩
  · ext e
    simp only [cuffPrefixUnion, union_edgeSet, Portrayal.cellsUnion, mem_union, mem_iUnion,
      mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro (heA | ⟨c, ⟨⟨i, hi, rfl⟩, hcC⟩, hec⟩)
      · exact Or.inl (Or.inl heA)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
        · exact Or.inl (Or.inr ⟨E.cell i, ⟨⟨i, hlt, rfl⟩, hcC⟩, hec⟩)
        · have hi_eq : i = ⟨j, hj⟩ := Fin.ext heq
          exact Or.inr (hi_eq ▸ hec)
    · rintro ((heA | ⟨c, ⟨⟨i, hi, rfl⟩, hcC⟩, hec⟩) | hec)
      · exact Or.inl heA
      · exact Or.inr ⟨E.cell i, ⟨⟨i, Nat.lt_succ_of_lt hi, rfl⟩, hcC⟩, hec⟩
      · exact Or.inr ⟨E.cell ⟨j, hj⟩, ⟨⟨⟨j, hj⟩, Nat.lt_succ_self j, rfl⟩, hcell_mem⟩, hec⟩

/-- Claim (2) in the proof of **Graph Minors XVII, (4.3)** (page 170):
For $1 \le j \le k$, every attachment of $X_j$ which is not an attachment of $A$ is in
$\beta(n_1) \cup \beta(n_{j+1})$, and when $j = k$ every attachment of $X_k$ is an attachment of
$A$. In particular, if $A$ has $< \theta - 2p$ attachments and $\pi$ has warp $\le p$, then $X_j$
has fewer than $\theta$ attachments. -/
theorem theorem_4_3_claim_2 {α : Type u} {β : Type v} {G : Hypergraph α β} {θ p : ℕ}
     (π : Portrayal G) (hwarp : π.warp ≤ p)
    {Θ : Set π.S} {k : ℕ} (E : π.Γ.CuffEnumeration Θ k)
    {A : Hypergraph α β} (hatt : (attachments G A).ncard < θ - 2 * p)
    (hdom : ∀ n ∈ π.domγ, π.nodeVertex n ∈ A.vertexSet)
    (_hint : ∀ c ∈ π.Γ.C, ¬ (c ∩ bd π.S).Nonempty → π.cellGraph c ≤ A)
    {j : ℕ} (hj_pos : 1 ≤ j) (hj_le : j ≤ k) :
    have hk_pos : 0 < k := by linarith [E.two_le]
    attachments G (cuffPrefixUnion π E A j) \ attachments G A ⊆
      π.borderSet (E.node ⟨0, hk_pos⟩) ∪
      π.borderSet (E.node ⟨j % k, Nat.mod_lt _ hk_pos⟩) ∧
    (j = k → attachments G (cuffPrefixUnion π E A j) ⊆ attachments G A) ∧
    (attachments G (cuffPrefixUnion π E A j)).ncard < θ := by
  classical
  have hk_pos : 0 < k := by linarith [E.two_le]
  let r₀ : Fin k := ⟨0, hk_pos⟩
  let r_j : Fin k := ⟨j % k, Nat.mod_lt _ hk_pos⟩
  -- First prove the core property for any v ∈ attachments G (X_j) \ attachments G A
  have hcore : ∀ v ∈ attachments G (cuffPrefixUnion π E A j) \ attachments G A,
      j < k ∧ v ∈ π.borderSet (E.node r₀) ∪ π.borderSet (E.node r_j) := by
    rintro v ⟨⟨hvX, e, ⟨heG, henotX⟩, hinc⟩, hvnotAttA⟩
    have henotA : e ∉ A.edgeSet := fun heA => henotX (Or.inl heA)
    have hvnotA : v ∉ A.vertexSet := fun hvA => hvnotAttA ⟨hvA, e, ⟨heG, henotA⟩, hinc⟩
    have hvCells : v ∈ (π.cellsUnion {c | ∃ i : Fin k, i.1 < j ∧ E.cell i = c}).vertexSet :=
      hvX.resolve_left hvnotA
    simp only [Portrayal.cellsUnion, mem_iUnion, mem_inter_iff, mem_ofPred_eq] at hvCells
    rcases hvCells with ⟨_, ⟨⟨i, hi_lt, rfl⟩, hiC⟩, hvi⟩
    have hiΘ : (E.cell i ∩ Θ).Nonempty := by
      have h : E.cell i ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} := by
        rw [← E.range_cell]; exact mem_range_self i
      exact h.2
    have hibd : (E.cell i ∩ bd π.S).Nonempty := by
      rw [(π.Γ.border_cell_subset_cuff hiC E.cuff_mem hiΘ).2.1]; exact hiΘ
    obtain ⟨c, hcC, hec⟩ := π.p1_edge e heG
    have hvc : v ∈ (π.cellGraph c).vertexSet :=
      (π.cellGraph c).vertex_mem_of_inc ((inc_iff_of_le (π.cellGraph_le c hcC) hec).2 hinc)
    have hne_ic : E.cell i ≠ c := by
      rintro rfl
      apply henotX
      right
      simp only [Portrayal.cellsUnion, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
      exact ⟨E.cell i, ⟨⟨i, hi_lt, rfl⟩, hiC⟩, hec⟩
    have hvo_i : v ∈ π.otherVertices (E.cell i) := ⟨c, hcC, hne_ic.symm, hvc⟩
    obtain ⟨n_h, hn_h_tilde, hvn_h_plus⟩ := π.p6_borderPlus hiC hibd hvi hvo_i
    have hvn_h : v ∈ π.borderSet n_h := by
      rcases hvn_h_plus with h | ⟨hdom_nh, rfl⟩
      · exact h
      · exact (hvnotA (hdom n_h hdom_nh)).elim
    have hcΘ : (c ∩ Θ).Nonempty := by
      by_contra hnotΘ
      obtain ⟨_, n, hn, _, rfl⟩ :=
        π.exists_node_of_not_borders_cuff hiC hcC hne_ic E.cuff_mem hiΘ hnotΘ hn_h_tilde hvn_h hvc
      exact hvnotA (hdom n hn.2)
    have hc_range : c ∈ Set.range E.cell := by
      rw [E.range_cell]; exact ⟨hcC, hcΘ⟩
    rcases hc_range with ⟨j', rfl⟩
    have hj'_ge : j ≤ j'.1 := by
      by_contra hlt
      push Not at hlt
      apply henotX
      right
      simp only [Portrayal.cellsUnion, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
      exact ⟨E.cell j', ⟨⟨j', hlt, rfl⟩, hcC⟩, hec⟩
    have hj_lt_k : j < k := lt_of_le_of_lt hj'_ge j'.2
    refine ⟨hj_lt_k, ?_⟩
    have hj'bd : (E.cell j' ∩ bd π.S).Nonempty := by
      rw [(π.Γ.border_cell_subset_cuff hcC E.cuff_mem hcΘ).2.1]; exact hcΘ
    have hvo_j' : v ∈ π.otherVertices (E.cell j') := ⟨E.cell i, hiC, hne_ic, hvi⟩
    obtain ⟨n_h', hn_h'_tilde, hvn_h'_plus⟩ := π.p6_borderPlus hcC hj'bd hvc hvo_j'
    -- Identify the indices a, b in Fin k for n_h and n_h'
    rw [E.cell_tilde i] at hn_h_tilde
    rw [E.cell_tilde j'] at hn_h'_tilde
    let a : Fin k :=
      if n_h = E.node i then i else ⟨(i.1 + 1) % k, Nat.mod_lt _ hk_pos⟩
    have ha_eq : E.node a = n_h := by
      dsimp [a]
      split_ifs with h
      · exact h.symm
      · rcases hn_h_tilde with h1 | h2
        · exact (h h1).elim
        · exact h2.symm
    have ha_le : a.1 ≤ j := by
      dsimp [a]
      split_ifs
      · omega
      · dsimp
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
    let b : Fin k :=
      if n_h' = E.node j' then j' else ⟨(j'.1 + 1) % k, Nat.mod_lt _ hk_pos⟩
    have hb_eq : E.node b = n_h' := by
      dsimp [b]
      split_ifs with h
      · exact h.symm
      · rcases hn_h'_tilde with h1 | h2
        · exact (h h1).elim
        · exact h2.symm
    have hb_range : j ≤ b.1 ∨ b.1 = 0 := by
      dsimp [b]
      split_ifs
      · exact Or.inl hj'_ge
      · dsimp
        by_cases hsucc : j'.1 + 1 < k
        · rw [Nat.mod_eq_of_lt hsucc]
          exact Or.inl (by omega)
        · have heq : j'.1 + 1 = k := by omega
          rw [heq, Nat.mod_self]
          exact Or.inr rfl
    have hr₀_val : r₀.1 = 0 := rfl
    have hr_j_val : r_j.1 = j := Nat.mod_eq_of_lt hj_lt_k
    have hdist_ar : cyclicDist a r_j = j - a.1 := by
      rw [cyclicDist_eq_ite, hr_j_val]
      simp only [ha_le, ↓reduceIte]
    have hdist_sum : cyclicDist a r_j + cyclicDist r_j b + cyclicDist b r₀ ≤ k := by
      rcases hb_range with hb_ge | hb_zero
      · have h1 : cyclicDist r_j b = b.1 - j := by
          rw [cyclicDist_eq_ite, hr_j_val]
          simp only [hb_ge, ↓reduceIte]
        have h2 : cyclicDist b r₀ = k - b.1 := by
          rw [cyclicDist_eq_ite, hr₀_val]
          have hb_pos : 0 < b.1 := by omega
          split_ifs <;> omega
        have := b.2
        omega
      · have h1 : cyclicDist r_j b = k - j := by
          rw [cyclicDist_eq_ite, hr_j_val, hb_zero]
          split_ifs <;> omega
        have h2 : cyclicDist b r₀ = 0 := by
          have hb_r₀ : b = r₀ := Fin.ext hb_zero
          rw [hb_r₀, cyclicDist_self]
        omega
    have hva_plus : v ∈ π.borderPlus (E.node a) := ha_eq.symm ▸ hvn_h_plus
    have hvb_plus : v ∈ π.borderPlus (E.node b) := hb_eq.symm ▸ hvn_h'_plus
    have h_or := π.p7_of_cyclicDist E hdist_sum hva_plus hvb_plus
    rcases h_or with hvr_j | hvr₀
    · rcases hvr_j with h | ⟨hdom_rj, rfl⟩
      · exact Or.inr h
      · exact (hvnotA (hdom (E.node r_j) hdom_rj)).elim
    · rcases hvr₀ with h | ⟨hdom_r0, rfl⟩
      · exact Or.inl h
      · exact (hvnotA (hdom (E.node r₀) hdom_r0)).elim
  have hsub : attachments G (cuffPrefixUnion π E A j) \ attachments G A ⊆
      π.borderSet (E.node r₀) ∪ π.borderSet (E.node r_j) :=
    fun v hv => (hcore v hv).2
  have hjk : j = k → attachments G (cuffPrefixUnion π E A j) ⊆ attachments G A := by
    intro hjk v hv
    by_contra hvnot
    have hlt := (hcore v ⟨hv, hvnot⟩).1
    omega
  refine ⟨hsub, hjk, ?_⟩
  have hcov : attachments G (cuffPrefixUnion π E A j) ⊆
      attachments G A ∪ (π.borderSet (E.node r₀) ∪ π.borderSet (E.node r_j)) := by
    intro v hv
    by_cases hvA : v ∈ attachments G A
    · exact Or.inl hvA
    · exact Or.inr (hsub ⟨hv, hvA⟩)
  have hn_bd : ∀ i : Fin k, E.node i ∈ π.Γ.N ∩ bd π.S := by
    intro i
    have h : E.node i ∈ π.Γ.N ∩ Θ := by
      rw [← E.range_node]; exact mem_range_self i
    rcases E.cuff_mem with ⟨x₀, _, hΘ_eq⟩
    refine ⟨h.1, ?_⟩
    have h2 : E.node i ∈ connectedComponentIn (bd π.S) x₀ := hΘ_eq ▸ h.2
    exact connectedComponentIn_subset (bd π.S) x₀ h2
  have hcard0 : (π.borderSet (E.node r₀)).ncard ≤ p :=
    (π.ncard_borderSet_le_warp (hn_bd r₀)).trans hwarp
  have hcardj : (π.borderSet (E.node r_j)).ncard ≤ p :=
    (π.ncard_borderSet_le_warp (hn_bd r_j)).trans hwarp
  have hfin0 : (π.borderSet (E.node r₀)).Finite := π.borderSet_finite (hn_bd r₀)
  have hfinj : (π.borderSet (E.node r_j)).Finite := π.borderSet_finite (hn_bd r_j)
  have hcard_union :
      (attachments G (cuffPrefixUnion π E A j)).ncard ≤
        (attachments G A).ncard + (π.borderSet (E.node r₀)).ncard +
          (π.borderSet (E.node r_j)).ncard := by
    calc (attachments G (cuffPrefixUnion π E A j)).ncard
      _ ≤ (attachments G A ∪ (π.borderSet (E.node r₀) ∪ π.borderSet (E.node r_j))).ncard :=
        ncard_le_ncard hcov (attachments_finite.union (hfin0.union hfinj))
      _ ≤ (attachments G A).ncard +
          (π.borderSet (E.node r₀) ∪ π.borderSet (E.node r_j)).ncard :=
        ncard_union_le _ _
      _ ≤ (attachments G A).ncard +
          ((π.borderSet (E.node r₀)).ncard + (π.borderSet (E.node r_j)).ncard) :=
        Nat.add_le_add_left (ncard_union_le _ _) _
      _ = (attachments G A).ncard + (π.borderSet (E.node r₀)).ncard +
          (π.borderSet (E.node r_j)).ncard := by omega
  omega

/-- Claim (3) in the proof of **Graph Minors XVII, (4.3)** (page 170):
For $0 \le j \le k$, $X_j$ is small relative to $\mathcal{T}$. -/
theorem theorem_4_3_claim_3 {α : Type u} {β : Type v} {G : Hypergraph α β} {θ p : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G) (hcentral : π.IsCentral 𝒯) (hwarp : π.warp ≤ p)
    {Θ : Set π.S} {k : ℕ} (E : π.Γ.CuffEnumeration Θ k)
    {A : Hypergraph α β} (hAsmall : IsSmallWrt 𝒯 A)
    (hatt : (attachments G A).ncard < θ - 2 * p)
    (hdom : ∀ n ∈ π.domγ, π.nodeVertex n ∈ A.vertexSet)
    (hint : ∀ c ∈ π.Γ.C, ¬ (c ∩ bd π.S).Nonempty → π.cellGraph c ≤ A) :
    ∀ j ≤ k, IsSmallWrt 𝒯 (cuffPrefixUnion π E A j) := by
  have hA_le : A ≤ G := hAsmall.le_G h𝒯
  intro j hj
  induction j with
  | zero =>
    rw [cuffPrefixUnion_zero π E hA_le]
    exact hAsmall
  | succ j ih =>
    have hj_lt : j < k := Nat.lt_of_succ_le hj
    have hprev : IsSmallWrt 𝒯 (cuffPrefixUnion π E A j) := ih (Nat.le_of_lt hj_lt)
    have hcell_mem : E.cell ⟨j, hj_lt⟩ ∈ π.Γ.C := by
      have h : E.cell ⟨j, hj_lt⟩ ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} := by
        rw [← E.range_cell]; exact mem_range_self _
      exact h.1
    have hcell_small : IsSmallWrt 𝒯 (π.cellGraph (E.cell ⟨j, hj_lt⟩)) :=
      hcentral _ hcell_mem
    have hatt_succ : (attachments G (cuffPrefixUnion π E A (j + 1))).ncard < θ :=
      (theorem_4_3_claim_2 π hwarp E hatt hdom hint (Nat.succ_pos j) hj).2.2
    rw [cuffPrefixUnion_succ π E hA_le hj_lt] at hatt_succ ⊢
    exact hprev.union h𝒯 hcell_small hatt_succ

/-- **Graph Minors XVII, (4.3)** (pages 169–170):
Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a $\mathcal{T}$-central portrayal of a
hypergraph $G$, with $\operatorname{warp} \le p$, and let $\mathcal{T}$ have order $\theta$.
There is no small subhypergraph $A \subseteq G$ with $< \theta - 2p$ attachments, such that
$\gamma(n) \in V(A)$ for all $n \in \operatorname{dom}(\gamma)$. -/
theorem theorem_4_3_proof {α : Type u} {β : Type v} {G : Hypergraph α β} {θ p : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G) (hcentral : π.IsCentral 𝒯) (hwarp : π.warp ≤ p) :
    ¬ ∃ A : Hypergraph α β,
      IsSmallWrt 𝒯 A ∧
      (attachments G A).ncard < θ - 2 * p ∧
      (∀ n ∈ π.domγ, π.nodeVertex n ∈ A.vertexSet) := by
  rintro ⟨A₀, hA₀_small, hA₀_att, hA₀_dom⟩
  let P : Hypergraph α β → Prop := fun A =>
    IsSmallWrt 𝒯 A ∧
    (attachments G A).ncard < θ - 2 * p ∧
    (∀ n ∈ π.domγ, π.nodeVertex n ∈ A.vertexSet)
  let μ : Hypergraph α β → ℕ := fun A =>
    (G.vertexSet.ncard + G.edgeSet.ncard) - (A.vertexSet.ncard + A.edgeSet.ncard)
  -- By well-foundedness of < on ℕ, choose A ∈ P minimizing μ A (hence maximal under ≤)
  have hP_nonempty : {A | P A}.Nonempty := ⟨A₀, hA₀_small, hA₀_att, hA₀_dom⟩
  let A := WellFounded.min ( InvImage.wf μ wellFounded_lt ) {A | P A} hP_nonempty
  have hPA : P A := WellFounded.min_mem (InvImage.wf μ wellFounded_lt) {A | P A} hP_nonempty
  rcases hPA with ⟨hAsmall, hatt, hdom⟩
  have hA_le : A ≤ G := hAsmall.le_G h𝒯
  have hmax : ∀ A' : Hypergraph α β, A ≤ A' → IsSmallWrt 𝒯 A' →
      (attachments G A').ncard < θ - 2 * p →
      (∀ n ∈ π.domγ, π.nodeVertex n ∈ A'.vertexSet) → A' = A := by
    intro A' hle hA'small hA'att hA'dom
    have hPA' : A' ∈ {B | P B} := ⟨hA'small, hA'att, hA'dom⟩
    have hnot_lt : ¬ μ A' < μ A :=
      WellFounded.not_lt_min (InvImage.wf μ wellFounded_lt) {B | P B} hPA'
    have hA'_le : A' ≤ G := hA'small.le_G h𝒯
    have hV_A' : A'.vertexSet.ncard ≤ G.vertexSet.ncard :=
      ncard_le_ncard hA'_le.vertexSet_subset G.vertexSet_finite
    have hE_A' : A'.edgeSet.ncard ≤ G.edgeSet.ncard :=
      ncard_le_ncard hA'_le.edgeSet_subset G.edgeSet_finite
    have hV_le : A.vertexSet.ncard ≤ A'.vertexSet.ncard :=
      ncard_le_ncard hle.vertexSet_subset A'.vertexSet_finite
    have hE_le : A.edgeSet.ncard ≤ A'.edgeSet.ncard :=
      ncard_le_ncard hle.edgeSet_subset A'.edgeSet_finite
    dsimp [μ] at hnot_lt
    exact (eq_of_le_of_ncard_eq hle (by omega) (by omega)).symm
  -- Claim (1): every internal cell c satisfies π.cellGraph c ≤ A
  have hint : ∀ c ∈ π.Γ.C, ¬ (c ∩ bd π.S).Nonempty → π.cellGraph c ≤ A :=
    fun c hc hnot_bd => theorem_4_3_claim_1 h𝒯 π hcentral hAsmall hatt hdom hmax hc hnot_bd
  -- Since A ≠ G, some cell c₁ ∈ π.Γ.C has ¬ (π.cellGraph c₁ ≤ A)
  have hex_c₁ : ∃ c₁ ∈ π.Γ.C, ¬ (π.cellGraph c₁ ≤ A) := by
    by_contra hall
    push Not at hall
    apply hAsmall.ne_G h𝒯
    apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq hA_le le_rfl
    · refine Subset.antisymm hA_le.vertexSet_subset ?_
      intro v hv
      obtain ⟨c, hc, hvc⟩ := π.p1_vertex v hv
      exact (hall c hc).vertexSet_subset hvc
    · refine Subset.antisymm hA_le.edgeSet_subset ?_
      intro e he
      obtain ⟨c, hc, hec⟩ := π.p1_edge e he
      exact (hall c hc).edgeSet_subset hec
  rcases hex_c₁ with ⟨c₁, hc₁, hnot_le_c₁⟩
  -- By Claim (1), c₁ is a border cell, so it borders some cuff Θ
  have hbd_c₁ : (c₁ ∩ bd π.S).Nonempty := by
    by_contra hnot_bd
    exact hnot_le_c₁ (hint c₁ hc₁ hnot_bd)
  rcases hbd_c₁ with ⟨x₀, hxc₁, hxbd⟩
  let Θ := connectedComponentIn (bd π.S) x₀
  have hΘ : Θ ∈ cuffs π.S := ⟨x₀, hxbd, rfl⟩
  have hΘ_arc : IsOArc Θ := (GraphMinor.Surface.cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
  have hc₁Θ : (c₁ ∩ Θ).Nonempty := ⟨x₀, hxc₁, mem_connectedComponentIn hxbd⟩
  obtain ⟨E⟩ := π.Γ.exists_cuffEnumeration hΘ hΘ_arc
  set k := (π.Γ.N ∩ Θ).ncard
  have hk_pos : 1 ≤ k := by linarith [E.two_le]
  -- By Claims (2) and (3) for j = k, X_k is small and has attachments ⊆ attachments G A
  have hXk_small : IsSmallWrt 𝒯 (cuffPrefixUnion π E A k) :=
    theorem_4_3_claim_3 h𝒯 π hcentral hwarp E hAsmall hatt hdom hint k le_rfl
  have hXk_att_sub : attachments G (cuffPrefixUnion π E A k) ⊆ attachments G A :=
    (theorem_4_3_claim_2 π hwarp E hatt hdom hint hk_pos le_rfl).2.1 rfl
  have hXk_att : (attachments G (cuffPrefixUnion π E A k)).ncard < θ - 2 * p :=
    (ncard_le_ncard hXk_att_sub attachments_finite).trans_lt hatt
  have hXk_dom : ∀ n ∈ π.domγ, π.nodeVertex n ∈ (cuffPrefixUnion π E A k).vertexSet :=
    fun n hn => Or.inl (hdom n hn)
  have hA_le_Xk : A ≤ cuffPrefixUnion π E A k :=
    le_union_left hA_le (π.cellsUnion_le _)
  have hXk_eq_A : cuffPrefixUnion π E A k = A :=
    hmax (cuffPrefixUnion π E A k) hA_le_Xk hXk_small hXk_att hXk_dom
  -- Yet c₁ = E.cell i for some i : Fin k, so π.cellGraph c₁ ≤ X_k = A, contradiction!
  have hc₁_range : c₁ ∈ Set.range E.cell := by
    rw [E.range_cell]; exact ⟨hc₁, hc₁Θ⟩
  rcases hc₁_range with ⟨i, rfl⟩
  have hi_le_Xk : π.cellGraph (E.cell i) ≤ cuffPrefixUnion π E A k :=
    (π.cellGraph_le_cellsUnion (I := {c | ∃ j : Fin k, j.1 < k ∧ E.cell j = c})
      ⟨i, i.2, rfl⟩ hc₁).trans (le_union_right hA_le (π.cellsUnion_le _))
  rw [hXk_eq_A] at hi_le_Xk
  exact hnot_le_c₁ hi_le_Xk

end GraphMinor.GM17
