/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section5

import LeanPool.GraphMinor.Surface.Cuffs

/-!
# Section 6 of Graph Minors XVII: Redundancy

This file formalizes Section 6 (pages 173–178) of N. Robertson and P. D. Seymour,
*Graph Minors. XVII. Taming a vortex*, J. Combin. Theory Ser. B 77 (1999) 162–210:
- **Graph Minors XVII, (6.1)** (`theorem_6_1`, page 174): smallness of $A$ relative to
  $\mathcal{T}$ is equivalent to smallness of $A / (Z \cap V(A))$ relative to $\mathcal{T} / Z$
  when $A / (Z \cap V(A))$ has fewer than $\theta - |Z|$ attachments in $G / Z$.
- **Graph Minors XVII, (6.2)** (`theorem_6_2`, page 174): the quotient portrayal
  $\pi' = \pi.\text{quotientBy } Z$ is a $(\mathcal{T} / Z)$-central portrayal of $G / Z$,
  resembling or simpler than $\pi$.
- **Graph Minors XVII, (6.3)** (`theorem_6_3`, page 174): a $\Gamma$-normal $I$-arc $F$ with
  $|F \cap \operatorname{dom}(\gamma)| \le z - 2p$ cuts off a disc $\Delta$ with $\alpha(\Delta)$
  small.
- **Graph Minors XVII, (6.4)** (`theorem_6_4`, page 175): a $\Gamma$-normal $O$-arc $F$ with
  $|F \cap \operatorname{dom}(\gamma)| \le z$ bounds a disc $\Delta$ with $\alpha(\Delta)$ small.
- **Graph Minors XVII, (6.5)** (`theorem_6_5`, page 175): behavior of a separation $(A, B) \in
  \mathcal{T}$
  of order $\le z$ on a cuff $\Theta$ where $\pi$ has warp $p$.
- **Graph Minors XVII, (6.6)** (`theorem_6_6`, page 176), with its subproof claims (1), (2), and
  (3):
  no vertex set $X \subseteq V(G)$ of size $\le z / 3$ meets $\beta(n+)$ for every node $n$
  bordering a cuff $\Theta$.
- **Graph Minors XVII, (6.7)** (`theorem_6_7`, page 177): for a $\Gamma$-normal $I$-arc $F$ with
  ends $n_1, n_2$ and $|F \cap \operatorname{dom}(\gamma)| \le z - 2p - 1$, the disc $\Delta$ of
  (6.3) satisfies $\beta(n_1 +) \cap \beta(n_2 +) \subseteq \beta(n+)$ for all
  $n \in N(\Gamma) \cap \Delta \cap \operatorname{bd}(\Sigma)$.
The portrayal deductions that use painting results are proved in `Section6Proved`.
-/

public section

namespace GraphMinor.GM17

open Set Function Topology
open GraphMinor.Surface
open GraphMinor.GM10
open GraphMinor.Hypergraph

universe u v

/-! ## 1. Quotient Hypergraphs and Graph Minors XVII, (6.1) (Page 174) -/

/-- For any hypergraph $A$ and vertex set $Z$, $A / (Z \cap V(A)) = A / Z$. -/
@[simp]
theorem quotientVertices_inter_vertexSet {α : Type u} {β : Type v}
    (A : Hypergraph α β) (Z : Set α) :
    quotientVertices A (Z ∩ A.vertexSet) = quotientVertices A Z := by
  have hle₁ : quotientVertices A (Z ∩ A.vertexSet) ≤ quotientVertices A Z := by
    refine ⟨fun v hv => ⟨hv.1, fun hz => hv.2 ⟨hz, hv.1⟩⟩, Subset.rfl, fun e _ => ?_⟩
    ext v
    change (A.Inc e v ∧ v ∉ Z) ↔ (A.Inc e v ∧ v ∉ Z ∩ A.vertexSet)
    exact ⟨fun ⟨hinc, hv⟩ => ⟨hinc, fun ⟨hz, _⟩ => hv hz⟩,
      fun ⟨hinc, hv⟩ => ⟨hinc, fun hz => hv ⟨hz, A.vertex_mem_of_inc hinc⟩⟩⟩
  refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle₁ le_rfl ?_ rfl
  ext v
  change v ∈ A.vertexSet \ (Z ∩ A.vertexSet) ↔ v ∈ A.vertexSet \ Z
  simp only [mem_sdiff, mem_inter_iff]
  tauto

@[simp]
theorem quotientVertices_empty {α : Type u} {β : Type v} (A : Hypergraph α β) :
    quotientVertices A ∅ = A := by
  have hle : quotientVertices A ∅ ≤ A := by
    refine ⟨sdiff_subset, Subset.rfl, fun e _ => ?_⟩
    ext v
    change A.Inc e v ↔ (A.Inc e v ∧ v ∉ (∅ : Set α))
    simp
  exact eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle le_rfl sdiff_empty rfl

theorem quotientVertices_mono {α : Type u} {β : Type v} {G A : Hypergraph α β}
    (hA : A ≤ G) (Z : Set α) :
    quotientVertices A Z ≤ quotientVertices G Z where
  vertexSet_subset := sdiff_subset_sdiff hA.vertexSet_subset Subset.rfl
  edgeSet_subset := hA.edgeSet_subset
  ends_eq e he := by
    ext v
    change ((G.Inc e v ∧ v ∉ Z) ↔ (A.Inc e v ∧ v ∉ Z))
    rw [inc_iff_of_le hA he]

/-- The attachments of $A / Z$ in $G / Z$ are exactly the attachments of $A$ in $G$ outside $Z$. -/
@[simp]
theorem attachments_quotientVertices {α : Type u} {β : Type v}
    (G A : Hypergraph α β) (Z : Set α) :
    attachments (quotientVertices G Z) (quotientVertices A Z) = attachments G A \ Z := by
  ext v
  simp only [attachments, quotientVertices, mem_ofPred_eq, mem_sdiff]
  tauto

/-- The complementary subhypergraph of $A / Z$ in $G / Z$ is $(G \setminus A) / Z$. -/
theorem complSubhypergraph_quotientVertices {α : Type u} {β : Type v}
    {G A : Hypergraph α β} (hA : A ≤ G) (Z : Set α) :
    complSubhypergraph (quotientVertices G Z) (quotientVertices A Z) =
      quotientVertices (complSubhypergraph G A) Z := by
  have h1 : complSubhypergraph (quotientVertices G Z) (quotientVertices A Z) ≤
      quotientVertices G Z :=
    complSubhypergraph_le (quotientVertices_mono hA Z)
  have h2 : quotientVertices (complSubhypergraph G A) Z ≤ quotientVertices G Z :=
    quotientVertices_mono (complSubhypergraph_le hA) Z
  apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq h1 h2
  · rw [complSubhypergraph_vertexSet, attachments_quotientVertices]
    ext v
    change v ∈ ((G.vertexSet \ Z) \ (A.vertexSet \ Z)) ∪ (attachments G A \ Z) ↔
      v ∈ ((G.vertexSet \ A.vertexSet) ∪ attachments G A) \ Z
    simp only [mem_union, mem_sdiff]
    tauto
  · rfl

/-- Adding a subset $W \subseteq V(G)$ of isolated vertices to a subhypergraph $A \le G$ gives the
subhypergraph $C \le G$ with $V(C) = V(A) \cup W$ and $E(C) = E(A)$. -/
@[expose]
def addVertices {α : Type u} {β : Type v} (G A : Hypergraph α β) (W : Set α)
    (hW : W ⊆ G.vertexSet) : Hypergraph α β where
  vertexSet := A.vertexSet ∪ W
  edgeSet := A.edgeSet
  Inc := A.Inc
  vertex_mem_of_inc _ _ h := Or.inl (A.vertex_mem_of_inc h)
  edge_mem_of_inc := A.edge_mem_of_inc
  vertexSet_finite := A.vertexSet_finite.union (G.vertexSet_finite.subset hW)
  edgeSet_finite := A.edgeSet_finite

@[simp]
theorem addVertices_vertexSet {α : Type u} {β : Type v} (G A : Hypergraph α β) (W : Set α)
    (hW : W ⊆ G.vertexSet) :
    (addVertices G A W hW).vertexSet = A.vertexSet ∪ W :=
  rfl

@[simp]
theorem addVertices_edgeSet {α : Type u} {β : Type v} (G A : Hypergraph α β) (W : Set α)
    (hW : W ⊆ G.vertexSet) :
    (addVertices G A W hW).edgeSet = A.edgeSet :=
  rfl

theorem le_addVertices {α : Type u} {β : Type v} {G A : Hypergraph α β} {W : Set α}
    (hW : W ⊆ G.vertexSet) :
    A ≤ addVertices G A W hW where
  vertexSet_subset := subset_union_left
  edgeSet_subset := Subset.rfl
  ends_eq _ _ := rfl

theorem addVertices_le {α : Type u} {β : Type v} {G A : Hypergraph α β} {W : Set α}
    (hA : A ≤ G) (hW : W ⊆ G.vertexSet) :
    addVertices G A W hW ≤ G where
  vertexSet_subset := union_subset hA.vertexSet_subset hW
  edgeSet_subset := hA.edgeSet_subset
  ends_eq := hA.ends_eq

theorem quotientVertices_addVertices {α : Type u} {β : Type v} {G A : Hypergraph α β} {W : Set α}
    (hA : A ≤ G) (hW : W ⊆ G.vertexSet) :
    quotientVertices (addVertices G A W hW) W = quotientVertices A W := by
  have h1 : quotientVertices (addVertices G A W hW) W ≤ quotientVertices G W :=
    quotientVertices_mono (addVertices_le hA hW) W
  have h2 : quotientVertices A W ≤ quotientVertices G W :=
    quotientVertices_mono hA W
  apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq h1 h2
  · ext v
    change v ∈ (A.vertexSet ∪ W) \ W ↔ v ∈ A.vertexSet \ W
    simp only [mem_sdiff, mem_union]
    tauto
  · rfl

/-- **Graph Minors XVII, (6.1)** (page 174):
"Let $\mathscr{T}$ be a tangle of order $\theta$ in a hypergraph $G$, and let $Z \subseteq
V(G)$ with $|Z| < \theta$. Let $A \subseteq G$ such that $A/Z'$ has fewer than $\theta -
|Z|$ attachments in $G/Z$, where $Z' = Z \cap V(A)$. Then $A$ is small relative to
$\mathscr{T}$ if and only if $A/Z'$ is small relative to $\mathscr{T}/Z$." -/
theorem theorem_6_1_proof {α : Type u} {β : Type v} {G A : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {Z : Set α} (hZ : Z ⊆ G.vertexSet) (hZ_lt : Z.ncard < θ)
    (hA : A ≤ G)
    (hatt : (attachments (quotientVertices G Z)
      (quotientVertices A (Z ∩ A.vertexSet))).ncard < θ - Z.ncard) :
    IsSmallWrt 𝒯 A ↔
      IsSmallWrt (quotientTangle G 𝒯 Z) (quotientVertices A (Z ∩ A.vertexSet)) := by
  rw [quotientVertices_inter_vertexSet] at hatt ⊢
  let A' := quotientVertices A Z
  have hA'_le : A' ≤ quotientVertices G Z := quotientVertices_mono hA Z
  let B₀ := complSubhypergraph G A
  have hsep₀ : G.IsSeparation A B₀ := isSeparation_complSubhypergraph hA
  let D' := complSubhypergraph (quotientVertices G Z) A'
  have hsep' : (quotientVertices G Z).IsSeparation A' D' :=
    isSeparation_complSubhypergraph hA'_le
  -- Following the paper's proof, let C have V(C) = V(A) ∪ Z and E(C) = E(A), and let D have
  -- V(D) = V(B₀) ∪ Z and E(D) = E(B₀), so Z ⊆ V(C ∩ D), C / Z = A', D / Z = D', and (C, D) is a
  -- separation of G of order < θ.
  let C := addVertices G A Z hZ
  let D := addVertices G B₀ Z hZ
  have hC_le : C ≤ G := addVertices_le hA hZ
  have hD_le : D ≤ G := addVertices_le hsep₀.right_le hZ
  have hCZ : quotientVertices C Z = A' := quotientVertices_addVertices hA hZ
  have hDZ : quotientVertices D Z = D' := by
    rw [quotientVertices_addVertices hsep₀.right_le hZ]
    exact (complSubhypergraph_quotientVertices hA Z).symm
  have hZ_CD : Z ⊆ (C ∩ D).vertexSet :=
    subset_inter subset_union_right subset_union_right
  have hsepCD : G.IsSeparation C D := by
    rw [isSeparation_iff_of_le hC_le hD_le]
    refine ⟨?_, hsep₀.edgeSet_union, hsep₀.edgeSet_inter_eq⟩
    ext v
    simp only [C, D, addVertices_vertexSet, mem_union]
    constructor
    · rintro ((hvA | hvZ) | (hvB | hvZ))
      · exact hA.vertexSet_subset hvA
      · exact hZ hvZ
      · exact hsep₀.right_le.vertexSet_subset hvB
      · exact hZ hvZ
    · intro hvG
      rw [← hsep₀.vertexSet_union] at hvG
      rcases hvG with hvA | hvB
      · exact Or.inl (Or.inl hvA)
      · exact Or.inr (Or.inl hvB)
  have hsepAD : G.IsSeparation A D := by
    rw [isSeparation_iff_of_le hA hD_le]
    refine ⟨?_, hsep₀.edgeSet_union, hsep₀.edgeSet_inter_eq⟩
    ext v
    simp only [D, addVertices_vertexSet, mem_union]
    constructor
    · rintro (hvA | (hvB | hvZ))
      · exact hA.vertexSet_subset hvA
      · exact hsep₀.right_le.vertexSet_subset hvB
      · exact hZ hvZ
    · intro hvG
      rw [← hsep₀.vertexSet_union] at hvG
      rcases hvG with hvA | hvB
      · exact Or.inl hvA
      · exact Or.inr (Or.inl hvB)
  have hordCD : separationOrder C D < θ := by
    have hinter : (C ∩ D).vertexSet = (attachments G A \ Z) ∪ Z := by
      ext v
      simp only [inter_vertexSet, C, D, B₀, addVertices_vertexSet, complSubhypergraph_vertexSet,
        mem_inter_iff, mem_union, mem_sdiff]
      constructor
      · rintro ⟨hvA | hvZ, (⟨_, hvnotA⟩ | hvAtt) | hvZ⟩
        · exact (hvnotA hvA).elim
        · by_cases hz : v ∈ Z
          · exact Or.inr hz
          · exact Or.inl ⟨hvAtt, hz⟩
        · exact Or.inr hvZ
        · exact Or.inr hvZ
        · exact Or.inr hvZ
        · exact Or.inr hvZ
      · rintro (⟨hvAtt, _⟩ | hvZ)
        · exact ⟨Or.inl hvAtt.1, Or.inl (Or.inr hvAtt)⟩
        · exact ⟨Or.inr hvZ, Or.inr hvZ⟩
    have hdisj : Disjoint (attachments G A \ Z) Z := disjoint_sdiff_self_left
    have hcard : separationOrder C D = (attachments G A \ Z).ncard + Z.ncard := by
      rw [separationOrder, hinter,
        ncard_union_eq hdisj (attachments_finite.sdiff) (G.vertexSet_finite.subset hZ)]
    rw [attachments_quotientVertices] at hatt
    omega
  have hordAD : separationOrder A D < θ := by
    have hsub : (A ∩ D).vertexSet ⊆ (C ∩ D).vertexSet :=
      inter_subset_inter_left _ subset_union_left
    exact (ncard_le_ncard hsub (C ∩ D).vertexSet_finite).trans_lt hordCD
  have hTangleQ : IsTangle (quotientVertices G Z) (θ - Z.ncard) (quotientTangle G 𝒯 Z) :=
    theorem_4_2_proof h𝒯 hZ hZ_lt
  -- Now follow the two cases of the paper's proof: (C, D) ∈ 𝒯 or (C, D) ∉ 𝒯.
  rcases h𝒯.axiom1 hsepCD hordCD with hCD | hDC
  · have hA_small : IsSmallWrt 𝒯 A := by
      rcases h𝒯.axiom1 hsepAD hordAD with hAD | hDA
      · exact ⟨D, hAD⟩
      · exfalso
        apply h𝒯.axiom2 hCD hDA hDA
        have hU_le : C ∪ D ∪ D ≤ G := union_le (union_le hC_le hD_le) hD_le
        apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq hU_le le_rfl
        · rw [union_vertexSet, union_vertexSet, Set.union_assoc, Set.union_self,
            hsepCD.vertexSet_union]
        · rw [union_edgeSet, union_edgeSet, Set.union_assoc, Set.union_self, hsepCD.edgeSet_union]
    have hA'_small : IsSmallWrt (quotientTangle G 𝒯 Z) A' :=
      ⟨D', hsep', ⟨(C, D), hCD, hZ_CD, hCZ, hDZ⟩⟩
    exact ⟨fun _ => hA'_small, fun _ => hA_small⟩
  · have hA_not_small : ¬ IsSmallWrt 𝒯 A := by
      rintro ⟨B₁, hAB₁⟩
      have hA₁_le := (h𝒯.isSeparation hAB₁).left_le
      apply h𝒯.axiom2 hDC hAB₁ hAB₁
      have hU_le : D ∪ A ∪ A ≤ G := union_le (union_le hD_le hA₁_le) hA₁_le
      apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq hU_le le_rfl
      · rw [union_vertexSet, union_vertexSet, Set.union_assoc, Set.union_self, Set.union_comm,
          hsepAD.vertexSet_union]
      · rw [union_edgeSet, union_edgeSet, Set.union_assoc, Set.union_self, Set.union_comm,
          hsepAD.edgeSet_union]
    have hD'A'_mem : (D', A') ∈ quotientTangle G 𝒯 Z := by
      refine ⟨hsep'.symm, ⟨(D, C), hDC, ?_, hDZ, hCZ⟩⟩
      rw [GM10.inter_comm]
      exact hZ_CD
    have hA'_not_small : ¬ IsSmallWrt (quotientTangle G 𝒯 Z) A' := by
      rintro ⟨B₁', hA'B₁'⟩
      have hA₁'_le := (hTangleQ.isSeparation hA'B₁').left_le
      apply hTangleQ.axiom2 hD'A'_mem hA'B₁' hA'B₁'
      have hU_le : D' ∪ A' ∪ A' ≤ quotientVertices G Z :=
        union_le (union_le hsep'.right_le hA₁'_le) hA₁'_le
      apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq hU_le le_rfl
      · rw [union_vertexSet, union_vertexSet, Set.union_assoc, Set.union_self, Set.union_comm,
          hsep'.vertexSet_union]
      · rw [union_edgeSet, union_edgeSet, Set.union_assoc, Set.union_self, Set.union_comm,
          hsep'.edgeSet_union]
    exact ⟨fun h => (hA_not_small h).elim, fun h => (hA'_not_small h).elim⟩

/-! ## 2. Quotient Portrayal and Graph Minors XVII, (6.2)–(6.4) (Pages 174–175) -/

/-- If a portrayal $\pi'$ on a surface homeomorphic to $\pi.S$ has warp at each cuff at most that
of $\pi$, then $\pi'$ either resembles or is simpler than $\pi$. -/
theorem Portrayal.resembles_or_isSimpler_of_warpAt_le
    {α α' β β' : Type*} {G : Hypergraph α β} {G' : Hypergraph α' β'}
    {π : Portrayal G} {π' : Portrayal G'}
    (ψ : π'.S ≃ₜ π.S)
    (hle : ∀ Θ ∈ cuffs π'.S, π'.warpAt Θ ≤ π.warpAt (ψ '' Θ)) :
    π'.Resembles π ∨ π'.IsSimpler π := by
  by_cases hex : ∃ Θ ∈ cuffs π'.S, π'.warpAt Θ < π.warpAt (ψ '' Θ)
  · exact Or.inr (Or.inr ⟨ψ, hle, hex⟩)
  · refine Or.inl ⟨ψ, fun Θ hΘ => le_antisymm (hle Θ hΘ) ?_⟩
    by_contra hlt
    exact hex ⟨Θ, hΘ, Nat.lt_of_not_le hlt⟩

theorem Portrayal.warpAt_eq_of_warpAt_le_of_not_isSimpler
    {α : Type u} {β : Type v} {G G' : Hypergraph α β}
    {π : Portrayal G} {π' : Portrayal G'}
    (ψ : π'.S ≃ₜ π.S)
    (hle : ∀ Θ ∈ cuffs π'.S, π'.warpAt Θ ≤ π.warpAt (ψ '' Θ))
    (hnot : ¬ π'.IsSimpler π) :
    ∀ Θ ∈ cuffs π'.S, π'.warpAt Θ = π.warpAt (ψ '' Θ) := by
  intro Θ hΘ
  refine le_antisymm (hle Θ hΘ) ?_
  by_contra hlt
  exact hnot (Or.inr ⟨ψ, hle, Θ, hΘ, Nat.lt_of_not_le hlt⟩)

/-- Any walk in $(H / W)^*$ is a walk in $H^*$ with the same support. -/
theorem walk_skeleton_of_quotientVertices {α : Type u} {β : Type v}
    {H : Hypergraph α β} {W : Set α} {u w : α}
    (P : (quotientVertices H W).skeleton.Walk u w) :
    ∃ P' : H.skeleton.Walk u w, P'.support = P.support := by
  induction P with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons u v w hadj P_tail ih =>
    rcases hadj with ⟨huv, e, ⟨heu, _⟩, ⟨hev, _⟩⟩
    have hadj' : H.skeleton.Adj u v := ⟨huv, e, heu, hev⟩
    obtain ⟨P'_tail, hsupp⟩ := ih
    exact ⟨SimpleGraph.Walk.cons hadj' P'_tail, by
      dsimp [SimpleGraph.Walk.support]
      rw [hsupp]⟩

@[simp]
theorem Portrayal.quotientBy_borderPlus {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (Z : Set α) (n : π.S) :
    (π.quotientBy Z).borderPlus n = π.borderPlus n \ Z := by
  ext v
  simp only [Portrayal.borderPlus, Portrayal.quotientBy, mem_sdiff, mem_ofPred_eq]
  constructor
  · rintro (⟨h, hz⟩ | ⟨⟨h, hz⟩, rfl⟩)
    · exact ⟨Or.inl h, hz⟩
    · exact ⟨Or.inr ⟨h, rfl⟩, hz⟩
  · rintro ⟨h | ⟨h, rfl⟩, hz⟩
    · exact Or.inl ⟨h, hz⟩
    · exact Or.inr ⟨⟨h, hz⟩, rfl⟩

theorem Portrayal.quotientBy_cellsUnion {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (Z : Set α) (I : Set (Set π.S)) :
    (π.quotientBy Z).cellsUnion I =
      quotientVertices (π.cellsUnion I) (Z ∩ (π.cellsUnion I).vertexSet) := by
  rw [quotientVertices_inter_vertexSet]
  apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq
    ((π.quotientBy Z).cellsUnion_le I) (quotientVertices_mono (π.cellsUnion_le I) Z)
  · ext v
    simp only [Portrayal.cellsUnion, Portrayal.quotientBy, quotientVertices, mem_iUnion,
      mem_inter_iff, mem_sdiff]
    constructor
    · rintro ⟨c, hc, hvc, hvnot⟩
      exact ⟨⟨c, hc, hvc⟩, fun hz => hvnot ⟨hz, hvc⟩⟩
    · rintro ⟨⟨c, hc, hvc⟩, hvZ⟩
      exact ⟨c, hc, hvc, fun ⟨hz, _⟩ => hvZ hz⟩
  · rfl

theorem Portrayal.quotientBy_areaGraph {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (Z : Set α) (Δ : Set π.S) :
    (π.quotientBy Z).areaGraph Δ =
      quotientVertices (π.areaGraph Δ) (Z ∩ (π.areaGraph Δ).vertexSet) :=
  π.quotientBy_cellsUnion Z {c ∈ π.Γ.C | c ⊆ Δ}

/-- A walk lift preserving support transports the warp condition to smaller border sets. -/
theorem Portrayal.cellWarp_pair_of_walk_lift {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) {c : Set π.S} (hc : c ∈ π.Γ.C) (hbd : (c ∩ bd π.S).Nonempty)
    {n₁ n₂ : π.S} (hn₁ : n₁ ∈ tilde c) (hn₂ : n₂ ∈ tilde c) (hne : n₁ ≠ n₂)
    {K : SimpleGraph α} {B₁ B₂ U₁ U₂ : Set α}
    (hB₁ : B₁ ⊆ π.borderSet n₁) (hB₂ : B₂ ⊆ π.borderSet n₂)
    (hU₁ : U₁ ⊆ π.borderPlus n₁) (hU₂ : U₂ ⊆ π.borderPlus n₂)
    (hlift : ∀ {a b : α}, a ∈ U₁ → (W : K.Walk a b) →
      ∃ W' : (π.cellGraph c).skeleton.Walk a b, W'.support = W.support) :
    B₁.ncard ≤ π.cellWarp c ∧ B₂.ncard ≤ π.cellWarp c ∧
      (U₁.ncard = π.cellWarp c + 1 → U₂.ncard = π.cellWarp c + 1 →
        Portrayal.LinkagePairs K U₁ U₂ (π.cellWarp c + 1) (π.nodeVertex n₁) (π.nodeVertex n₂)) := by
  obtain ⟨u, v, _, htilde, _, _, hu, hv⟩ := π.Γ.border_cell_exists_ends hc hbd
  have hn₁' : n₁ ∈ ({u, v} : Set π.S) := htilde ▸ hn₁
  have hn₂' : n₂ ∈ ({u, v} : Set π.S) := htilde ▸ hn₂
  have hn₁_mem : n₁ ∈ π.Γ.N ∩ bd π.S := by
    rcases hn₁' with rfl | rfl <;> assumption
  have hn₂_mem : n₂ ∈ π.Γ.N ∩ bd π.S := by
    rcases hn₂' with rfl | rfl <;> assumption
  have hspec := π.cellWarp_spec hc hbd n₁ hn₁ n₂ hn₂ hne
  refine ⟨(ncard_le_ncard hB₁ (π.borderSet_finite hn₁_mem)).trans hspec.1,
    (ncard_le_ncard hB₂ (π.borderSet_finite hn₂_mem)).trans hspec.2.1,
    fun hcard₁ hcard₂ P hP_disj => ?_⟩
  have hcard₁' : (π.borderPlus n₁).ncard = π.cellWarp c + 1 := by
    have hle := (π.ncard_borderPlus_le hn₁_mem).trans (Nat.add_le_add_right hspec.1 1)
    have hge := ncard_le_ncard hU₁ (π.borderPlus_finite hn₁_mem)
    omega
  have hcard₂' : (π.borderPlus n₂).ncard = π.cellWarp c + 1 := by
    have hle := (π.ncard_borderPlus_le hn₂_mem).trans (Nat.add_le_add_right hspec.2.1 1)
    have hge := ncard_le_ncard hU₂ (π.borderPlus_finite hn₂_mem)
    omega
  choose W hW using fun i => hlift (P i).first_mem (P i).walk
  let Q (i : Fin (π.cellWarp c + 1)) :
      PathFromTo (π.cellGraph c).skeleton (π.borderPlus n₁) (π.borderPlus n₂) :=
    ⟨(P i).first, (P i).last, W i,
      (by rw [SimpleGraph.Walk.isPath_def, hW i]; exact (P i).isPath.support_nodup),
      hU₁ (P i).first_mem, hU₂ (P i).last_mem⟩
  have hQ_disj : Pairwise fun i j =>
      Disjoint {z | z ∈ (Q i).walk.support} {z | z ∈ (Q j).walk.support} := by
    intro i j hij
    change Disjoint {z | z ∈ (W i).support} {z | z ∈ (W j).support}
    rw [hW i, hW j]
    exact hP_disj hij
  obtain ⟨i, hfirst, hlast⟩ := hspec.2.2 hcard₁' hcard₂' Q hQ_disj
  exact ⟨i, hfirst, hlast⟩

theorem Portrayal.quotientBy_cellWarp_le {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (Z : Set α)
    {c : Set π.S} (hc : c ∈ π.Γ.C) (hbd : (c ∩ bd π.S).Nonempty) :
    (π.quotientBy Z).cellWarp c ≤ π.cellWarp c := by
  apply Nat.sInf_le
  intro n₁ hn₁ n₂ hn₂ hne
  refine π.cellWarp_pair_of_walk_lift hc hbd hn₁ hn₂ hne sdiff_subset sdiff_subset ?_ ?_ ?_
  · rw [π.quotientBy_borderPlus Z n₁]
    exact sdiff_subset
  · rw [π.quotientBy_borderPlus Z n₂]
    exact sdiff_subset
  · intro _ _ _ W
    exact walk_skeleton_of_quotientVertices W

theorem Portrayal.quotientBy_warpAt_le {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (Z : Set α) {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S) :
    (π.quotientBy Z).warpAt Θ ≤ π.warpAt Θ := by
  refine ((π.quotientBy Z).warpAt_le_iff (Θ := Θ)).mpr fun c hc hcΘ => ?_
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x
  have hbd : (c ∩ bd π.S).Nonempty := hcΘ.mono (inter_subset_inter_right _ hΘ_bd)
  exact (π.quotientBy_cellWarp_le Z hc hbd).trans (π.cellWarp_le_warpAt hc hcΘ)

/-- Every cell $c \in C(\Gamma)$ of a portrayal $\pi$ with $\operatorname{warp}(\pi) \le p$ has at
most $\max(3, 2p + 2)$ attachments in $G$ (which equals $2p + 2$ whenever $p \ge 1$). -/
theorem Portrayal.ncard_attachments_cellGraph_le {α : Type u} {β : Type v} {G : Hypergraph α β}
     (π : Portrayal G) {p : ℕ} (hwarp : π.warp ≤ p)
    {c : Set π.S} (hc : c ∈ π.Γ.C) :
    (attachments G (π.cellGraph c)).ncard ≤ max 3 (2 * p + 2) := by
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have hsub := π.attachments_cellGraph_subset_otherVertices hc
  by_cases hbd : (c ∩ bd π.S).Nonempty
  · obtain ⟨n₁, n₂, _, htilde, _, _, hn₁_mem, hn₂_mem⟩ := π.Γ.border_cell_exists_ends hc hbd
    have hsub₂ : (π.cellGraph c).vertexSet ∩ π.otherVertices c ⊆
        π.borderPlus n₁ ∪ π.borderPlus n₂ := by
      rintro v ⟨hvc, hvo⟩
      obtain ⟨n, hnt, hvn⟩ := π.p6_borderPlus hc hbd hvc hvo
      rw [htilde] at hnt
      rcases hnt with rfl | rfl
      · exact Or.inl hvn
      · exact Or.inr hvn
    have hcw_le : π.cellWarp c ≤ p := by
      rcases hbd with ⟨x, hxc, hxbd⟩
      have hΘ : connectedComponentIn (bd π.S) x ∈ cuffs π.S := ⟨x, hxbd, rfl⟩
      have hcΘ : (c ∩ connectedComponentIn (bd π.S) x).Nonempty :=
        ⟨x, hxc, mem_connectedComponentIn hxbd⟩
      exact (π.cellWarp_le_warpAt hc hcΘ).trans ((π.warpAt_le_warp hΘ).trans hwarp)
    have h₁ : (π.borderPlus n₁).ncard ≤ p + 1 := by
      have hn₁ : n₁ ∈ tilde c := by rw [htilde]; exact mem_insert _ _
      exact (π.ncard_borderPlus_le hn₁_mem).trans
        (Nat.add_le_add_right ((π.ncard_borderSet_le_cellWarp hc hbd hn₁).trans hcw_le) 1)
    have h₂ : (π.borderPlus n₂).ncard ≤ p + 1 := by
      have hn₂ : n₂ ∈ tilde c := by rw [htilde]; exact mem_insert_of_mem _ (mem_singleton _)
      exact (π.ncard_borderPlus_le hn₂_mem).trans
        (Nat.add_le_add_right ((π.ncard_borderSet_le_cellWarp hc hbd hn₂).trans hcw_le) 1)
    have hcard : (attachments G (π.cellGraph c)).ncard ≤
        (π.borderPlus n₁).ncard + (π.borderPlus n₂).ncard :=
      (ncard_le_ncard (hsub.trans hsub₂)
        ((π.borderPlus_finite hn₁_mem).union (π.borderPlus_finite hn₂_mem))).trans
        (ncard_union_le _ _)
    omega
  · have hsub₂ : (π.cellGraph c).vertexSet ∩ π.otherVertices c ⊆
        π.nodeVertex '' (tilde c ∩ π.domγ) := by
      rintro v ⟨hvc, hvo⟩
      obtain ⟨n, hn, rfl⟩ := π.p5 c hc hbd v hvc hvo
      exact ⟨n, hn, rfl⟩
    have hcard₁ : (attachments G (π.cellGraph c)).ncard ≤ (tilde c ∩ π.domγ).ncard :=
      (ncard_le_ncard (hsub.trans hsub₂)
        (((π.Γ.finite_tilde_cell hc).inter_of_left _).image _)).trans
        (ncard_image_le ((π.Γ.finite_tilde_cell hc).inter_of_left _))
    have hcard₂ : (tilde c ∩ π.domγ).ncard ≤ (tilde c).ncard :=
      ncard_le_ncard inter_subset_left (π.Γ.finite_tilde_cell hc)
    have hcard₃ : (tilde c).ncard ≤ 3 := π.Γ.ncard_tilde_cell_le hc
    omega

/-- **Graph Minors XVII, (6.2)** (page 174):
"Let $\mathscr{T}$ be a tangle in a hypergraph $G$ and let $\pi = (\Sigma, \Gamma, \alpha, \beta,
\gamma)$ be a $\mathscr{T}$-central portrayal of $G$ with $warp \le p$. Let $Z \subseteq V(G)$,
with $|Z| < ord(\mathscr{T}) - 2p - 2$. Define
$$ \begin{aligned} \alpha'(c) &= \alpha(c)/(Z \cap V(\alpha(c))) && (c \in C(\Gamma)) \\ \beta'(n)
&= \beta(n) - Z && (n \in N(\Gamma) \cap bd(\Sigma)) \\ \gamma' &= \gamma \mid \{n : n \in
dom(\gamma), \gamma(n) \notin Z\}. \end{aligned} $$
Then $\pi' = (\Sigma, \Gamma, \alpha', \beta', \gamma')$ is a $\mathscr{T}/Z$-central portrayal of
$G/Z$, resembling or simpler than $\pi$."

Note: For an internal cell $c \in C(\Gamma)$ the number of attachments of
$\alpha(c)$ is bounded by $|\tilde{c}| \le 3$, which is $\le 2p + 2$ whenever $p \ge 1$ (in
particular for all 0-redundant portrayals by (5.1)), while for $p = 0$ the bound is
$\max(3, 2p + 2) = 3$. -/
theorem theorem_6_2_proof {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
     (h𝒯 : IsTangle G θ 𝒯)
    (π : Portrayal G) (hT : π.IsCentral 𝒯) (hwarp : π.warp ≤ p)
    {Z : Set α} (hZ : Z ⊆ G.vertexSet)
    (hZ_lt : Z.ncard + max 3 (2 * p + 2) < θ) :
    (π.quotientBy Z).IsCentral (quotientTangle G 𝒯 Z) ∧
      ((π.quotientBy Z).Resembles π ∨ (π.quotientBy Z).IsSimpler π) := by
  have : T2Space π.S := π.isSurface.2.1
  refine ⟨fun c hc => ?_, ?_⟩
  · change IsSmallWrt (quotientTangle G 𝒯 Z)
      (quotientVertices (π.cellGraph c) (Z ∩ (π.cellGraph c).vertexSet))
    have hatt_le : (attachments (quotientVertices G Z)
        (quotientVertices (π.cellGraph c) (Z ∩ (π.cellGraph c).vertexSet))).ncard ≤
        max 3 (2 * p + 2) := by
      rw [quotientVertices_inter_vertexSet, attachments_quotientVertices]
      exact (ncard_le_ncard sdiff_subset attachments_finite).trans
        (π.ncard_attachments_cellGraph_le hwarp hc)
    exact (theorem_6_1_proof h𝒯 hZ (by omega) (π.cellGraph_le c hc) (by omega)).mp (hT c hc)
  · apply Portrayal.resembles_or_isSimpler_of_warpAt_le (π' := π.quotientBy Z) (Homeomorph.refl π.S)
    intro Θ hΘ
    have hle := π.quotientBy_warpAt_le Z hΘ
    have himg : (Homeomorph.refl π.S : π.S → π.S) '' Θ = Θ := image_id Θ
    change (π.quotientBy Z).warpAt Θ ≤ π.warpAt ((Homeomorph.refl π.S : π.S → π.S) '' Θ)
    rw [himg]
    exact hle

/-- Every $z$-redundant portrayal is $0$-redundant. -/
theorem Portrayal.IsRedundant.isZeroRedundant {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ z : ℕ}
    {π : Portrayal G} (h𝒯 : IsTangle G θ 𝒯) (hred : π.IsRedundant 𝒯 θ z) :
    π.IsZeroRedundant 𝒯 := by
  intro π' hT' hsimp
  have hT'' : (π'.quotientBy ∅).IsCentral (quotientTangle G 𝒯 ∅) := by
    intro c hc
    obtain ⟨B, hAB⟩ := hT' c hc
    have hsep := h𝒯.isSeparation hAB
    refine ⟨quotientVertices B ∅, ?_⟩
    change (quotientVertices (π'.cellGraph c) (∅ ∩ _), quotientVertices B ∅) ∈
      quotientTangle G 𝒯 ∅
    rw [quotientVertices_inter_vertexSet]
    exact ⟨IsSeparation.quotientVertices hsep ∅, ⟨(π'.cellGraph c, B), hAB, empty_subset _, rfl,
      rfl⟩⟩
  have hcg_eq : ∀ c : Set π'.S, (π'.quotientBy ∅).cellGraph c = π'.cellGraph c := fun c =>
    (quotientVertices_inter_vertexSet (π'.cellGraph c) ∅).trans (quotientVertices_empty _)
  have hbp_eq : ∀ n : π'.S, (π'.quotientBy ∅).borderPlus n = π'.borderPlus n := by
    intro n
    rw [π'.quotientBy_borderPlus ∅ n, sdiff_empty]
  have hbs_eq : ∀ n : π'.S, (π'.quotientBy ∅).borderSet n = π'.borderSet n := by
    intro n
    change π'.borderSet n \ ∅ = π'.borderSet n
    exact sdiff_empty
  have hnv_eq : ∀ n : π'.S, (π'.quotientBy ∅).nodeVertex n = π'.nodeVertex n := fun _ => rfl
  have hcw_eq : ∀ c : Set π'.S, (π'.quotientBy ∅).cellWarp c = π'.cellWarp c := by
    intro c
    unfold Portrayal.cellWarp Portrayal.CellWarpLE
    congr 1; ext p
    refine forall_congr' fun n₁ => imp_congr_right fun _ =>
      forall_congr' fun n₂ => imp_congr_right fun _ =>
      imp_congr_right fun _ => ?_
    rw [hbs_eq n₁, hbs_eq n₂, hbp_eq n₁, hbp_eq n₂, hcg_eq c, hnv_eq n₁, hnv_eq n₂]
  have hwarpAt_eq : ∀ Θ : Set π'.S, (π'.quotientBy ∅).warpAt Θ = π'.warpAt Θ := by
    intro Θ
    unfold Portrayal.warpAt
    congr 1; ext q
    exact exists_congr fun c => and_congr_right fun _ =>
      and_congr_right fun _ => by rw [hcw_eq c]
  have hwarp_eq : (π'.quotientBy ∅).warp = π'.warp := by
    classical
    unfold Portrayal.warp
    change (if (cuffs π'.S).Nonempty then _ else 1) = _
    split_ifs
    · refine congrArg (max 1) (congrArg sSup ?_)
      ext q
      exact exists_congr fun Θ => and_congr_right fun _ => by rw [hwarpAt_eq Θ]
    · rfl
  have hsimp' : (π'.quotientBy ∅).IsSimpler π := by
    rcases hsimp with ⟨hS, hw⟩ | ⟨ψ, hle, Θ, hΘ, hlt⟩
    · exact Or.inl ⟨hS, hwarp_eq.trans_le hw⟩
    · refine Or.inr ⟨ψ, fun Φ hΦ => ?_, Θ, hΘ, ?_⟩
      · exact (hwarpAt_eq Φ).trans_le (hle Φ hΦ)
      · exact (hwarpAt_eq Θ).trans_lt hlt
  exact hred.2 ∅ (empty_subset _) (by simp) (π'.quotientBy ∅) hT'' hsimp'

/-- When $\pi$ is $z$-redundant and $|Z| \le z$, $\pi.\text{quotientBy } Z$ resembles $\pi$ and is
$0$-redundant relative to $\mathcal{T} / Z$. -/
theorem Portrayal.quotientBy_resembles_and_isZeroRedundant
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p z : ℕ}
     (h𝒯 : IsTangle G θ 𝒯)
    (π : Portrayal G) (hT : π.IsCentral 𝒯) (hwarp : π.warp ≤ p)
    (hred : π.IsRedundant 𝒯 θ z)
    {Z : Set α} (hZ : Z ⊆ G.vertexSet) (hZ_le : Z.ncard ≤ z)
    (hZ_lt : Z.ncard + max 3 (2 * p + 2) < θ) :
    (π.quotientBy Z).IsCentral (quotientTangle G 𝒯 Z) ∧
      (π.quotientBy Z).Resembles π ∧
      (π.quotientBy Z).IsZeroRedundant (quotientTangle G 𝒯 Z) := by
  obtain ⟨hT', hres_or_simp⟩ := theorem_6_2_proof h𝒯 π hT hwarp hZ hZ_lt
  have hnot_simp : ¬ (π.quotientBy Z).IsSimpler π := hred.2 Z hZ hZ_le (π.quotientBy Z) hT'
  have hres : (π.quotientBy Z).Resembles π := hres_or_simp.resolve_right hnot_simp
  refine ⟨hT', hres, ?_⟩
  exact hres.isZeroRedundant_quotient hred hZ hZ_le

/-- The portrayal after restricting cells to one side of a separation
and identifying its boundary vertices. -/
@[expose]
noncomputable def Portrayal.restrictQuotient {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (A B : Hypergraph α β) (hsep : IsSeparation G A B)
    (c' : Set π.S) (hc' : c' ∈ π.Γ.C) :
    Portrayal (quotientVertices G (A.vertexSet ∩ B.vertexSet)) := by
  classical
  let Z := A.vertexSet ∩ B.vertexSet
  have hnotA_iff : ∀ {v : α}, v ∈ G.vertexSet → (v ∉ A.vertexSet ↔ v ∈ B.vertexSet ∧ v ∉ Z) := by
    intro v hv
    have hvAB : v ∈ A.vertexSet ∪ B.vertexSet := hsep.vertexSet_union ▸ hv
    refine ⟨fun hvA => ⟨hvAB.resolve_left hvA, fun hZ => hvA hZ.1⟩, fun ⟨_, hvZ⟩ hvA => hvZ ⟨hvA,
      ‹_›⟩⟩
  let QB : Set π.S → Hypergraph α β := fun c => quotientVertices (π.cellGraph c ∩ B) Z
  let QA : Hypergraph α β := quotientVertices A Z
  have hQB_le : ∀ c ∈ π.Γ.C, QB c ≤ quotientVertices G Z := by
    intro c hc
    refine quotientVertices_mono ?_ Z
    exact ⟨inter_subset_left.trans (π.cellGraph_le c hc).1,
      inter_subset_left.trans (π.cellGraph_le c hc).2,
      fun e he => by
        ext v
        simp only [ends, Inter.inter, mem_ofPred_eq]
        have h1 := congrArg (v ∈ ·) ((π.cellGraph_le c hc).3 e he.1)
        have h2 := congrArg (v ∈ ·) (hsep.right_le.3 e he.2)
        dsimp [ends] at h1 h2
        exact ⟨fun h => ⟨h1.mp h, h2.mp h⟩, fun h => h1.mpr h.1⟩⟩
  have hQA_le : QA ≤ quotientVertices G Z := quotientVertices_mono hsep.left_le Z
  have hunion_le : ∀ {H₁ H₂ H : Hypergraph α β}, H₁ ≤ H → H₂ ≤ H → H₁ ∪ H₂ ≤ H :=
    fun h₁ h₂ => union_le h₁ h₂
  let α' : Set π.S → Hypergraph α β := fun c => if c = c' then QB c ∪ QA else QB c
  have hα'_notA : ∀ c ∈ π.Γ.C, ∀ v, v ∉ A.vertexSet →
      (v ∈ (α' c).vertexSet ↔ v ∈ (π.cellGraph c).vertexSet) := by
    intro c hc v hvA
    dsimp only [α', QB, QA, quotientVertices, Union.union, Inter.inter]
    split_ifs
    · constructor
      · rintro (⟨⟨hvc, _⟩, _⟩ | ⟨hvA', _⟩)
        · exact hvc
        · exact (hvA hvA').elim
      · intro hvc
        have hB := (hnotA_iff ((π.cellGraph_le c hc).1 hvc)).mp hvA
        exact Or.inl ⟨⟨hvc, hB.1⟩, hB.2⟩
    · constructor
      · exact fun ⟨⟨hvc, _⟩, _⟩ => hvc
      · intro hvc
        have hB := (hnotA_iff ((π.cellGraph_le c hc).1 hvc)).mp hvA
        exact ⟨⟨hvc, hB.1⟩, hB.2⟩
  have hα'_other : ∀ {c₁ c₂ : Set π.S}, c₁ ∈ π.Γ.C → c₂ ∈ π.Γ.C → c₁ ≠ c₂ →
      ∀ {v : α}, v ∈ (α' c₁).vertexSet → v ∈ (α' c₂).vertexSet →
      v ∉ A.vertexSet ∧ v ∈ (π.cellGraph c₁).vertexSet ∧ v ∈ (π.cellGraph c₂).vertexSet := by
    intro c₁ c₂ hc₁ hc₂ hne v hv₁ hv₂
    have hvnotA : v ∉ A.vertexSet := by
      intro hvA
      by_cases h₁ : c₁ = c'
      · have h₂ : c₂ ≠ c' := fun h => hne (h₁.trans h.symm)
        dsimp only [α'] at hv₂
        rw [ite_eq_right h₂] at hv₂
        exact hv₂.2 ⟨hvA, hv₂.1.2⟩
      · dsimp only [α'] at hv₁
        rw [ite_eq_right h₁] at hv₁
        exact hv₁.2 ⟨hvA, hv₁.1.2⟩
    exact ⟨hvnotA, (hα'_notA c₁ hc₁ v hvnotA).mp hv₁, (hα'_notA c₂ hc₂ v hvnotA).mp hv₂⟩
  exact
    { S := π.S
      top := π.top
      isSurface := π.isSurface
      connected := π.connected
      Γ := π.Γ
      cellGraph := α'
      borderSet := fun n => π.borderSet n \ A.vertexSet
      domγ := {n ∈ π.domγ | π.nodeVertex n ∉ A.vertexSet}
      nodeVertex := π.nodeVertex
      cellGraph_le := by
        intro c hc
        dsimp only [α']
        split_ifs
        · exact hunion_le (hQB_le c hc) hQA_le
        · exact hQB_le c hc
      borderSet_subset := by
        intro n hn v ⟨hvn, hvA⟩
        have hvG := π.borderSet_subset n hn hvn
        exact ⟨hvG, ((hnotA_iff hvG).mp hvA).2⟩
      domγ_subset := fun n hn => π.domγ_subset hn.1
      nodeVertex_mem := by
        intro n ⟨hn, hvA⟩
        have hvG := π.nodeVertex_mem n hn
        exact ⟨hvG, ((hnotA_iff hvG).mp hvA).2⟩
      nodeVertex_injOn := π.nodeVertex_injOn.mono fun _ hn => hn.1
      p1_vertex := by
        rintro v ⟨hvG, hvZ⟩
        by_cases hvA : v ∈ A.vertexSet
        · refine ⟨c', hc', ?_⟩
          dsimp only [α']
          rw [ite_eq_left rfl]
          exact Or.inr ⟨hvA, hvZ⟩
        · obtain ⟨c, hc, hvc⟩ := π.p1_vertex v hvG
          exact ⟨c, hc, (hα'_notA c hc v hvA).mpr hvc⟩
      p1_edge := by
        intro e heG
        have heAB : e ∈ A.edgeSet ∪ B.edgeSet := hsep.edgeSet_union ▸ heG
        rcases heAB with heA | heB
        · refine ⟨c', hc', ?_⟩
          dsimp only [α']
          rw [ite_eq_left rfl]
          exact Or.inr heA
        · obtain ⟨c, hc, hec⟩ := π.p1_edge e heG
          refine ⟨c, hc, ?_⟩
          dsimp only [α']
          split_ifs
          · exact Or.inl ⟨hec, heB⟩
          · exact ⟨hec, heB⟩
      p1_disjoint := by
        intro c₁ hc₁ c₂ hc₂ hne
        refine Set.disjoint_left.mpr fun e he₁ he₂ => ?_
        have hdisjAB : Disjoint A.edgeSet B.edgeSet :=
          Set.disjoint_iff_inter_eq_empty.mpr hsep.edgeSet_inter_eq
        dsimp only [α', QB, QA, quotientVertices, Union.union, Inter.inter] at he₁ he₂
        split_ifs at he₁ he₂ with h₁ h₂
        · exact hne (h₁.trans h₂.symm)
        · rcases he₁ with ⟨hec₁, _⟩ | heA
          · exact Set.disjoint_left.mp (π.p1_disjoint c₁ hc₁ c₂ hc₂ hne) hec₁ he₂.1
          · exact Set.disjoint_left.mp hdisjAB heA he₂.2
        · rcases he₂ with ⟨hec₂, _⟩ | heA
          · exact Set.disjoint_left.mp (π.p1_disjoint c₁ hc₁ c₂ hc₂ hne) he₁.1 hec₂
          · exact Set.disjoint_left.mp hdisjAB heA he₁.2
        · exact Set.disjoint_left.mp (π.p1_disjoint c₁ hc₁ c₂ hc₂ hne) he₁.1 he₂.1
      p2 := by
        intro c hc n ⟨hnt, hnγ, hvA⟩
        exact (hα'_notA c hc (π.nodeVertex n) hvA).mpr (π.p2 c hc n ⟨hnt, hnγ⟩)
      p3_notMem := fun n ⟨⟨hnγ, _⟩, hnbd⟩ hmem => π.p3_notMem n ⟨hnγ, hnbd⟩ hmem.1
      p3_subset := by
        intro c hc hbd n hnt v ⟨hvn, hvA⟩
        exact (hα'_notA c hc v hvA).mpr (π.p3_subset c hc hbd n hnt hvn)
      p4_disjoint := fun Θ₁ hΘ₁ Θ₂ hΘ₂ hne n₁ hn₁ n₂ hn₂ =>
        (π.p4_disjoint Θ₁ hΘ₁ Θ₂ hΘ₂ hne n₁ hn₁ n₂ hn₂).mono sdiff_subset sdiff_subset
      p4_notMem := fun Θ hΘ n₁ hn₁ n₂ hn₂ hn₂Θ hmem =>
        π.p4_notMem Θ hΘ n₁ hn₁ n₂ hn₂.1 hn₂Θ hmem.1
      p5 := by
        intro c hc hbd v hv₁ ⟨c₂, hc₂, hne, hv₂⟩
        obtain ⟨hvA, hvc₁, hvc₂⟩ := hα'_other hc hc₂ hne.symm hv₁ hv₂
        obtain ⟨n, ⟨hnt, hnγ⟩, rfl⟩ := π.p5 c hc hbd v hvc₁ ⟨c₂, hc₂, hne, hvc₂⟩
        exact ⟨n, ⟨hnt, hnγ, hvA⟩, rfl⟩
      p6 := by
        intro c hc hbd v hv₁ ⟨c₂, hc₂, hne, hv₂⟩
        obtain ⟨hvA, hvc₁, hvc₂⟩ := hα'_other hc hc₂ hne.symm hv₁ hv₂
        obtain ⟨n, hnt, hvn | ⟨hnγ, rfl⟩⟩ := π.p6 c hc hbd v hvc₁ ⟨c₂, hc₂, hne, hvc₂⟩
        · exact ⟨n, hnt, Or.inl ⟨hvn, hvA⟩⟩
        · exact ⟨n, hnt, Or.inr ⟨⟨hnγ, hvA⟩, rfl⟩⟩
      p7 := by
        intro Θ hΘ n₁ hn₁ n₂ hn₂ n₃ hn₃ n₄ hn₄ hord v hv₁ hv₃
        have hvA : v ∉ A.vertexSet := by
          rcases hv₁ with ⟨_, hvA⟩ | ⟨⟨_, hvA⟩, rfl⟩ <;> exact hvA
        have hv₁' : v ∈ π.borderPlus n₁ := by
          rcases hv₁ with ⟨hvn₁, _⟩ | ⟨⟨hn₁γ, _⟩, rfl⟩
          · exact Or.inl hvn₁
          · exact Or.inr ⟨hn₁γ, rfl⟩
        have hv₃' : v ∈ π.borderPlus n₃ := by
          rcases hv₃ with ⟨hvn₃, _⟩ | ⟨⟨hn₃γ, _⟩, rfl⟩
          · exact Or.inl hvn₃
          · exact Or.inr ⟨hn₃γ, rfl⟩
        rcases π.p7 Θ hΘ n₁ hn₁ n₂ hn₂ n₃ hn₃ n₄ hn₄ hord v hv₁' hv₃' with
          (hvn₂ | ⟨hn₂γ, rfl⟩) | (hvn₄ | ⟨hn₄γ, rfl⟩)
        · exact Or.inl (Or.inl ⟨hvn₂, hvA⟩)
        · exact Or.inl (Or.inr ⟨⟨hn₂γ, hvA⟩, rfl⟩)
        · exact Or.inr (Or.inl ⟨hvn₄, hvA⟩)
        · exact Or.inr (Or.inr ⟨⟨hn₄γ, hvA⟩, rfl⟩) }

theorem Portrayal.restrictQuotient_borderPlus {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (A B : Hypergraph α β) (hsep : IsSeparation G A B)
    (c' : Set π.S) (hc' : c' ∈ π.Γ.C) (n : π.S) :
    (π.restrictQuotient A B hsep c' hc').borderPlus n = π.borderPlus n \ A.vertexSet := by
  ext v
  simp only [Portrayal.borderPlus, Portrayal.restrictQuotient, mem_ofPred_eq, mem_sdiff]
  constructor
  · rintro (⟨h, hvA⟩ | ⟨⟨hnγ, hvA⟩, rfl⟩)
    · exact ⟨Or.inl h, hvA⟩
    · exact ⟨Or.inr ⟨hnγ, rfl⟩, hvA⟩
  · rintro ⟨h | ⟨hnγ, rfl⟩, hvA⟩
    · exact Or.inl ⟨h, hvA⟩
    · exact Or.inr ⟨⟨hnγ, hvA⟩, rfl⟩

theorem Portrayal.restrictQuotient_isCentral {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
     (h𝒯 : IsTangle G θ 𝒯)
    (π : Portrayal G) (hT : π.IsCentral 𝒯) (hwarp : π.warp ≤ p)
    {A B : Hypergraph α β} (hAB : (A, B) ∈ 𝒯)
    (hZ_lt : (A.vertexSet ∩ B.vertexSet).ncard + max 3 (2 * p + 2) < θ)
    (c' : Set π.S) (hc' : c' ∈ π.Γ.C) :
    (π.restrictQuotient A B (h𝒯.isSeparation hAB) c' hc').IsCentral
      (quotientTangle G 𝒯 (A.vertexSet ∩ B.vertexSet)) := by
  classical
  set Z := A.vertexSet ∩ B.vertexSet
  have hsep := h𝒯.isSeparation hAB
  have hZ_sub : Z ⊆ G.vertexSet := inter_subset_left.trans hsep.left_le.1
  have hTangle' : IsTangle (quotientVertices G Z) (θ - Z.ncard) (quotientTangle G 𝒯 Z) :=
    theorem_4_2_proof h𝒯 hZ_sub (by omega)
  obtain ⟨hT_quot, _⟩ := theorem_6_2_proof h𝒯 π hT hwarp hZ_sub hZ_lt
  have hQB_small : ∀ c ∈ π.Γ.C,
      IsSmallWrt (quotientTangle G 𝒯 Z) (quotientVertices (π.cellGraph c ∩ B) Z) := by
    intro c hc
    have hsmall_c : IsSmallWrt (quotientTangle G 𝒯 Z) (quotientVertices (π.cellGraph c) Z) := by
      have := hT_quot c hc
      change IsSmallWrt (quotientTangle G 𝒯 Z)
        (quotientVertices (π.cellGraph c) (Z ∩ (π.cellGraph c).vertexSet)) at this
      rwa [quotientVertices_inter_vertexSet] at this
    have hle : quotientVertices (π.cellGraph c ∩ B) Z ≤ quotientVertices (π.cellGraph c) Z :=
      quotientVertices_mono (inter_le_left (π.cellGraph_le c hc) hsep.right_le) Z
    have hatt_le : (attachments (quotientVertices G Z)
        (quotientVertices (π.cellGraph c ∩ B) Z)).ncard ≤ max 3 (2 * p + 2) := by
      rw [attachments_quotientVertices]
      have hsub_att : attachments G (π.cellGraph c ∩ B) \ Z ⊆ attachments G (π.cellGraph c) := by
        rintro v ⟨⟨⟨hvc, hvB⟩, e, ⟨heG, he_not⟩, hinc⟩, hvZ⟩
        have heAB : e ∈ A.edgeSet ∪ B.edgeSet := hsep.edgeSet_union ▸ heG
        have he_not_A : e ∉ A.edgeSet := by
          intro heA
          have hincA : A.Inc e v := (inc_iff_of_le hsep.left_le heA).2 hinc
          exact hvZ ⟨A.vertex_mem_of_inc hincA, hvB⟩
        have heB : e ∈ B.edgeSet := heAB.resolve_left he_not_A
        exact ⟨hvc, e, ⟨heG, fun hec => he_not ⟨hec, heB⟩⟩, hinc⟩
      exact (ncard_le_ncard hsub_att attachments_finite).trans
        (π.ncard_attachments_cellGraph_le hwarp hc)
    exact hsmall_c.mono hTangle' hle (by omega)
  have hQA_small : IsSmallWrt (quotientTangle G 𝒯 Z) (quotientVertices A Z) :=
    ⟨quotientVertices B Z, IsSeparation.quotientVertices hsep Z, ⟨(A, B), hAB, subset_rfl, rfl,
      rfl⟩⟩
  have hQA_att_empty : attachments (quotientVertices G Z) (quotientVertices A Z) = ∅ := by
    rw [attachments_quotientVertices]
    ext v
    simp only [mem_sdiff, mem_empty_iff_false, iff_false, not_and, not_not]
    intro hvAtt
    exact attachments_subset_inter_of_isSeparation hsep hvAtt
  intro c hc
  change IsSmallWrt (quotientTangle G 𝒯 Z) (if c = c' then _ else _)
  split_ifs
  · refine (hQB_small c hc).union hTangle' hQA_small ?_
    have hsub := @attachments_union_subset α β (quotientVertices G Z)
      (quotientVertices (π.cellGraph c ∩ B) Z) (quotientVertices A Z)
    rw [hQA_att_empty, union_empty] at hsub
    exact (ncard_le_ncard hsub attachments_finite).trans_lt
      ((hQB_small c hc).ncard_attachments_lt hTangle')
  · exact hQB_small c hc

/-- Next index around `Fin k` for $k \ge 2$. -/
def nextIdx {k : ℕ} (hk : 2 ≤ k) (i : Fin k) : Fin k :=
  cyclicSucc (by omega) i

theorem nextIdx_ne_self {k : ℕ} (hk : 2 ≤ k) (i : Fin k) : nextIdx hk i ≠ i :=
  cyclicSucc_ne_self hk i

/-- **Graph Minors XVII, proof of (6.6), Claim (1)** (page 176):
"For each $x \in X$ there is at most one $n \in N(\Gamma) \cap \Theta$ such that
$x \in \beta(n+)$ and $x \notin \beta(n'+)$ where $n'$ is the node of $N(\Gamma)$ bordering
$\Theta$ immediately following $n$." -/
theorem lemma_6_6_claim_1 {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S} {k : ℕ} (E : π.Γ.CuffEnumeration Θ k)
    {x : α} {i₁ i₂ : Fin k}
    (hi₁ : x ∈ π.borderPlus (E.node i₁) ∧ x ∉ π.borderPlus (E.node (nextIdx E.two_le i₁)))
    (hi₂ : x ∈ π.borderPlus (E.node i₂) ∧ x ∉ π.borderPlus (E.node (nextIdx E.two_le i₂))) :
    i₁ = i₂ := by
  by_contra hne
  have hk : 2 ≤ k := E.two_le
  have v12 : i₁.1 ≠ i₂.1 := fun h => hne (Fin.ext h)
  have b1 := i₁.2
  have b2 := i₂.2
  have hcyc : cyclicDist i₁ (nextIdx hk i₁) + cyclicDist (nextIdx hk i₁) i₂ +
      cyclicDist i₂ (nextIdx hk i₂) ≤ k := by
    have hnext1 : (nextIdx hk i₁).1 = if i₁.1 + 1 < k then i₁.1 + 1 else 0 := by
      dsimp [nextIdx, cyclicSucc]
      split_ifs with h
      · exact Nat.mod_eq_of_lt h
      · have : i₁.1 + 1 = k := by omega
        rw [this, Nat.mod_self]
    have hnext2 : (nextIdx hk i₂).1 = if i₂.1 + 1 < k then i₂.1 + 1 else 0 := by
      dsimp [nextIdx, cyclicSucc]
      split_ifs with h
      · exact Nat.mod_eq_of_lt h
      · have : i₂.1 + 1 = k := by omega
        rw [this, Nat.mod_self]
    simp only [cyclicDist_eq_ite, hnext1, hnext2]
    split_ifs <;> omega
  have hp7 := π.p7_of_cyclicDist E hcyc hi₁.1 hi₂.1
  rcases hp7 with h1 | h2
  · exact hi₁.2 h1
  · exact hi₂.2 h2

/-- **Graph Minors XVII, proof of (6.6), Claim (2)** (page 176):
"For each $n \in N(\Gamma) \cap \Theta$, if $|\beta(n)| = q$ then $W \cap \beta(n) \ne \emptyset$."
-/
theorem lemma_6_6_claim_2 {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) {Θ : Set π.S} (hΘ_bd : Θ ⊆ bd π.S)
    {q : ℕ} {X : Set α} (hX : ∀ n ∈ π.Γ.N ∩ Θ, (X ∩ π.borderPlus n).Nonempty)
    {z_fn : α → α}
    (hz_spec : ∀ x ∈ X, ∀ n ∈ π.domγ ∩ bd π.S, x = π.nodeVertex n → (π.borderSet n).ncard = q →
      z_fn x ∈ π.borderSet n)
    {W : Set α} (hXW : X ⊆ W) (hzW : z_fn '' X ⊆ W)
    {n : π.S} (hn : n ∈ π.Γ.N ∩ Θ) (hcard : (π.borderSet n).ncard = q) :
    (W ∩ π.borderSet n).Nonempty := by
  obtain ⟨x, hxX, hxn⟩ := hX n hn
  rcases hxn with hxn_bs | ⟨hn_dom, rfl⟩
  · exact ⟨x, hXW hxX, hxn_bs⟩
  · exact ⟨z_fn (π.nodeVertex n), hzW ⟨π.nodeVertex n, hxX, rfl⟩,
      hz_spec (π.nodeVertex n) hxX n ⟨hn_dom, hΘ_bd hn.2⟩ rfl hcard⟩

/-- **Graph Minors XVII, proof of (6.6), Claim (3)** (page 177):
"For each cell $c$ bordering $\Theta$ with ends $n_1, n_2 \in \operatorname{dom}(\gamma)$, if
$\gamma(n_1), \gamma(n_2) \notin W$ and $|\beta(n_1) - W| = |\beta(n_2) - W| = q - 1$ then
$W \cap \beta(n_1) \cap \beta(n_2) \ne \emptyset$." -/
theorem lemma_6_6_claim_3 {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S} {k : ℕ} (E : π.Γ.CuffEnumeration Θ k)
    {X : Set α} (hX : ∀ n ∈ π.Γ.N ∩ Θ, (X ∩ π.borderPlus n).Nonempty)
    {y_fn : α → α}
    (hy_spec : ∀ x ∈ X, ∀ i : Fin k,
      x ∈ π.borderPlus (E.node i) → x ∉ π.borderPlus (E.node (nextIdx E.two_le i)) →
      E.node i ∈ π.domγ → y_fn x = π.nodeVertex (E.node i))
    {W : Set α} (hXW : X ⊆ W) (hyW : y_fn '' X ⊆ W)
    {c : Set π.S} (hc : c ∈ π.Γ.C) (hcΘ : (c ∩ Θ).Nonempty)
    {n₁ n₂ : π.S} (htilde : tilde c = {n₁, n₂})
    (hn₁_dom : n₁ ∈ π.domγ) (hn₂_dom : n₂ ∈ π.domγ)
    (hn₁_notW : π.nodeVertex n₁ ∉ W) (hn₂_notW : π.nodeVertex n₂ ∉ W) :
    (W ∩ π.borderSet n₁ ∩ π.borderSet n₂).Nonempty := by
  have hc_range : c ∈ Set.range E.cell := by
    rw [E.range_cell]; exact ⟨hc, hcΘ⟩
  rcases hc_range with ⟨i, rfl⟩
  let m₁ := E.node i
  let m₂ := E.node (nextIdx E.two_le i)
  have htilde_i : tilde (E.cell i) = {m₁, m₂} := E.cell_tilde i
  have hpair_eq : ({m₁, m₂} : Set π.S) = {n₁, n₂} := htilde_i.symm.trans htilde
  have hm₁_mem : m₁ ∈ ({n₁, n₂} : Set π.S) := hpair_eq ▸ mem_insert _ _
  have hm₂_mem : m₂ ∈ ({n₁, n₂} : Set π.S) := hpair_eq ▸ mem_insert_of_mem _ (mem_singleton _)
  have hm₁_dom : m₁ ∈ π.domγ := by rcases hm₁_mem with h | h <;> exact h ▸ ‹_›
  have hm₂_dom : m₂ ∈ π.domγ := by rcases hm₂_mem with h | h <;> exact h ▸ ‹_›
  have hm₁_notW : π.nodeVertex m₁ ∉ W := by rcases hm₁_mem with h | h <;> exact h ▸ ‹_›
  have hm₂_notW : π.nodeVertex m₂ ∉ W := by rcases hm₂_mem with h | h <;> exact h ▸ ‹_›
  have hm₁_Θ : m₁ ∈ π.Γ.N ∩ Θ := by
    rw [← E.range_node]; exact mem_range_self i
  obtain ⟨x, hxX, hxm₁⟩ := hX m₁ hm₁_Θ
  have hxW : x ∈ W := hXW hxX
  have hx_bs₁ : x ∈ π.borderSet m₁ := by
    rcases hxm₁ with h | ⟨_, rfl⟩
    · exact h
    · exact (hm₁_notW hxW).elim
  have hxm₂ : x ∈ π.borderPlus m₂ := by
    by_contra hnot
    have hy_eq := hy_spec x hxX i hxm₁ hnot hm₁_dom
    exact hm₁_notW (hy_eq ▸ hyW ⟨x, hxX, rfl⟩)
  have hx_bs₂ : x ∈ π.borderSet m₂ := by
    rcases hxm₂ with h | ⟨_, rfl⟩
    · exact h
    · exact (hm₂_notW hxW).elim
  have h_inter_eq : π.borderSet m₁ ∩ π.borderSet m₂ = π.borderSet n₁ ∩ π.borderSet n₂ := by
    have hm_ne : m₁ ≠ m₂ := E.injective_node.ne (nextIdx_ne_self E.two_le i).symm
    rcases hm₁_mem with h₁ | h₁ <;> rcases hm₂_mem with h₂ | h₂
    · exact (hm_ne (h₁.trans h₂.symm)).elim
    · rw [h₁, h₂]
    · rw [h₁, h₂, Set.inter_comm]
    · exact (hm_ne (h₁.trans h₂.symm)).elim
  refine ⟨x, ?_⟩
  rw [Set.inter_assoc, ← h_inter_eq, ← Set.inter_assoc]
  exact ⟨⟨hxW, hx_bs₁⟩, hx_bs₂⟩

/-- The discrete (edgeless) subhypergraph of $G$ on a vertex subset $W \subseteq V(G)$. -/
@[expose]
def discreteSubhypergraph {α : Type u} {β : Type v} (G : Hypergraph α β) (W : Set α)
    (hW : W ⊆ G.vertexSet) : Hypergraph α β where
  vertexSet := W
  edgeSet := ∅
  Inc _ _ := False
  vertex_mem_of_inc _ _ h := h.elim
  edge_mem_of_inc _ _ h := h.elim
  vertexSet_finite := G.vertexSet_finite.subset hW
  edgeSet_finite := finite_empty

theorem IsTangle.discrete_mem {α : Type u} {β : Type v} {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {W : Set α} (hW : W ⊆ G.vertexSet) (hcard : W.ncard < θ) :
    (discreteSubhypergraph G W hW, G) ∈ 𝒯 := by
  let A := discreteSubhypergraph G W hW
  have hA_le : A ≤ G := ⟨hW, empty_subset _, fun _ h => h.elim⟩
  have hsep : G.IsSeparation A G := by
    rw [isSeparation_iff_of_le hA_le le_rfl]
    exact ⟨union_eq_self_of_subset_left hW, empty_union _, empty_inter _⟩
  have hord : separationOrder A G < θ := by
    change (W ∩ G.vertexSet).ncard < θ
    rwa [inter_eq_self_of_subset_left hW]
  have hGA_not : (G, A) ∉ 𝒯 := fun hGA => h𝒯.axiom3 hGA rfl
  exact (h𝒯.axiom1 hsep hord).resolve_right hGA_not

/-- Pure surface-and-painting topological property of a closed disc $\Delta \subseteq \Sigma$
bounded by a $\Gamma$-normal $I$-arc $F$ (with ends $n_1, n_2$ on a cuff $\Theta$) and
$\operatorname{bd}(\Sigma)$:
(1) for every $c_1 \in C(\Gamma)$ with $c_1 \subseteq \Delta$ and every $c_2 \in C(\Gamma)$ with
    $c_2 \not\subseteq \Delta$, $\tilde{c}_1 \cap \tilde{c}_2 \subseteq F$;
(2) there is a border cell $c_1 \in C(\Gamma)$ with $c_1 \subseteq \Delta$ and $n_1 \in
\tilde{c}_1$;
    and
(3) for every node $n' \in N(\Gamma) \cap \Delta \cap \operatorname{bd}(\Sigma)$ and every cell
    $c \in C(\Gamma)$ bordering $\Theta$ with $c \not\subseteq \Delta$ and $m \in \tilde{c}$,
    $n' \in \Theta$ and $n_1, n', n_2, m$ are in order on $\Theta$. -/
@[expose] def NormalIArcDiscPaintingStatement : Prop :=
  ∀ (S : Type) [TopologicalSpace S] [CompactSpace S] [T2Space S] [ConnectedSpace S],
    IsSurface S → ∀ (Γ : Painting S) (F Δ : Set S) (Θ : Set S) (n₁ n₂ : S),
    Γ.IsNormal F → IsLineWithEnds F n₁ n₂ → F ∩ bd S = {n₁, n₂} →
    Θ ∈ cuffs S → n₁ ∈ Θ → n₂ ∈ Θ →
    IsClosedDisc Δ → F ⊆ discBd Δ → discBd Δ ⊆ F ∪ bd S →
    (∀ c₁ ∈ Γ.C, c₁ ⊆ Δ → ∀ c₂ ∈ Γ.C, ¬ c₂ ⊆ Δ → tilde c₁ ∩ tilde c₂ ⊆ F) ∧
    (∃ c₁ ∈ Γ.C, c₁ ⊆ Δ ∧ (c₁ ∩ bd S).Nonempty ∧ n₁ ∈ tilde c₁) ∧
    (∀ n' ∈ Γ.N ∩ Δ ∩ bd S, ∀ c ∈ Γ.C, (c ∩ Θ).Nonempty → ¬ c ⊆ Δ → ∀ m ∈ tilde c,
      n' ∈ Θ ∧ GM19.InOrderOn Θ n₁ n' n₂ m)

theorem Portrayal.cuff_eq_of_borderPlus_inter_nonempty {α : Type u} {β : Type v}
    {G : Hypergraph α β} (π : Portrayal G)
    {n₁ n₂ : π.S} (hn₁ : n₁ ∈ π.Γ.N ∩ bd π.S) (hn₂ : n₂ ∈ π.Γ.N ∩ bd π.S)
    {v : α} (hv₁ : v ∈ π.borderPlus n₁) (hv₂ : v ∈ π.borderPlus n₂) :
    ∃ Θ ∈ cuffs π.S, n₁ ∈ Θ ∧ n₂ ∈ Θ := by
  let Θ₁ := connectedComponentIn (bd π.S) n₁
  let Θ₂ := connectedComponentIn (bd π.S) n₂
  have hΘ₁ : Θ₁ ∈ cuffs π.S := ⟨n₁, hn₁.2, rfl⟩
  have hΘ₂ : Θ₂ ∈ cuffs π.S := ⟨n₂, hn₂.2, rfl⟩
  have hn₁Θ₁ : n₁ ∈ Θ₁ := mem_connectedComponentIn hn₁.2
  have hn₂Θ₂ : n₂ ∈ Θ₂ := mem_connectedComponentIn hn₂.2
  refine ⟨Θ₁, hΘ₁, hn₁Θ₁, ?_⟩
  by_contra hn₂_not_Θ₁
  have hne : Θ₁ ≠ Θ₂ := fun h => hn₂_not_Θ₁ (h ▸ hn₂Θ₂)
  have hn₁_not_Θ₂ : n₁ ∉ Θ₂ := fun h => hne (connectedComponentIn_eq h).symm
  rcases hv₁ with hv₁ | ⟨hn₁γ, rfl⟩ <;> rcases hv₂ with hv₂ | ⟨hn₂γ, hEq⟩
  · exact Set.disjoint_left.mp (π.p4_disjoint Θ₁ hΘ₁ Θ₂ hΘ₂ hne n₁ ⟨hn₁.1, hn₁Θ₁⟩ n₂ ⟨hn₂.1, hn₂Θ₂⟩)
      hv₁ hv₂
  · rw [hEq] at hv₁
    exact π.p4_notMem Θ₁ hΘ₁ n₁ ⟨hn₁.1, hn₁Θ₁⟩ n₂ hn₂γ hn₂_not_Θ₁ hv₁
  · exact π.p4_notMem Θ₂ hΘ₂ n₂ ⟨hn₂.1, hn₂Θ₂⟩ n₁ hn₁γ hn₁_not_Θ₂ hv₂
  · have := π.nodeVertex_injOn hn₁γ hn₂γ hEq
    exact hn₂_not_Θ₁ (this ▸ hn₁Θ₁)

end GraphMinor.GM17
