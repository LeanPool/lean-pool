/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section2a
import LeanPool.GraphMinor.GM09.Section2d
import LeanPool.GraphMinor.GM09.Section3a

/-!
# Graph Minors IX, Section 3 (Part 2): Attachments, Switches, and (3.2)

This file establishes:
- basic properties of attachments (`IsAttachmentWithEnds`, `IsAttachment`), feet (`IsFoot`),
  legs (`IsLeg`), and switches (`IsSwitch`),
- Graph Minors IX, (3.2) (`lemma_3_2_claim_1`, `lemma_3_2_claim_2`, `lemma_3_2_claim_3`,
  `theorem_3_2`, pages 47–48): every attachment to a crooked transaction that is not exchangeable
  is an overpass attachment.
-/

public section

namespace GraphMinor.GM09

open Set Graph GraphMinor GraphMinor.Surface

universe u v

variable {α : Type u} {β : Type v}

namespace Society

/-! ## Attachments, legs, and switches -/

theorem IsAttachmentWithEnds.foot_mem_transactionUnion (S : Society α β)
    {P_set : Set (Graph α β)} {P : Graph α β} {b u : α}
    (h : S.IsAttachmentWithEnds P_set P b u) :
    b ∈ V(S.transactionUnion P_set) := by
  have hb : b ∈ V(P) ∩ V(S.transactionUnion P_set) := h.2.1.symm ▸ mem_singleton b
  exact hb.2

theorem IsAttachmentWithEnds.end_mem_bar_diff (S : Society α β)
    {P_set : Set (Graph α β)} {P : Graph α β} {b u : α}
    (h : S.IsAttachmentWithEnds P_set P b u) :
    u ∈ S.Ω.bar \ S.transactionEnds P_set := by
  have hu : u ∈ V(P) ∩ (S.Ω.bar \ S.transactionEnds P_set) := h.2.2.symm ▸ mem_singleton u
  exact hu.2

theorem IsAttachmentWithEnds.end_mem_bar (S : Society α β)
    {P_set : Set (Graph α β)} {P : Graph α β} {b u : α}
    (h : S.IsAttachmentWithEnds P_set P b u) :
    u ∈ S.Ω.bar :=
  (h.end_mem_bar_diff S).1

theorem IsAttachmentWithEnds.end_not_mem_transactionEnds (S : Society α β)
    {P_set : Set (Graph α β)} {P : Graph α β} {b u : α}
    (h : S.IsAttachmentWithEnds P_set P b u) :
    u ∉ S.transactionEnds P_set :=
  (h.end_mem_bar_diff S).2

theorem IsAttachmentWithEnds.exists_leg (S : Society α β)
    {P_set : Set (Graph α β)} {P : Graph α β} {b u : α}
    (h : S.IsAttachmentWithEnds P_set P b u) :
    ∃ L ∈ P_set, b ∈ V(L) := by
  have hb : b ∈ V(S.transactionUnion P_set) := h.foot_mem_transactionUnion S
  change b ∈ ⋃ L ∈ P_set, V(L) at hb
  simpa using hb

theorem IsAttachmentWithEnds.leg_unique (S : Society α β)
    {P_set : Set (Graph α β)} (hdisj : S.IsDisjointOmegaPathSet P_set)
    {_P L₁ L₂ : Graph α β} {b : α}
    (hL₁ : L₁ ∈ P_set) (hb₁ : b ∈ V(L₁))
    (hL₂ : L₂ ∈ P_set) (hb₂ : b ∈ V(L₂)) :
    L₁ = L₂ := by
  by_contra hne
  exact disjoint_left.mp (hdisj.2 hL₁ hL₂ hne) hb₁ hb₂

theorem IsAttachmentWithEnds.inter_leg_eq_singleton (S : Society α β)
    {P_set : Set (Graph α β)} {P L : Graph α β} {b u : α}
    (h : S.IsAttachmentWithEnds P_set P b u) (hL : L ∈ P_set) (hbL : b ∈ V(L)) :
    V(P) ∩ V(L) = {b} := by
  apply Subset.antisymm
  · intro x ⟨hxP, hxL⟩
    have hxU : x ∈ V(S.transactionUnion P_set) := by
      change x ∈ ⋃ R ∈ P_set, V(R)
      exact mem_iUnion₂.mpr ⟨L, hL, hxL⟩
    have hx_inter : x ∈ V(P) ∩ V(S.transactionUnion P_set) := ⟨hxP, hxU⟩
    rwa [h.2.1] at hx_inter
  · rintro x rfl
    exact ⟨h.1.left_mem, hbL⟩

theorem IsAttachmentWithEnds.disjoint_of_ne_leg (S : Society α β)
    {P_set : Set (Graph α β)} (hdisj : S.IsDisjointOmegaPathSet P_set)
    {P L R : Graph α β} {b u : α}
    (h : S.IsAttachmentWithEnds P_set P b u)
    (hL : L ∈ P_set) (hbL : b ∈ V(L))
    (hR : R ∈ P_set) (hne : R ≠ L) :
    Disjoint V(P) V(R) := by
  rw [disjoint_left]
  intro x hxP hxR
  have hxU : x ∈ V(S.transactionUnion P_set) := by
    change x ∈ ⋃ M ∈ P_set, V(M)
    exact mem_iUnion₂.mpr ⟨R, hR, hxR⟩
  have hxb : x = b := by
    have hx_inter : x ∈ V(P) ∩ V(S.transactionUnion P_set) := ⟨hxP, hxU⟩
    rwa [h.2.1, mem_singleton_iff] at hx_inter
  subst hxb
  exact disjoint_left.mp (hdisj.2 hR hL hne) hxR hbL

/-- If `P` is an attachment to `P_set` with foot `b ∈ V(L)` (`L ∈ P_set`) and outer end `u`, and
`Q ≤ L` is a subpath of `L` from `b` to an end `e` of `L`, then `subgraphUnion S.G P Q` is an
`Ω`-path with ends `u` and `e`. -/
theorem IsAttachmentWithEnds.isOmegaPathWithEnds_subgraphUnion (S : Society α β)
    {P_set : Set (Graph α β)} {P L Q : Graph α β} {b u a₁ b₁ e : α}
    (h : S.IsAttachmentWithEnds P_set P b u)
    (hL : L ∈ P_set) (hbL : b ∈ V(L))
    (hL_ends : S.IsOmegaPathWithEnds L a₁ b₁)
    (hQ : IsGraphPathWithEnds L Q b e)
    (he : e = a₁ ∨ e = b₁) :
    S.IsOmegaPathWithEnds (subgraphUnion S.G P Q) u e := by
  have hinter : V(P) ∩ V(Q) = {b} := by
    apply Subset.antisymm
    · intro x ⟨hxP, hxQ⟩
      have hxL : x ∈ V(L) := hQ.le.vertexSet_mono hxQ
      have hx_inter : x ∈ V(P) ∩ V(L) := ⟨hxP, hxL⟩
      rwa [h.inter_leg_eq_singleton S hL hbL] at hx_inter
    · rintro x rfl
      exact ⟨h.1.left_mem, hQ.left_mem⟩
  have hpath : IsGraphPathWithEnds S.G (subgraphUnion S.G P Q) u e :=
    h.1.symm.subgraphUnion (hQ.mono hL_ends.1.le) hinter
  have he_mem : e ∈ S.transactionEnds P_set := by
    rcases he with rfl | rfl
    · exact hL_ends.mem_transactionEnds_left S hL
    · exact hL_ends.mem_transactionEnds_right S hL
  have he_bar : e ∈ S.Ω.bar := S.transactionEnds_subset_bar P_set he_mem
  have hue : u ≠ e := fun h_eq => h.end_not_mem_transactionEnds S (h_eq ▸ he_mem)
  exact ⟨hpath, hue, h.end_mem_bar S, he_bar⟩

theorem IsAttachmentWithEnds.disjoint_subgraphUnion_of_ne_leg (S : Society α β)
    {P_set : Set (Graph α β)} (hdisj : S.IsDisjointOmegaPathSet P_set)
    {P L Q R : Graph α β} {b u : α}
    (h : S.IsAttachmentWithEnds P_set P b u)
    (hL : L ∈ P_set) (hbL : b ∈ V(L)) (hQL : Q ≤ L)
    (hR : R ∈ P_set) (hne : R ≠ L) :
    Disjoint V(subgraphUnion S.G P Q) V(R) := by
  rw [vertexSet_subgraphUnion, disjoint_union_left]
  exact ⟨h.disjoint_of_ne_leg S hdisj hL hbL hR hne,
    (hdisj.2 hL hR hne.symm).mono_left hQL.vertexSet_mono⟩

theorem IsAttachmentWithEnds.subgraphUnion_not_mem_sdiff (S : Society α β)
    {P_set : Set (Graph α β)} (hdisj : S.IsDisjointOmegaPathSet P_set)
    {P L Q : Graph α β} {b u : α}
    (h : S.IsAttachmentWithEnds P_set P b u)
    (hL : L ∈ P_set) (hbL : b ∈ V(L)) :
    subgraphUnion S.G P Q ∉ P_set \ {L} := by
  rintro ⟨h_in, hne⟩
  have hd := h.disjoint_of_ne_leg S hdisj hL hbL h_in hne
  exact disjoint_left.mp hd h.1.left_mem (Or.inl h.1.left_mem)

theorem IsAttachmentWithEnds.isDisjointOmegaPathSet_switch (S : Society α β)
    {P_set : Set (Graph α β)} (hdisj : S.IsDisjointOmegaPathSet P_set)
    {P L Q : Graph α β} {b u a₁ b₁ e : α}
    (h : S.IsAttachmentWithEnds P_set P b u)
    (hL : L ∈ P_set) (hbL : b ∈ V(L))
    (hL_ends : S.IsOmegaPathWithEnds L a₁ b₁)
    (hQ : IsGraphPathWithEnds L Q b e)
    (he : e = a₁ ∨ e = b₁) :
    S.IsDisjointOmegaPathSet ((P_set \ {L}) ∪ {subgraphUnion S.G P Q}) := by
  let L' := subgraphUnion S.G P Q
  have hL'_ends : S.IsOmegaPathWithEnds L' u e :=
    h.isOmegaPathWithEnds_subgraphUnion S hL hbL hL_ends hQ he
  refine ⟨?_, ?_⟩
  · rintro R (hR | rfl)
    · exact hdisj.1 R hR.1
    · exact ⟨u, e, hL'_ends⟩
  · rintro R₁ (hR₁ | rfl) R₂ (hR₂ | rfl) hne
    · exact hdisj.2 hR₁.1 hR₂.1 hne
    · exact (h.disjoint_subgraphUnion_of_ne_leg S hdisj hL hbL hQ.le hR₁.1 hR₁.2).symm
    · exact h.disjoint_subgraphUnion_of_ne_leg S hdisj hL hbL hQ.le hR₂.1 hR₂.2
    · exact (hne rfl).elim

theorem IsAttachmentWithEnds.transactionEnds_switch (S : Society α β)
    {P_set : Set (Graph α β)} {P L Q : Graph α β} {b u a₁ b₁ e : α}
    (h : S.IsAttachmentWithEnds P_set P b u)
    (hL : L ∈ P_set) (hbL : b ∈ V(L))
    (hL_ends : S.IsOmegaPathWithEnds L a₁ b₁)
    (hQ : IsGraphPathWithEnds L Q b e)
    (he : e = a₁ ∨ e = b₁) :
    S.transactionEnds ((P_set \ {L}) ∪ {subgraphUnion S.G P Q}) =
      S.transactionEnds (P_set \ {L}) ∪ {u, e} := by
  let L' := subgraphUnion S.G P Q
  have hL'_ends : S.IsOmegaPathWithEnds L' u e :=
    h.isOmegaPathWithEnds_subgraphUnion S hL hbL hL_ends hQ he
  ext x
  simp only [transactionEnds, mem_ofPred_eq, mem_union, mem_singleton_iff, mem_insert_iff]
  constructor
  · rintro ⟨R, hR | rfl, y, hR_ends⟩
    · exact Or.inl ⟨R, hR, y, hR_ends⟩
    · rcases hL'_ends.ends_eq S hR_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  · rintro (⟨R, hR, y, hR_ends⟩ | rfl | rfl)
    · exact ⟨R, Or.inl hR, y, hR_ends⟩
    · exact ⟨L', Or.inr rfl, e, hL'_ends⟩
    · exact ⟨L', Or.inr rfl, u, hL'_ends.symm S⟩

theorem IsFenceFor.transactionEnds_eq_union (S : Society α β)
    {P_set : Set (Graph α β)} {A B : Set α}
    (_hfence : S.IsFenceFor P_set A B)
    {L : Graph α β} {a₁ b₁ : α} (hL : L ∈ P_set)
    (hL_ends : S.IsOmegaPathWithEnds L a₁ b₁) :
    S.transactionEnds P_set = S.transactionEnds (P_set \ {L}) ∪ {a₁, b₁} := by
  ext x
  simp only [transactionEnds, mem_ofPred_eq, mem_union, mem_sdiff, mem_singleton_iff,
    mem_insert_iff]
  constructor
  · rintro ⟨R, hR, y, hR_ends⟩
    by_cases hRL : R = L
    · subst hRL
      rcases hL_ends.ends_eq S hR_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · exact Or.inl ⟨R, ⟨hR, hRL⟩, y, hR_ends⟩
  · rintro (⟨R, ⟨hR, _⟩, y, hR_ends⟩ | rfl | rfl)
    · exact ⟨R, hR, y, hR_ends⟩
    · exact ⟨L, hL, b₁, hL_ends⟩
    · exact ⟨L, hL, a₁, hL_ends.symm S⟩

theorem IsFenceFor.not_mem_transactionEnds_diff_left (S : Society α β)
    {P_set : Set (Graph α β)} {A B : Set α}
    (hfence : S.IsFenceFor P_set A B)
    {L : Graph α β} {a₁ b₁ : α} (hL : L ∈ P_set)
    (hL_ends : S.IsOmegaPathWithEnds L a₁ b₁) :
    a₁ ∉ S.transactionEnds (P_set \ {L}) := by
  rintro ⟨R, ⟨hR, hne⟩, y, hR_ends⟩
  exact disjoint_left.mp (hfence.1.2 hL hR (Ne.symm hne)) hL_ends.1.left_mem hR_ends.1.left_mem

theorem IsFenceFor.not_mem_transactionEnds_diff_right (S : Society α β)
    {P_set : Set (Graph α β)} {A B : Set α}
    (hfence : S.IsFenceFor P_set A B)
    {L : Graph α β} {a₁ b₁ : α} (hL : L ∈ P_set)
    (hL_ends : S.IsOmegaPathWithEnds L a₁ b₁) :
    b₁ ∉ S.transactionEnds (P_set \ {L}) := by
  rintro ⟨R, ⟨hR, hne⟩, y, hR_ends⟩
  exact disjoint_left.mp (hfence.1.2 hL hR (Ne.symm hne)) hL_ends.1.right_mem hR_ends.1.left_mem

/-! ## Interval-fence helpers for switches in (3.2) -/

/-- If `W ⊆ S.Ω.bar` is partitioned into `A ∩ W` and `B ∩ W` by a fence `(A, B)` of `S.Ω`, and
`x₀ ∈ A ∩ W` satisfies `Disjoint (S.Ω.interval b' x₀) W` for some `b' ∈ B ∩ W`, then the interval
fence `(S.Ω.interval x₀ b, {b, x₀} ∪ S.Ω.interval b x₀)` (where `Disjoint (S.Ω.interval a' b) W`)
separates `(A ∩ W) \ {x₀}` from `(B ∩ W) ∪ {x₀}`. -/
theorem exists_fence_separating_of_disjoint_BA {Ω : CyclicPerm α} {A B W : Set α}
    (hfence : Ω.IsFence A B) (hW : W ⊆ Ω.bar)
    {a' b b' x₀ : α} (ha' : a' ∈ A ∩ W) (hb : b ∈ B ∩ W)
    (hb' : b' ∈ B ∩ W) (hx₀ : x₀ ∈ A ∩ W)
    (hdisj_ab : Disjoint (Ω.interval a' b) W)
    (hdisj_bx : Disjoint (Ω.interval b' x₀) W) :
    ∃ A' B' : Set α, Ω.IsFence A' B' ∧
      (A ∩ W) \ {x₀} ⊆ A' ∧ (B ∩ W) ∪ {x₀} ⊆ B' := by
  have hb_bar : b ∈ Ω.bar := hW hb.2
  have hx₀_bar : x₀ ∈ Ω.bar := hW hx₀.2
  have hbx₀ : b ≠ x₀ := fun h => disjoint_left.mp hfence.2.2.1 hx₀.1 (h ▸ hb.1)
  refine ⟨Ω.interval x₀ b, {b, x₀} ∪ Ω.interval b x₀,
    (Ω.isFence_interval_compl hb_bar hx₀_bar hbx₀).symm, ?_, ?_⟩
  · intro x ⟨hxA, hx_ne⟩
    exact Ω.mem_interval_rotate_left
      (Ω.mem_interval_of_mem_B_of_disjoint_AB hfence.symm hW hb' hx₀ hdisj_bx hb hxA hx_ne).1
  · rintro y (hyB | rfl)
    · by_cases hyb : y = b
      · exact Or.inl (Or.inl hyb)
      · exact Or.inr (Ω.mem_interval_rotate_left
          (Ω.mem_interval_of_mem_B_of_disjoint_AB hfence hW ha' hb hdisj_ab hx₀ hyB hyb).1)
    · exact Or.inl (Or.inr rfl)

/-- Dual version: if `x₀ ∈ A ∩ W` satisfies `Disjoint (Ω.interval x₀ b) W` for some `b ∈ B ∩ W`,
then the interval fence `(Ω.interval b' x₀, {x₀, b'} ∪ Ω.interval x₀ b')` separates
`(A ∩ W) \ {x₀}` from `(B ∩ W) ∪ {x₀}`. -/
theorem exists_fence_separating_of_disjoint_AB {Ω : CyclicPerm α} {A B W : Set α}
    (hfence : Ω.IsFence A B) (hW : W ⊆ Ω.bar)
    {a b b' x₀ : α} (ha : a ∈ A ∩ W) (hb : b ∈ B ∩ W)
    (hb' : b' ∈ B ∩ W) (hx₀ : x₀ ∈ A ∩ W)
    (hdisj_ba : Disjoint (Ω.interval b' a) W)
    (hdisj_xb : Disjoint (Ω.interval x₀ b) W) :
    ∃ A' B' : Set α, Ω.IsFence A' B' ∧
      (A ∩ W) \ {x₀} ⊆ A' ∧ (B ∩ W) ∪ {x₀} ⊆ B' := by
  have hb'_bar : b' ∈ Ω.bar := hW hb'.2
  have hx₀_bar : x₀ ∈ Ω.bar := hW hx₀.2
  have hx₀b' : x₀ ≠ b' := fun h => disjoint_left.mp hfence.2.2.1 hx₀.1 (h ▸ hb'.1)
  refine ⟨Ω.interval b' x₀, {x₀, b'} ∪ Ω.interval x₀ b',
    (Ω.isFence_interval_compl hx₀_bar hb'_bar hx₀b').symm, ?_, ?_⟩
  · intro x ⟨hxA, hx_ne⟩
    exact Ω.mem_interval_rotate_right
      (Ω.mem_interval_of_mem_A_of_disjoint_AB hfence hW hx₀ hb hdisj_xb hxA hx_ne hb').1
  · rintro y (hyB | rfl)
    · by_cases hyb' : y = b'
      · exact Or.inl (Or.inr hyb')
      · exact Or.inr (Ω.mem_interval_rotate_right
          (Ω.mem_interval_of_mem_A_of_disjoint_AB hfence.symm hW hb' ha hdisj_ba hyB hyb' hx₀).1)
    · exact Or.inl (Or.inl rfl)

/-! ## Proof of (3.2) -/

/-- **Graph Minors IX, (3.2), Claim (1)** (page 47):
"Either $u^- = b_1$, or $a_1 = a'$ and there exists $P_2 \in \mathscr{P} - \{P_1\}$ with ends
$a_1^+, a_1^-$. In either case $a_1^- \ne u$."

Expressed in terms of intervals of `S.Ω` and `W = V(P_set) ∪ {u}`, when `u ∈ A` and `(u, a₁, b₁)`
is clockwise (`a₁ ∈ S.Ω.interval u b₁`):
either `Disjoint (S.Ω.interval b₁ u) W`, or `Disjoint (S.Ω.interval a₁ b) W` and there exists
`P₂ ∈ P_set \ {P₁}` peripheral in `P_set \ {P₁}` with ends `a₂ ∈ A`, `b₂ ∈ B` such that
`a₁ ∈ S.Ω.interval a₂ b₂` and `Disjoint (S.Ω.interval a₂ b₂) (W \ {a₁})`. In either case
`¬ Disjoint (S.Ω.interval u a₁) W`. -/
theorem lemma_3_2_claim_1 (S : Society α β)
    {P_set : Set (Graph α β)} {A B : Set α}
    (hcrooked : S.IsCrookedTransaction P_set)
    (hfence : S.IsFenceFor P_set A B)
    {P P₁ Q_b : Graph α β} {v u a₁ b₁ : α}
    (hatt : S.IsAttachmentWithEnds P_set P v u)
    (hnot_exch : ¬ S.IsExchangeableAttachment P_set P)
    (hP₁ : P₁ ∈ P_set) (hvP₁ : v ∈ V(P₁))
    (hP₁_ends : S.IsOmegaPathWithEnds P₁ a₁ b₁)
    (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ B) (huA : u ∈ A)
    (hcw : a₁ ∈ S.Ω.interval u b₁)
    (hQ_b : IsGraphPathWithEnds P₁ Q_b v b₁) :
    let W := S.transactionEnds P_set ∪ {u}
    (Disjoint (S.Ω.interval b₁ u) W ∨
      ∃ P₂ ∈ P_set \ {P₁}, S.IsPeripheralIn (P_set \ {P₁}) P₂ ∧
        ∃ a₂ ∈ A, ∃ b₂ ∈ B, S.IsOmegaPathWithEnds P₂ a₂ b₂ ∧
          a₁ ∈ S.Ω.interval a₂ b₂ ∧ Disjoint (S.Ω.interval a₂ b₂) (W \ {a₁})) ∧
    ¬ Disjoint (S.Ω.interval u a₁) W := by
  intro W
  let T_sw := subgraphUnion S.G P Q_b
  let T_set := (P_set \ {P₁}) ∪ {T_sw}
  have hT_ends : S.IsOmegaPathWithEnds T_sw u b₁ :=
    hatt.isOmegaPathWithEnds_subgraphUnion S hP₁ hvP₁ hP₁_ends hQ_b (Or.inr rfl)
  have hT_disj : S.IsDisjointOmegaPathSet T_set :=
    hatt.isDisjointOmegaPathSet_switch S hfence.1 hP₁ hvP₁ hP₁_ends hQ_b (Or.inr rfl)
  have hT_fence : S.IsFenceFor T_set A B := by
    refine ⟨hT_disj, hfence.2.1, ?_⟩
    rintro R (hR | rfl)
    · exact hfence.2.2 R hR.1
    · exact ⟨u, huA, b₁, hb₁, hT_ends⟩
  have hT_not_crooked : ¬ S.IsCrookedTransaction T_set := fun hcr =>
    hnot_exch ⟨⟨v, u, hatt⟩, P₁, T_sw,
      ⟨hP₁, v, u, a₁, b₁, hatt, hvP₁, hP₁_ends, Q_b, Or.inr hQ_b, rfl⟩, hcr⟩
  have hW_eq : S.transactionEnds T_set = W \ {a₁} := by
    rw [hatt.transactionEnds_switch S hP₁ hvP₁ hP₁_ends hQ_b (Or.inr rfl)]
    have hP_eq := hfence.transactionEnds_eq_union S hP₁ hP₁_ends
    have ha₁_not_W' := hfence.not_mem_transactionEnds_diff_left S hP₁ hP₁_ends
    have hua₁ : u ≠ a₁ := fun h => (hatt.end_not_mem_transactionEnds S)
      (h ▸ hP₁_ends.mem_transactionEnds_left S hP₁)
    have ha₁b₁ : a₁ ≠ b₁ := hP₁_ends.2.1
    ext x
    simp only [W, hP_eq, mem_union, mem_insert_iff, mem_singleton_iff, mem_sdiff]
    constructor
    · rintro (hx | rfl | rfl)
      · exact ⟨Or.inl (Or.inl hx), fun h => ha₁_not_W' (h ▸ hx)⟩
      · exact ⟨Or.inr rfl, hua₁⟩
      · exact ⟨Or.inl (Or.inr (Or.inr rfl)), ha₁b₁.symm⟩
    · rintro ⟨(hx | rfl | rfl) | rfl, hne⟩
      · exact Or.inl hx
      · exact (hne rfl).elim
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl rfl)
  have hPW_eq : S.transactionEnds P_set = W \ {u} := by
    ext x
    simp only [W, mem_union, mem_singleton_iff, mem_sdiff]
    exact ⟨fun hx => ⟨Or.inl hx, fun h => (hatt.end_not_mem_transactionEnds S) (h ▸ hx)⟩,
      fun ⟨hx, hne⟩ => hx.resolve_right hne⟩
  -- Since `T_set` is a transaction and not crooked, it has a peripheral member `M`.
  have hex_per : ∃ M ∈ T_set, S.IsPeripheralIn T_set M := by
    by_contra! hno
    exact hT_not_crooked ⟨⟨A, B, hT_fence⟩, hno⟩
  -- First note that `S.Ω.interval u a₁` cannot be disjoint from `W` if `S.Ω.interval b₁ u` is,
  -- nor if some `a₂ ∈ W` lies in `S.Ω.interval u a₁`.
  have hub₁_split : S.Ω.interval u b₁ = S.Ω.interval u a₁ ∪ {a₁} ∪ S.Ω.interval a₁ b₁ :=
    S.Ω.interval_eq_union_of_mem hcw
  have hb₁a₁_split : S.Ω.interval b₁ a₁ = S.Ω.interval b₁ u ∪ {u} ∪ S.Ω.interval u a₁ :=
    S.Ω.interval_eq_union_of_mem (S.Ω.mem_interval_rotate_right hcw)
  rcases hex_per with ⟨M, hM_in, hM_per⟩
  rcases hM_in with hM_diff | rfl
  · -- `M = P₂ ∈ P_set \ {P₁}` is peripheral in `T_set`.
    obtain ⟨a₂, ha₂, b₂, hb₂, hP₂_ends⟩ := hfence.2.2 M hM_diff.1
    have hM_per' := (hP₂_ends.isPeripheralIn_iff S (Or.inl hM_diff)).mp hM_per
    rw [hW_eq] at hM_per'
    have hW'_sub : S.transactionEnds (P_set \ {P₁}) ⊆ W \ {a₁} := by
      rw [← hW_eq, hatt.transactionEnds_switch S hP₁ hvP₁ hP₁_ends hQ_b (Or.inr rfl)]
      exact subset_union_left
    have hM_per_diff : S.IsPeripheralIn (P_set \ {P₁}) M := by
      refine ⟨hM_diff, a₂, b₂, hP₂_ends, ?_⟩
      rcases hM_per' with hd | hd
      · exact Or.inl (hd.mono_right hW'_sub)
      · exact Or.inr (hd.mono_right hW'_sub)
    -- `M` is not peripheral in `P_set`, so its `W \ {a₁}`-disjoint interval must contain `a₁`.
    have hnot_per_P : ¬ S.IsPeripheralIn P_set M := hcrooked.2 M hM_diff.1
    rcases hM_per' with hd_ab | hd_ba
    · have ha₁_in : a₁ ∈ S.Ω.interval a₂ b₂ := by
        by_contra ha₁_not
        apply hnot_per_P
        refine ⟨hM_diff.1, a₂, b₂, hP₂_ends, Or.inl ?_⟩
        rw [hPW_eq, disjoint_left]
        intro z hz ⟨hzW, _⟩
        have hza₁ : z ≠ a₁ := fun h => ha₁_not (h ▸ hz)
        exact disjoint_left.mp hd_ab hz ⟨hzW, hza₁⟩
      have ha₂_in_ua₁ : a₂ ∈ S.Ω.interval u a₁ := by
        have hu_not : u ∉ S.Ω.interval a₂ b₂ :=
          fun hu_in => disjoint_left.mp hd_ab hu_in
            ⟨Or.inr rfl, fun h => (hatt.end_not_mem_transactionEnds S)
              (h ▸ hP₁_ends.mem_transactionEnds_left S hP₁)⟩
        have hua₂ : u ≠ a₂ := fun h => (hatt.end_not_mem_transactionEnds S)
          (h ▸ hP₂_ends.mem_transactionEnds_left S hM_diff.1)
        have hub₂ : u ≠ b₂ := fun h => (hatt.end_not_mem_transactionEnds S)
          (h ▸ hP₂_ends.mem_transactionEnds_right S hM_diff.1)
        have hu_b₂a₂ : u ∈ S.Ω.interval b₂ a₂ :=
          (S.Ω.mem_interval_or_interval_swap hP₂_ends.2.2.1 hP₂_ends.2.2.2 (hatt.end_mem_bar S)
            hP₂_ends.2.1 hua₂ hub₂).resolve_left hu_not
        have hcw4 : S.Ω.IsClockwise4 a₂ a₁ b₂ u := S.Ω.isClockwise4_iff_interval.mpr ⟨ha₁_in,
          hu_b₂a₂⟩
        exact (S.Ω.isClockwise4_iff_interval.mp (S.Ω.isClockwise4_rotate hcw4)).2
      have hnot_ua₁ : ¬ Disjoint (S.Ω.interval u a₁) W := fun hd =>
        disjoint_left.mp hd ha₂_in_ua₁ (Or.inl (hP₂_ends.mem_transactionEnds_left S hM_diff.1))
      exact ⟨Or.inr ⟨M, hM_diff, hM_per_diff, a₂, ha₂, b₂, hb₂, hP₂_ends, ha₁_in, hd_ab⟩, hnot_ua₁⟩
    · -- Can `a₁ ∈ S.Ω.interval b₂ a₂` with `Disjoint (S.Ω.interval b₂ a₂) (W \ {a₁})`?
      -- No: then `u, b₁ ∉ S.Ω.interval b₂ a₂`, so `b₂, a₂` would separate `a₁` from `u, b₁`,
      -- forcing `a₁ ∈ S.Ω.interval b₁ u`, contradicting `a₁ ∈ S.Ω.interval u b₁`!
      exfalso
      have ha₁_in : a₁ ∈ S.Ω.interval b₂ a₂ := by
        by_contra ha₁_not
        apply hnot_per_P
        refine ⟨hM_diff.1, a₂, b₂, hP₂_ends, Or.inr ?_⟩
        rw [hPW_eq, disjoint_left]
        intro z hz ⟨hzW, _⟩
        have hza₁ : z ≠ a₁ := fun h => ha₁_not (h ▸ hz)
        exact disjoint_left.mp hd_ba hz ⟨hzW, hza₁⟩
      have ha₁_b₂a₁_sub : S.Ω.interval b₂ a₁ ⊆ S.Ω.interval b₂ a₂ :=
        S.Ω.interval_subset_interval_left ha₁_in
      have hd_b₂a₁ : Disjoint (S.Ω.interval b₂ a₁) W := by
        rw [disjoint_left]
        intro z hz hzW
        have hza₁ : z ≠ a₁ := fun h => S.Ω.not_mem_interval_right b₂ a₁ (h ▸ hz)
        exact disjoint_left.mp hd_ba (ha₁_b₂a₁_sub hz) ⟨hzW, hza₁⟩
      have hW_bar : W ⊆ S.Ω.bar := union_subset (S.transactionEnds_subset_bar P_set)
        (singleton_subset_iff.mpr (hatt.end_mem_bar S))
      have hb₂W : b₂ ∈ B ∩ W := ⟨hb₂, Or.inl (hP₂_ends.mem_transactionEnds_right S hM_diff.1)⟩
      have ha₁W : a₁ ∈ A ∩ W := ⟨ha₁, Or.inl (hP₁_ends.mem_transactionEnds_left S hP₁)⟩
      have hb₁W : b₁ ∈ B ∩ W := ⟨hb₁, Or.inl (hP₁_ends.mem_transactionEnds_right S hP₁)⟩
      have huW : u ∈ A ∩ W := ⟨huA, Or.inr rfl⟩
      have hua₁ : u ≠ a₁ := fun h => (hatt.end_not_mem_transactionEnds S)
        (h ▸ hP₁_ends.mem_transactionEnds_left S hP₁)
      have ha₁_b₁u : a₁ ∈ S.Ω.interval b₁ u :=
        (S.Ω.mem_interval_of_mem_B_of_disjoint_AB hfence.2.1.symm hW_bar hb₂W ha₁W hd_b₂a₁
          hb₁W huW hua₁).1
      exact disjoint_left.mp (S.Ω.disjoint_interval_swap u b₁) hcw ha₁_b₁u
  · -- `M = T_sw` is peripheral in `T_set`.
    have hT_per := (hT_ends.isPeripheralIn_iff S (Or.inr rfl)).mp hM_per
    rw [hW_eq] at hT_per
    rcases hT_per with hd_ub₁ | hd_b₁u
    · -- `Disjoint (S.Ω.interval u b₁) (W \ {a₁})` implies `Disjoint (S.Ω.interval a₁ b₁) (W \
      -- {u})`,
      -- so `P₁` is peripheral in `P_set`, contradiction.
      exfalso
      have hd_a₁b₁ : Disjoint (S.Ω.interval a₁ b₁) (S.transactionEnds P_set) := by
        rw [hPW_eq, disjoint_left]
        intro z hz ⟨hzW, _⟩
        have hza₁ : z ≠ a₁ := fun h => S.Ω.not_mem_interval_left a₁ b₁ (h ▸ hz)
        have hz_ub₁ : z ∈ S.Ω.interval u b₁ := S.Ω.interval_subset_interval_right hcw hz
        exact disjoint_left.mp hd_ub₁ hz_ub₁ ⟨hzW, hza₁⟩
      exact hcrooked.2 P₁ hP₁ ⟨hP₁, a₁, b₁, hP₁_ends, Or.inl hd_a₁b₁⟩
    · -- `Disjoint (S.Ω.interval b₁ u) (W \ {a₁})`: since `a₁ ∉ S.Ω.interval b₁ u`, this gives
      -- `Disjoint (S.Ω.interval b₁ u) W`.
      have hd_b₁u_W : Disjoint (S.Ω.interval b₁ u) W := by
        rw [disjoint_left]
        intro z hz hzW
        have hza₁ : z ≠ a₁ := fun h =>
          disjoint_left.mp (S.Ω.disjoint_interval_swap u b₁) hcw (h ▸ hz)
        exact disjoint_left.mp hd_b₁u hz ⟨hzW, hza₁⟩
      have hnot_ua₁ : ¬ Disjoint (S.Ω.interval u a₁) W := by
        intro hd_ua₁
        have hd_b₁a₁ : Disjoint (S.Ω.interval b₁ a₁) (S.transactionEnds P_set) := by
          rw [hPW_eq, hb₁a₁_split, disjoint_left]
          rintro z ((hz | rfl) | hz) ⟨hzW, hzu⟩
          · exact disjoint_left.mp hd_b₁u_W hz hzW
          · exact hzu rfl
          · exact disjoint_left.mp hd_ua₁ hz hzW
        exact hcrooked.2 P₁ hP₁ ⟨hP₁, a₁, b₁, hP₁_ends, Or.inr hd_b₁a₁⟩
      exact ⟨Or.inl hd_b₁u_W, hnot_ua₁⟩

/-- **Graph Minors IX, (3.2), Claim (2)** (page 48):
"Either `a ≠ u` or `b = b₁`."

Expressed in terms of intervals of `S.Ω` and `W = V(P_set) ∪ {u}`: if `Disjoint (S.Ω.interval b' u)
W`
for some `b' ∈ B ∩ W` (`a = u`), then `Disjoint (S.Ω.interval a' b₁) W` (`b = b₁`), which is
impossible since `|B ∩ W| ≥ 2`. -/
theorem lemma_3_2_claim_2 (S : Society α β)
    {P_set : Set (Graph α β)} {A B : Set α}
    (hcrooked : S.IsCrookedTransaction P_set)
    (hfence : S.IsFenceFor P_set A B)
    {P P₁ Q_a : Graph α β} {v u a₁ b₁ : α}
    (hatt : S.IsAttachmentWithEnds P_set P v u)
    (hnot_exch : ¬ S.IsExchangeableAttachment P_set P)
    (hP₁ : P₁ ∈ P_set) (hvP₁ : v ∈ V(P₁))
    (hP₁_ends : S.IsOmegaPathWithEnds P₁ a₁ b₁)
    (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ B) (huA : u ∈ A)
    (hcw : a₁ ∈ S.Ω.interval u b₁)
    (hQ_a : IsGraphPathWithEnds P₁ Q_a v a₁) :
    let W := S.transactionEnds P_set ∪ {u}
    ¬ Disjoint (S.Ω.interval b₁ u) W := by
  intro W hd_b₁u
  let S_sw := subgraphUnion S.G P Q_a
  let S_set := (P_set \ {P₁}) ∪ {S_sw}
  have hS_ends : S.IsOmegaPathWithEnds S_sw u a₁ :=
    hatt.isOmegaPathWithEnds_subgraphUnion S hP₁ hvP₁ hP₁_ends hQ_a (Or.inl rfl)
  have hS_disj : S.IsDisjointOmegaPathSet S_set :=
    hatt.isDisjointOmegaPathSet_switch S hfence.1 hP₁ hvP₁ hP₁_ends hQ_a (Or.inl rfl)
  have hW_bar : W ⊆ S.Ω.bar := union_subset (S.transactionEnds_subset_bar P_set)
    (singleton_subset_iff.mpr (hatt.end_mem_bar S))
  have hW_AB : W ⊆ A ∪ B := hfence.2.1.2.2.2.1 ▸ hW_bar
  have ha₁W : a₁ ∈ A ∩ W := ⟨ha₁, Or.inl (hP₁_ends.mem_transactionEnds_left S hP₁)⟩
  have hb₁W : b₁ ∈ B ∩ W := ⟨hb₁, Or.inl (hP₁_ends.mem_transactionEnds_right S hP₁)⟩
  have huW : u ∈ A ∩ W := ⟨huA, Or.inr rfl⟩
  obtain ⟨a', ha'W, b, hbW, hdisj_a'b⟩ :=
    S.Ω.exists_empty_interval_AB_of_subset_union hW_bar hW_AB ⟨a₁, ha₁W⟩ ⟨b₁, hb₁W⟩
  obtain ⟨A', B', hfence_A'B', hsubA', hsubB'⟩ :=
    exists_fence_separating_of_disjoint_BA hfence.2.1 hW_bar ha'W hbW hb₁W huW hdisj_a'b hd_b₁u
  have hS_fence : S.IsFenceFor S_set A' B' := by
    refine ⟨hS_disj, hfence_A'B', ?_⟩
    rintro R (hR | rfl)
    · obtain ⟨a_R, ha_R, b_R, hb_R, hR_ends⟩ := hfence.2.2 R hR.1
      have ha_R_W : a_R ∈ A ∩ W := ⟨ha_R, Or.inl (hR_ends.mem_transactionEnds_left S hR.1)⟩
      have hb_R_W : b_R ∈ B ∩ W := ⟨hb_R, Or.inl (hR_ends.mem_transactionEnds_right S hR.1)⟩
      have ha_R_ne_u : a_R ≠ u :=
        fun h => (hatt.end_not_mem_transactionEnds S) (h ▸ hR_ends.mem_transactionEnds_left S hR.1)
      exact ⟨a_R, hsubA' ⟨ha_R_W, ha_R_ne_u⟩, b_R, hsubB' (Or.inl hb_R_W), hR_ends⟩
    · have ha₁_ne_u : a₁ ≠ u :=
        fun h => (hatt.end_not_mem_transactionEnds S) (h ▸ hP₁_ends.mem_transactionEnds_left S hP₁)
      exact ⟨a₁, hsubA' ⟨ha₁W, ha₁_ne_u⟩, u, hsubB' (Or.inr rfl), hS_ends.symm S⟩
  have hS_not_crooked : ¬ S.IsCrookedTransaction S_set := fun hcr =>
    hnot_exch ⟨⟨v, u, hatt⟩, P₁, S_sw,
      ⟨hP₁, v, u, a₁, b₁, hatt, hvP₁, hP₁_ends, Q_a, Or.inl hQ_a, rfl⟩, hcr⟩
  -- Since `P_set` is crooked and `P₁ ∈ P_set`, there is at least one other member `P₀ ∈ P_set \
  -- {P₁}`.
  obtain ⟨P_x, hPx_in, P_y, hPy_in, hPxy, _⟩ := S.exists_crooked_pair_of_nonempty hcrooked ⟨P₁, hP₁⟩
  have hex_other : ∃ P₀ ∈ P_set \ {P₁}, True := by
    by_cases h1 : P_x = P₁
    · exact ⟨P_y, ⟨hPy_in, h1 ▸ hPxy.symm⟩, trivial⟩
    · exact ⟨P_x, ⟨hPx_in, h1⟩, trivial⟩
  obtain ⟨P₀, hP₀_diff, _⟩ := hex_other
  obtain ⟨a₀, ha₀, b₀, hb₀, hP₀_ends⟩ := hfence.2.2 P₀ hP₀_diff.1
  have hb₀W : b₀ ∈ B ∩ W := ⟨hb₀, Or.inl (hP₀_ends.mem_transactionEnds_right S hP₀_diff.1)⟩
  have hb₀_ne_b₁ : b₀ ≠ b₁ := fun h =>
    disjoint_left.mp (hfence.1.2 hP₀_diff.1 hP₁ hP₀_diff.2)
      hP₀_ends.1.right_mem (h ▸ hP₁_ends.1.right_mem)
  -- Notice `b ≠ b₁`: if `b = b₁`, then `Disjoint (interval a' b₁) W` and `Disjoint (interval b₁ u)
  -- W`
  -- give `b₁ ∈ interval a' b₀` and `b₁ ∈ interval b₀ a'`, contradiction.
  have hb_ne_b₁ : b ≠ b₁ := by
    intro h_eq
    have h1 : b₁ ∈ S.Ω.interval a' b₀ :=
      (S.Ω.mem_interval_of_mem_B_of_disjoint_AB hfence.2.1 hW_bar ha'W hb₁W (h_eq ▸ hdisj_a'b)
        ha'W hb₀W hb₀_ne_b₁).1
    have h2 : b₁ ∈ S.Ω.interval b₀ a' :=
      (S.Ω.mem_interval_of_mem_A_of_disjoint_AB hfence.2.1.symm hW_bar hb₁W huW hd_b₁u
        hb₀W hb₀_ne_b₁ ha'W).1
    exact disjoint_left.mp (S.Ω.disjoint_interval_swap a' b₀) h1 h2
  -- Yet `S_set` is not crooked, so some member `M ∈ S_set` is peripheral in `S_set`.
  have hex_per : ∃ M ∈ S_set, S.IsPeripheralIn S_set M := by
    by_contra! hno
    exact hS_not_crooked ⟨⟨A', B', hS_fence⟩, hno⟩
  have hSW_eq : S.transactionEnds S_set = W \ {b₁} := by
    rw [hatt.transactionEnds_switch S hP₁ hvP₁ hP₁_ends hQ_a (Or.inl rfl)]
    have hP_eq := hfence.transactionEnds_eq_union S hP₁ hP₁_ends
    have hb₁_not_W' := hfence.not_mem_transactionEnds_diff_right S hP₁ hP₁_ends
    have hub₁ : u ≠ b₁ := fun h => (hatt.end_not_mem_transactionEnds S)
      (h ▸ hP₁_ends.mem_transactionEnds_right S hP₁)
    have ha₁b₁ : a₁ ≠ b₁ := hP₁_ends.2.1
    ext x
    simp only [W, hP_eq, mem_union, mem_insert_iff, mem_singleton_iff, mem_sdiff]
    constructor
    · rintro (hx | rfl | rfl)
      · exact ⟨Or.inl (Or.inl hx), fun h => hb₁_not_W' (h ▸ hx)⟩
      · exact ⟨Or.inr rfl, hub₁⟩
      · exact ⟨Or.inl (Or.inr (Or.inl rfl)), ha₁b₁⟩
    · rintro ⟨(hx | rfl | rfl) | rfl, hne⟩
      · exact Or.inl hx
      · exact Or.inr (Or.inr rfl)
      · exact (hne rfl).elim
      · exact Or.inr (Or.inl rfl)
  have hPW_eq : S.transactionEnds P_set = W \ {u} := by
    ext x
    simp only [W, mem_union, mem_singleton_iff, mem_sdiff]
    exact ⟨fun hx => ⟨Or.inl hx, fun h => (hatt.end_not_mem_transactionEnds S) (h ▸ hx)⟩,
      fun ⟨hx, hne⟩ => hx.resolve_right hne⟩
  rcases hex_per with ⟨M, hM_in, hM_per⟩
  rcases hM_in with hM_diff | rfl
  · -- `M = P₃ ∈ P_set \ {P₁}` is peripheral in `S_set`.
    obtain ⟨a₃, ha₃, b₃, hb₃, hP₃_ends⟩ := hfence.2.2 M hM_diff.1
    have hM_per' := (hP₃_ends.isPeripheralIn_iff S (Or.inl hM_diff)).mp hM_per
    rw [hSW_eq] at hM_per'
    have hnot_per_P : ¬ S.IsPeripheralIn P_set M := hcrooked.2 M hM_diff.1
    have ha₃W : a₃ ∈ A ∩ W := ⟨ha₃, Or.inl (hP₃_ends.mem_transactionEnds_left S hM_diff.1)⟩
    have hb₃W : b₃ ∈ B ∩ W := ⟨hb₃, Or.inl (hP₃_ends.mem_transactionEnds_right S hM_diff.1)⟩
    rcases hM_per' with hd_ab | hd_ba
    · have hb₁_in : b₁ ∈ S.Ω.interval a₃ b₃ := by
        by_contra hb₁_not
        apply hnot_per_P
        refine ⟨hM_diff.1, a₃, b₃, hP₃_ends, Or.inl ?_⟩
        rw [hPW_eq, disjoint_left]
        intro z hz ⟨hzW, _⟩
        have hzb₁ : z ≠ b₁ := fun h => hb₁_not (h ▸ hz)
        exact disjoint_left.mp hd_ab hz ⟨hzW, hzb₁⟩
      have hd_a₃b₁ : Disjoint (S.Ω.interval a₃ b₁) W := by
        rw [disjoint_left]
        intro z hz hzW
        have hzb₁ : z ≠ b₁ := fun h => S.Ω.not_mem_interval_right a₃ b₁ (h ▸ hz)
        exact disjoint_left.mp hd_ab (S.Ω.interval_subset_interval_left hb₁_in hz) ⟨hzW, hzb₁⟩
      have hb_eq : b = b₁ :=
        (S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1 hW_bar ha'W hbW ha₃W hb₁W
          hdisj_a'b hd_a₃b₁).2
      exact hb_ne_b₁ hb_eq
    · have hb₁_in : b₁ ∈ S.Ω.interval b₃ a₃ := by
        by_contra hb₁_not
        apply hnot_per_P
        refine ⟨hM_diff.1, a₃, b₃, hP₃_ends, Or.inr ?_⟩
        rw [hPW_eq, disjoint_left]
        intro z hz ⟨hzW, _⟩
        have hzb₁ : z ≠ b₁ := fun h => hb₁_not (h ▸ hz)
        exact disjoint_left.mp hd_ba hz ⟨hzW, hzb₁⟩
      have hd_b₁a₃ : Disjoint (S.Ω.interval b₁ a₃) W := by
        rw [disjoint_left]
        intro z hz hzW
        have hzb₁ : z ≠ b₁ := fun h => S.Ω.not_mem_interval_left b₁ a₃ (h ▸ hz)
        exact disjoint_left.mp hd_ba (S.Ω.interval_subset_interval_right hb₁_in hz) ⟨hzW, hzb₁⟩
      have hu_eq : u = a₃ :=
        (S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1.symm hW_bar hb₁W huW hb₁W ha₃W
          hd_b₁u hd_b₁a₃).2
      exact (hatt.end_not_mem_transactionEnds S) (hu_eq ▸ hP₃_ends.mem_transactionEnds_left S
        hM_diff.1)
  · -- `M = S_sw` is peripheral in `S_set`.
    have hS_per := (hS_ends.isPeripheralIn_iff S (Or.inr rfl)).mp hM_per
    rw [hSW_eq] at hS_per
    rcases hS_per with hd_ua₁ | hd_a₁u
    · -- `Disjoint (S.Ω.interval u a₁) (W \ {b₁})`: since `b₁ ∉ S.Ω.interval u a₁`, this gives
      -- `Disjoint (S.Ω.interval u a₁) W`, contradicting Claim (1).
      have hd_ua₁_W : Disjoint (S.Ω.interval u a₁) W := by
        rw [disjoint_left]
        intro z hz hzW
        have hzb₁ : z ≠ b₁ := fun h => by
          have hb₁_a₁u : b₁ ∈ S.Ω.interval a₁ u := S.Ω.mem_interval_rotate_left hcw
          exact disjoint_left.mp (S.Ω.disjoint_interval_swap u a₁) hz (h ▸ hb₁_a₁u)
        exact disjoint_left.mp hd_ua₁ hz ⟨hzW, hzb₁⟩
      have hb₁a₁_split : S.Ω.interval b₁ a₁ = S.Ω.interval b₁ u ∪ {u} ∪ S.Ω.interval u a₁ :=
        S.Ω.interval_eq_union_of_mem (S.Ω.mem_interval_rotate_right hcw)
      have hd_b₁a₁ : Disjoint (S.Ω.interval b₁ a₁) (S.transactionEnds P_set) := by
        rw [hPW_eq, hb₁a₁_split, disjoint_left]
        rintro z ((hz | rfl) | hz) ⟨hzW, hzu⟩
        · exact disjoint_left.mp hd_b₁u hz hzW
        · exact hzu rfl
        · exact disjoint_left.mp hd_ua₁_W hz hzW
      exact hcrooked.2 P₁ hP₁ ⟨hP₁, a₁, b₁, hP₁_ends, Or.inr hd_b₁a₁⟩
    · -- `Disjoint (S.Ω.interval a₁ u) (W \ {b₁})`: yet `b₀ ∈ B ∩ W \ {b₁}` lies in `S.Ω.interval a₁
      -- u`!
      have hb₁_b₀a₁ : b₁ ∈ S.Ω.interval b₀ a₁ :=
        (S.Ω.mem_interval_of_mem_A_of_disjoint_AB hfence.2.1.symm hW_bar hb₁W huW hd_b₁u
          hb₀W hb₀_ne_b₁ ha₁W).1
      have hb₀_a₁b₁ : b₀ ∈ S.Ω.interval a₁ b₁ := S.Ω.mem_interval_rotate_right hb₁_b₀a₁
      have hb₁_a₁u : b₁ ∈ S.Ω.interval a₁ u := S.Ω.mem_interval_rotate_left hcw
      have hb₀_a₁u : b₀ ∈ S.Ω.interval a₁ u :=
        S.Ω.interval_subset_interval_left hb₁_a₁u hb₀_a₁b₁
      exact disjoint_left.mp hd_a₁u hb₀_a₁u ⟨ hb₀W.2, hb₀_ne_b₁⟩

/-- **Graph Minors IX, (3.2), Claim (3)** (page 48):
"Either $a' \ne a_1$ or there exists $P_3 \in \mathscr{P} - \{P_1\}$ with ends $b_1^+, b_1^-$." -/
theorem lemma_3_2_claim_3 (S : Society α β)
    {P_set : Set (Graph α β)} {A B : Set α}
    (_hcrooked : S.IsCrookedTransaction P_set)
    (hfence : S.IsFenceFor P_set A B)
    {P P₁ P₂ Q_a : Graph α β} {v u a₁ b₁ a₂ b₂ : α}
    (hatt : S.IsAttachmentWithEnds P_set P v u)
    (hnot_exch : ¬ S.IsExchangeableAttachment P_set P)
    (hP₁ : P₁ ∈ P_set) (hvP₁ : v ∈ V(P₁))
    (hP₁_ends : S.IsOmegaPathWithEnds P₁ a₁ b₁)
    (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ B) (huA : u ∈ A)
    (hQ_a : IsGraphPathWithEnds P₁ Q_a v a₁)
    (hP₂ : P₂ ∈ P_set \ {P₁})
    (hP₂_ends : S.IsOmegaPathWithEnds P₂ a₂ b₂)
    (_ha₂ : a₂ ∈ A) (hb₂ : b₂ ∈ B)
    (ha₁_in_P₂ : a₁ ∈ S.Ω.interval a₂ b₂)
    (hd_P₂ : Disjoint (S.Ω.interval a₂ b₂) ((S.transactionEnds P_set ∪ {u}) \ {a₁})) :
    ∃ P₃ ∈ P_set \ {P₁}, P₃ ≠ P₂ ∧ S.IsPeripheralIn (P_set \ {P₁}) P₃ := by
  let W := S.transactionEnds P_set ∪ {u}
  let S_sw := subgraphUnion S.G P Q_a
  let S_set := (P_set \ {P₁}) ∪ {S_sw}
  have hS_ends : S.IsOmegaPathWithEnds S_sw u a₁ :=
    hatt.isOmegaPathWithEnds_subgraphUnion S hP₁ hvP₁ hP₁_ends hQ_a (Or.inl rfl)
  have hS_disj : S.IsDisjointOmegaPathSet S_set :=
    hatt.isDisjointOmegaPathSet_switch S hfence.1 hP₁ hvP₁ hP₁_ends hQ_a (Or.inl rfl)
  have hW_bar : W ⊆ S.Ω.bar := union_subset (S.transactionEnds_subset_bar P_set)
    (singleton_subset_iff.mpr (hatt.end_mem_bar S))
  have hW_AB : W ⊆ A ∪ B := hfence.2.1.2.2.2.1 ▸ hW_bar
  have ha₁W : a₁ ∈ A ∩ W := ⟨ha₁, Or.inl (hP₁_ends.mem_transactionEnds_left S hP₁)⟩
  have hb₁W : b₁ ∈ B ∩ W := ⟨hb₁, Or.inl (hP₁_ends.mem_transactionEnds_right S hP₁)⟩
  have hb₂W : b₂ ∈ B ∩ W := ⟨hb₂, Or.inl (hP₂_ends.mem_transactionEnds_right S hP₂.1)⟩
  have hd_a₁b₂ : Disjoint (S.Ω.interval a₁ b₂) W := by
    rw [disjoint_left]
    intro z hz hzW
    have hza₁ : z ≠ a₁ := fun h => S.Ω.not_mem_interval_left a₁ b₂ (h ▸ hz)
    exact disjoint_left.mp hd_P₂ (S.Ω.interval_subset_interval_right ha₁_in_P₂ hz) ⟨hzW, hza₁⟩
  obtain ⟨b', hb'W, a, haW, hdisj_b'a⟩ :=
    S.Ω.exists_empty_interval_AB_of_subset_union hW_bar (union_comm A B ▸ hW_AB) ⟨b₁, hb₁W⟩ ⟨a₁,
      ha₁W⟩
  obtain ⟨A', B', hfence_A'B', hsubA', hsubB'⟩ :=
    exists_fence_separating_of_disjoint_AB hfence.2.1 hW_bar haW hb₂W hb'W ha₁W hdisj_b'a hd_a₁b₂
  have hS_fence : S.IsFenceFor S_set A' B' := by
    refine ⟨hS_disj, hfence_A'B', ?_⟩
    rintro R (hR | rfl)
    · obtain ⟨a_R, ha_R, b_R, hb_R, hR_ends⟩ := hfence.2.2 R hR.1
      have ha_R_W : a_R ∈ A ∩ W := ⟨ha_R, Or.inl (hR_ends.mem_transactionEnds_left S hR.1)⟩
      have hb_R_W : b_R ∈ B ∩ W := ⟨hb_R, Or.inl (hR_ends.mem_transactionEnds_right S hR.1)⟩
      have ha_R_ne_a₁ : a_R ≠ a₁ := fun h =>
        disjoint_left.mp (hfence.1.2 hR.1 hP₁ hR.2)
          hR_ends.1.left_mem (h ▸ hP₁_ends.1.left_mem)
      exact ⟨a_R, hsubA' ⟨ha_R_W, ha_R_ne_a₁⟩, b_R, hsubB' (Or.inl hb_R_W), hR_ends⟩
    · have hua₁ : u ≠ a₁ :=
        fun h => (hatt.end_not_mem_transactionEnds S) (h ▸ hP₁_ends.mem_transactionEnds_left S hP₁)
      exact ⟨u, hsubA' ⟨⟨huA, Or.inr rfl⟩, hua₁⟩, a₁, hsubB' (Or.inr rfl), hS_ends⟩
  have hS_not_crooked : ¬ S.IsCrookedTransaction S_set := fun hcr =>
    hnot_exch ⟨⟨v, u, hatt⟩, P₁, S_sw,
      ⟨hP₁, v, u, a₁, b₁, hatt, hvP₁, hP₁_ends, Q_a, Or.inl hQ_a, rfl⟩, hcr⟩
  have hex_per : ∃ M ∈ S_set, S.IsPeripheralIn S_set M := by
    by_contra! hno
    exact hS_not_crooked ⟨⟨A', B', hS_fence⟩, hno⟩
  have hSW_eq : S.transactionEnds S_set = W \ {b₁} := by
    rw [hatt.transactionEnds_switch S hP₁ hvP₁ hP₁_ends hQ_a (Or.inl rfl)]
    have hP_eq := hfence.transactionEnds_eq_union S hP₁ hP₁_ends
    have hb₁_not_W' := hfence.not_mem_transactionEnds_diff_right S hP₁ hP₁_ends
    have hub₁ : u ≠ b₁ := fun h => (hatt.end_not_mem_transactionEnds S)
      (h ▸ hP₁_ends.mem_transactionEnds_right S hP₁)
    have ha₁b₁ : a₁ ≠ b₁ := hP₁_ends.2.1
    ext x
    simp only [W, hP_eq, mem_union, mem_insert_iff, mem_singleton_iff, mem_sdiff]
    constructor
    · rintro (hx | rfl | rfl)
      · exact ⟨Or.inl (Or.inl hx), fun h => hb₁_not_W' (h ▸ hx)⟩
      · exact ⟨Or.inr rfl, hub₁⟩
      · exact ⟨Or.inl (Or.inr (Or.inl rfl)), ha₁b₁⟩
    · rintro ⟨(hx | rfl | rfl) | rfl, hne⟩
      · exact Or.inl hx
      · exact Or.inr (Or.inr rfl)
      · exact (hne rfl).elim
      · exact Or.inr (Or.inl rfl)
  -- Notice `u ∈ S.Ω.interval b₂ a₂`, so `(a₂, a₁, b₂, u)` is clockwise, which implies
  -- `b₂ ∈ S.Ω.interval a₁ u` and `a₂ ∈ S.Ω.interval u a₁`.
  have hu_not_a₂b₂ : u ∉ S.Ω.interval a₂ b₂ := fun hu_in =>
    disjoint_left.mp hd_P₂ hu_in
      ⟨Or.inr rfl, fun h => (hatt.end_not_mem_transactionEnds S) (h ▸
        hP₁_ends.mem_transactionEnds_left S hP₁)⟩
  have hua₂ : u ≠ a₂ := fun h => (hatt.end_not_mem_transactionEnds S)
    (h ▸ hP₂_ends.mem_transactionEnds_left S hP₂.1)
  have hub₂ : u ≠ b₂ := fun h => (hatt.end_not_mem_transactionEnds S)
    (h ▸ hP₂_ends.mem_transactionEnds_right S hP₂.1)
  have hu_b₂a₂ : u ∈ S.Ω.interval b₂ a₂ :=
    (S.Ω.mem_interval_or_interval_swap hP₂_ends.2.2.1 hP₂_ends.2.2.2 (hatt.end_mem_bar S)
      hP₂_ends.2.1 hua₂ hub₂).resolve_left hu_not_a₂b₂
  have hcw4 : S.Ω.IsClockwise4 a₂ a₁ b₂ u :=
    S.Ω.isClockwise4_iff_interval.mpr ⟨ha₁_in_P₂, hu_b₂a₂⟩
  have h_b₂_a₂ := S.Ω.isClockwise4_iff_interval.mp (S.Ω.isClockwise4_rotate hcw4)
  have ha₂_in_SW : a₂ ∈ W \ {b₁} :=
    ⟨Or.inl (hP₂_ends.mem_transactionEnds_left S hP₂.1),
      fun h => disjoint_left.mp (hfence.1.2 hP₂.1 hP₁ hP₂.2)
        hP₂_ends.1.left_mem (h ▸ hP₁_ends.1.right_mem)⟩
  have hb₂_in_SW : b₂ ∈ W \ {b₁} :=
    ⟨Or.inl (hP₂_ends.mem_transactionEnds_right S hP₂.1),
      fun h => disjoint_left.mp (hfence.1.2 hP₂.1 hP₁ hP₂.2)
        hP₂_ends.1.right_mem (h ▸ hP₁_ends.1.right_mem)⟩
  rcases hex_per with ⟨M, hM_in, hM_per⟩
  rcases hM_in with hM_diff | rfl
  · -- `M = P₃ ∈ P_set \ {P₁}` is peripheral in `S_set`.
    obtain ⟨a₃, _ha₃, b₃, _hb₃, hP₃_ends⟩ := hfence.2.2 M hM_diff.1
    have hM_per' := (hP₃_ends.isPeripheralIn_iff S (Or.inl hM_diff)).mp hM_per
    rw [hSW_eq] at hM_per'
    have hW'_sub : S.transactionEnds (P_set \ {P₁}) ⊆ W \ {b₁} := by
      rw [← hSW_eq, hatt.transactionEnds_switch S hP₁ hvP₁ hP₁_ends hQ_a (Or.inl rfl)]
      exact subset_union_left
    have hM_per_diff : S.IsPeripheralIn (P_set \ {P₁}) M := by
      refine ⟨hM_diff, a₃, b₃, hP₃_ends, ?_⟩
      rcases hM_per' with hd | hd
      · exact Or.inl (hd.mono_right hW'_sub)
      · exact Or.inr (hd.mono_right hW'_sub)
    have hne : M ≠ P₂ := by
      rintro rfl
      have hM_per'' := (hP₂_ends.isPeripheralIn_iff S (Or.inl hP₂)).mp hM_per
      rw [hSW_eq] at hM_per''
      rcases hM_per'' with hd_ab | hd_ba
      · exact disjoint_left.mp hd_ab ha₁_in_P₂
          ⟨Or.inl (hP₁_ends.mem_transactionEnds_left S hP₁), hP₁_ends.2.1⟩
      · exact disjoint_left.mp hd_ba hu_b₂a₂
          ⟨Or.inr rfl, fun h => (hatt.end_not_mem_transactionEnds S) (h ▸
            hP₁_ends.mem_transactionEnds_right S hP₁)⟩
    exact ⟨M, hM_diff, hne, hM_per_diff⟩
  · -- `M = S_sw` cannot be peripheral in `S_set` since `a₂ ∈ interval u a₁` and `b₂ ∈ interval a₁
    -- u`.
    exfalso
    have hS_per := (hS_ends.isPeripheralIn_iff S (Or.inr rfl)).mp hM_per
    rw [hSW_eq] at hS_per
    rcases hS_per with hd_ua₁ | hd_a₁u
    · exact disjoint_left.mp hd_ua₁ h_b₂_a₂.2 ha₂_in_SW
    · exact disjoint_left.mp hd_a₁u h_b₂_a₂.1 hb₂_in_SW

private theorem replace_endpoint_set {D : Set α} {a b u : α}
    (ha : a ∉ D) (hab : a ≠ b) (hua : u ≠ a) :
    D ∪ {u, b} = ((D ∪ {a, b}) ∪ {u}) \ {a} := by
  ext x
  simp only [mem_union, mem_insert_iff, mem_singleton_iff, mem_sdiff]
  constructor
  · rintro (hx | rfl | rfl)
    · exact ⟨Or.inl (Or.inl hx), fun h => ha (h ▸ hx)⟩
    · exact ⟨Or.inr rfl, hua⟩
    · exact ⟨Or.inl (Or.inr (Or.inr rfl)), hab.symm⟩
  · rintro ⟨(hx | rfl | rfl) | rfl, hne⟩
    · exact Or.inl hx
    · exact (hne rfl).elim
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)

private theorem switched_path_cannot_be_peripheral_mirror (S : Society α β)
    {P_set : Set (Graph α β)} {A B : Set α} {P₁ S_sw : Graph α β} {u a₁ b₁ : α}
    (hcrooked : S.IsCrookedTransaction P_set) (hfence : S.IsFenceFor P_set A B)
    (hP₁ : P₁ ∈ P_set) (hP₁_ends : S.IsOmegaPathWithEnds P₁ a₁ b₁)
    (hu_not : u ∉ S.transactionEnds P_set) (hcw : a₁ ∈ S.Ω.interval b₁ u)
    (hS_ends : S.IsOmegaPathWithEnds S_sw u a₁) :
    let W := S.transactionEnds P_set ∪ {u}
    let S_set := (P_set \ {P₁}) ∪ {S_sw}
    S.IsDisjointOmegaPathSet S_set → (¬ S.IsCrookedTransaction S_set) →
    S.transactionEnds S_set = W \ {b₁} → S.transactionEnds P_set = W \ {u} →
    W ⊆ S.Ω.bar → W ⊆ A ∪ B → a₁ ∈ A ∩ W → b₁ ∈ B ∩ W → u ∈ A ∩ W →
    (Disjoint (S.Ω.interval u b₁) (W \ {a₁}) ∨ Disjoint (S.Ω.interval b₁ u) (W \ {a₁})) →
    False := by
  intro W S_set hS_disj hS_not_crooked hSW_eq hPW_eq hW_bar hW_AB ha₁W hb₁W huW hT_per
  rcases hT_per with hd_ub₁ | hd_b₁u
  · -- `Disjoint (S.Ω.interval u b₁) (W \ {a₁})` gives `Disjoint (S.Ω.interval u b₁) W`
    -- (since `a₁ ∉ S.Ω.interval u b₁`).
    have hd_ub₁_W : Disjoint (S.Ω.interval u b₁) W := by
      rw [disjoint_left]
      intro z hz hzW
      have hza₁ : z ≠ a₁ := fun h =>
        disjoint_left.mp (S.Ω.disjoint_interval_swap b₁ u) hcw (h ▸ hz)
      exact disjoint_left.mp hd_ub₁ hz ⟨hzW, hza₁⟩
    obtain ⟨b', hb'W, a, haW, hdisj_b'a⟩ :=
      S.Ω.exists_empty_interval_AB_of_subset_union hW_bar (union_comm A B ▸ hW_AB) ⟨b₁, hb₁W⟩ ⟨a₁,
        ha₁W⟩
    obtain ⟨A', B', hfence_A'B', hsubA', hsubB'⟩ :=
      exists_fence_separating_of_disjoint_AB hfence.2.1 hW_bar haW hb₁W hb'W huW hdisj_b'a hd_ub₁_W
    have hS_fence : S.IsFenceFor S_set A' B' := by
      refine ⟨hS_disj, hfence_A'B', ?_⟩
      rintro R (hR | rfl)
      · obtain ⟨a_R, ha_R, b_R, hb_R, hR_ends⟩ := hfence.2.2 R hR.1
        have ha_R_W : a_R ∈ A ∩ W := ⟨ha_R, Or.inl (hR_ends.mem_transactionEnds_left S hR.1)⟩
        have hb_R_W : b_R ∈ B ∩ W := ⟨hb_R, Or.inl (hR_ends.mem_transactionEnds_right S hR.1)⟩
        have ha_R_ne_u : a_R ≠ u :=
          fun h => hu_not (h ▸ hR_ends.mem_transactionEnds_left S hR.1)
        exact ⟨a_R, hsubA' ⟨ha_R_W, ha_R_ne_u⟩, b_R, hsubB' (Or.inl hb_R_W), hR_ends⟩
      · have ha₁_ne_u : a₁ ≠ u :=
          fun h => hu_not (h ▸ hP₁_ends.mem_transactionEnds_left S hP₁)
        exact ⟨a₁, hsubA' ⟨ha₁W, ha₁_ne_u⟩, u, hsubB' (Or.inr rfl), hS_ends.symm S⟩
    obtain ⟨P_x, hPx_in, P_y, hPy_in, hPxy, _⟩ := S.exists_crooked_pair_of_nonempty hcrooked ⟨P₁,
      hP₁⟩
    have hex_other : ∃ P₀ ∈ P_set \ {P₁}, True := by
      by_cases h1 : P_x = P₁
      · exact ⟨P_y, ⟨hPy_in, h1 ▸ hPxy.symm⟩, trivial⟩
      · exact ⟨P_x, ⟨hPx_in, h1⟩, trivial⟩
    obtain ⟨P₀, hP₀_diff, _⟩ := hex_other
    obtain ⟨a₀, _ha₀, b₀, hb₀, hP₀_ends⟩ := hfence.2.2 P₀ hP₀_diff.1
    have hb₀W : b₀ ∈ B ∩ W := ⟨hb₀, Or.inl (hP₀_ends.mem_transactionEnds_right S hP₀_diff.1)⟩
    have hb₀_ne_b₁ : b₀ ≠ b₁ := fun h =>
      disjoint_left.mp (hfence.1.2 hP₀_diff.1 hP₁ hP₀_diff.2)
        hP₀_ends.1.right_mem (h ▸ hP₁_ends.1.right_mem)
    have hb'_ne_b₁ : b' ≠ b₁ := by
      intro h_eq
      have h1 : b₁ ∈ S.Ω.interval b₀ a :=
        (S.Ω.mem_interval_of_mem_A_of_disjoint_AB hfence.2.1.symm hW_bar hb₁W haW (h_eq ▸ hdisj_b'a)
          hb₀W hb₀_ne_b₁ haW).1
      have h2 : b₁ ∈ S.Ω.interval a b₀ :=
        (S.Ω.mem_interval_of_mem_B_of_disjoint_AB hfence.2.1 hW_bar huW hb₁W hd_ub₁_W
          haW hb₀W hb₀_ne_b₁).1
      exact disjoint_left.mp (S.Ω.disjoint_interval_swap b₀ a) h1 h2
    have hex_per_S : ∃ M' ∈ S_set, S.IsPeripheralIn S_set M' := by
      by_contra! hno
      exact hS_not_crooked ⟨⟨A', B', hS_fence⟩, hno⟩
    rcases hex_per_S with ⟨M', hM'_in, hM'_per⟩
    rcases hM'_in with hM'_diff | rfl
    · obtain ⟨a₃, ha₃, b₃, hb₃, hP₃_ends⟩ := hfence.2.2 M' hM'_diff.1
      have hM'_per' := (hP₃_ends.isPeripheralIn_iff S (Or.inl hM'_diff)).mp hM'_per
      rw [hSW_eq] at hM'_per'
      have hnot_per_P : ¬ S.IsPeripheralIn P_set M' := hcrooked.2 M' hM'_diff.1
      have ha₃W : a₃ ∈ A ∩ W := ⟨ha₃, Or.inl (hP₃_ends.mem_transactionEnds_left S hM'_diff.1)⟩
      rcases hM'_per' with hd_ab' | hd_ba'
      · have hb₁_in : b₁ ∈ S.Ω.interval a₃ b₃ := by
          by_contra hb₁_not
          apply hnot_per_P
          refine ⟨hM'_diff.1, a₃, b₃, hP₃_ends, Or.inl ?_⟩
          rw [hPW_eq, disjoint_left]
          intro z hz ⟨hzW, _⟩
          have hzb₁ : z ≠ b₁ := fun h => hb₁_not (h ▸ hz)
          exact disjoint_left.mp hd_ab' hz ⟨hzW, hzb₁⟩
        have hd_a₃b₁ : Disjoint (S.Ω.interval a₃ b₁) W := by
          rw [disjoint_left]
          intro z hz hzW
          have hzb₁ : z ≠ b₁ := fun h => S.Ω.not_mem_interval_right a₃ b₁ (h ▸ hz)
          exact disjoint_left.mp hd_ab' (S.Ω.interval_subset_interval_left hb₁_in hz) ⟨hzW, hzb₁⟩
        have hu_eq : u = a₃ :=
          (S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1 hW_bar huW hb₁W ha₃W hb₁W
            hd_ub₁_W hd_a₃b₁).1
        exact hu_not (hu_eq ▸ hP₃_ends.mem_transactionEnds_left S hM'_diff.1)
      · have hb₁_in : b₁ ∈ S.Ω.interval b₃ a₃ := by
          by_contra hb₁_not
          apply hnot_per_P
          refine ⟨hM'_diff.1, a₃, b₃, hP₃_ends, Or.inr ?_⟩
          rw [hPW_eq, disjoint_left]
          intro z hz ⟨hzW, _⟩
          have hzb₁ : z ≠ b₁ := fun h => hb₁_not (h ▸ hz)
          exact disjoint_left.mp hd_ba' hz ⟨hzW, hzb₁⟩
        have hd_b₁a₃ : Disjoint (S.Ω.interval b₁ a₃) W := by
          rw [disjoint_left]
          intro z hz hzW
          have hzb₁ : z ≠ b₁ := fun h => S.Ω.not_mem_interval_left b₁ a₃ (h ▸ hz)
          exact disjoint_left.mp hd_ba' (S.Ω.interval_subset_interval_right hb₁_in hz) ⟨hzW, hzb₁⟩
        have hb'_eq : b' = b₁ :=
          (S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1.symm hW_bar hb'W haW hb₁W ha₃W
            hdisj_b'a hd_b₁a₃).1
        exact hb'_ne_b₁ hb'_eq
    · have hS_per := (hS_ends.isPeripheralIn_iff S (Or.inr rfl)).mp hM'_per
      rw [hSW_eq] at hS_per
      rcases hS_per with hd_ua₁ | hd_a₁u
      · have hb₁_a₁b₀ : b₁ ∈ S.Ω.interval a₁ b₀ :=
          (S.Ω.mem_interval_of_mem_B_of_disjoint_AB hfence.2.1 hW_bar huW hb₁W hd_ub₁_W
            ha₁W hb₀W hb₀_ne_b₁).1
        have hb₀_b₁a₁ : b₀ ∈ S.Ω.interval b₁ a₁ := S.Ω.mem_interval_rotate_left hb₁_a₁b₀
        have hb₁_ua₁ : b₁ ∈ S.Ω.interval u a₁ := S.Ω.mem_interval_rotate_right hcw
        have hb₀_ua₁ : b₀ ∈ S.Ω.interval u a₁ :=
          S.Ω.interval_subset_interval_right hb₁_ua₁ hb₀_b₁a₁
        exact disjoint_left.mp hd_ua₁ hb₀_ua₁ ⟨hb₀W.2, hb₀_ne_b₁⟩
      · have hd_a₁u_W : Disjoint (S.Ω.interval a₁ u) W := by
          rw [disjoint_left]
          intro z hz hzW
          have hzb₁ : z ≠ b₁ := fun h => by
            have hb₁_ua₁ : b₁ ∈ S.Ω.interval u a₁ := S.Ω.mem_interval_rotate_right hcw
            exact disjoint_left.mp (S.Ω.disjoint_interval_swap a₁ u) hz (h ▸ hb₁_ua₁)
          exact disjoint_left.mp hd_a₁u hz ⟨hzW, hzb₁⟩
        have ha₁b₁_split : S.Ω.interval a₁ b₁ = S.Ω.interval a₁ u ∪ {u} ∪ S.Ω.interval u b₁ :=
          S.Ω.interval_eq_union_of_mem (S.Ω.mem_interval_rotate_left hcw)
        have hd_a₁b₁ : Disjoint (S.Ω.interval a₁ b₁) (S.transactionEnds P_set) := by
          rw [hPW_eq, ha₁b₁_split, disjoint_left]
          rintro z ((hz | rfl) | hz) ⟨hzW, hzu⟩
          · exact disjoint_left.mp hd_a₁u_W hz hzW
          · exact hzu rfl
          · exact disjoint_left.mp hd_ub₁_W hz hzW
        exact hcrooked.2 P₁ hP₁ ⟨hP₁, a₁, b₁, hP₁_ends, Or.inl hd_a₁b₁⟩
  · -- `Disjoint (S.Ω.interval b₁ u) (W \ {a₁})` implies `Disjoint (S.Ω.interval b₁ a₁) (W \ {u})`.
    have hd_b₁a₁ : Disjoint (S.Ω.interval b₁ a₁) (S.transactionEnds P_set) := by
      rw [hPW_eq, disjoint_left]
      intro z hz ⟨hzW, _⟩
      have hza₁ : z ≠ a₁ := fun h => S.Ω.not_mem_interval_right b₁ a₁ (h ▸ hz)
      have hz_b₁u : z ∈ S.Ω.interval b₁ u := S.Ω.interval_subset_interval_left hcw hz
      exact disjoint_left.mp hd_b₁u hz_b₁u ⟨hzW, hza₁⟩
    exact hcrooked.2 P₁ hP₁ ⟨hP₁, a₁, b₁, hP₁_ends, Or.inr hd_b₁a₁⟩

/-- Mirror version of Claims (1)–(3) when `u ∈ A` and `(b₁, a₁, u)` is clockwise
(`a₁ ∈ S.Ω.interval b₁ u`). -/
theorem isOverpass_of_u_in_A_mirror (S : Society α β)
    {P_set : Set (Graph α β)} {A B : Set α}
    (hcrooked : S.IsCrookedTransaction P_set)
    (hfence : S.IsFenceFor P_set A B)
    {P P₁ Q_a Q_b : Graph α β} {v u a₁ b₁ : α}
    (hatt : S.IsAttachmentWithEnds P_set P v u)
    (hnot_exch : ¬ S.IsExchangeableAttachment P_set P)
    (hP₁ : P₁ ∈ P_set) (hvP₁ : v ∈ V(P₁))
    (hP₁_ends : S.IsOmegaPathWithEnds P₁ a₁ b₁)
    (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ B) (huA : u ∈ A)
    (hcw : a₁ ∈ S.Ω.interval b₁ u)
    (hQ_a : IsGraphPathWithEnds P₁ Q_a v a₁)
    (hQ_b : IsGraphPathWithEnds P₁ Q_b v b₁) :
    S.IsOverpass P_set P₁ := by
  let W := S.transactionEnds P_set ∪ {u}
  let T_sw := subgraphUnion S.G P Q_b
  let T_set := (P_set \ {P₁}) ∪ {T_sw}
  let S_sw := subgraphUnion S.G P Q_a
  let S_set := (P_set \ {P₁}) ∪ {S_sw}
  have hT_ends : S.IsOmegaPathWithEnds T_sw u b₁ :=
    hatt.isOmegaPathWithEnds_subgraphUnion S hP₁ hvP₁ hP₁_ends hQ_b (Or.inr rfl)
  have hT_disj : S.IsDisjointOmegaPathSet T_set :=
    hatt.isDisjointOmegaPathSet_switch S hfence.1 hP₁ hvP₁ hP₁_ends hQ_b (Or.inr rfl)
  have hT_fence : S.IsFenceFor T_set A B := by
    refine ⟨hT_disj, hfence.2.1, ?_⟩
    rintro R (hR | rfl)
    · exact hfence.2.2 R hR.1
    · exact ⟨u, huA, b₁, hb₁, hT_ends⟩
  have hT_not_crooked : ¬ S.IsCrookedTransaction T_set := fun hcr =>
    hnot_exch ⟨⟨v, u, hatt⟩, P₁, T_sw,
      ⟨hP₁, v, u, a₁, b₁, hatt, hvP₁, hP₁_ends, Q_b, Or.inr hQ_b, rfl⟩, hcr⟩
  have hS_ends : S.IsOmegaPathWithEnds S_sw u a₁ :=
    hatt.isOmegaPathWithEnds_subgraphUnion S hP₁ hvP₁ hP₁_ends hQ_a (Or.inl rfl)
  have hS_disj : S.IsDisjointOmegaPathSet S_set :=
    hatt.isDisjointOmegaPathSet_switch S hfence.1 hP₁ hvP₁ hP₁_ends hQ_a (Or.inl rfl)
  have hS_not_crooked : ¬ S.IsCrookedTransaction S_set := fun hcr =>
    hnot_exch ⟨⟨v, u, hatt⟩, P₁, S_sw,
      ⟨hP₁, v, u, a₁, b₁, hatt, hvP₁, hP₁_ends, Q_a, Or.inl hQ_a, rfl⟩, hcr⟩
  have hTW_eq : S.transactionEnds T_set = W \ {a₁} := by
    rw [hatt.transactionEnds_switch S hP₁ hvP₁ hP₁_ends hQ_b (Or.inr rfl),
      show W = _ from congrArg (fun X => X ∪ {u}) (hfence.transactionEnds_eq_union S hP₁ hP₁_ends)]
    exact replace_endpoint_set (hfence.not_mem_transactionEnds_diff_left S hP₁ hP₁_ends)
      hP₁_ends.2.1
      (fun h => (hatt.end_not_mem_transactionEnds S) (h ▸ hP₁_ends.mem_transactionEnds_left S hP₁))
  have hSW_eq : S.transactionEnds S_set = W \ {b₁} := by
    rw [hatt.transactionEnds_switch S hP₁ hvP₁ hP₁_ends hQ_a (Or.inl rfl),
      show W = _ from congrArg (fun X => X ∪ {u}) (hfence.transactionEnds_eq_union S hP₁ hP₁_ends)]
    rw [show ({a₁, b₁} : Set α) = {b₁, a₁} from pair_comm _ _]
    exact replace_endpoint_set (hfence.not_mem_transactionEnds_diff_right S hP₁ hP₁_ends)
      hP₁_ends.2.1.symm
      (fun h => (hatt.end_not_mem_transactionEnds S) (h ▸ hP₁_ends.mem_transactionEnds_right S hP₁))
  have hPW_eq : S.transactionEnds P_set = W \ {u} := by
    ext x
    simp only [W, mem_union, mem_singleton_iff, mem_sdiff]
    exact ⟨fun hx => ⟨Or.inl hx, fun h => (hatt.end_not_mem_transactionEnds S) (h ▸ hx)⟩,
      fun ⟨hx, hne⟩ => hx.resolve_right hne⟩
  have hW_bar : W ⊆ S.Ω.bar := union_subset (S.transactionEnds_subset_bar P_set)
    (singleton_subset_iff.mpr (hatt.end_mem_bar S))
  have hW_AB : W ⊆ A ∪ B := hfence.2.1.2.2.2.1 ▸ hW_bar
  have ha₁W : a₁ ∈ A ∩ W := ⟨ha₁, Or.inl (hP₁_ends.mem_transactionEnds_left S hP₁)⟩
  have hb₁W : b₁ ∈ B ∩ W := ⟨hb₁, Or.inl (hP₁_ends.mem_transactionEnds_right S hP₁)⟩
  have huW : u ∈ A ∩ W := ⟨huA, Or.inr rfl⟩
  have hex_per_T : ∃ M ∈ T_set, S.IsPeripheralIn T_set M := by
    by_contra! hno
    exact hT_not_crooked ⟨⟨A, B, hT_fence⟩, hno⟩
  rcases hex_per_T with ⟨M, hM_in, hM_per⟩
  rcases hM_in with hM_diff | rfl
  · -- `M = P₂ ∈ P_set \ {P₁}` is peripheral in `T_set`.
    obtain ⟨a₂, ha₂, b₂, hb₂, hP₂_ends⟩ := hfence.2.2 M hM_diff.1
    have hM_per' := (hP₂_ends.isPeripheralIn_iff S (Or.inl hM_diff)).mp hM_per
    rw [hTW_eq] at hM_per'
    have hW'_sub_T : S.transactionEnds (P_set \ {P₁}) ⊆ W \ {a₁} := by
      rw [← hTW_eq, hatt.transactionEnds_switch S hP₁ hvP₁ hP₁_ends hQ_b (Or.inr rfl)]
      exact subset_union_left
    have hM_per_diff : S.IsPeripheralIn (P_set \ {P₁}) M := by
      refine ⟨hM_diff, a₂, b₂, hP₂_ends, ?_⟩
      rcases hM_per' with hd | hd
      · exact Or.inl (hd.mono_right hW'_sub_T)
      · exact Or.inr (hd.mono_right hW'_sub_T)
    have hnot_per_P : ¬ S.IsPeripheralIn P_set M := hcrooked.2 M hM_diff.1
    rcases hM_per' with hd_ab | hd_ba
    · -- `a₁ ∈ S.Ω.interval a₂ b₂` and `Disjoint (S.Ω.interval a₂ b₂) (W \ {a₁})`
      -- contradicts `a₁ ∈ S.Ω.interval b₁ u`.
      exfalso
      have ha₁_in : a₁ ∈ S.Ω.interval a₂ b₂ := by
        by_contra ha₁_not
        apply hnot_per_P
        refine ⟨hM_diff.1, a₂, b₂, hP₂_ends, Or.inl ?_⟩
        rw [hPW_eq, disjoint_left]
        intro z hz ⟨hzW, _⟩
        have hza₁ : z ≠ a₁ := fun h => ha₁_not (h ▸ hz)
        exact disjoint_left.mp hd_ab hz ⟨hzW, hza₁⟩
      have hd_a₁b₂ : Disjoint (S.Ω.interval a₁ b₂) W := by
        rw [disjoint_left]
        intro z hz hzW
        have hza₁ : z ≠ a₁ := fun h => S.Ω.not_mem_interval_left a₁ b₂ (h ▸ hz)
        exact disjoint_left.mp hd_ab (S.Ω.interval_subset_interval_right ha₁_in hz) ⟨hzW, hza₁⟩
      have hb₂W : b₂ ∈ B ∩ W := ⟨hb₂, Or.inl (hP₂_ends.mem_transactionEnds_right S hM_diff.1)⟩
      have hua₁ : u ≠ a₁ := fun h => (hatt.end_not_mem_transactionEnds S)
        (h ▸ hP₁_ends.mem_transactionEnds_left S hP₁)
      have ha₁_ub₁ : a₁ ∈ S.Ω.interval u b₁ :=
        (S.Ω.mem_interval_of_mem_A_of_disjoint_AB hfence.2.1 hW_bar ha₁W hb₂W hd_a₁b₂
          huW hua₁ hb₁W).1
      exact disjoint_left.mp (S.Ω.disjoint_interval_swap u b₁) ha₁_ub₁ hcw
    · -- `a₁ ∈ S.Ω.interval b₂ a₂` and `Disjoint (S.Ω.interval b₂ a₂) (W \ {a₁})`.
      have ha₁_in : a₁ ∈ S.Ω.interval b₂ a₂ := by
        by_contra ha₁_not
        apply hnot_per_P
        refine ⟨hM_diff.1, a₂, b₂, hP₂_ends, Or.inr ?_⟩
        rw [hPW_eq, disjoint_left]
        intro z hz ⟨hzW, _⟩
        have hza₁ : z ≠ a₁ := fun h => ha₁_not (h ▸ hz)
        exact disjoint_left.mp hd_ba hz ⟨hzW, hza₁⟩
      have hd_b₂a₁ : Disjoint (S.Ω.interval b₂ a₁) W := by
        rw [disjoint_left]
        intro z hz hzW
        have hza₁ : z ≠ a₁ := fun h => S.Ω.not_mem_interval_right b₂ a₁ (h ▸ hz)
        exact disjoint_left.mp hd_ba (S.Ω.interval_subset_interval_left ha₁_in hz) ⟨hzW, hza₁⟩
      have hb₂W : b₂ ∈ B ∩ W := ⟨hb₂, Or.inl (hP₂_ends.mem_transactionEnds_right S hM_diff.1)⟩
      obtain ⟨a', ha'W, b, hbW, hdisj_a'b⟩ :=
        S.Ω.exists_empty_interval_AB_of_subset_union hW_bar hW_AB ⟨a₁, ha₁W⟩ ⟨b₁, hb₁W⟩
      obtain ⟨A', B', hfence_A'B', hsubA', hsubB'⟩ :=
        exists_fence_separating_of_disjoint_BA hfence.2.1 hW_bar ha'W hbW hb₂W ha₁W hdisj_a'b
          hd_b₂a₁
      have hS_fence : S.IsFenceFor S_set A' B' := by
        refine ⟨hS_disj, hfence_A'B', ?_⟩
        rintro R (hR | rfl)
        · obtain ⟨a_R, ha_R, b_R, hb_R, hR_ends⟩ := hfence.2.2 R hR.1
          have ha_R_W : a_R ∈ A ∩ W := ⟨ha_R, Or.inl (hR_ends.mem_transactionEnds_left S hR.1)⟩
          have hb_R_W : b_R ∈ B ∩ W := ⟨hb_R, Or.inl (hR_ends.mem_transactionEnds_right S hR.1)⟩
          have ha_R_ne_a₁ : a_R ≠ a₁ := fun h =>
            disjoint_left.mp (hfence.1.2 hR.1 hP₁ hR.2)
              hR_ends.1.left_mem (h ▸ hP₁_ends.1.left_mem)
          exact ⟨a_R, hsubA' ⟨ha_R_W, ha_R_ne_a₁⟩, b_R, hsubB' (Or.inl hb_R_W), hR_ends⟩
        · have hua₁ : u ≠ a₁ :=
            fun h => (hatt.end_not_mem_transactionEnds S) (h ▸ hP₁_ends.mem_transactionEnds_left S
              hP₁)
          exact ⟨u, hsubA' ⟨huW, hua₁⟩, a₁, hsubB' (Or.inr rfl), hS_ends⟩
      have hex_per_S : ∃ M' ∈ S_set, S.IsPeripheralIn S_set M' := by
        by_contra! hno
        exact hS_not_crooked ⟨⟨A', B', hS_fence⟩, hno⟩
      have hu_not_b₂a₂ : u ∉ S.Ω.interval b₂ a₂ := fun hu_in =>
        disjoint_left.mp hd_ba hu_in
          ⟨Or.inr rfl, fun h => (hatt.end_not_mem_transactionEnds S) (h ▸
            hP₁_ends.mem_transactionEnds_left S hP₁)⟩
      have hua₂ : u ≠ a₂ := fun h => (hatt.end_not_mem_transactionEnds S)
        (h ▸ hP₂_ends.mem_transactionEnds_left S hM_diff.1)
      have hub₂ : u ≠ b₂ := fun h => (hatt.end_not_mem_transactionEnds S)
        (h ▸ hP₂_ends.mem_transactionEnds_right S hM_diff.1)
      have hu_a₂b₂ : u ∈ S.Ω.interval a₂ b₂ :=
        (S.Ω.mem_interval_or_interval_swap hP₂_ends.2.2.2 hP₂_ends.2.2.1 (hatt.end_mem_bar S)
          hP₂_ends.2.1.symm hub₂ hua₂).resolve_left hu_not_b₂a₂
      have hcw4 : S.Ω.IsClockwise4 b₂ a₁ a₂ u :=
        S.Ω.isClockwise4_iff_interval.mpr ⟨ha₁_in, hu_a₂b₂⟩
      have h_a₂_b₂ := S.Ω.isClockwise4_iff_interval.mp (S.Ω.isClockwise4_rotate hcw4)
      have ha₂_in_SW : a₂ ∈ W \ {b₁} :=
        ⟨Or.inl (hP₂_ends.mem_transactionEnds_left S hM_diff.1),
          fun h => disjoint_left.mp (hfence.1.2 hM_diff.1 hP₁ hM_diff.2)
            hP₂_ends.1.left_mem (h ▸ hP₁_ends.1.right_mem)⟩
      have hb₂_in_SW : b₂ ∈ W \ {b₁} :=
        ⟨Or.inl (hP₂_ends.mem_transactionEnds_right S hM_diff.1),
          fun h => disjoint_left.mp (hfence.1.2 hM_diff.1 hP₁ hM_diff.2)
            hP₂_ends.1.right_mem (h ▸ hP₁_ends.1.right_mem)⟩
      rcases hex_per_S with ⟨M', hM'_in, hM'_per⟩
      rcases hM'_in with hM'_diff | rfl
      · obtain ⟨a₃, _ha₃, b₃, _hb₃, hP₃_ends⟩ := hfence.2.2 M' hM'_diff.1
        have hM'_per' := (hP₃_ends.isPeripheralIn_iff S (Or.inl hM'_diff)).mp hM'_per
        rw [hSW_eq] at hM'_per'
        have hW'_sub_S : S.transactionEnds (P_set \ {P₁}) ⊆ W \ {b₁} := by
          rw [← hSW_eq, hatt.transactionEnds_switch S hP₁ hvP₁ hP₁_ends hQ_a (Or.inl rfl)]
          exact subset_union_left
        have hM'_per_diff : S.IsPeripheralIn (P_set \ {P₁}) M' := by
          refine ⟨hM'_diff, a₃, b₃, hP₃_ends, ?_⟩
          rcases hM'_per' with hd | hd
          · exact Or.inl (hd.mono_right hW'_sub_S)
          · exact Or.inr (hd.mono_right hW'_sub_S)
        have hne : M' ≠ M := by
          rintro rfl
          have hM'_per'' := (hP₂_ends.isPeripheralIn_iff S (Or.inl hM_diff)).mp hM'_per
          rw [hSW_eq] at hM'_per''
          rcases hM'_per'' with hd_ab' | hd_ba'
          · exact disjoint_left.mp hd_ab' hu_a₂b₂
              ⟨Or.inr rfl, fun h => (hatt.end_not_mem_transactionEnds S)
                (h ▸ hP₁_ends.mem_transactionEnds_right S hP₁)⟩
          · exact disjoint_left.mp hd_ba' ha₁_in
              ⟨Or.inl (hP₁_ends.mem_transactionEnds_left S hP₁), hP₁_ends.2.1⟩
        exact ⟨hcrooked, hP₁, M, hM_diff, M', hM'_diff, hne.symm, hM_per_diff, hM'_per_diff⟩
      · exfalso
        have hS_per := (hS_ends.isPeripheralIn_iff S (Or.inr rfl)).mp hM'_per
        rw [hSW_eq] at hS_per
        rcases hS_per with hd_ua₁ | hd_a₁u
        · exact disjoint_left.mp hd_ua₁ h_a₂_b₂.2 hb₂_in_SW
        · exact disjoint_left.mp hd_a₁u h_a₂_b₂.1 ha₂_in_SW
  · -- `M = T_sw` is peripheral in `T_set`.
    exfalso
    have hT_per := (hT_ends.isPeripheralIn_iff S (Or.inr rfl)).mp hM_per
    rw [hTW_eq] at hT_per
    exact switched_path_cannot_be_peripheral_mirror S hcrooked hfence hP₁ hP₁_ends
      (hatt.end_not_mem_transactionEnds S) hcw hS_ends hS_disj hS_not_crooked
      hSW_eq hPW_eq hW_bar hW_AB ha₁W hb₁W huW hT_per

/-- Core case of (3.2) when `u ∈ A`. -/
theorem isOverpass_of_u_in_A (S : Society α β)
    {P_set : Set (Graph α β)} {A B : Set α}
    (hcrooked : S.IsCrookedTransaction P_set)
    (hfence : S.IsFenceFor P_set A B)
    {P P₁ : Graph α β} {v u a₁ b₁ : α}
    (hatt : S.IsAttachmentWithEnds P_set P v u)
    (hnot_exch : ¬ S.IsExchangeableAttachment P_set P)
    (hP₁ : P₁ ∈ P_set) (hvP₁ : v ∈ V(P₁))
    (hP₁_ends : S.IsOmegaPathWithEnds P₁ a₁ b₁)
    (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ B) (huA : u ∈ A) :
    S.IsOverpass P_set P₁ := by
  obtain ⟨Q_a', Q_b, _, _, hQ_a', hQ_b, _, _, _⟩ := hP₁_ends.1.exists_split_at hvP₁
  have hQ_a : IsGraphPathWithEnds P₁ Q_a' v a₁ := hQ_a'.symm
  have hua₁ : u ≠ a₁ := fun h => (hatt.end_not_mem_transactionEnds S)
    (h ▸ hP₁_ends.mem_transactionEnds_left S hP₁)
  have hub₁ : u ≠ b₁ := fun h => (hatt.end_not_mem_transactionEnds S)
    (h ▸ hP₁_ends.mem_transactionEnds_right S hP₁)
  rcases S.Ω.mem_interval_or_interval_swap (hatt.end_mem_bar S) hP₁_ends.2.2.2 hP₁_ends.2.2.1
    hub₁ hua₁.symm hP₁_ends.2.1 with hcw | hcw
  · -- `(u, a₁, b₁)` is clockwise.
    have h1 := S.lemma_3_2_claim_1 hcrooked hfence hatt hnot_exch hP₁ hvP₁ hP₁_ends
      ha₁ hb₁ huA hcw hQ_b
    have h2 := S.lemma_3_2_claim_2 hcrooked hfence hatt hnot_exch hP₁ hvP₁ hP₁_ends
      ha₁ hb₁ huA hcw hQ_a
    obtain ⟨P₂, hP₂_in, hP₂_per, a₂, ha₂, b₂, hb₂, hP₂_ends, ha₁_in_P₂, hd_P₂⟩ :=
      h1.1.resolve_left h2
    obtain ⟨P₃, hP₃_in, hP32, hP₃_per⟩ :=
      S.lemma_3_2_claim_3 hcrooked hfence hatt hnot_exch hP₁ hvP₁ hP₁_ends
        ha₁ hb₁ huA hQ_a hP₂_in hP₂_ends ha₂ hb₂ ha₁_in_P₂ hd_P₂
    exact ⟨hcrooked, hP₁, P₂, hP₂_in, P₃, hP₃_in, hP32.symm, hP₂_per, hP₃_per⟩
  · -- `(b₁, a₁, u)` is clockwise.
    exact S.isOverpass_of_u_in_A_mirror hcrooked hfence hatt hnot_exch hP₁ hvP₁ hP₁_ends
      ha₁ hb₁ huA hcw hQ_a hQ_b

/-- **Graph Minors IX, (3.2)** (page 47):
"Every attachment to a crooked transaction that is not exchangeable is an overpass attachment." -/
theorem theorem_3_2_proof (S : Society α β)
    {P_set : Set (Graph α β)} {P : Graph α β}
    (hcrooked : S.IsCrookedTransaction P_set)
    (hatt : S.IsAttachment P_set P)
    (hnot_exch : ¬ S.IsExchangeableAttachment P_set P) :
    S.IsOverpassAttachment P_set P := by
  rcases hatt with ⟨v, u, hatt_vu⟩
  obtain ⟨P₁, hP₁_in, hvP₁⟩ := hatt_vu.exists_leg S
  refine ⟨⟨v, u, hatt_vu⟩, P₁, ⟨hP₁_in, v, ⟨u, hatt_vu⟩, hvP₁⟩, ?_⟩
  obtain ⟨A, B, hfence⟩ := hcrooked.1
  obtain ⟨a₁, ha₁, b₁, hb₁, hP₁_ends⟩ := hfence.2.2 P₁ hP₁_in
  have hu_AB : u ∈ A ∪ B := hfence.2.1.2.2.2.1 ▸ (hatt_vu.end_mem_bar S)
  rcases hu_AB with huA | huB
  · exact S.isOverpass_of_u_in_A hcrooked hfence hatt_vu hnot_exch hP₁_in hvP₁ hP₁_ends ha₁ hb₁ huA
  · have hfence_BA : S.IsFenceFor P_set B A :=
      ⟨hfence.1, hfence.2.1.symm, fun R hR => by
        obtain ⟨a, ha, b, hb, hR_e⟩ := hfence.2.2 R hR
        exact ⟨b, hb, a, ha, hR_e.symm S⟩⟩
    exact S.isOverpass_of_u_in_A hcrooked hfence_BA hatt_vu hnot_exch hP₁_in hvP₁
      (hP₁_ends.symm S) hb₁ ha₁ huB

end Society

end GraphMinor.GM09
