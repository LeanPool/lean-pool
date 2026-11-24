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
import LeanPool.GraphMinor.GM09.Section3a
import LeanPool.GraphMinor.GM09.Section3c
import LeanPool.GraphMinor.GM09.Section4a
import LeanPool.GraphMinor.GM09.Section4b
import Mathlib.Data.Set.Card

/-!
# Graph Minors IX, Section 4 (Part C): Proof of (4.5) and (4.6)

This file completes the formalization of Section 4 of Robertson and Seymour,
*Graph Minors IX. Disjoint Crossed Paths*, J. Combin. Theory Ser. B 49 (1990), 40–77:
- `(4.5)` (`theorem_4_5`, pages 51–52): under Statement **S**, if `Q₁, Q₂, Q₃, Q₄, Q₅ ∈ Q_set`
  are in order and `Q₂, Q₃, Q₄` are separating, then not all of `Q₁, …, Q₅` are half-covered.
- `(4.6)` (`theorem_4_6`, page 52): under Statement **S** with `p ≥ 2`, `p ≠ 3`, and
  `|Q_set| = p + 4`, if every member of `Q_set` is separating, then some `Q ∈ Q_set` is
  disjoint from `⋃ P_set`.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Graph GraphMinor GraphMinor.Surface

universe u v
variable {α : Type u} {β : Type v}

/-! ## Interval Inclusion and Fence Alignment Lemmas -/

namespace CyclicPerm

variable (Ω : CyclicPerm α)

/-- In a fence `(U, V)`, if `a, x ∈ U`, `b, y ∈ V`, and `x, y ∉ Ω.interval a b`, then
`Ω.interval a b ⊆ Ω.interval x y`. -/
theorem IsFence.interval_subset_of_not_mem {U V : Set α} (hfence : Ω.IsFence U V)
    {a b x y : α} (ha : a ∈ U) (hb : b ∈ V) (hx : x ∈ U) (hy : y ∈ V)
    (hx_not : x ∉ Ω.interval a b) (hy_not : y ∉ Ω.interval a b) :
    Ω.interval a b ⊆ Ω.interval x y := by
  let W : Set α := {a, b, x, y}
  have hW : W ⊆ Ω.bar := by
    rintro z (rfl | rfl | rfl | rfl)
    · exact hfence.1 ha
    · exact hfence.2.1 hb
    · exact hfence.1 hx
    · exact hfence.2.1 hy
  have hdisj : Disjoint (Ω.interval a b) W := by
    rw [disjoint_right]
    intro z hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Ω.not_mem_interval_left z b
    · exact Ω.not_mem_interval_right a z
    · exact hx_not
    · exact hy_not
  exact Ω.interval_subset_of_disjoint_AB hfence hW
    ⟨ha, by simp [W]⟩ ⟨hb, by simp [W]⟩ hdisj ⟨hx, by simp [W]⟩ ⟨hy, by simp [W]⟩

/-- In a fence `(U, V)`, if `a, a₂ ∈ U` and `b, b₂ ∈ V`, it is impossible that both
`a ∈ Ω.interval a₂ b₂` and `a₂ ∈ Ω.interval a b`. -/
theorem IsFence.not_mem_interval_both_left {U V : Set α} (hfence : Ω.IsFence U V)
    {a b a₂ b₂ : α} (ha : a ∈ U) (hb : b ∈ V) (ha₂ : a₂ ∈ U) (hb₂ : b₂ ∈ V)
    (ha_in : a ∈ Ω.interval a₂ b₂) (ha₂_in : a₂ ∈ Ω.interval a b) : False := by
  have hb₂_aa₂ : b₂ ∈ Ω.interval a a₂ := Ω.mem_interval_rotate_left ha_in
  have hb_a₂a : b ∈ Ω.interval a₂ a := Ω.mem_interval_rotate_left ha₂_in
  have haa₂ : a ≠ a₂ := fun h => Ω.not_mem_interval_left a₂ b₂ (h ▸ ha_in)
  have hbb₂ : b₂ ≠ b :=
    fun h => disjoint_left.mp (Ω.disjoint_interval_swap a a₂) hb₂_aa₂ (h ▸ hb_a₂a)
  exact hfence.2.2.2.2 a ha a₂ ha₂ haa₂ b₂ hb₂ b hb hbb₂
    (Ω.crosses_iff_interval.mpr (Or.inl ⟨hb₂_aa₂, hb_a₂a⟩))

/-- In a fence `(U, V)`, for any `a, a₂ ∈ U` and `b, b₂ ∈ V`, either one of the intervals
`Ω.interval a b` and `Ω.interval a₂ b₂` is a subset of the other, or one of `a, b` lies in
`Ω.interval a₂ b₂` and the other lies in `Ω.interval b₂ a₂`. -/
theorem IsFence.interval_subset_or_subset_or_cross {U V : Set α} (hfence : Ω.IsFence U V)
    {a b a₂ b₂ : α} (ha : a ∈ U) (hb : b ∈ V) (ha₂ : a₂ ∈ U) (hb₂ : b₂ ∈ V) :
    Ω.interval a b ⊆ Ω.interval a₂ b₂ ∨
      Ω.interval a₂ b₂ ⊆ Ω.interval a b ∨
      (a ∈ Ω.interval a₂ b₂ ∧ b ∈ Ω.interval b₂ a₂) ∨
      (b ∈ Ω.interval a₂ b₂ ∧ a ∈ Ω.interval b₂ a₂) := by
  have ha_bar : a ∈ Ω.bar := hfence.1 ha
  have hb_bar : b ∈ Ω.bar := hfence.2.1 hb
  have ha₂_bar : a₂ ∈ Ω.bar := hfence.1 ha₂
  have hb₂_bar : b₂ ∈ Ω.bar := hfence.2.1 hb₂
  have ha₂b₂ : a₂ ≠ b₂ := fun h => disjoint_left.mp hfence.2.2.1 ha₂ (h ▸ hb₂)
  have hab₂ : a ≠ b₂ := fun h => disjoint_left.mp hfence.2.2.1 ha (h ▸ hb₂)
  have hba₂ : b ≠ a₂ := fun h => disjoint_left.mp hfence.2.2.1 ha₂ (h ▸ hb)
  by_cases ha_in : a ∈ Ω.interval a₂ b₂
  · by_cases hbb₂ : b = b₂
    · subst hbb₂
      exact Or.inl (Ω.interval_subset_interval_right ha_in)
    · rcases Ω.mem_interval_or_interval_swap ha₂_bar hb₂_bar hb_bar ha₂b₂ hba₂ hbb₂ with
        hb_in | hb_ba
      · have ha₂_not : a₂ ∉ Ω.interval a b :=
          fun h => hfence.not_mem_interval_both_left Ω ha hb ha₂ hb₂ ha_in h
        have hb₂_not : b₂ ∉ Ω.interval a b := by
          intro hb₂_in
          have hb_b₂a₂ : b ∈ Ω.interval b₂ a₂ := by
            exfalso
            have ha₂_b₂b : a₂ ∈ Ω.interval b₂ b := Ω.mem_interval_rotate_right hb_in
            have ha_bb₂ : a ∈ Ω.interval b b₂ := Ω.mem_interval_rotate_right hb₂_in
            have hbb₂' : b₂ ≠ b := Ne.symm hbb₂
            have ha₂a : a₂ ≠ a := fun h => Ω.not_mem_interval_left a₂ b₂ (h ▸ ha_in)
            exact hfence.symm.2.2.2.2 b₂ hb₂ b hb hbb₂' a₂ ha₂ a ha ha₂a
              (Ω.crosses_iff_interval.mpr (Or.inl ⟨ha₂_b₂b, ha_bb₂⟩))
          exact disjoint_left.mp (Ω.disjoint_interval_swap a₂ b₂) hb_in hb_b₂a₂
        exact Or.inl (hfence.interval_subset_of_not_mem Ω ha hb ha₂ hb₂ ha₂_not hb₂_not)
      · exact Or.inr (Or.inr (Or.inl ⟨ha_in, hb_ba⟩))
  · by_cases hb_in : b ∈ Ω.interval a₂ b₂
    · by_cases haa₂ : a = a₂
      · subst haa₂
        exact Or.inl (Ω.interval_subset_interval_left hb_in)
      · have ha_ba : a ∈ Ω.interval b₂ a₂ :=
          (Ω.mem_interval_or_interval_swap ha₂_bar hb₂_bar ha_bar ha₂b₂ haa₂ hab₂).resolve_left
            ha_in
        exact Or.inr (Or.inr (Or.inr ⟨hb_in, ha_ba⟩))
    · exact Or.inr (Or.inl (hfence.interval_subset_of_not_mem Ω ha₂ hb₂ ha hb ha_in hb_in))

/-- In a fence `(U, V)`, if `x₁ ∈ U`, `y₁ ∈ V`, `(x₂ ∈ U ∧ y₂ ∈ V) ∨ (x₂ ∈ V ∧ y₂ ∈ U)`, and
`x₂ ∈ Ω.interval x₁ y₁` and `y₂ ∈ Ω.interval x₂ y₁`, then `x₂ ∈ U ∧ y₂ ∈ V`. -/
theorem IsFence.same_side_of_mem_interval {U V : Set α} (hfence : Ω.IsFence U V)
    {x₁ y₁ x₂ y₂ : α} (hx₁ : x₁ ∈ U) (hy₁ : y₁ ∈ V)
    (h₂ : (x₂ ∈ U ∧ y₂ ∈ V) ∨ (x₂ ∈ V ∧ y₂ ∈ U))
    (hx₂_in : x₂ ∈ Ω.interval x₁ y₁) (hy₂_in : y₂ ∈ Ω.interval x₂ y₁) :
    x₂ ∈ U ∧ y₂ ∈ V := by
  rcases h₂ with hUV | ⟨hx₂V, hy₂U⟩
  · exact hUV
  · exfalso
    have hx₂_x₁y₂ : x₂ ∈ Ω.interval x₁ y₂ :=
      Ω.mem_interval_left_of_mem_interval_right hx₂_in hy₂_in
    have hy₁_y₂x₁ : y₁ ∈ Ω.interval y₂ x₁ :=
      Ω.mem_interval_rotate_left (Ω.interval_subset_interval_right hx₂_in hy₂_in)
    have hx₁y₂ : x₁ ≠ y₂ := fun h => (Ω.mem_interval_rotate_left hy₁_y₂x₁).1.2 (Or.inr h)
    have hx₂y₁ : x₂ ≠ y₁ := fun h => hx₂_in.1.2 (Or.inr h)
    exact hfence.2.2.2.2 x₁ hx₁ y₂ hy₂U hx₁y₂ x₂ hx₂V y₁ hy₁ hx₂y₁
      (Ω.crosses_iff_interval.mpr (Or.inl ⟨hx₂_x₁y₂, hy₁_y₂x₁⟩))

end CyclicPerm

/-! ## Proof of (4.5) (pages 51–52) -/

namespace Society

variable (S : Society α β)

/-- A single path `P₃` in `S` cannot share an end with each of three pairwise vertex-disjoint
`Ω`-paths `Q₁, Q₂, Q₃`. -/
theorem not_shares_end_with_three {P₃ Q₁ Q₂ Q₃ : Graph α β}
    {x₁ y₁ x₂ y₂ x₃ y₃ : α}
    (hQ₁ : S.IsOmegaPathWithEnds Q₁ x₁ y₁)
    (hQ₂ : S.IsOmegaPathWithEnds Q₂ x₂ y₂)
    (hQ₃ : S.IsOmegaPathWithEnds Q₃ x₃ y₃)
    (hdisj_12 : Disjoint V(Q₁) V(Q₂))
    (hdisj_13 : Disjoint V(Q₁) V(Q₃))
    (hdisj_23 : Disjoint V(Q₂) V(Q₃))
    {u v : α} (_hP₃ : S.IsOmegaPathWithEnds P₃ u v)
    {s₁ s₂ s₃ : α}
    (hs₁_P : s₁ = u ∨ s₁ = v) (hs₂_P : s₂ = u ∨ s₂ = v) (hs₃_P : s₃ = u ∨ s₃ = v)
    (hs₁_Q : s₁ = x₁ ∨ s₁ = y₁) (hs₂_Q : s₂ = x₂ ∨ s₂ = y₂) (hs₃_Q : s₃ = x₃ ∨ s₃ = y₃) :
    False := by
  have hs₁_V : s₁ ∈ V(Q₁) := by
    rcases hs₁_Q with rfl | rfl
    · exact hQ₁.1.left_mem
    · exact hQ₁.1.right_mem
  have hs₂_V : s₂ ∈ V(Q₂) := by
    rcases hs₂_Q with rfl | rfl
    · exact hQ₂.1.left_mem
    · exact hQ₂.1.right_mem
  have hs₃_V : s₃ ∈ V(Q₃) := by
    rcases hs₃_Q with rfl | rfl
    · exact hQ₃.1.left_mem
    · exact hQ₃.1.right_mem
  have hne_12 : s₁ ≠ s₂ := fun h => disjoint_left.mp hdisj_12 hs₁_V (h ▸ hs₂_V)
  have hne_13 : s₁ ≠ s₃ := fun h => disjoint_left.mp hdisj_13 hs₁_V (h ▸ hs₃_V)
  have hne_23 : s₂ ≠ s₃ := fun h => disjoint_left.mp hdisj_23 hs₂_V (h ▸ hs₃_V)
  rcases hs₁_P with rfl | rfl <;> rcases hs₂_P with h₂ | h₂ <;> rcases hs₃_P with h₃ | h₃
  · exact hne_12 h₂.symm
  · exact hne_12 h₂.symm
  · exact hne_13 h₃.symm
  · exact hne_23 (h₂.trans h₃.symm)
  · exact hne_23 (h₂.trans h₃.symm)
  · exact hne_13 h₃.symm
  · exact hne_12 h₂.symm
  · exact hne_12 h₂.symm

/-- Unified contradiction for both cases of `(4.5)` on one side `(U, V)` of the fence. -/
theorem half_covered_side_contradiction
    {P_set : Set (Graph α β)} {U V : Set α}
    {P₃ Q₁ Q₂ Q₃ : Graph α β} {x₁ y₁ x₂ y₂ x₃ y₃ : α}
    (hfence : S.IsFenceFor P_set U V)
    (hcrooked : S.IsCrookedTransaction P_set)
    (hP₃_in : P₃ ∈ P_set)
    (hQ₁_ends : S.IsOmegaPathWithEnds Q₁ x₁ y₁)
    (hQ₂_ends : S.IsOmegaPathWithEnds Q₂ x₂ y₂)
    (hQ₃_ends : S.IsOmegaPathWithEnds Q₃ x₃ y₃)
    (hx₂ : x₂ ∈ U) (hy₂ : y₂ ∈ V) (hx₃ : x₃ ∈ U) (hy₃ : y₃ ∈ V)
    (hx₁_2 : x₁ ∈ S.Ω.interval x₂ y₂) (hy₁_2 : y₁ ∈ S.Ω.interval x₂ y₂)
    (hx₁_3 : x₁ ∈ S.Ω.interval x₃ y₃) (hy₁_3 : y₁ ∈ S.Ω.interval x₃ y₃)
    (hx₂_3 : x₂ ∈ S.Ω.interval x₃ y₃) (hy₂_3 : y₂ ∈ S.Ω.interval x₃ y₃)
    (hx₃_2 : x₃ ∈ S.Ω.interval y₂ x₂) (hy₃_2 : y₃ ∈ S.Ω.interval y₂ x₂)
    (hdisj_12 : Disjoint V(Q₁) V(Q₂))
    (hdisj_13 : Disjoint V(Q₁) V(Q₃))
    (hdisj_23 : Disjoint V(Q₂) V(Q₃))
    (hsep₂ : S.IsSeparatingOmegaPath Q₂)
    (hcov₁ : S.IsHalfCovered P_set Q₁)
    (hcov₂ : S.IsHalfCovered P_set Q₂)
    (hcov₃ : S.IsHalfCovered P_set Q₃)
    (hmeet₃ : (V(P₃) ∩ V(Q₃)).Nonempty)
    (hcase : Disjoint (S.Ω.interval x₃ y₃) (S.transactionEnds ((P_set \ {P₃}) ∪ {Q₃})) ∨
      ∃ P ∈ P_set \ {P₃}, ∃ a ∈ U, ∃ b ∈ V,
        S.IsOmegaPathWithEnds P a b ∧
        Disjoint (S.Ω.interval a b) (S.transactionEnds ((P_set \ {P₃}) ∪ {Q₃}))) :
    False := by
  let P_set' : Set (Graph α β) := (P_set \ {P₃}) ∪ {Q₃}
  -- Extract the witness paths `P₁, P₂, P₃` from `hcov₁, hcov₂, hcov₃`.
  have hcov₂' : S.IsHalfCovered P_set Q₂ := hcov₂
  rcases hcov₁ with ⟨P₁, hP₁_in, _, _, s₁, t₁, a₁', b₁', _, hP₁_ends, hQ₁_ends', rfl, _, _⟩
  rcases hcov₂ with ⟨P₂, hP₂_in, _, _, s₂, t₂, a₂', b₂', _, hP₂_ends, hQ₂_ends', rfl, _, _⟩
  rcases hcov₃ with ⟨P₃', hP₃'_in, _, huniq₃, s₃, t₃, a₃', b₃', _, hP₃'_ends, hQ₃_ends', rfl, _, _⟩
  have hP₃_eq : P₃ = P₃' := huniq₃ P₃ hP₃_in hmeet₃
  subst hP₃_eq
  have hs₁_xy : s₁ = x₁ ∨ s₁ = y₁ := by
    rcases hQ₁_ends.ends_eq S hQ₁_ends' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hs₂_xy : s₂ = x₂ ∨ s₂ = y₂ := by
    rcases hQ₂_ends.ends_eq S hQ₂_ends' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hs₃_xy : s₃ = x₃ ∨ s₃ = y₃ := by
    rcases hQ₃_ends.ends_eq S hQ₃_ends' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hs₁_2 : s₁ ∈ S.Ω.interval x₂ y₂ := by
    rcases hs₁_xy with rfl | rfl
    · exact hx₁_2
    · exact hy₁_2
  have hs₁_3 : s₁ ∈ S.Ω.interval x₃ y₃ := by
    rcases hs₁_xy with rfl | rfl
    · exact hx₁_3
    · exact hy₁_3
  have hs₂_3 : s₂ ∈ S.Ω.interval x₃ y₃ := by
    rcases hs₂_xy with rfl | rfl
    · exact hx₂_3
    · exact hy₂_3
  have hs₃_2 : s₃ ∈ S.Ω.interval y₂ x₂ := by
    rcases hs₃_xy with rfl | rfl
    · exact hx₃_2
    · exact hy₃_2
  rcases hcase with hdisj_3 | ⟨P, hP_diff, a, haU, b, hbV, hP_ends, hdisj_ab⟩
  · -- Case 1: `Q₃` is peripheral in `P_set'` with `S.Ω.interval x₃ y₃` empty.
    have hP₁_eq : P₁ = P₃ := by
      by_contra hne
      have hP₁_in' : P₁ ∈ P_set' := Or.inl ⟨hP₁_in, hne⟩
      have hs₁_W' : s₁ ∈ S.transactionEnds P_set' :=
        hP₁_ends.mem_transactionEnds_left S hP₁_in'
      exact disjoint_left.mp hdisj_3 hs₁_3 hs₁_W'
    have hP₂_eq : P₂ = P₃ := by
      by_contra hne
      have hP₂_in' : P₂ ∈ P_set' := Or.inl ⟨hP₂_in, hne⟩
      have hs₂_W' : s₂ ∈ S.transactionEnds P_set' :=
        hP₂_ends.mem_transactionEnds_left S hP₂_in'
      exact disjoint_left.mp hdisj_3 hs₂_3 hs₂_W'
    subst hP₁_eq hP₂_eq
    have hs₁_P : s₁ = s₃ ∨ s₁ = t₃ := by
      rcases hP₃'_ends.ends_eq S hP₁_ends with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr h
    have hs₂_P : s₂ = s₃ ∨ s₂ = t₃ := by
      rcases hP₃'_ends.ends_eq S hP₂_ends with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr h
    exact S.not_shares_end_with_three hQ₁_ends hQ₂_ends hQ₃_ends hdisj_12 hdisj_13 hdisj_23
      hP₃'_ends hs₁_P hs₂_P (Or.inl rfl) hs₁_xy hs₂_xy hs₃_xy
  · -- Case 2: Some `P ∈ P_set \ {P₃}` is peripheral in `P_set'` with `S.Ω.interval a b` empty.
    rcases hfence.2.1.interval_subset_or_subset_or_cross S.Ω haU hbV hx₂ hy₂ with
      hab_sub | hx₂y₂_sub | ⟨ha_2, hb_2⟩ | ⟨hb_2, ha_2⟩
    · -- Subcase 2.1: `S.Ω.interval a b ⊆ S.Ω.interval x₂ y₂`.
      have hdisj_diff : Disjoint (S.Ω.interval a b) (S.transactionEnds (P_set \ {P₃})) := by
        refine hdisj_ab.mono_right ?_
        rintro v ⟨R, hR, hvR, hv_bar⟩
        exact ⟨R, Or.inl hR, hvR, hv_bar⟩
      obtain ⟨u₃, hu₃U, v₃, hv₃V, hP₃_uv⟩ := hfence.2.2 P₃ hP₃_in
      have hu₃_or_v₃ : u₃ ∈ S.Ω.interval a b ∨ v₃ ∈ S.Ω.interval a b := by
        rcases S.mem_interval_of_peripheral_diff_singleton hfence hcrooked
          hP₃_in hP_diff hu₃U hv₃V hP₃_uv haU hbV hP_ends hdisj_diff with ⟨h, _⟩ | ⟨h, _⟩
        · exact Or.inl h
        · exact Or.inr h
      have hs₃_or_t₃ : s₃ ∈ S.Ω.interval a b ∨ t₃ ∈ S.Ω.interval a b := by
        rcases hP₃'_ends.ends_eq S hP₃_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hu₃_or_v₃
        · exact hu₃_or_v₃.symm
      have hs₃_not_ab : s₃ ∉ S.Ω.interval a b := by
        have hs₃_W' : s₃ ∈ S.transactionEnds P_set' := by
          rcases hs₃_xy with rfl | rfl
          · exact hQ₃_ends.mem_transactionEnds_left S (Or.inr rfl)
          · exact hQ₃_ends.mem_transactionEnds_right S (Or.inr rfl)
        exact disjoint_right.mp hdisj_ab hs₃_W'
      have ht₃_ab : t₃ ∈ S.Ω.interval a b := hs₃_or_t₃.resolve_left hs₃_not_ab
      exact S.not_ends_in_both_intervals_of_separating_halfCovered
        hQ₂_ends hsep₂ hcov₂' hP₃_in (hP₃'_ends.symm S) (hab_sub ht₃_ab) hs₃_2
    · -- Subcase 2.2: `S.Ω.interval x₂ y₂ ⊆ S.Ω.interval a b`.
      have hs₁_ab : s₁ ∈ S.Ω.interval a b := hx₂y₂_sub hs₁_2
      have hP₁_eq : P₁ = P₃ := by
        by_contra hne
        have hP₁_in' : P₁ ∈ P_set' := Or.inl ⟨hP₁_in, hne⟩
        have hs₁_W' : s₁ ∈ S.transactionEnds P_set' :=
          hP₁_ends.mem_transactionEnds_left S hP₁_in'
        exact disjoint_left.mp hdisj_ab hs₁_ab hs₁_W'
      subst hP₁_eq
      have hs₁_ne_s₃ : s₁ ≠ s₃ := by
        have hs₁_V : s₁ ∈ V(Q₁) := by
          rcases hs₁_xy with rfl | rfl
          · exact hQ₁_ends.1.left_mem
          · exact hQ₁_ends.1.right_mem
        have hs₃_V : s₃ ∈ V(Q₃) := by
          rcases hs₃_xy with rfl | rfl
          · exact hQ₃_ends.1.left_mem
          · exact hQ₃_ends.1.right_mem
        exact fun h => disjoint_left.mp hdisj_13 hs₁_V (h ▸ hs₃_V)
      have hs₁_eq_t₃ : s₁ = t₃ := by
        rcases hP₃'_ends.ends_eq S hP₁_ends with ⟨h, _⟩ | ⟨h, _⟩
        · exact (hs₁_ne_s₃ h).elim
        · exact h
      subst hs₁_eq_t₃
      exact S.not_ends_in_both_intervals_of_separating_halfCovered
        hQ₂_ends hsep₂ hcov₂' hP₁_in (hP₃'_ends.symm S) hs₁_2 hs₃_2
    · -- Subcase 2.3: `a ∈ S.Ω.interval x₂ y₂` and `b ∈ S.Ω.interval y₂ x₂`.
      exact S.not_ends_in_both_intervals_of_separating_halfCovered
        hQ₂_ends hsep₂ hcov₂' hP_diff.1 hP_ends ha_2 hb_2
    · -- Subcase 2.4: `b ∈ S.Ω.interval x₂ y₂` and `a ∈ S.Ω.interval y₂ x₂`.
      exact S.not_ends_in_both_intervals_of_separating_halfCovered
        hQ₂_ends hsep₂ hcov₂' hP_diff.1 (hP_ends.symm S) hb_2 ha_2

/-- Symmetry of `StatementS` under swapping the fence sides `A` and `B`. -/
theorem StatementS.symm {p : ℕ} {P_set Q_set : Set (Graph α β)} {A B : Set α}
    (hS : S.StatementS p P_set Q_set A B) : S.StatementS p P_set Q_set B A where
  two_le_p := hS.two_le_p
  isTransaction_Q := hS.isTransaction_Q
  no_internal_in_bar := hS.no_internal_in_bar
  isCrooked_P := hS.isCrooked_P
  card_P_ge := hS.card_P_ge
  minimal_union := hS.minimal_union
  minimal_card := hS.minimal_card
  isFenceFor_P := ⟨hS.isFenceFor_P.1, hS.isFenceFor_P.2.1.symm, fun P hP => by
    obtain ⟨a, ha, b, hb, hab⟩ := hS.isFenceFor_P.2.2 P hP
    exact ⟨b, hb, a, ha, hab.symm S⟩⟩

private theorem replacement_of_half_covered_path {p : ℕ} {P_set Q_set : Set (Graph α β)}
    {U V : Set α} (hSUV : S.StatementS p P_set Q_set U V)
    {P₃ Q₃ : Graph α β} (hP₃_in : P₃ ∈ P_set) (hQ₃ : Q₃ ∈ Q_set)
    (hmeet₃ : (V(P₃) ∩ V(Q₃)).Nonempty)
    (huniq₃ : ∀ R ∈ P_set, (V(R) ∩ V(Q₃)).Nonempty → R = P₃)
    {s₃ t₃ a₃ b₃ b₃' : α}
    (hQ₃_ends : S.IsOmegaPathWithEnds Q₃ a₃ b₃) (ha₃U : a₃ ∈ U) (hb₃V : b₃ ∈ V)
    (hP₃_ends : S.IsOmegaPathWithEnds P₃ s₃ t₃) (hQ₃_ends' : S.IsOmegaPathWithEnds Q₃ s₃ b₃')
    (hb₃'_not_P : b₃' ∉ S.transactionEnds P_set) :
    let P_set' := (P_set \ {P₃}) ∪ {Q₃}
    S.IsFenceFor P_set' U V ∧ ¬ S.IsCrookedTransaction P_set' := by
  intro P_set'
  have hQ₃_not_diff : Q₃ ∉ P_set \ {P₃} := by
    intro hQ₃_diff
    have hdisj_P₃Q₃ : Disjoint V(P₃) V(Q₃) :=
      hSUV.isFenceFor_P.1.2 hP₃_in hQ₃_diff.1 (Ne.symm hQ₃_diff.2)
    exact disjoint_left.mp hdisj_P₃Q₃ hmeet₃.some_mem.1 hmeet₃.some_mem.2
  -- `(U, V)` is a fence for `P_set'`.
  have hfence_P' : S.IsFenceFor P_set' U V := by
    refine ⟨⟨?_, ?_⟩, hSUV.isFenceFor_P.2.1, ?_⟩
    · rintro R (hR | rfl)
      · exact hSUV.isFenceFor_P.1.1 R hR.1
      · exact ⟨a₃, b₃, hQ₃_ends⟩
    · rintro R₁ (hR₁ | rfl) R₂ (hR₂ | rfl) hne
      · exact hSUV.isFenceFor_P.1.2 hR₁.1 hR₂.1 hne
      · exact Disjoint.symm (by
          by_contra hnot
          rw [not_disjoint_iff_nonempty_inter] at hnot
          exact hR₁.2 (huniq₃ R₁ hR₁.1 (inter_comm V(R₂) V(R₁) ▸ hnot)))
      · by_contra hnot
        rw [not_disjoint_iff_nonempty_inter] at hnot
        exact hR₂.2 (huniq₃ R₂ hR₂.1 (inter_comm V(R₁) V(R₂) ▸ hnot))
      · exact (hne rfl).elim
    · rintro R (hR | rfl)
      · exact hSUV.isFenceFor_P.2.2 R hR.1
      · exact ⟨a₃, ha₃U, b₃, hb₃V, hQ₃_ends⟩
  -- `P_set'` is not crooked by minimality of `⋃ P_set ∪ ⋃ Q_set`.
  have hnot_crooked_P' : ¬ S.IsCrookedTransaction P_set' := by
    intro hcr'
    have hfin_P : P_set.Finite :=
      hSUV.isFenceFor_P.1.finite S
    have hcard_P' : P_set'.ncard = P_set.ncard := by
      rw [ncard_union_eq (disjoint_singleton_right.mpr hQ₃_not_diff)
        (hfin_P.subset sdiff_subset) (finite_singleton Q₃),
        ncard_singleton, ncard_sdiff_singleton_of_mem hP₃_in]
      have := hSUV.two_le_p
      have := hSUV.card_P_ge
      omega
    have hP_le : ∀ M ∈ P_set, M ≤ S.G :=
      fun M hM => let ⟨_, _, h⟩ := hSUV.isFenceFor_P.1.1 M hM; h.1.1
    have hQ_le : ∀ M ∈ Q_set, M ≤ S.G := by
      obtain ⟨_, _, hfQ⟩ := hSUV.isTransaction_Q
      exact fun M hM => let ⟨_, _, h⟩ := hfQ.1.1 M hM; h.1.1
    have hP'_le : ∀ M ∈ P_set', M ≤ S.G := by
      rintro M (hM | rfl)
      · exact hP_le M hM.1
      · exact hQ_le M hQ₃
    have hUP_le : S.transactionUnion P_set ≤ S.G := subgraphSUnion_le hP_le
    have hUP'_le : S.transactionUnion P_set' ≤ S.G := subgraphSUnion_le hP'_le
    have hUQ_le : S.transactionUnion Q_set ≤ S.G := subgraphSUnion_le hQ_le
    have hle_union :
        subgraphUnion S.G (S.transactionUnion P_set') (S.transactionUnion Q_set) ≤
          subgraphUnion S.G (S.transactionUnion P_set) (S.transactionUnion Q_set) := by
      rw [subgraphUnion_le_iff hUP'_le hUQ_le (subgraphUnion_le hUP_le hUQ_le)]
      refine ⟨?_, le_subgraphUnion_right hUP_le hUQ_le⟩
      rw [(Compatible.of_le_le hUP'_le (subgraphUnion_le hUP_le hUQ_le)).le_iff]
      refine ⟨?_, ?_⟩
      · intro v hv
        change v ∈ ⋃ M ∈ P_set', V(M) at hv
        rw [vertexSet_subgraphUnion]
        rcases mem_iUnion₂.mp hv with ⟨R, hR | rfl, hvR⟩
        · exact Or.inl (mem_iUnion₂.mpr ⟨R, hR.1, hvR⟩)
        · exact Or.inr (mem_iUnion₂.mpr ⟨R, hQ₃, hvR⟩)
      · rw [show E(S.transactionUnion P_set') = ⋃ M ∈ P_set', E(M) from edgeSet_subgraphSUnion
        hP'_le,
          edgeSet_subgraphUnion hUP_le hUQ_le,
          show E(S.transactionUnion P_set) = ⋃ M ∈ P_set, E(M) from edgeSet_subgraphSUnion hP_le,
          show E(S.transactionUnion Q_set) = ⋃ M ∈ Q_set, E(M) from edgeSet_subgraphSUnion hQ_le]
        intro e he
        rcases mem_iUnion₂.mp he with ⟨R, hR | rfl, heR⟩
        · exact Or.inl (mem_iUnion₂.mpr ⟨R, hR.1, heR⟩)
        · exact Or.inr (mem_iUnion₂.mpr ⟨R, hQ₃, heR⟩)
    have heq_union := hSUV.minimal_union P_set' hcr' (hcard_P' ▸ hSUV.card_P_ge) hle_union
    -- Every edge of `P₃` lies in `E(S.transactionUnion Q_set)`.
    have hEP₃_sub_UQ : E(P₃) ⊆ E(S.transactionUnion Q_set) := by
      intro e heP₃
      have he_rhs : e ∈ E(subgraphUnion S.G (S.transactionUnion P_set) (S.transactionUnion Q_set))
        := by
        rw [edgeSet_subgraphUnion hUP_le hUQ_le]
        exact Or.inl ((le_subgraphSUnion hP_le hP₃_in).edgeSet_mono heP₃)
      rw [← heq_union, edgeSet_subgraphUnion hUP'_le hUQ_le] at he_rhs
      rcases he_rhs with heP' | heQ
      · rw [show E(S.transactionUnion P_set') = ⋃ M ∈ P_set', E(M) from
          edgeSet_subgraphSUnion hP'_le] at heP'
        rcases mem_iUnion₂.mp heP' with ⟨R, hR | rfl, heR⟩
        · exfalso
          obtain ⟨x₃, y₃, hxy₃⟩ := P₃.exists_isLink_of_mem_edgeSet heP₃
          obtain ⟨xR, yR, hxyR⟩ := R.exists_isLink_of_mem_edgeSet heR
          have hxy₃G : S.G.IsLink e x₃ y₃ := hxy₃.mono (hP_le P₃ hP₃_in)
          have hxyRG : S.G.IsLink e xR yR := hxyR.mono (hP_le R hR.1)
          rcases hxy₃G.left_eq_or_eq hxyRG with rfl | rfl
          · exact disjoint_left.mp (hSUV.isFenceFor_P.1.2 hP₃_in hR.1 (Ne.symm hR.2))
              hxy₃.left_mem hxyR.left_mem
          · exact disjoint_left.mp (hSUV.isFenceFor_P.1.2 hP₃_in hR.1 (Ne.symm hR.2))
              hxy₃.left_mem hxyR.right_mem
        · exact (le_subgraphSUnion hQ_le hQ₃).edgeSet_mono heR
      · exact heQ
    -- Since `P₃` is a path starting at `s₃ ∈ V(Q₃)` and `Q_set` is pairwise vertex-disjoint, `t₃
    -- ∈ V(Q₃)`.
    have ht₃_in_Q₃ : t₃ ∈ V(Q₃) := by
      rcases hP₃_ends.1 with ⟨hP₃_le, W₃, _, hVP₃, hEP₃⟩
      have hs₃_in_Q₃ : s₃ ∈ V(Q₃) := hQ₃_ends'.1.left_mem
      have h_ind : ∀ {u_w v_w : α} (W : GraphWalk P₃ u_w v_w),
          (∀ e ∈ W.edges, e ∈ E(P₃)) → u_w ∈ V(Q₃) → v_w ∈ V(Q₃) := by
        intro u_w v_w W
        induction W with
        | nil _ =>
          intro _ hu
          exact hu
        | @cons u_c w_c _ e_c he_c W_tail ih =>
          intro hW_edges hu_Q₃
          have he_P₃ : e_c ∈ E(P₃) := hW_edges e_c List.mem_cons_self
          have he_UQ : e_c ∈ ⋃ M ∈ Q_set, E(M) := by
            have h := hEP₃_sub_UQ he_P₃
            rwa [show E(S.transactionUnion Q_set) = ⋃ M ∈ Q_set, E(M) from
              edgeSet_subgraphSUnion hQ_le] at h
          obtain ⟨M, hM_in, he_M⟩ := mem_iUnion₂.mp he_UQ
          obtain ⟨x_M, y_M, hxy_M⟩ := M.exists_isLink_of_mem_edgeSet he_M
          have hxy_G : S.G.IsLink e_c x_M y_M := hxy_M.mono (hQ_le M hM_in)
          have he_G : S.G.IsLink e_c u_c w_c := he_c.mono hP₃_le
          have hu_M : u_c ∈ V(M) := by
            rcases he_G.left_eq_or_eq hxy_G with rfl | rfl
            · exact hxy_M.left_mem
            · exact hxy_M.right_mem
          have hw_M : w_c ∈ V(M) := by
            rcases he_G.symm.left_eq_or_eq hxy_G with rfl | rfl
            · exact hxy_M.left_mem
            · exact hxy_M.right_mem
          have hMQ₃ : M = Q₃ := by
            by_contra hne
            exact disjoint_left.mp
              (hSUV.isTransaction_Q.choose_spec.choose_spec.1.2 hM_in hQ₃ hne) hu_M hu_Q₃
          subst hMQ₃
          exact ih (fun e he => hW_edges e (List.mem_cons_of_mem e_c he)) hw_M
      exact h_ind W₃ (fun e he => by rwa [hEP₃, mem_ofPred_eq]) hs₃_in_Q₃
    have ht₃_ends_Q₃ : t₃ ∈ pathEnds S.G Q₃ := by
      by_contra ht₃_not_end
      exact disjoint_left.mp (hSUV.no_internal_in_bar Q₃ hQ₃)
        ⟨ht₃_in_Q₃, ht₃_not_end⟩ hP₃_ends.2.2.2
    rw [hQ₃_ends'.1.pathEnds_eq, mem_insert_iff, mem_singleton_iff] at ht₃_ends_Q₃
    rcases ht₃_ends_Q₃ with rfl | rfl
    · obtain ⟨u₃, hu₃U, v₃, hv₃V, hP₃_uv⟩ := hSUV.isFenceFor_P.2.2 P₃ hP₃_in
      have huv_ne : u₃ ≠ v₃ := fun h =>
        disjoint_left.mp hSUV.isFenceFor_P.2.1.2.2.1 hu₃U (h ▸ hv₃V)
      rcases hP₃_ends.ends_eq S hP₃_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact huv_ne rfl
      · exact huv_ne rfl
    · exact hb₃'_not_P (hP₃_ends.mem_transactionEnds_right S hP₃_in)
  exact ⟨hfence_P', hnot_crooked_P'⟩

/-- **Graph Minors IX, (4.5)** (pages 51–52):
"(4.5) *Let S be true, and let $Q_1, Q_2, Q_3, Q_4, Q_5 \in \mathscr{Q}$ be in order. Suppose that
$Q_2, Q_3, Q_4$ are all separating. Then not all of $Q_1, ..., Q_5$ are half-covered.*" -/
theorem theorem_4_5_proof {p : ℕ} {P_set Q_set : Set (Graph α β)} {A B : Set α}
    (hS : S.StatementS p P_set Q_set A B)
    {Q₁ Q₂ Q₃ Q₄ Q₅ : Graph α β}
    (_hQ₁ : Q₁ ∈ Q_set) (_hQ₂ : Q₂ ∈ Q_set) (hQ₃ : Q₃ ∈ Q_set)
    (_hQ₄ : Q₄ ∈ Q_set) (_hQ₅ : Q₅ ∈ Q_set)
    (hord : S.AreInOrder [Q₁, Q₂, Q₃, Q₄, Q₅])
    (hsep₂ : S.IsSeparatingOmegaPath Q₂)
    (hsep₃ : S.IsSeparatingOmegaPath Q₃)
    (hsep₄ : S.IsSeparatingOmegaPath Q₄) :
    ¬ (S.IsHalfCovered P_set Q₁ ∧ S.IsHalfCovered P_set Q₂ ∧ S.IsHalfCovered P_set Q₃ ∧
       S.IsHalfCovered P_set Q₄ ∧ S.IsHalfCovered P_set Q₅) := by
  rintro ⟨hcov₁, hcov₂, hcov₃, hcov₄, hcov₅⟩
  rcases hord with ⟨hpair, a_l, b_l, ha_len, hb_len, hends, hcw⟩
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at ha_len hb_len
  rcases a_l with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, _ | ⟨a₄, _ | ⟨a₅, _ | _⟩⟩⟩⟩⟩ <;> simp at ha_len
  rcases b_l with _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, _ | ⟨b₄, _ | ⟨b₅, _ | _⟩⟩⟩⟩⟩ <;> simp at hb_len
  have hQ₁_ends : S.IsOmegaPathWithEnds Q₁ a₁ b₁ := hends 0 (by simp)
  have hQ₂_ends : S.IsOmegaPathWithEnds Q₂ a₂ b₂ := hends 1 (by simp)
  have hQ₃_ends : S.IsOmegaPathWithEnds Q₃ a₃ b₃ := hends 2 (by simp)
  have hQ₄_ends : S.IsOmegaPathWithEnds Q₄ a₄ b₄ := hends 3 (by simp)
  have hQ₅_ends : S.IsOmegaPathWithEnds Q₅ a₅ b₅ := hends 4 (by simp)
  -- Helper to extract interval memberships from indices in `[a₅, a₄, a₃, a₂, a₁, b₁, b₂, b₃, b₄,
  -- b₅]`.
  have hmem_int : ∀ (i₁ i₂ i₃ : ℕ) (h12 : i₁ < i₂) (h23 : i₂ < i₃)
      (h3 : i₃ < [a₅, a₄, a₃, a₂, a₁, b₁, b₂, b₃, b₄, b₅].length),
      [a₅, a₄, a₃, a₂, a₁, b₁, b₂, b₃, b₄, b₅][i₂]'(Nat.lt_trans h23 h3) ∈
        S.Ω.interval
          ([a₅, a₄, a₃, a₂, a₁, b₁, b₂, b₃, b₄, b₅][i₁]'(Nat.lt_trans h12 (Nat.lt_trans h23 h3)))
          ([a₅, a₄, a₃, a₂, a₁, b₁, b₂, b₃, b₄, b₅][i₃]'h3) :=
    fun i₁ i₂ i₃ h12 h23 h3 => S.Ω.mem_interval_of_lt hcw h12 h23 h3
  -- Interval memberships for `(Q₁, Q₂, Q₃)`:
  have ha₁_2 : a₁ ∈ S.Ω.interval a₂ b₂ := hmem_int 3 4 6 (by decide) (by decide) (by simp)
  have hb₁_2 : b₁ ∈ S.Ω.interval a₂ b₂ := hmem_int 3 5 6 (by decide) (by decide) (by simp)
  have ha₁_3 : a₁ ∈ S.Ω.interval a₃ b₃ := hmem_int 2 4 7 (by decide) (by decide) (by simp)
  have hb₁_3 : b₁ ∈ S.Ω.interval a₃ b₃ := hmem_int 2 5 7 (by decide) (by decide) (by simp)
  have ha₂_3 : a₂ ∈ S.Ω.interval a₃ b₃ := hmem_int 2 3 7 (by decide) (by decide) (by simp)
  have hb₂_3 : b₂ ∈ S.Ω.interval a₃ b₃ := hmem_int 2 6 7 (by decide) (by decide) (by simp)
  have ha₃_2 : a₃ ∈ S.Ω.interval b₂ a₂ :=
    S.Ω.mem_interval_rotate_right (hmem_int 2 3 6 (by decide) (by decide) (by simp))
  have hb₃_2 : b₃ ∈ S.Ω.interval b₂ a₂ :=
    S.Ω.mem_interval_rotate_left (hmem_int 3 6 7 (by decide) (by decide) (by simp))
  have hb₂_a₂b₃ : b₂ ∈ S.Ω.interval a₂ b₃ := hmem_int 3 6 7 (by decide) (by decide) (by simp)
  -- Interval memberships for `(Q₅, Q₄, Q₃)` with swapped ends `(bᵢ, aᵢ)`:
  have hb₅_4 : b₅ ∈ S.Ω.interval b₄ a₄ :=
    S.Ω.mem_interval_rotate_left (hmem_int 1 8 9 (by decide) (by decide) (by simp))
  have ha₅_4 : a₅ ∈ S.Ω.interval b₄ a₄ :=
    S.Ω.mem_interval_rotate_right (hmem_int 0 1 8 (by decide) (by decide) (by simp))
  have hb₅_3 : b₅ ∈ S.Ω.interval b₃ a₃ :=
    S.Ω.mem_interval_rotate_left (hmem_int 2 7 9 (by decide) (by decide) (by simp))
  have ha₅_3 : a₅ ∈ S.Ω.interval b₃ a₃ :=
    S.Ω.mem_interval_rotate_right (hmem_int 0 2 7 (by decide) (by decide) (by simp))
  have hb₄_3 : b₄ ∈ S.Ω.interval b₃ a₃ :=
    S.Ω.mem_interval_rotate_left (hmem_int 2 7 8 (by decide) (by decide) (by simp))
  have ha₄_3 : a₄ ∈ S.Ω.interval b₃ a₃ :=
    S.Ω.mem_interval_rotate_right (hmem_int 1 2 7 (by decide) (by decide) (by simp))
  have hb₃_4 : b₃ ∈ S.Ω.interval a₄ b₄ := hmem_int 1 7 8 (by decide) (by decide) (by simp)
  have ha₃_4 : a₃ ∈ S.Ω.interval a₄ b₄ := hmem_int 1 2 8 (by decide) (by decide) (by simp)
  have ha₄_b₄a₃ : a₄ ∈ S.Ω.interval b₄ a₃ :=
    S.Ω.mem_interval_rotate_right (hmem_int 1 2 8 (by decide) (by decide) (by simp))
  -- Pairwise disjointness of `Q₁, Q₂, Q₃, Q₄, Q₅`.
  have hdisj : ∀ (i j : ℕ) (hi : i < 5) (hj : j < 5), i < j →
      Disjoint V([Q₁, Q₂, Q₃, Q₄, Q₅][i]'hi) V([Q₁, Q₂, Q₃, Q₄, Q₅][j]'hj) :=
    List.pairwise_iff_getElem.mp hpair
  have hdisj_12 : Disjoint V(Q₁) V(Q₂) := hdisj 0 1 (by decide) (by decide) (by decide)
  have hdisj_13 : Disjoint V(Q₁) V(Q₃) := hdisj 0 2 (by decide) (by decide) (by decide)
  have hdisj_23 : Disjoint V(Q₂) V(Q₃) := hdisj 1 2 (by decide) (by decide) (by decide)
  have hdisj_34 : Disjoint V(Q₃) V(Q₄) := hdisj 2 3 (by decide) (by decide) (by decide)
  have hdisj_35 : Disjoint V(Q₃) V(Q₅) := hdisj 2 4 (by decide) (by decide) (by decide)
  have hdisj_45 : Disjoint V(Q₄) V(Q₅) := hdisj 3 4 (by decide) (by decide) (by decide)
  -- By the proof of (4.4), each of `Q₂, Q₃, Q₄` has one end in `A` and one end in `B`.
  have hends_AB : ∀ {Q_a Q_m Q_b : Graph α β} {x_a y_a x_m y_m x_b y_b : α},
      S.IsOmegaPathWithEnds Q_a x_a y_a →
      S.IsOmegaPathWithEnds Q_m x_m y_m →
      S.IsOmegaPathWithEnds Q_b x_b y_b →
      S.IsSeparatingOmegaPath Q_m →
      S.IsHalfCovered P_set Q_a →
      S.IsHalfCovered P_set Q_m →
      S.IsHalfCovered P_set Q_b →
      x_a ∈ S.Ω.interval x_m y_m → y_a ∈ S.Ω.interval x_m y_m →
      x_b ∈ S.Ω.interval y_m x_m → y_b ∈ S.Ω.interval y_m x_m →
      (x_m ∈ A ∧ y_m ∈ B) ∨ (x_m ∈ B ∧ y_m ∈ A) := by
    intro Q_a Q_m Q_b x_a y_a x_m y_m x_b y_b hQa hQm hQb hsep_m hc_a hc_m hc_b
      hxa hym hxb hyb
    have hnot_both : ∀ {U V : Set α}, S.IsFenceFor P_set U V → x_m ∈ U → y_m ∈ U → False := by
      intro U V hfenceU hxmU hymU
      rcases S.subset_interval_or_swap hfenceU.2.1 hxmU hymU hQm.2.1 with hV_ab | hV_ba
      · rcases hc_b with ⟨P_b, hPb_in, _, _, s_b, t_b, _, _, _, hPb_ends, hQb', rfl, _, _⟩
        have hsb_ba : s_b ∈ S.Ω.interval y_m x_m := by
          rcases hQb.ends_eq S hQb' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hxb
          · exact hyb
        have hsb_not_V : s_b ∉ V :=
          fun hsV => disjoint_left.mp (S.Ω.disjoint_interval_swap x_m y_m) (hV_ab hsV) hsb_ba
        obtain ⟨u_b, _, v_b, hvV, hPb_uv⟩ := hfenceU.2.2 P_b hPb_in
        have htb_V : t_b ∈ V := by
          rcases hPb_ends.ends_eq S hPb_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hvV
          · exact (hsb_not_V hvV).elim
        exact S.not_ends_in_both_intervals_of_separating_halfCovered
          hQm hsep_m hc_m hPb_in (hPb_ends.symm S) (hV_ab htb_V) hsb_ba
      · rcases hc_a with ⟨P_a, hPa_in, _, _, s_a, t_a, _, _, _, hPa_ends, hQa', rfl, _, _⟩
        have hsa_ab : s_a ∈ S.Ω.interval x_m y_m := by
          rcases hQa.ends_eq S hQa' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hxa
          · exact hym
        have hsa_not_V : s_a ∉ V :=
          fun hsV => disjoint_left.mp (S.Ω.disjoint_interval_swap x_m y_m) hsa_ab (hV_ba hsV)
        obtain ⟨u_a, _, v_a, hvV, hPa_uv⟩ := hfenceU.2.2 P_a hPa_in
        have hta_V : t_a ∈ V := by
          rcases hPa_ends.ends_eq S hPa_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hvV
          · exact (hsa_not_V hvV).elim
        exact S.not_ends_in_both_intervals_of_separating_halfCovered
          hQm hsep_m hc_m hPa_in hPa_ends hsa_ab (hV_ba hta_V)
    have hxm_AB : x_m ∈ A ∪ B := by
      rw [hS.isFenceFor_P.2.1.2.2.2.1]; exact hQm.2.2.1
    have hym_AB : y_m ∈ A ∪ B := by
      rw [hS.isFenceFor_P.2.1.2.2.2.1]; exact hQm.2.2.2
    rcases hxm_AB with hxmA | hxmB <;> rcases hym_AB with hymA | hymB
    · exact (hnot_both hS.isFenceFor_P hxmA hymA).elim
    · exact Or.inl ⟨hxmA, hymB⟩
    · exact Or.inr ⟨hxmB, hymA⟩
    · exact (hnot_both hS.symm.isFenceFor_P hxmB hymB).elim
  have hQ₂_AB : (a₂ ∈ A ∧ b₂ ∈ B) ∨ (a₂ ∈ B ∧ b₂ ∈ A) :=
    hends_AB hQ₁_ends hQ₂_ends hQ₃_ends hsep₂ hcov₁ hcov₂ hcov₃ ha₁_2 hb₁_2 ha₃_2 hb₃_2
  have hQ₃_AB : (a₃ ∈ A ∧ b₃ ∈ B) ∨ (a₃ ∈ B ∧ b₃ ∈ A) :=
    hends_AB hQ₂_ends hQ₃_ends hQ₄_ends hsep₃ hcov₂ hcov₃ hcov₄ ha₂_3 hb₂_3 ha₄_3 hb₄_3
  have hQ₄_AB : (a₄ ∈ A ∧ b₄ ∈ B) ∨ (a₄ ∈ B ∧ b₄ ∈ A) :=
    hends_AB hQ₃_ends hQ₄_ends hQ₅_ends hsep₄ hcov₃ hcov₄ hcov₅ ha₃_4 hb₃_4 ha₅_4 hb₅_4
  -- Choose `(U, V) ∈ {(A, B), (B, A)}` so that `a₃ ∈ U` and `b₃ ∈ V`.
  have hmain : ∀ {U V : Set α}, S.StatementS p P_set Q_set U V →
      a₃ ∈ U → b₃ ∈ V →
      (a₂ ∈ U ∧ b₂ ∈ V ∨ a₂ ∈ V ∧ b₂ ∈ U) →
      (a₄ ∈ U ∧ b₄ ∈ V ∨ a₄ ∈ V ∧ b₄ ∈ U) → False := by
    intro U V hSUV ha₃U hb₃V hQ₂_UV hQ₄_UV
    have ⟨ha₂U, hb₂V⟩ := hSUV.isFenceFor_P.2.1.same_side_of_mem_interval S.Ω
      ha₃U hb₃V hQ₂_UV ha₂_3 hb₂_a₂b₃
    have ⟨hb₄V, ha₄U⟩ := hSUV.isFenceFor_P.2.1.symm.same_side_of_mem_interval S.Ω
      hb₃V ha₃U (hQ₄_UV.imp And.symm And.symm) hb₄_3 ha₄_b₄a₃
    -- Let `P₃` be the unique member of `P_set` meeting `Q₃`.
    have hcov₃' : S.IsHalfCovered P_set Q₃ := hcov₃
    rcases hcov₃ with ⟨P₃, hP₃_in, hmeet₃, huniq₃, s₃, t₃, a₃', b₃', _, hP₃_ends, hQ₃_ends',
      rfl, hb₃'_not_P, _⟩
    let P_set' : Set (Graph α β) := (P_set \ {P₃}) ∪ {Q₃}
    obtain ⟨hfence_P', hnot_crooked_P'⟩ :=
      replacement_of_half_covered_path S hSUV hP₃_in hQ₃ hmeet₃ huniq₃
        hQ₃_ends ha₃U hb₃V hP₃_ends hQ₃_ends' hb₃'_not_P
    -- Since `P_set'` is a transaction and not crooked, some `R ∈ P_set'` is peripheral in `P_set'`.
    have hex_periph : ∃ R ∈ P_set', S.IsPeripheralIn P_set' R := by
      by_contra hno
      push Not at hno
      exact hnot_crooked_P' ⟨⟨U, V, hfence_P'⟩, hno⟩
    rcases hex_periph with ⟨R, hR_diff | rfl, hperiph⟩
    · -- `R ∈ P_set \ {P₃}` is peripheral in `P_set'`.
      obtain ⟨a, haU, b, hbV, hR_ab⟩ := hSUV.isFenceFor_P.2.2 R hR_diff.1
      rcases hperiph with ⟨_, a', b', hR_a'b', hdisj_int⟩
      have hdisj_ab_or_ba :
          Disjoint (S.Ω.interval a b) (S.transactionEnds P_set') ∨
            Disjoint (S.Ω.interval b a) (S.transactionEnds P_set') := by
        rcases hR_ab.ends_eq S hR_a'b' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hdisj_int
        · exact hdisj_int.symm
      rcases hdisj_ab_or_ba with hdisj_ab | hdisj_ba
      · exact S.half_covered_side_contradiction hSUV.isFenceFor_P hSUV.isCrooked_P hP₃_in
          hQ₁_ends hQ₂_ends hQ₃_ends ha₂U hb₂V ha₃U hb₃V
          ha₁_2 hb₁_2 ha₁_3 hb₁_3 ha₂_3 hb₂_3 ha₃_2 hb₃_2
          hdisj_12 hdisj_13 hdisj_23 hsep₂ hcov₁ hcov₂ hcov₃'
          hmeet₃ (Or.inr ⟨R, hR_diff, a, haU, b, hbV, hR_ab, hdisj_ab⟩)
      · exact S.half_covered_side_contradiction hSUV.symm.isFenceFor_P hSUV.isCrooked_P hP₃_in
          (hQ₅_ends.symm S) (hQ₄_ends.symm S) (hQ₃_ends.symm S) hb₄V ha₄U hb₃V ha₃U
          hb₅_4 ha₅_4 hb₅_3 ha₅_3 hb₄_3 ha₄_3 hb₃_4 ha₃_4
          hdisj_45.symm hdisj_35.symm hdisj_34.symm hsep₄ hcov₅ hcov₄ hcov₃'
          hmeet₃ (Or.inr ⟨R, hR_diff, b, hbV, a, haU, hR_ab.symm S, hdisj_ba⟩)
    · -- `Q₃` is peripheral in `P_set'`.
      rcases hperiph with ⟨_, a', b', hQ₃_a'b', hdisj_int⟩
      have hdisj_ab_or_ba :
          Disjoint (S.Ω.interval a₃ b₃) (S.transactionEnds P_set') ∨
            Disjoint (S.Ω.interval b₃ a₃) (S.transactionEnds P_set') := by
        rcases hQ₃_ends.ends_eq S hQ₃_a'b' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hdisj_int
        · exact hdisj_int.symm
      rcases hdisj_ab_or_ba with hdisj_ab | hdisj_ba
      · exact S.half_covered_side_contradiction hSUV.isFenceFor_P hSUV.isCrooked_P hP₃_in
          hQ₁_ends hQ₂_ends hQ₃_ends ha₂U hb₂V ha₃U hb₃V
          ha₁_2 hb₁_2 ha₁_3 hb₁_3 ha₂_3 hb₂_3 ha₃_2 hb₃_2
          hdisj_12 hdisj_13 hdisj_23 hsep₂ hcov₁ hcov₂ hcov₃'
          hmeet₃ (Or.inl hdisj_ab)
      · exact S.half_covered_side_contradiction hSUV.symm.isFenceFor_P hSUV.isCrooked_P hP₃_in
          (hQ₅_ends.symm S) (hQ₄_ends.symm S) (hQ₃_ends.symm S) hb₄V ha₄U hb₃V ha₃U
          hb₅_4 ha₅_4 hb₅_3 ha₅_3 hb₄_3 ha₄_3 hb₃_4 ha₃_4
          hdisj_45.symm hdisj_35.symm hdisj_34.symm hsep₄ hcov₅ hcov₄ hcov₃'
          hmeet₃ (Or.inl hdisj_ba)
  rcases hQ₃_AB with ⟨ha₃A, hb₃B⟩ | ⟨ha₃B, hb₃A⟩
  · exact hmain hS ha₃A hb₃B hQ₂_AB hQ₄_AB
  · exact hmain hS.symm ha₃B hb₃A hQ₂_AB.symm hQ₄_AB.symm

/-! ## Proof of (4.6) (page 52) -/

/-- Under Statement **S** with `p ≠ 3`, `|P_set| = p` by `(3.4)` and minimality of `|P_set|`. -/
theorem StatementS.card_P_eq {p : ℕ} {P_set Q_set : Set (Graph α β)} {A B : Set α}
    (hS : S.StatementS p P_set Q_set A B) (hp3 : p ≠ 3) :
    P_set.ncard = p := by
  obtain ⟨P_set', hsub, hcard_eq, hcr'⟩ :=
    S.theorem_3_4_proof hS.two_le_p hp3 hS.isCrooked_P hS.card_P_ge
  have hP_le : ∀ M ∈ P_set, M ≤ S.G :=
    fun M hM => let ⟨_, _, h⟩ := hS.isFenceFor_P.1.1 M hM; h.1.1
  have hP'_le : ∀ M ∈ P_set', M ≤ S.G := fun M hM => hP_le M (hsub hM)
  have hQ_le : ∀ M ∈ Q_set, M ≤ S.G := by
    obtain ⟨_, _, hfQ⟩ := hS.isTransaction_Q
    exact fun M hM => let ⟨_, _, h⟩ := hfQ.1.1 M hM; h.1.1
  have hUP_le : S.transactionUnion P_set ≤ S.G := subgraphSUnion_le hP_le
  have hUP'_le : S.transactionUnion P_set' ≤ S.G := subgraphSUnion_le hP'_le
  have hUQ_le : S.transactionUnion Q_set ≤ S.G := subgraphSUnion_le hQ_le
  have hle_union :
      subgraphUnion S.G (S.transactionUnion P_set') (S.transactionUnion Q_set) ≤
        subgraphUnion S.G (S.transactionUnion P_set) (S.transactionUnion Q_set) :=
    (subgraphUnion_le_iff hUP'_le hUQ_le (subgraphUnion_le hUP_le hUQ_le)).mpr
      ⟨(subgraphSUnion_mono hP_le hsub).trans (le_subgraphUnion_left hUP_le hUQ_le),
       le_subgraphUnion_right hUP_le hUQ_le⟩
  have heq_union := hS.minimal_union P_set' hcr' (by omega) hle_union
  have hle_card := hS.minimal_card P_set' hcr' (by omega) heq_union
  have := hS.card_P_ge
  omega

/-- If `F` is a finite set of pairwise vertex-disjoint graphs and each `Q ∈ F` has at least `k`
vertices in a finite set `W`, then `⋃ Q ∈ F, (V(Q) ∩ W)` has at least `k * F.ncard` vertices. -/
theorem mul_ncard_le_ncard_biUnion {F : Set (Graph α β)} {W : Set α} {k : ℕ}
    (hfin_F : F.Finite) (hfin_W : W.Finite)
    (hdisj : F.PairwiseDisjoint (fun Q => V(Q)))
    (hk : ∀ Q ∈ F, k ≤ (V(Q) ∩ W).ncard) :
    k * F.ncard ≤ (⋃ Q ∈ F, (V(Q) ∩ W)).ncard := by
  induction F, hfin_F using Set.Finite.induction_on with
  | empty => simp
  | @insert Q F hQ_not hfin ih =>
    have hdisj_F : F.PairwiseDisjoint (fun R => V(R)) :=
      hdisj.subset (subset_insert Q F)
    have hk_F : ∀ R ∈ F, k ≤ (V(R) ∩ W).ncard :=
      fun R hR => hk R (mem_insert_of_mem Q hR)
    have ih' := ih hdisj_F hk_F
    have hk_Q : k ≤ (V(Q) ∩ W).ncard := hk Q (mem_insert Q F)
    rw [biUnion_insert, ncard_insert_of_notMem hQ_not hfin]
    have hdisj_QW : Disjoint (V(Q) ∩ W) (⋃ R ∈ F, (V(R) ∩ W)) := by
      rw [disjoint_left]
      intro v hvQ hvF
      simp only [mem_iUnion, exists_prop] at hvF
      rcases hvF with ⟨R, hR, hvR⟩
      have hne : Q ≠ R := fun h => hQ_not (h ▸ hR)
      exact disjoint_left.mp (hdisj (mem_insert Q F) (mem_insert_of_mem Q hR) hne) hvQ.1 hvR.1
    have hfin_QW : (V(Q) ∩ W).Finite := hfin_W.subset inter_subset_right
    have hfin_FW : (⋃ R ∈ F, (V(R) ∩ W)).Finite :=
      hfin_W.subset (iUnion₂_subset fun _ _ => inter_subset_right)
    rw [ncard_union_eq hdisj_QW hfin_QW hfin_FW, Nat.mul_add, Nat.mul_one]
    omega

/-- **Graph Minors IX, (4.6)** (page 52):
"Let $S$ be true, with $p \ge 2$ and $p \ne 3$, let $|\mathcal{Q}| = p + 4$, and let every
member of $\mathcal{Q}$ be separating. Then $Q \cap \bigcup \mathcal{P}$ is null for some $Q
\in \mathcal{Q}$." -/
theorem theorem_4_6_proof {p : ℕ} {P_set Q_set : Set (Graph α β)} {A B : Set α}
    (hS : S.StatementS p P_set Q_set A B) (hp3 : p ≠ 3)
    (hcard_Q : Q_set.ncard = p + 4)
    (hsep : ∀ Q ∈ Q_set, S.IsSeparatingOmegaPath Q) :
    ∃ Q ∈ Q_set, Disjoint V(Q) V(S.transactionUnion P_set) := by
  by_contra hno
  push Not at hno
  have hmeet : ∀ Q ∈ Q_set, (V(Q) ∩ V(S.transactionUnion P_set)).Nonempty := by
    intro Q hQ
    exact not_disjoint_iff_nonempty_inter.mp (hno Q hQ)
  obtain ⟨A_Q, B_Q, hfence_Q⟩ := hS.isTransaction_Q
  have hfin_Q : Q_set.Finite := hfence_Q.1.finite S
  -- Let `H` be the set of half-covered members of `Q_set`, and `C` the set of members of `Q_set`
  -- with both ends in `V(P_set)`.
  let H : Set (Graph α β) := {Q ∈ Q_set | S.IsHalfCovered P_set Q}
  let C : Set (Graph α β) := {Q ∈ Q_set | pathEnds S.G Q ⊆ S.transactionEnds P_set}
  have hH_sub : H ⊆ Q_set := fun _ h => h.1
  have hC_sub : C ⊆ Q_set := fun _ h => h.1
  have hfin_H : H.Finite := hfin_Q.subset hH_sub
  have hfin_C : C.Finite := hfin_Q.subset hC_sub
  -- `H` and `C` are disjoint because a half-covered path has an end not in `V(P_set)`.
  have hdisj_HC : Disjoint H C := by
    rw [disjoint_left]
    intro Q ⟨_, hcov⟩ ⟨_, hboth⟩
    rcases hcov with ⟨_, _, _, _, s, t, a, b, _, _, hQ_ends, rfl, hnot_in, _⟩
    have hb_ends : b ∈ pathEnds S.G Q := by
      rw [hQ_ends.1.pathEnds_eq]
      exact Or.inr rfl
    exact hnot_in (hboth hb_ends)
  -- By (4.5), `H.ncard ≤ 4`.
  have hH_le_4 : H.ncard ≤ 4 := by
    by_contra hgt
    obtain ⟨H₅, hH₅_sub, hH₅_card⟩ := Set.exists_subset_card_eq (by omega : 5 ≤ H.ncard)
    have hH₅_Q : H₅ ⊆ Q_set := hH₅_sub.trans hH_sub
    have htr_H₅ : S.IsTransaction H₅ :=
      ⟨A_Q, B_Q, ⟨fun Q hQ => hfence_Q.1.1 Q (hH₅_Q hQ),
        fun Q₁ hQ₁ Q₂ hQ₂ hne => hfence_Q.1.2 (hH₅_Q hQ₁) (hH₅_Q hQ₂) hne⟩,
        hfence_Q.2.1, fun Q hQ => hfence_Q.2.2 Q (hH₅_Q hQ)⟩
    have hno_cr_H₅ : ∀ Q₁ ∈ H₅, ∀ Q₂ ∈ H₅, ¬ S.OmegaPathsCross Q₁ Q₂ := by
      intro Q₁ _ Q₂ hQ₂ hcr
      exact (hsep Q₂ (hH₅_Q hQ₂)).2 ⟨Q₁, hcr⟩
    obtain ⟨Q_l, hQl_len, _, hQl_set, hQl_ord⟩ :=
      htr_H₅.exists_areInOrder_of_not_cross S hno_cr_H₅
    rw [hH₅_card] at hQl_len
    rcases Q_l with _ | ⟨Q₁, _ | ⟨Q₂, _ | ⟨Q₃, _ | ⟨Q₄, _ | ⟨Q₅, _ | _⟩⟩⟩⟩⟩ <;> simp at hQl_len
    have hmem_H₅ : ∀ Q ∈ ([Q₁, Q₂, Q₃, Q₄, Q₅] : List (Graph α β)), Q ∈ H₅ := by
      intro Q hQ
      rw [← hQl_set]
      exact hQ
    have h₁ : Q₁ ∈ H := hH₅_sub (hmem_H₅ Q₁ (by simp))
    have h₂ : Q₂ ∈ H := hH₅_sub (hmem_H₅ Q₂ (by simp))
    have h₃ : Q₃ ∈ H := hH₅_sub (hmem_H₅ Q₃ (by simp))
    have h₄ : Q₄ ∈ H := hH₅_sub (hmem_H₅ Q₄ (by simp))
    have h₅ : Q₅ ∈ H := hH₅_sub (hmem_H₅ Q₅ (by simp))
    exact S.theorem_4_5_proof hS h₁.1 h₂.1 h₃.1 h₄.1 h₅.1 hQl_ord
      (hsep Q₂ h₂.1) (hsep Q₃ h₃.1) (hsep Q₄ h₄.1)
      ⟨h₁.2, h₂.2, h₃.2, h₄.2, h₅.2⟩
  -- By (4.3), `Q_set \ (H ∪ C)` has at most 1 element.
  let R_set : Set (Graph α β) := Q_set \ (H ∪ C)
  have hfin_R : R_set.Finite := hfin_Q.subset sdiff_subset
  have hR_le_1 : R_set.ncard ≤ 1 := by
    rw [Set.ncard_le_one_iff hfin_R]
    intro Q₁ Q₂ ⟨hQ₁_in, hQ₁_not⟩ ⟨hQ₂_in, hQ₂_not⟩
    refine (S.theorem_4_3_proof hS).1 Q₁ hQ₁_in Q₂ hQ₂_in ?_ ?_
    · rintro (hdisj₁ | hboth₁ | hcov₁)
      · exact hno Q₁ hQ₁_in hdisj₁
      · exact hQ₁_not (Or.inr ⟨hQ₁_in, hboth₁⟩)
      · exact hQ₁_not (Or.inl ⟨hQ₁_in, hcov₁⟩)
    · rintro (hdisj₂ | hboth₂ | hcov₂)
      · exact hno Q₂ hQ₂_in hdisj₂
      · exact hQ₂_not (Or.inr ⟨hQ₂_in, hboth₂⟩)
      · exact hQ₂_not (Or.inl ⟨hQ₂_in, hcov₂⟩)
  -- Since `Q_set = (H ∪ C) ∪ R_set`, we get `p + 3 ≤ H.ncard + C.ncard`.
  have hQ_eq : Q_set = (H ∪ C) ∪ R_set :=
    (union_sdiff_cancel (union_subset hH_sub hC_sub)).symm
  have hcard_HC_ge : p + 3 ≤ H.ncard + C.ncard := by
    have hle1 : Q_set.ncard ≤ (H ∪ C).ncard + R_set.ncard := by
      rw [hQ_eq]
      exact ncard_union_le (H ∪ C) R_set
    have hle2 : (H ∪ C).ncard = H.ncard + C.ncard :=
      ncard_union_eq hdisj_HC hfin_H hfin_C
    omega
  -- Count the ends in `W_P = S.transactionEnds P_set`.
  let W_P : Set α := S.transactionEnds P_set
  have hfin_WP : W_P.Finite := S.finite_V.subset ((S.transactionEnds_subset_bar P_set).trans
    S.bar_subset)
  have hH_ends : ∀ Q ∈ H, 1 ≤ (V(Q) ∩ W_P).ncard := by
    intro Q ⟨_, hcov⟩
    rcases hcov with ⟨P, hP_in, _, _, s, t, a, b, _, hP_ends, hQ_ends, rfl, _, _⟩
    exact Nat.succ_le_iff.mpr ((ncard_pos (hfin_WP.subset inter_subset_right)).mpr
      ⟨s, hQ_ends.1.left_mem, hP_ends.mem_transactionEnds_left S hP_in⟩)
  have hC_ends : ∀ Q ∈ C, 2 ≤ (V(Q) ∩ W_P).ncard := by
    intro Q ⟨hQ_in, hboth⟩
    rcases hfence_Q.1.1 Q hQ_in with ⟨a, b, hQ_ends⟩
    have ha_ends : a ∈ pathEnds S.G Q := by
      rw [hQ_ends.1.pathEnds_eq]
      exact Or.inl rfl
    have hb_ends : b ∈ pathEnds S.G Q := by
      rw [hQ_ends.1.pathEnds_eq]
      exact Or.inr rfl
    have ha_in : a ∈ V(Q) ∩ W_P := ⟨hQ_ends.1.left_mem, hboth ha_ends⟩
    have hb_in : b ∈ V(Q) ∩ W_P := ⟨hQ_ends.1.right_mem, hboth hb_ends⟩
    have hsub : ({a, b} : Set α) ⊆ V(Q) ∩ W_P := by
      rintro z (rfl | rfl)
      · exact ha_in
      · exact hb_in
    have hcard_ab : ({a, b} : Set α).ncard = 2 := ncard_pair hQ_ends.2.1
    rw [← hcard_ab]
    exact ncard_le_ncard hsub (hfin_WP.subset inter_subset_right)
  have hdisj_Q : Q_set.PairwiseDisjoint (fun Q => V(Q)) :=
    fun Q₁ hQ₁ Q₂ hQ₂ hne => hfence_Q.1.2 hQ₁ hQ₂ hne
  let U_H : Set α := ⋃ Q ∈ H, (V(Q) ∩ W_P)
  let U_C : Set α := ⋃ Q ∈ C, (V(Q) ∩ W_P)
  have hU_H : 1 * H.ncard ≤ U_H.ncard :=
    mul_ncard_le_ncard_biUnion hfin_H hfin_WP (hdisj_Q.subset hH_sub) hH_ends
  have hU_C : 2 * C.ncard ≤ U_C.ncard :=
    mul_ncard_le_ncard_biUnion hfin_C hfin_WP (hdisj_Q.subset hC_sub) hC_ends
  have hdisj_U : Disjoint U_H U_C := by
    rw [disjoint_left]
    intro v hvH hvC
    simp only [U_H, U_C, mem_iUnion, exists_prop] at hvH hvC
    rcases hvH with ⟨Q₁, hQ₁H, hv₁⟩
    rcases hvC with ⟨Q₂, hQ₂C, hv₂⟩
    have hne : Q₁ ≠ Q₂ := fun h => disjoint_left.mp hdisj_HC hQ₁H (h ▸ hQ₂C)
    exact disjoint_left.mp (hfence_Q.1.2 (hH_sub hQ₁H) (hC_sub hQ₂C) hne) hv₁.1 hv₂.1
  have hfin_UH : U_H.Finite := hfin_WP.subset (iUnion₂_subset fun _ _ => inter_subset_right)
  have hfin_UC : U_C.Finite := hfin_WP.subset (iUnion₂_subset fun _ _ => inter_subset_right)
  have hsub_WP : U_H ∪ U_C ⊆ W_P :=
    union_subset (iUnion₂_subset fun _ _ => inter_subset_right)
      (iUnion₂_subset fun _ _ => inter_subset_right)
  have hle_WP : U_H.ncard + U_C.ncard ≤ W_P.ncard := by
    rw [← ncard_union_eq hdisj_U hfin_UH hfin_UC]
    exact ncard_le_ncard hsub_WP hfin_WP
  have hWP_eq : W_P.ncard = 2 * p := by
    rw [(hS.isFenceFor_P.ncard_transactionEnds S).2.2, hS.card_P_eq S hp3]
  omega

end Society

end GraphMinor.GM09
