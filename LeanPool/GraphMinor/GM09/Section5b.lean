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
import LeanPool.GraphMinor.GM09.Section2c
import LeanPool.GraphMinor.GM09.Section2d
import LeanPool.GraphMinor.GM09.Section3a
import LeanPool.GraphMinor.GM09.Section3c
import LeanPool.GraphMinor.GM09.Section4a
import LeanPool.GraphMinor.GM09.Section4b
import LeanPool.GraphMinor.GM09.Section4c
import LeanPool.GraphMinor.GM09.Section5a
public import LeanPool.GraphMinor.GM09.Restriction
import LeanPool.GraphMinor.GM09.Section7
import Mathlib.Data.Set.Card

/-!
# Graph Minors IX, Section 5 (Part B): One-Point Extensions, Contractions, and (5.3)–(5.5)

This file formalizes (5.3), (5.4), and (5.5) from Section 5 of
N. Robertson and P. D. Seymour, *Graph Minors. IX. Disjoint crossed paths*,
J. Combin. Theory Ser. B **49** (1990) 40–77 (pages 53–55):
- `(5.3)` (`theorem_5_3`, page 53): if `Q` is an induced `Ω`-path in `(K, Ω)` with ends `a, b`
  such that `Ω(a, b) = ∅` and `ΩBar - {a, b}` catches `K \ V(Q)`, and `(K, Ω₁)` has a cross where
  `Ω₁` extends `Ω` by an internal vertex `r` of `Q` with `(a, r, b)` clockwise, then `(K, Ω)` has
  a cross or tripod.
- `(5.4)` (`theorem_5_4`, page 54): if `(G, Ω)` is internally 4-connected, `Q` is a separating
  `Ω`-path with separation `(G₁, G₂)`, and `(G \ V(G₂), Ω | V(G \ V(G₂)))` has a tripod, then
  `(G₁, Ω | V(G₁))` has a cross.
- `(5.5)` (`theorem_5_5`, pages 54–55): combines `(5.2)`, `(5.3)`, and `(5.4)` to produce a
  non-separating `Ω`-path `P ≤ G₁`.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM06

universe u v

variable {α : Type u} {β : Type v}

/-! ## Restrictions and one-point extensions of cyclic permutations -/

namespace CyclicPerm

variable {Ω : CyclicPerm α}

/-- If `Ω₁` extends `Ω` by a single point `r ∉ Ω.bar` with `(a, r, b)` `Ω₁`-clockwise and
`Ω(a, b) = ∅`, then `Ω₁(a, b) = {r}`, `Ω₁(a, r) = ∅`, `Ω₁(r, b) = ∅`, and
`Ω₁(b, a) = Ω(b, a) = Ω.bar \ {a, b}`. -/
theorem extension_intervals {Ω₁ : CyclicPerm α} {a b r : α}
    (hbar₁ : Ω₁.bar = Ω.bar ∪ {r})
    (hrest : Ω₁.IsRestriction Ω.bar Ω)
    (hab_empty : Ω.interval a b = ∅)
    (harb : Ω₁.IsClockwise3 a r b) :
    Ω₁.interval a b = {r} ∧
      Ω₁.interval a r = ∅ ∧
      Ω₁.interval r b = ∅ ∧
      Ω₁.interval b a = Ω.interval b a ∧
      Ω.interval b a = Ω.bar \ {a, b} := by
  have harb_iff := Ω₁.isClockwise3_iff.mp harb
  have hab_ne : a ≠ b := harb_iff.2.1
  have har_ne : a ≠ r := harb_iff.1
  have hrb_ne : r ≠ b := harb_iff.2.2.1
  have hr_bar₁ : r ∈ Ω₁.bar := by rw [hbar₁]; exact Or.inr rfl
  have hr_in_ab : r ∈ Ω₁.interval a b := by
    refine ⟨⟨hr_bar₁, ?_⟩, harb⟩
    simp [har_ne.symm, hrb_ne]
  have ha_bar : a ∈ Ω.bar := by
    have ha₁ : a ∈ Ω₁.bar := harb_iff.2.2.2.1
    rw [hbar₁] at ha₁
    rcases ha₁ with ha | rfl
    · exact ha
    · exact (har_ne rfl).elim
  have hb_bar : b ∈ Ω.bar := by
    have hb₁ : b ∈ Ω₁.bar := harb_iff.2.2.2.2.2.1
    rw [hbar₁] at hb₁
    rcases hb₁ with hb | rfl
    · exact hb
    · exact (hrb_ne rfl).elim
  have hint_ab : Ω₁.interval a b = {r} := by
    ext x
    simp only [mem_singleton_iff]
    refine ⟨fun hx => ?_, fun h => h ▸ hr_in_ab⟩
    have hx_bar₁ : x ∈ Ω₁.bar := hx.1.1
    rw [hbar₁] at hx_bar₁
    rcases hx_bar₁ with hx_bar | rfl
    · exfalso
      have hx_in : x ∈ Ω.interval a b := by
        rw [hrest.interval_eq ha_bar hb_bar]
        exact ⟨hx, hx_bar⟩
      rw [hab_empty] at hx_in
      exact hx_in
    · rfl
  have hunion_r := Ω₁.interval_eq_union_of_mem hr_in_ab
  rw [hint_ab] at hunion_r
  have hint_ar : Ω₁.interval a r = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro x hx
    have hx_r : x ∈ ({r} : Set α) := by
      rw [hunion_r]
      exact Or.inl (Or.inl hx)
    rw [mem_singleton_iff] at hx_r
    exact Ω₁.not_mem_interval_right a r (hx_r ▸ hx)
  have hint_rb : Ω₁.interval r b = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro x hx
    have hx_r : x ∈ ({r} : Set α) := by
      rw [hunion_r]
      exact Or.inr hx
    rw [mem_singleton_iff] at hx_r
    exact Ω₁.not_mem_interval_left r b (hx_r ▸ hx)
  have hint_ba_bar : Ω.interval b a = Ω.bar \ {a, b} := by
    have hun := Ω.interval_union_interval_swap ha_bar hb_bar hab_ne
    rwa [hab_empty, empty_union] at hun
  have hint_ba₁ : Ω₁.interval b a = Ω.interval b a := by
    ext x
    constructor
    · intro hx
      have hx_ne_r : x ≠ r := fun h =>
        disjoint_left.mp (Ω₁.disjoint_interval_swap a b) (h ▸ hr_in_ab) hx
      have hx_bar₁ : x ∈ Ω₁.bar := hx.1.1
      rw [hbar₁] at hx_bar₁
      rcases hx_bar₁ with hx_bar | rfl
      · rw [hrest.interval_eq hb_bar ha_bar]
        exact ⟨hx, hx_bar⟩
      · exact (hx_ne_r rfl).elim
    · intro hx
      have hx' := hx
      rw [hrest.interval_eq hb_bar ha_bar] at hx'
      exact hx'.1
  exact ⟨hint_ab, hint_ar, hint_rb, hint_ba₁, hint_ba_bar⟩

theorem Crosses.interval_nonempty {s₁ t₁ s₂ t₂ : α} (h : Ω.Crosses s₁ t₁ s₂ t₂) :
    (Ω.interval s₁ t₁).Nonempty ∧ (Ω.interval t₁ s₁).Nonempty := by
  rcases Ω.crosses_iff_interval.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨⟨s₂, h1⟩, ⟨t₂, h2⟩⟩
  · exact ⟨⟨t₂, h1⟩, ⟨s₂, h2⟩⟩

theorem Crosses.not_interval_empty {s₁ t₁ s₂ t₂ : α}
    (hempty : Ω.interval s₁ t₁ = ∅ ∨ Ω.interval t₁ s₁ = ∅) :
    ¬ Ω.Crosses s₁ t₁ s₂ t₂ := by
  intro hcr
  obtain ⟨hne1, hne2⟩ := hcr.interval_nonempty
  rcases hempty with h1 | h2
  · rw [h1] at hne1; exact not_nonempty_empty hne1
  · rw [h2] at hne2; exact not_nonempty_empty hne2

/-- If `{s₁, t₁}` crosses `{s₂, t₂}` in `Ω` and `e₀ ∈ Ω.bar \ {s₂, t₂}`, then either `{e₀, s₁}`
or `{e₀, t₁}` crosses `{s₂, t₂}` in `Ω`. -/
theorem Crosses.left_or_right_of_notMem {s₁ t₁ s₂ t₂ e₀ : α}
    (hcr : Ω.Crosses s₁ t₁ s₂ t₂) (he₀ : e₀ ∈ Ω.bar) (he₀_not : e₀ ∉ ({s₂, t₂} : Set α)) :
    Ω.Crosses e₀ s₁ s₂ t₂ ∨ Ω.Crosses e₀ t₁ s₂ t₂ := by
  by_cases he₀_s₁ : e₀ = s₁
  · subst he₀_s₁; exact Or.inr hcr
  by_cases he₀_t₁ : e₀ = t₁
  · subst he₀_t₁; exact Or.inl hcr.swap_left
  have haux : ∀ {u₁ v₁ u₂ v₂ : α},
      u₂ ∈ Ω.interval u₁ v₁ → v₂ ∈ Ω.interval v₁ u₁ →
      u₂ ≠ e₀ → e₀ ∈ Ω.interval u₁ v₁ →
      Ω.Crosses e₀ u₁ u₂ v₂ ∨ Ω.Crosses e₀ v₁ u₂ v₂ := by
    intro u₁ v₁ u₂ v₂ hu₂ hv₂ hu₂_ne he₀_int
    have hunion := Ω.interval_eq_union_of_mem he₀_int
    have hu₂' : u₂ ∈ Ω.interval u₁ e₀ ∪ {e₀} ∪ Ω.interval e₀ v₁ := hunion ▸ hu₂
    have hv₁_e₀u₁ : v₁ ∈ Ω.interval e₀ u₁ := Ω.mem_interval_rotate_left he₀_int
    have hu₁_v₁e₀ : u₁ ∈ Ω.interval v₁ e₀ := Ω.mem_interval_rotate_right he₀_int
    rcases hu₂' with (hu₂_left | h_eq) | hu₂_right
    · left
      have hv₂' : v₂ ∈ Ω.interval e₀ u₁ :=
        (Ω.interval_subset_interval_right hv₁_e₀u₁) hv₂
      exact Ω.crosses_iff_interval.mpr (Or.inr ⟨hv₂', hu₂_left⟩)
    · exact (hu₂_ne (mem_singleton_iff.mp h_eq)).elim
    · right
      have hv₂' : v₂ ∈ Ω.interval v₁ e₀ :=
        (Ω.interval_subset_interval_left hu₁_v₁e₀) hv₂
      exact Ω.crosses_iff_interval.mpr (Or.inl ⟨hu₂_right, hv₂'⟩)
  have hs₂_ne : s₂ ≠ e₀ := fun h => he₀_not (by simp [h])
  have ht₂_ne : t₂ ≠ e₀ := fun h => he₀_not (by simp [h])
  have hs₁_bar : s₁ ∈ Ω.bar := by
    rcases Ω.crosses_iff_interval.mp hcr with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact (Ω.isClockwise3_iff.mp h1.2).2.2.2.1
    · exact (Ω.isClockwise3_iff.mp h1.2).2.2.2.1
  have ht₁_bar : t₁ ∈ Ω.bar := by
    rcases Ω.crosses_iff_interval.mp hcr with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact (Ω.isClockwise3_iff.mp h1.2).2.2.2.2.2.1
    · exact (Ω.isClockwise3_iff.mp h1.2).2.2.2.2.2.1
  have hs₁t₁_ne : s₁ ≠ t₁ := by
    rcases Ω.crosses_iff_interval.mp hcr with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact (Ω.isClockwise3_iff.mp h1.2).2.1
    · exact (Ω.isClockwise3_iff.mp h1.2).2.1
  rcases Ω.mem_interval_or_interval_swap hs₁_bar ht₁_bar he₀ hs₁t₁_ne he₀_s₁ he₀_t₁ with
    he₀_st | he₀_ts
  · rcases Ω.crosses_iff_interval.mp hcr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact haux h1 h2 hs₂_ne he₀_st
    · rcases haux h1 h2 ht₂_ne he₀_st with h | h
      · exact Or.inl h.swap_right
      · exact Or.inr h.swap_right
  · rcases Ω.crosses_iff_interval.mp hcr.swap_left with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (haux h1 h2 hs₂_ne he₀_ts).symm
    · rcases haux h1 h2 ht₂_ne he₀_ts with h | h
      · exact Or.inr h.swap_right
      · exact Or.inl h.swap_right

end CyclicPerm

/-! ## Proof of (5.3) (page 53) -/

namespace Society

variable (S : Society α β)

/-- If `(K, Ω₁)` extends `(K, Ω)` by `r ∉ Ω.bar`, and `{M₁, M₂}` is a cross in `S₁` with ends
`u₁, v₁` and `u₂, v₂` while `S` has no cross, then `r ∈ {u₁, v₁, u₂, v₂}`. -/
theorem mem_ends_of_isCross_of_not_hasCross {S₁ : Society α β} {r : α}
    (hG₁ : S₁.G = S.G)
    (hbar₁ : S₁.Ω.bar = S.Ω.bar ∪ {r})
    (hrest : S₁.Ω.IsRestriction S.Ω.bar S.Ω)
    (hno_cross : ¬ ∃ M₁ M₂ : Graph α β, S.IsCross M₁ M₂)
    {M₁ M₂ : Graph α β} {u₁ v₁ u₂ v₂ : α}
    (hdisj : Disjoint V(M₁) V(M₂))
    (hM₁ : S₁.IsOmegaPathWithEnds M₁ u₁ v₁)
    (hM₂ : S₁.IsOmegaPathWithEnds M₂ u₂ v₂)
    (hcr : S₁.Ω.Crosses u₁ v₁ u₂ v₂) :
    r ∈ ({u₁, v₁, u₂, v₂} : Set α) := by
  by_contra hr_not
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hr_not
  have hmem_bar : ∀ {x : α}, x ∈ S₁.Ω.bar → x ≠ r → x ∈ S.Ω.bar := by
    intro x hx hne
    rw [hbar₁] at hx
    rcases hx with hx | rfl
    · exact hx
    · exact (hne rfl).elim
  have hu₁ : u₁ ∈ S.Ω.bar := hmem_bar hM₁.2.2.1 (Ne.symm hr_not.1)
  have hv₁ : v₁ ∈ S.Ω.bar := hmem_bar hM₁.2.2.2 (Ne.symm hr_not.2.1)
  have hu₂ : u₂ ∈ S.Ω.bar := hmem_bar hM₂.2.2.1 (Ne.symm hr_not.2.2.1)
  have hv₂ : v₂ ∈ S.Ω.bar := hmem_bar hM₂.2.2.2 (Ne.symm hr_not.2.2.2)
  have hcr_S : S.Ω.Crosses u₁ v₁ u₂ v₂ :=
    (hrest.crosses_iff.mpr ⟨hu₁, hv₁, hu₂, hv₂, hcr⟩)
  exact hno_cross ⟨M₁, M₂, hdisj, u₁, v₁, u₂, v₂,
    ⟨hG₁ ▸ hM₁.1, hM₁.2.1, hu₁, hv₁⟩,
    ⟨hG₁ ▸ hM₂.1, hM₂.2.1, hu₂, hv₂⟩, hcr_S⟩

/-- Helper for Claim (1) of (5.3): in a minimal cross `{P₁, P₂}` of `S₁`, if `A ≤ Q₁` is a path
from `e₀` to `a' ∈ V(P₁)` meeting `V(P₁) ∪ V(P₂)` only at `a'`, and `P₁` splits at `a'` into `S_p`
(to `u₁`) and `T_p` (to `v₁`) such that `{e₀, u₁}` crosses `{s₂, t₂}`, we obtain a contradiction
assuming `e₀ ∉ {u₁, v₁, s₂, t₂}` and `S` has no cross. -/
private theorem contradiction_of_branch {S₁ : Society α β} {Q Q₁ Q₂ P₁ P₂ A S_p T_p : Graph α β}
    {e₀ e₁ r s₂ t₂ a' u₁ v₁ : α}
    (hG₁ : S₁.G = S.G)
    (hbar₁ : S₁.Ω.bar = S.Ω.bar ∪ {r})
    (hrest : S₁.Ω.IsRestriction S.Ω.bar S.Ω)
    (hno_cross : ¬ ∃ M₁ M₂ : Graph α β, S.IsCross M₁ M₂)
    (hQ : S.IsOmegaPathWithEnds Q e₀ e₁)
    (hno_int : Disjoint (pathInternalVerts S.G Q) S.Ω.bar)
    (hr_Q : r ∈ V(Q) \ {e₀, e₁})
    (hre₁_empty : S₁.Ω.interval r e₁ = ∅ ∨ S₁.Ω.interval e₁ r = ∅)
    (hsep_Q : IsGraphSeparation Q Q₁ Q₂)
    (hinter_Q : V(Q₁) ∩ V(Q₂) = {r})
    (he₁_Q₂ : e₁ ∈ V(Q₂))
    (hdisj_P : Disjoint V(P₁) V(P₂))
    (hP₁_le : P₁ ≤ S.G)
    (hP₂ : S₁.IsOmegaPathWithEnds P₂ s₂ t₂)
    (hmin : ∀ P₁' P₂' : Graph α β, S₁.IsCross P₁' P₂' →
      subgraphUnion S.G (subgraphUnion S.G P₁' P₂') Q ≤
        subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q →
      V(subgraphUnion S.G (subgraphUnion S.G P₁' P₂') Q) =
        V(subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q) ∧
      E(subgraphUnion S.G (subgraphUnion S.G P₁' P₂') Q) =
        E(subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q))
    (hA_Q₁ : A ≤ Q₁)
    (hA_path : IsGraphPathWithEnds S.G A e₀ a')
    (hA_inter : V(A) ∩ (V(P₁) ∪ V(P₂)) = {a'})
    (hSp_le : S_p ≤ P₁) (hTp_le : T_p ≤ P₁)
    (hSp_path : IsGraphPathWithEnds S.G S_p a' u₁)
    (hTp_path : IsGraphPathWithEnds S.G T_p a' v₁)
    (hinter_ST : V(S_p) ∩ V(T_p) = {a'})
    (hdisj_EST : Disjoint E(S_p) E(T_p))
    (hu₁_bar : u₁ ∈ S₁.Ω.bar) (hv₁_bar : v₁ ∈ S₁.Ω.bar)
    (hu₁v₁_ne : u₁ ≠ v₁) (he₀_u₁ : e₀ ≠ u₁) (he₀_v₁ : e₀ ≠ v₁)
    (hcr_uv : S₁.Ω.Crosses u₁ v₁ s₂ t₂)
    (hcr_e₀u₁ : S₁.Ω.Crosses e₀ u₁ s₂ t₂) : False := by
  have hA_Q : A ≤ Q := hA_Q₁.trans hsep_Q.1
  have hinter_AS : V(A) ∩ V(S_p) = {a'} := by
    apply Subset.antisymm
    · intro z ⟨hzA, hzS⟩
      have : z ∈ V(A) ∩ (V(P₁) ∪ V(P₂)) := ⟨hzA, Or.inl (hSp_le.vertexSet_mono hzS)⟩
      rwa [hA_inter] at this
    · rintro z rfl
      exact ⟨hA_path.right_mem, hSp_path.left_mem⟩
  let P' := subgraphUnion S.G A S_p
  have hP'_path : IsGraphPathWithEnds S.G P' e₀ u₁ :=
    hA_path.subgraphUnion hSp_path hinter_AS
  have he₀_bar₁ : e₀ ∈ S₁.Ω.bar := by
    rw [hbar₁]; exact Or.inl hQ.2.2.1
  have hP'_ends : S₁.IsOmegaPathWithEnds P' e₀ u₁ :=
    ⟨hG₁.symm ▸ hP'_path, he₀_u₁, he₀_bar₁, hu₁_bar⟩
  have hdisj_P'P₂ : Disjoint V(P') V(P₂) := by
    rw [vertexSet_subgraphUnion, disjoint_union_left]
    refine ⟨disjoint_left.mpr fun z hzA hzP₂ => ?_, hdisj_P.mono_left hSp_le.vertexSet_mono⟩
    have hz_a' : z = a' := by
      have : z ∈ V(A) ∩ (V(P₁) ∪ V(P₂)) := ⟨hzA, Or.inr hzP₂⟩
      rwa [hA_inter, mem_singleton_iff] at this
    subst hz_a'
    exact disjoint_left.mp hdisj_P (hSp_le.vertexSet_mono hSp_path.left_mem) hzP₂
  have hcr_P'P₂ : S₁.IsCross P' P₂ :=
    ⟨hdisj_P'P₂, e₀, u₁, s₂, t₂, hP'_ends, hP₂, hcr_e₀u₁⟩
  have hP₂_le : P₂ ≤ S.G := hG₁ ▸ hP₂.1.le
  have hQ_le : Q ≤ S.G := hQ.1.le
  have hP'_le : P' ≤ S.G := hP'_path.le
  have hU'_le : subgraphUnion S.G (subgraphUnion S.G P' P₂) Q ≤
      subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q := by
    have hU_le : subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q ≤ S.G :=
      subgraphUnion_le (subgraphUnion_le hP₁_le hP₂_le) hQ_le
    have hP₁_U : P₁ ≤ subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q :=
      (le_subgraphUnion_left hP₁_le hP₂_le).trans
        (le_subgraphUnion_left (subgraphUnion_le hP₁_le hP₂_le) hQ_le)
    have hP₂_U : P₂ ≤ subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q :=
      (le_subgraphUnion_right hP₁_le hP₂_le).trans
        (le_subgraphUnion_left (subgraphUnion_le hP₁_le hP₂_le) hQ_le)
    have hQ_U : Q ≤ subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q :=
      le_subgraphUnion_right (subgraphUnion_le hP₁_le hP₂_le) hQ_le
    have hP'_U : P' ≤ subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q :=
      (subgraphUnion_le_iff hA_path.le hSp_path.le hU_le).mpr
        ⟨hA_Q.trans hQ_U, hSp_le.trans hP₁_U⟩
    have hP'P₂_U : subgraphUnion S.G P' P₂ ≤ subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q :=
      (subgraphUnion_le_iff hP'_le hP₂_le hU_le).mpr ⟨hP'_U, hP₂_U⟩
    exact (subgraphUnion_le_iff (subgraphUnion_le hP'_le hP₂_le) hQ_le hU_le).mpr
      ⟨hP'P₂_U, hQ_U⟩
  obtain ⟨hV_eq, hE_eq⟩ := hmin P' P₂ hcr_P'P₂ hU'_le
  -- Deduce `T_p ≤ Q`.
  have hVT_Q : V(T_p) ⊆ V(Q) := by
    intro z hzT
    have hz_in : z ∈ V(subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q) :=
      Or.inl (Or.inl (hTp_le.vertexSet_mono hzT))
    rw [← hV_eq] at hz_in
    change z ∈ (V(A) ∪ V(S_p)) ∪ V(P₂) ∪ V(Q) at hz_in
    rcases hz_in with ((hzA | hzS) | hzP₂) | hzQ
    · exact hA_Q.vertexSet_mono hzA
    · have hza' : z = a' := by
        have : z ∈ V(S_p) ∩ V(T_p) := ⟨hzS, hzT⟩
        rwa [hinter_ST, mem_singleton_iff] at this
      exact hza' ▸ hA_Q.vertexSet_mono hA_path.right_mem
    · exact (disjoint_left.mp hdisj_P (hTp_le.vertexSet_mono hzT) hzP₂).elim
    · exact hzQ
  have hET_Q : E(T_p) ⊆ E(Q) := by
    intro e heT
    have he_in : e ∈ E(subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q) := by
      rw [edgeSet_subgraphUnion (subgraphUnion_le hP₁_le hP₂_le) hQ_le,
        edgeSet_subgraphUnion hP₁_le hP₂_le]
      exact Or.inl (Or.inl (hTp_le.edgeSet_mono heT))
    rw [← hE_eq, edgeSet_subgraphUnion (subgraphUnion_le hP'_le hP₂_le) hQ_le,
      edgeSet_subgraphUnion hP'_le hP₂_le, edgeSet_subgraphUnion hA_path.le hSp_path.le] at he_in
    rcases he_in with ((heA | heS) | heP₂) | heQ
    · exact hA_Q.edgeSet_mono heA
    · exact (disjoint_left.mp hdisj_EST heS heT).elim
    · obtain ⟨x, y, hxy₁⟩ := T_p.exists_isLink_of_mem_edgeSet heT
      obtain ⟨u, v, huv₂⟩ := P₂.exists_isLink_of_mem_edgeSet heP₂
      have heq := (hxy₁.mono hTp_path.le).left_eq_or_eq (huv₂.mono hP₂_le)
      have hx_P₂ : x ∈ V(P₂) := by
        rcases heq with rfl | rfl
        · exact huv₂.left_mem
        · exact huv₂.right_mem
      exact (disjoint_left.mp hdisj_P (hTp_le.vertexSet_mono hxy₁.left_mem) hx_P₂).elim
    · exact heQ
  have hTp_Q : T_p ≤ Q := by
    rw [(Compatible.of_le_le hTp_path.le hQ_le).le_iff]
    exact ⟨hVT_Q, hET_Q⟩
  have hTp_path_Q : IsGraphPathWithEnds Q T_p a' v₁ := hTp_path.of_le hTp_Q
  -- Since `S₁.IsCross P' P₂`, `r ∈ {e₀, u₁, s₂, t₂}`; thus `r ∈ V(P₁) → r = u₁`.
  have hr_in_ends : r ∈ ({e₀, u₁, s₂, t₂} : Set α) :=
    S.mem_ends_of_isCross_of_not_hasCross hG₁ hbar₁ hrest hno_cross
      hdisj_P'P₂ hP'_ends hP₂ hcr_e₀u₁
  have hr_eq_u₁_of_P₁ : r ∈ V(P₁) → r = u₁ := by
    intro hr_P₁
    rcases hr_in_ends with rfl | rfl | rfl | rfl
    · exact (hr_Q.2 (by simp)).elim
    · rfl
    · exact (disjoint_left.mp hdisj_P hr_P₁ hP₂.1.left_mem).elim
    · exact (disjoint_left.mp hdisj_P hr_P₁ hP₂.1.right_mem).elim
  -- Now `v₁ ∈ V(Q) ∩ S₁.Ω.bar`, so `v₁ ∈ {e₀, e₁, r}`.
  have hv₁_Q : v₁ ∈ V(Q) := hVT_Q hTp_path.right_mem
  have hv₁_bar' : v₁ ∈ S.Ω.bar ∪ {r} := hbar₁ ▸ hv₁_bar
  rcases hv₁_bar' with hv₁_S | rfl
  · have hv₁_ends : v₁ ∈ ({e₀, e₁} : Set α) := by
      by_contra hnot
      have hv₁_int : v₁ ∈ pathInternalVerts S.G Q := by
        rw [hQ.1.pathInternalVerts_eq]
        exact ⟨hv₁_Q, hnot⟩
      exact disjoint_left.mp hno_int hv₁_int hv₁_S
    rcases hv₁_ends with rfl | rfl
    · exact he₀_v₁ rfl
    · -- `v₁ = e₁`: `T_p` is a path in `Q` from `a' ∈ V(Q₁)` to `e₁ ∈ V(Q₂)`, so `r ∈ V(T_p)`.
      have ha'_Q₁ : a' ∈ V(Q₁) := hA_Q₁.vertexSet_mono hA_path.right_mem
      obtain ⟨z, hzT, hz_inter⟩ :=
        exists_mem_inter_of_isGraphPathWithEnds hsep_Q hTp_path_Q ha'_Q₁ he₁_Q₂
      rw [hinter_Q, mem_singleton_iff] at hz_inter
      have hr_u₁ : r = u₁ := hr_eq_u₁_of_P₁ (hTp_le.vertexSet_mono (hz_inter ▸ hzT))
      exact CyclicPerm.Crosses.not_interval_empty hre₁_empty (hr_u₁.symm ▸ hcr_uv)
  · -- `v₁ = r`: then `r ∈ V(T_p) ⊆ V(P₁)`, so `r = u₁ = v₁`, contradicting `u₁ ≠ v₁`.
    have hr_u₁ : v₁ = u₁ := hr_eq_u₁_of_P₁ (hTp_le.vertexSet_mono hTp_path.right_mem)
    exact hu₁v₁_ne hr_u₁.symm

/-- Helper for Claim (1) of (5.3) when `a' ∈ V(P₁)`. -/
private theorem end_mem_of_hit_left {S₁ : Society α β} {Q Q₁ Q₂ P₁ P₂ A : Graph α β}
    {e₀ e₁ r s₁ t₁ s₂ t₂ a' : α}
    (hG₁ : S₁.G = S.G)
    (hbar₁ : S₁.Ω.bar = S.Ω.bar ∪ {r})
    (hrest : S₁.Ω.IsRestriction S.Ω.bar S.Ω)
    (hno_cross : ¬ ∃ M₁ M₂ : Graph α β, S.IsCross M₁ M₂)
    (hQ : S.IsOmegaPathWithEnds Q e₀ e₁)
    (hno_int : Disjoint (pathInternalVerts S.G Q) S.Ω.bar)
    (hr_Q : r ∈ V(Q) \ {e₀, e₁})
    (hre₁_empty : S₁.Ω.interval r e₁ = ∅ ∨ S₁.Ω.interval e₁ r = ∅)
    (hsep_Q : IsGraphSeparation Q Q₁ Q₂)
    (hinter_Q : V(Q₁) ∩ V(Q₂) = {r})
    (he₁_Q₂ : e₁ ∈ V(Q₂))
    (hdisj_P : Disjoint V(P₁) V(P₂))
    (hP₁ : S₁.IsOmegaPathWithEnds P₁ s₁ t₁)
    (hP₂ : S₁.IsOmegaPathWithEnds P₂ s₂ t₂)
    (hcr : S₁.Ω.Crosses s₁ t₁ s₂ t₂)
    (hmin : ∀ P₁' P₂' : Graph α β, S₁.IsCross P₁' P₂' →
      subgraphUnion S.G (subgraphUnion S.G P₁' P₂') Q ≤
        subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q →
      V(subgraphUnion S.G (subgraphUnion S.G P₁' P₂') Q) =
        V(subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q) ∧
      E(subgraphUnion S.G (subgraphUnion S.G P₁' P₂') Q) =
        E(subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q))
    (hA_Q₁ : A ≤ Q₁)
    (hA_path : IsGraphPathWithEnds S.G A e₀ a')
    (hA_inter : V(A) ∩ (V(P₁) ∪ V(P₂)) = {a'})
    (ha'_P₁ : a' ∈ V(P₁)) :
    e₀ ∈ ({s₁, t₁, s₂, t₂} : Set α) := by
  by_contra he₀_not
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at he₀_not
  have hP₁_G : IsGraphPathWithEnds S.G P₁ s₁ t₁ := hG₁ ▸ hP₁.1
  obtain ⟨S_p, T_p, hSp_le, hTp_le, hSp_P₁, hTp_P₁, _, hinter_ST, hdisj_EST⟩ :=
    hP₁_G.exists_split_at ha'_P₁
  have hSp_G : IsGraphPathWithEnds S.G S_p a' s₁ := (hSp_P₁.mono hP₁_G.le).symm
  have hTp_G : IsGraphPathWithEnds S.G T_p a' t₁ := hTp_P₁.mono hP₁_G.le
  have he₀_bar₁ : e₀ ∈ S₁.Ω.bar := by rw [hbar₁]; exact Or.inl hQ.2.2.1
  have he₀_not_2 : e₀ ∉ ({s₂, t₂} : Set α) := by
    simp [he₀_not.2.2.1, he₀_not.2.2.2]
  rcases hcr.left_or_right_of_notMem he₀_bar₁ he₀_not_2 with hcr_s₁ | hcr_t₁
  · exact S.contradiction_of_branch hG₁ hbar₁ hrest hno_cross hQ hno_int hr_Q hre₁_empty
      hsep_Q hinter_Q he₁_Q₂ hdisj_P hP₁_G.le hP₂ hmin hA_Q₁ hA_path hA_inter
      hSp_le hTp_le hSp_G hTp_G hinter_ST hdisj_EST
      hP₁.2.2.1 hP₁.2.2.2 hP₁.2.1 he₀_not.1 he₀_not.2.1 hcr hcr_s₁
  · exact S.contradiction_of_branch hG₁ hbar₁ hrest hno_cross hQ hno_int hr_Q hre₁_empty
      hsep_Q hinter_Q he₁_Q₂ hdisj_P hP₁_G.le hP₂ hmin hA_Q₁ hA_path hA_inter
      hTp_le hSp_le hTp_G hSp_G (inter_comm V(T_p) V(S_p) ▸ hinter_ST) hdisj_EST.symm
      hP₁.2.2.2 hP₁.2.2.1 hP₁.2.1.symm he₀_not.2.1 he₀_not.1 hcr.swap_left hcr_t₁

/-- General end-membership lemma for Claim (1) of (5.3): for an `Ω`-path `Q` with ends `e₀, e₁`
satisfying `S₁.Ω.interval r e₁ = ∅ ∨ S₁.Ω.interval e₁ r = ∅`, either `S` has a cross or
`e₀ ∈ {s₁, t₁, s₂, t₂}`. -/
private theorem end_mem_of_minimal_cross {S₁ : Society α β} {Q P₁ P₂ : Graph α β}
    {e₀ e₁ r s₁ t₁ s₂ t₂ : α}
    (hG₁ : S₁.G = S.G)
    (hbar₁ : S₁.Ω.bar = S.Ω.bar ∪ {r})
    (hrest : S₁.Ω.IsRestriction S.Ω.bar S.Ω)
    (hno_cross : ¬ ∃ M₁ M₂ : Graph α β, S.IsCross M₁ M₂)
    (hQ : S.IsOmegaPathWithEnds Q e₀ e₁)
    (hno_int : Disjoint (pathInternalVerts S.G Q) S.Ω.bar)
    (hr_Q : r ∈ V(Q) \ {e₀, e₁})
    (hre₁_empty : S₁.Ω.interval r e₁ = ∅ ∨ S₁.Ω.interval e₁ r = ∅)
    (hdisj_P : Disjoint V(P₁) V(P₂))
    (hP₁ : S₁.IsOmegaPathWithEnds P₁ s₁ t₁)
    (hP₂ : S₁.IsOmegaPathWithEnds P₂ s₂ t₂)
    (hcr : S₁.Ω.Crosses s₁ t₁ s₂ t₂)
    (hmin : ∀ P₁' P₂' : Graph α β, S₁.IsCross P₁' P₂' →
      subgraphUnion S.G (subgraphUnion S.G P₁' P₂') Q ≤
        subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q →
      V(subgraphUnion S.G (subgraphUnion S.G P₁' P₂') Q) =
        V(subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q) ∧
      E(subgraphUnion S.G (subgraphUnion S.G P₁' P₂') Q) =
        E(subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q)) :
    e₀ ∈ ({s₁, t₁, s₂, t₂} : Set α) := by
  obtain ⟨Q₁, Q₂, hQ₁_le, hQ₂_le, hQ₁_path, hQ₂_path, hunion_Q, hinter_Q, hdisj_EQ⟩ :=
    hQ.1.exists_split_at hr_Q.1
  have hsep_Q : IsGraphSeparation Q Q₁ Q₂ :=
    ⟨hQ₁_le, hQ₂_le,
      by rw [← vertexSet_subgraphUnion Q Q₁ Q₂, hunion_Q],
      by rw [← edgeSet_subgraphUnion hQ₁_le hQ₂_le, hunion_Q],
      hdisj_EQ⟩
  have hr_ends : r ∈ ({s₁, t₁, s₂, t₂} : Set α) :=
    S.mem_ends_of_isCross_of_not_hasCross hG₁ hbar₁ hrest hno_cross hdisj_P hP₁ hP₂ hcr
  have hr_P₁₂ : r ∈ V(P₁) ∪ V(P₂) := by
    rcases hr_ends with rfl | rfl | rfl | rfl
    · exact Or.inl hP₁.1.left_mem
    · exact Or.inl hP₁.1.right_mem
    · exact Or.inr hP₂.1.left_mem
    · exact Or.inr hP₂.1.right_mem
  have hQ₁_G : IsGraphPathWithEnds S.G Q₁ e₀ r := hQ₁_path.mono hQ.1.le
  obtain ⟨e₀', he₀'_eq, a', ha'_P₁₂, A, hA_Q₁, hA_ft⟩ :=
    hQ₁_G.exists_isFromToPathWithEnds (X := {e₀}) (Y := V(P₁) ∪ V(P₂)) rfl hr_P₁₂
  rw [mem_singleton_iff] at he₀'_eq
  subst he₀'_eq
  rcases ha'_P₁₂ with ha'_P₁ | ha'_P₂
  · exact S.end_mem_of_hit_left hG₁ hbar₁ hrest hno_cross hQ hno_int hr_Q hre₁_empty
      hsep_Q hinter_Q hQ₂_path.right_mem hdisj_P hP₁ hP₂ hcr hmin hA_Q₁ hA_ft.1 hA_ft.2.2 ha'_P₁
  · have hP₁_le : P₁ ≤ S.G := hG₁ ▸ hP₁.1.le
    have hP₂_le : P₂ ≤ S.G := hG₁ ▸ hP₂.1.le
    have hmin_swap : ∀ P₂' P₁' : Graph α β, S₁.IsCross P₂' P₁' →
        subgraphUnion S.G (subgraphUnion S.G P₂' P₁') Q ≤
          subgraphUnion S.G (subgraphUnion S.G P₂ P₁) Q →
        V(subgraphUnion S.G (subgraphUnion S.G P₂' P₁') Q) =
          V(subgraphUnion S.G (subgraphUnion S.G P₂ P₁) Q) ∧
        E(subgraphUnion S.G (subgraphUnion S.G P₂' P₁') Q) =
          E(subgraphUnion S.G (subgraphUnion S.G P₂ P₁) Q) := by
      intro P₂' P₁' hcr' hle'
      obtain ⟨hdisj', a₁, b₁, a₂, b₂, h1', h2', hcr_ends'⟩ := hcr'
      have hcr_swap : S₁.IsCross P₁' P₂' :=
        ⟨hdisj'.symm, a₂, b₂, a₁, b₁, h2', h1', hcr_ends'.symm⟩
      have hP₂'_le : P₂' ≤ S.G := hG₁ ▸ h1'.1.le
      have hP₁'_le : P₁' ≤ S.G := hG₁ ▸ h2'.1.le
      rw [subgraphUnion_comm hP₂'_le hP₁'_le, subgraphUnion_comm hP₂_le hP₁_le] at hle' ⊢
      exact hmin P₁' P₂' hcr_swap hle'
    have hA_inter' : V(A) ∩ (V(P₂) ∪ V(P₁)) = {a'} := by
      rw [union_comm]
      exact hA_ft.2.2
    have hmem := S.end_mem_of_hit_left hG₁ hbar₁ hrest hno_cross hQ hno_int hr_Q hre₁_empty
      hsep_Q hinter_Q hQ₂_path.right_mem hdisj_P.symm hP₂ hP₁ hcr.symm hmin_swap
      hA_Q₁ hA_ft.1 hA_inter' ha'_P₂
    simp only [mem_insert_iff, mem_singleton_iff] at hmem ⊢
    tauto

/-- **Graph Minors IX, (5.3), Claim (1)** (page 53):
"Either $(K, \Omega)$ has a cross or $a, b \in \{s_1, t_1, s_2, t_2\}$." -/
theorem lemma_5_3_claim_1 {S₁ : Society α β} {Q P₁ P₂ : Graph α β}
    {a b r s₁ t₁ s₂ t₂ : α}
    (hG₁ : S₁.G = S.G)
    (hbar₁ : S₁.Ω.bar = S.Ω.bar ∪ {r})
    (hrest : S₁.Ω.IsRestriction S.Ω.bar S.Ω)
    (hab_empty : S.Ω.interval a b = ∅)
    (harb : S₁.Ω.IsClockwise3 a r b)
    (hQ : S.IsOmegaPathWithEnds Q a b)
    (hno_int : Disjoint (pathInternalVerts S.G Q) S.Ω.bar)
    (hr_Q : r ∈ V(Q) \ {a, b})
    (hdisj_P : Disjoint V(P₁) V(P₂))
    (hP₁ : S₁.IsOmegaPathWithEnds P₁ s₁ t₁)
    (hP₂ : S₁.IsOmegaPathWithEnds P₂ s₂ t₂)
    (hcr : S₁.Ω.Crosses s₁ t₁ s₂ t₂)
    (hmin : ∀ P₁' P₂' : Graph α β, S₁.IsCross P₁' P₂' →
      subgraphUnion S.G (subgraphUnion S.G P₁' P₂') Q ≤
        subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q →
      V(subgraphUnion S.G (subgraphUnion S.G P₁' P₂') Q) =
        V(subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q) ∧
      E(subgraphUnion S.G (subgraphUnion S.G P₁' P₂') Q) =
        E(subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q)) :
    (∃ M₁ M₂ : Graph α β, S.IsCross M₁ M₂) ∨
      (a ∈ ({s₁, t₁, s₂, t₂} : Set α) ∧ b ∈ ({s₁, t₁, s₂, t₂} : Set α)) := by
  by_cases hcross : ∃ M₁ M₂ : Graph α β, S.IsCross M₁ M₂
  · exact Or.inl hcross
  · right
    obtain ⟨_, hint_ar, hint_rb, _, _⟩ :=
      S.Ω.extension_intervals hbar₁ hrest hab_empty harb
    have ha_mem : a ∈ ({s₁, t₁, s₂, t₂} : Set α) :=
      S.end_mem_of_minimal_cross hG₁ hbar₁ hrest hcross hQ hno_int hr_Q
        (Or.inl hint_rb) hdisj_P hP₁ hP₂ hcr hmin
    have hr_Q_ba : r ∈ V(Q) \ {b, a} := by
      rw [pair_comm]; exact hr_Q
    have hb_mem : b ∈ ({s₁, t₁, s₂, t₂} : Set α) :=
      S.end_mem_of_minimal_cross hG₁ hbar₁ hrest hcross (hQ.symm S) hno_int hr_Q_ba
        (Or.inr hint_ar) hdisj_P hP₁ hP₂ hcr hmin
    exact ⟨ha_mem, hb_mem⟩

/-- If `R` is a path in `G` from `u` to `v` with `u ≠ v` and `¬ G.Adj u v`, then `R` has an
internal vertex `w ∈ V(R) \ {u, v}`. -/
private theorem exists_internal_of_not_adj {G R : Graph α β} {u v : α}
    (hR : IsGraphPathWithEnds G R u v) (huv : u ≠ v) (hnadj : ¬ G.Adj u v) :
    ∃ w ∈ V(R), w ≠ u ∧ w ≠ v := by
  rcases hR with ⟨hRG, W, hW, hVR, _⟩
  cases W with
  | nil _ => exact (huv rfl).elim
  | @cons _ w _ e hlink W' =>
    have hnd : (u :: W'.support).Nodup := hW
    have hu_not : u ∉ W'.support := (List.nodup_cons.mp hnd).1
    have hwu : w ≠ u := fun h => hu_not (h ▸ W'.start_mem_support)
    have hwv : w ≠ v := fun h => hnadj ⟨e, h ▸ hlink.mono hRG⟩
    refine ⟨w, ?_, hwu, hwv⟩
    rw [hVR, mem_ofPred_eq]
    exact List.mem_cons_of_mem u W'.start_mem_support

/-- If `Z` catches `G'`, `X ⊆ V(G')`, and `w₀ ∈ X`, then there exists an `X → Z` path `P ≤ G'` in
`G'`. -/
theorem exists_isFromToPathWithEnds_of_catches {G' : Graph α β} {X Z : Set α} {w₀ : α}
    (hcatch : Catches Z G') (hX : X ⊆ V(G')) (hw₀ : w₀ ∈ X) :
    ∃ d ∈ X, ∃ p_end ∈ Z, ∃ P : Graph α β,
      P ≤ G' ∧ IsFromToPathWithEnds G' P X Z d p_end := by
  obtain ⟨C, hC_comp, hw₀_C⟩ := exists_graphComponent_of_mem (hX hw₀)
  obtain ⟨z₀, hz₀_Z, hz₀_C⟩ := hcatch.2 C hC_comp
  obtain ⟨W_C⟩ := hC_comp.2.1.2 w₀ hw₀_C z₀ hz₀_C
  obtain ⟨W, _, _⟩ := exists_walk_up_of_le hC_comp.1 W_C
  obtain ⟨d, hdX, p_end, hpZ, P, hP_W, _, hP_ft⟩ :=
    exists_isFromToPathWithEnds_of_walk W hw₀ hz₀_Z
  exact ⟨d, hdX, p_end, hpZ, P, hP_W.trans (walkSubgraph_le W), hP_ft⟩

private theorem range_fin3 (x₀ x₁ x₂ : α) : range ![x₀, x₁, x₂] = {x₀, x₁, x₂} := by
  ext z
  simp only [mem_range, mem_insert_iff, mem_singleton_iff, Fin.exists_fin_succ,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ, IsEmpty.exists_iff, or_false]
  tauto

private theorem pairwise_disjoint_fin3 {L₀ L₁ L₂ : Graph α β}
    (h01 : Disjoint V(L₀) V(L₁)) (h02 : Disjoint V(L₀) V(L₂)) (h12 : Disjoint V(L₁) V(L₂)) :
    Pairwise (fun i j : Fin 3 => Disjoint V(![L₀, L₁, L₂] i) V(![L₀, L₁, L₂] j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact h01
  · exact h02
  · exact h01.symm
  · exact (hij rfl).elim
  · exact h12
  · exact h02.symm
  · exact h12.symm
  · exact (hij rfl).elim

/-- Helper for Case 1 of (5.3): when `Disjoint V(P) V(R₂)` and `{a', p_end}` crosses `{b', t₂}`,
constructing `M₁ = (C'_a ∪ R₁_left) ∪ P` and `M₂ = D'.symm ∪ R₂.symm` yields a cross in `S`. -/
private theorem exists_cross_of_disjoint_P_R₂
    {Q R₁ R₂ P C'_a R₁_left D' : Graph α β} {a' b' c u' d p_end t₂ : α}
    (ha'_bar : a' ∈ S.Ω.bar) (hb'_bar : b' ∈ S.Ω.bar)
    (hp_bar : p_end ∈ S.Ω.bar) (ht₂_bar : t₂ ∈ S.Ω.bar)
    (ha'_p : a' ≠ p_end) (hb'_t₂ : b' ≠ t₂)
    (hcr : S.Ω.Crosses a' p_end b' t₂)
    (hCa_Q : C'_a ≤ Q) (hD'_Q : D' ≤ Q)
    (hdisj_Ca_D' : Disjoint V(C'_a) V(D'))
    (hc_not_Ca : c ∉ V(C'_a))
    (hCa_path : IsGraphPathWithEnds S.G C'_a a' u')
    (hD'_path : IsGraphPathWithEnds S.G D' b' c)
    (hR₁_left_le : R₁_left ≤ R₁)
    (hR₁_left_path : IsGraphPathWithEnds S.G R₁_left u' d)
    (hCa_R₁_inter : V(C'_a) ∩ V(R₁_left) = {u'})
    (hdisj_R₁left_D' : Disjoint V(R₁_left) V(D'))
    (hP_path : IsGraphPathWithEnds S.G P d p_end)
    (hdisj_PQ : Disjoint V(P) V(Q))
    (hPR₁_inter : V(P) ∩ V(R₁) = {d})
    (hR₂_path : IsGraphPathWithEnds S.G R₂ c t₂)
    (hR₂Q_inter : V(R₂) ∩ V(Q) = {c})
    (hdisj_R₁R₂ : Disjoint V(R₁) V(R₂))
    (hdisj_PR₂ : Disjoint V(P) V(R₂)) :
    ∃ M₁ M₂ : Graph α β, S.IsCross M₁ M₂ := by
  let M₁_0 := subgraphUnion S.G C'_a R₁_left
  have hM₁_0_path : IsGraphPathWithEnds S.G M₁_0 a' d :=
    hCa_path.subgraphUnion hR₁_left_path hCa_R₁_inter
  have hinter_M₁0_P : V(M₁_0) ∩ V(P) = {d} := by
    ext z
    simp only [M₁_0, vertexSet_subgraphUnion, mem_inter_iff, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨hzCa | hzR₁, hzP⟩
      · exact (disjoint_left.mp hdisj_PQ hzP (hCa_Q.vertexSet_mono hzCa)).elim
      · have : z ∈ V(P) ∩ V(R₁) := ⟨hzP, hR₁_left_le.vertexSet_mono hzR₁⟩
        rwa [hPR₁_inter, mem_singleton_iff] at this
    · rintro rfl
      exact ⟨Or.inr hR₁_left_path.right_mem, hP_path.left_mem⟩
  let M₁ := subgraphUnion S.G M₁_0 P
  have hM₁_path : IsGraphPathWithEnds S.G M₁ a' p_end :=
    hM₁_0_path.subgraphUnion hP_path hinter_M₁0_P
  have hinter_D'R₂ : V(D') ∩ V(R₂) = {c} := by
    ext z
    simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hzD', hzR₂⟩
      have : z ∈ V(R₂) ∩ V(Q) := ⟨hzR₂, hD'_Q.vertexSet_mono hzD'⟩
      rwa [hR₂Q_inter, mem_singleton_iff] at this
    · rintro rfl
      exact ⟨hD'_path.right_mem, hR₂_path.left_mem⟩
  let M₂ := subgraphUnion S.G D' R₂
  have hM₂_path : IsGraphPathWithEnds S.G M₂ b' t₂ :=
    hD'_path.subgraphUnion hR₂_path hinter_D'R₂
  have hdisj_M₁M₂ : Disjoint V(M₁) V(M₂) := by
    rw [disjoint_left]
    rintro z ((hzCa | hzR₁) | hzP) (hzD' | hzR₂)
    · exact disjoint_left.mp hdisj_Ca_D' hzCa hzD'
    · have hzc : z = c := by
        have : z ∈ V(R₂) ∩ V(Q) := ⟨hzR₂, hCa_Q.vertexSet_mono hzCa⟩
        rwa [hR₂Q_inter, mem_singleton_iff] at this
      exact hc_not_Ca (hzc ▸ hzCa)
    · exact disjoint_left.mp hdisj_R₁left_D' hzR₁ hzD'
    · exact disjoint_left.mp hdisj_R₁R₂ (hR₁_left_le.vertexSet_mono hzR₁) hzR₂
    · exact disjoint_left.mp hdisj_PQ hzP (hD'_Q.vertexSet_mono hzD')
    · exact disjoint_left.mp hdisj_PR₂ hzP hzR₂
  exact ⟨M₁, M₂, hdisj_M₁M₂, a', p_end, b', t₂,
    ⟨hM₁_path, ha'_p, ha'_bar, hp_bar⟩,
    ⟨hM₂_path, hb'_t₂, hb'_bar, ht₂_bar⟩, hcr⟩

private theorem crossFromSplitPaths {Q R₁ R₂ C D C_a D_b R1C R1D P : Graph α β}
    {a b t₂ c u₁ v₁ d p_end : α} (hQ : S.IsOmegaPathWithEnds Q a b)
    (hab_empty : S.Ω.interval a b = ∅) (ht₂_ba : t₂ ∈ S.Ω.interval b a)
    (hR₂_ft : IsFromToPathWithEnds S.G R₂ {t₂} V(Q) t₂ c)
    (hC_Q : C ≤ Q) (hD_Q : D ≤ Q)
    (hC_path : IsGraphPathWithEnds Q C a c) (hD_path : IsGraphPathWithEnds Q D c b)
    (hinter_CD : V(C) ∩ V(D) = {c})
    (hR₁_ft : IsFromToPathWithEnds S.G R₁ V(C) V(D) u₁ v₁)
    (hCa_C : C_a ≤ C) (hDb_D : D_b ≤ D)
    (hCa_path : IsGraphPathWithEnds C C_a a u₁) (hDb_path : IsGraphPathWithEnds D D_b v₁ b)
    (hc_not_Ca : c ∉ V(C_a)) (hc_not_Db : c ∉ V(D_b))
    (hR1C_le : R1C ≤ R₁) (hR1D_le : R1D ≤ R₁)
    (hR1C_path : IsGraphPathWithEnds R₁ R1C u₁ d)
    (hR1D_path : IsGraphPathWithEnds R₁ R1D d v₁)
    (hv₁_not_R1C : v₁ ∉ V(R1C)) (hu₁_not_R1D : u₁ ∉ V(R1D))
    (hp_bar_ab : p_end ∈ S.Ω.bar \ {a, b}) (hP_G : IsGraphPathWithEnds S.G P d p_end)
    (hdisj_PQ : Disjoint V(P) V(Q)) (hPR₁_inter : V(P) ∩ V(R₁) = {d})
    (hdisj_R₁R₂ : Disjoint V(R₁) V(R₂)) (hdisj_PR₂ : Disjoint V(P) V(R₂)) :
    ∃ M₁ M₂ : Graph α β, S.IsCross M₁ M₂ := by
  have hp_ba : p_end ∈ S.Ω.interval b a := by
    have hun := S.Ω.interval_union_interval_swap hQ.2.2.1 hQ.2.2.2 hQ.2.1
    rw [hab_empty, empty_union] at hun
    rwa [hun]
  have hp_ne_t₂ : p_end ≠ t₂ := fun h =>
    disjoint_left.mp hdisj_PR₂ hP_G.right_mem (h ▸ hR₂_ft.1.left_mem)
  have hp_union : p_end ∈ S.Ω.interval b t₂ ∪ {t₂} ∪ S.Ω.interval t₂ a := by
    rw [← S.Ω.interval_eq_union_of_mem ht₂_ba]
    exact hp_ba
  have ha_bt₂ : a ∈ S.Ω.interval t₂ b := S.Ω.mem_interval_rotate_left ht₂_ba
  have hb_t₂a : b ∈ S.Ω.interval a t₂ := S.Ω.mem_interval_rotate_right ht₂_ba
  have hp_not_ab : p_end ∉ ({a, b} : Set α) := hp_bar_ab.2
  have ht₂_not_ab : t₂ ∉ ({a, b} : Set α) := by
    intro h
    rcases h with ht₂a | ht₂b
    · exact S.Ω.not_mem_interval_right b a (ht₂a ▸ ht₂_ba)
    · exact S.Ω.not_mem_interval_left b a (mem_singleton_iff.mp ht₂b ▸ ht₂_ba)
  rcases hp_union with (hp_bt₂ | h_eq) | hp_t₂a
  · -- `p_end ∈ Ω(b, t₂)`: `{a, p_end}` crosses `{b, t₂}`.
    have hcr_ap_bt₂ : S.Ω.Crosses a p_end b t₂ :=
      (S.Ω.crosses_iff_interval.mpr (Or.inl ⟨hp_bt₂, ha_bt₂⟩)).symm.swap_left
    have hdisj_Ca_D : Disjoint V(C_a) V(D) := by
      rw [disjoint_left]
      intro z hzCa hzD
      have : z ∈ V(C) ∩ V(D) := ⟨hCa_C.vertexSet_mono hzCa, hzD⟩
      rw [hinter_CD, mem_singleton_iff] at this
      exact hc_not_Ca (this ▸ hzCa)
    have hCa_R1C_inter : V(C_a) ∩ V(R1C) = {u₁} := by
      ext z
      simp only [mem_inter_iff, mem_singleton_iff]
      refine ⟨fun ⟨hzCa, hzR⟩ => ?_, fun h => h ▸ ⟨hCa_path.right_mem, hR1C_path.left_mem⟩⟩
      have : z ∈ V(R₁) ∩ V(C) := ⟨hR1C_le.vertexSet_mono hzR, hCa_C.vertexSet_mono hzCa⟩
      rwa [hR₁_ft.2.1, mem_singleton_iff] at this
    have hdisj_R1C_D : Disjoint V(R1C) V(D) := by
      rw [disjoint_left]
      intro z hzR hzD
      have : z ∈ V(R₁) ∩ V(D) := ⟨hR1C_le.vertexSet_mono hzR, hzD⟩
      rw [hR₁_ft.2.2, mem_singleton_iff] at this
      exact hv₁_not_R1C (this ▸ hzR)
    exact S.exists_cross_of_disjoint_P_R₂
      hQ.2.2.1 hQ.2.2.2 hp_bar_ab.1 ht₂_ba.1.1
      (fun h => hp_not_ab (Or.inl h.symm))
      (fun h => ht₂_not_ab (Or.inr h.symm))
      hcr_ap_bt₂ (hCa_C.trans hC_Q) hD_Q hdisj_Ca_D hc_not_Ca
      (hCa_path.mono (hC_Q.trans hQ.1.le)) (hD_path.mono hQ.1.le).symm
      hR1C_le (hR1C_path.mono hR₁_ft.1.le) hCa_R1C_inter hdisj_R1C_D
      hP_G hdisj_PQ hPR₁_inter hR₂_ft.1.symm hR₂_ft.2.2 hdisj_R₁R₂ hdisj_PR₂
  · exact (hp_ne_t₂ (mem_singleton_iff.mp h_eq)).elim
  · -- `p_end ∈ Ω(t₂, a)`: `{b, p_end}` crosses `{a, t₂}`.
    have hcr_bp_at₂ : S.Ω.Crosses b p_end a t₂ :=
      (S.Ω.crosses_iff_interval.mpr (Or.inl ⟨hp_t₂a, hb_t₂a⟩)).symm.swap_left.swap_right
    have hdisj_Db_C : Disjoint V(D_b) V(C) := by
      rw [disjoint_left]
      intro z hzDb hzC
      have : z ∈ V(C) ∩ V(D) := ⟨hzC, hDb_D.vertexSet_mono hzDb⟩
      rw [hinter_CD, mem_singleton_iff] at this
      exact hc_not_Db (this ▸ hzDb)
    have hDb_R1D_inter : V(D_b) ∩ V(R1D) = {v₁} := by
      ext z
      simp only [mem_inter_iff, mem_singleton_iff]
      refine ⟨fun ⟨hzDb, hzR⟩ => ?_, fun h => h ▸ ⟨hDb_path.left_mem, hR1D_path.right_mem⟩⟩
      have : z ∈ V(R₁) ∩ V(D) := ⟨hR1D_le.vertexSet_mono hzR, hDb_D.vertexSet_mono hzDb⟩
      rwa [hR₁_ft.2.2, mem_singleton_iff] at this
    have hdisj_R1D_C : Disjoint V(R1D) V(C) := by
      rw [disjoint_left]
      intro z hzR hzC
      have : z ∈ V(R₁) ∩ V(C) := ⟨hR1D_le.vertexSet_mono hzR, hzC⟩
      rw [hR₁_ft.2.1, mem_singleton_iff] at this
      exact hu₁_not_R1D (this ▸ hzR)
    exact S.exists_cross_of_disjoint_P_R₂
      hQ.2.2.2 hQ.2.2.1 hp_bar_ab.1 ht₂_ba.1.1
      (fun h => hp_not_ab (Or.inr h.symm))
      (fun h => ht₂_not_ab (Or.inl h.symm))
      hcr_bp_at₂ (hDb_D.trans hD_Q) hC_Q hdisj_Db_C hc_not_Db
      (hDb_path.mono (hD_Q.trans hQ.1.le)).symm (hC_path.mono hQ.1.le)
      hR1D_le (hR1D_path.mono hR₁_ft.1.le).symm hDb_R1D_inter hdisj_R1D_C
      hP_G hdisj_PQ hPR₁_inter hR₂_ft.1.symm hR₂_ft.2.2 hdisj_R₁R₂ hdisj_PR₂

private theorem redirectsTo_branchEnds
    {Q P₁ C D R₁ R₂ C_a C_c D_c D_b R1C R1D P R2t R2c P_d L₃ : Graph α β}
    {a b c d u₁ v₁ t₂ z t₃ : α}
    (hQ : S.IsOmegaPathWithEnds Q a b)
    (hno_int : Disjoint (pathInternalVerts S.G Q) S.Ω.bar)
    (hP₁ : IsGraphPathWithEnds S.G P₁ a b) (hc_not_P₁ : c ∉ V(P₁))
    (hC_Q : C ≤ Q) (hD_Q : D ≤ Q)
    (hC_path : IsGraphPathWithEnds Q C a c) (hD_path : IsGraphPathWithEnds Q D c b)
    (hinter_CD : V(C) ∩ V(D) = {c})
    (hR₁_ft : IsFromToPathWithEnds S.G R₁ V(C) V(D) u₁ v₁)
    (hR₂_ft : IsFromToPathWithEnds S.G R₂ {t₂} V(Q) t₂ c)
    (hCa_C : C_a ≤ C) (hCc_C : C_c ≤ C) (hDc_D : D_c ≤ D) (hDb_D : D_b ≤ D)
    (hCa_path : IsGraphPathWithEnds C C_a a u₁) (hDb_path : IsGraphPathWithEnds D D_b v₁ b)
    (hinter_CaCc : V(C_a) ∩ V(C_c) = {u₁}) (hinter_DcDb : V(D_c) ∩ V(D_b) = {v₁})
    (hc_not_Ca : c ∉ V(C_a)) (hc_not_Db : c ∉ V(D_b))
    (hR1C_le : R1C ≤ R₁) (hR1D_le : R1D ≤ R₁)
    (hu₁_not_R1D : u₁ ∉ V(R1D)) (hv₁_not_R1C : v₁ ∉ V(R1C))
    (hR1C_G : IsGraphPathWithEnds S.G R1C d u₁) (hR1D_G : IsGraphPathWithEnds S.G R1D d v₁)
    (hR2t_le : R2t ≤ R₂) (hR2c_le : R2c ≤ R₂) (hR2c_path : IsGraphPathWithEnds R₂ R2c z c)
    (hinter_R2 : V(R2t) ∩ V(R2c) = {z}) (hz_ne_c : z ≠ c) (hPd_P : P_d ≤ P)
    (hPd_ft : IsFromToPathWithEnds S.G P_d {d} V(R₂) d z)
    (hL₃_R2t : L₃ ≤ R2t) (hL₃_ft : IsFromToPathWithEnds S.G L₃ {z} S.Ω.bar z t₃)
    (hdisj_PQ : Disjoint V(P) V(Q)) (hdisj_R₁R₂ : Disjoint V(R₁) V(R₂)) :
    RedirectsTo S.G
      (V(subgraphUnion S.G R1C C_c) ∪ V(subgraphUnion S.G R1D D_c) ∪
        V(subgraphUnion S.G P_d R2c)) S.Ω.bar {u₁, v₁, z} {a, b, t₃} := by
  let N₁ := subgraphUnion S.G R1C C_c
  let N₂ := subgraphUnion S.G R1D D_c
  let N₃ := subgraphUnion S.G P_d R2c
  let X_N := V(N₁) ∪ V(N₂) ∪ V(N₃)
  have hQ_bar_inter : V(Q) ∩ S.Ω.bar = {a, b} := by
    apply Subset.antisymm
    · intro w ⟨hwQ, hw_bar⟩
      by_contra hnot
      exact disjoint_left.mp hno_int
        (by rw [hQ.1.pathInternalVerts_eq]; exact ⟨hwQ, hnot⟩) hw_bar
    · rintro w (rfl | rfl)
      · exact ⟨hQ.1.left_mem, hQ.2.2.1⟩
      · exact ⟨hQ.1.right_mem, hQ.2.2.2⟩
  have hb_not_C : b ∉ V(C) := fun hbC => by
    have hbc : b = c := by
      have : b ∈ V(C) ∩ V(D) := ⟨hbC, hD_path.right_mem⟩
      rwa [hinter_CD, mem_singleton_iff] at this
    exact hc_not_P₁ (hbc ▸ hP₁.right_mem)
  have ha_not_D : a ∉ V(D) := fun haD => by
    have hac : a = c := by
      have : a ∈ V(C) ∩ V(D) := ⟨hC_path.left_mem, haD⟩
      rwa [hinter_CD, mem_singleton_iff] at this
    exact hc_not_P₁ (hac ▸ hP₁.left_mem)
  have hL₁_ft : IsFromToPathWithEnds S.G C_a X_N S.Ω.bar u₁ a := by
    refine ⟨(hCa_path.mono (hC_Q.trans hQ.1.le)).symm, ?_, ?_⟩
    · apply Subset.antisymm
      · rintro w ⟨hwCa, ((hwR1C | hwCc) | (hwR1D | hwDc)) | (hwPd | hwR2c)⟩
        · have : w ∈ V(R₁) ∩ V(C) := ⟨hR1C_le.vertexSet_mono hwR1C, hCa_C.vertexSet_mono hwCa⟩
          rwa [hR₁_ft.2.1] at this
        · have : w ∈ V(C_a) ∩ V(C_c) := ⟨hwCa, hwCc⟩
          rwa [hinter_CaCc] at this
        · have : w ∈ V(R₁) ∩ V(C) := ⟨hR1D_le.vertexSet_mono hwR1D, hCa_C.vertexSet_mono hwCa⟩
          rw [hR₁_ft.2.1, mem_singleton_iff] at this
          exact (hu₁_not_R1D (this ▸ hwR1D)).elim
        · have : w ∈ V(C) ∩ V(D) := ⟨hCa_C.vertexSet_mono hwCa, hDc_D.vertexSet_mono hwDc⟩
          rw [hinter_CD, mem_singleton_iff] at this
          exact (hc_not_Ca (this ▸ hwCa)).elim
        · exact (disjoint_left.mp hdisj_PQ
            (hPd_P.vertexSet_mono hwPd) ((hCa_C.trans hC_Q).vertexSet_mono hwCa)).elim
        · have : w ∈ V(R₂) ∩ V(Q) :=
            ⟨hR2c_le.vertexSet_mono hwR2c, (hCa_C.trans hC_Q).vertexSet_mono hwCa⟩
          rw [hR₂_ft.2.2, mem_singleton_iff] at this
          exact (hc_not_Ca (this ▸ hwCa)).elim
      · rintro w rfl
        exact ⟨hCa_path.right_mem, Or.inl (Or.inl (Or.inl hR1C_G.right_mem))⟩
    · apply Subset.antisymm
      · rintro w ⟨hwCa, hw_bar⟩
        have : w ∈ V(Q) ∩ S.Ω.bar := ⟨(hCa_C.trans hC_Q).vertexSet_mono hwCa, hw_bar⟩
        rw [hQ_bar_inter, mem_insert_iff, mem_singleton_iff] at this
        rcases this with rfl | rfl
        · rfl
        · exact (hb_not_C (hCa_C.vertexSet_mono hwCa)).elim
      · rintro w rfl
        exact ⟨hCa_path.left_mem, hQ.2.2.1⟩
  have hL₂_ft : IsFromToPathWithEnds S.G D_b X_N S.Ω.bar v₁ b := by
    refine ⟨hDb_path.mono (hD_Q.trans hQ.1.le), ?_, ?_⟩
    · apply Subset.antisymm
      · rintro w ⟨hwDb, ((hwR1C | hwCc) | (hwR1D | hwDc)) | (hwPd | hwR2c)⟩
        · have : w ∈ V(R₁) ∩ V(D) := ⟨hR1C_le.vertexSet_mono hwR1C, hDb_D.vertexSet_mono hwDb⟩
          rw [hR₁_ft.2.2, mem_singleton_iff] at this
          exact (hv₁_not_R1C (this ▸ hwR1C)).elim
        · have : w ∈ V(C) ∩ V(D) := ⟨hCc_C.vertexSet_mono hwCc, hDb_D.vertexSet_mono hwDb⟩
          rw [hinter_CD, mem_singleton_iff] at this
          exact (hc_not_Db (this ▸ hwDb)).elim
        · have : w ∈ V(R₁) ∩ V(D) := ⟨hR1D_le.vertexSet_mono hwR1D, hDb_D.vertexSet_mono hwDb⟩
          rwa [hR₁_ft.2.2] at this
        · have : w ∈ V(D_c) ∩ V(D_b) := ⟨hwDc, hwDb⟩
          rwa [hinter_DcDb] at this
        · exact (disjoint_left.mp hdisj_PQ
            (hPd_P.vertexSet_mono hwPd) ((hDb_D.trans hD_Q).vertexSet_mono hwDb)).elim
        · have : w ∈ V(R₂) ∩ V(Q) :=
            ⟨hR2c_le.vertexSet_mono hwR2c, (hDb_D.trans hD_Q).vertexSet_mono hwDb⟩
          rw [hR₂_ft.2.2, mem_singleton_iff] at this
          exact (hc_not_Db (this ▸ hwDb)).elim
      · rintro w rfl
        exact ⟨hDb_path.left_mem, Or.inl (Or.inr (Or.inl hR1D_G.right_mem))⟩
    · apply Subset.antisymm
      · rintro w ⟨hwDb, hw_bar⟩
        have : w ∈ V(Q) ∩ S.Ω.bar := ⟨(hDb_D.trans hD_Q).vertexSet_mono hwDb, hw_bar⟩
        rw [hQ_bar_inter, mem_insert_iff, mem_singleton_iff] at this
        rcases this with rfl | rfl
        · exact (ha_not_D (hDb_D.vertexSet_mono hwDb)).elim
        · rfl
      · rintro w rfl
        exact ⟨hDb_path.right_mem, hQ.2.2.2⟩
  have hc_not_R2t : c ∉ V(R2t) := fun hc_R2t =>
    hz_ne_c <| Eq.symm <| by
      have : c ∈ V(R2t) ∩ V(R2c) := ⟨hc_R2t, hR2c_path.right_mem⟩
      rwa [hinter_R2, mem_singleton_iff] at this
  have hL₃_ft' : IsFromToPathWithEnds S.G L₃ X_N S.Ω.bar z t₃ := by
    refine ⟨hL₃_ft.1, ?_, hL₃_ft.2.2⟩
    apply Subset.antisymm
    · rintro w ⟨hwL₃, ((hwR1C | hwCc) | (hwR1D | hwDc)) | (hwPd | hwR2c)⟩
      · exact (disjoint_left.mp hdisj_R₁R₂
          (hR1C_le.vertexSet_mono hwR1C) ((hL₃_R2t.trans hR2t_le).vertexSet_mono hwL₃)).elim
      · have : w ∈ V(R₂) ∩ V(Q) :=
          ⟨(hL₃_R2t.trans hR2t_le).vertexSet_mono hwL₃, (hCc_C.trans hC_Q).vertexSet_mono hwCc⟩
        rw [hR₂_ft.2.2, mem_singleton_iff] at this
        exact (hc_not_R2t (this ▸ hL₃_R2t.vertexSet_mono hwL₃)).elim
      · exact (disjoint_left.mp hdisj_R₁R₂
          (hR1D_le.vertexSet_mono hwR1D) ((hL₃_R2t.trans hR2t_le).vertexSet_mono hwL₃)).elim
      · have : w ∈ V(R₂) ∩ V(Q) :=
          ⟨(hL₃_R2t.trans hR2t_le).vertexSet_mono hwL₃, (hDc_D.trans hD_Q).vertexSet_mono hwDc⟩
        rw [hR₂_ft.2.2, mem_singleton_iff] at this
        exact (hc_not_R2t (this ▸ hL₃_R2t.vertexSet_mono hwL₃)).elim
      · have : w ∈ V(P_d) ∩ V(R₂) := ⟨hwPd, (hL₃_R2t.trans hR2t_le).vertexSet_mono hwL₃⟩
        rwa [hPd_ft.2.2] at this
      · have : w ∈ V(R2t) ∩ V(R2c) := ⟨hL₃_R2t.vertexSet_mono hwL₃, hwR2c⟩
        rwa [hinter_R2] at this
    · rintro w rfl
      exact ⟨hL₃_ft.1.left_mem, Or.inr (Or.inl hPd_ft.1.right_mem)⟩
  have hdisj_L₁L₂ : Disjoint V(C_a) V(D_b) := by
    rw [disjoint_left]
    intro w hwCa hwDb
    have : w ∈ V(C) ∩ V(D) := ⟨hCa_C.vertexSet_mono hwCa, hDb_D.vertexSet_mono hwDb⟩
    rw [hinter_CD, mem_singleton_iff] at this
    exact hc_not_Ca (this ▸ hwCa)
  have hdisj_L₁L₃ : Disjoint V(C_a) V(L₃) := by
    rw [disjoint_left]
    intro w hwCa hwL₃
    have : w ∈ V(R₂) ∩ V(Q) :=
      ⟨(hL₃_R2t.trans hR2t_le).vertexSet_mono hwL₃, (hCa_C.trans hC_Q).vertexSet_mono hwCa⟩
    rw [hR₂_ft.2.2, mem_singleton_iff] at this
    exact hc_not_Ca (this ▸ hwCa)
  have hdisj_L₂L₃ : Disjoint V(D_b) V(L₃) := by
    rw [disjoint_left]
    intro w hwDb hwL₃
    have : w ∈ V(R₂) ∩ V(Q) :=
      ⟨(hL₃_R2t.trans hR2t_le).vertexSet_mono hwL₃, (hDb_D.trans hD_Q).vertexSet_mono hwDb⟩
    rw [hR₂_ft.2.2, mem_singleton_iff] at this
    exact hc_not_Db (this ▸ hwDb)
  have hdisj_L : Pairwise (fun i j : Fin 3 => Disjoint V(![C_a, D_b, L₃] i) V(![C_a, D_b, L₃] j)) :=
    pairwise_disjoint_fin3 hdisj_L₁L₂ hdisj_L₁L₃ hdisj_L₂L₃
  have hL_all : ∀ i : Fin 3,
      IsFromToPathWithEnds S.G (![C_a, D_b, L₃] i) X_N S.Ω.bar (![u₁, v₁, z] i) (![a, b, t₃] i)
        := by
    intro i
    fin_cases i
    · exact hL₁_ft
    · exact hL₂_ft
    · exact hL₃_ft'
  have hred := (redirectsTo_of_disjoint_fromToPaths hdisj_L hL_all).2.2.2.2
  rw [range_fin3, range_fin3] at hred
  exact hred

private theorem tripodFromIntersectingPaths
    {Q P₁ C D R₁ R₂ C_a C_c D_c D_b R1C R1D P : Graph α β}
    {a b c d u₁ v₁ t₂ p_end : α}
    (hQ : S.IsOmegaPathWithEnds Q a b)
    (hno_int : Disjoint (pathInternalVerts S.G Q) S.Ω.bar)
    (hP₁ : IsGraphPathWithEnds S.G P₁ a b) (ht₂_ba : t₂ ∈ S.Ω.interval b a) (hc_Q : c ∈ V(Q))
    (hR₂_ft : IsFromToPathWithEnds S.G R₂ {t₂} V(Q) t₂ c) (hc_not_P₁ : c ∉ V(P₁))
    (hC_Q : C ≤ Q) (hD_Q : D ≤ Q)
    (hC_path : IsGraphPathWithEnds Q C a c) (hD_path : IsGraphPathWithEnds Q D c b)
    (hinter_CD : V(C) ∩ V(D) = {c})
    (hR₁_ft : IsFromToPathWithEnds S.G R₁ V(C) V(D) u₁ v₁)
    (hu₁_ne_c : u₁ ≠ c) (hv₁_ne_c : v₁ ≠ c) (hd_R₁Q : d ∈ V(R₁) \ V(Q))
    (hP_G : IsGraphPathWithEnds S.G P d p_end) (hdisj_PQ : Disjoint V(P) V(Q))
    (hPR₁_inter : V(P) ∩ V(R₁) = {d})
    (hR1C_le : R1C ≤ R₁) (hR1D_le : R1D ≤ R₁)
    (hR1C_path : IsGraphPathWithEnds R₁ R1C u₁ d) (hR1D_path : IsGraphPathWithEnds R₁ R1D d v₁)
    (hinter_R1 : V(R1C) ∩ V(R1D) = {d})
    (hCa_C : C_a ≤ C) (hCc_C : C_c ≤ C)
    (hCa_path : IsGraphPathWithEnds C C_a a u₁) (hCc_path : IsGraphPathWithEnds C C_c u₁ c)
    (hinter_CaCc : V(C_a) ∩ V(C_c) = {u₁})
    (hDc_D : D_c ≤ D) (hDb_D : D_b ≤ D)
    (hDc_path : IsGraphPathWithEnds D D_c c v₁) (hDb_path : IsGraphPathWithEnds D D_b v₁ b)
    (hinter_DcDb : V(D_c) ∩ V(D_b) = {v₁})
    (hc_not_Ca : c ∉ V(C_a)) (hc_not_Db : c ∉ V(D_b))
    (hd_ne_u₁ : d ≠ u₁) (hd_ne_v₁ : d ≠ v₁)
    (hv₁_not_R1C : v₁ ∉ V(R1C)) (hu₁_not_R1D : u₁ ∉ V(R1D))
    (hdisj_R₁R₂ : Disjoint V(R₁) V(R₂)) (hdisj_PR₂ : ¬Disjoint V(P) V(R₂)) :
    ∃ N₁ N₂ N₃ : Graph α β, S.IsTripod N₁ N₂ N₃ := by
  rw [not_disjoint_iff_nonempty_inter] at hdisj_PR₂
  rcases hdisj_PR₂ with ⟨z₀, hz₀_P, hz₀_R₂⟩
  obtain ⟨P_dz₀, hPdz₀_P, _, hPdz₀_G⟩ := hP_G.exists_subpath hP_G.left_mem hz₀_P
  obtain ⟨d', hd'_eq, z, hz_R₂, P_d, hPd_Pdz₀, hPd_ft⟩ :=
    hPdz₀_G.exists_isFromToPathWithEnds (X := {d}) (Y := V(R₂)) rfl hz₀_R₂
  rw [mem_singleton_iff] at hd'_eq
  subst d'
  have hPd_P : P_d ≤ P := hPd_Pdz₀.trans hPdz₀_P
  obtain ⟨R2t, R2c, hR2t_le, hR2c_le, hR2t_path, hR2c_path, _, hinter_R2, _⟩ :=
    hR₂_ft.1.exists_split_at hz_R₂
  -- Extract `{z} → S.Ω.bar` subpath `L₃ ≤ R2t` from `z` to `t₃ ∈ S.Ω.bar`.
  obtain ⟨z', hz'_eq, t₃, ht₃_bar, L₃, hL₃_R2t, hL₃_ft⟩ :=
    (hR2t_path.mono hR₂_ft.1.le).symm.exists_isFromToPathWithEnds
      (X := {z}) (Y := S.Ω.bar) rfl ht₂_ba.1.1
  rw [mem_singleton_iff] at hz'_eq
  subst z'
  -- Build `N₁ = R1C.symm ∪ C_c`, `N₂ = R1D ∪ D_c.symm`, `N₃ = P_d ∪ R2c`.
  have hR1C_G : IsGraphPathWithEnds S.G R1C d u₁ := (hR1C_path.mono hR₁_ft.1.le).symm
  have hCc_G : IsGraphPathWithEnds S.G C_c u₁ c := hCc_path.mono (hC_Q.trans hQ.1.le)
  have hinter_N₁ : V(R1C) ∩ V(C_c) = {u₁} := by
    ext w
    simp only [mem_inter_iff, mem_singleton_iff]
    refine ⟨fun ⟨hwR, hwC⟩ => ?_, fun h => h ▸ ⟨hR1C_G.right_mem, hCc_G.left_mem⟩⟩
    have : w ∈ V(R₁) ∩ V(C) := ⟨hR1C_le.vertexSet_mono hwR, hCc_C.vertexSet_mono hwC⟩
    rwa [hR₁_ft.2.1, mem_singleton_iff] at this
  let N₁ := subgraphUnion S.G R1C C_c
  have hN₁_G : IsGraphPathWithEnds S.G N₁ d c := hR1C_G.subgraphUnion hCc_G hinter_N₁
  have hR1D_G : IsGraphPathWithEnds S.G R1D d v₁ := hR1D_path.mono hR₁_ft.1.le
  have hDc_G : IsGraphPathWithEnds S.G D_c v₁ c := (hDc_path.mono (hD_Q.trans hQ.1.le)).symm
  have hinter_N₂ : V(R1D) ∩ V(D_c) = {v₁} := by
    ext w
    simp only [mem_inter_iff, mem_singleton_iff]
    refine ⟨fun ⟨hwR, hwD⟩ => ?_, fun h => h ▸ ⟨hR1D_G.right_mem, hDc_G.left_mem⟩⟩
    have : w ∈ V(R₁) ∩ V(D) := ⟨hR1D_le.vertexSet_mono hwR, hDc_D.vertexSet_mono hwD⟩
    rwa [hR₁_ft.2.2, mem_singleton_iff] at this
  let N₂ := subgraphUnion S.G R1D D_c
  have hN₂_G : IsGraphPathWithEnds S.G N₂ d c := hR1D_G.subgraphUnion hDc_G hinter_N₂
  have hR2c_G : IsGraphPathWithEnds S.G R2c z c := hR2c_path.mono hR₂_ft.1.le
  have hinter_N₃ : V(P_d) ∩ V(R2c) = {z} := by
    ext w
    simp only [mem_inter_iff, mem_singleton_iff]
    refine ⟨fun ⟨hwP, hwR⟩ => ?_, fun h => h ▸ ⟨hPd_ft.1.right_mem, hR2c_G.left_mem⟩⟩
    have : w ∈ V(P_d) ∩ V(R₂) := ⟨hwP, hR2c_le.vertexSet_mono hwR⟩
    rwa [hPd_ft.2.2, mem_singleton_iff] at this
  let N₃ := subgraphUnion S.G P_d R2c
  have hN₃_G : IsGraphPathWithEnds S.G N₃ d c := hPd_ft.1.subgraphUnion hR2c_G hinter_N₃
  have hdc_ne : d ≠ c := fun h => hd_R₁Q.2 (h ▸ hc_Q)
  -- Pairwise intersections of `V(N₁), V(N₂), V(N₃)` are `{d, c}`.
  have hinter_N₁N₂ : V(N₁) ∩ V(N₂) = {d, c} := by
    apply Subset.antisymm
    · rintro w ⟨hwR1C | hwCc, hwR1D | hwDc⟩
      · have : w ∈ V(R1C) ∩ V(R1D) := ⟨hwR1C, hwR1D⟩
        rw [hinter_R1, mem_singleton_iff] at this
        exact Or.inl this
      · have : w ∈ V(R₁) ∩ V(D) := ⟨hR1C_le.vertexSet_mono hwR1C, hDc_D.vertexSet_mono hwDc⟩
        rw [hR₁_ft.2.2, mem_singleton_iff] at this
        exact (hv₁_not_R1C (this ▸ hwR1C)).elim
      · have : w ∈ V(R₁) ∩ V(C) := ⟨hR1D_le.vertexSet_mono hwR1D, hCc_C.vertexSet_mono hwCc⟩
        rw [hR₁_ft.2.1, mem_singleton_iff] at this
        exact (hu₁_not_R1D (this ▸ hwR1D)).elim
      · have : w ∈ V(C) ∩ V(D) := ⟨hCc_C.vertexSet_mono hwCc, hDc_D.vertexSet_mono hwDc⟩
        rw [hinter_CD, mem_singleton_iff] at this
        exact Or.inr this
    · rintro w (rfl | rfl)
      · exact ⟨hN₁_G.left_mem, hN₂_G.left_mem⟩
      · exact ⟨hN₁_G.right_mem, hN₂_G.right_mem⟩
  have hinter_N₁N₃ : V(N₁) ∩ V(N₃) = {d, c} := by
    apply Subset.antisymm
    · rintro w ⟨hwR1C | hwCc, hwPd | hwR2c⟩
      · have : w ∈ V(P) ∩ V(R₁) := ⟨hPd_P.vertexSet_mono hwPd, hR1C_le.vertexSet_mono hwR1C⟩
        rw [hPR₁_inter, mem_singleton_iff] at this
        exact Or.inl this
      · exact (disjoint_left.mp hdisj_R₁R₂
          (hR1C_le.vertexSet_mono hwR1C) (hR2c_le.vertexSet_mono hwR2c)).elim
      · exact (disjoint_left.mp hdisj_PQ
          (hPd_P.vertexSet_mono hwPd) ((hCc_C.trans hC_Q).vertexSet_mono hwCc)).elim
      · have : w ∈ V(R₂) ∩ V(Q) :=
          ⟨hR2c_le.vertexSet_mono hwR2c, (hCc_C.trans hC_Q).vertexSet_mono hwCc⟩
        rw [hR₂_ft.2.2, mem_singleton_iff] at this
        exact Or.inr this
    · rintro w (rfl | rfl)
      · exact ⟨hN₁_G.left_mem, hN₃_G.left_mem⟩
      · exact ⟨hN₁_G.right_mem, hN₃_G.right_mem⟩
  have hinter_N₂N₃ : V(N₂) ∩ V(N₃) = {d, c} := by
    apply Subset.antisymm
    · rintro w ⟨hwR1D | hwDc, hwPd | hwR2c⟩
      · have : w ∈ V(P) ∩ V(R₁) := ⟨hPd_P.vertexSet_mono hwPd, hR1D_le.vertexSet_mono hwR1D⟩
        rw [hPR₁_inter, mem_singleton_iff] at this
        exact Or.inl this
      · exact (disjoint_left.mp hdisj_R₁R₂
          (hR1D_le.vertexSet_mono hwR1D) (hR2c_le.vertexSet_mono hwR2c)).elim
      · exact (disjoint_left.mp hdisj_PQ
          (hPd_P.vertexSet_mono hwPd) ((hDc_D.trans hD_Q).vertexSet_mono hwDc)).elim
      · have : w ∈ V(R₂) ∩ V(Q) :=
          ⟨hR2c_le.vertexSet_mono hwR2c, (hDc_D.trans hD_Q).vertexSet_mono hwDc⟩
        rw [hR₂_ft.2.2, mem_singleton_iff] at this
        exact Or.inr this
    · rintro w (rfl | rfl)
      · exact ⟨hN₂_G.left_mem, hN₃_G.left_mem⟩
      · exact ⟨hN₂_G.right_mem, hN₃_G.right_mem⟩
  -- Internal vertices `u₁ ∈ V(N₁) \ {d, c}`, `v₁ ∈ V(N₂) \ {d, c}`, `z ∈ V(N₃) \ {d, c}`.
  have hu₁_int : u₁ ∈ V(N₁) \ {d, c} := by
    refine ⟨Or.inl hR1C_G.right_mem, ?_⟩
    simp [hd_ne_u₁.symm, hu₁_ne_c]
  have hv₁_int : v₁ ∈ V(N₂) \ {d, c} := by
    refine ⟨Or.inl hR1D_G.right_mem, ?_⟩
    simp [hd_ne_v₁.symm, hv₁_ne_c]
  have hz_ne_d : z ≠ d := fun h =>
    disjoint_left.mp hdisj_R₁R₂ hd_R₁Q.1 (h ▸ hz_R₂)
  have hz_ne_c : z ≠ c := fun h =>
    disjoint_left.mp hdisj_PQ (hPd_P.vertexSet_mono hPd_ft.1.right_mem) (h ▸ hc_Q)
  have hz_int : z ∈ V(N₃) \ {d, c} := by
    refine ⟨Or.inl hPd_ft.1.right_mem, ?_⟩
    simp [hz_ne_d, hz_ne_c]
  have hred := S.redirectsTo_branchEnds hQ hno_int hP₁ hc_not_P₁ hC_Q hD_Q
    hC_path hD_path hinter_CD hR₁_ft hR₂_ft hCa_C hCc_C hDc_D hDb_D
    hCa_path hDb_path hinter_CaCc hinter_DcDb hc_not_Ca hc_not_Db
    hR1C_le hR1D_le hu₁_not_R1D hv₁_not_R1C hR1C_G hR1D_G
    hR2t_le hR2c_le hR2c_path hinter_R2 hz_ne_c hPd_P hPd_ft
    hL₃_R2t hL₃_ft hdisj_PQ hdisj_R₁R₂
  exact ⟨N₁, N₂, N₃, d, c, hdc_ne, hN₁_G, hN₂_G, hN₃_G,
    hinter_N₁N₂, hinter_N₁N₃, hinter_N₂N₃,
    u₁, hu₁_int, v₁, hv₁_int, z, hz_int,
    a, hQ.2.2.1, b, hQ.2.2.2, t₃, ht₃_bar, hred⟩

/-- Main geometric construction of (5.3) once `{P₁, P₂}` is normalized so that `P₁` has ends `a, b`
and `P₂` has ends `r, t₂` with `t₂ ∈ Ω(b, a)`. -/
private theorem theorem_5_3_of_normalized {Q P₁ P₂ : Graph α β} {a b r t₂ : α}
    (hQ : S.IsOmegaPathWithEnds Q a b)
    (hQ_ind : S.G.induce V(Q) = Q)
    (hno_int : Disjoint (pathInternalVerts S.G Q) S.Ω.bar)
    (hab_empty : S.Ω.interval a b = ∅)
    (hcatch : Catches (S.Ω.bar \ {a, b}) (deleteVertices S.G V(Q)))
    (hr_Q : r ∈ V(Q))
    (hdisj_P : Disjoint V(P₁) V(P₂))
    (hP₁ : IsGraphPathWithEnds S.G P₁ a b)
    (hP₂ : IsGraphPathWithEnds S.G P₂ r t₂)
    (ht₂_ba : t₂ ∈ S.Ω.interval b a) :
    (∃ M₁ M₂ : Graph α β, S.IsCross M₁ M₂) ∨
      (∃ N₁ N₂ N₃ : Graph α β, S.IsTripod N₁ N₂ N₃) := by
  -- Extract minimal subpath `R₂ ≤ P₂` from `{t₂}` to `V(Q)` with ends `t₂, c`.
  obtain ⟨t₂', ht₂'_eq, c, hc_Q, R₂, hR₂_P₂, hR₂_ft⟩ :=
    hP₂.symm.exists_isFromToPathWithEnds (X := {t₂}) (Y := V(Q)) rfl hr_Q
  rw [mem_singleton_iff] at ht₂'_eq
  subst t₂'
  have hc_not_P₁ : c ∉ V(P₁) := fun hc₁ =>
    disjoint_left.mp hdisj_P hc₁ (hR₂_P₂.vertexSet_mono hR₂_ft.1.right_mem)
  -- Split `Q` at `c` into `C` (from `a` to `c`) and `D` (from `c` to `b`).
  obtain ⟨C, D, hC_Q, hD_Q, hC_path, hD_path, hunion_CD, hinter_CD, hdisj_ECD⟩ :=
    hQ.1.exists_split_at hc_Q
  have hVC_UD : V(C) ∪ V(D) = V(Q) := by
    rw [← vertexSet_subgraphUnion Q C D, hunion_CD]
  have hEC_UD : E(C) ∪ E(D) = E(Q) := by
    rw [← edgeSet_subgraphUnion hC_Q hD_Q, hunion_CD]
  -- Extract minimal subpath `R₁ ≤ P₁` from `V(C)` to `V(D)` with ends `u₁ ∈ V(C)` and `v₁ ∈ V(D)`.
  obtain ⟨u₁, hu₁_C, v₁, hv₁_D, R₁, hR₁_P₁, hR₁_ft⟩ :=
    hP₁.exists_isFromToPathWithEnds (X := V(C)) (Y := V(D)) hC_path.left_mem hD_path.right_mem
  have hu₁_ne_c : u₁ ≠ c := fun h => hc_not_P₁ (h ▸ hR₁_P₁.vertexSet_mono hR₁_ft.1.left_mem)
  have hv₁_ne_c : v₁ ≠ c := fun h => hc_not_P₁ (h ▸ hR₁_P₁.vertexSet_mono hR₁_ft.1.right_mem)
  have hu₁_not_D : u₁ ∉ V(D) := fun h =>
    hu₁_ne_c (by
      have : u₁ ∈ V(C) ∩ V(D) := ⟨hu₁_C, h⟩
      rwa [hinter_CD, mem_singleton_iff] at this)
  have hv₁_not_C : v₁ ∉ V(C) := fun h =>
    hv₁_ne_c (by
      have : v₁ ∈ V(C) ∩ V(D) := ⟨h, hv₁_D⟩
      rwa [hinter_CD, mem_singleton_iff] at this)
  have hu₁v₁_ne : u₁ ≠ v₁ := fun h => hu₁_not_D (h ▸ hv₁_D)
  have hR₁_Q_inter : V(R₁) ∩ V(Q) = {u₁, v₁} := by
    rw [← hVC_UD, inter_union_distrib_left, hR₁_ft.2.1, hR₁_ft.2.2]
    rfl
  -- Since `Q` is induced in `S.G`, `u₁` and `v₁` are not adjacent in `S.G`.
  have hnadj_uv : ¬ S.G.Adj u₁ v₁ := by
    rintro ⟨e, huv⟩
    have huv_Q : Q.IsLink e u₁ v₁ := by
      rw [← hQ_ind, induce_isLink]
      exact ⟨huv, hC_Q.vertexSet_mono hu₁_C, hD_Q.vertexSet_mono hv₁_D⟩
    have he_CD : e ∈ E(C) ∪ E(D) := hEC_UD.symm ▸ huv_Q.edge_mem
    rcases he_CD with heC | heD
    · have hlinkC : C.IsLink e u₁ v₁ := (hC_Q.isLink_iff heC).mpr huv_Q
      exact hv₁_not_C hlinkC.right_mem
    · have hlinkD : D.IsLink e u₁ v₁ := (hD_Q.isLink_iff heD).mpr huv_Q
      exact hu₁_not_D hlinkD.left_mem
  obtain ⟨w₀, hw₀_R₁, hw₀_u₁, hw₀_v₁⟩ :=
    exists_internal_of_not_adj hR₁_ft.1 hu₁v₁_ne hnadj_uv
  have hw₀_not_Q : w₀ ∉ V(Q) := by
    intro hw₀_Q
    have : w₀ ∈ V(R₁) ∩ V(Q) := ⟨hw₀_R₁, hw₀_Q⟩
    rw [hR₁_Q_inter, mem_insert_iff, mem_singleton_iff] at this
    rcases this with rfl | rfl
    · exact hw₀_u₁ rfl
    · exact hw₀_v₁ rfl
  -- Use `hcatch` to find a `(V(R₁) \ V(Q)) → (S.Ω.bar \ {a, b})` path `P ≤ deleteVertices S.G
  -- V(Q)`.
  let G_del := deleteVertices S.G V(Q)
  have hX_sub : V(R₁) \ V(Q) ⊆ V(G_del) :=
    sdiff_le_sdiff_right hR₁_ft.1.le.vertexSet_mono
  obtain ⟨d, hd_R₁Q, p_end, hp_bar_ab, P, hP_Gdel, hP_ft⟩ :=
    exists_isFromToPathWithEnds_of_catches hcatch hX_sub ⟨hw₀_R₁, hw₀_not_Q⟩
  have hP_G : IsGraphPathWithEnds S.G P d p_end :=
    hP_ft.1.mono (deleteVertices_le S.G V(Q))
  have hdisj_PQ : Disjoint V(P) V(Q) :=
    disjoint_left.mpr fun z hzP hzQ => (hP_Gdel.vertexSet_mono hzP).2 hzQ
  have hPR₁_inter : V(P) ∩ V(R₁) = {d} := by
    rw [← hP_ft.2.1]
    ext z
    simp only [mem_inter_iff, mem_sdiff]
    exact ⟨fun ⟨hzP, hzR₁⟩ => ⟨hzP, hzR₁, disjoint_left.mp hdisj_PQ hzP⟩,
      fun ⟨hzP, hzR₁, _⟩ => ⟨hzP, hzR₁⟩⟩
  -- Split `R₁` at `d`, `C` at `u₁`, and `D` at `v₁`.
  obtain ⟨R1C, R1D, hR1C_le, hR1D_le, hR1C_path, hR1D_path, _, hinter_R1, _⟩ :=
    hR₁_ft.1.exists_split_at hd_R₁Q.1
  obtain ⟨C_a, C_c, hCa_C, hCc_C, hCa_path, hCc_path, _, hinter_CaCc, _⟩ :=
    (hC_path.mono hQ.1.le).exists_split_at hu₁_C
  obtain ⟨D_c, D_b, hDc_D, hDb_D, hDc_path, hDb_path, _, hinter_DcDb, _⟩ :=
    (hD_path.mono hQ.1.le).exists_split_at hv₁_D
  have hc_not_Ca : c ∉ V(C_a) := fun hc_Ca =>
    hu₁_ne_c <| Eq.symm <| by
      have : c ∈ V(C_a) ∩ V(C_c) := ⟨hc_Ca, hCc_path.right_mem⟩
      rwa [hinter_CaCc, mem_singleton_iff] at this
  have hc_not_Db : c ∉ V(D_b) := fun hc_Db =>
    hv₁_ne_c <| Eq.symm <| by
      have : c ∈ V(D_c) ∩ V(D_b) := ⟨hDc_path.left_mem, hc_Db⟩
      rwa [hinter_DcDb, mem_singleton_iff] at this
  have hd_ne_u₁ : d ≠ u₁ := fun h => hd_R₁Q.2 (h ▸ hC_Q.vertexSet_mono hu₁_C)
  have hd_ne_v₁ : d ≠ v₁ := fun h => hd_R₁Q.2 (h ▸ hD_Q.vertexSet_mono hv₁_D)
  have hv₁_not_R1C : v₁ ∉ V(R1C) := fun h =>
    hd_ne_v₁ <| Eq.symm <| by
      have : v₁ ∈ V(R1C) ∩ V(R1D) := ⟨h, hR1D_path.right_mem⟩
      rwa [hinter_R1, mem_singleton_iff] at this
  have hu₁_not_R1D : u₁ ∉ V(R1D) := fun h =>
    hd_ne_u₁ <| Eq.symm <| by
      have : u₁ ∈ V(R1C) ∩ V(R1D) := ⟨hR1C_path.left_mem, h⟩
      rwa [hinter_R1, mem_singleton_iff] at this
  have hdisj_R₁R₂ : Disjoint V(R₁) V(R₂) :=
    hdisj_P.mono hR₁_P₁.vertexSet_mono hR₂_P₂.vertexSet_mono
  -- Branch on whether `V(P)` and `V(R₂)` are disjoint.
  by_cases hdisj_PR₂ : Disjoint V(P) V(R₂)
  · -- Case 1: `Disjoint V(P) V(R₂)` yields a cross in `S`.
    exact Or.inl (S.crossFromSplitPaths hQ hab_empty ht₂_ba hR₂_ft hC_Q hD_Q
      hC_path hD_path hinter_CD hR₁_ft hCa_C hDb_D hCa_path hDb_path hc_not_Ca hc_not_Db
      hR1C_le hR1D_le hR1C_path hR1D_path hv₁_not_R1C hu₁_not_R1D
      hp_bar_ab hP_G hdisj_PQ hPR₁_inter hdisj_R₁R₂ hdisj_PR₂)
  · exact Or.inr (S.tripodFromIntersectingPaths hQ hno_int hP₁ ht₂_ba hc_Q hR₂_ft
      hc_not_P₁ hC_Q hD_Q hC_path hD_path hinter_CD hR₁_ft hu₁_ne_c hv₁_ne_c
      hd_R₁Q hP_G hdisj_PQ hPR₁_inter hR1C_le hR1D_le hR1C_path hR1D_path hinter_R1
      hCa_C hCc_C hCa_path hCc_path hinter_CaCc
      hDc_D hDb_D hDc_path hDb_path hinter_DcDb hc_not_Ca hc_not_Db hd_ne_u₁ hd_ne_v₁
      hv₁_not_R1C hu₁_not_R1D hdisj_R₁R₂ hdisj_PR₂)

/-- Helper for (5.3): once `a, b, r ∈ {s₁, t₁, s₂, t₂}` for a cross `{P₁, P₂}` of `S₁` where `r =
s₂`,
we must have `t₂ ∈ Ω(b, a)` and `{s₁, t₁} = {a, b}`, allowing us to apply
`theorem_5_3_of_normalized`. -/
private theorem theorem_5_3_of_s₂_eq_r {S₁ : Society α β} {Q P₁ P₂ : Graph α β}
    {a b r s₁ t₁ t₂ : α}
    (hG : S₁.G = S.G)
    (hQ : S.IsOmegaPathWithEnds Q a b)
    (hQ_ind : S.G.induce V(Q) = Q)
    (hab_empty : S.Ω.interval a b = ∅)
    (hcatch : Catches (S.Ω.bar \ {a, b}) (deleteVertices S.G V(Q)))
    (hno_int : Disjoint (pathInternalVerts S.G Q) S.Ω.bar)
    (hr_Q : r ∈ V(Q) \ {a, b})
    (hbar₁ : S₁.Ω.bar = S.Ω.bar ∪ {r})
    (hrest₁ : S₁.Ω.IsRestriction S.Ω.bar S.Ω)
    (hcw_arb : S₁.Ω.IsClockwise3 a r b)
    (hdisj_P : Disjoint V(P₁) V(P₂))
    (hP₁ : S₁.IsOmegaPathWithEnds P₁ s₁ t₁)
    (hP₂ : S₁.IsOmegaPathWithEnds P₂ r t₂)
    (hcr_ends : S₁.Ω.Crosses s₁ t₁ r t₂)
    (ha_mem : a ∈ ({s₁, t₁, r, t₂} : Set α))
    (hb_mem : b ∈ ({s₁, t₁, r, t₂} : Set α)) :
    (∃ M₁ M₂ : Graph α β, S.IsCross M₁ M₂) ∨
      (∃ N₁ N₂ N₃ : Graph α β, S.IsTripod N₁ N₂ N₃) := by
  have hr_not_bar : r ∉ S.Ω.bar := by
    have hr_int : r ∈ pathInternalVerts S.G Q := by
      rw [hQ.1.pathInternalVerts_eq]
      exact hr_Q
    exact disjoint_left.mp hno_int hr_int
  obtain ⟨_, h₁_ar, h₁_rb, _, h_ba_sdiff⟩ :=
    S.Ω.extension_intervals hbar₁ hrest₁ hab_empty hcw_arb
  have h_not_empty := hcr_ends.symm.not_interval_empty
  have ht₂_ne_a : t₂ ≠ a := fun h => h_not_empty (Or.inr (h ▸ h₁_ar))
  have ht₂_ne_b : t₂ ≠ b := fun h => h_not_empty (Or.inl (h ▸ h₁_rb))
  have ht₂_bar : t₂ ∈ S.Ω.bar := by
    have ht₂_bar₁ : t₂ ∈ S₁.Ω.bar := hP₂.2.2.2
    rw [hbar₁, mem_union, mem_singleton_iff] at ht₂_bar₁
    exact ht₂_bar₁.resolve_right hP₂.2.1.symm
  have ht₂_ba : t₂ ∈ S.Ω.interval b a := by
    rw [h_ba_sdiff]
    exact ⟨ht₂_bar, fun h => by
      rcases h with rfl | h_eq
      · exact ht₂_ne_a rfl
      · exact ht₂_ne_b (mem_singleton_iff.mp h_eq)⟩
  have ha_ne_r : a ≠ r := fun h => hr_Q.2 (Or.inl h.symm)
  have hb_ne_r : b ≠ r := fun h => hr_Q.2 (Or.inr (mem_singleton_iff.mpr h.symm))
  have ha_s₁t₁ : a = s₁ ∨ a = t₁ := by
    rcases ha_mem with rfl | rfl | rfl | h_eq
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact (ha_ne_r rfl).elim
    · exact (ht₂_ne_a (mem_singleton_iff.mp h_eq).symm).elim
  have hb_s₁t₁ : b = s₁ ∨ b = t₁ := by
    rcases hb_mem with rfl | rfl | rfl | h_eq
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact (hb_ne_r rfl).elim
    · exact (ht₂_ne_b (mem_singleton_iff.mp h_eq).symm).elim
  have hP₁_ab : IsGraphPathWithEnds S.G P₁ a b := by
    have hP₁_G : IsGraphPathWithEnds S.G P₁ s₁ t₁ := hG ▸ hP₁.1
    rcases ha_s₁t₁ with rfl | rfl <;> rcases hb_s₁t₁ with rfl | rfl
    · exact (hQ.2.1 rfl).elim
    · exact hP₁_G
    · exact hP₁_G.symm
    · exact (hQ.2.1 rfl).elim
  have hP₂_rt₂ : IsGraphPathWithEnds S.G P₂ r t₂ := hG ▸ hP₂.1
  exact S.theorem_5_3_of_normalized hQ hQ_ind hno_int hab_empty hcatch hr_Q.1
    hdisj_P hP₁_ab hP₂_rt₂ ht₂_ba

/-- **Graph Minors IX, (5.3)** (page 53):
"Let $Q$ be an induced $\Omega$-path in $(K, \Omega)$ with ends $a, b$ such that $\Omega(a,
b) = \emptyset$ and $\bar{\Omega} - \{a, b\}$ catches $K \setminus V(Q)$, and no internal
vertex of $Q$ is in $\bar{\Omega}$. Let $r \in V(Q) - \{a, b\}$, and let $\Omega_1$ be the
cyclic permutation in $V(K)$ with $\bar{\Omega}_1 = \bar{\Omega} \cup \{r\}$ and $\Omega_1
\mid \bar{\Omega} = \Omega$, and with $(a, r, b)$ $\Omega_1$-clockwise. If $(K, \Omega_1)$
has a cross then $(K, \Omega)$ has a cross or tripod." -/
theorem theorem_5_3_proof [Finite V(S.G)] [Finite E(S.G)]
    {S₁ : Society α β} {Q : Graph α β} {a b r : α}
    (hG : S₁.G = S.G)
    (hQ : S.IsOmegaPathWithEnds Q a b)
    (hQ_ind : S.G.induce V(Q) = Q)
    (hab_empty : S.Ω.interval a b = ∅)
    (hcatch : Catches (S.Ω.bar \ {a, b}) (deleteVertices S.G V(Q)))
    (hno_int : Disjoint (pathInternalVerts S.G Q) S.Ω.bar)
    (hr_Q : r ∈ V(Q) \ {a, b})
    (hbar₁ : S₁.Ω.bar = S.Ω.bar ∪ {r})
    (hrest₁ : S₁.Ω.IsRestriction S.Ω.bar S.Ω)
    (hcw_arb : S₁.Ω.IsClockwise3 a r b)
    (hcross₁ : ∃ P₁ P₂ : Graph α β, S₁.IsCross P₁ P₂) :
    (∃ M₁ M₂ : Graph α β, S.IsCross M₁ M₂) ∨
      (∃ N₁ N₂ N₃ : Graph α β, S.IsTripod N₁ N₂ N₃) := by
  by_cases hcross : ∃ M₁ M₂ : Graph α β, S.IsCross M₁ M₂
  · exact Or.inl hcross
  · -- Choose a cross `{P₁, P₂}` of `S₁` minimizing `|V(P₁ ∪ P₂ ∪ Q)| + |E(P₁ ∪ P₂ ∪ Q)|`.
    let cost (P₁ P₂ : Graph α β) : ℕ :=
      (V(subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q)).ncard +
        (E(subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q)).ncard
    have hex : ∃ n : ℕ, ∃ P₁ P₂ : Graph α β, S₁.IsCross P₁ P₂ ∧ cost P₁ P₂ = n := by
      rcases hcross₁ with ⟨P₁, P₂, hcr⟩
      exact ⟨cost P₁ P₂, P₁, P₂, hcr, rfl⟩
    classical
    obtain ⟨P₁, P₂, hcr₁, hcost_eq⟩ := Nat.find_spec hex
    have hmin_cost : ∀ P₁' P₂' : Graph α β, S₁.IsCross P₁' P₂' → cost P₁ P₂ ≤ cost P₁' P₂' := by
      intro P₁' P₂' hcr'
      rw [hcost_eq]
      exact Nat.find_min' hex ⟨P₁', P₂', hcr', rfl⟩
    have hmin : ∀ P₁' P₂' : Graph α β, S₁.IsCross P₁' P₂' →
        subgraphUnion S.G (subgraphUnion S.G P₁' P₂') Q ≤
          subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q →
        V(subgraphUnion S.G (subgraphUnion S.G P₁' P₂') Q) =
          V(subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q) ∧
        E(subgraphUnion S.G (subgraphUnion S.G P₁' P₂') Q) =
          E(subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q) := by
      intro P₁' P₂' hcr' hle
      let H' := subgraphUnion S.G (subgraphUnion S.G P₁' P₂') Q
      let H := subgraphUnion S.G (subgraphUnion S.G P₁ P₂) Q
      rcases hcr₁ with ⟨_, s₁, t₁, s₂, t₂, hP₁, hP₂, _⟩
      have hH_le : H ≤ S.G :=
        subgraphUnion_le (subgraphUnion_le (hG ▸ hP₁.1.le) (hG ▸ hP₂.1.le)) hQ.1.le
      have hVH_fin : V(H).Finite := toFinite V(S.G) |>.subset hH_le.vertexSet_mono
      have hEH_fin : E(H).Finite := toFinite E(S.G) |>.subset hH_le.edgeSet_mono
      have hV_le : V(H').ncard ≤ V(H).ncard := ncard_le_ncard hle.vertexSet_mono hVH_fin
      have hE_le : E(H').ncard ≤ E(H).ncard := ncard_le_ncard hle.edgeSet_mono hEH_fin
      have h_cost : V(H).ncard + E(H).ncard ≤ V(H').ncard + E(H').ncard := hmin_cost P₁' P₂' hcr'
      have hV_ge : V(H).ncard ≤ V(H').ncard := by omega
      have hE_ge : E(H).ncard ≤ E(H').ncard := by omega
      exact ⟨eq_of_subset_of_ncard_le hle.vertexSet_mono hV_ge hVH_fin,
        eq_of_subset_of_ncard_le hle.edgeSet_mono hE_ge hEH_fin⟩
    rcases hcr₁ with ⟨hdisj_P, s₁, t₁, s₂, t₂, hP₁, hP₂, hcr_ends⟩
    have hclaim1 := S.lemma_5_3_claim_1 hG hbar₁ hrest₁ hab_empty hcw_arb hQ hno_int hr_Q
      hdisj_P hP₁ hP₂ hcr_ends hmin
    obtain ⟨ha_mem, hb_mem⟩ := hclaim1.resolve_left hcross
    have hr_mem : r ∈ ({s₁, t₁, s₂, t₂} : Set α) :=
      S.mem_ends_of_isCross_of_not_hasCross hG hbar₁ hrest₁ hcross
        hdisj_P hP₁ hP₂ hcr_ends
    -- Normalize `(P₁, s₁, t₁)` and `(P₂, s₂, t₂)` so that `r` is the left end of the second path.
    rcases hr_mem with rfl | rfl | rfl | h_eq
    · -- `r = s₁`: swap `P₁` and `P₂`.
      refine S.theorem_5_3_of_s₂_eq_r hG hQ hQ_ind hab_empty hcatch hno_int hr_Q
        hbar₁ hrest₁ hcw_arb hdisj_P.symm hP₂ hP₁ hcr_ends.symm ?_ ?_
      · rcases ha_mem with ha | ha | ha | ha <;> simp_all
      · rcases hb_mem with hb | hb | hb | hb <;> simp_all
    · -- `r = t₁`: swap `P₁` and `P₂` and reverse `P₁`.
      refine S.theorem_5_3_of_s₂_eq_r hG hQ hQ_ind hab_empty hcatch hno_int hr_Q
        hbar₁ hrest₁ hcw_arb hdisj_P.symm hP₂ hP₁.symm hcr_ends.symm.swap_right ?_ ?_
      · rcases ha_mem with ha | ha | ha | ha <;> simp_all
      · rcases hb_mem with hb | hb | hb | hb <;> simp_all
    · -- `r = s₂`: already normalized.
      exact S.theorem_5_3_of_s₂_eq_r hG hQ hQ_ind hab_empty hcatch hno_int hr_Q
        hbar₁ hrest₁ hcw_arb hdisj_P hP₁ hP₂ hcr_ends ha_mem hb_mem
    · -- `r = t₂`: reverse `P₂`.
      have hr_t₂ : r = t₂ := mem_singleton_iff.mp h_eq
      subst hr_t₂
      refine S.theorem_5_3_of_s₂_eq_r hG hQ hQ_ind hab_empty hcatch hno_int hr_Q
        hbar₁ hrest₁ hcw_arb hdisj_P hP₁ hP₂.symm hcr_ends.swap_right ?_ ?_
      · rcases ha_mem with ha | ha | ha | ha <;> simp_all
      · rcases hb_mem with hb | hb | hb | hb <;> simp_all

/-! ## Proof of (5.4): Contracting a Separating Path and Tripod-to-Cross Reduction -/

/-- Contraction map sending every vertex in `V(Q)` to `a` and fixing all other vertices. -/
private noncomputable def contractMap (Q : Graph α β) (a u : α) : α :=
  by classical exact if u ∈ V(Q) then a else u

private theorem contractMap_of_mem {Q : Graph α β} {a u : α} (hu : u ∈ V(Q)) :
    contractMap Q a u = a := by
  simp [contractMap, hu]

private theorem contractMap_of_notMem {Q : Graph α β} {a u : α} (hu : u ∉ V(Q)) :
    contractMap Q a u = u := by
  simp [contractMap, hu]

private theorem contractMap_eq_self_of_ne {Q : Graph α β} {a u : α}
    (h : contractMap Q a u ≠ a) : u ∉ V(Q) ∧ contractMap Q a u = u := by
  by_cases hu : u ∈ V(Q)
  · exact (h (contractMap_of_mem hu)).elim
  · exact ⟨hu, contractMap_of_notMem hu⟩

private theorem contractMap_mem {G₁ Q : Graph α β} {a u : α} (hu : u ∈ V(G₁)) :
    contractMap Q a u ∈ (V(G₁) \ V(Q)) ∪ {a} := by
  by_cases huQ : u ∈ V(Q)
  · rw [contractMap_of_mem huQ]
    exact Or.inr rfl
  · rw [contractMap_of_notMem huQ]
    exact Or.inl ⟨hu, huQ⟩

/-- The graph `G''` obtained from `G₁` by contracting `V(Q)` onto `a`. -/
private noncomputable def contractGraph (G₁ Q : Graph α β) (a : α) : Graph α β where
  vertexSet := (V(G₁) \ V(Q)) ∪ {a}
  edgeSet := E(G₁)
  IsLink e x y := ∃ u v : α, G₁.IsLink e u v ∧ x = contractMap Q a u ∧ y = contractMap Q a v
  isLink_symm _ _ := ⟨fun _ _ ⟨u, v, huv, hx, hy⟩ => ⟨v, u, huv.symm, hy, hx⟩⟩
  eq_or_eq_of_isLink_of_isLink e x y z w := by
    rintro ⟨u₁, v₁, h₁, rfl, rfl⟩ ⟨u₂, v₂, h₂, rfl, rfl⟩
    rcases h₁.left_eq_or_eq h₂ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  edge_mem_iff_exists_isLink e := by
    constructor
    · intro he
      obtain ⟨u, v, huv⟩ := G₁.exists_isLink_of_mem_edgeSet he
      exact ⟨contractMap Q a u, contractMap Q a v, u, v, huv, rfl, rfl⟩
    · rintro ⟨_, _, u, v, huv, _, _⟩
      exact huv.edge_mem
  left_mem_of_isLink e x y := by
    rintro ⟨u, _, huv, rfl, _⟩
    exact contractMap_mem huv.left_mem

@[simp]
private theorem vertexSet_contractGraph (G₁ Q : Graph α β) (a : α) :
    V(contractGraph G₁ Q a) = (V(G₁) \ V(Q)) ∪ {a} := rfl

@[simp]
private theorem edgeSet_contractGraph (G₁ Q : Graph α β) (a : α) :
    E(contractGraph G₁ Q a) = E(G₁) := rfl

private theorem deleteVertices_contractGraph {G₁ Q : Graph α β} {a : α} (ha_Q : a ∈ V(Q)) :
    deleteVertices (contractGraph G₁ Q a) {a} = deleteVertices G₁ V(Q) := by
  refine Graph.ext ?_ fun e x y => ?_
  · ext z
    simp only [vertexSet_deleteVertices, vertexSet_contractGraph, mem_sdiff, mem_union,
      mem_singleton_iff]
    constructor
    · rintro ⟨hz | rfl, hne⟩
      · exact hz
      · exact (hne rfl).elim
    · rintro ⟨hz₁, hzQ⟩
      exact ⟨Or.inl ⟨hz₁, hzQ⟩, fun h => hzQ (h ▸ ha_Q)⟩
  · simp only [deleteVertices_isLink, mem_singleton_iff]
    constructor
    · rintro ⟨⟨u, v, huv, hx_eq, hy_eq⟩, hxa, hya⟩
      obtain ⟨huQ, hu_eq⟩ := contractMap_eq_self_of_ne (hx_eq ▸ hxa)
      obtain ⟨hvQ, hv_eq⟩ := contractMap_eq_self_of_ne (hy_eq ▸ hya)
      have hxu : x = u := hx_eq.trans hu_eq
      have hyv : y = v := hy_eq.trans hv_eq
      exact ⟨hxu ▸ hyv ▸ huv, hxu ▸ huQ, hyv ▸ hvQ⟩
    · rintro ⟨hxy, hxQ, hyQ⟩
      exact ⟨⟨x, y, hxy, (contractMap_of_notMem hxQ).symm, (contractMap_of_notMem hyQ).symm⟩,
        fun h => hxQ (h ▸ ha_Q), fun h => hyQ (h ▸ ha_Q)⟩

private theorem deleteVertices_eq_of_isGraphSeparation {G G₁ G₂ Q : Graph α β}
    (hsep : IsGraphSeparation G G₁ G₂) (hinter : V(G₁) ∩ V(G₂) = V(Q)) :
    deleteVertices G V(G₂) = deleteVertices G₁ V(Q) := by
  refine Graph.ext ?_ fun e x y => ?_
  · ext z
    simp only [vertexSet_deleteVertices, mem_sdiff]
    rw [← hsep.2.2.1, ← hinter]
    simp only [mem_union, mem_inter_iff]
    tauto
  · simp only [deleteVertices_isLink]
    constructor
    · rintro ⟨hxy, hx₂, hy₂⟩
      have he : e ∈ E(G₁) ∪ E(G₂) := hsep.2.2.2.1 ▸ hxy.edge_mem
      rcases he with he₁ | he₂
      · have hxy₁ : G₁.IsLink e x y := (hsep.1.isLink_iff he₁).mpr hxy
        have hxQ : x ∉ V(Q) := fun h => hx₂ (hinter ▸ h).2
        have hyQ : y ∉ V(Q) := fun h => hy₂ (hinter ▸ h).2
        exact ⟨hxy₁, hxQ, hyQ⟩
      · have hxy₂ : G₂.IsLink e x y := (hsep.2.1.isLink_iff he₂).mpr hxy
        exact (hx₂ hxy₂.left_mem).elim
    · rintro ⟨hxy₁, hxQ, hyQ⟩
      refine ⟨hxy₁.mono hsep.1, fun hx₂ => hxQ ?_, fun hy₂ => hyQ ?_⟩
      · rw [← hinter]; exact ⟨hxy₁.left_mem, hx₂⟩
      · rw [← hinter]; exact ⟨hxy₁.right_mem, hy₂⟩

/-- Any two vertices in `V(Q)` are connected by a walk in `G₁` whose support lies in `V(Q)`. -/
private theorem exists_walk_in_Q {G₁ Q : Graph α β} {a b u v : α}
    (hQ : IsGraphPathWithEnds G₁ Q a b) (hu : u ∈ V(Q)) (hv : v ∈ V(Q)) :
    ∃ W : GraphWalk G₁ u v, ∀ z ∈ W.support, z ∈ V(Q) := by
  obtain ⟨P_uv, hPuv_Q, _, hPuv_G₁⟩ := hQ.exists_subpath hu hv
  obtain ⟨hPuv_le, W₀, _, hV₀, _⟩ := hPuv_G₁
  obtain ⟨W, hW_supp, _⟩ := W₀.exists_transfer
    (fun _ _ _ _ hl => hl.mono hPuv_le) (fun _ hx => hPuv_le.vertexSet_mono (by rw [hV₀]; exact hx))
  refine ⟨W, fun z hz => hPuv_Q.vertexSet_mono ?_⟩
  rw [hV₀, mem_ofPred_eq, ← hW_supp]
  exact hz

/-- A single edge step in `contractGraph G₁ Q a` lifts to a walk in `G₁`. -/
private theorem exists_step_lift_walk {G₁ Q : Graph α β} {a b : α}
    (hQ : IsGraphPathWithEnds G₁ Q a b) {e : β} {x y : α}
    (hlink : (contractGraph G₁ Q a).IsLink e x y) :
    ∃ W : GraphWalk G₁ x y,
      ∀ z ∈ W.support, z = x ∨ z = y ∨ ((x = a ∨ y = a) ∧ z ∈ V(Q)) := by
  rcases hlink with ⟨u, v, huv, hx_eq, hy_eq⟩
  have hW_xu : ∃ W₁ : GraphWalk G₁ x u,
      ∀ z ∈ W₁.support, z = x ∨ (x = a ∧ z ∈ V(Q)) := by
    by_cases huQ : u ∈ V(Q)
    · have hxa : x = a := hx_eq.trans (contractMap_of_mem huQ)
      obtain ⟨W₁, hW₁⟩ := exists_walk_in_Q hQ (hxa ▸ hQ.left_mem) huQ
      exact ⟨W₁, fun z hz => Or.inr ⟨hxa, hW₁ z hz⟩⟩
    · have hxu : x = u := hx_eq.trans (contractMap_of_notMem huQ)
      subst hxu
      exact ⟨.nil huv.left_mem, fun z hz => Or.inl (List.mem_singleton.mp hz)⟩
  have hW_vy : ∃ W₂ : GraphWalk G₁ v y,
      ∀ z ∈ W₂.support, z = y ∨ (y = a ∧ z ∈ V(Q)) := by
    by_cases hvQ : v ∈ V(Q)
    · have hya : y = a := hy_eq.trans (contractMap_of_mem hvQ)
      obtain ⟨W₂, hW₂⟩ := exists_walk_in_Q hQ hvQ (hya ▸ hQ.left_mem)
      exact ⟨W₂, fun z hz => Or.inr ⟨hya, hW₂ z hz⟩⟩
    · have hyv : y = v := hy_eq.trans (contractMap_of_notMem hvQ)
      subst hyv
      exact ⟨.nil huv.right_mem, fun z hz => Or.inl (List.mem_singleton.mp hz)⟩
  obtain ⟨W₁, hW₁⟩ := hW_xu
  obtain ⟨W₂, hW₂⟩ := hW_vy
  let W_uv : GraphWalk G₁ u v := .cons huv (.nil huv.right_mem)
  refine ⟨W₁.append (W_uv.append W₂), fun z hz => ?_⟩
  rw [GraphWalk.mem_support_append] at hz
  rcases hz with hz₁ | hz₂₃
  · rcases hW₁ z hz₁ with rfl | ⟨hxa, hzQ⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨Or.inl hxa, hzQ⟩)
  · rw [GraphWalk.mem_support_append] at hz₂₃
    rcases hz₂₃ with hz_uv | hz₂
    · simp only [W_uv, GraphWalk.support_cons, GraphWalk.support_nil, List.mem_cons] at hz_uv
      rcases hz_uv with hzu | hzv | h_nil
      · subst z
        rcases hW₁ u W₁.end_mem_support with rfl | ⟨hxa, huQ⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ⟨Or.inl hxa, huQ⟩)
      · subst z
        rcases hW₂ v W₂.start_mem_support with rfl | ⟨hya, hvQ⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr ⟨Or.inr hya, hvQ⟩)
      · exact (List.not_mem_nil h_nil).elim
    · rcases hW₂ z hz₂ with rfl | ⟨hya, hzQ⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨Or.inr hya, hzQ⟩)

/-- Every walk in `contractGraph G₁ Q a` lifts to a walk in `G₁` with the same endpoints. -/
private theorem exists_lift_walk {G₁ Q : Graph α β} {a b s t : α}
    (hQ : IsGraphPathWithEnds G₁ Q a b)
    (W : GraphWalk (contractGraph G₁ Q a) s t) :
    ∃ W' : GraphWalk G₁ s t,
      ∀ z ∈ W'.support, z ∈ W.support ∨ (a ∈ W.support ∧ z ∈ V(Q)) := by
  induction W with
  | @nil u hu =>
    have hu_G₁ : u ∈ V(G₁) := by
      rcases hu with ⟨hu₁, _⟩ | rfl
      · exact hu₁
      · exact hQ.le.vertexSet_mono hQ.left_mem
    exact ⟨.nil hu_G₁, fun z hz => Or.inl hz⟩
  | @cons x y t e hxy W_rest ih =>
    obtain ⟨W_step, hstep⟩ := exists_step_lift_walk hQ hxy
    obtain ⟨W_tail, htail⟩ := ih
    refine ⟨W_step.append W_tail, fun z hz => ?_⟩
    rw [GraphWalk.mem_support_append] at hz
    rcases hz with hz₁ | hz₂
    · rcases hstep z hz₁ with rfl | rfl | ⟨hxy_a, hzQ⟩
      · exact Or.inl List.mem_cons_self
      · exact Or.inl (List.mem_cons_of_mem x W_rest.start_mem_support)
      · refine Or.inr ⟨?_, hzQ⟩
        rcases hxy_a with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem x W_rest.start_mem_support
    · rcases htail z hz₂ with hz_in | ⟨ha_in, hzQ⟩
      · exact Or.inl (List.mem_cons_of_mem x hz_in)
      · exact Or.inr ⟨List.mem_cons_of_mem x ha_in, hzQ⟩

/-- Every path `M` in `contractGraph G₁ Q a` with ends `s, t` lifts to a path `M'` in `G₁` with
the same ends `s, t` such that `V(M') ⊆ (V(M) \ {a}) ∪ (if a ∈ V(M) then V(Q) else ∅)`. -/
private theorem exists_lift_path_of_contractGraph {G₁ Q M : Graph α β} {a b s t : α}
    (hQ : IsGraphPathWithEnds G₁ Q a b)
    (hM : IsGraphPathWithEnds (contractGraph G₁ Q a) M s t) :
    ∃ M' : Graph α β, IsGraphPathWithEnds G₁ M' s t ∧
      ∀ z ∈ V(M'), (z ∈ V(M) ∧ z ≠ a) ∨ (a ∈ V(M) ∧ z ∈ V(Q)) := by
  obtain ⟨hM_le, W₀, _, hV₀, _⟩ := hM
  obtain ⟨W, hW_supp, _⟩ := W₀.exists_transfer
    (fun _ _ _ _ hl => hl.mono hM_le) (fun _ hx => hM_le.vertexSet_mono (by rw [hV₀]; exact hx))
  obtain ⟨W₁, hW₁⟩ := exists_lift_walk hQ W
  obtain ⟨M', hM'_path, hM'_V, _⟩ := exists_isGraphPathWithEnds_of_walk W₁
  refine ⟨M', hM'_path, fun z hz => ?_⟩
  have hz_W₁ : z ∈ W₁.support := hM'_V hz
  rcases hW₁ z hz_W₁ with hz_W | ⟨ha_W, hzQ⟩
  · have hz_M : z ∈ V(M) := by rw [hV₀, mem_ofPred_eq, ← hW_supp]; exact hz_W
    by_cases hza : z = a
    · subst hza
      exact Or.inr ⟨hz_M, hQ.left_mem⟩
    · exact Or.inl ⟨hz_M, hza⟩
  · have ha_M : a ∈ V(M) := by rw [hV₀, mem_ofPred_eq, ← hW_supp]; exact ha_W
    exact Or.inr ⟨ha_M, hzQ⟩

/-- A tripod `{P₁, P₂, P₃}` of `S'` (where `S'.G = deleteVertices S''.G {a}`) is also a tripod of
`S''` whenever `S''.Ω.bar = S'.Ω.bar ∪ {a}`. -/
private theorem isTripod_of_deleteVertices_singleton {S' S'' : Society α β}
    {P₁ P₂ P₃ : Graph α β} {a : α}
    (hG' : S'.G = deleteVertices S''.G {a})
    (hbar'' : S''.Ω.bar = S'.Ω.bar ∪ {a})
    (htrip : S'.IsTripod P₁ P₂ P₃) :
    S''.IsTripod P₁ P₂ P₃ := by
  have hle : S'.G ≤ S''.G := hG' ▸ deleteVertices_le S''.G {a}
  have ha_not_G' : ∀ z ∈ V(S'.G), z ≠ a := by
    intro z hz
    rw [hG', vertexSet_deleteVertices, mem_sdiff, mem_singleton_iff] at hz
    exact hz.2
  rcases htrip with ⟨u, v, huv, hP₁, hP₂, hP₃, h12, h13, h23,
    s₁, hs₁, s₂, hs₂, s₃, hs₃, t₁, ht₁, t₂, ht₂, t₃, ht₃,
    hX_sub, hY_sub, hcard, L, hdisj_L, hL⟩
  refine ⟨u, v, huv, hP₁.mono hle, hP₂.mono hle, hP₃.mono hle, h12, h13, h23,
    s₁, hs₁, s₂, hs₂, s₃, hs₃,
    t₁, hbar'' ▸ Or.inl ht₁, t₂, hbar'' ▸ Or.inl ht₂, t₃, hbar'' ▸ Or.inl ht₃,
    hX_sub, hY_sub.trans (hbar'' ▸ subset_union_left), hcard, L, hdisj_L, fun i => ?_⟩
  obtain ⟨x, hx, y, hy, hLi⟩ := hL i
  refine ⟨x, hx, y, hy, hLi.1.mono hle, hLi.2.1, ?_⟩
  rw [hbar'', inter_union_distrib_left, hLi.2.2]
  have hdisj_a : V(L i) ∩ {a} = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
    intro hzL rfl
    exact ha_not_G' z (hLi.1.le.vertexSet_mono hzL) rfl
  rw [hdisj_a, union_empty]

/-- Deleting a vertex set `X` from a graph separation `(A₁, A₂)` of `G` yields a graph separation
of `deleteVertices G X`. -/
private theorem IsGraphSeparation.deleteVertices {G A₁ A₂ : Graph α β}
    (h : IsGraphSeparation G A₁ A₂) (X : Set α) :
    IsGraphSeparation (GM09.deleteVertices G X)
      (GM09.deleteVertices A₁ X) (GM09.deleteVertices A₂ X) := by
  have hle₁ : GM09.deleteVertices A₁ X ≤ GM09.deleteVertices G X := by
    refine ⟨sdiff_le_sdiff_right h.1.vertexSet_mono, fun e x y hxy => ?_⟩
    rw [deleteVertices_isLink] at hxy ⊢
    exact ⟨hxy.1.mono h.1, hxy.2⟩
  have hle₂ : GM09.deleteVertices A₂ X ≤ GM09.deleteVertices G X := by
    refine ⟨sdiff_le_sdiff_right h.2.1.vertexSet_mono, fun e x y hxy => ?_⟩
    rw [deleteVertices_isLink] at hxy ⊢
    exact ⟨hxy.1.mono h.2.1, hxy.2⟩
  have hV : V(GM09.deleteVertices A₁ X) ∪ V(GM09.deleteVertices A₂ X) =
      V(GM09.deleteVertices G X) := by
    simp only [vertexSet_deleteVertices, ← union_sdiff_distrib, h.2.2.1]
  have hE₁_sub : E(GM09.deleteVertices A₁ X) ⊆ E(A₁) :=
    (deleteVertices_le A₁ X).edgeSet_mono
  have hE₂_sub : E(GM09.deleteVertices A₂ X) ⊆ E(A₂) :=
    (deleteVertices_le A₂ X).edgeSet_mono
  have hE : E(GM09.deleteVertices A₁ X) ∪ E(GM09.deleteVertices A₂ X) =
      E(GM09.deleteVertices G X) := by
    apply Subset.antisymm
    · exact union_subset hle₁.edgeSet_mono hle₂.edgeSet_mono
    · intro e he
      obtain ⟨x, y, hxy⟩ := (GM09.deleteVertices G X).exists_isLink_of_mem_edgeSet he
      rw [deleteVertices_isLink] at hxy
      rcases h.2.2.2.1 ▸ hxy.1.edge_mem with he₁ | he₂
      · left
        exact ((deleteVertices_isLink A₁ X).mpr
          ⟨(h.1.isLink_iff he₁).mpr hxy.1, hxy.2⟩).edge_mem
      · right
        exact ((deleteVertices_isLink A₂ X).mpr
          ⟨(h.2.1.isLink_iff he₂).mpr hxy.1, hxy.2⟩).edge_mem
  exact ⟨hle₁, hle₂, hV, hE, h.2.2.2.2.mono hE₁_sub hE₂_sub⟩

private theorem deleteVertices_eq_self_of_notMem {G : Graph α β} {a : α} (ha : a ∉ V(G)) :
    deleteVertices G {a} = G := by
  refine (Compatible.of_le_le (deleteVertices_le G {a}) le_rfl).ext ?_ ?_
  · ext z
    simp only [vertexSet_deleteVertices, mem_sdiff, mem_singleton_iff, and_iff_left_iff_imp]
    rintro hz rfl
    exact ha hz
  · apply Subset.antisymm (deleteVertices_le G {a}).edgeSet_mono
    intro e he
    obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
    exact ((deleteVertices_isLink G {a}).mpr ⟨hxy,
      fun h => ha (mem_singleton_iff.mp h ▸ hxy.left_mem),
      fun h => ha (mem_singleton_iff.mp h ▸ hxy.right_mem)⟩).edge_mem

private theorem liftCrossFromContractGraph {G₁ Q : Graph α β} {a b : α}
    {S' S₁ S'' : Society α β}
    (hQ_path_G₁ : IsGraphPathWithEnds G₁ Q a b) (hG₁ : S₁.G = G₁)
    (hG'' : S''.G = contractGraph G₁ Q a)
    (hrest'' : S₁.Ω.IsRestriction (S'.Ω.bar ∪ {a}) S''.Ω)
    (hbar'' : S''.Ω.bar = S'.Ω.bar ∪ {a})
    (hsub_bar₁ : S'.Ω.bar ∪ {a} ⊆ S₁.Ω.bar)
    (hcr'' : ∃ M₁ M₂ : Graph α β, S''.IsCross M₁ M₂) :
    ∃ M₁ M₂ : Graph α β, S₁.IsCross M₁ M₂ := by
  let G'' := contractGraph G₁ Q a
  rcases hcr'' with ⟨M₁, M₂, hdisj_M, s₁, t₁, s₂, t₂, hM₁, hM₂, hcr_ends⟩
  obtain ⟨M₁', hM₁'_path, hM₁'_V⟩ := exists_lift_path_of_contractGraph hQ_path_G₁ (hG'' ▸ hM₁.1)
  obtain ⟨M₂', hM₂'_path, hM₂'_V⟩ := exists_lift_path_of_contractGraph hQ_path_G₁ (hG'' ▸ hM₂.1)
  have hdisj_M' : Disjoint V(M₁') V(M₂') := by
    rw [disjoint_left]
    intro z hz₁ hz₂
    rcases hM₁'_V z hz₁ with ⟨hzM₁, hza⟩ | ⟨haM₁, hzQ⟩ <;>
      rcases hM₂'_V z hz₂ with ⟨hzM₂, hza'⟩ | ⟨haM₂, hzQ'⟩
    · exact disjoint_left.mp hdisj_M hzM₁ hzM₂
    · have hz_G'' : z ∈ V(G'') := by
        change z ∈ V(contractGraph G₁ Q a)
        rw [← hG'']
        exact hM₁.1.le.vertexSet_mono hzM₁
      rcases hz_G'' with ⟨_, hz_notQ⟩ | rfl
      · exact hz_notQ hzQ'
      · exact hza rfl
    · have hz_G'' : z ∈ V(G'') := by
        change z ∈ V(contractGraph G₁ Q a)
        rw [← hG'']
        exact hM₂.1.le.vertexSet_mono hzM₂
      rcases hz_G'' with ⟨_, hz_notQ⟩ | rfl
      · exact hz_notQ hzQ
      · exact hza' rfl
    · exact disjoint_left.mp hdisj_M haM₁ haM₂
  have hs₁_bar₁ : s₁ ∈ S₁.Ω.bar := hsub_bar₁ (hbar'' ▸ hM₁.2.2.1)
  have ht₁_bar₁ : t₁ ∈ S₁.Ω.bar := hsub_bar₁ (hbar'' ▸ hM₁.2.2.2)
  have hs₂_bar₁ : s₂ ∈ S₁.Ω.bar := hsub_bar₁ (hbar'' ▸ hM₂.2.2.1)
  have ht₂_bar₁ : t₂ ∈ S₁.Ω.bar := hsub_bar₁ (hbar'' ▸ hM₂.2.2.2)
  have hcr₁_ends : S₁.Ω.Crosses s₁ t₁ s₂ t₂ :=
    (hrest''.crosses_iff.mp hcr_ends).2.2.2.2
  exact ⟨M₁', M₂', hdisj_M', s₁, t₁, s₂, t₂,
    ⟨hG₁ ▸ hM₁'_path, hM₁.2.1, hs₁_bar₁, ht₁_bar₁⟩,
    ⟨hG₁ ▸ hM₂'_path, hM₂.2.1, hs₂_bar₁, ht₂_bar₁⟩, hcr₁_ends⟩

/-- **Graph Minors IX, (5.4)** (page 54):
"Let $(G, \Omega)$ be internally 4-connected. Let $Q$ be a separating $\Omega$-path with ends
$a, b$ and with no internal vertex in $\bar{\Omega}$, and let $(G_1, G_2)$ be a separation
of $G$ such that $V(G_1 \cap G_2) = V(Q)$, $\Omega(a, b) \subseteq V(G_1)$ and $\Omega(b, a)
\subseteq V(G_2)$. Let $G' = G \setminus V(G_2)$, let $\Omega' = \Omega \mid V(G')$, and let
$\Omega_1 = \Omega \mid V(G_1)$. If $(G', \Omega')$ has a tripod then $(G_1, \Omega_1)$ has
a cross." -/
theorem theorem_5_4_proof (hconn : S.IsInternallyKConnected 4)
    {Q G₁ G₂ : Graph α β} {a b : α}
    (hQ : S.IsOmegaPathWithEnds Q a b)
    (_hsep_Q : S.IsSeparatingOmegaPath Q)
    (_hno_int : Disjoint (pathInternalVerts S.G Q) S.Ω.bar)
    (hsep_G : IsGraphSeparation S.G G₁ G₂)
    (hinter_G : V(G₁) ∩ V(G₂) = V(Q))
    (hQ_G₁ : Q ≤ G₁)
    (_hint_G₁ : S.Ω.interval a b ⊆ V(G₁))
    (_hint_G₂ : S.Ω.interval b a ⊆ V(G₂))
    {S' S₁ : Society α β}
    (hG' : S'.G = deleteVertices S.G V(G₂))
    (hΩ' : S.Ω.IsRestriction V(deleteVertices S.G V(G₂)) S'.Ω)
    (hG₁ : S₁.G = G₁)
    (hΩ₁ : S.Ω.IsRestriction V(G₁) S₁.Ω)
    (htripod : ∃ P₁ P₂ P₃ : Graph α β, S'.IsTripod P₁ P₂ P₃) :
    ∃ M₁ M₂ : Graph α β, S₁.IsCross M₁ M₂ := by
  have hQ_path_G₁ : IsGraphPathWithEnds G₁ Q a b := hQ.1.of_le hQ_G₁
  let G'' := contractGraph G₁ Q a
  have hVG''_sub : V(G'') ⊆ V(S.G) := by
    rintro z (⟨hz₁, _⟩ | rfl)
    · exact hsep_G.1.vertexSet_mono hz₁
    · exact hQ.1.le.vertexSet_mono hQ.1.left_mem
  have hVG''_fin : V(G'').Finite := S.finite_V.subset hVG''_sub
  have hEG''_fin : E(G'').Finite := S.finite_E.subset hsep_G.1.edgeSet_mono
  have hG'_eq : S'.G = deleteVertices G'' {a} := by
    rw [hG', deleteVertices_eq_of_isGraphSeparation hsep_G hinter_G,
      deleteVertices_contractGraph hQ.1.left_mem]
  have hS'_bar_sub_G₁ : S'.Ω.bar ⊆ S₁.Ω.bar := by
    rw [hΩ'.1, hΩ₁.1]
    rintro z ⟨hz_bar, hz_del⟩
    rw [vertexSet_deleteVertices, ← hsep_G.2.2.1] at hz_del
    exact ⟨hz_bar, hz_del.1.resolve_right hz_del.2⟩
  have ha_bar₁ : a ∈ S₁.Ω.bar := by
    rw [hΩ₁.1]
    exact ⟨hQ.2.2.1, hQ_G₁.vertexSet_mono hQ.1.left_mem⟩
  have hsub_bar₁ : S'.Ω.bar ∪ {a} ⊆ S₁.Ω.bar :=
    union_subset hS'_bar_sub_G₁ (singleton_subset_iff.mpr ha_bar₁)
  obtain ⟨Ω'', hrest''⟩ := S₁.Ω.exists_isRestriction (S'.Ω.bar ∪ {a})
  have hbar'' : Ω''.bar = S'.Ω.bar ∪ {a} := by
    rw [hrest''.1, inter_eq_right.mpr hsub_bar₁]
  have hbar''_sub : Ω''.bar ⊆ V(G'') := by
    rw [hbar'']
    refine union_subset ?_ subset_union_right
    have hsub : S'.Ω.bar ⊆ V(S'.G) := S'.bar_subset
    rw [hG'_eq, vertexSet_deleteVertices] at hsub
    exact hsub.trans sdiff_subset
  let S'' : Society α β := Society.mk G'' Ω'' hVG''_fin hEG''_fin hbar''_sub
  by_cases hcr'' : ∃ M₁ M₂ : Graph α β, S''.IsCross M₁ M₂
  · exact liftCrossFromContractGraph hQ_path_G₁ hG₁ (rfl : S''.G = G'')
      hrest'' hbar'' hsub_bar₁ hcr''
  · -- Case 2: `(G'', Ω'')` has no cross; apply (2.3) to get an internal 3-separation of `S''`.
    exfalso
    rcases htripod with ⟨P₁, P₂, P₃, htrip'⟩
    have htrip'' : S''.IsTripod P₁ P₂ P₃ :=
      isTripod_of_deleteVertices_singleton hG'_eq hbar'' htrip'
    obtain ⟨G''₁, G''₂, hint_sep'', hP_le_G''₁⟩ := (theorem_2_3_proof S'' htrip'').resolve_left
      hcr''
    have hsep'' : IsGraphSeparation G'' G''₁ G''₂ := hint_sep''.1.1.1
    have hbar_G''₂ : Ω''.bar ⊆ V(G''₂) := hint_sep''.1.1.2
    have hcard_inter'' : (V(G''₁) ∩ V(G''₂)).ncard ≤ 3 := hint_sep''.1.2.1
    have hV''₂_add_2 : V(G''₂).ncard + 2 ≤ V(G'').ncard := hint_sep''.2
    -- Show `a ∉ V(G''₁)` using the tripod `{P₁, P₂, P₃}` in `S'`.
    let J₁ := deleteVertices G''₁ {a}
    let J₂ := deleteVertices G''₂ {a}
    have hsep_J : IsGraphSeparation S'.G J₁ J₂ :=
      hG'_eq ▸ IsGraphSeparation.deleteVertices hsep'' {a}
    rcases htrip' with ⟨u, v, _, hP₁, hP₂, hP₃, h12, h13, h23,
      s₁, hs₁, s₂, hs₂, s₃, hs₃, t₁, _, t₂, _, t₃, _, hred₃⟩
    have hs12 : s₁ ≠ s₂ := fun h => hs₁.2 (by
      have : s₁ ∈ V(P₁) ∩ V(P₂) := ⟨hs₁.1, h ▸ hs₂.1⟩; rwa [h12] at this)
    have hs13 : s₁ ≠ s₃ := fun h => hs₁.2 (by
      have : s₁ ∈ V(P₁) ∩ V(P₃) := ⟨hs₁.1, h ▸ hs₃.1⟩; rwa [h13] at this)
    have hs23 : s₂ ≠ s₃ := fun h => hs₂.2 (by
      have : s₂ ∈ V(P₂) ∩ V(P₃) := ⟨hs₂.1, h ▸ hs₃.1⟩; rwa [h23] at this)
    have hcard_s : ({s₁, s₂, s₃} : Set α).ncard = 3 := by
      rw [ncard_insert_of_notMem (by simp [hs12, hs13]), ncard_pair hs23]
    have ha_not_S' : ∀ z ∈ V(S'.G), z ≠ a := by
      intro z hz
      rw [hG'_eq, vertexSet_deleteVertices, mem_sdiff, mem_singleton_iff] at hz
      exact hz.2
    have hX_J₁ : V(P₁) ∪ V(P₂) ∪ V(P₃) ⊆ V(J₁) := by
      intro z hz
      have hz_G''₁ : z ∈ V(G''₁) := by
        apply hP_le_G''₁.vertexSet_mono
        simpa [vertexSet_subgraphUnion] using hz
      have hz_S' : z ∈ V(S'.G) := by
        rcases hz with (hz₁ | hz₂) | hz₃
        · exact hP₁.le.vertexSet_mono hz₁
        · exact hP₂.le.vertexSet_mono hz₂
        · exact hP₃.le.vertexSet_mono hz₃
      exact ⟨hz_G''₁, ha_not_S' z hz_S'⟩
    have hbar'_J₂ : S'.Ω.bar ⊆ V(J₂) := fun z hz =>
      ⟨hbar_G''₂ (hbar'' ▸ Or.inl hz), ha_not_S' z (S'.bar_subset hz)⟩
    rcases hred₃ with ⟨hX'_sub, hY'_sub, _, L, hdisj_L, hL⟩
    have hJ_inter_ge : 3 ≤ (V(J₁) ∩ V(J₂)).ncard := by
      have hmeet : ∀ i, ∃ z, z ∈ V(L i) ∧ z ∈ V(J₁) ∩ V(J₂) := by
        intro i
        obtain ⟨x, hx, y, hy, hLi⟩ := hL i
        exact exists_mem_inter_of_isGraphPathWithEnds hsep_J hLi.1
          (hX_J₁ (hX'_sub hx)) (hbar'_J₂ (hY'_sub hy))
      choose z hzL hz_inter using hmeet
      have hz_inj : Function.Injective z := fun i j hij => by
        by_contra hne
        exact disjoint_left.mp (hdisj_L hne) (hzL i) (hij ▸ hzL j)
      have hfin_J : (V(J₁) ∩ V(J₂)).Finite :=
        S'.finite_V.subset (inter_subset_left.trans hsep_J.1.vertexSet_mono)
      have hle := ncard_le_ncard (range_subset_iff.mpr hz_inter) hfin_J
      rw [ncard_range_of_injective hz_inj, Nat.card_eq_fintype_card, Fintype.card_fin,
        hcard_s] at hle
      exact hle
    have hJ_inter_eq : V(J₁) ∩ V(J₂) = (V(G''₁) ∩ V(G''₂)) \ {a} := by
      ext w
      simp only [J₁, J₂, vertexSet_deleteVertices, mem_inter_iff, mem_sdiff, mem_singleton_iff]
      tauto
    have ha_not_G''₁ : a ∉ V(G''₁) := by
      intro ha_G''₁
      have ha_inter : a ∈ V(G''₁) ∩ V(G''₂) := ⟨ha_G''₁, hbar_G''₂ (hbar'' ▸ Or.inr rfl)⟩
      have hfin_inter : (V(G''₁) ∩ V(G''₂)).Finite :=
        hVG''_fin.subset (inter_subset_left.trans hsep''.1.vertexSet_mono)
      have hdiff := ncard_sdiff_singleton_add_one ha_inter hfin_inter
      rw [← hJ_inter_eq] at hdiff
      omega
    have hG''₁_eq_J₁ : G''₁ = J₁ := (deleteVertices_eq_self_of_notMem ha_not_G''₁).symm
    have hG''₁_le_S' : G''₁ ≤ S'.G := hG''₁_eq_J₁ ▸ hsep_J.1
    have hG''₁_le_G : G''₁ ≤ S.G :=
      hG''₁_le_S'.trans (hG' ▸ deleteVertices_le S.G V(G₂))
    have hdisj_G''₁_G₂ : Disjoint V(G''₁) V(G₂) := by
      rw [disjoint_left]
      intro z hz₁ hz₂
      have hz_S' : z ∈ V(S'.G) := hG''₁_le_S'.vertexSet_mono hz₁
      rw [hG', vertexSet_deleteVertices] at hz_S'
      exact hz_S'.2 hz₂
    -- Construct `G2_star` on `(V(G''₂) \ {a}) ∪ V(G₂)` and `E(G''₂) ∪ E(G₂)`.
    let G2_star : Graph α β :=
      (S.G.induce ((V(G''₂) \ {a}) ∪ V(G₂))).restrict (E(G''₂) ∪ E(G₂))
    have hV_star_sub : (V(G''₂) \ {a}) ∪ V(G₂) ⊆ V(S.G) := by
      rintro z (⟨hz₂, _⟩ | hz₂)
      · exact hVG''_sub ( hsep''.2.1.vertexSet_mono hz₂ )
      · exact hsep_G.2.1.vertexSet_mono hz₂
    have hG2_star_le : G2_star ≤ S.G := restrict_le.trans (S.G.induce_le hV_star_sub)
    have hV_star : V(G2_star) = (V(G''₂) \ {a}) ∪ V(G₂) := rfl
    have hE_star : E(G2_star) = E(G''₂) ∪ E(G₂) := by
      unfold G2_star
      rw [edgeSet_restrict, inter_eq_right]
      rintro e (he₂'' | he₂)
      · obtain ⟨x', y', hx'y'⟩ := G''₂.exists_isLink_of_mem_edgeSet he₂''
        have hx'y'_G'' : G''.IsLink e x' y' := hx'y'.mono hsep''.2.1
        rcases hx'y'_G'' with ⟨u, v, huv, rfl, rfl⟩
        have hu_mem : u ∈ (V(G''₂) \ {a}) ∪ V(G₂) := by
          by_cases huQ : u ∈ V(Q)
          · exact Or.inr ((hinter_G ▸ huQ).2)
          · rw [contractMap_of_notMem huQ] at hx'y'
            exact Or.inl ⟨hx'y'.left_mem, fun h => huQ (h ▸ hQ.1.left_mem)⟩
        have hv_mem : v ∈ (V(G''₂) \ {a}) ∪ V(G₂) := by
          by_cases hvQ : v ∈ V(Q)
          · exact Or.inr ((hinter_G ▸ hvQ).2)
          · rw [contractMap_of_notMem hvQ] at hx'y'
            exact Or.inl ⟨hx'y'.right_mem, fun h => hvQ (h ▸ hQ.1.left_mem)⟩
        exact ⟨u, v, huv.mono hsep_G.1, hu_mem, hv_mem⟩
      · obtain ⟨u, v, huv⟩ := G₂.exists_isLink_of_mem_edgeSet he₂
        exact ⟨u, v, huv.mono hsep_G.2.1, Or.inr huv.left_mem, Or.inr huv.right_mem⟩
    have hsep_star : IsGraphSeparation S.G G''₁ G2_star := by
      refine ⟨hG''₁_le_G, hG2_star_le, ?_, ?_, ?_⟩
      · apply Subset.antisymm
        · exact union_subset hG''₁_le_G.vertexSet_mono hG2_star_le.vertexSet_mono
        · intro z hz
          by_cases hz₂ : z ∈ V(G₂)
          · exact Or.inr (Or.inr hz₂)
          · have hz_S' : z ∈ V(S'.G) := by
              rw [hG', vertexSet_deleteVertices]; exact ⟨hz, hz₂⟩
            have hz_G'' : z ∈ V(G'') ∧ z ≠ a := by
              rwa [hG'_eq, vertexSet_deleteVertices] at hz_S'
            rcases hsep''.2.2.1 ▸ hz_G''.1 with hz₁'' | hz₂''
            · exact Or.inl hz₁''
            · exact Or.inr (Or.inl ⟨hz₂'', hz_G''.2⟩)
      · rw [hE_star, ← union_assoc]
        have hE_G''₁ : E(G''₁) ∪ E(G''₂) = E(G₁) := hsep''.2.2.2.1
        rw [hE_G''₁, hsep_G.2.2.2.1]
      · rw [hE_star, disjoint_union_right]
        refine ⟨hsep''.2.2.2.2, ?_⟩
        have hE₁_sub : E(G''₁) ⊆ E(G₁) := hsep''.1.edgeSet_mono
        exact hsep_G.2.2.2.2.mono_left hE₁_sub
    have hbar_star : S.Ω.bar ⊆ V(G2_star) := by
      intro z hz
      by_cases hz₂ : z ∈ V(G₂)
      · exact Or.inr hz₂
      · have hz_S'_bar : z ∈ S'.Ω.bar := by
          rw [hΩ'.1, vertexSet_deleteVertices]; exact ⟨hz, S.bar_subset hz, hz₂⟩
        have hz_S' : z ∈ V(S'.G) := S'.bar_subset hz_S'_bar
        exact Or.inl ⟨hbar_G''₂ (hbar'' ▸ Or.inl hz_S'_bar), ha_not_S' z hz_S'⟩
    have hinter_star : V(G''₁) ∩ V(G2_star) = V(G''₁) ∩ V(G''₂) := by
      ext z
      simp only [hV_star, mem_inter_iff, mem_union, mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ⟨hz₁, ⟨hz₂, _⟩ | hzG₂⟩
        · exact ⟨hz₁, hz₂⟩
        · exact (disjoint_left.mp hdisj_G''₁_G₂ hz₁ hzG₂).elim
      · rintro ⟨hz₁, hz₂⟩
        exact ⟨hz₁, Or.inl ⟨hz₂, fun h => ha_not_G''₁ (h ▸ hz₁)⟩⟩
    have hcard_star : (V(G''₁) ∩ V(G2_star)).ncard ≤ 3 := hinter_star ▸ hcard_inter''
    have hV_star_add_2 : V(G2_star).ncard + 2 ≤ V(S.G).ncard := by
      have hfin₁'' : V(G''₁).Finite := hVG''_fin.subset hsep''.1.vertexSet_mono
      have hfin₂'' : V(G''₂).Finite := hVG''_fin.subset hsep''.2.1.vertexSet_mono
      have hfin_star : V(G2_star).Finite := S.finite_V.subset hG2_star_le.vertexSet_mono
      have hun'' := ncard_union_add_ncard_inter V(G''₁) V(G''₂) hfin₁'' hfin₂''
      rw [hsep''.2.2.1] at hun''
      have hun_star := ncard_union_add_ncard_inter V(G''₁) V(G2_star) hfin₁'' hfin_star
      rw [hsep_star.2.2.1, hinter_star] at hun_star
      omega
    have hV_star_ne : V(G2_star) ≠ V(S.G) := by
      intro heq
      rw [heq] at hV_star_add_2
      omega
    have hint_sep_G : S.IsInternalKSeparation 3 G''₁ G2_star :=
      ⟨⟨⟨hsep_star, hbar_star⟩, hcard_star, hV_star_ne⟩, hV_star_add_2⟩
    exact hconn 3 (by omega) G''₁ G2_star hint_sep_G

/-! ## Proof of (5.5): Combining (5.2), (5.3), and (5.4) -/

/-- Dropping `a 0` and `b 0` from `(List.ofFn a).reverse ++ List.ofFn b` preserves
`IsClockwiseSeq`. -/
private theorem isClockwiseSeq_succ_ofFn {m : ℕ} {a b : Fin (m + 1) → α}
    (hcw : S.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b)) :
    S.Ω.IsClockwiseSeq
      ((List.ofFn (fun i : Fin m => a i.succ)).reverse ++
        List.ofFn (fun i : Fin m => b i.succ)) := by
  let L := (List.ofFn a).reverse ++ List.ofFn b
  let a' : Fin m → α := fun i => a i.succ
  let b' : Fin m → α := fun i => b i.succ
  let M := (List.ofFn a').reverse ++ List.ofFn b'
  have hlen_L : L.length = (m + 1) + (m + 1) := by simp [L]; omega
  have hlen_M : M.length = m + m := by simp [M]
  let pos (i : ℕ) : ℕ := if i < m then i else i + 2
  have hsub : CyclicPerm.IsBoundedSubseq L M 0 L.length := by
    refine ⟨Nat.zero_le _, pos, fun i hi => ?_, fun i j hij hj => ?_⟩
    · have hi' : i < m + m := hlen_M ▸ hi
      by_cases him : i < m
      · have hpos_lt : pos i < L.length := by simp [pos, him, hlen_L]; omega
        refine ⟨hpos_lt, Nat.zero_le _, hpos_lt, ?_⟩
        have hM_i : M[i]'hi = a ⟨m - i, by omega⟩ := by
          dsimp [M]
          rw [List.getElem_append_left (by simp; omega), List.getElem_reverse]
          simp only [List.length_ofFn, List.getElem_ofFn, a', Fin.succ]
          congr 1; ext; dsimp; omega
        have hL_i : L[pos i]'hpos_lt = a ⟨m - i, by omega⟩ := by
          dsimp [L]
          rw [List.getElem_append_left (by simp [pos, him]; omega), List.getElem_reverse]
          simp only [List.length_ofFn, List.getElem_ofFn, pos, him, ↓reduceIte]
          rfl
        exact hM_i.trans hL_i.symm
      · have hpos_lt : pos i < L.length := by simp [pos, him, hlen_L]; omega
        refine ⟨hpos_lt, Nat.zero_le _, hpos_lt, ?_⟩
        have hM_i : M[i]'hi = b ⟨i - m + 1, by omega⟩ := by
          dsimp [M]
          rw [List.getElem_append_right (by simp; omega)]
          simp only [List.length_reverse, List.length_ofFn, List.getElem_ofFn, b', Fin.succ]
        have hL_i : L[pos i]'hpos_lt = b ⟨i - m + 1, by omega⟩ := by
          dsimp [L]
          rw [List.getElem_append_right (by simp [pos, him]; omega)]
          simp only [List.length_reverse, List.length_ofFn, List.getElem_ofFn, pos, him, ↓reduceIte]
          congr 1; ext; dsimp; omega
        exact hM_i.trans hL_i.symm
    · rw [hlen_M] at hj
      dsimp [pos]
      split_ifs <;> omega
  exact hcw.of_isBoundedSubseq hsub

/-- If `(List.ofFn a).reverse ++ List.ofFn b` is clockwise in `S.Ω` and `0 < j`, then in `S₀.Ω`
we have `r ∈ S₀.Ω.interval (a j) (b j)`,
`S₀.Ω.interval (a j) (b j) = S.Ω.interval (a j) (b j) ∪ {r}`, and
`S₀.Ω.interval (b j) (a j) = S.Ω.interval (b j) (a j)`. -/
private theorem mem_interval_r_of_clockwise {S₀ : Society α β} {m : ℕ}
    {a b : Fin (m + 1) → α} {r : α}
    (hbar₀ : S₀.Ω.bar = S.Ω.bar ∪ {r})
    (hrest₀ : S₀.Ω.IsRestriction S.Ω.bar S.Ω)
    (hab_empty : S.Ω.interval (a 0) (b 0) = ∅)
    (hcw_arb : S₀.Ω.IsClockwise3 (a 0) r (b 0))
    (hcw : S.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b))
    {j : Fin (m + 1)} (hj : (0 : Fin (m + 1)) < j) :
    r ∈ S₀.Ω.interval (a j) (b j) ∧
      S₀.Ω.interval (a j) (b j) = S.Ω.interval (a j) (b j) ∪ {r} ∧
      S₀.Ω.interval (b j) (a j) = S.Ω.interval (b j) (a j) := by
  obtain ⟨h₀_ab, _, _, _, _⟩ :=
    S.Ω.extension_intervals hbar₀ hrest₀ hab_empty hcw_arb
  obtain ⟨ha0_j, hb0_j, _, haj_b0a0, hbj_b0a0⟩ :=
    S.Ω.mem_intervals_of_isClockwiseSeq_ofFn hcw hj
  have haj_bar : a j ∈ S.Ω.bar := haj_b0a0.1.1
  have hbj_bar : b j ∈ S.Ω.bar := hbj_b0a0.1.1
  have hr_a0b0 : r ∈ S₀.Ω.interval (a 0) (b 0) := by rw [h₀_ab]; rfl
  -- Also `a 0 ∈ S.Ω.interval (a j) (b 0)`.
  have ha0_ajb0 : a 0 ∈ S.Ω.interval (a j) (b 0) := by
    let L := (List.ofFn a).reverse ++ List.ofFn b
    have hj_lt : j.1 < m + 1 := j.2
    have h1 : m - j.1 < m := by omega
    have h2 : m < m + 1 := by omega
    have hlen_rev : (List.ofFn a).reverse.length = m + 1 := by simp
    have hlen_L : L.length = (m + 1) + (m + 1) := by simp [L]; omega
    have h3 : m + 1 < L.length := by omega
    have h := S.Ω.mem_interval_of_lt hcw h1 h2 h3
    have hL1 : L[m - j.1]'(by omega) = a j := by
      dsimp [L]
      rw [List.getElem_append_left (by omega), List.getElem_reverse]
      simp only [List.length_ofFn, List.getElem_ofFn]
      congr 1; ext; dsimp; omega
    have hL2 : L[m]'(by omega) = a 0 := by
      dsimp [L]
      rw [List.getElem_append_left (by omega), List.getElem_reverse]
      simp only [List.length_ofFn, List.getElem_ofFn]
      congr 1; ext; dsimp; omega
    have hL3 : L[m + 1]'h3 = b 0 := by
      dsimp [L]
      rw [List.getElem_append_right (by omega)]
      simp only [List.length_reverse, List.length_ofFn, List.getElem_ofFn]
      congr 1; ext; dsimp; omega
    rwa [hL1, hL2, hL3] at h
  have ha0_ajb0' : a 0 ∈ S₀.Ω.interval (a j) (b 0) :=
    ⟨⟨hbar₀ ▸ Or.inl ha0_ajb0.1.1, ha0_ajb0.1.2⟩, (hrest₀.isClockwise3_iff.mp ha0_ajb0.2).2.2.2⟩
  have hb0_ajbj' : b 0 ∈ S₀.Ω.interval (a j) (b j) :=
    ⟨⟨hbar₀ ▸ Or.inl hb0_j.1.1, hb0_j.1.2⟩, (hrest₀.isClockwise3_iff.mp hb0_j.2).2.2.2⟩
  have hr_ajb0 : r ∈ S₀.Ω.interval (a j) (b 0) :=
    S₀.Ω.interval_subset_interval_right ha0_ajb0' hr_a0b0
  have hr_ajbj : r ∈ S₀.Ω.interval (a j) (b j) :=
    S₀.Ω.interval_subset_interval_left hb0_ajbj' hr_ajb0
  have hr_not_bja : r ∉ S₀.Ω.interval (b j) (a j) :=
    disjoint_left.mp (S₀.Ω.disjoint_interval_swap (a j) (b j)) hr_ajbj
  have h_inter_ab := hrest₀.interval_eq haj_bar hbj_bar
  have h_inter_ba := hrest₀.interval_eq hbj_bar haj_bar
  refine ⟨hr_ajbj, ?_, ?_⟩
  · ext z
    simp only [mem_union, mem_singleton_iff]
    constructor
    · intro hz
      have hz_bar : z ∈ S.Ω.bar ∪ {r} := hbar₀ ▸ hz.1.1
      rcases hz_bar with hzS | rfl
      · left; rw [h_inter_ab]; exact ⟨hz, hzS⟩
      · exact Or.inr rfl
    · rintro (hz | rfl)
      · rw [h_inter_ab] at hz; exact hz.1
      · exact hr_ajbj
  · ext z
    constructor
    · intro hz
      have hz_bar : z ∈ S.Ω.bar ∪ {r} := hbar₀ ▸ hz.1.1
      rcases hz_bar with hzS | rfl
      · rw [h_inter_ba]; exact ⟨hz, hzS⟩
      · exact (hr_not_bja hz).elim
    · intro hz
      rw [h_inter_ba] at hz; exact hz.1

/-- **Graph Minors IX, (5.5), Claim (1)** (page 54):
"$Q_2, \dots, Q_{p+5}$ are separating $\Omega_0$-paths of $(G, \Omega_0)$." -/
theorem lemma_5_5_claim_1 {S₀ : Society α β} {m : ℕ}
    {Q : Fin (m + 1) → Graph α β} {a b : Fin (m + 1) → α} {r : α}
    (hG₀ : S₀.G = S.G)
    (hbar₀ : S₀.Ω.bar = S.Ω.bar ∪ {r})
    (hrest₀ : S₀.Ω.IsRestriction S.Ω.bar S.Ω)
    (hab_empty : S.Ω.interval (a 0) (b 0) = ∅)
    (hcw_arb : S₀.Ω.IsClockwise3 (a 0) r (b 0))
    (hr_Q0 : r ∈ V(Q 0) \ {a 0, b 0})
    (hno_int0 : Disjoint (pathInternalVerts S.G (Q 0)) S.Ω.bar)
    (hdisj_Q : Pairwise (fun i j => Disjoint V(Q i) V(Q j)))
    (hends_Q : ∀ i, S.IsOmegaPathWithEnds (Q i) (a i) (b i))
    (hsep_Q : ∀ i, S.IsSeparatingOmegaPath (Q i))
    (hcw : S.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b))
    (j : Fin (m + 1)) (hj : (0 : Fin (m + 1)) < j) :
    S₀.IsSeparatingOmegaPath (Q j) := by
  have hQj_ends : S.IsOmegaPathWithEnds (Q j) (a j) (b j) := hends_Q j
  have hQj_ends₀ : S₀.IsOmegaPathWithEnds (Q j) (a j) (b j) :=
    ⟨hG₀ ▸ hQj_ends.1, hQj_ends.2.1, hbar₀ ▸ Or.inl hQj_ends.2.2.1,
      hbar₀ ▸ Or.inl hQj_ends.2.2.2⟩
  refine ⟨⟨a j, b j, hQj_ends₀⟩, ?_⟩
  rintro ⟨P, hdisj_PQj, s, t, a', b', hP₀, hQj₀', hcr₀⟩
  have hQj_S' : S.IsOmegaPathWithEnds (Q j) a' b' := by
    refine ⟨hG₀ ▸ hQj₀'.1, hQj₀'.2.1, ?_, ?_⟩
    · rcases (hG₀ ▸ hQj₀'.1).ends_eq hQj_ends.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hQj_ends.2.2.1
      · exact hQj_ends.2.2.2
    · rcases (hG₀ ▸ hQj₀'.1).ends_eq hQj_ends.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hQj_ends.2.2.2
      · exact hQj_ends.2.2.1
  have hcr₀_ajbj : S₀.Ω.Crosses s t (a j) (b j) := by
    rcases hQj_ends.ends_eq S hQj_S' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcr₀
    · exact hcr₀.swap_right
  obtain ⟨hr_ajbj, _, h₀_bja⟩ :=
    S.mem_interval_r_of_clockwise hbar₀ hrest₀ hab_empty hcw_arb hcw hj
  obtain ⟨ha0_ajbj, hb0_ajbj, _, _, _⟩ := S.Ω.mem_intervals_of_isClockwiseSeq_ofFn hcw hj
  -- Helper when one end of `P` is `r` and the other end `t'` is in `S₀.Ω.bar`.
  have h_from_r : ∀ {t' : α}, S₀.IsOmegaPathWithEnds P r t' →
      S₀.Ω.Crosses r t' (a j) (b j) → False := by
    intro t' hP_rt' hcr_rt'
    have ht'_bja : t' ∈ S.Ω.interval (b j) (a j) := by
      rcases S₀.Ω.crosses_iff_interval.mp hcr_rt'.symm with ⟨_, ht'⟩ | ⟨_, hr_ba⟩
      · rwa [← h₀_bja]
      · exact (disjoint_left.mp (S₀.Ω.disjoint_interval_swap (a j) (b j)) hr_ajbj hr_ba).elim
    have ht'_not_Q0 : t' ∉ V(Q 0) := by
      intro ht'_Q0
      have ht'_ab0 : t' = a 0 ∨ t' = b 0 := by
        by_contra hnot
        have hint : t' ∈ pathInternalVerts S.G (Q 0) := by
          rw [(hends_Q 0).1.pathInternalVerts_eq]
          exact ⟨ht'_Q0, hnot⟩
        exact disjoint_left.mp hno_int0 hint ht'_bja.1.1
      rcases ht'_ab0 with rfl | rfl
      · exact disjoint_left.mp (S.Ω.disjoint_interval_swap (a j) (b j)) ha0_ajbj ht'_bja
      · exact disjoint_left.mp (S.Ω.disjoint_interval_swap (a j) (b j)) hb0_ajbj ht'_bja
    have hP_G : IsGraphPathWithEnds S.G P t' r := (hG₀ ▸ hP_rt'.1).symm
    obtain ⟨t'', ht''_eq, x, hx_Q0, R₁, hR₁_P, hR₁_ft⟩ :=
      hP_G.exists_isFromToPathWithEnds (X := {t'}) (Y := V(Q 0)) rfl hr_Q0.1
    rw [mem_singleton_iff] at ht''_eq
    subst t''
    obtain ⟨R₂, hR₂_Q0, _, hR₂_G⟩ := (hends_Q 0).1.exists_subpath hx_Q0 (hends_Q 0).1.left_mem
    have hinter_R₁R₂ : V(R₁) ∩ V(R₂) = {x} := by
      ext z
      simp only [mem_inter_iff, mem_singleton_iff]
      refine ⟨fun ⟨hz₁, hz₂⟩ => ?_, fun h => h ▸ ⟨hR₁_ft.1.right_mem, hR₂_G.left_mem⟩⟩
      have : z ∈ V(R₁) ∩ V(Q 0) := ⟨hz₁, hR₂_Q0.vertexSet_mono hz₂⟩
      rwa [hR₁_ft.2.2, mem_singleton_iff] at this
    let P' := subgraphUnion S.G R₁ R₂
    have hP'_G : IsGraphPathWithEnds S.G P' t' (a 0) := hR₁_ft.1.subgraphUnion hR₂_G hinter_R₁R₂
    have ht'_ne_a0 : t' ≠ a 0 := fun h =>
      disjoint_left.mp (S.Ω.disjoint_interval_swap (a j) (b j)) ha0_ajbj (h ▸ ht'_bja)
    have hP'_omega : S.IsOmegaPathWithEnds P' t' (a 0) :=
      ⟨hP'_G, ht'_ne_a0, ht'_bja.1.1, (hends_Q 0).2.2.1⟩
    have hdisj_Q0Qj : Disjoint V(Q 0) V(Q j) := hdisj_Q (ne_of_lt hj)
    have hdisj_P'Qj : Disjoint V(P') V(Q j) := by
      rw [disjoint_left]
      rintro z (hz₁ | hz₂) hzQj
      · exact disjoint_left.mp hdisj_PQj (hR₁_P.vertexSet_mono hz₁) hzQj
      · exact disjoint_left.mp hdisj_Q0Qj (hR₂_Q0.vertexSet_mono hz₂) hzQj
    have hcr_P'Qj : S.Ω.Crosses t' (a 0) (a j) (b j) :=
      (S.Ω.crosses_iff_interval.mpr (Or.inr ⟨ht'_bja, ha0_ajbj⟩)).symm.swap_left.swap_right
    exact (hsep_Q j).2 ⟨P', hdisj_P'Qj, t', a 0, a j, b j, hP'_omega, hQj_ends, hcr_P'Qj⟩
  by_cases hsr : s = r
  · subst hsr; exact h_from_r hP₀ hcr₀_ajbj
  · by_cases htr : t = r
    · subst htr; exact h_from_r hP₀.symm hcr₀_ajbj.swap_left
    · have hs_S : s ∈ S.Ω.bar := by
        have hs₀ := hP₀.2.2.1; rw [hbar₀, mem_union, mem_singleton_iff] at hs₀
        exact hs₀.resolve_right hsr
      have ht_S : t ∈ S.Ω.bar := by
        have ht₀ := hP₀.2.2.2; rw [hbar₀, mem_union, mem_singleton_iff] at ht₀
        exact ht₀.resolve_right htr
      have hcr_S : S.Ω.Crosses s t (a j) (b j) :=
        hrest₀.crosses_iff.mpr ⟨hs_S, ht_S, hQj_ends.2.2.1, hQj_ends.2.2.2, hcr₀_ajbj⟩
      have hP_S : S.IsOmegaPathWithEnds P s t := ⟨hG₀ ▸ hP₀.1, hP₀.2.1, hs_S, ht_S⟩
      exact (hsep_Q j).2 ⟨P, hdisj_PQj, s, t, a j, b j, hP_S, hQj_ends, hcr_S⟩

/-- If `P_set` is a crooked transaction in `S₀` with `r ∉ S₀.transactionEnds P_set` (where
`S₀.Ω.bar = S.Ω.bar ∪ {r}` and `S₀.Ω.IsRestriction S.Ω.bar S.Ω`), then `P_set` is a crooked
transaction in `S`. -/
private theorem isCrookedTransaction_of_notMem_ends {S₀ : Society α β}
    {P_set : Set (Graph α β)} {r : α}
    (hG₀ : S₀.G = S.G)
    (hbar₀ : S₀.Ω.bar = S.Ω.bar ∪ {r})
    (hrest₀ : S₀.Ω.IsRestriction S.Ω.bar S.Ω)
    (hcr₀ : S₀.IsCrookedTransaction P_set)
    (hr_not : r ∉ S₀.transactionEnds P_set) :
    S.IsCrookedTransaction P_set := by
  rcases hcr₀ with ⟨⟨A₀, B₀, hfence₀⟩, hnot_per₀⟩
  have hends_sub_S : S₀.transactionEnds P_set ⊆ S.Ω.bar := by
    intro v hv
    rcases hv with ⟨P, hP, b, hP_ends⟩
    have hv_bar : v ∈ S.Ω.bar ∪ {r} := hbar₀ ▸ hP_ends.2.2.1
    rcases hv_bar with hvS | rfl
    · exact hvS
    · exact (hr_not ⟨P, hP, b, hP_ends⟩).elim
  have hP_ends_iff : ∀ {P : Graph α β} {x y : α},
      P ∈ P_set → (S.IsOmegaPathWithEnds P x y ↔ S₀.IsOmegaPathWithEnds P x y) := by
    intro P x y hP
    constructor
    · rintro ⟨hPG, hxy, hx, hy⟩
      exact ⟨hG₀.symm ▸ hPG, hxy, hbar₀ ▸ Or.inl hx, hbar₀ ▸ Or.inl hy⟩
    · rintro hP₀
      have hx_S : x ∈ S.Ω.bar := hends_sub_S (hP₀.mem_transactionEnds_left S₀ hP)
      have hy_S : y ∈ S.Ω.bar := hends_sub_S (hP₀.mem_transactionEnds_right S₀ hP)
      exact ⟨hG₀ ▸ hP₀.1, hP₀.2.1, hx_S, hy_S⟩
  have hW_eq : S.transactionEnds P_set = S₀.transactionEnds P_set := by
    ext v
    simp only [transactionEnds]
    exact ⟨fun ⟨P, hP, b, h⟩ => ⟨P, hP, b, (hP_ends_iff hP).mp h⟩,
      fun ⟨P, hP, b, h⟩ => ⟨P, hP, b, (hP_ends_iff hP).mpr h⟩⟩
  let A := A₀ ∩ S.Ω.bar
  let B := B₀ ∩ S.Ω.bar
  have hfence_AB : S.Ω.IsFence A B := by
    refine ⟨inter_subset_right, inter_subset_right,
      hfence₀.2.1.2.2.1.mono inter_subset_left inter_subset_left, ?_, ?_⟩
    · rw [← union_inter_distrib_right, hfence₀.2.1.2.2.2.1, hbar₀,
        inter_eq_right.mpr subset_union_left]
    · intro a₁ ha₁ a₂ ha₂ ha12 b₁ hb₁ b₂ hb₂ hb12 hcr
      exact hfence₀.2.1.2.2.2.2 a₁ ha₁.1 a₂ ha₂.1 ha12 b₁ hb₁.1 b₂ hb₂.1 hb12
        ((hrest₀.crosses_iff.mp hcr).2.2.2.2)
  have hfence_S : S.IsFenceFor P_set A B := by
    refine ⟨⟨?_, hfence₀.1.2⟩, hfence_AB, ?_⟩
    · intro P hP
      obtain ⟨x, y, hxy⟩ := hfence₀.1.1 P hP
      exact ⟨x, y, (hP_ends_iff hP).mpr hxy⟩
    · intro P hP
      obtain ⟨x, hxA, y, hyB, hxy⟩ := hfence₀.2.2 P hP
      have hxy_S := (hP_ends_iff hP).mpr hxy
      exact ⟨x, ⟨hxA, hxy_S.2.2.1⟩, y, ⟨hyB, hxy_S.2.2.2⟩, hxy_S⟩
  refine ⟨⟨A, B, hfence_S⟩, ?_⟩
  intro P hP ⟨_, x, y, hxy_S, hdisj_S⟩
  have hxy₀ : S₀.IsOmegaPathWithEnds P x y := (hP_ends_iff hP).mp hxy_S
  apply hnot_per₀ P hP ⟨hP, x, y, hxy₀, ?_⟩
  rw [← hW_eq]
  rcases hdisj_S with hd | hd
  · left
    rw [disjoint_left]
    intro z hz₀ hzW
    have hz_S : z ∈ S.Ω.interval x y := by
      rw [hrest₀.interval_eq hxy_S.2.2.1 hxy_S.2.2.2]
      exact ⟨hz₀, hends_sub_S (hW_eq ▸ hzW)⟩
    exact disjoint_left.mp hd hz_S hzW
  · right
    rw [disjoint_left]
    intro z hz₀ hzW
    have hz_S : z ∈ S.Ω.interval y x := by
      rw [hrest₀.interval_eq hxy_S.2.2.2 hxy_S.2.2.1]
      exact ⟨hz₀, hends_sub_S (hW_eq ▸ hzW)⟩
    exact disjoint_left.mp hd hz_S hzW

/-- Extending a fence `(A, B)` of `S.Ω` across a one-point extension `S₀.Ω` where
`S.Ω.interval a₀ b₀ = ∅` and `(a₀, r, b₀)` is `S₀.Ω`-clockwise. -/
private theorem exists_isFence_extension {S₀ : Society α β} {A B : Set α} {a₀ b₀ r : α}
    (hbar₀ : S₀.Ω.bar = S.Ω.bar ∪ {r})
    (hrest₀ : S₀.Ω.IsRestriction S.Ω.bar S.Ω)
    (hab_empty : S.Ω.interval a₀ b₀ = ∅)
    (hcw_arb : S₀.Ω.IsClockwise3 a₀ r b₀)
    (hfence : S.Ω.IsFence A B) :
    ∃ A₀ B₀ : Set α, A ⊆ A₀ ∧ B ⊆ B₀ ∧ S₀.Ω.IsFence A₀ B₀ := by
  obtain ⟨h₀_ab, h_a0r_empty, _, _, _⟩ :=
    S.Ω.extension_intervals hbar₀ hrest₀ hab_empty hcw_arb
  have hr_a0b0 : r ∈ S₀.Ω.interval a₀ b₀ := by rw [h₀_ab]; rfl
  have harb_iff := S₀.Ω.isClockwise3_iff.mp hcw_arb
  have ha0_bar : a₀ ∈ S.Ω.bar := by
    rcases hbar₀ ▸ harb_iff.2.2.2.1 with ha0S | rfl
    · exact ha0S
    · exact (harb_iff.1 rfl).elim
  have hb0_bar : b₀ ∈ S.Ω.bar := by
    rcases hbar₀ ▸ harb_iff.2.2.2.2.2.1 with hb0S | rfl
    · exact hb0S
    · exact (harb_iff.2.2.1 rfl).elim
  have hr_not_bar : r ∉ S.Ω.bar := by
    intro hrS
    have hr_in : r ∈ S.Ω.interval a₀ b₀ := by
      rw [hrest₀.interval_eq ha0_bar hb0_bar]
      exact ⟨hr_a0b0, hrS⟩
    rw [hab_empty] at hr_in
    exact hr_in
  have hnot_cr_a0r : ∀ x y : α, ¬ S₀.Ω.Crosses a₀ r x y := fun _ _ =>
    CyclicPerm.Crosses.not_interval_empty (Or.inl h_a0r_empty)
  -- Helper when `a₀ ∈ X` for a fence `(X, Y)` of `S.Ω`.
  have h_case : ∀ {X Y : Set α}, S.Ω.IsFence X Y → a₀ ∈ X →
      S₀.Ω.IsFence (X ∪ {r}) Y := by
    intro X Y hf ha0_X
    have hX_bar : X ⊆ S.Ω.bar := hf.1
    have hY_bar : Y ⊆ S.Ω.bar := hf.2.1
    have hdisj_XY : Disjoint X Y := hf.2.2.1
    have hunion_XY : X ∪ Y = S.Ω.bar := hf.2.2.2.1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hbar₀]; exact union_subset_union_left _ hX_bar
    · rw [hbar₀]; exact hY_bar.trans subset_union_left
    · rw [disjoint_union_left, disjoint_singleton_left]
      exact ⟨hdisj_XY, fun hrY => hr_not_bar (hY_bar hrY)⟩
    · rw [union_right_comm, hunion_XY, hbar₀]
    · intro x₁ hx₁ x₂ hx₂ hx12 y₁ hy₁ y₂ hy₂ hy12 hcr₀
      have hy₁_S : y₁ ∈ S.Ω.bar := hY_bar hy₁
      have hy₂_S : y₂ ∈ S.Ω.bar := hY_bar hy₂
      have ha0_not_Y : a₀ ∉ Y := disjoint_left.mp hdisj_XY ha0_X
      have ha0_not_y12 : a₀ ∉ ({y₁, y₂} : Set α) := by
        rintro (rfl | rfl)
        · exact ha0_not_Y hy₁
        · exact ha0_not_Y hy₂
      have ha0_0 : a₀ ∈ S₀.Ω.bar := hbar₀ ▸ Or.inl ha0_bar
      have h_from_r : ∀ {x : α}, x ∈ X → ¬ S₀.Ω.Crosses r x y₁ y₂ := by
        intro x hxX hcr_rx
        have hx_S : x ∈ S.Ω.bar := hX_bar hxX
        have hcr_a0x : S₀.Ω.Crosses a₀ x y₁ y₂ :=
          (hcr_rx.left_or_right_of_notMem ha0_0 ha0_not_y12).resolve_left (hnot_cr_a0r y₁ y₂)
        have ha0_ne_x : a₀ ≠ x := by
          rcases S₀.Ω.crosses_iff_interval.mp hcr_a0x with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
            exact (S₀.Ω.isClockwise3_iff.mp h1.2).2.1
        have hcr_S : S.Ω.Crosses a₀ x y₁ y₂ :=
          hrest₀.crosses_iff.mpr ⟨ha0_bar, hx_S, hy₁_S, hy₂_S, hcr_a0x⟩
        exact hf.2.2.2.2 a₀ ha0_X x hxX ha0_ne_x y₁ hy₁ y₂ hy₂ hy12 hcr_S
      rcases hx₁ with hx₁X | rfl
      · rcases hx₂ with hx₂X | rfl
        · have hcr_S : S.Ω.Crosses x₁ x₂ y₁ y₂ :=
            hrest₀.crosses_iff.mpr ⟨hX_bar hx₁X, hX_bar hx₂X, hy₁_S, hy₂_S, hcr₀⟩
          exact hf.2.2.2.2 x₁ hx₁X x₂ hx₂X hx12 y₁ hy₁ y₂ hy₂ hy12 hcr_S
        · exact h_from_r hx₁X hcr₀.swap_left
      · rcases hx₂ with hx₂X | rfl
        · exact h_from_r hx₂X hcr₀
        · exact hx12 rfl
  have ha0_AB : a₀ ∈ A ∪ B := hfence.2.2.2.1.symm ▸ ha0_bar
  rcases ha0_AB with ha0_A | ha0_B
  · exact ⟨A ∪ {r}, B, subset_union_left, Subset.rfl, h_case hfence ha0_A⟩
  · have hfence_BA : S.Ω.IsFence B A :=
      ⟨hfence.2.1, hfence.1, hfence.2.2.1.symm, union_comm B A ▸ hfence.2.2.2.1,
        fun b₁ hb₁ b₂ hb₂ hb12 a₁ ha₁ a₂ ha₂ ha12 hcr =>
          hfence.2.2.2.2 a₁ ha₁ a₂ ha₂ ha12 b₁ hb₁ b₂ hb₂ hb12 hcr.symm⟩
    have hf₀_BA := h_case hfence_BA ha0_B
    exact ⟨A, B ∪ {r}, Subset.rfl, subset_union_left,
      ⟨hf₀_BA.2.1, hf₀_BA.1, hf₀_BA.2.2.1.symm, union_comm A (B ∪ {r}) ▸ hf₀_BA.2.2.2.1,
        fun a₁ ha₁ a₂ ha₂ ha12 b₁ hb₁ b₂ hb₂ hb12 hcr =>
          hf₀_BA.2.2.2.2 b₁ hb₁ b₂ hb₂ hb12 a₁ ha₁ a₂ ha₂ ha12 hcr.symm⟩⟩

/-- A crooked transaction in `S` remains a crooked transaction in `S₀`. -/
private theorem isCrookedTransaction_extension {S₀ : Society α β}
    {P_set : Set (Graph α β)} {a₀ b₀ r : α}
    (hG₀ : S₀.G = S.G)
    (hbar₀ : S₀.Ω.bar = S.Ω.bar ∪ {r})
    (hrest₀ : S₀.Ω.IsRestriction S.Ω.bar S.Ω)
    (hab_empty : S.Ω.interval a₀ b₀ = ∅)
    (hcw_arb : S₀.Ω.IsClockwise3 a₀ r b₀)
    (hcr : S.IsCrookedTransaction P_set) :
    S₀.IsCrookedTransaction P_set := by
  rcases hcr with ⟨⟨A, B, hfence⟩, hnot_per⟩
  obtain ⟨A₀, B₀, hAA₀, hBB₀, hfence₀⟩ :=
    S.exists_isFence_extension hbar₀ hrest₀ hab_empty hcw_arb hfence.2.1
  have hP_ends_iff : ∀ {P : Graph α β} {x y : α},
      P ∈ P_set → (S.IsOmegaPathWithEnds P x y ↔ S₀.IsOmegaPathWithEnds P x y) := by
    intro P x y hP
    constructor
    · rintro ⟨hPG, hxy, hx, hy⟩
      exact ⟨hG₀.symm ▸ hPG, hxy, hbar₀ ▸ Or.inl hx, hbar₀ ▸ Or.inl hy⟩
    · rintro hP₀
      obtain ⟨x', y', hP_S⟩ := hfence.1.1 P hP
      rcases (hG₀ ▸ hP₀.1).ends_eq hP_S.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hP_S
      · exact hP_S.symm
  have hW_eq : S₀.transactionEnds P_set = S.transactionEnds P_set := by
    ext v
    simp only [transactionEnds]
    exact ⟨fun ⟨P, hP, b, h⟩ => ⟨P, hP, b, (hP_ends_iff hP).mpr h⟩,
      fun ⟨P, hP, b, h⟩ => ⟨P, hP, b, (hP_ends_iff hP).mp h⟩⟩
  have htr₀ : S₀.IsTransaction P_set := by
    refine ⟨A₀, B₀, ⟨?_, hfence.1.2⟩, hfence₀, ?_⟩
    · intro P hP
      obtain ⟨x, y, hxy⟩ := hfence.1.1 P hP
      exact ⟨x, y, (hP_ends_iff hP).mp hxy⟩
    · intro P hP
      obtain ⟨x, hxA, y, hyB, hxy⟩ := hfence.2.2 P hP
      exact ⟨x, hAA₀ hxA, y, hBB₀ hyB, (hP_ends_iff hP).mp hxy⟩
  refine ⟨htr₀, fun P hP ⟨_, x, y, hxy₀, hdisj₀⟩ => ?_⟩
  have hxy_S : S.IsOmegaPathWithEnds P x y := (hP_ends_iff hP).mpr hxy₀
  apply hnot_per P hP ⟨hP, x, y, hxy_S, ?_⟩
  rw [← hW_eq]
  rcases hdisj₀ with hd | hd
  · left
    apply hd.mono_left
    rw [hrest₀.interval_eq hxy_S.2.2.1 hxy_S.2.2.2]
    exact inter_subset_left
  · right
    apply hd.mono_left
    rw [hrest₀.interval_eq hxy_S.2.2.2 hxy_S.2.2.1]
    exact inter_subset_left

/-- Preliminary step for **Graph Minors IX, (5.5), Claim (2)** (pages 54–55): by (5.2), either
there is a cross `{P₁, P₂}` of `(G, Ω₀)` disjoint from `V(G₂)`, or `(G, Ω)` has a crooked
transaction of cardinality `p` avoiding `Ω(a₂, b₂)`. -/
theorem lemma_5_5_claim_2_disjoint {S₀ : Society α β} {p : ℕ}
    (hp2 : 2 ≤ p) (hp3 : p ≠ 3)
    (hex_cr₀ : ∃ P₀ : Set (Graph α β), S₀.IsCrookedTransaction P₀ ∧ p ≤ P₀.ncard)
    {Q : Fin (p + 5) → Graph α β} {a b : Fin (p + 5) → α} {r : α}
    (hG₀ : S₀.G = S.G)
    (hbar₀ : S₀.Ω.bar = S.Ω.bar ∪ {r})
    (hrest₀ : S₀.Ω.IsRestriction S.Ω.bar S.Ω)
    (hab_empty : S.Ω.interval (a 0) (b 0) = ∅)
    (hcw_arb : S₀.Ω.IsClockwise3 (a 0) r (b 0))
    (hr_Q0 : r ∈ V(Q 0) \ {a 0, b 0})
    (hinj_Q : Function.Injective Q)
    (htr_Q : S.IsTransaction (range Q))
    (hsep_Q : ∀ i : Fin (p + 5), S.IsSeparatingOmegaPath (Q i))
    (hno_int : ∀ i : Fin (p + 5), Disjoint (pathInternalVerts S.G (Q i)) S.Ω.bar)
    (hends_Q : ∀ i : Fin (p + 5), S.IsOmegaPathWithEnds (Q i) (a i) (b i))
    (hcw : S.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b))
    {G₁ G₂ : Graph α β} (hsep_G : IsGraphSeparation S.G G₁ G₂)
    (hinter_G : V(G₁) ∩ V(G₂) = V(Q ⟨p + 4, by omega⟩))
    (hint_G₁ : S.Ω.interval (a ⟨p + 4, by omega⟩) (b ⟨p + 4, by omega⟩) ⊆ V(G₁))
    (hint_G₂ : S.Ω.interval (b ⟨p + 4, by omega⟩) (a ⟨p + 4, by omega⟩) ⊆ V(G₂)) :
    (∃ P₁ P₂ : Graph α β, S₀.OmegaPathsCross P₁ P₂ ∧
      Disjoint V(P₁) V(G₂) ∧ Disjoint V(P₂) V(G₂)) ∨
    (∃ P_set : Set (Graph α β), S.IsCrookedTransaction P_set ∧ P_set.ncard = p ∧
      Disjoint (S.Ω.interval (a ⟨1, by omega⟩) (b ⟨1, by omega⟩)) (S.transactionEnds P_set)) := by
  have : Finite V(S₀.G) := S₀.finite_V
  have : Finite E(S₀.G) := S₀.finite_E
  let Q' : Fin (p + 4) → Graph α β := fun i => Q i.succ
  let a' : Fin (p + 4) → α := fun i => a i.succ
  let b' : Fin (p + 4) → α := fun i => b i.succ
  have hinj_Q' : Function.Injective Q' := fun i j h => Fin.succ_injective _ (hinj_Q h)
  have hdisj_Q : Pairwise (fun i j : Fin (p + 5) => Disjoint V(Q i) V(Q j)) := by
    rcases htr_Q with ⟨_, _, hfence_Q⟩
    intro i j hij
    exact hfence_Q.1.2 (mem_range_self i) (mem_range_self j) (fun h => hij (hinj_Q h))
  have htr_Q' : S₀.IsTransaction (range Q') := by
    rcases htr_Q with ⟨A, B, hfence_Q⟩
    obtain ⟨A₀, B₀, hAA₀, hBB₀, hfence₀⟩ :=
      S.exists_isFence_extension hbar₀ hrest₀ hab_empty hcw_arb hfence_Q.2.1
    refine ⟨A₀, B₀, ⟨?_, ?_⟩, hfence₀, ?_⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨a' i, b' i, (hends_Q i.succ).1 |> fun h =>
        ⟨hG₀.symm ▸ h, (hends_Q i.succ).2.1, hbar₀ ▸ Or.inl (hends_Q i.succ).2.2.1,
          hbar₀ ▸ Or.inl (hends_Q i.succ).2.2.2⟩⟩
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
      exact hfence_Q.1.2 (mem_range_self i.succ) (mem_range_self j.succ) hne
    · rintro _ ⟨i, rfl⟩
      obtain ⟨x, hxA, y, hyB, hxy⟩ := hfence_Q.2.2 (Q i.succ) (mem_range_self i.succ)
      exact ⟨x, hAA₀ hxA, y, hBB₀ hyB,
        ⟨hG₀.symm ▸ hxy.1, hxy.2.1, hbar₀ ▸ Or.inl hxy.2.2.1, hbar₀ ▸ Or.inl hxy.2.2.2⟩⟩
  have hsep_Q' : ∀ i : Fin (p + 4), S₀.IsSeparatingOmegaPath (Q' i) := fun i =>
    S.lemma_5_5_claim_1 hG₀ hbar₀ hrest₀ hab_empty hcw_arb hr_Q0 (hno_int 0)
      hdisj_Q hends_Q hsep_Q hcw i.succ (Fin.succ_pos i)
  have hno_int' : ∀ i : Fin (p + 4), Disjoint (pathInternalVerts S₀.G (Q' i)) S₀.Ω.bar := by
    intro i
    rw [hG₀, hbar₀, disjoint_union_right, disjoint_singleton_right]
    refine ⟨hno_int i.succ, fun hr_int => ?_⟩
    exact disjoint_left.mp (hdisj_Q (Fin.succ_ne_zero i).symm) hr_Q0.1 hr_int.1
  have hends_Q' : ∀ i : Fin (p + 4), S₀.IsOmegaPathWithEnds (Q' i) (a' i) (b' i) := fun i =>
    ⟨hG₀.symm ▸ (hends_Q i.succ).1, (hends_Q i.succ).2.1,
      hbar₀ ▸ Or.inl (hends_Q i.succ).2.2.1, hbar₀ ▸ Or.inl (hends_Q i.succ).2.2.2⟩
  have hcw' : S₀.Ω.IsClockwiseSeq ((List.ofFn a').reverse ++ List.ofFn b') := by
    have hcw_S := S.isClockwiseSeq_succ_ofFn hcw
    exact (hrest₀.isClockwiseSeq_iff.mp hcw_S).2
  let i_last : Fin (p + 4) := ⟨p + 3, by omega⟩
  have hinter_G' : V(G₁) ∩ V(G₂) = V(Q' i_last) := hinter_G
  obtain ⟨hr_mlast, h₀_ab_mlast, h₀_ba_mlast⟩ :=
    S.mem_interval_r_of_clockwise hbar₀ hrest₀ hab_empty hcw_arb hcw (Fin.succ_pos i_last)
  -- Show `r ∈ V(G₁)` since `Q 0` is disjoint from `V(G₂)`.
  have hr_G₁ : r ∈ V(G₁) := by
    obtain ⟨ha0_mlast, hb0_mlast, _, _, _⟩ :=
      S.Ω.mem_intervals_of_isClockwiseSeq_ofFn hcw (Fin.succ_pos i_last)
    have hdisj_Q0_G₂ : Disjoint V(Q 0) V(G₂) :=
      S.disjoint_right_of_ends_in_interval_of_separating
        (hends_Q i_last.succ) (hsep_Q i_last.succ) (hends_Q i_last.succ) (hno_int i_last.succ)
        Subset.rfl (Or.inl rfl) hsep_G hinter_G hint_G₁ (hends_Q 0)
        (hdisj_Q (Fin.succ_ne_zero i_last).symm) ha0_mlast hb0_mlast
    have hr_G : r ∈ V(S.G) := (hends_Q 0).1.1.vertexSet_mono hr_Q0.1
    rw [← hsep_G.2.2.1] at hr_G
    exact hr_G.resolve_right (disjoint_left.mp hdisj_Q0_G₂ hr_Q0.1)
  have hint_G₁' : S₀.Ω.interval (a' i_last) (b' i_last) ⊆ V(G₁) := by
    dsimp [a', b']
    rw [h₀_ab_mlast, union_subset_iff, singleton_subset_iff]
    exact ⟨hint_G₁, hr_G₁⟩
  have hint_G₂' : S₀.Ω.interval (b' i_last) (a' i_last) ⊆ V(G₂) := by
    dsimp [a', b']
    rwa [h₀_ba_mlast]
  rcases S₀.theorem_5_2_proof hp2 hp3 hex_cr₀ hinj_Q' htr_Q' hsep_Q' hno_int' hends_Q' hcw'
      (hG₀.symm ▸ hsep_G) hinter_G' hint_G₁' hint_G₂' with
    ⟨P₁, P₂, hcr₁₂, hd₁, hd₂⟩ | ⟨P_set, hcr_P, hcard_P, hdisj_1⟩
  · exact Or.inl ⟨P₁, P₂, hcr₁₂, hd₁, hd₂⟩
  · right
    let j₁ : Fin (p + 5) := ⟨1, by omega⟩
    have hj₁_pos : (0 : Fin (p + 5)) < j₁ := by
      change (0 : ℕ) < 1
      omega
    obtain ⟨hr_j1, h₀_ab_j1, _⟩ :=
      S.mem_interval_r_of_clockwise hbar₀ hrest₀ hab_empty hcw_arb hcw hj₁_pos
    have hdisj_1' : Disjoint (S₀.Ω.interval (a j₁) (b j₁)) (S₀.transactionEnds P_set) := hdisj_1
    have hr_not_ends : r ∉ S₀.transactionEnds P_set :=
      disjoint_left.mp hdisj_1' hr_j1
    have hcr_P_S : S.IsCrookedTransaction P_set :=
      S.isCrookedTransaction_of_notMem_ends hG₀ hbar₀ hrest₀ hcr_P hr_not_ends
    have hends_sub : S.transactionEnds P_set ⊆ S₀.transactionEnds P_set := by
      intro v ⟨P, hP, y, hxy⟩
      exact ⟨P, hP, y, hG₀.symm ▸ hxy.1, hxy.2.1,
        hbar₀ ▸ Or.inl hxy.2.2.1, hbar₀ ▸ Or.inl hxy.2.2.2⟩
    have hdisj_S : Disjoint (S.Ω.interval (a j₁) (b j₁)) (S.transactionEnds P_set) := by
      apply hdisj_1'.mono _ hends_sub
      rw [h₀_ab_j1]
      exact subset_union_left
    exact ⟨P_set, hcr_P_S, hcard_P, hdisj_S⟩

/-- If `a₀, b₀ ∈ S.Ω.bar` are distinct with `S.Ω.interval a₀ b₀ = ∅`, and `r ∈ V(S.G) \ S.Ω.bar`,
then there is a society `S₀` with `S₀.G = S.G`, `S₀.Ω.bar = S.Ω.bar ∪ {r}`,
`S₀.Ω.IsRestriction S.Ω.bar S.Ω`, and `S₀.Ω.IsClockwise3 a₀ r b₀`. -/
private theorem exists_society_extension {a₀ b₀ r : α}
    (ha₀ : a₀ ∈ S.Ω.bar) (hb₀ : b₀ ∈ S.Ω.bar) (hab_ne : a₀ ≠ b₀)
    (hab_empty : S.Ω.interval a₀ b₀ = ∅)
    (hr_G : r ∈ V(S.G)) (hr_not : r ∉ S.Ω.bar) :
    ∃ S₀ : Society α β,
      S₀.G = S.G ∧
      S₀.Ω.bar = S.Ω.bar ∪ {r} ∧
      S₀.Ω.IsRestriction S.Ω.bar S.Ω ∧
      S₀.Ω.IsClockwise3 a₀ r b₀ := by
  classical
  have hnext_a0 : S.Ω a₀ = b₀ := by
    by_contra hne_b
    have hne_a : S.Ω a₀ ≠ a₀ := by
      intro heq
      have hhit_self : S.Ω.FirstHitIn S.Ω.bar a₀ a₀ :=
        ⟨1, le_rfl, heq, ha₀, fun j hj1 hjlt _ => by omega⟩
      exact S.Ω.not_firstHitIn_self ha₀ hb₀ hb₀ hab_ne.symm hhit_self
    have hmem_ba : S.Ω a₀ ∈ S.Ω.interval b₀ a₀ := by
      rcases S.Ω.mem_interval_or_interval_swap ha₀ hb₀ (S.Ω.toFun_mem ha₀) hab_ne hne_a hne_b with
        hab | hba
      · rw [hab_empty] at hab; exact hab.elim
      · exact hba
    have hcw3 : S.Ω.IsClockwise3 a₀ b₀ (S.Ω a₀) :=
      S.Ω.isClockwise3_rotate (S.Ω.isClockwise3_rotate hmem_ba.2)
    have hhit_b : S.Ω.FirstHitIn {a₀, b₀, S.Ω a₀} a₀ b₀ :=
      (S.Ω.isClockwise3_iff.mp hcw3).2.2.2.2.2.2.1
    have hhit_1 : S.Ω.FirstHitIn {a₀, b₀, S.Ω a₀} a₀ (S.Ω a₀) :=
      ⟨1, le_rfl, rfl, by simp, fun j hj1 hjlt _ => by omega⟩
    exact hne_b (hhit_1.unique hhit_b)
  have ha0_ne_r : a₀ ≠ r := fun h => hr_not (h ▸ ha₀)
  have hb0_ne_r : b₀ ≠ r := fun h => hr_not (h ▸ hb₀)
  let bar₀ : Set α := S.Ω.bar ∪ {r}
  let f (x : α) : α := if x = a₀ then r else if x = r then b₀ else S.Ω x
  have hf_a0 : f a₀ = r := by simp [f]
  have hf_r : f r = b₀ := by simp [f, ha0_ne_r.symm]
  have hf_other : ∀ {x : α}, x ∈ S.Ω.bar → x ≠ a₀ → f x = S.Ω x := by
    intro x hx hne
    have hxr : x ≠ r := fun h => hr_not (h ▸ hx)
    simp [f, hne, hxr]
  have hmaps : MapsTo f bar₀ bar₀ := by
    rintro x (hxS | hxr)
    · by_cases hxa : x = a₀
      · subst x; rw [hf_a0]; exact Or.inr rfl
      · rw [hf_other hxS hxa]; exact Or.inl (S.Ω.toFun_mem hxS)
    · rw [mem_singleton_iff] at hxr; subst x
      rw [hf_r]; exact Or.inl hb₀
  have hinj : InjOn f bar₀ := by
    rintro x (hxS | hxr) y (hyS | hyr) hxy
    · by_cases hxa : x = a₀
      · subst x; rw [hf_a0] at hxy
        by_cases hya : y = a₀
        · exact hya.symm
        · rw [hf_other hyS hya] at hxy
          exact (hr_not (hxy ▸ S.Ω.toFun_mem hyS)).elim
      · rw [hf_other hxS hxa] at hxy
        by_cases hya : y = a₀
        · subst y; rw [hf_a0] at hxy
          exact (hr_not (hxy ▸ S.Ω.toFun_mem hxS)).elim
        · rw [hf_other hyS hya] at hxy
          exact S.Ω.bijOn.injOn hxS hyS hxy
    · rw [mem_singleton_iff] at hyr; subst y
      rw [hf_r] at hxy
      by_cases hxa : x = a₀
      · subst x; rw [hf_a0] at hxy
        exact (hb0_ne_r hxy.symm).elim
      · rw [hf_other hxS hxa, ← hnext_a0] at hxy
        exact (hxa (S.Ω.bijOn.injOn hxS ha₀ hxy)).elim
    · rw [mem_singleton_iff] at hxr; subst x
      rw [hf_r] at hxy
      by_cases hya : y = a₀
      · subst y; rw [hf_a0] at hxy; exact (hb0_ne_r hxy).elim
      · rw [hf_other hyS hya, ← hnext_a0] at hxy
        exact (hya (S.Ω.bijOn.injOn hyS ha₀ hxy.symm)).elim
    · rw [mem_singleton_iff] at hxr hyr; exact hxr.trans hyr.symm
  have hsurj : SurjOn f bar₀ bar₀ := by
    rintro y (hyS | hyr)
    · by_cases hyb : y = b₀
      · subst y; exact ⟨r, Or.inr rfl, hf_r⟩
      · obtain ⟨x, hxS, rfl⟩ := S.Ω.bijOn.surjOn hyS
        have hxa : x ≠ a₀ := fun h => hyb (h ▸ hnext_a0)
        exact ⟨x, Or.inl hxS, hf_other hxS hxa⟩
    · rw [mem_singleton_iff] at hyr; subst y
      exact ⟨a₀, Or.inl ha₀, hf_a0⟩
  have hstep_S : ∀ x ∈ S.Ω.bar, ∃ m : ℕ, (f^[m]) x = S.Ω x := by
    intro x hx
    by_cases hxa : x = a₀
    · subst x
      refine ⟨2, ?_⟩
      change f (f a₀) = S.Ω a₀
      rw [hf_a0, hf_r, hnext_a0]
    · exact ⟨1, hf_other hx hxa⟩
  have hiter_S : ∀ (k : ℕ) {x : α}, x ∈ S.Ω.bar → ∃ N : ℕ, (f^[N]) x = (S.Ω.toFun^[k]) x := by
    intro k
    induction k with
    | zero => intro x _; exact ⟨0, rfl⟩
    | succ k ih =>
      intro x hx
      obtain ⟨N, hN⟩ := ih hx
      obtain ⟨m, hm⟩ := hstep_S ((S.Ω.toFun^[k]) x) (S.Ω.iterate_mem k hx)
      refine ⟨m + N, ?_⟩
      rw [Function.iterate_add_apply, hN, hm, Function.iterate_succ_apply']
  have horb_S : ∀ x ∈ S.Ω.bar, ∀ y ∈ S.Ω.bar, ∃ N : ℕ, (f^[N]) x = y := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := S.Ω.single_orbit x hx y hy
    exact hiter_S k hx
  have horb₀ : ∀ x ∈ bar₀, ∀ y ∈ bar₀, ∃ N : ℕ, (f^[N]) x = y := by
    rintro x (hxS | hxr) y (hyS | hyr)
    · exact horb_S x hxS y hyS
    · rw [mem_singleton_iff] at hyr; subst y
      obtain ⟨N, hN⟩ := horb_S x hxS a₀ ha₀
      refine ⟨N + 1, ?_⟩
      rw [Function.iterate_succ_apply', hN, hf_a0]
    · rw [mem_singleton_iff] at hxr; subst x
      obtain ⟨N, hN⟩ := horb_S b₀ hb₀ y hyS
      refine ⟨N + 1, ?_⟩
      rw [Function.iterate_succ_apply, hf_r, hN]
    · rw [mem_singleton_iff] at hxr hyr; subst x y; exact ⟨0, rfl⟩
  let Ω₀ : CyclicPerm α :=
    { bar := bar₀
      toFun := f
      finite_bar := S.Ω.finite_bar.union (finite_singleton r)
      bijOn := ⟨hmaps, hinj, hsurj⟩
      single_orbit := horb₀ }
  let S₀ : Society α β :=
    { G := S.G
      Ω := Ω₀
      finite_V := S.finite_V
      finite_E := S.finite_E
      bar_subset := union_subset S.bar_subset (singleton_subset_iff.mpr hr_G) }
  have hrest₀ : Ω₀.IsRestriction S.Ω.bar S.Ω := by
    refine ⟨(inter_eq_right.mpr subset_union_left).symm, fun x hx => ?_⟩
    by_cases hxa : x = a₀
    · subst x
      refine ⟨2, by omega, ?_, S.Ω.toFun_mem ha₀, fun j hj1 hjlt => ?_⟩
      · change f (f a₀) = S.Ω a₀
        rw [hf_a0, hf_r, hnext_a0]
      · have hj_eq : j = 1 := by omega
        subst hj_eq
        change f a₀ ∉ S.Ω.bar
        rw [hf_a0]
        exact hr_not
    · refine ⟨1, le_rfl, hf_other hx hxa, S.Ω.toFun_mem hx, fun j hj1 hjlt => by omega⟩
  have hcw_arb : Ω₀.IsClockwise3 a₀ r b₀ := by
    have ha₀_0 : a₀ ∈ Ω₀.bar := Or.inl ha₀
    have hr_0 : r ∈ Ω₀.bar := Or.inr rfl
    have hb₀_0 : b₀ ∈ Ω₀.bar := Or.inl hb₀
    have hhit_ar : Ω₀.FirstHitIn {a₀, r, b₀} a₀ r :=
      ⟨1, le_rfl, hf_a0, by simp, fun j hj1 hjlt _ => by omega⟩
    have hhit_rb : Ω₀.FirstHitIn {a₀, r, b₀} r b₀ :=
      ⟨1, le_rfl, hf_r, by simp, fun j hj1 hjlt _ => by omega⟩
    obtain ⟨z, hhit_bz⟩ := Ω₀.exists_firstHitIn (X := {a₀, r, b₀}) hb₀_0 ⟨b₀, hb₀_0, by simp⟩
    have hz_ne_b : z ≠ b₀ := fun h =>
      Ω₀.not_firstHitIn_self hb₀_0 ha₀_0 (by simp) hab_ne (h ▸ hhit_bz)
    have hz_ne_r : z ≠ r := fun h =>
      hab_ne (hhit_ar.inj_left ha₀_0 hb₀_0 (by simp) (by simp) (h ▸ hhit_bz))
    have hz_eq : z = a₀ := by
      rcases hhit_bz.mem_set with rfl | rfl | rfl
      · rfl
      · exact (hz_ne_r rfl).elim
      · exact (hz_ne_b rfl).elim
    rw [hz_eq] at hhit_bz
    exact Ω₀.isClockwise3_iff.mpr
      ⟨ha0_ne_r, hab_ne, hb0_ne_r.symm, ha₀_0, hr_0, hb₀_0, hhit_ar, hhit_rb, hhit_bz⟩
  exact ⟨S₀, rfl, rfl, hrest₀, hcw_arb⟩

/-- The vertex set of `K`: vertices of `G' = S.G \ V(G₂)` that can reach `ΩBar \ V(G₂)` in `G'`. -/
def reachFromBarMinusSet (G₂ : Graph α β) : Set α :=
  {v ∈ V(deleteVertices S.G V(G₂)) |
    ∃ z ∈ S.Ω.bar \ V(G₂), Nonempty (GraphWalk (deleteVertices S.G V(G₂)) v z)}

/-- The subgraph `K` of `G' = S.G \ V(G₂)` induced on `reachFromBarMinusSet G₂` (the union of all
components of `G'` meeting `ΩBar \ V(G₂)`). -/
def reachFromBarMinusGraph (G₂ : Graph α β) : Graph α β :=
  (deleteVertices S.G V(G₂)).induce (S.reachFromBarMinusSet G₂)

@[simp]
private theorem vertexSet_reachFromBarMinusGraph (G₂ : Graph α β) :
    V(S.reachFromBarMinusGraph G₂) = S.reachFromBarMinusSet G₂ := rfl

private theorem reachFromBarMinusGraph_le_deleteVertices (G₂ : Graph α β) :
    S.reachFromBarMinusGraph G₂ ≤ deleteVertices S.G V(G₂) :=
  (deleteVertices S.G V(G₂)).induce_le fun _ hv => hv.1

private theorem reachFromBarMinusGraph_le (G₂ : Graph α β) :
    S.reachFromBarMinusGraph G₂ ≤ S.G :=
  (S.reachFromBarMinusGraph_le_deleteVertices G₂).trans (deleteVertices_le S.G V(G₂))

private theorem bar_diff_subset_reachFromBarMinusSet (G₂ : Graph α β) :
    S.Ω.bar \ V(G₂) ⊆ S.reachFromBarMinusSet G₂ := by
  intro z hz
  have hz_G' : z ∈ V(deleteVertices S.G V(G₂)) := ⟨S.bar_subset hz.1, hz.2⟩
  exact ⟨hz_G', z, hz, ⟨.nil hz_G'⟩⟩

private theorem bar_inter_reachFromBarMinusGraph (G₂ : Graph α β) :
    S.Ω.bar ∩ V(S.reachFromBarMinusGraph G₂) = S.Ω.bar ∩ V(deleteVertices S.G V(G₂)) := by
  ext z
  simp only [mem_inter_iff, vertexSet_reachFromBarMinusGraph]
  refine ⟨fun ⟨hz_bar, hz_K⟩ => ⟨hz_bar, hz_K.1⟩, fun ⟨hz_bar, hz_G'⟩ => ?_⟩
  exact ⟨hz_bar, S.bar_diff_subset_reachFromBarMinusSet G₂ ⟨hz_bar, hz_G'.2⟩⟩

/-- Any path `P` in `S.G` disjoint from `V(G₂)` whose left end is in `reachFromBarMinusSet G₂`
is a subgraph of `reachFromBarMinusGraph G₂`. -/
private theorem le_reachFromBarMinusGraph_of_isGraphPathWithEnds {G₂ P : Graph α β} {s t : α}
    (hP : IsGraphPathWithEnds S.G P s t) (hdisj : Disjoint V(P) V(G₂))
    (hs : s ∈ S.reachFromBarMinusSet G₂) :
    P ≤ S.reachFromBarMinusGraph G₂ := by
  have hP_G' : P ≤ deleteVertices S.G V(G₂) := le_deleteVertices hP.1 hdisj
  have hVP_K : V(P) ⊆ S.reachFromBarMinusSet G₂ := by
    intro v hv
    obtain ⟨Q_vs, _, hQ_vs_P, _⟩ := hP.exists_subpath hv hP.left_mem
    rcases hQ_vs_P with ⟨hQ_P, W_vs, _, _, _⟩
    obtain ⟨W_vs', _, _⟩ := exists_walk_up_of_le (hQ_P.trans hP_G') W_vs
    rcases hs with ⟨_, z, hz, ⟨W_sz⟩⟩
    exact ⟨hP_G'.vertexSet_mono hv, z, hz, ⟨W_vs'.append W_sz⟩⟩
  rw [(Compatible.of_le_le hP_G' (S.reachFromBarMinusGraph_le_deleteVertices G₂)).le_iff]
  refine ⟨?_, fun e he => ?_⟩
  · rw [vertexSet_reachFromBarMinusGraph]; exact hVP_K
  · obtain ⟨x, y, hxy⟩ := P.exists_isLink_of_mem_edgeSet he
    exact ⟨x, y, hxy.mono hP_G', hVP_K hxy.left_mem, hVP_K hxy.right_mem⟩

/-- **Graph Minors IX, (5.5), Claim (3)** (page 55):
"Let $K$ be the maximal subgraph of $G_1 \setminus V(Q_{p+5})$ caught by $\bar{\Omega} - V(G_2)$...
(3) *$\bar{\Omega} \cap V(K \setminus V(Q_1))$ catches $K \setminus V(Q_1)$.*" -/
theorem lemma_5_5_claim_3 {p : ℕ} (hp2 : 2 ≤ p)
    {Q : Fin (p + 5) → Graph α β} {a b : Fin (p + 5) → α}
    (hinj_Q : Function.Injective Q)
    (htr_Q : S.IsTransaction (range Q))
    (hsep_Q : ∀ i : Fin (p + 5), S.IsSeparatingOmegaPath (Q i))
    (hno_int : ∀ i : Fin (p + 5), Disjoint (pathInternalVerts S.G (Q i)) S.Ω.bar)
    (hends_Q : ∀ i : Fin (p + 5), S.IsOmegaPathWithEnds (Q i) (a i) (b i))
    (hcw : S.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b))
    (hcatches : Catches (S.Ω.bar \ {a 0, b 0}) (deleteVertices S.G V(Q 0)))
    {G₁ G₂ : Graph α β} (hsep_G : IsGraphSeparation S.G G₁ G₂)
    (hinter_G : V(G₁) ∩ V(G₂) = V(Q ⟨p + 4, by omega⟩))
    (hint_G₁ : S.Ω.interval (a ⟨p + 4, by omega⟩) (b ⟨p + 4, by omega⟩) ⊆ V(G₁)) :
    Catches ((S.Ω.bar \ V(G₂)) \ {a 0, b 0})
      (deleteVertices (S.reachFromBarMinusGraph G₂) V(Q 0)) := by
  let K := S.reachFromBarMinusGraph G₂
  let K_del := deleteVertices K V(Q 0)
  let j₁ : Fin (p + 5) := ⟨1, by omega⟩
  let m_last : Fin (p + 5) := ⟨p + 4, by omega⟩
  have hj₁_pos : (0 : Fin (p + 5)) < j₁ := by change (0 : ℕ) < 1; omega
  have hj₁_lt_m : j₁ < m_last := by change 1 < p + 4; omega
  have h0_lt_m : (0 : Fin (p + 5)) < m_last := by change 0 < p + 4; omega
  have hdisj_Q : Pairwise (fun i j : Fin (p + 5) => Disjoint V(Q i) V(Q j)) := by
    rcases htr_Q with ⟨_, _, hfence_Q⟩
    intro i j hij
    exact hfence_Q.1.2 (mem_range_self i) (mem_range_self j) (fun h => hij (hinj_Q h))
  have hdisj_01 : Disjoint V(Q 0) V(Q j₁) := hdisj_Q (ne_of_lt hj₁_pos)
  have hdisj_1m : Disjoint V(Q j₁) V(Q m_last) := hdisj_Q (ne_of_lt hj₁_lt_m)
  obtain ⟨ha0_j1, hb0_j1, hsub_01, _, _⟩ := S.Ω.mem_intervals_of_isClockwiseSeq_ofFn hcw hj₁_pos
  obtain ⟨ha1_m, hb1_m, hsub_1m, ham_b1a1, hbm_b1a1⟩ :=
    S.Ω.mem_intervals_of_isClockwiseSeq_ofFn hcw hj₁_lt_m
  -- `Q j₁` is disjoint from `V(G₂)` and lies in `K_del`.
  have hdisj_Q1_G₂ : Disjoint V(Q j₁) V(G₂) :=
    S.disjoint_right_of_ends_in_interval_of_separating
      (hends_Q m_last) (hsep_Q m_last) (hends_Q m_last) (hno_int m_last)
      Subset.rfl (Or.inl rfl) hsep_G hinter_G hint_G₁
      (hends_Q j₁) hdisj_1m ha1_m hb1_m
  have ha1_bar_diff : a j₁ ∈ S.Ω.bar \ V(G₂) :=
    ⟨(hends_Q j₁).2.2.1, disjoint_left.mp hdisj_Q1_G₂ (hends_Q j₁).1.left_mem⟩
  have hQ1_Kdel : Q j₁ ≤ K_del :=
    le_deleteVertices
      (S.le_reachFromBarMinusGraph_of_isGraphPathWithEnds (hends_Q j₁).1 hdisj_Q1_G₂
        (S.bar_diff_subset_reachFromBarMinusSet G₂ ha1_bar_diff))
      hdisj_01.symm
  have ha1_not_ab0 : a j₁ ∉ ({a 0, b 0} : Set α) := by
    rintro (h | h)
    · exact disjoint_left.mp hdisj_01 (h ▸ (hends_Q 0).1.left_mem) (hends_Q j₁).1.left_mem
    · exact disjoint_left.mp hdisj_01 (h ▸ (hends_Q 0).1.right_mem) (hends_Q j₁).1.left_mem
  have ha1_target : a j₁ ∈ (S.Ω.bar \ V(G₂)) \ {a 0, b 0} :=
    ⟨ha1_bar_diff, ha1_not_ab0⟩
  have ha1_Kdel : a j₁ ∈ V(K_del) := hQ1_Kdel.vertexSet_mono (hends_Q j₁).1.left_mem
  refine ⟨fun z hz => ⟨S.bar_diff_subset_reachFromBarMinusSet G₂ hz.1,
    (hcatches.1 ⟨hz.1.1, hz.2⟩).2⟩, fun C hC => ?_⟩
  obtain ⟨v₀, hv₀_C⟩ := hC.2.1.1
  have hC_eq : C = reachableComponent K_del v₀ := isGraphComponent_eq_reachableComponent hC hv₀_C
  have hv₀_Kdel : v₀ ∈ V(K_del) := hC.1.vertexSet_mono hv₀_C
  have hv₀_K : v₀ ∈ S.reachFromBarMinusSet G₂ := hv₀_Kdel.1
  have hv₀_not_Q0 : v₀ ∉ V(Q 0) := hv₀_Kdel.2
  have hv₀_G' : v₀ ∈ V(deleteVertices S.G V(G₂)) := hv₀_K.1
  have hv₀_G₁ : v₀ ∈ V(G₁) := (hsep_G.2.2.1.symm ▸ hv₀_G'.1).resolve_right hv₀_G'.2
  -- Helper: if `v₀` has a path `P_v` in `K_del` to some `u ∈ V(Q j₁)`, then `C` meets the target.
  have hreach_of_Q1 : ∀ {P_v : Graph α β} {u : α},
      IsGraphPathWithEnds K_del P_v v₀ u → u ∈ V(Q j₁) →
      (((S.Ω.bar \ V(G₂)) \ {a 0, b 0}) ∩ V(C)).Nonempty := by
    intro P_v u hPv hu_Q1
    rcases hPv with ⟨hPv_Kdel, W_vu, _, _, _⟩
    obtain ⟨W_vu', _, _⟩ := exists_walk_up_of_le hPv_Kdel W_vu
    obtain ⟨Q1_ua, hQ1_ua_le, hQ1_ua, _⟩ :=
      (hends_Q j₁).1.exists_subpath hu_Q1 (hends_Q j₁).1.left_mem
    rcases hQ1_ua with ⟨_, W_ua, _, _, _⟩
    obtain ⟨W_ua', _, _⟩ := exists_walk_up_of_le (hQ1_ua_le.trans hQ1_Kdel) W_ua
    refine ⟨a j₁, ha1_target, ?_⟩
    rw [hC_eq, vertexSet_reachableComponent]
    exact ⟨ha1_Kdel, ⟨W_vu'.append W_ua'⟩⟩
  -- Step 1: Extract a path `R` in `K` from `v₀` to `z₁ ∈ S.Ω.bar \ V(G₂)`.
  rcases hv₀_K with ⟨_, z₁, hz₁, ⟨W₁⟩⟩
  obtain ⟨R, hR_G', _, _⟩ := exists_isGraphPathWithEnds_of_walk W₁
  have hz₁_K : z₁ ∈ S.reachFromBarMinusSet G₂ := S.bar_diff_subset_reachFromBarMinusSet G₂ hz₁
  have hdisj_R_G₂ : Disjoint V(R) V(G₂) :=
    disjoint_left.mpr fun _ hx => (hR_G'.1.vertexSet_mono hx).2
  have hR_K : R ≤ K :=
    S.le_reachFromBarMinusGraph_of_isGraphPathWithEnds
      (hR_G'.mono (deleteVertices_le S.G V(G₂))).symm hdisj_R_G₂ hz₁_K
  have hR_path_K : IsGraphPathWithEnds K R v₀ z₁ := hR_G'.of_le hR_K
  by_cases hdisj_R_Q0 : Disjoint V(R) V(Q 0)
  · have hR_Kdel : R ≤ K_del := le_deleteVertices hR_K hdisj_R_Q0
    rcases hR_path_K with ⟨_, W_R, _, _, _⟩
    obtain ⟨W_R', _, _⟩ := exists_walk_up_of_le hR_Kdel W_R
    have hz₁_not_Q0 : z₁ ∉ V(Q 0) := disjoint_left.mp hdisj_R_Q0 hR_G'.right_mem
    have hz₁_not_ab0 : z₁ ∉ ({a 0, b 0} : Set α) := by
      rintro (rfl | rfl)
      · exact hz₁_not_Q0 (hends_Q 0).1.left_mem
      · exact hz₁_not_Q0 (hends_Q 0).1.right_mem
    refine ⟨z₁, ⟨hz₁, hz₁_not_ab0⟩, ?_⟩
    rw [hC_eq, vertexSet_reachableComponent]
    exact ⟨⟨hz₁_K, hz₁_not_Q0⟩, ⟨W_R'⟩⟩
  · rw [not_disjoint_iff_nonempty_inter] at hdisj_R_Q0
    rcases hdisj_R_Q0 with ⟨x₀, hx₀_R, hx₀_Q0⟩
    obtain ⟨R₀, hR₀_R, _, hR₀_K⟩ := hR_path_K.exists_subpath hR_path_K.left_mem hx₀_R
    obtain ⟨v₀', hv₀'_eq, x₁, hx₁_01, R₁, hR₁_R₀, hR₁_ft⟩ :=
      hR₀_K.exists_isFromToPathWithEnds (X := {v₀}) (Y := V(Q 0) ∪ V(Q j₁)) rfl (Or.inl hx₀_Q0)
    rw [mem_singleton_iff] at hv₀'_eq
    subst v₀'
    by_cases hx₁_Q1 : x₁ ∈ V(Q j₁)
    · have hx₁_not_Q0 : x₁ ∉ V(Q 0) := disjoint_right.mp hdisj_01 hx₁_Q1
      have hdisj_R₁_Q0 : Disjoint V(R₁) V(Q 0) := by
        rw [disjoint_left]
        intro u hu_R₁ hu_Q0
        have hu_in : u ∈ V(R₁) ∩ (V(Q 0) ∪ V(Q j₁)) := ⟨hu_R₁, Or.inl hu_Q0⟩
        rw [hR₁_ft.2.2, mem_singleton_iff] at hu_in
        exact hx₁_not_Q0 (hu_in ▸ hu_Q0)
      have hR₁_Kdel : IsGraphPathWithEnds K_del R₁ v₀ x₁ :=
        hR₁_ft.1.of_le (le_deleteVertices hR₁_ft.1.1 hdisj_R₁_Q0)
      exact hreach_of_Q1 hR₁_Kdel hx₁_Q1
    · have hx₁_Q0 : x₁ ∈ V(Q 0) := hx₁_01.resolve_right hx₁_Q1
      have hdisj_R₁_Q1 : Disjoint V(R₁) V(Q j₁) := by
        rw [disjoint_left]
        intro u hu_R₁ hu_Q1
        have hu_in : u ∈ V(R₁) ∩ (V(Q 0) ∪ V(Q j₁)) := ⟨hu_R₁, Or.inr hu_Q1⟩
        rw [hR₁_ft.2.2, mem_singleton_iff] at hu_in
        exact hx₁_Q1 (hu_in ▸ hu_Q1)
      -- Step 2: Use `hcatches` on `deleteVertices S.G V(Q 0)` at `v₀`.
      have hv₀_G_no_Q0 : v₀ ∈ V(deleteVertices S.G V(Q 0)) := ⟨hv₀_G'.1, hv₀_not_Q0⟩
      obtain ⟨C_G, hC_G, hv₀_CG⟩ := exists_graphComponent_of_mem hv₀_G_no_Q0
      obtain ⟨z₂, hz₂_bar_diff, hz₂_CG⟩ := hcatches.2 C_G hC_G
      rw [isGraphComponent_eq_reachableComponent hC_G hv₀_CG,
        vertexSet_reachableComponent] at hz₂_CG
      rcases hz₂_CG with ⟨_, ⟨W₂⟩⟩
      obtain ⟨M, hM_no_Q0, _, _⟩ := exists_isGraphPathWithEnds_of_walk W₂
      have hdisj_M_Q0 : Disjoint V(M) V(Q 0) :=
        disjoint_left.mpr fun _ hx => (hM_no_Q0.1.vertexSet_mono hx).2
      have hM_G : IsGraphPathWithEnds S.G M v₀ z₂ :=
        hM_no_Q0.mono (deleteVertices_le S.G V(Q 0))
      by_cases hdisj_M_G₂ : Disjoint V(M) V(G₂)
      · have hM_K : M ≤ K :=
          S.le_reachFromBarMinusGraph_of_isGraphPathWithEnds hM_G hdisj_M_G₂ ⟨hv₀_G', z₁, hz₁, ⟨W₁⟩⟩
        have hM_Kdel : M ≤ K_del := le_deleteVertices hM_K hdisj_M_Q0
        rcases hM_G with ⟨_, W_M, _, _, _⟩
        obtain ⟨W_M', _, _⟩ := exists_walk_up_of_le hM_Kdel W_M
        have hz₂_not_G₂ : z₂ ∉ V(G₂) := disjoint_left.mp hdisj_M_G₂ hM_no_Q0.right_mem
        have hz₂_not_Q0 : z₂ ∉ V(Q 0) := disjoint_left.mp hdisj_M_Q0 hM_no_Q0.right_mem
        have hz₂_K : z₂ ∈ S.reachFromBarMinusSet G₂ :=
          S.bar_diff_subset_reachFromBarMinusSet G₂ ⟨hz₂_bar_diff.1, hz₂_not_G₂⟩
        refine ⟨z₂, ⟨⟨hz₂_bar_diff.1, hz₂_not_G₂⟩, hz₂_bar_diff.2⟩, ?_⟩
        rw [hC_eq, vertexSet_reachableComponent]
        exact ⟨⟨hz₂_K, hz₂_not_Q0⟩, ⟨W_M'⟩⟩
      · rw [not_disjoint_iff_nonempty_inter] at hdisj_M_G₂
        rcases hdisj_M_G₂ with ⟨y₀, hy₀_M, hy₀_G₂⟩
        obtain ⟨M₀, hM₀_M, _, hM₀_G⟩ := hM_G.exists_subpath hM_G.left_mem hy₀_M
        obtain ⟨v₀'', hv₀''_eq, y₁, hy₁_G₂1, M₁, hM₁_M₀, hM₁_ft⟩ :=
          hM₀_G.exists_isFromToPathWithEnds (X := {v₀}) (Y := V(G₂) ∪ V(Q j₁)) rfl (Or.inl hy₀_G₂)
        rw [mem_singleton_iff] at hv₀''_eq
        subst v₀''
        have hM₁_M : M₁ ≤ M := hM₁_M₀.trans hM₀_M
        by_cases hy₁_Q1 : y₁ ∈ V(Q j₁)
        · have hy₁_not_G₂ : y₁ ∉ V(G₂) := disjoint_left.mp hdisj_Q1_G₂ hy₁_Q1
          have hdisj_M₁_G₂ : Disjoint V(M₁) V(G₂) := by
            rw [disjoint_left]
            intro u hu_M₁ hu_G₂
            have hu_in : u ∈ V(M₁) ∩ (V(G₂) ∪ V(Q j₁)) := ⟨hu_M₁, Or.inl hu_G₂⟩
            rw [hM₁_ft.2.2, mem_singleton_iff] at hu_in
            exact hy₁_not_G₂ (hu_in ▸ hu_G₂)
          have hM₁_K : M₁ ≤ K :=
            S.le_reachFromBarMinusGraph_of_isGraphPathWithEnds hM₁_ft.1 hdisj_M₁_G₂
              ⟨hv₀_G', z₁, hz₁, ⟨W₁⟩⟩
          have hdisj_M₁_Q0 : Disjoint V(M₁) V(Q 0) :=
            hdisj_M_Q0.mono_left hM₁_M.vertexSet_mono
          have hM₁_Kdel : IsGraphPathWithEnds K_del M₁ v₀ y₁ :=
            hM₁_ft.1.of_le (le_deleteVertices hM₁_K hdisj_M₁_Q0)
          exact hreach_of_Q1 hM₁_Kdel hy₁_Q1
        · exfalso
          have hy₁_G₂ : y₁ ∈ V(G₂) := hy₁_G₂1.resolve_right hy₁_Q1
          have hdisj_M₁_Q1 : Disjoint V(M₁) V(Q j₁) := by
            rw [disjoint_left]
            intro u hu_M₁ hu_Q1
            have hu_in : u ∈ V(M₁) ∩ (V(G₂) ∪ V(Q j₁)) := ⟨hu_M₁, Or.inr hu_Q1⟩
            rw [hM₁_ft.2.2, mem_singleton_iff] at hu_in
            exact hy₁_Q1 (hu_in ▸ hu_Q1)
          obtain ⟨w, hw_M₁, hw_inter⟩ :=
            exists_mem_inter_of_isGraphPathWithEnds hsep_G hM₁_ft.1 hv₀_G₁ hy₁_G₂
          have hw_eq_y₁ : w = y₁ := by
            have hw_in : w ∈ V(M₁) ∩ (V(G₂) ∪ V(Q j₁)) := ⟨hw_M₁, Or.inl hw_inter.2⟩
            rwa [hM₁_ft.2.2, mem_singleton_iff] at hw_in
          have hy₁_Qm : y₁ ∈ V(Q m_last) := by
            rw [← hinter_G, ← hw_eq_y₁]; exact hw_inter
          -- Build a walk in `G_no_Q1 := deleteVertices S.G V(Q j₁)` from `a 0` to `a m_last`.
          let G_no_Q1 := deleteVertices S.G V(Q j₁)
          obtain ⟨Q0_ax, hQ0_ax_le, _, hQ0_ax_G⟩ :=
            (hends_Q 0).1.exists_subpath (hends_Q 0).1.left_mem hx₁_Q0
          have hQ0_ax_no : Q0_ax ≤ G_no_Q1 :=
            le_deleteVertices hQ0_ax_G.1 (hdisj_01.mono_left hQ0_ax_le.vertexSet_mono)
          rcases hQ0_ax_G with ⟨_, W_ax, _, _, _⟩
          obtain ⟨W_ax', _, _⟩ := exists_walk_up_of_le hQ0_ax_no W_ax
          have hR₁_no : R₁ ≤ G_no_Q1 :=
            le_deleteVertices (hR₁_ft.1.1.trans (S.reachFromBarMinusGraph_le G₂)) hdisj_R₁_Q1
          rcases (hR₁_ft.1.mono (S.reachFromBarMinusGraph_le G₂)).symm with ⟨_, W_xv, _, _, _⟩
          obtain ⟨W_xv', _, _⟩ := exists_walk_up_of_le hR₁_no W_xv
          have hM₁_no : M₁ ≤ G_no_Q1 := le_deleteVertices hM₁_ft.1.1 hdisj_M₁_Q1
          rcases hM₁_ft.1 with ⟨_, W_vy, _, _, _⟩
          obtain ⟨W_vy', _, _⟩ := exists_walk_up_of_le hM₁_no W_vy
          obtain ⟨Qm_ya, hQm_ya_le, _, hQm_ya_G⟩ :=
            (hends_Q m_last).1.exists_subpath hy₁_Qm (hends_Q m_last).1.left_mem
          have hQm_ya_no : Qm_ya ≤ G_no_Q1 :=
            le_deleteVertices hQm_ya_G.1 (hdisj_1m.symm.mono_left hQm_ya_le.vertexSet_mono)
          rcases hQm_ya_G with ⟨_, W_ya, _, _, _⟩
          obtain ⟨W_ya', _, _⟩ := exists_walk_up_of_le hQm_ya_no W_ya
          let W_cross := (W_ax'.append W_xv').append (W_vy'.append W_ya')
          obtain ⟨P_cross, hP_cross_no, _, _⟩ := exists_isGraphPathWithEnds_of_walk W_cross
          have hdisj_P_Q1 : Disjoint V(P_cross) V(Q j₁) :=
            disjoint_left.mpr fun _ hx => (hP_cross_no.1.vertexSet_mono hx).2
          have ha0_ne_am : a 0 ≠ a m_last := fun h =>
            disjoint_left.mp (S.Ω.disjoint_interval_swap (a j₁) (b j₁)) ha0_j1 (h ▸ ham_b1a1)
          have hP_cross_omega : S.IsOmegaPathWithEnds P_cross (a 0) (a m_last) :=
            ⟨hP_cross_no.mono (deleteVertices_le S.G V(Q j₁)), ha0_ne_am,
              (hends_Q 0).2.2.1, (hends_Q m_last).2.2.1⟩
          have hcr_PQ1 : S.Ω.Crosses (a 0) (a m_last) (a j₁) (b j₁) :=
            (S.Ω.crosses_iff_interval.mpr (Or.inl ⟨ha0_j1, ham_b1a1⟩)).symm
          exact (hsep_Q j₁).2
            ⟨P_cross, hdisj_P_Q1, a 0, a m_last, a j₁, b j₁, hP_cross_omega, hends_Q j₁, hcr_PQ1⟩

/-- If `S₀.Ω` is a one-point extension of `S.Ω` by `r` in `(a₀, b₀)`, `S_K.Ω` is a restriction of
`S.Ω` to `X` containing `a₀, b₀`, and `S₀_K.Ω` is a one-point extension of `S_K.Ω` by `r` in
`(a₀, b₀)`, then any four vertices in `S₀_K.Ω.bar` that cross in `S₀.Ω` also cross in `S₀_K.Ω`. -/
private theorem crosses_of_extension_restriction {S₀ S_K S₀_K : Society α β} {X : Set α}
    {a₀ b₀ r s₁ t₁ s₂ t₂ : α}
    (hbar₀ : S₀.Ω.bar = S.Ω.bar ∪ {r})
    (hrest₀ : S₀.Ω.IsRestriction S.Ω.bar S.Ω)
    (hab_empty : S.Ω.interval a₀ b₀ = ∅)
    (hcw_arb : S₀.Ω.IsClockwise3 a₀ r b₀)
    (hrest_K : S.Ω.IsRestriction X S_K.Ω)
    (ha₀_K : a₀ ∈ S_K.Ω.bar) (hb₀_K : b₀ ∈ S_K.Ω.bar)
    (hbar₀_K : S₀_K.Ω.bar = S_K.Ω.bar ∪ {r})
    (hrest₀_K : S₀_K.Ω.IsRestriction S_K.Ω.bar S_K.Ω)
    (hab_empty_K : S_K.Ω.interval a₀ b₀ = ∅)
    (hcw_arb_K : S₀_K.Ω.IsClockwise3 a₀ r b₀)
    (hs₁ : s₁ ∈ S₀_K.Ω.bar) (ht₁ : t₁ ∈ S₀_K.Ω.bar)
    (hs₂ : s₂ ∈ S₀_K.Ω.bar) (ht₂ : t₂ ∈ S₀_K.Ω.bar)
    (hcr₀ : S₀.Ω.Crosses s₁ t₁ s₂ t₂) :
    S₀_K.Ω.Crosses s₁ t₁ s₂ t₂ := by
  obtain ⟨h₀_ab, h_a0r_empty, h_rb0_empty, _, _⟩ :=
    S.Ω.extension_intervals hbar₀ hrest₀ hab_empty hcw_arb
  obtain ⟨h₀K_ab, _, _, _, _⟩ :=
    S_K.Ω.extension_intervals hbar₀_K hrest₀_K hab_empty_K hcw_arb_K
  have hr_a0b0 : r ∈ S₀.Ω.interval a₀ b₀ := by rw [h₀_ab]; rfl
  have hr_a0b0_K : r ∈ S₀_K.Ω.interval a₀ b₀ := by rw [h₀K_ab]; rfl
  have hK_sub_S : S_K.Ω.bar ⊆ S.Ω.bar := hrest_K.1 ▸ inter_subset_left
  have hr_not_S : r ∉ S.Ω.bar := by
    intro hrS
    have hr_in : r ∈ S.Ω.interval a₀ b₀ := by
      rw [hrest₀.interval_eq (hK_sub_S ha₀_K) (hK_sub_S hb₀_K)]
      exact ⟨hr_a0b0, hrS⟩
    rw [hab_empty] at hr_in
    exact hr_in
  have hr_not_K : r ∉ S_K.Ω.bar := fun h => hr_not_S (hK_sub_S h)
  have h_bar_trans : ∀ {x y z : α},
      x ∈ S_K.Ω.bar → y ∈ S_K.Ω.bar → z ∈ S_K.Ω.bar →
      z ∈ S₀.Ω.interval x y → z ∈ S₀_K.Ω.interval x y := by
    intro x y z hx hy hz hz₀
    have hz_S : z ∈ S.Ω.interval x y := by
      rw [hrest₀.interval_eq (hK_sub_S hx) (hK_sub_S hy)]
      exact ⟨hz₀, hK_sub_S hz⟩
    have hz_K : z ∈ S_K.Ω.interval x y := by
      rw [hrest_K.interval_eq hx hy]
      exact ⟨hz_S, hz⟩
    have h_eq := hrest₀_K.interval_eq hx hy
    rw [h_eq] at hz_K
    exact hz_K.1
  have hr_a0v : ∀ {v : α}, v ∈ S_K.Ω.bar →
      r ∈ S₀.Ω.interval a₀ v → r ∈ S₀_K.Ω.interval a₀ v := by
    intro v hv hrv
    by_cases hvb : v = b₀
    · subst v; exact hr_a0b0_K
    · have hv_ne_r : v ≠ r := fun h => hr_not_K (h ▸ hv)
      have hr_ne_b0 : r ≠ b₀ := (S₀.Ω.isClockwise3_iff.mp hcw_arb).2.2.1
      have hv_0 : v ∈ S₀.Ω.bar := hbar₀ ▸ Or.inl (hK_sub_S hv)
      have hb0_0 : b₀ ∈ S₀.Ω.bar := hbar₀ ▸ Or.inl (hK_sub_S hb₀_K)
      have hr_0 : r ∈ S₀.Ω.bar := hbar₀ ▸ Or.inr rfl
      have hv_b0r : v ∈ S₀.Ω.interval b₀ r := by
        rcases S₀.Ω.mem_interval_or_interval_swap hr_0 hb0_0 hv_0 hr_ne_b0 hv_ne_r hvb with
          h1 | h2
        · rw [h_rb0_empty] at h1; exact h1.elim
        · exact h2
      have hb0_rv : b₀ ∈ S₀.Ω.interval r v := S₀.Ω.mem_interval_rotate_right hv_b0r
      have hb0_a0v : b₀ ∈ S₀.Ω.interval a₀ v :=
        S₀.Ω.interval_subset_interval_right hrv hb0_rv
      have hb0_a0v_K : b₀ ∈ S₀_K.Ω.interval a₀ v := h_bar_trans ha₀_K hv hb₀_K hb0_a0v
      exact S₀_K.Ω.interval_subset_interval_left hb0_a0v_K hr_a0b0_K
  have hr_uv : ∀ {u v : α}, u ∈ S_K.Ω.bar → v ∈ S_K.Ω.bar →
      r ∈ S₀.Ω.interval u v → r ∈ S₀_K.Ω.interval u v := by
    intro u v hu hv hruv
    by_cases hua : u = a₀
    · subst u; exact hr_a0v hv hruv
    · have hu_ne_r : u ≠ r := fun h => hr_not_K (h ▸ hu)
      have ha0_ne_r : a₀ ≠ r := (S₀.Ω.isClockwise3_iff.mp hcw_arb).1
      have hu_0 : u ∈ S₀.Ω.bar := hbar₀ ▸ Or.inl (hK_sub_S hu)
      have ha0_0 : a₀ ∈ S₀.Ω.bar := hbar₀ ▸ Or.inl (hK_sub_S ha₀_K)
      have hr_0 : r ∈ S₀.Ω.bar := hbar₀ ▸ Or.inr rfl
      have hu_ra0 : u ∈ S₀.Ω.interval r a₀ := by
        rcases S₀.Ω.mem_interval_or_interval_swap ha0_0 hr_0 hu_0 ha0_ne_r hua hu_ne_r with
          h1 | h2
        · rw [h_a0r_empty] at h1; exact h1.elim
        · exact h2
      have ha0_ur : a₀ ∈ S₀.Ω.interval u r := S₀.Ω.mem_interval_rotate_left hu_ra0
      have ha0_uv : a₀ ∈ S₀.Ω.interval u v := S₀.Ω.interval_subset_interval_left hruv ha0_ur
      have hr_a0u : r ∈ S₀.Ω.interval a₀ u := S₀.Ω.mem_interval_rotate_right hu_ra0
      have hr_not_ua0 : r ∉ S₀.Ω.interval u a₀ :=
        disjoint_left.mp (S₀.Ω.disjoint_interval_swap a₀ u) hr_a0u
      have hunion := S₀.Ω.interval_eq_union_of_mem ha0_uv
      have hr_a0v₀ : r ∈ S₀.Ω.interval a₀ v := by
        have hruv' : r ∈ S₀.Ω.interval u a₀ ∪ {a₀} ∪ S₀.Ω.interval a₀ v := hunion ▸ hruv
        rcases hruv' with (h1 | h2) | h3
        · exact (hr_not_ua0 h1).elim
        · exact (ha0_ne_r (mem_singleton_iff.mp h2).symm).elim
        · exact h3
      have ha0_uv_K : a₀ ∈ S₀_K.Ω.interval u v := h_bar_trans hu hv ha₀_K ha0_uv
      have hr_a0v_K : r ∈ S₀_K.Ω.interval a₀ v := hr_a0v hv hr_a0v₀
      exact S₀_K.Ω.interval_subset_interval_right ha0_uv_K hr_a0v_K
  have hz_uv : ∀ {u v z : α},
      u ∈ S₀_K.Ω.bar → v ∈ S₀_K.Ω.bar → z ∈ S₀_K.Ω.bar →
      z ∈ S₀.Ω.interval u v → z ∈ S₀_K.Ω.interval u v := by
    intro u v z hu hv hz hz₀
    have hc_iff := S₀.Ω.isClockwise3_iff.mp hz₀.2
    have huz : u ≠ z := hc_iff.1
    have huv : u ≠ v := hc_iff.2.1
    have hzv : z ≠ v := hc_iff.2.2.1
    rcases hbar₀_K ▸ hz with hzK | hzr
    · rcases hbar₀_K ▸ hu with huK | hur
      · rcases hbar₀_K ▸ hv with hvK | hvr
        · exact h_bar_trans huK hvK hzK hz₀
        · rw [mem_singleton_iff] at hvr; subst v
          exact S₀_K.Ω.mem_interval_rotate_right
            (hr_uv hzK huK (S₀.Ω.mem_interval_rotate_left hz₀))
      · rw [mem_singleton_iff] at hur; subst u
        have hvK : v ∈ S_K.Ω.bar := (hbar₀_K ▸ hv).resolve_right (fun h => huv
          (mem_singleton_iff.mp h).symm)
        exact S₀_K.Ω.mem_interval_rotate_left
          (hr_uv hvK hzK (S₀.Ω.mem_interval_rotate_right hz₀))
    · rw [mem_singleton_iff] at hzr; subst z
      have huK : u ∈ S_K.Ω.bar := (hbar₀_K ▸ hu).resolve_right (fun h => huz
        (mem_singleton_iff.mp h))
      have hvK : v ∈ S_K.Ω.bar := (hbar₀_K ▸ hv).resolve_right (fun h => hzv
        (mem_singleton_iff.mp h).symm)
      exact hr_uv huK hvK hz₀
  rcases S₀.Ω.crosses_iff_interval.mp hcr₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact S₀_K.Ω.crosses_iff_interval.mpr
      (Or.inl ⟨hz_uv hs₁ ht₁ hs₂ h1, hz_uv ht₁ hs₁ ht₂ h2⟩)
  · exact S₀_K.Ω.crosses_iff_interval.mpr
      (Or.inr ⟨hz_uv hs₁ ht₁ ht₂ h1, hz_uv ht₁ hs₁ hs₂ h2⟩)

/-- **Graph Minors IX, (5.5), Claim (2)** (pages 54–55):
"(2) *There is a cross in $(K, \Omega_0 \mid V(K))$.*" -/
theorem lemma_5_5_claim_2 {S₀ S_K S₀_K : Society α β} {p : ℕ}
    (hp2 : 2 ≤ p) (hp3 : p ≠ 3)
    {Q : Fin (p + 5) → Graph α β} {a b : Fin (p + 5) → α} {r : α}
    (hinj_Q : Function.Injective Q)
    (htr_Q : S.IsTransaction (range Q))
    (hsep_Q : ∀ i : Fin (p + 5), S.IsSeparatingOmegaPath (Q i))
    (hno_int : ∀ i : Fin (p + 5), Disjoint (pathInternalVerts S.G (Q i)) S.Ω.bar)
    (hends_Q : ∀ i : Fin (p + 5), S.IsOmegaPathWithEnds (Q i) (a i) (b i))
    (hcw : S.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b))
    (hab_empty : S.Ω.interval (a 0) (b 0) = ∅)
    (hr_Q0 : r ∈ V(Q 0) \ {a 0, b 0})
    {G₁ G₂ : Graph α β} (hsep_G : IsGraphSeparation S.G G₁ G₂)
    (hinter_G : V(G₁) ∩ V(G₂) = V(Q ⟨p + 4, by omega⟩))
    (hint_G₁ : S.Ω.interval (a ⟨p + 4, by omega⟩) (b ⟨p + 4, by omega⟩) ⊆ V(G₁))
    (hint_G₂ : S.Ω.interval (b ⟨p + 4, by omega⟩) (a ⟨p + 4, by omega⟩) ⊆ V(G₂))
    (hG₀ : S₀.G = S.G)
    (hbar₀ : S₀.Ω.bar = S.Ω.bar ∪ {r})
    (hrest₀ : S₀.Ω.IsRestriction S.Ω.bar S.Ω)
    (hcw_arb : S₀.Ω.IsClockwise3 (a 0) r (b 0))
    (hex_cr₀ : ∃ P₀ : Set (Graph α β), S₀.IsCrookedTransaction P₀ ∧ p ≤ P₀.ncard)
    (hno_cr : ∀ P_set : Set (Graph α β), S.IsCrookedTransaction P_set → P_set.ncard ≠ p)
    (hGK : S_K.G = S.reachFromBarMinusGraph G₂)
    (hrest_K : S.Ω.IsRestriction V(S_K.G) S_K.Ω)
    (hG₀_K : S₀_K.G = S_K.G)
    (hbar₀_K : S₀_K.Ω.bar = S_K.Ω.bar ∪ {r})
    (hrest₀_K : S₀_K.Ω.IsRestriction S_K.Ω.bar S_K.Ω)
    (hcw_arb_K : S₀_K.Ω.IsClockwise3 (a 0) r (b 0)) :
    ∃ P₁ P₂ : Graph α β, S₀_K.IsCross P₁ P₂ := by
  have : Finite V(S.G) := S.finite_V
  have : Finite E(S.G) := S.finite_E
  obtain ⟨P₁, P₂, hcr₁₂₀, hd₁, hd₂⟩ :
      ∃ P₁ P₂ : Graph α β, S₀.OmegaPathsCross P₁ P₂ ∧
        Disjoint V(P₁) V(G₂) ∧ Disjoint V(P₂) V(G₂) := by
    rcases S.lemma_5_5_claim_2_disjoint hp2 hp3 hex_cr₀ hG₀ hbar₀ hrest₀ hab_empty hcw_arb hr_Q0
        hinj_Q htr_Q hsep_Q hno_int hends_Q hcw hsep_G hinter_G hint_G₁ hint_G₂ with
      h1 | ⟨P_set, hcr_P, hcard_P, _⟩
    · exact h1
    · exact (hno_cr P_set hcr_P hcard_P).elim
  let m_last : Fin (p + 5) := ⟨p + 4, by omega⟩
  have hdisj_Q : Pairwise (fun i j : Fin (p + 5) => Disjoint V(Q i) V(Q j)) := by
    rcases htr_Q with ⟨_, _, hfence_Q⟩
    intro i j hij
    exact hfence_Q.1.2 (mem_range_self i) (mem_range_self j) (fun h => hij (hinj_Q h))
  have h0_lt_m : (0 : Fin (p + 5)) < m_last := by change (0 : ℕ) < p + 4; omega
  obtain ⟨ha0_mlast, hb0_mlast, _, _, _⟩ :=
    S.Ω.mem_intervals_of_isClockwiseSeq_ofFn hcw h0_lt_m
  have hdisj_Q0_G₂ : Disjoint V(Q 0) V(G₂) :=
    S.disjoint_right_of_ends_in_interval_of_separating
      (hends_Q m_last) (hsep_Q m_last) (hends_Q m_last) (hno_int m_last)
      Subset.rfl (Or.inl rfl) hsep_G hinter_G hint_G₁ (hends_Q 0)
      (hdisj_Q (ne_of_lt h0_lt_m)) ha0_mlast hb0_mlast
  have ha0_not_G₂ : a 0 ∉ V(G₂) := disjoint_left.mp hdisj_Q0_G₂ (hends_Q 0).1.left_mem
  have hb0_not_G₂ : b 0 ∉ V(G₂) := disjoint_left.mp hdisj_Q0_G₂ (hends_Q 0).1.right_mem
  have ha0_K_set : a 0 ∈ S.reachFromBarMinusSet G₂ :=
    S.bar_diff_subset_reachFromBarMinusSet G₂ ⟨(hends_Q 0).2.2.1, ha0_not_G₂⟩
  have hb0_K_set : b 0 ∈ S.reachFromBarMinusSet G₂ :=
    S.bar_diff_subset_reachFromBarMinusSet G₂ ⟨(hends_Q 0).2.2.2, hb0_not_G₂⟩
  have hQ0_K : Q 0 ≤ S_K.G :=
    hGK ▸ S.le_reachFromBarMinusGraph_of_isGraphPathWithEnds (hends_Q 0).1 hdisj_Q0_G₂ ha0_K_set
  have ha0_bar_K : a 0 ∈ S_K.Ω.bar := by
    rw [hrest_K.1, hGK]
    exact ⟨(hends_Q 0).2.2.1, ha0_K_set⟩
  have hb0_bar_K : b 0 ∈ S_K.Ω.bar := by
    rw [hrest_K.1, hGK]
    exact ⟨(hends_Q 0).2.2.2, hb0_K_set⟩
  have hab_empty_K : S_K.Ω.interval (a 0) (b 0) = ∅ := by
    rw [hrest_K.interval_eq ha0_bar_K hb0_bar_K, hab_empty, empty_inter]
  have hr_K : r ∈ V(S.reachFromBarMinusGraph G₂) :=
    (hGK ▸ hQ0_K).vertexSet_mono hr_Q0.1
  have hP_in_0K : ∀ {P : Graph α β} {s t : α},
      S₀.IsOmegaPathWithEnds P s t → Disjoint V(P) V(G₂) →
      S₀_K.IsOmegaPathWithEnds P s t := by
    intro P s t hP₀ hdP
    have hP_G : IsGraphPathWithEnds S.G P s t := hG₀ ▸ hP₀.1
    have h_end_0K : ∀ {u : α}, u ∈ S₀.Ω.bar → u ∈ V(P) →
        u ∈ S₀_K.Ω.bar ∧ u ∈ S.reachFromBarMinusSet G₂ := by
      intro u hu₀ huP
      have hu_not_G₂ : u ∉ V(G₂) := disjoint_left.mp hdP huP
      rcases hbar₀ ▸ hu₀ with huS | hur
      · have huK : u ∈ S.reachFromBarMinusSet G₂ :=
          S.bar_diff_subset_reachFromBarMinusSet G₂ ⟨huS, hu_not_G₂⟩
        have hu_bar_K : u ∈ S_K.Ω.bar := by
          rw [hrest_K.1, hGK]; exact ⟨huS, huK⟩
        exact ⟨hbar₀_K ▸ Or.inl hu_bar_K, huK⟩
      · rw [mem_singleton_iff] at hur; subst u
        exact ⟨hbar₀_K ▸ Or.inr rfl, hr_K⟩
    have hs_0K := h_end_0K hP₀.2.2.1 hP_G.left_mem
    have ht_0K := h_end_0K hP₀.2.2.2 hP_G.right_mem
    have hP_K : P ≤ S_K.G :=
      hGK ▸ S.le_reachFromBarMinusGraph_of_isGraphPathWithEnds hP_G hdP hs_0K.2
    exact ⟨hG₀_K ▸ hP_G.of_le hP_K, hP₀.2.1, hs_0K.1, ht_0K.1⟩
  rcases hcr₁₂₀ with ⟨hdisj_12, s₁, t₁, s₂, t₂, hP₁₀, hP₂₀, hcr_st₀⟩
  have hP₁_0K := hP_in_0K hP₁₀ hd₁
  have hP₂_0K := hP_in_0K hP₂₀ hd₂
  have hcr_st_0K : S₀_K.Ω.Crosses s₁ t₁ s₂ t₂ :=
    S.crosses_of_extension_restriction hbar₀ hrest₀ hab_empty hcw_arb
      hrest_K ha0_bar_K hb0_bar_K hbar₀_K hrest₀_K hab_empty_K hcw_arb_K
      hP₁_0K.2.2.1 hP₁_0K.2.2.2 hP₂_0K.2.2.1 hP₂_0K.2.2.2 hcr_st₀
  exact ⟨P₁, P₂, hdisj_12, s₁, t₁, s₂, t₂, hP₁_0K, hP₂_0K, hcr_st_0K⟩

/-- **Graph Minors IX, (5.5)** (pages 54–55):
"Let $(G, \Omega)$ be internally 4-connected and let $p \ge 2$ with $p \ne 3$. Let $\{Q_1,
\dots, Q_{p+5}\}$ be a transaction such that for $1 \le i \le p+5$, $Q_i$ is separating, has
no internal vertex in $\bar{\Omega}$, and has ends $a_i, b_i$, where $(a_{p+5}, a_{p+4},
\dots, a_1, b_1, b_2, \dots, b_{p+5})$ is clockwise. Let $\Omega(a_1, b_1) = \emptyset$, and
let $r \in V(Q_1) - \{a_1, b_1\}$. Let $(G_1, G_2)$ be a separation of $G$ with $V(G_1 \cap
G_2) = V(Q_{p+5})$, $\Omega(a_{p+5}, b_{p+5}) \subseteq V(G_1)$, and $\Omega(b_{p+5},
a_{p+5}) \subseteq V(G_2)$. Let $\Omega_0$ be the cyclic permutation with $\bar{\Omega}_0 =
\bar{\Omega} \cup \{r\}$ and $\Omega_0 \mid \bar{\Omega} = \Omega$, such that $(a_1, r,
b_1)$ is $\Omega_0$-clockwise. Suppose that $Q_1$ is induced, that $\bar{\Omega} - \{a_1,
b_1\}$ catches $G \setminus V(Q_1)$, that $(G, \Omega_0)$ has a crooked transaction of
cardinality $p$ and that $(G, \Omega)$ has no crooked transaction of cardinality $p$. Then
there is a non-separating $\Omega$-path $P$ of $(G, \Omega)$ with $P \subseteq G_1$." -/
theorem theorem_5_5_proof {S₀ : Society α β} {p : ℕ}
    (hconn : S.IsInternallyKConnected 4)
    (hp2 : 2 ≤ p) (hp3 : p ≠ 3)
    {Q : Fin (p + 5) → Graph α β} {a b : Fin (p + 5) → α} {r : α}
    (hinj_Q : Function.Injective Q)
    (htr_Q : S.IsTransaction (range Q))
    (hsep_Q : ∀ i : Fin (p + 5), S.IsSeparatingOmegaPath (Q i))
    (hno_int : ∀ i : Fin (p + 5), Disjoint (pathInternalVerts S.G (Q i)) S.Ω.bar)
    (hends_Q : ∀ i : Fin (p + 5), S.IsOmegaPathWithEnds (Q i) (a i) (b i))
    (hcw : S.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b))
    (hab_empty : S.Ω.interval (a 0) (b 0) = ∅)
    (hr_Q0 : r ∈ V(Q 0) \ {a 0, b 0})
    {G₁ G₂ : Graph α β} (hsep_G : IsGraphSeparation S.G G₁ G₂)
    (hinter_G : V(G₁) ∩ V(G₂) = V(Q ⟨p + 4, by omega⟩))
    (hQm_G₁ : Q ⟨p + 4, by omega⟩ ≤ G₁)
    (hint_G₁ : S.Ω.interval (a ⟨p + 4, by omega⟩) (b ⟨p + 4, by omega⟩) ⊆ V(G₁))
    (hint_G₂ : S.Ω.interval (b ⟨p + 4, by omega⟩) (a ⟨p + 4, by omega⟩) ⊆ V(G₂))
    (hG₀ : S₀.G = S.G)
    (hbar₀ : S₀.Ω.bar = S.Ω.bar ∪ {r})
    (hrest₀ : S₀.Ω.IsRestriction S.Ω.bar S.Ω)
    (hcw_arb : S₀.Ω.IsClockwise3 (a 0) r (b 0))
    (hQ0_ind : S.G.induce V(Q 0) = Q 0)
    (hcatches : Catches (S.Ω.bar \ {a 0, b 0}) (deleteVertices S.G V(Q 0)))
    (hex_cr₀ : ∃ P₀ : Set (Graph α β), S₀.IsCrookedTransaction P₀ ∧ p ≤ P₀.ncard)
    (hno_cr : ∀ P_set : Set (Graph α β), S.IsCrookedTransaction P_set → P_set.ncard ≠ p) :
    (∃ P₁ P₂ : Graph α β, P₁ ≤ G₁ ∧ P₂ ≤ G₁ ∧ S.IsCross P₁ P₂) ∧
    (∃ P : Graph α β, S.IsNonSeparatingOmegaPath P ∧ P ≤ G₁) := by
  have : Finite V(S.G) := S.finite_V
  have : Finite E(S.G) := S.finite_E
  -- Suffices to find a cross `M₁, M₂ ≤ G₁` in `S`.
  suffices h_cross_G₁ : ∃ M₁ M₂ : Graph α β, M₁ ≤ G₁ ∧ M₂ ≤ G₁ ∧ S.IsCross M₁ M₂ by
    refine ⟨h_cross_G₁, ?_⟩
    rcases h_cross_G₁ with ⟨M₁, M₂, _, hM₂_G₁, hcr_M⟩
    rcases hcr_M.2 with ⟨_, _, s₂, t₂, _, hM₂_ends, _⟩
    exact ⟨M₂, ⟨⟨s₂, t₂, hM₂_ends⟩, M₁, hcr_M⟩, hM₂_G₁⟩
  -- Define `G'`, `K`, `S'`, `S_K`, and `S₁`.
  let m_last : Fin (p + 5) := ⟨p + 4, by omega⟩
  let G' := deleteVertices S.G V(G₂)
  let K := S.reachFromBarMinusGraph G₂
  obtain ⟨Ω', hrest'⟩ := S.Ω.exists_isRestriction V(G')
  have hrest_K : S.Ω.IsRestriction V(K) Ω' :=
    ⟨hrest'.1.trans (S.bar_inter_reachFromBarMinusGraph G₂).symm, hrest'.2⟩
  let S' : Society α β :=
    { G := G'
      Ω := Ω'
      finite_V := S.finite_V.subset (deleteVertices_le S.G V(G₂)).vertexSet_mono
      finite_E := S.finite_E.subset (deleteVertices_le S.G V(G₂)).edgeSet_mono
      bar_subset := hrest'.1 ▸ inter_subset_right }
  let S_K : Society α β :=
    { G := K
      Ω := Ω'
      finite_V := S.finite_V.subset (S.reachFromBarMinusGraph_le G₂).vertexSet_mono
      finite_E := S.finite_E.subset (S.reachFromBarMinusGraph_le G₂).edgeSet_mono
      bar_subset := hrest_K.1 ▸ inter_subset_right }
  obtain ⟨Ω₁, hrest₁⟩ := S.Ω.exists_isRestriction V(G₁)
  let S₁ : Society α β :=
    { G := G₁
      Ω := Ω₁
      finite_V := S.finite_V.subset hsep_G.1.vertexSet_mono
      finite_E := S.finite_E.subset hsep_G.1.edgeSet_mono
      bar_subset := hrest₁.1 ▸ inter_subset_right }
  have hdisj_Q : Pairwise (fun i j : Fin (p + 5) => Disjoint V(Q i) V(Q j)) := by
    rcases htr_Q with ⟨_, _, hfence_Q⟩
    intro i j hij
    exact hfence_Q.1.2 (mem_range_self i) (mem_range_self j) (fun h => hij (hinj_Q h))
  -- Show `Q 0 ≤ K` and `a 0, b 0 ∈ S_K.Ω.bar`.
  have h0_lt_m : (0 : Fin (p + 5)) < m_last := by change (0 : ℕ) < p + 4; omega
  obtain ⟨ha0_mlast, hb0_mlast, _, _, _⟩ :=
    S.Ω.mem_intervals_of_isClockwiseSeq_ofFn hcw h0_lt_m
  have hdisj_Q0_G₂ : Disjoint V(Q 0) V(G₂) :=
    S.disjoint_right_of_ends_in_interval_of_separating
      (hends_Q m_last) (hsep_Q m_last) (hends_Q m_last) (hno_int m_last)
      Subset.rfl (Or.inl rfl) hsep_G hinter_G hint_G₁ (hends_Q 0)
      (hdisj_Q (ne_of_lt h0_lt_m)) ha0_mlast hb0_mlast
  have ha0_not_G₂ : a 0 ∉ V(G₂) := disjoint_left.mp hdisj_Q0_G₂ (hends_Q 0).1.left_mem
  have hb0_not_G₂ : b 0 ∉ V(G₂) := disjoint_left.mp hdisj_Q0_G₂ (hends_Q 0).1.right_mem
  have ha0_K_set : a 0 ∈ S.reachFromBarMinusSet G₂ :=
    S.bar_diff_subset_reachFromBarMinusSet G₂ ⟨(hends_Q 0).2.2.1, ha0_not_G₂⟩
  have hb0_K_set : b 0 ∈ S.reachFromBarMinusSet G₂ :=
    S.bar_diff_subset_reachFromBarMinusSet G₂ ⟨(hends_Q 0).2.2.2, hb0_not_G₂⟩
  have hQ0_K : Q 0 ≤ K :=
    S.le_reachFromBarMinusGraph_of_isGraphPathWithEnds (hends_Q 0).1 hdisj_Q0_G₂ ha0_K_set
  have ha0_bar_K : a 0 ∈ S_K.Ω.bar := by
    change a 0 ∈ Ω'.bar
    rw [hrest_K.1]
    exact ⟨(hends_Q 0).2.2.1, ha0_K_set⟩
  have hb0_bar_K : b 0 ∈ S_K.Ω.bar := by
    change b 0 ∈ Ω'.bar
    rw [hrest_K.1]
    exact ⟨(hends_Q 0).2.2.2, hb0_K_set⟩
  have hab_empty_K : S_K.Ω.interval (a 0) (b 0) = ∅ := by
    rw [hrest_K.interval_eq ha0_bar_K hb0_bar_K, hab_empty, empty_inter]
  have hr_K : r ∈ V(K) := hQ0_K.vertexSet_mono hr_Q0.1
  have hr_not_S : r ∉ S.Ω.bar := by
    have hr_int : r ∈ pathInternalVerts S.G (Q 0) := by
      rw [(hends_Q 0).1.pathInternalVerts_eq]
      exact hr_Q0
    exact disjoint_left.mp (hno_int 0) hr_int
  have hr_not_bar_K : r ∉ S_K.Ω.bar := by
    intro hrK
    have hrS : r ∈ S.Ω.bar := (hrest_K.1 ▸ hrK).1
    exact hr_not_S hrS
  -- Construct `S₀_K` extending `S_K` by `r` in `(a 0, b 0)`.
  obtain ⟨S₀_K, hG₀_K, hbar₀_K, hrest₀_K, hcw_arb_K⟩ :=
    S_K.exists_society_extension ha0_bar_K hb0_bar_K (hends_Q 0).2.1 hab_empty_K hr_K hr_not_bar_K
  -- By Claim (2), there is a cross in `S₀_K`.
  have hcross_0K : ∃ P₁ P₂ : Graph α β, S₀_K.IsCross P₁ P₂ :=
    S.lemma_5_5_claim_2 hp2 hp3 hinj_Q htr_Q hsep_Q hno_int hends_Q hcw hab_empty hr_Q0
      hsep_G hinter_G hint_G₁ hint_G₂ hG₀ hbar₀ hrest₀ hcw_arb hex_cr₀ hno_cr
      rfl hrest_K hG₀_K hbar₀_K hrest₀_K hcw_arb_K
  -- Check remaining hypotheses of `S_K.theorem_5_3_proof`.
  have hQ0_ends_K : S_K.IsOmegaPathWithEnds (Q 0) (a 0) (b 0) :=
    ⟨(hends_Q 0).1.of_le hQ0_K, (hends_Q 0).2.1, ha0_bar_K, hb0_bar_K⟩
  have hQ0_ind_K : S_K.G.induce V(Q 0) = Q 0 := by
    have hK_le_G : S_K.G ≤ S.G := S.reachFromBarMinusGraph_le G₂
    refine (Compatible.of_le_le (S_K.G.induce_le hQ0_K.vertexSet_mono) hQ0_K).ext rfl ?_
    ext e
    simp only [edgeSet_induce, mem_ofPred_eq]
    refine ⟨fun ⟨x, y, hxy, hx, hy⟩ => ?_, fun he => ?_⟩
    · have hxy_G : (S.G.induce V(Q 0)).IsLink e x y := by
        rw [S.G.induce_isLink V(Q 0)]
        exact ⟨hxy.mono hK_le_G, hx, hy⟩
      rw [hQ0_ind] at hxy_G
      exact hxy_G.edge_mem
    · obtain ⟨x, y, hxy⟩ := (Q 0).exists_isLink_of_mem_edgeSet he
      exact ⟨x, y, hxy.mono hQ0_K, hxy.left_mem, hxy.right_mem⟩
  have hcatches_K : Catches (S_K.Ω.bar \ {a 0, b 0}) (deleteVertices S_K.G V(Q 0)) := by
    have hbar_K_eq : S_K.Ω.bar = S.Ω.bar \ V(G₂) := by
      change Ω'.bar = S.Ω.bar \ V(G₂)
      rw [hrest'.1]
      ext z
      simp only [mem_inter_iff, mem_sdiff]
      exact ⟨fun ⟨hz₁, _, hz₂⟩ => ⟨hz₁, hz₂⟩,
        fun ⟨hz₁, hz₂⟩ => ⟨hz₁, S.bar_subset hz₁, hz₂⟩⟩
    rw [hbar_K_eq]
    exact S.lemma_5_5_claim_3 hp2 hinj_Q htr_Q hsep_Q hno_int hends_Q hcw
      hcatches hsep_G hinter_G hint_G₁
  have hno_int_K : Disjoint (pathInternalVerts S_K.G (Q 0)) S_K.Ω.bar := by
    rw [hQ0_ends_K.1.pathInternalVerts_eq, ← (hends_Q 0).1.pathInternalVerts_eq]
    exact (hno_int 0).mono_right (hrest_K.1 ▸ inter_subset_left)
  -- Apply `S_K.theorem_5_3_proof`.
  have hG'_eq : deleteVertices S.G V(G₂) = deleteVertices G₁ V(Q m_last) :=
    deleteVertices_eq_of_isGraphSeparation hsep_G hinter_G
  have hK_le_G₁ : K ≤ G₁ :=
    (S.reachFromBarMinusGraph_le_deleteVertices G₂).trans
      (hG'_eq ▸ deleteVertices_le G₁ V(Q m_last))
  have : Finite V(S_K.G) := S_K.finite_V
  have : Finite E(S_K.G) := S_K.finite_E
  rcases S_K.theorem_5_3_proof hG₀_K hQ0_ends_K hQ0_ind_K hab_empty_K hcatches_K hno_int_K
      hr_Q0 hbar₀_K hrest₀_K hcw_arb_K hcross_0K with
    ⟨M₁, M₂, hdisj_M, u₁, v₁, u₂, v₂, hM₁_K, hM₂_K, hcr_M_K⟩ | ⟨N₁, N₂, N₃, htri_K⟩
  · -- `S_K` has a cross `{M₁, M₂}`.
    have hM₁_G₁ : M₁ ≤ G₁ := hM₁_K.1.1.trans hK_le_G₁
    have hM₂_G₁ : M₂ ≤ G₁ := hM₂_K.1.1.trans hK_le_G₁
    have hM₁_S : S.IsOmegaPathWithEnds M₁ u₁ v₁ :=
      ⟨hM₁_K.1.mono (S.reachFromBarMinusGraph_le G₂), hM₁_K.2.1,
        (hrest_K.1 ▸ hM₁_K.2.2.1).1, (hrest_K.1 ▸ hM₁_K.2.2.2).1⟩
    have hM₂_S : S.IsOmegaPathWithEnds M₂ u₂ v₂ :=
      ⟨hM₂_K.1.mono (S.reachFromBarMinusGraph_le G₂), hM₂_K.2.1,
        (hrest_K.1 ▸ hM₂_K.2.2.1).1, (hrest_K.1 ▸ hM₂_K.2.2.2).1⟩
    have hcr_M_S : S.Ω.Crosses u₁ v₁ u₂ v₂ :=
      (hrest_K.crosses_iff.mp hcr_M_K).2.2.2.2
    exact ⟨M₁, M₂, hM₁_G₁, hM₂_G₁, hdisj_M, u₁, v₁, u₂, v₂, hM₁_S, hM₂_S, hcr_M_S⟩
  · -- `S_K` has a tripod `{N₁, N₂, N₃}`; lift it to `S'` and apply `S.theorem_5_4_proof`.
    have hK_le_G' : K ≤ G' := S.reachFromBarMinusGraph_le_deleteVertices G₂
    have htri' : S'.IsTripod N₁ N₂ N₃ := by
      rcases htri_K with ⟨u, v, huv, hN₁, hN₂, hN₃, h12, h13, h23,
        s₁, hs₁, s₂, hs₂, s₃, hs₃, t₁, ht₁, t₂, ht₂, t₃, ht₃,
        hX_sub, hY_sub, hcard_XY, P_r, hdisj_Pr, hPr_ft⟩
      refine ⟨u, v, huv, hN₁.mono hK_le_G', hN₂.mono hK_le_G', hN₃.mono hK_le_G',
        h12, h13, h23, s₁, hs₁, s₂, hs₂, s₃, hs₃, t₁, ht₁, t₂, ht₂, t₃, ht₃,
        hX_sub, hY_sub, hcard_XY, P_r, hdisj_Pr, fun i => ?_⟩
      obtain ⟨x, hx, y, hy, hft⟩ := hPr_ft i
      exact ⟨x, hx, y, hy, hft.1.mono hK_le_G', hft.2.1, hft.2.2⟩
    obtain ⟨M₁, M₂, hdisj_M, u₁, v₁, u₂, v₂, hM₁_1, hM₂_1, hcr_M_1⟩ :=
      S.theorem_5_4_proof hconn (hends_Q m_last) (hsep_Q m_last) (hno_int m_last)
        hsep_G hinter_G hQm_G₁ hint_G₁ hint_G₂
        (rfl : S'.G = _) hrest' (rfl : S₁.G = _) hrest₁ ⟨N₁, N₂, N₃, htri'⟩
    have hM₁_S : S.IsOmegaPathWithEnds M₁ u₁ v₁ :=
      ⟨hM₁_1.1.mono hsep_G.1, hM₁_1.2.1,
        (hrest₁.1 ▸ hM₁_1.2.2.1).1, (hrest₁.1 ▸ hM₁_1.2.2.2).1⟩
    have hM₂_S : S.IsOmegaPathWithEnds M₂ u₂ v₂ :=
      ⟨hM₂_1.1.mono hsep_G.1, hM₂_1.2.1,
        (hrest₁.1 ▸ hM₂_1.2.2.1).1, (hrest₁.1 ▸ hM₂_1.2.2.2).1⟩
    have hcr_M_S : S.Ω.Crosses u₁ v₁ u₂ v₂ :=
      (hrest₁.crosses_iff.mp hcr_M_1).2.2.2.2
    exact ⟨M₁, M₂, hM₁_1.1.1, hM₂_1.1.1, hdisj_M, u₁, v₁, u₂, v₂, hM₁_S, hM₂_S, hcr_M_S⟩

end Society

export Society (theorem_5_3_proof theorem_5_4_proof theorem_5_5_proof)

end GraphMinor.GM09
