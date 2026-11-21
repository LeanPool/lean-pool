/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.Linarith

/-!
# Splitting a family of small pieces evenly for two measures

Let `I` be a finite family of pieces carrying two nonnegative measures `x` and `y`, every piece
having `x`-measure at most `ε` and `y`-measure at most `η`. Then the family can be split into two
subfamilies `J` and `I \ J` such that `x(J)` differs from half of `x(I)` by at most `ε`, and the
`y`-measures of both subfamilies are at most `c`, as soon as `η + y(I) ≤ 2c`
(`PlanarSeparator.exists_balanced_split`).

The proof is a discrete intermediate value argument. Start from a subfamily `J₁` maximal (in
size) with `x(J₁) ≤ x(I)/2` and its complement `J₂`. If one of them, say `J₁`, has too large
`y`-measure, move from `J₁` to `J₂` one piece at a time, adding a piece of `J₂` while the
`x`-measure is below half of the total, and removing a piece of `J₁` otherwise. The
`x`-measure stays within `ε` of half the total, and the `y`-measure decreases by at most `η` at
each step and ends below `y(I) - c`; at the first time it is at most `c`, it is at least
`c - η ≥ y(I) - c`, so both subfamilies have `y`-measure at most `c`.
-/

@[expose] public section

namespace PlanarSeparator

open Finset

variable {ι : Type*} [DecidableEq ι] (x y : ι → ℝ)

/-- The walk from one subfamily to a disjoint one. -/
theorem exists_balanced_walk {S₁ S₂ : Finset ι} (hdisj : Disjoint S₁ S₂) {X Y ε η c : ℝ}
    (hxε : ∀ i ∈ S₁ ∪ S₂, x i ≤ ε) (hyη : ∀ i ∈ S₁, y i ≤ η) (hy : ∀ i, 0 ≤ y i)
    (hx : ∀ i, 0 ≤ x i) (hη : 0 ≤ η) (hc : η + Y ≤ 2 * c) (hS₂x : X / 2 - ε ≤ ∑ i ∈ S₂, x i)
    (hS₂y : ∑ i ∈ S₂, y i < Y - c) :
    ∀ n, ∀ R A : Finset ι, R ⊆ S₁ → A ⊆ S₂ → #R + #(S₂ \ A) = n →
      X / 2 - ε ≤ ∑ i ∈ R ∪ A, x i → ∑ i ∈ R ∪ A, x i ≤ X / 2 + ε →
      c < ∑ i ∈ R ∪ A, y i →
      ∃ K ⊆ S₁ ∪ S₂, X / 2 - ε ≤ ∑ i ∈ K, x i ∧ ∑ i ∈ K, x i ≤ X / 2 + ε ∧
        Y - c ≤ ∑ i ∈ K, y i ∧ ∑ i ∈ K, y i ≤ c := by
  intro n
  induction n with
  | zero =>
    intro R A hR hA hn _ _ hy'
    have hR0 : R = ∅ := card_eq_zero.1 (by omega)
    subst hR0
    rw [empty_union] at hy'
    have : ∑ i ∈ A, y i ≤ ∑ i ∈ S₂, y i := sum_le_sum_of_subset_of_nonneg hA fun i _ _ => hy i
    linarith
  | succ n ih =>
    intro R A hR hA hn hx1 hx2 hy'
    have hRA : Disjoint R A := disjoint_of_subset_left hR (disjoint_of_subset_right hA hdisj)
    by_cases hR0 : R = ∅
    · subst hR0
      rw [empty_union] at hy'
      have : ∑ i ∈ A, y i ≤ ∑ i ∈ S₂, y i :=
        sum_le_sum_of_subset_of_nonneg hA fun i _ _ => hy i
      linarith
    by_cases hstep : ∑ i ∈ R ∪ A, x i < X / 2 ∧ (S₂ \ A).Nonempty
    · -- add a piece of `S₂`
      obtain ⟨hlt, q, hq⟩ := hstep
      obtain ⟨hq2, hqA⟩ := mem_sdiff.1 hq
      have hqR : q ∉ R := fun h => disjoint_left.1 hdisj (hR h) hq2
      have hqRA : q ∉ R ∪ A := by simp [hqR, hqA]
      have e : R ∪ insert q A = insert q (R ∪ A) := by
        ext i; simp only [mem_union, mem_insert]; tauto
      have hcard : #(S₂ \ insert q A) + 1 = #(S₂ \ A) := by
        rw [sdiff_insert, card_erase_of_mem hq]
        have := card_pos.2 ⟨q, hq⟩
        omega
      have hxq := hxε q (mem_union_right _ hq2)
      refine ih R (insert q A) hR (insert_subset hq2 hA) (by omega) ?_ ?_ ?_
      · rw [e, sum_insert hqRA]
        linarith [hx q]
      · rw [e, sum_insert hqRA]
        linarith
      · rw [e, sum_insert hqRA]
        linarith [hy q]
    · -- remove a piece of `S₁`
      obtain ⟨p, hp⟩ := nonempty_iff_ne_empty.2 hR0
      have hpA : p ∉ A := fun h => disjoint_left.1 hRA hp h
      have e : R.erase p ∪ A = (R ∪ A).erase p := by
        ext i
        by_cases hi : i = p
        · subst hi
          simp [hpA]
        · simp [hi]
      have hpRA : p ∈ R ∪ A := mem_union_left _ hp
      have hsx := sum_erase_add (R ∪ A) x hpRA
      have hsy := sum_erase_add (R ∪ A) y hpRA
      have hxp := hxε p (mem_union_left _ (hR hp))
      have hyp := hyη p (hR hp)
      have hx1' : X / 2 - ε ≤ ∑ i ∈ R.erase p ∪ A, x i := by
        rw [e]
        rw [not_and_or, not_lt, not_nonempty_iff_eq_empty] at hstep
        rcases hstep with h | h
        · linarith
        · have hAS : A = S₂ := by
            rw [sdiff_eq_empty_iff_subset] at h
            exact Subset.antisymm hA h
          rw [← e, hAS]
          have : ∑ i ∈ S₂, x i ≤ ∑ i ∈ R.erase p ∪ S₂, x i :=
            sum_le_sum_of_subset_of_nonneg subset_union_right fun i _ _ => hx i
          linarith
      have hx2' : ∑ i ∈ R.erase p ∪ A, x i ≤ X / 2 + ε := by
        rw [e]; linarith [hx p]
      by_cases hfin : ∑ i ∈ R.erase p ∪ A, y i ≤ c
      · refine ⟨R.erase p ∪ A, union_subset_union ((erase_subset _ _).trans hR) hA, hx1', hx2',
          ?_, hfin⟩
        rw [e]
        linarith
      · refine ih (R.erase p) A ((erase_subset _ _).trans hR) hA ?_ hx1' hx2' (not_le.1 hfin)
        rw [card_erase_of_mem hp]
        have := card_pos.2 ⟨p, hp⟩
        omega

/-- **Splitting small pieces evenly for two measures.** If every piece has `x`-measure at most
`ε` and `y`-measure at most `η`, and `η + y(I) ≤ 2c`, then there is a subfamily `J` with
`|x(J) - x(I)/2| ≤ ε` such that `J` and its complement both have `y`-measure at most `c`. -/
theorem exists_balanced_split (I : Finset ι) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    {ε η c : ℝ} (hε : 0 ≤ ε) (hxε : ∀ i ∈ I, x i ≤ ε) (hyη : ∀ i ∈ I, y i ≤ η) (hη : 0 ≤ η)
    (hc : η + ∑ i ∈ I, y i ≤ 2 * c) :
    ∃ J ⊆ I, (∑ i ∈ I, x i) / 2 - ε ≤ ∑ i ∈ J, x i ∧ ∑ i ∈ J, x i ≤ (∑ i ∈ I, x i) / 2 + ε ∧
      ∑ i ∈ J, y i ≤ c ∧ ∑ i ∈ I \ J, y i ≤ c := by
  set X := ∑ i ∈ I, x i
  set Y := ∑ i ∈ I, y i
  -- a subfamily of maximal size with at most half of the `x`-measure
  set F := I.powerset.filter fun J => ∑ i ∈ J, x i ≤ X / 2
  have hX0 : 0 ≤ X := sum_nonneg fun i _ => hx i
  have hF : F.Nonempty := ⟨∅, by simp [F]; linarith⟩
  obtain ⟨J₁, hJ₁, hmax⟩ := exists_max_image F card hF
  obtain ⟨hJ₁I, hJ₁x⟩ := mem_filter.1 hJ₁
  rw [mem_powerset] at hJ₁I
  have hJ₁x' : X / 2 - ε ≤ ∑ i ∈ J₁, x i := by
    by_contra h
    push Not at h
    by_cases hJI : J₁ = I
    · rw [hJI] at h
      linarith
    obtain ⟨i, hiI, hiJ⟩ : ∃ i ∈ I, i ∉ J₁ := by
      by_contra h'
      push Not at h'
      exact hJI (Subset.antisymm hJ₁I h')
    have hmem : insert i J₁ ∈ F := by
      refine mem_filter.2 ⟨mem_powerset.2 (insert_subset hiI hJ₁I), ?_⟩
      rw [sum_insert hiJ]
      linarith [hxε i hiI]
    have := hmax _ hmem
    rw [card_insert_of_notMem hiJ] at this
    omega
  set J₂ := I \ J₁
  have hdisj : Disjoint J₁ J₂ := disjoint_sdiff
  have hunion : J₁ ∪ J₂ = I := union_sdiff_of_subset hJ₁I
  have hsx : ∑ i ∈ J₂, x i + ∑ i ∈ J₁, x i = X := sum_sdiff hJ₁I
  have hsy : ∑ i ∈ J₂, y i + ∑ i ∈ J₁, y i = Y := sum_sdiff hJ₁I
  have hxεU : ∀ i ∈ J₁ ∪ J₂, x i ≤ ε := fun i hi => hxε i (hunion ▸ hi)
  have hfinish : ∀ K ⊆ I, X / 2 - ε ≤ ∑ i ∈ K, x i → ∑ i ∈ K, x i ≤ X / 2 + ε →
      Y - c ≤ ∑ i ∈ K, y i → ∑ i ∈ K, y i ≤ c →
      ∃ J ⊆ I, X / 2 - ε ≤ ∑ i ∈ J, x i ∧ ∑ i ∈ J, x i ≤ X / 2 + ε ∧
        ∑ i ∈ J, y i ≤ c ∧ ∑ i ∈ I \ J, y i ≤ c := by
    intro K hK h1 h2 h3 h4
    refine ⟨K, hK, h1, h2, h4, ?_⟩
    have := sum_sdiff hK (f := y)
    linarith
  by_cases h1 : c < ∑ i ∈ J₁, y i
  · obtain ⟨K, hK, hK1, hK2, hK3, hK4⟩ := exists_balanced_walk x y (X := X) (Y := Y) hdisj hxεU
      (fun i hi => hyη i (hJ₁I hi)) hy hx hη hc (by linarith) (by linarith)
      _ J₁ ∅ subset_rfl (empty_subset _) rfl (by rw [union_empty]; exact hJ₁x')
      (by rw [union_empty]; linarith) (by rw [union_empty]; exact h1)
    exact hfinish K (hunion ▸ hK) hK1 hK2 hK3 hK4
  by_cases h2 : c < ∑ i ∈ J₂, y i
  · obtain ⟨K, hK, hK1, hK2, hK3, hK4⟩ := exists_balanced_walk x y (X := X) (Y := Y) hdisj.symm
      (fun i hi => hxεU i (by rw [union_comm]; exact hi)) (fun i hi => hyη i (mem_sdiff.1 hi).1)
      hy hx hη hc hJ₁x' (by linarith) _ J₂ ∅ subset_rfl (empty_subset _) rfl
      (by rw [union_empty]; linarith) (by rw [union_empty]; linarith)
      (by rw [union_empty]; exact h2)
    exact hfinish K (by rw [← hunion, union_comm]; exact hK) hK1 hK2 hK3 hK4
  push Not at h1 h2
  exact ⟨J₁, hJ₁I, hJ₁x', by linarith, h1, h2⟩

end PlanarSeparator
