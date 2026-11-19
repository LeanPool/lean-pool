/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The `p`-biased cube as weights on subsets

Choosing each element of a finite set `U` independently with probability `p` gives the subset
`A ⊆ U` probability `p ^ |A| (1 - p) ^ |U \ A|`. This file develops that finite probability space
by counting, without measure theory: the weights sum to `1`, a fixed set `F ⊆ U` is contained in
the random set with probability `p ^ |F|` and avoided with probability `(1 - p) ^ |F|`, events
that depend on disjoint coordinate sets are independent, and the first-moment method (union bound
and averaging) holds.

The random graph `G(n, p)` is the case where `U` is the set of pairs of vertices (see
`LeanPool.ProbabilisticMethod.RandomGraph`). The counting probability agrees
with Mathlib's product of Bernoulli measures `setBer(U, p)` and binomial random graph `G(V, p)`
(see `LeanPool.ProbabilisticMethod.MeasureBridge`).

## Main definitions

* `Finset.bernoulliWeight U p A`: the probability `p ^ |A| (1 - p) ^ |U \ A|` of `A ⊆ U`.
* `Finset.bernoulliProb U p P`: the probability `∑ A ⊆ U with P A, bernoulliWeight U p A` of an
  event `P`.
* `Finset.DependsOnCoords P T`: the event `P` only depends on the coordinates in `T` (the
  `Finset` analogue of Mathlib's `DependsOn`).

## Main statements

* `Finset.sum_bernoulliWeight`: the weights sum to `1`.
* `Finset.bernoulliProb_superset`, `Finset.bernoulliProb_disjoint`: `P(F ⊆ A) = p ^ |F|` and
  `P(A ∩ F = ∅) = (1 - p) ^ |F|`.
* `Finset.bernoulliProb_and`: events depending on disjoint coordinate sets are independent.
* `Finset.exists_forall_not_of_sum_bernoulliProb_lt`: **the union bound**. If the probabilities
  of finitely many bad events add up to less than `1`, some `A ⊆ U` avoids all of them.
* `Finset.exists_le_expectation`: **the first-moment method**. Some `A ⊆ U` has `f A` at most the
  expectation of `f`.
* `Finset.expectation_card_filter`: linearity of expectation for the number of events that
  occur.
-/

@[expose] public section

open Finset

namespace Finset

variable {α : Type*} [DecidableEq α] (U : Finset α) (p : ℝ)

/-- The weight `p ^ |A| (1 - p) ^ |U \ A|`: for `0 ≤ p ≤ 1` and `A ⊆ U`, the probability of the
outcome `A` under independent `p`-biased choices of the elements of `U`. It is defined as a
polynomial for every real `p` and every `A` (no zero extension outside `U.powerset`), so the
algebraic identities hold unrestricted; the probability inequalities assume `0 ≤ p ≤ 1`. -/
noncomputable def bernoulliWeight (A : Finset α) : ℝ := p ^ #A * (1 - p) ^ #(U \ A)

/-- The probability of the event `P` under independent `p`-biased choices of the elements of
`U`: the total weight of the subsets `A ⊆ U` satisfying `P`. It is a probability for
`0 ≤ p ≤ 1`, and a polynomial in `p` in general. -/
noncomputable def bernoulliProb (P : Finset α → Prop) [DecidablePred P] : ℝ :=
  ∑ A ∈ U.powerset with P A, U.bernoulliWeight p A

variable {U p}

/-- For `0 ≤ p ≤ 1` the weights are nonnegative. -/
theorem bernoulliWeight_nonneg (h0 : 0 ≤ p) (h1 : p ≤ 1) (A : Finset α) :
    0 ≤ U.bernoulliWeight p A := by
  unfold bernoulliWeight
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- For `0 ≤ p ≤ 1` probabilities are nonnegative. -/
theorem bernoulliProb_nonneg (h0 : 0 ≤ p) (h1 : p ≤ 1) (P : Finset α → Prop) [DecidablePred P] :
    0 ≤ U.bernoulliProb p P :=
  sum_nonneg fun A _ => bernoulliWeight_nonneg h0 h1 A

variable (U p) in
/-- The weights sum to `1`. -/
theorem sum_bernoulliWeight : ∑ A ∈ U.powerset, U.bernoulliWeight p A = 1 := by
  have := sum_pow_mul_eq_add_pow p (1 - p) U
  rw [add_sub_cancel, one_pow] at this
  rw [← this]
  exact sum_congr rfl fun A hA => by
    rw [bernoulliWeight, card_sdiff_of_subset (mem_powerset.mp hA)]

/-- For `0 ≤ p ≤ 1` probabilities are at most `1`. -/
theorem bernoulliProb_le_one (h0 : 0 ≤ p) (h1 : p ≤ 1) (P : Finset α → Prop) [DecidablePred P] :
    U.bernoulliProb p P ≤ 1 := by
  rw [← sum_bernoulliWeight U p]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun A _ _ =>
    bernoulliWeight_nonneg h0 h1 A

/-- Events that agree on the subsets of `U` have the same probability. -/
theorem bernoulliProb_congr {P Q : Finset α → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ A ⊆ U, P A ↔ Q A) : U.bernoulliProb p P = U.bernoulliProb p Q :=
  sum_congr (filter_congr fun A hA => h A (mem_powerset.mp hA)) fun _ _ => rfl

/-- Complementing swaps `p` and `1 - p`. -/
theorem bernoulliWeight_sdiff {A : Finset α} (hA : A ⊆ U) :
    U.bernoulliWeight (1 - p) (U \ A) = U.bernoulliWeight p A := by
  rw [bernoulliWeight, bernoulliWeight, sdiff_sdiff_eq_self hA, sub_sub_cancel, mul_comm]

/-- **`P(F ⊆ A) = p ^ |F|`.** -/
theorem bernoulliProb_superset {F : Finset α} (hF : F ⊆ U) :
    U.bernoulliProb p (F ⊆ ·) = p ^ #F := by
  unfold bernoulliProb
  have key : ∀ A ∈ U.powerset.filter (F ⊆ ·),
      U.bernoulliWeight p A = p ^ #F * (U \ F).bernoulliWeight p (A \ F) := by
    intro A hA
    obtain ⟨-, hFA⟩ := mem_filter.mp hA
    rw [bernoulliWeight, bernoulliWeight, sdiff_sdiff_sdiff_cancel_right hFA,
      card_sdiff_of_subset hFA, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' (card_le_card hFA)]
  rw [sum_congr rfl key, ← mul_sum]
  conv_rhs => rw [← mul_one (p ^ #F), ← sum_bernoulliWeight (U \ F) p]
  congr 1
  refine sum_nbij' (· \ F) (· ∪ F) (fun A hA => ?_) (fun B hB => ?_) (fun A hA => ?_)
    (fun B hB => ?_) fun _ _ => rfl
  · obtain ⟨hAU, -⟩ := mem_filter.mp hA
    exact mem_powerset.mpr (sdiff_subset_sdiff (mem_powerset.mp hAU) (Subset.refl F))
  · rw [mem_powerset] at hB
    refine mem_filter.mpr ⟨mem_powerset.mpr (union_subset (hB.trans sdiff_subset) hF),
      subset_union_right⟩
  · exact sdiff_union_of_subset (mem_filter.mp hA).2
  · rw [mem_powerset] at hB
    exact union_sdiff_cancel_right (disjoint_of_subset_left hB disjoint_sdiff_self_left)

/-- **`P(A ∩ F = ∅) = (1 - p) ^ |F|`.** -/
theorem bernoulliProb_disjoint {F : Finset α} (hF : F ⊆ U) :
    U.bernoulliProb p (Disjoint · F) = (1 - p) ^ #F := by
  rw [← bernoulliProb_superset (p := 1 - p) hF, bernoulliProb, bernoulliProb]
  refine sum_nbij' (U \ ·) (U \ ·) (fun A hA => ?_) (fun A hA => ?_) (fun A hA => ?_)
    (fun A hA => ?_) fun A hA => ?_
  · obtain ⟨-, hAF⟩ := mem_filter.mp hA
    refine mem_filter.mpr ⟨mem_powerset.mpr sdiff_subset, fun x hx => mem_sdiff.mpr ⟨hF hx, ?_⟩⟩
    exact fun hxA => disjoint_left.mp hAF hxA hx
  · obtain ⟨-, hFA⟩ := mem_filter.mp hA
    refine mem_filter.mpr ⟨mem_powerset.mpr sdiff_subset, disjoint_left.mpr fun x hx hxF => ?_⟩
    exact (mem_sdiff.mp hx).2 (hFA hxF)
  · exact sdiff_sdiff_eq_self (mem_powerset.mp (mem_filter.mp hA).1)
  · exact sdiff_sdiff_eq_self (mem_powerset.mp (mem_filter.mp hA).1)
  · rw [bernoulliWeight_sdiff (mem_powerset.mp (mem_filter.mp hA).1)]

/-! ### Independence -/

/-- The event `P` depends only on the coordinates in `T`: `P A ↔ P B` whenever
`A ∩ T = B ∩ T`, for all finite sets `A` and `B` of the ambient type, not only subsets of `U`. -/
def DependsOnCoords (P : Finset α → Prop) (T : Finset α) : Prop :=
  ∀ A B, A ∩ T = B ∩ T → (P A ↔ P B)

/-- Splitting a subset of `U` along `T ⊆ U` multiplies the weights. -/
private theorem bernoulliWeight_union {T : Finset α} (hT : T ⊆ U) {a b : Finset α} (ha : a ⊆ T)
    (hb : b ⊆ U \ T) :
    U.bernoulliWeight p (a ∪ b) = T.bernoulliWeight p a * (U \ T).bernoulliWeight p b := by
  have hab : Disjoint a b := disjoint_of_subset_left ha (disjoint_of_subset_right hb
    disjoint_sdiff)
  have hsplit : U \ (a ∪ b) = (T \ a) ∪ ((U \ T) \ b) := by
    ext x
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨hx, hxab⟩
      by_cases hxT : x ∈ T
      · exact .inl ⟨hxT, fun h => hxab (.inl h)⟩
      · exact .inr ⟨⟨hx, hxT⟩, fun h => hxab (.inr h)⟩
    · rintro (⟨hxT, hxa⟩ | ⟨⟨hx, hxT⟩, hxb⟩)
      · exact ⟨hT hxT, by rintro (h | h); exacts [hxa h, (mem_sdiff.mp (hb h)).2 hxT]⟩
      · exact ⟨hx, by rintro (h | h); exacts [hxT (ha h), hxb h]⟩
  have hdisj : Disjoint (T \ a) ((U \ T) \ b) :=
    disjoint_of_subset_left sdiff_subset (disjoint_of_subset_right sdiff_subset disjoint_sdiff)
  rw [bernoulliWeight, bernoulliWeight, bernoulliWeight, hsplit, card_union_of_disjoint hab,
    card_union_of_disjoint hdisj, pow_add, pow_add]
  ring

/-- Summing over subsets of `U` is summing over pairs of subsets of `T` and `U \ T`. -/
private theorem sum_powerset_split {T : Finset α} (hT : T ⊆ U) (f : Finset α → ℝ) :
    ∑ A ∈ U.powerset, f A = ∑ a ∈ T.powerset, ∑ b ∈ (U \ T).powerset, f (a ∪ b) := by
  rw [← sum_product']
  refine sum_nbij' (fun A => (A ∩ T, A \ T)) (fun x => x.1 ∪ x.2) (fun A hA => ?_)
    (fun x hx => ?_) (fun A _ => ?_) (fun x hx => ?_) fun A _ => ?_
  · rw [mem_product, mem_powerset, mem_powerset]
    exact ⟨inter_subset_right, sdiff_subset_sdiff (mem_powerset.mp hA) (Subset.refl T)⟩
  · rw [mem_product, mem_powerset, mem_powerset] at hx
    exact mem_powerset.mpr (union_subset (hx.1.trans hT) (hx.2.trans sdiff_subset))
  · rw [union_comm, sdiff_union_inter]
  · rw [mem_product, mem_powerset, mem_powerset] at hx
    ext1
    · simp only
      rw [union_inter_distrib_right, inter_eq_left.mpr hx.1,
        disjoint_iff_inter_eq_empty.mp (disjoint_of_subset_right hx.2 disjoint_sdiff).symm,
        union_empty]
    · simp only
      rw [union_sdiff_distrib, sdiff_eq_empty_iff_subset.mpr hx.1, empty_union,
        sdiff_eq_self_of_disjoint (disjoint_of_subset_left hx.2 disjoint_sdiff_self_left)]
  · simp only
    rw [union_comm, sdiff_union_inter]

/-- **Independence.** Events depending on disjoint coordinate sets `T ⊆ U` and `T'` are
independent: `P(P ∧ Q) = P(P) P(Q)`. -/
theorem bernoulliProb_and {T T' : Finset α} (hT : T ⊆ U) (hTT' : Disjoint T T')
    {P Q : Finset α → Prop} [DecidablePred P] [DecidablePred Q] (hP : DependsOnCoords P T)
    (hQ : DependsOnCoords Q T') :
    U.bernoulliProb p (fun A => P A ∧ Q A) = U.bernoulliProb p P * U.bernoulliProb p Q := by
  -- on `a ∪ b` with `a ⊆ T` and `b ⊆ U \ T`, `P` sees only `a` and `Q` only `b`
  have hPa : ∀ a ⊆ T, ∀ b ⊆ U \ T, (P (a ∪ b) ↔ P a) := fun a ha b hb => hP _ _ (by
    rw [union_inter_distrib_right, inter_eq_left.mpr ha,
      disjoint_iff_inter_eq_empty.mp (disjoint_of_subset_left hb disjoint_sdiff_self_left),
      union_empty])
  have hQb : ∀ a ⊆ T, ∀ b ⊆ U \ T, (Q (a ∪ b) ↔ Q b) := fun a ha b hb => hQ _ _ (by
    rw [union_inter_distrib_right,
      disjoint_iff_inter_eq_empty.mp (disjoint_of_subset_left ha hTT'), empty_union])
  have hsplit : ∀ R : Finset α → Prop, [DecidablePred R] →
      U.bernoulliProb p R = ∑ a ∈ T.powerset, ∑ b ∈ (U \ T).powerset,
        if R (a ∪ b) then T.bernoulliWeight p a * (U \ T).bernoulliWeight p b else 0 := by
    intro R _
    rw [bernoulliProb, sum_filter, sum_powerset_split hT]
    refine sum_congr rfl fun a ha => sum_congr rfl fun b hb => ?_
    rw [bernoulliWeight_union hT (mem_powerset.mp ha) (mem_powerset.mp hb)]
  rw [hsplit, hsplit P, hsplit Q]
  have e1 : ∀ a ∈ T.powerset, ∀ b ∈ (U \ T).powerset,
      (if P (a ∪ b) ∧ Q (a ∪ b) then T.bernoulliWeight p a * (U \ T).bernoulliWeight p b else 0) =
        (if P a then T.bernoulliWeight p a else 0) *
          (if Q b then (U \ T).bernoulliWeight p b else 0) := fun a ha b hb => by
    have h1 := hPa a (mem_powerset.mp ha) b (mem_powerset.mp hb)
    have h2 := hQb a (mem_powerset.mp ha) b (mem_powerset.mp hb)
    by_cases hp : P a <;> by_cases hq : Q b <;> simp [h1, h2, hp, hq]
  have e2 : ∀ a ∈ T.powerset, ∀ b ∈ (U \ T).powerset,
      (if P (a ∪ b) then T.bernoulliWeight p a * (U \ T).bernoulliWeight p b else 0) =
        (if P a then T.bernoulliWeight p a else 0) * (U \ T).bernoulliWeight p b :=
    fun a ha b hb => by
      have h1 := hPa a (mem_powerset.mp ha) b (mem_powerset.mp hb)
      by_cases hp : P a <;> simp [h1, hp]
  have e3 : ∀ a ∈ T.powerset, ∀ b ∈ (U \ T).powerset,
      (if Q (a ∪ b) then T.bernoulliWeight p a * (U \ T).bernoulliWeight p b else 0) =
        T.bernoulliWeight p a * (if Q b then (U \ T).bernoulliWeight p b else 0) :=
    fun a ha b hb => by
      have h2 := hQb a (mem_powerset.mp ha) b (mem_powerset.mp hb)
      by_cases hq : Q b <;> simp [h2, hq]
  rw [sum_congr rfl fun a ha => sum_congr rfl (e1 a ha), sum_congr rfl fun a ha =>
    sum_congr rfl (e2 a ha), sum_congr rfl fun a ha => sum_congr rfl (e3 a ha)]
  simp_rw [← mul_sum, ← sum_mul, sum_bernoulliWeight, mul_one, one_mul]

/-! ### The first-moment method -/

/-- **The first-moment method.** Some `A ⊆ U` has `f A` at most the expectation
`∑ A ⊆ U, bernoulliWeight U p A * f A`. -/
theorem exists_le_expectation (h0 : 0 ≤ p) (h1 : p ≤ 1) (f : Finset α → ℝ) :
    ∃ A ∈ U.powerset, f A ≤ ∑ B ∈ U.powerset, U.bernoulliWeight p B * f B := by
  obtain ⟨A, hA, hmin⟩ := U.powerset.exists_min_image f (powerset_nonempty U)
  refine ⟨A, hA, ?_⟩
  calc f A = ∑ B ∈ U.powerset, U.bernoulliWeight p B * f A := by
        rw [← sum_mul, sum_bernoulliWeight, one_mul]
    _ ≤ _ := sum_le_sum fun B hB =>
        mul_le_mul_of_nonneg_left (hmin B hB) (bernoulliWeight_nonneg h0 h1 B)

/-- **Linearity of expectation for counts.** The expected number of the events `E i`, `i ∈ I`,
that occur is the sum of their probabilities. -/
theorem expectation_card_filter {ι : Type*} (I : Finset ι) (E : ι → Finset α → Prop)
    [∀ i, DecidablePred (E i)] :
    ∑ B ∈ U.powerset, U.bernoulliWeight p B * (#{i ∈ I | E i B} : ℝ) =
      ∑ i ∈ I, U.bernoulliProb p (E i) := by
  simp_rw [card_filter, Nat.cast_sum, mul_sum, bernoulliProb, sum_filter]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun B _ => by split_ifs <;> simp

/-- **The union bound.** If the probabilities of the bad events `E i`, `i ∈ I`, add up to less
than `1`, then some `A ⊆ U` avoids all of them. -/
theorem exists_forall_not_of_sum_bernoulliProb_lt {ι : Type*} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (I : Finset ι) (E : ι → Finset α → Prop) [∀ i, DecidablePred (E i)]
    (h : ∑ i ∈ I, U.bernoulliProb p (E i) < 1) :
    ∃ A ∈ U.powerset, ∀ i ∈ I, ¬E i A := by
  obtain ⟨A, hA, hle⟩ := exists_le_expectation h0 h1 fun A => (#{i ∈ I | E i A} : ℝ)
  refine ⟨A, hA, fun i hi hiA => ?_⟩
  rw [expectation_card_filter] at hle
  have hone : (1 : ℝ) ≤ #{i ∈ I | E i A} := by
    exact_mod_cast card_pos.mpr ⟨i, mem_filter.mpr ⟨hi, hiA⟩⟩
  linarith

end Finset
