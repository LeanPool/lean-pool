/-
Copyright (c) 2026 Antigravity / Arithmetica4 Prize Campaign Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity / Arithmetica4 Prize Campaign Contributors
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Primorial
public import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# Cauchy–Schwarz barriers for Erdős problem 711

The lower bounds constrain the three-path reflection method over arbitrary covers.
They give exponents of two thirds for unabsorbed multiplicities and one half after absorption.
The proofs use dyadic prime counts and finite Bernoulli weights on subsets of primes.
-/

@[expose] public section

namespace Erdos711.Barriers

/-! ### Section 1: Elementary Real & Partition-Elimination Inequalities -/

/-- Elementary lower bound `1 / 2 ≤ log 2`. -/
private lemma half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h ⊢
  exact h

/-- Elementary upper bound `log 2 ≤ 1`. -/
private lemma log_two_le_one : Real.log 2 ≤ 1 := by
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- For `0 ≤ x ≤ 1`, `exp (x / 2) ≤ 1 + x`. -/
private lemma exp_half_le_one_add {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (x / 2) ≤ 1 + x := by
  have h1 : Real.exp (-(x / 2)) ≥ 1 - x / 2 := by
    have := Real.add_one_le_exp (-(x / 2)); linarith
  have hpos : 0 < Real.exp (x / 2) := Real.exp_pos _
  have hinv : Real.exp (-(x / 2)) = (Real.exp (x / 2))⁻¹ := Real.exp_neg (x / 2)
  rw [hinv] at h1
  have hmul : (1 - x / 2) * Real.exp (x / 2) ≤ 1 := by
    calc (1 - x / 2) * Real.exp (x / 2)
        ≤ (Real.exp (x / 2))⁻¹ * Real.exp (x / 2) :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt hpos)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  have hden : 0 < 1 - x / 2 := by linarith
  have hprod : 1 ≤ (1 - x / 2) * (1 + x) := by nlinarith
  nlinarith

/-- Hölder with the constant function one bounds the sum of inverse powers. -/
private lemma sum_rpow_inv_le {α : Type*} (S : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ S, 0 ≤ f x) {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∑ x ∈ S, f x ^ (1 / p) ≤ (∑ x ∈ S, f x) ^ (1 / p) * (S.card : ℝ) ^ (1 / q) := by
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg (s := S) (f := fun x => f x ^ (1 / p))
    (g := fun _ => 1) hpq (fun x hx => Real.rpow_nonneg (hf x hx) _) (fun _ _ => zero_le_one)
  have hpower : ∑ x ∈ S, (f x ^ (1 / p)) ^ p = ∑ x ∈ S, f x := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← Real.rpow_mul (hf x hx), one_div, inv_mul_cancel₀ hpq.ne_zero, Real.rpow_one]
  rw [hpower] at h
  simpa only [mul_one, Real.one_rpow, Finset.sum_const, nsmul_eq_mul] using h

private lemma sum_rpow_two_thirds_le {α : Type*} (S : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ S, 0 ≤ f x) :
    ∑ x ∈ S, (f x) ^ ((2 : ℝ) / 3) ≤ (∑ x ∈ S, f x) ^ ((2 : ℝ) / 3) *
      (S.card : ℝ) ^ ((1 : ℝ) / 3) := by
  have hpq : ((3 : ℝ) / 2).HolderConjugate 3 := ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [show (1 : ℝ) / (3 / 2) = 2 / 3 by norm_num] using sum_rpow_inv_le S f hf hpq

private lemma sum_rpow_half_le {α : Type*} (S : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ S, 0 ≤ f x) :
    ∑ x ∈ S, (f x) ^ ((1 : ℝ) / 2) ≤ (∑ x ∈ S, f x) ^ ((1 : ℝ) / 2) *
      (S.card : ℝ) ^ ((1 : ℝ) / 2) :=
  sum_rpow_inv_le S f hf Real.HolderConjugate.two_two

/-- `ℓ^{3/2} ≤ ℓ^1` monotonicity: `∑ x_i^{3/2} ≤ (∑ x_i)^{3/2}` for `x_i ≥ 0`. -/
private lemma sum_rpow_three_halves_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, (f i) ^ ((3 : ℝ) / 2) ≤ (∑ i ∈ s, f i) ^ ((3 : ℝ) / 2) := by
  set S : ℝ := ∑ i ∈ s, f i
  have hS : 0 ≤ S := Finset.sum_nonneg hf
  have hpt : ∀ i ∈ s, (f i) ^ ((3 : ℝ) / 2) ≤ f i * S ^ ((1 : ℝ) / 2) := by
    intro i hi
    have hfi : 0 ≤ f i := hf i hi
    have hfi_le : f i ≤ S := Finset.single_le_sum hf hi
    have hsplit : (f i) ^ ((3 : ℝ) / 2) = f i * (f i) ^ ((1 : ℝ) / 2) := by
      rw [show ((3 : ℝ) / 2) = 1 + ((1 : ℝ) / 2) by norm_num,
        Real.rpow_add_of_nonneg hfi (by norm_num) (by norm_num), Real.rpow_one]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hfi hfi_le (by norm_num)) hfi
  calc ∑ i ∈ s, (f i) ^ ((3 : ℝ) / 2)
      ≤ ∑ i ∈ s, f i * S ^ ((1 : ℝ) / 2) := Finset.sum_le_sum hpt
    _ = S * S ^ ((1 : ℝ) / 2) := by rw [← Finset.sum_mul]
    _ = S ^ ((3 : ℝ) / 2) := by
        rw [show ((3 : ℝ) / 2) = 1 + ((1 : ℝ) / 2) by norm_num,
          Real.rpow_add_of_nonneg hS (by norm_num) (by norm_num), Real.rpow_one]

/-- Subadditivity of nonnegative sums over `Finset.biUnion`. -/
private lemma finset_sum_biUnion_le {ι α : Type*} [DecidableEq α] (idx : Finset ι)
    (S : ι → Finset α) (f : α → ℝ) (hf : ∀ x ∈ idx.biUnion S, 0 ≤ f x) :
    ∑ x ∈ idx.biUnion S, f x ≤ ∑ i ∈ idx, ∑ x ∈ S i, f x := by
  classical
  induction idx using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hf_a : ∀ x ∈ S a, 0 ≤ f x := fun x hx =>
      hf x (Finset.mem_biUnion.mpr ⟨a, Finset.mem_insert_self a s, hx⟩)
    have hf_s : ∀ x ∈ s.biUnion S, 0 ≤ f x := fun x hx => by
      rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxi⟩
      exact hf x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_insert_of_mem hi, hxi⟩)
    have hunion : ∑ x ∈ S a ∪ s.biUnion S, f x ≤ ∑ x ∈ S a, f x + ∑ x ∈ s.biUnion S, f x := by
      have h := Finset.sum_union_inter (s₁ := S a) (s₂ := s.biUnion S) (f := f)
      have hinter_nn : 0 ≤ ∑ x ∈ S a ∩ s.biUnion S, f x :=
        Finset.sum_nonneg fun x hx => hf_a x (Finset.mem_inter.mp hx).1
      linarith
    exact le_trans hunion (add_le_add (le_refl _) (ih hf_s))

/-- Summing weights over a finite relation counts each weight with its multiplicity. -/
private lemma sum_filtered_weights {α β : Type*} (A : Finset α) (B : Finset β)
    (rel : α → β → Prop) [DecidableRel rel] (weight : β → ℝ) :
    ∑ a ∈ A, ∑ b ∈ B.filter (rel a), weight b =
      ∑ b ∈ B, ((A.filter fun a => rel a b).card : ℝ) * weight b := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- Total divisor weight on one set is at most its maximum multiplicity. -/
private lemma sum_dvd_weight_le (S : Finset ℕ) (H : ℕ) (w : ℕ → ℝ)
    (hw_nn : ∀ t ∈ Finset.Icc 1 H, 0 ≤ w t)
    (hw_sum : ∑ t ∈ Finset.Icc 1 H, w t ≤ 1) :
    (∑ d ∈ S, ∑ t ∈ (Finset.Icc 1 H).filter (fun t => d ∣ t), w t) ≤
      (((Finset.Icc 1 H).sup (fun t => (S.filter (fun d => d ∣ t)).card) : ℕ) : ℝ) := by
  rw [sum_filtered_weights]
  set κ := (Finset.Icc 1 H).sup (fun t => (S.filter (fun d => d ∣ t)).card)
  calc ∑ t ∈ Finset.Icc 1 H, ((S.filter (fun d => d ∣ t)).card : ℝ) * w t
      ≤ ∑ t ∈ Finset.Icc 1 H, (κ : ℝ) * w t := by
        refine Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_right ?_ (hw_nn t ht)
        exact_mod_cast Finset.le_sup (f := fun t => (S.filter (fun d => d ∣ t)).card) ht
    _ = (κ : ℝ) * ∑ t ∈ Finset.Icc 1 H, w t := by rw [← Finset.mul_sum]
    _ ≤ (κ : ℝ) * 1 := mul_le_mul_of_nonneg_left hw_sum (Nat.cast_nonneg _)
    _ = (κ : ℝ) := mul_one _

/-- Abstract Partition-Elimination for Barrier 1 (`2/3`): for any sub-probability weight `w` on
`Icc 1 H` and any cover `D ⊆ idx.biUnion S`,
`∑ d ∈ D, p_w(d)^(2/3) ≤ ∑ α ∈ idx, κ(S α, H)^(2/3) * |S α|^(1/3)`. -/
lemma partition_lower_two_thirds {ι : Type*} (D : Finset ℕ) (H : ℕ)
    (w : ℕ → ℝ) (hw_nn : ∀ t ∈ Finset.Icc 1 H, 0 ≤ w t) (hw_sum : ∑ t ∈ Finset.Icc 1 H, w t ≤ 1)
    (idx : Finset ι) (S : ι → Finset ℕ) (hcover : D ⊆ idx.biUnion S) :
    let p_w : ℕ → ℝ := fun d => ∑ t ∈ (Finset.Icc 1 H).filter (fun t => d ∣ t), w t
    ∑ d ∈ D, (p_w d) ^ ((2 : ℝ) / 3) ≤
      ∑ α ∈ idx,
        (((Finset.Icc 1 H).sup (fun t => ((S α).filter (fun d => d ∣ t)).card) : ℕ) : ℝ) ^ ((2 :
          ℝ) / 3) *
          ((S α).card : ℝ) ^ ((1 : ℝ) / 3) := by
  intro p_w
  have hp_nn : ∀ d, 0 ≤ p_w d := fun d =>
    Finset.sum_nonneg fun t ht => hw_nn t (Finset.mem_filter.mp ht).1
  calc ∑ d ∈ D, (p_w d) ^ ((2 : ℝ) / 3)
      ≤ ∑ d ∈ idx.biUnion S, (p_w d) ^ ((2 : ℝ) / 3) :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover fun d _ _ => Real.rpow_nonneg (hp_nn d) _
    _ ≤ ∑ α ∈ idx, ∑ d ∈ S α, (p_w d) ^ ((2 : ℝ) / 3) :=
        finset_sum_biUnion_le idx S (fun d => (p_w d) ^ ((2 : ℝ) / 3)) (fun d _ =>
          Real.rpow_nonneg (hp_nn d) _)
    _ ≤ ∑ α ∈ idx,
          (((Finset.Icc 1 H).sup (fun t => ((S α).filter (fun d => d ∣ t)).card) : ℕ) : ℝ) ^ ((2 :
            ℝ) / 3) *
            ((S α).card : ℝ) ^ ((1 : ℝ) / 3) := by
        refine Finset.sum_le_sum fun α _ => ?_
        have h1 := sum_rpow_two_thirds_le (S α) p_w (fun d _ => hp_nn d)
        have h2 := Real.rpow_le_rpow (Finset.sum_nonneg fun d _ => hp_nn d)
          (sum_dvd_weight_le (S α) H w hw_nn hw_sum) (by
          norm_num : (0 : ℝ) ≤ 2 / 3)
        exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (by positivity))

/-- Abstract Partition-Elimination for Barrier 2a (`1/2`): for any sub-probability weight `w` on
`Icc 1 H` and any cover `D ⊆ idx.biUnion S`,
`(∑ d ∈ D, p_w(d)^(1/2))^(2/3) ≤ ∑ α ∈ idx, κ(S α, H)^(1/3) * |S α|^(1/3)`. -/
lemma partition_lower_half {ι : Type*} (D : Finset ℕ) (H : ℕ)
    (w : ℕ → ℝ) (hw_nn : ∀ t ∈ Finset.Icc 1 H, 0 ≤ w t) (hw_sum : ∑ t ∈ Finset.Icc 1 H, w t ≤ 1)
    (idx : Finset ι) (S : ι → Finset ℕ) (hcover : D ⊆ idx.biUnion S) :
    let p_w : ℕ → ℝ := fun d => ∑ t ∈ (Finset.Icc 1 H).filter (fun t => d ∣ t), w t
    (∑ d ∈ D, (p_w d) ^ ((1 : ℝ) / 2)) ^ ((2 : ℝ) / 3) ≤
      ∑ α ∈ idx,
        (((Finset.Icc 1 H).sup (fun t => ((S α).filter (fun d => d ∣ t)).card) : ℕ) : ℝ) ^ ((1 :
          ℝ) / 3) *
          ((S α).card : ℝ) ^ ((1 : ℝ) / 3) := by
  intro p_w
  have hp_nn : ∀ d, 0 ≤ p_w d := fun d =>
    Finset.sum_nonneg fun t ht => hw_nn t (Finset.mem_filter.mp ht).1
  let a : ι → ℝ := fun α =>
    (((Finset.Icc 1 H).sup (fun t => ((S α).filter (fun d => d ∣ t)).card) : ℕ) : ℝ) ^ ((1 : ℝ) /
      3) *
      ((S α).card : ℝ) ^ ((1 : ℝ) / 3)
  have ha_nn : ∀ α ∈ idx, 0 ≤ a α := fun _ _ => by dsimp [a]; positivity
  have h32 : ∑ d ∈ D, (p_w d) ^ ((1 : ℝ) / 2) ≤ (∑ α ∈ idx, a α) ^ ((3 : ℝ) / 2) := by
    calc ∑ d ∈ D, (p_w d) ^ ((1 : ℝ) / 2)
        ≤ ∑ d ∈ idx.biUnion S, (p_w d) ^ ((1 : ℝ) / 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hcover fun d _ _ => Real.rpow_nonneg (hp_nn d) _
      _ ≤ ∑ α ∈ idx, ∑ d ∈ S α, (p_w d) ^ ((1 : ℝ) / 2) :=
          finset_sum_biUnion_le idx S (fun d => (p_w d) ^ ((1 : ℝ) / 2)) (fun d _ =>
            Real.rpow_nonneg (hp_nn d) _)
      _ ≤ ∑ α ∈ idx, (a α) ^ ((3 : ℝ) / 2) := by
          refine Finset.sum_le_sum fun α _ => ?_
          have h1 := sum_rpow_half_le (S α) p_w (fun d _ => hp_nn d)
          have h2 := Real.rpow_le_rpow (Finset.sum_nonneg fun d _ => hp_nn d)
            (sum_dvd_weight_le (S α) H w hw_nn hw_sum) (by
            norm_num : (0 : ℝ) ≤ 1 / 2)
          have ha32 : (a α) ^ ((3 : ℝ) / 2) =
              (((Finset.Icc 1 H).sup (fun t => ((S α).filter (fun d => d ∣ t)).card) : ℕ) : ℝ) ^
                ((1 : ℝ) / 2) *
                ((S α).card : ℝ) ^ ((1 : ℝ) / 2) := by
            dsimp [a]
            rw [Real.mul_rpow (by positivity) (by positivity),
              ← Real.rpow_mul (Nat.cast_nonneg _), ← Real.rpow_mul (Nat.cast_nonneg _)]
            norm_num
          rw [ha32]
          exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (by positivity))
      _ ≤ (∑ α ∈ idx, a α) ^ ((3 : ℝ) / 2) := sum_rpow_three_halves_le idx a ha_nn
  have hpow := Real.rpow_le_rpow (Finset.sum_nonneg fun d _ => Real.rpow_nonneg (hp_nn d) _) h32
    (by norm_num : (0 : ℝ) ≤ 2 / 3)
  rw [← Real.rpow_mul (Finset.sum_nonneg ha_nn)] at hpow
  norm_num at hpow
  exact hpow

/-! ### Section 2: Elementary Chebyshev Primorial Upper Bound & Dyadic Prime Lower Bound -/

/-- Erdős's 1932 elementary primorial bound: `∏_{p ≤ N} p ≤ 4 ^ N` for all `N : ℕ`. -/
private lemma prod_primes_le_four_pow (N : ℕ) :
    ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime, p ≤ 4 ^ N := by
  have h : (Finset.Icc 1 N).filter Nat.Prime = (Finset.range (N + 1)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range, Nat.lt_succ_iff]
    exact ⟨fun ⟨⟨_, hpN⟩, hp⟩ => ⟨hpN, hp⟩, fun ⟨hpN, hp⟩ => ⟨⟨hp.one_lt.le, hpN⟩, hp⟩⟩
  rw [h]
  exact primorial_le_four_pow N

/-- Dyadic prime reciprocal sum upper bound: for `r ≥ 1`, `∑_{2^r < p ≤ 2^(r+1)} 1/p ≤ 4 / r`. -/
private lemma sum_inv_primes_dyadic_le (r : ℕ) (hr : 1 ≤ r) :
    ∑ p ∈ (Finset.Ioc (2 ^ r) (2 ^ (r + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤ 4 / (r : ℝ) := by
  let S := (Finset.Ioc (2 ^ r) (2 ^ (r + 1))).filter Nat.Prime
  have hsub : S ⊆ (Finset.Icc 1 (2 ^ (r + 1))).filter Nat.Prime := fun p hp => by
    have h1 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, h1.2⟩, (Finset.mem_filter.mp hp).2⟩
  have hpow_le : 2 ^ (r * S.card) ≤ 2 ^ (4 * 2 ^ r) := by
    calc 2 ^ (r * S.card) = (2 ^ r) ^ S.card := by rw [pow_mul]
      _ = ∏ _p ∈ S, 2 ^ r := by simp
      _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod fun p hp => le_of_lt (Finset.mem_Ioc.mp
        (Finset.mem_filter.mp hp).1).1
      _ ≤ ∏ p ∈ (Finset.Icc 1 (2 ^ (r + 1))).filter Nat.Prime, p :=
          Finset.prod_le_prod_of_subset_of_one_le hsub fun p hp _ => (Finset.mem_filter.mp
            hp).2.one_le
      _ ≤ 4 ^ (2 ^ (r + 1)) := prod_primes_le_four_pow (2 ^ (r + 1))
      _ = 2 ^ (4 * 2 ^ r) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, pow_succ]
          congr 1
          ring
  have hcard : r * S.card ≤ 4 * 2 ^ r := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow_le
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have h2r_pos : (0 : ℝ) < ((2 ^ r : ℕ) : ℝ) := by positivity
  have hcard_r : (r : ℝ) * (S.card : ℝ) ≤ 4 * ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast hcard
  calc ∑ p ∈ S, (1 : ℝ) / (p : ℝ)
      ≤ ∑ _p ∈ S, (1 : ℝ) / ((2 ^ r : ℕ) : ℝ) := Finset.sum_le_sum fun p hp =>
        one_div_le_one_div_of_le h2r_pos (by exact_mod_cast le_of_lt (Finset.mem_Ioc.mp
          (Finset.mem_filter.mp hp).1).1)
    _ = (S.card : ℝ) / ((2 ^ r : ℕ) : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    _ ≤ 4 / (r : ℝ) := by rw [div_le_div_iff₀ h2r_pos hr_pos]; linarith

private lemma dyadicPrimeCount_B2 :
    ∀ (m : ℕ),
        let P_mid : Finset ℕ := Finset.filter Nat.Prime (Finset.Ioc ((2 : ℕ) * m).sqrt ((2 : ℕ) *
          m / (3 : ℕ)));
        ∏ p ∈ P_mid, p ^ ((((2 : ℕ) * m).choose m).factorization : ℕ → ℕ) p ≤ (4 : ℕ) ^ ((2 : ℕ) *
          m / (3 : ℕ)) := by
  intro m P_mid
  classical
  have hpt : ∀ p ∈ P_mid, p ^ ((Nat.choose (2 * m) m).factorization p) ≤ p := by
    intro p hp
    have hpr := (Finset.mem_filter.mp hp).2
    have hp_gt : Nat.sqrt (2 * m) < p := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    have hp2 : 2 * m < p ^ 2 := Nat.sqrt_lt'.mp hp_gt
    have hv1 : (Nat.choose (2 * m) m).factorization p ≤ 1 := Nat.factorization_choose_le_one hp2
    calc p ^ ((Nat.choose (2 * m) m).factorization p) ≤ p ^ 1 := Nat.pow_le_pow_right hpr.pos hv1
      _ = p := pow_one p
  have hsub2 : P_mid ⊆ (Finset.Icc 1 (2 * m / 3)).filter Nat.Prime := fun p hp =>
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hp).2.one_le,
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2⟩, (Finset.mem_filter.mp hp).2⟩
  calc ∏ p ∈ P_mid, p ^ ((Nat.choose (2 * m) m).factorization p)
      ≤ ∏ p ∈ P_mid, p := Finset.prod_le_prod hpt
    _ ≤ ∏ p ∈ (Finset.Icc 1 (2 * m / 3)).filter Nat.Prime, p :=
        Finset.prod_le_prod_of_subset_of_one_le hsub2 fun p hp _ => (Finset.mem_filter.mp
          hp).2.one_le
    _ ≤ 4 ^ (2 * m / 3) := prod_primes_le_four_pow (2 * m / 3)


private lemma dyadicPrimeCount_ch_le :
    ∀ (m : ℕ),
      (10 : ℕ) ^ (9 : ℕ) ≤ m →
        let P_sq : Finset ℕ := Finset.filter Nat.Prime (Finset.Icc (1 : ℕ) ((2 : ℕ) * m).sqrt);
        let P_mid : Finset ℕ := Finset.filter Nat.Prime (Finset.Ioc ((2 : ℕ) * m).sqrt ((2 : ℕ) *
          m / (3 : ℕ)));
        let P_hi : Finset ℕ := Finset.filter Nat.Prime (Finset.Ioc m ((2 : ℕ) * m));
          (((2 : ℕ) * m).choose m).primeFactors ⊆ P_sq ∪ P_mid ∪ P_hi →
            ((2 : ℕ) * m).choose m ≤
              ((2 : ℕ) * m) ^ ((2 : ℕ) * m).sqrt * (4 : ℕ) ^ ((2 : ℕ) * m / (3 : ℕ)) * ((2 : ℕ) *
                m) ^ P_hi.card := by
  intro m hm P_sq P_mid P_hi hsub_union
  classical
  have hch_pos : 0 < Nat.choose (2 * m) m := Nat.choose_pos (by omega)
  have hdisj1 : Disjoint P_sq P_mid := by
    rw [Finset.disjoint_left]; intro p hp1 hp2
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp1).1).2
    have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp2).1).1; omega
  have hdisj2 : Disjoint (P_sq ∪ P_mid) P_hi := by
    rw [Finset.disjoint_left]; intro p hp1 hp2
    have hhi := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp2).1).1
    rcases Finset.mem_union.mp hp1 with ha | hb
    · have hle := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2
      have hsq : Nat.sqrt (2 * m) * Nat.sqrt (2 * m) ≤ 2 * m := Nat.sqrt_le (2 * m)
      nlinarith
    · have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hb).1).2; omega
  have hprod_eq : Nat.choose (2 * m) m =
      (∏ p ∈ P_sq, p ^ ((Nat.choose (2 * m) m).factorization p)) *
      (∏ p ∈ P_mid, p ^ ((Nat.choose (2 * m) m).factorization p)) *
      (∏ p ∈ P_hi, p ^ ((Nat.choose (2 * m) m).factorization p)) := by
    rw [← Finset.prod_union hdisj1, ← Finset.prod_union hdisj2]
    symm
    calc ∏ p ∈ P_sq ∪ P_mid ∪ P_hi, p ^ ((Nat.choose (2 * m) m).factorization p)
        = ∏ p ∈ (Nat.choose (2 * m) m).primeFactors, p ^ ((Nat.choose (2 * m) m).factorization p)
          := by
          symm; refine Finset.prod_subset hsub_union fun p _ hp_not => ?_
          rw [Finsupp.notMem_support_iff.mp hp_not, pow_zero]
      _ = Nat.choose (2 * m) m := Nat.prod_factorization_pow_eq_self (Nat.ne_of_gt hch_pos)
  rw [hprod_eq]
  have hB1 : ∏ p ∈ P_sq, p ^ ((Nat.choose (2 * m) m).factorization p) ≤ (2 * m) ^ (Nat.sqrt (2 *
    m)) := by
    calc ∏ p ∈ P_sq, p ^ ((Nat.choose (2 * m) m).factorization p)
        ≤ ∏ _p ∈ P_sq, (2 * m) := Finset.prod_le_prod fun p hp =>
          Nat.pow_factorization_choose_le (by omega)
      _ = (2 * m) ^ P_sq.card := by simp
      _ ≤ (2 * m) ^ (Nat.sqrt (2 * m)) := Nat.pow_le_pow_right (by omega) (by
          calc P_sq.card ≤ (Finset.Icc 1 (Nat.sqrt (2 * m))).card := Finset.card_filter_le _ _
            _ = Nat.sqrt (2 * m) := by simp)
  have hB2 : ∏ p ∈ P_mid, p ^ ((Nat.choose (2 * m) m).factorization p) ≤ 4 ^ (2 * m / 3) := by
    exact @dyadicPrimeCount_B2 m
  have hB3 : ∏ p ∈ P_hi, p ^ ((Nat.choose (2 * m) m).factorization p) ≤ (2 * m) ^ P_hi.card := by
    calc ∏ p ∈ P_hi, p ^ ((Nat.choose (2 * m) m).factorization p)
        ≤ ∏ _p ∈ P_hi, (2 * m) := Finset.prod_le_prod fun p hp =>
          Nat.pow_factorization_choose_le (by omega)
      _ = (2 * m) ^ P_hi.card := by simp
  exact Nat.mul_le_mul (Nat.mul_le_mul hB1 hB2) hB3


private lemma dyadicPrimeCount_sqrt_le :
    ∀ (m : ℕ),
      (10 : ℕ) ^ (9 : ℕ) ≤ m →
          (0 : ℝ) < (↑m : ℝ) →
            (0 : ℝ) < (2 : ℝ) * (↑m : ℝ) →
              (0 : ℝ) < Real.log ((2 : ℝ) * (↑m : ℝ)) →
                ((↑((2 : ℕ) * m).sqrt : ℝ) + (2 : ℝ)) * Real.log ((2 : ℝ) * (↑m : ℝ)) ≤ (↑m : ℝ) /
                  (12 : ℝ) := by
  intro m hm hm_pos h2m_pos hlog2m_pos
  classical
  have hlog_rpow : Real.log (2 * (m : ℝ)) ≤ 4 * (2 * (m : ℝ)) ^ ((1 : ℝ) / 4) := by
    have h1 : Real.log ((2 * (m : ℝ)) ^ ((1 : ℝ) / 4)) ≤ (2 * (m : ℝ)) ^ ((1 : ℝ) / 4) := by
      linarith [Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos h2m_pos ((1 : ℝ) / 4))]
    rw [Real.log_rpow h2m_pos] at h1; linarith
  have hsq_le : (Nat.sqrt (2 * m) : ℝ) + 2 ≤ 2 * (2 * (m : ℝ)) ^ ((1 : ℝ) / 2) := by
    have hsq : (Nat.sqrt (2 * m) : ℝ) ≤ (2 * (m : ℝ)) ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (Real.nat_sqrt_le_real_sqrt (a := 2 * m))
    have h2_le : (2 : ℝ) ≤ (2 * (m : ℝ)) ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by norm_num) (le_of_lt h2m_pos)]
      have : (10 ^ 9 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    linarith
  have hprod_rpow : (2 * (m : ℝ)) ^ ((1 : ℝ) / 2) * (2 * (m : ℝ)) ^ ((1 : ℝ) / 4) =
      (2 * (m : ℝ)) ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_add h2m_pos]; norm_num
  have h34_le : 8 * (2 * (m : ℝ)) ^ ((3 : ℝ) / 4) ≤ (m : ℝ) / 12 := by
    have hpow4 : (96 * (2 * (m : ℝ)) ^ ((3 : ℝ) / 4)) ^ (4 : ℕ) ≤ (m : ℝ) ^ (4 : ℕ) := by
      rw [mul_pow, ← Real.rpow_natCast ((2 * (m : ℝ)) ^ ((3 : ℝ) / 4)) 4,
        ← Real.rpow_mul (le_of_lt h2m_pos)]
      have h3 : ((3 : ℝ) / 4) * ((4 : ℕ) : ℝ) = (3 : ℝ) := by push_cast; norm_num
      rw [h3, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hm_r : (10 ^ 9 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have h96 : (96 : ℝ) ^ 4 * 8 ≤ (m : ℝ) := by linarith
      have hm3_nn : 0 ≤ (m : ℝ) ^ 3 := by positivity
      calc (96 : ℝ) ^ 4 * (2 * (m : ℝ)) ^ 3
          = ((96 : ℝ) ^ 4 * 8) * (m : ℝ) ^ 3 := by ring
        _ ≤ (m : ℝ) * (m : ℝ) ^ 3 := mul_le_mul_of_nonneg_right h96 hm3_nn
        _ = (m : ℝ) ^ 4 := by ring
    have h96_le : 96 * (2 * (m : ℝ)) ^ ((3 : ℝ) / 4) ≤ (m : ℝ) := by
      by_contra hgt; push Not at hgt
      have : (m : ℝ) ^ (4 : ℕ) < (96 * (2 * (m : ℝ)) ^ ((3 : ℝ) / 4)) ^ (4 : ℕ) :=
        pow_lt_pow_left₀ hgt (le_of_lt hm_pos) (by norm_num)
      linarith
    linarith
  calc ((Nat.sqrt (2 * m) : ℝ) + 2) * Real.log (2 * (m : ℝ))
      ≤ (2 * (2 * (m : ℝ)) ^ ((1 : ℝ) / 2)) * (4 * (2 * (m : ℝ)) ^ ((1 : ℝ) / 4)) :=
        mul_le_mul hsq_le hlog_rpow (le_of_lt hlog2m_pos) (by positivity)
    _ = 8 * (2 * (m : ℝ)) ^ ((3 : ℝ) / 4) := by rw [← hprod_rpow]; ring
    _ ≤ (m : ℝ) / 12 := h34_le


/-- Elementary Chebyshev dyadic prime lower bound: for `m ≥ 10^9`,
`#{p ∈ (m, 2*m] | p.Prime} ≥ m / (4 * log (2 * m))`. -/
private lemma prime_dyadic_card_lower (m : ℕ) (hm : 10 ^ 9 ≤ m) :
    (m : ℝ) / (4 * Real.log (2 * (m : ℝ))) ≤
      (((Finset.Ioc m (2 * m)).filter Nat.Prime).card : ℝ) := by
  let P_sq := (Finset.Icc 1 (Nat.sqrt (2 * m))).filter Nat.Prime
  let P_mid := (Finset.Ioc (Nat.sqrt (2 * m)) (2 * m / 3)).filter Nat.Prime
  let P_hi := (Finset.Ioc m (2 * m)).filter Nat.Prime
  -- The prime factors lie in the three ranges with nonzero valuation.
  have hsub_union : (Nat.choose (2 * m) m).primeFactors ⊆ P_sq ∪ P_mid ∪ P_hi := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hp_le : p ≤ 2 * m := by
      by_contra! hlt
      exact Finsupp.mem_support_iff.mp hp (Nat.factorization_choose_eq_zero_of_lt hlt)
    by_cases h1 : p ≤ Nat.sqrt (2 * m)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hpr.one_le, h1⟩, hpr⟩))
    · by_cases h2 : p ≤ 2 * m / 3
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨by omega, h2⟩, hpr⟩))
      · by_cases h3 : p ≤ m
        · exfalso
          have hv0 := Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul
            (by omega : 2 < m) h3 (by omega)
          rw [Nat.centralBinom_eq_two_mul_choose] at hv0
          exact Finsupp.mem_support_iff.mp hp hv0
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega,
          hp_le⟩, hpr⟩)
  have hch_le : Nat.choose (2 * m) m ≤
      (2 * m) ^ (Nat.sqrt (2 * m)) * 4 ^ (2 * m / 3) * (2 * m) ^ P_hi.card := by
    exact @dyadicPrimeCount_ch_le m hm hsub_union
  -- Combine with 4 ^ m ≤ (2 * m + 1) * Nat.choose (2 * m) m
  have h4m_le : 4 ^ m ≤ (2 * m + 1) * Nat.choose (2 * m) m := by
    simpa only [Nat.centralBinom_eq_two_mul_choose] using
      Nat.four_pow_le_two_mul_add_one_mul_centralBinom m
  have hcomb : 4 ^ m ≤ (2 * m + 1) * ((2 * m) ^ (Nat.sqrt (2 * m)) * 4 ^ (2 * m / 3) * (2 * m) ^
    P_hi.card) :=
    le_trans h4m_le (Nat.mul_le_mul_left _ hch_le)
  -- Take logs in ℝ
  have hm_ge_r : (10 ^ 9 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have h2m_pos : (0 : ℝ) < 2 * (m : ℝ) := by linarith
  have hlog2m_pos : 0 < Real.log (2 * (m : ℝ)) := Real.log_pos (by linarith)
  have hcomb_r : (4 : ℝ) ^ m ≤ ((2 * (m : ℝ) + 1) * ((2 * (m : ℝ)) ^ (Nat.sqrt (2 * m)) *
      (4 : ℝ) ^ (2 * m / 3) * (2 * (m : ℝ)) ^ P_hi.card)) := by
    have := (Nat.cast_le (α := ℝ)).mpr hcomb
    push_cast at this; exact this
  have hlg := Real.log_le_log (pow_pos (by norm_num) m) hcomb_r
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow] at hlg
  have hlog4_ge1 : (1 : ℝ) ≤ Real.log 4 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast;
      linarith [half_le_log_two]
  have h2m3_le : ((2 * m / 3 : ℕ) : ℝ) ≤ (2 : ℝ) / 3 * (m : ℝ) := by
    have : 3 * (2 * m / 3) ≤ 2 * m := Nat.mul_div_le (2 * m) 3
    have : (3 : ℝ) * ((2 * m / 3 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast this
    linarith
  have hlog2m1 : Real.log (2 * (m : ℝ) + 1) ≤ 2 * Real.log (2 * (m : ℝ)) := by
    have h1 : 2 * (m : ℝ) + 1 ≤ (2 * (m : ℝ)) ^ (2 : ℕ) := by nlinarith
    have := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at this; push_cast at this; exact this
  -- Bound (√(2m) + 2) * log (2m) ≤ m / 12 for m ≥ 10^9 using log(2m) ≤ 4 * (2m)^(1/4)
  have hsqrt_le : ((Nat.sqrt (2 * m) : ℝ) + 2) * Real.log (2 * (m : ℝ)) ≤ (m : ℝ) / 12 := by
    exact @dyadicPrimeCount_sqrt_le m hm hm_pos h2m_pos hlog2m_pos
  have h1 : (m : ℝ) / 4 ≤ (P_hi.card : ℝ) * Real.log (2 * (m : ℝ)) := by
    have hdiff : (m : ℝ) / 3 * Real.log 4 ≤ (m : ℝ) * Real.log 4 - ((2 * m / 3 : ℕ) : ℝ) *
      Real.log 4 := by
      have : 0 ≤ Real.log 4 := by linarith
      nlinarith
    have hthird : (m : ℝ) / 3 ≤ (m : ℝ) / 3 * Real.log 4 := by nlinarith
    nlinarith
  exact (div_le_iff₀ (by positivity)).mpr (by linarith)

/-- The auxiliary prime interval for a fixed divisor factor. -/
private def tiltAuxiliaryPrimes (N d : ℕ) : Finset ℕ :=
  (Finset.Ioc (N / (2 * d)) (N / d)).filter Nat.Prime

/-- Dyadic prime lower bound on `(N / (2 * d), N / d]` for `2 * 10^9 ≤ N / d`. -/
private lemma prime_dyadic_div_lower (N d : ℕ) (hd : 1 ≤ d) (hbig : 2 * 10 ^ 9 ≤ N / d) :
    (N : ℝ) / (16 * (d : ℝ) * Real.log (N : ℝ)) ≤
      ((tiltAuxiliaryPrimes N d).card : ℝ) := by
  let m := N / (2 * d)
  have hm_ge : 10 ^ 9 ≤ m := by
    have hdiv : N / (2 * d) = (N / d) / 2 := by rw [mul_comm, ← Nat.div_div_eq_div_mul]
    omega
  have h2m_le : 2 * m ≤ N / d := by
    have hdiv : N / (2 * d) = (N / d) / 2 := by rw [mul_comm, ← Nat.div_div_eq_div_mul]
    have := Nat.mul_div_le (N / d) 2
    omega
  have hsub : (Finset.Ioc m (2 * m)).filter Nat.Prime ⊆ tiltAuxiliaryPrimes N d := by
    intro p hp
    have hI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hI.1, le_trans hI.2 h2m_le⟩,
      (Finset.mem_filter.mp hp).2⟩
  have hcard : (((Finset.Ioc m (2 * m)).filter Nat.Prime).card : ℝ) ≤
      ((tiltAuxiliaryPrimes N d).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hcheb := prime_dyadic_card_lower m hm_ge
  have hN_ge : 2 * 10 ^ 9 ≤ N := le_trans hbig (Nat.div_le_self N d)
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have h2m_le_N : 2 * (m : ℝ) ≤ (N : ℝ) := by
    have : 2 * m ≤ N := le_trans h2m_le (Nat.div_le_self N d)
    exact_mod_cast this
  have hlog_le : Real.log (2 * (m : ℝ)) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < 2 * m)) h2m_le_N
  have hm_lb : (N : ℝ) / (4 * (d : ℝ)) ≤ (m : ℝ) := by
    have hmod := Nat.div_add_mod N (2 * d)
    have hlt := Nat.mod_lt N (by omega : 0 < 2 * d)
    have h2 : N < 2 * d * (m + 1) := by dsimp [m]; nlinarith
    have h3 : N ≤ 4 * d * m := by
      have : m + 1 ≤ 2 * m := by omega
      nlinarith
    have h4 : (N : ℝ) ≤ (m : ℝ) * (4 * (d : ℝ)) := by
      have := (Nat.cast_le (α := ℝ)).mpr h3
      push_cast at this; linarith
    exact (div_le_iff₀ (by positivity)).mpr h4
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlog2m_pos : 0 < Real.log (2 * (m : ℝ)) := Real.log_pos (by exact_mod_cast (by omega : 1 <
    2 * m))
  calc (N : ℝ) / (16 * (d : ℝ) * Real.log (N : ℝ))
      = ((N : ℝ) / (4 * (d : ℝ))) / (4 * Real.log (N : ℝ)) := by ring
    _ ≤ (m : ℝ) / (4 * Real.log (2 * (m : ℝ))) :=
        div_le_div₀ (by positivity) hm_lb (by positivity) (by linarith)
    _ ≤ (((Finset.Ioc m (2 * m)).filter Nat.Prime).card : ℝ) := hcheb
    _ ≤ ((tiltAuxiliaryPrimes N d).card : ℝ) := hcard

/-! ### Section 3: Super-Dyadic Prime Window `P_win J = {p ∈ (2^J, 2^(2J)] | p.Prime}` -/

private def P_win (J : ℕ) : Finset ℕ := (Finset.Ioc (2 ^ J) (2 ^ (2 * J))).filter Nat.Prime

/-- Exact upper & lower bounds on `∑_{p ∈ P_win J} 1 / p` for `J ≥ 30`:
`1 / 16 ≤ ∑ p ∈ P_win J, 1 / p ≤ 4`. -/
private lemma sum_inv_primes_win_bounds (J : ℕ) (hJ : 30 ≤ J) :
    (1 : ℝ) / 16 ≤ ∑ p ∈ P_win J, (1 : ℝ) / (p : ℝ) ∧
    ∑ p ∈ P_win J, (1 : ℝ) / (p : ℝ) ≤ 4 := by
  let I := Finset.Ico J (2 * J)
  let F : ℕ → Finset ℕ := fun r => (Finset.Ioc (2 ^ r) (2 ^ (r + 1))).filter Nat.Prime
  have hdisj : Set.PairwiseDisjoint (I : Set ℕ) F := by
    intro r₁ _ r₂ _ hne
    dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro p hp1 hp2
    have h1 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp1).1
    have h2 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp2).1
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : 2 ^ (r₁ + 1) ≤ 2 ^ r₂ := Nat.pow_le_pow_right (by norm_num) hlt
      omega
    · have : 2 ^ (r₂ + 1) ≤ 2 ^ r₁ := Nat.pow_le_pow_right (by norm_num) hgt
      omega
  have hEq : P_win J = I.biUnion F := by
    ext p
    simp only [P_win, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_biUnion, I, F, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hp⟩
      let r := Nat.log 2 (p - 1)
      have hp_ge2 : 2 ≤ p := hp.two_le
      have hr_le : 2 ^ r ≤ p - 1 := Nat.pow_log_le_self 2 (by omega)
      have hr_lt : p - 1 < 2 ^ (r + 1) := Nat.lt_pow_succ_log_self (by norm_num) (p - 1)
      have hr_ge : J ≤ r := Nat.le_log_of_pow_le (by norm_num) (by omega)
      have hr_ub : r < 2 * J := by
        by_contra hge; push Not at hge
        have : 2 ^ (2 * J) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hge
        omega
      exact ⟨r, ⟨hr_ge, hr_ub⟩, ⟨by omega, by omega⟩, hp⟩
    · rintro ⟨r, ⟨hr1, hr2⟩, ⟨h1, h2⟩, hp⟩
      have hlo : 2 ^ J ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr1
      have hhi : 2 ^ (r + 1) ≤ 2 ^ (2 * J) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact ⟨⟨by omega, by omega⟩, hp⟩
  rw [hEq, Finset.sum_biUnion hdisj]
  have hJ_pos : (0 : ℝ) < (J : ℝ) := by exact_mod_cast (by omega : 0 < J)
  have hIcard : I.card = J := by dsimp [I]; rw [Nat.card_Ico]; omega
  constructor
  · -- Lower bound: each r ∈ [J, 2J) contributes ≥ 1 / (8 * (r + 1)) ≥ 1 / (16 * J)
    have hper : ∀ r ∈ I, (1 : ℝ) / (16 * (J : ℝ)) ≤ ∑ p ∈ F r, (1 : ℝ) / (p : ℝ) := by
      intro r hr
      have hr_ge : J ≤ r := (Finset.mem_Ico.mp hr).1
      have hr_lt : r < 2 * J := (Finset.mem_Ico.mp hr).2
      have h2r_ge : 10 ^ 9 ≤ 2 ^ r := by
        calc 10 ^ 9 ≤ 2 ^ 30 := by norm_num
          _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hcheb := prime_dyadic_card_lower (2 ^ r) h2r_ge
      have hFr_eq : F r = (Finset.Ioc (2 ^ r) (2 * 2 ^ r)).filter Nat.Prime := by
        dsimp [F]; rw [pow_succ, mul_comm]
      rw [hFr_eq]
      have h2r1_pos : (0 : ℝ) < (2 * ((2 ^ r : ℕ) : ℝ)) := by positivity
      have hlog_le : Real.log (2 * ((2 ^ r : ℕ) : ℝ)) ≤ ((r + 1 : ℕ) : ℝ) := by
        have heq : 2 * ((2 ^ r : ℕ) : ℝ) = (2 : ℝ) ^ (r + 1) := by push_cast; rw [pow_succ]; ring
        rw [heq, Real.log_pow]
        have h1 := log_two_le_one
        nlinarith [Nat.cast_nonneg (α := ℝ) (r + 1)]
      have hlog_pos : 0 < Real.log (2 * ((2 ^ r : ℕ) : ℝ)) := Real.log_pos (by
        have : (1 : ℝ) < ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < 2 ^ r)
        linarith)
      have hr1_le : ((r + 1 : ℕ) : ℝ) ≤ 2 * (J : ℝ) := by exact_mod_cast (by omega : r + 1 ≤ 2 * J)
      calc (1 : ℝ) / (16 * (J : ℝ))
          ≤ (((2 ^ r : ℕ) : ℝ) / (4 * Real.log (2 * ((2 ^ r : ℕ) : ℝ)))) / (2 * ((2 ^ r : ℕ) : ℝ))
            := by
            have h1 : (((2 ^ r : ℕ) : ℝ) / (4 * Real.log (2 * ((2 ^ r : ℕ) : ℝ)))) / (2 * ((2 ^ r
              : ℕ) : ℝ)) =
                1 / (8 * Real.log (2 * ((2 ^ r : ℕ) : ℝ))) := by
              have h2r_ne : ((2 ^ r : ℕ) : ℝ) ≠ 0 := by positivity
              field_simp [h2r_ne, ne_of_gt hlog_pos]; ring
            rw [h1]
            exact one_div_le_one_div_of_le (by positivity) (by linarith)
        _ ≤ (((Finset.Ioc (2 ^ r) (2 * 2 ^ r)).filter Nat.Prime).card : ℝ) / (2 * ((2 ^ r : ℕ) :
          ℝ)) :=
            div_le_div_of_nonneg_right hcheb (le_of_lt h2r1_pos)
        _ = ∑ _p ∈ (Finset.Ioc (2 ^ r) (2 * 2 ^ r)).filter Nat.Prime, (1 : ℝ) / (2 * ((2 ^ r : ℕ)
          : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
        _ ≤ ∑ p ∈ (Finset.Ioc (2 ^ r) (2 * 2 ^ r)).filter Nat.Prime, (1 : ℝ) / (p : ℝ) :=
            Finset.sum_le_sum fun p hp => one_div_le_one_div_of_le
              (by exact_mod_cast (Finset.mem_filter.mp hp).2.pos)
              (by exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2)
    calc (1 : ℝ) / 16 = (I.card : ℝ) * ((1 : ℝ) / (16 * (J : ℝ))) := by
          rw [hIcard]; field_simp [ne_of_gt hJ_pos]
      _ = ∑ _r ∈ I, (1 : ℝ) / (16 * (J : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ r ∈ I, ∑ p ∈ F r, (1 : ℝ) / (p : ℝ) := Finset.sum_le_sum hper
  · -- Upper bound: each r ∈ [J, 2J) contributes ≤ 4 / r ≤ 4 / J
    calc ∑ r ∈ I, ∑ p ∈ F r, (1 : ℝ) / (p : ℝ)
        ≤ ∑ r ∈ I, (4 : ℝ) / (r : ℝ) :=
          Finset.sum_le_sum fun r hr =>
            sum_inv_primes_dyadic_le r (by have := (Finset.mem_Ico.mp hr).1; omega)
      _ ≤ ∑ _r ∈ I, (4 : ℝ) / (J : ℝ) := Finset.sum_le_sum fun r hr =>
          div_le_div_of_nonneg_left (by norm_num) hJ_pos (by exact_mod_cast (Finset.mem_Ico.mp
            hr).1)
      _ = (I.card : ℝ) * ((4 : ℝ) / (J : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = 4 := by rw [hIcard]; field_simp [ne_of_gt hJ_pos]

/-! ### Bernoulli weights on subsets of primes -/

/-- Mass of a subset in independent Bernoulli choices. -/
private noncomputable def bernoulliMass (P : Finset ℕ) (q : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  (∏ p ∈ S, q p) * (∏ p ∈ P \ S, (1 - q p))

private lemma bernoulliMass_nonneg {P : Finset ℕ} {q : ℕ → ℝ}
    (hq0 : ∀ p ∈ P, 0 ≤ q p) (hq1 : ∀ p ∈ P, q p ≤ 1) {S : Finset ℕ} (hS : S ⊆ P) :
    0 ≤ bernoulliMass P q S :=
  mul_nonneg (Finset.prod_nonneg fun p hp => hq0 p (hS hp))
    (Finset.prod_nonneg fun p hp => sub_nonneg.mpr (hq1 p (Finset.mem_sdiff.mp hp).1))

/-- Exact product-measure normalization on `P.powerset`. -/
private lemma powerset_prod_bernoulli_sum_eq_one (P : Finset ℕ) (q : ℕ → ℝ) :
    ∑ S ∈ P.powerset, bernoulliMass P q S = 1 := by
  classical
  have h := Finset.prod_add (s := P) (f := fun p => q p) (g := fun p => 1 - q p)
  have h1 : ∏ p ∈ P, (q p + (1 - q p)) = 1 := Finset.prod_eq_one fun p _ => by ring
  rw [h1] at h
  exact h.symm

/-- Adjoining a fixed subset multiplies every residual Bernoulli weight by its inclusion weight. -/
private lemma sum_bernoulli_adjoin (P S₀ : Finset ℕ) (choices : Finset (Finset ℕ))
    (hchoices : choices ⊆ (P \ S₀).powerset) (q : ℕ → ℝ) :
    ∑ S ∈ choices.image (fun T => S₀ ∪ T), bernoulliMass P q S =
      (∏ p ∈ S₀, q p) * ∑ T ∈ choices, bernoulliMass (P \ S₀) q T := by
  classical
  let R := P \ S₀
  have hdisj : ∀ T ∈ choices, Disjoint S₀ T := fun T hT =>
    Finset.disjoint_sdiff.mono_right (Finset.mem_powerset.mp (hchoices hT))
  have hinj : Set.InjOn (fun T => S₀ ∪ T) (choices : Set (Finset ℕ)) := by
    intro T₁ hT₁ T₂ hT₂ hEq
    have hd1 := hdisj T₁ hT₁
    have hd2 := hdisj T₂ hT₂
    calc T₁ = (S₀ ∪ T₁) \ S₀ := (Finset.union_sdiff_cancel_left hd1).symm
      _ = (S₀ ∪ T₂) \ S₀ := by dsimp only at hEq; rw [hEq]
      _ = T₂ := Finset.union_sdiff_cancel_left hd2
  rw [Finset.sum_image (fun T₁ hT₁ T₂ hT₂ hEq => hinj hT₁ hT₂ hEq)]
  have hterm : ∀ T ∈ choices,
      bernoulliMass P q (S₀ ∪ T) = (∏ p ∈ S₀, q p) * bernoulliMass R q T := by
    intro T hT
    have h1 : ∏ p ∈ S₀ ∪ T, q p = (∏ p ∈ S₀, q p) * (∏ p ∈ T, q p) :=
      Finset.prod_union (hdisj T hT)
    have h2 : P \ (S₀ ∪ T) = R \ T := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_union, R]; tauto
    rw [bernoulliMass, h1, h2, bernoulliMass]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]

/-- Exact subset-conditioning identity on `P.powerset`: for `S₀ ⊆ P`,
`∑ S ∈ P.powerset.filter (S₀ ⊆ ·), μ(S) = ∏ p ∈ S₀, q p`. -/
private lemma powerset_prod_bernoulli_filter_subset (P S₀ : Finset ℕ) (hS₀ : S₀ ⊆ P) (q : ℕ → ℝ) :
    ∑ S ∈ P.powerset.filter (fun S => S₀ ⊆ S), bernoulliMass P q S =
      ∏ p ∈ S₀, q p := by
  classical
  let R := P \ S₀
  have himg : P.powerset.filter (fun S => S₀ ⊆ S) = R.powerset.image (fun T => S₀ ∪ T) := by
    ext S; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image, R]
    constructor
    · rintro ⟨hSP, hS₀S⟩
      refine ⟨S \ S₀, Finset.sdiff_subset_sdiff hSP (Finset.Subset.refl _),
        Finset.union_sdiff_of_subset hS₀S⟩
    · rintro ⟨T, hTR, rfl⟩
      exact ⟨Finset.union_subset hS₀ (Finset.Subset.trans hTR Finset.sdiff_subset),
        Finset.subset_union_left⟩
  rw [himg, sum_bernoulli_adjoin P S₀ R.powerset (Finset.Subset.refl _) q,
    powerset_prod_bernoulli_sum_eq_one, mul_one]

/-- The expectation of the additive weight under independent Bernoulli choices. -/
private lemma powerset_prod_bernoulli_expect (P : Finset ℕ) (q f : ℕ → ℝ) :
    ∑ S ∈ P.powerset, bernoulliMass P q S * (∑ p ∈ S, f p) =
      ∑ p ∈ P, q p * f p := by
  classical
  have h1 : ∀ S ∈ P.powerset,
      bernoulliMass P q S * (∑ p ∈ S, f p) =
        ∑ p ∈ P, if p ∈ S then bernoulliMass P q S * f p else 0 := by
    intro S hS
    rw [Finset.mul_sum, ← Finset.sum_filter]
    have hEq : P.filter (fun p => p ∈ S) = S := by
      ext p; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_powerset.mp
        hS h, h⟩⟩
    rw [hEq]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.sum_filter, ← Finset.sum_mul]
  have hfilt : P.powerset.filter (fun S => p ∈ S) = P.powerset.filter (fun S => {p} ⊆ S) := by
    ext S; simp only [Finset.mem_filter, Finset.singleton_subset_iff]
  rw [hfilt, powerset_prod_bernoulli_filter_subset P {p} (Finset.singleton_subset_iff.mpr hp) q,
    Finset.prod_singleton]

/-- Markov truncation lemma on `P.powerset`: if `0 ≤ q p ≤ 1`, `0 ≤ f p`, `0 < B`, and
`∑ p ∈ P, q p * f p ≤ B / 2`, then the subset `{S ⊆ P | ∑ p ∈ S, f p ≤ B}` has total
measure `≥ 1 / 2`. -/
private lemma powerset_prod_bernoulli_markov (P : Finset ℕ) (q f : ℕ → ℝ) (B : ℝ)
    (hq0 : ∀ p ∈ P, 0 ≤ q p) (hq1 : ∀ p ∈ P, q p ≤ 1)
    (hf : ∀ p ∈ P, 0 ≤ f p) (hB : 0 < B)
    (hexp : ∑ p ∈ P, q p * f p ≤ B / 2) :
    (1 : ℝ) / 2 ≤ ∑ S ∈ P.powerset.filter (fun S => ∑ p ∈ S, f p ≤ B),
      bernoulliMass P q S := by
  classical
  let μ := bernoulliMass P q
  have hμ_nn : ∀ S ∈ P.powerset, 0 ≤ μ S := fun S hS =>
    bernoulliMass_nonneg hq0 hq1 (Finset.mem_powerset.mp hS)
  let Bad := P.powerset.filter (fun S => ¬ ∑ p ∈ S, f p ≤ B)
  have hbad : (∑ S ∈ Bad, μ S) * B ≤ ∑ p ∈ P, q p * f p := by
    calc (∑ S ∈ Bad, μ S) * B = ∑ S ∈ Bad, μ S * B := by rw [Finset.sum_mul]
      _ ≤ ∑ S ∈ Bad, μ S * (∑ p ∈ S, f p) :=
          Finset.sum_le_sum fun S hS => mul_le_mul_of_nonneg_left
            (le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hS).2)) (hμ_nn S (Finset.mem_filter.mp
              hS).1)
      _ ≤ ∑ S ∈ P.powerset, μ S * (∑ p ∈ S, f p) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun S hS _ =>
            mul_nonneg (hμ_nn S hS) (Finset.sum_nonneg fun p hp => hf p (Finset.mem_powerset.mp hS
              hp))
      _ = ∑ p ∈ P, q p * f p := powerset_prod_bernoulli_expect P q f
  have hbad_half : ∑ S ∈ Bad, μ S ≤ 1 / 2 := by nlinarith
  have hsplit := Finset.sum_filter_add_sum_filter_not P.powerset (fun S => ∑ p ∈ S, f p ≤ B) μ
  dsimp only [μ] at hsplit hbad_half
  rw [powerset_prod_bernoulli_sum_eq_one P q] at hsplit
  dsimp [Bad] at hbad_half
  linarith

/-- Truncated Euler sum lower bound via powerset Markov: if `0 ≤ r p ≤ 1` for `p ∈ P` and
`∑ p ∈ P, r p * log p ≤ B / 2` (`B > 0`), then
`∑ S ∈ P.powerset.filter (fun S => ∑ p ∈ S, log p ≤ B), ∏ p ∈ S, r p`
is at least `(1/2) * exp ((1/2) * ∑ p ∈ P, r p)`. -/
lemma truncated_euler_sum_lower (P : Finset ℕ) (r : ℕ → ℝ) (B : ℝ)
    (hP : ∀ p ∈ P, 2 ≤ p)
    (hr0 : ∀ p ∈ P, 0 ≤ r p) (hr1 : ∀ p ∈ P, r p ≤ 1)
    (hB : 0 < B)
    (hlog_sum : ∑ p ∈ P, r p * Real.log (p : ℝ) ≤ B / 2) :
    (1 : ℝ) / 2 * Real.exp ((1 : ℝ) / 2 * ∑ p ∈ P, r p) ≤
      ∑ S ∈ P.powerset.filter (fun S : Finset ℕ => ∑ p ∈ S, Real.log (p : ℝ) ≤ B), ∏ p ∈ S, r p :=
        by
  classical
  let q : ℕ → ℝ := fun p => r p / (1 + r p)
  have h1r_pos : ∀ p ∈ P, 0 < 1 + r p := fun p hp => by linarith [hr0 p hp]
  have hq0 : ∀ p ∈ P, 0 ≤ q p := fun p hp => div_nonneg (hr0 p hp) (le_of_lt (h1r_pos p hp))
  have hq1 : ∀ p ∈ P, q p ≤ 1 := fun p hp =>
    (div_le_one (h1r_pos p hp)).mpr (by linarith [hr0 p hp])
  have hq_le_r : ∀ p ∈ P, q p ≤ r p := fun p hp => by
    dsimp [q]; rw [div_le_iff₀ (h1r_pos p hp)]; nlinarith [hr0 p hp]
  have hlog_nn : ∀ p ∈ P, 0 ≤ Real.log (p : ℝ) := fun p hp =>
    Real.log_nonneg (by exact_mod_cast (by have := hP p hp; omega : 1 ≤ p))
  have hexp : ∑ p ∈ P, q p * Real.log (p : ℝ) ≤ B / 2 :=
    le_trans (Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right (hq_le_r p hp) (hlog_nn p
      hp)) hlog_sum
  have hmarkov := powerset_prod_bernoulli_markov P q (fun p => Real.log (p : ℝ)) B hq0 hq1 hlog_nn
    hB hexp
  have hZ_eq : ∀ S ∈ P.powerset,
      (∏ p ∈ P, (1 + r p)) * bernoulliMass P q S = ∏ p ∈ S, r p := by
    intro S hS
    have hsplit' : ∏ p ∈ P, (1 + r p) = (∏ p ∈ S, (1 + r p)) * (∏ p ∈ P \ S, (1 + r p)) := by
      rw [← Finset.prod_sdiff (Finset.mem_powerset.mp hS), mul_comm]
    rw [hsplit', bernoulliMass]
    have hA : (∏ p ∈ S, (1 + r p)) * (∏ p ∈ S, q p) = ∏ p ∈ S, r p := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      dsimp [q]; exact mul_div_cancel₀ _ (ne_of_gt (h1r_pos p (Finset.mem_powerset.mp hS hp)))
    have hB' : (∏ p ∈ P \ S, (1 + r p)) * (∏ p ∈ P \ S, (1 - q p)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun p hp => ?_
      have hpP := (Finset.mem_sdiff.mp hp).1
      dsimp [q]; field_simp [ne_of_gt (h1r_pos p hpP)]; ring
    calc ((∏ p ∈ S, (1 + r p)) * (∏ p ∈ P \ S, (1 + r p))) * ((∏ p ∈ S, q p) * (∏ p ∈ P \ S,
      (1 - q p)))
        = ((∏ p ∈ S, (1 + r p)) * (∏ p ∈ S, q p)) * ((∏ p ∈ P \ S, (1 + r p)) * (∏ p ∈ P \ S,
          (1 - q p))) := by ring
      _ = (∏ p ∈ S, r p) * 1 := by rw [hA, hB']
      _ = ∏ p ∈ S, r p := mul_one _
  have hZ_ge : Real.exp ((1 : ℝ) / 2 * ∑ p ∈ P, r p) ≤ ∏ p ∈ P, (1 + r p) := by
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun p _ => le_of_lt (Real.exp_pos _)) fun p hp => ?_
    rw [show (1 : ℝ) / 2 * r p = r p / 2 by ring]
    exact exp_half_le_one_add (hr0 p hp) (hr1 p hp)
  have hZ_nn : 0 ≤ ∏ p ∈ P, (1 + r p) := Finset.prod_nonneg fun p hp => le_of_lt (h1r_pos p hp)
  calc (1 : ℝ) / 2 * Real.exp ((1 : ℝ) / 2 * ∑ p ∈ P, r p)
      ≤ (1 : ℝ) / 2 * ∏ p ∈ P, (1 + r p) := mul_le_mul_of_nonneg_left hZ_ge (by norm_num)
    _ ≤ (∑ S ∈ P.powerset.filter (fun S : Finset ℕ => ∑ p ∈ S, Real.log (p : ℝ) ≤ B),
          bernoulliMass P q S) * ∏ p ∈ P, (1 + r p) :=
        mul_le_mul_of_nonneg_right hmarkov hZ_nn
    _ = ∑ S ∈ P.powerset.filter (fun S : Finset ℕ => ∑ p ∈ S, Real.log (p : ℝ) ≤ B),
          (∏ p ∈ P, (1 + r p)) * bernoulliMass P q S := by
        rw [mul_comm, Finset.mul_sum]
    _ = ∑ S ∈ P.powerset.filter (fun S : Finset ℕ => ∑ p ∈ S, Real.log (p : ℝ) ≤ B), ∏ p ∈ S, r p :=
        Finset.sum_congr rfl fun S hS => hZ_eq S (Finset.mem_filter.mp hS).1

/-- Unique recovery of `(S₀, p₀)` from `(∏ p ∈ S₀, p) * p₀` when `S₀` consists of primes `≤ M`
and `p₀ > M` is prime. -/
private lemma prod_primes_mul_large_prime_inj (M : ℕ)
    {S₁ S₂ : Finset ℕ} {p₁ p₂ : ℕ}
    (hS₁ : ∀ p ∈ S₁, p.Prime) (hS₂ : ∀ p ∈ S₂, p.Prime ∧ p ≤ M)
    (hp₁ : p₁.Prime ∧ M < p₁) (hp₂ : p₂.Prime)
    (hEq : (∏ p ∈ S₁, p) * p₁ = (∏ p ∈ S₂, p) * p₂) :
    S₁ = S₂ ∧ p₁ = p₂ := by
  have hp1_not_S2 : ∀ q ∈ S₂, ¬ p₁ ∣ q := fun q hq hdvd => by
    have hq_pr := (hS₂ q hq).1
    have := (Nat.prime_dvd_prime_iff_eq hp₁.1 hq_pr).mp hdvd
    have := (hS₂ q hq).2; omega
  have hp1_not_prod2 : ¬ p₁ ∣ ∏ q ∈ S₂, q := by
    intro hdvd
    rcases (Prime.dvd_finsetProd_iff hp₁.1.prime id).mp hdvd with ⟨q, hq, hq_dvd⟩
    exact hp1_not_S2 q hq hq_dvd
  have hp1_dvd : p₁ ∣ (∏ q ∈ S₂, q) * p₂ := ⟨∏ q ∈ S₁, q, by rw [← hEq, mul_comm]⟩
  have hp1_eq_p2 : p₁ = p₂ := by
    rcases hp₁.1.dvd_mul.mp hp1_dvd with h1 | h2
    · exact (hp1_not_prod2 h1).elim
    · exact (Nat.prime_dvd_prime_iff_eq hp₁.1 hp₂).mp h2
  subst hp1_eq_p2
  have hprod_eq : ∏ p ∈ S₁, p = ∏ p ∈ S₂, p := Nat.eq_of_mul_eq_mul_right hp₁.1.pos hEq
  have factors := congrArg Nat.primeFactors hprod_eq
  rw [Nat.primeFactors_prod hS₁,
    Nat.primeFactors_prod (fun p hp => (hS₂ p hp).1)] at factors
  exact ⟨factors, rfl⟩


/-- Subsets in the prime window below the logarithmic conditioning cutoff. -/
private noncomputable def tiltSmallSubsets (P : Finset ℕ) (L : ℝ) : Finset (Finset ℕ) :=
  P.powerset.filter (fun S => ∑ p ∈ S, Real.log (p : ℝ) ≤ L / 10)

/-- Subsets in the prime window whose product meets the cutoff. -/
private def tiltSupport (P : Finset ℕ) (Tmax : ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter (fun S => ∏ p ∈ S, p ≤ Tmax)

/-- Divisor weight obtained from the truncated prime-window mass. -/
private noncomputable def tiltWeight (N : ℕ) (choices : Finset (Finset ℕ))
    (mass : Finset ℕ → ℝ) (t : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ S ∈ choices with (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S, p) ≤ N, mass S

/-- A bound on a sum of logarithms gives a bound on the product of positive factors. -/
private lemma prod_le_rpow_of_sum_log_le {N a : ℝ} {S : Finset ℕ}
    (hN : 0 < N) (hS : ∀ p ∈ S, 0 < p)
    (h : ∑ p ∈ S, Real.log (p : ℝ) ≤ a * Real.log N) :
    ((∏ p ∈ S, p : ℕ) : ℝ) ≤ N ^ a := by
  have hp : (0 : ℝ) < ((∏ p ∈ S, p : ℕ) : ℝ) := by exact_mod_cast Finset.prod_pos hS
  have he : Real.log ((∏ p ∈ S, p : ℕ) : ℝ) = ∑ p ∈ S, Real.log (p : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (hS p hp).ne'
  rw [← Real.exp_log hp, he, Real.rpow_def_of_pos hN]
  exact Real.exp_le_exp.mpr (by rwa [mul_comm])

/-- A small divisor leaves a large real quotient. -/
private lemma quotient_ge_rpow {N d : ℝ} (hN : 0 < N) (hd : 0 < d)
    (hsmall : d ≤ N ^ ((1 : ℝ) / 10)) : N ^ ((9 : ℝ) / 10) ≤ N / d := by
  rw [le_div_iff₀ hd]
  calc N ^ ((9 : ℝ) / 10) * d ≤ N ^ ((9 : ℝ) / 10) * N ^ ((1 : ℝ) / 10) :=
    mul_le_mul_of_nonneg_left hsmall (by positivity)
  _ = N := by rw [← Real.rpow_add hN]; norm_num

private lemma randomTilt_card_le (N H d : ℕ) :
    ((Finset.Icc 1 H).filter (fun t => d ∣ t ∧ t / d ≤ N)).card ≤ N := by
  have hmaps : ∀ t ∈ (Finset.Icc 1 H).filter (fun t => d ∣ t ∧ t / d ≤ N),
      t / d ∈ Finset.Icc 1 N := by
    intro t ht
    have ht1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1).1
    have hdvd := (Finset.mem_filter.mp ht).2.1
    have hle := (Finset.mem_filter.mp ht).2.2
    have hpos : 1 ≤ t / d := by
      have hmul := Nat.mul_div_cancel' hdvd
      by_contra h0; push Not at h0
      have : t / d = 0 := Nat.lt_one_iff.mp h0
      rw [this, mul_zero] at hmul; omega
    exact Finset.mem_Icc.mpr ⟨hpos, hle⟩
  have hinj : Set.InjOn (fun t => t / d)
      (((Finset.Icc 1 H).filter (fun t => d ∣ t ∧ t / d ≤ N)) : Set ℕ) := by
    intro t₁ ht₁ t₂ ht₂ hEq; dsimp only at hEq
    calc t₁ = d * (t₁ / d) := (Nat.mul_div_cancel' (Finset.mem_filter.mp
      ht₁).2.1).symm
      _ = d * (t₂ / d) := by rw [hEq]
      _ = t₂ := Nat.mul_div_cancel' (Finset.mem_filter.mp ht₂).2.1
  calc ((Finset.Icc 1 H).filter (fun t => d ∣ t ∧ t / d ≤ N)).card
      ≤ (Finset.Icc 1 N).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = N := by simp


private lemma randomTilt_w_sum (N H : ℕ) (hN_pos : 0 < (N : ℝ))
    (P : Finset ℕ) (q : ℕ → ℝ) (GoodS : Finset (Finset ℕ))
    (hGoodS : GoodS ⊆ P.powerset) (hμ_nn : ∀ S ∈ P.powerset, 0 ≤ bernoulliMass P q S) :
    let μ := bernoulliMass P q
    let w := tiltWeight N GoodS μ
    ∑ t ∈ Finset.Icc 1 H, w t ≤ 1 := by
  intro μ w
  classical
  have hswap : ∑ t ∈ Finset.Icc 1 H, w t =
      ((N : ℝ))⁻¹ * ∑ S ∈ GoodS,
        (((Finset.Icc 1 H).filter (fun t => (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S, p) ≤ N)).card : ℝ) *
          μ S := by
    dsimp only [w, tiltWeight]
    rw [← Finset.mul_sum, sum_filtered_weights]
  rw [hswap]
  calc ((N : ℝ))⁻¹ * ∑ S ∈ GoodS,
          (((Finset.Icc 1 H).filter (fun t => (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S, p) ≤ N)).card : ℝ)
            * μ S
      ≤ ((N : ℝ))⁻¹ * ∑ S ∈ GoodS, (N : ℝ) * μ S := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun S hS => ?_) (by positivity)
        have hcount := randomTilt_card_le N H (∏ p ∈ S, p)
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount)
          (hμ_nn S (hGoodS hS))
    _ = ∑ S ∈ GoodS, μ S := by rw [← Finset.mul_sum, inv_mul_cancel_left₀ (ne_of_gt hN_pos)]
    _ ≤ ∑ S ∈ P.powerset, μ S := Finset.sum_le_sum_of_subset_of_nonneg hGoodS
      fun S hS _ => hμ_nn S hS
    _ = 1 := powerset_prod_bernoulli_sum_eq_one P q


private lemma randomTilt_cond_good :
    ∀ (N J : ℕ),
        (100 : ℝ) ≤ Real.log (↑N : ℝ) →
            (0 : ℝ) < (↑N : ℝ) →
              let P : Finset ℕ := P_win J;
              let Y : ℝ := (↑((2 : ℕ) ^ J) : ℝ);
              let q : ℕ → ℝ := fun p => Y / (↑p : ℝ);
              (∀ p ∈ P, Nat.Prime p ∧ (2 : ℕ) ^ J < p ∧ p ≤ (2 : ℕ) ^ ((2 : ℕ) * J)) →
                (∀ p ∈ P, (0 : ℝ) ≤ q p) →
                  (∀ p ∈ P, q p ≤ (1 : ℝ)) →
                    let μ := bernoulliMass P q;
                    (∀ S ∈ P.powerset, (0 : ℝ) ≤ μ S) →
                      let Tmax : ℕ := ⌊(↑N : ℝ) ^ (1 / 3 : ℝ)⌋₊;
                      let GoodS := tiltSupport P Tmax;
                      let L : ℝ := Real.log (↑N : ℝ);
                        (∀ p ∈ P, (0 : ℝ) ≤ Real.log (↑p : ℝ)) →
                          ∑ p ∈ P, q p * Real.log (↑p : ℝ) ≤ L / (10 : ℝ) →
                            let SmallS₀ : Finset (Finset ℕ) :=
                              tiltSmallSubsets P L;
                            ∀ S₀ ∈ SmallS₀, (1 / 2 : ℝ) * ∏ p ∈ S₀, q p ≤ ∑ S ∈ GoodS with S₀ ⊆ S,
                              μ S := by
  intro N J hlogN_ge hN_pos P Y q hP_prop hq0 hq1 μ hμ_nn Tmax GoodS L hlogp_nn
    hqlog_sum SmallS₀
  classical
  intro S₀ hS₀
  have hS₀P : S₀ ⊆ P := Finset.mem_powerset.mp (Finset.mem_filter.mp hS₀).1
  let R := P \ S₀
  have hqlog_R : ∑ p ∈ R, q p * Real.log (p : ℝ) ≤ (L / 5) / 2 := by
    calc ∑ p ∈ R, q p * Real.log (p : ℝ)
        ≤ ∑ p ∈ P, q p * Real.log (p : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
          Finset.sdiff_subset
          fun p hp _ => mul_nonneg (hq0 p hp) (hlogp_nn p hp)
      _ ≤ L / 10 := hqlog_sum
      _ = (L / 5) / 2 := by ring
  have hmk := powerset_prod_bernoulli_markov R q (fun p => Real.log (p : ℝ)) (L / 5)
    (fun p hp => hq0 p (Finset.mem_sdiff.mp hp).1) (fun p hp => hq1 p (Finset.mem_sdiff.mp hp).1)
    (fun p hp => hlogp_nn p (Finset.mem_sdiff.mp hp).1) (by linarith) hqlog_R
  let GoodT := R.powerset.filter (fun T : Finset ℕ => ∑ p ∈ T, Real.log (p : ℝ) ≤ L / 5)
  -- Every T ∈ GoodT maps via T ↦ S₀ ∪ T into GoodS.filter (S₀ ⊆ ·)
  have hmaps : ∀ T ∈ GoodT, S₀ ∪ T ∈ GoodS.filter (fun S => S₀ ⊆ S) := by
    intro T hT
    have hTR : T ⊆ R := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    have hdisj : Disjoint S₀ T := Finset.disjoint_sdiff.mono_right hTR
    have hSP : S₀ ∪ T ⊆ P := Finset.union_subset hS₀P (Finset.Subset.trans hTR Finset.sdiff_subset)
    have hlog_sum : ∑ p ∈ S₀ ∪ T, Real.log (p : ℝ) ≤ (3 : ℝ) / 10 * L := by
      rw [Finset.sum_union hdisj]
      linarith [(Finset.mem_filter.mp hS₀).2, (Finset.mem_filter.mp hT).2]
    have hprod_le : ((∏ p ∈ S₀ ∪ T, p : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by
      exact prod_le_rpow_of_sum_log_le hN_pos (fun p hp => (hP_prop p (hSP hp)).1.pos)
        (by change _ ≤ (1 : ℝ) / 3 * L; linarith)
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSP,
      Nat.le_floor hprod_le⟩,
      Finset.subset_union_left⟩
  have hsub_img : GoodT.image (fun T => S₀ ∪ T) ⊆ GoodS.filter (fun S => S₀ ⊆ S) := by
    intro S hS; rcases Finset.mem_image.mp hS with ⟨T, hT, rfl⟩; exact hmaps T hT
  calc (1 : ℝ) / 2 * (∏ p ∈ S₀, q p)
      ≤ (∏ p ∈ S₀, q p) * ∑ T ∈ GoodT, bernoulliMass R q T := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left hmk (Finset.prod_nonneg fun p hp =>
          hq0 p (hS₀P hp))
    _ = ∑ S ∈ GoodT.image (fun T => S₀ ∪ T), μ S :=
        (sum_bernoulli_adjoin P S₀ GoodT (Finset.filter_subset _ _) q).symm
    _ ≤ ∑ S ∈ GoodS.filter (fun S => S₀ ⊆ S), μ S :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub_img fun S hS _ =>
          hμ_nn S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1


private lemma randomTilt_count :
    ∀ (N J : ℕ),
      let H : ℕ := ⌊(↑N : ℝ) ^ (4 / 3 : ℝ)⌋₊;
      let P : Finset ℕ := P_win J;
      (∀ p ∈ P, Nat.Prime p ∧ (2 : ℕ) ^ J < p ∧ p ≤ (2 : ℕ) ^ ((2 : ℕ) * J)) →
        let Tmax : ℕ := ⌊(↑N : ℝ) ^ (1 / 3 : ℝ)⌋₊;
        let GoodS := tiltSupport P Tmax;
        Tmax * N ≤ H →
          ∀ (S₀ : Finset ℕ) (p₀ : ℕ),
            let d₁ : ℕ := ∏ p ∈ S₀, p;
            0 < p₀ →
              ∀ S ∈ {S ∈ GoodS | S₀ ⊆ S},
                N / p₀ ≤ {t ∈ Finset.Icc (1 : ℕ) H | d₁ * p₀ ∣ t ∧ ∏ p ∈ S, p ∣ t ∧ t / ∏ p ∈ S,
                  p ≤ N}.card := by
  intro N J H P hP_prop Tmax GoodS hTmax_mul S₀ p₀ d₁ hp₀
  classical
  intro S hS
  have hS_good := (Finset.mem_filter.mp hS).1
  have hS₀S : S₀ ⊆ S := (Finset.mem_filter.mp hS).2
  set T₁ := ∏ p ∈ S, p
  have hT₁_pos : 1 ≤ T₁ := Finset.one_le_prod₀ fun p hp =>
    (hP_prop p (Finset.mem_powerset.mp (Finset.mem_filter.mp hS_good).1 hp)).1.one_le
  have hT₁_le : T₁ ≤ Tmax := (Finset.mem_filter.mp hS_good).2
  have hd₁_dvd_T₁ : d₁ ∣ T₁ := Finset.prod_dvd_prod_of_subset S₀ S id hS₀S
  have hmaps : ∀ k ∈ Finset.Icc 1 (N / p₀),
      T₁ * (k * p₀) ∈ (Finset.Icc 1 H).filter (fun t => d₁ * p₀ ∣ t ∧ T₁ ∣ t ∧ t / T₁ ≤ N) := by
    intro k hk
    have hk_I := Finset.mem_Icc.mp hk
    have hkp₀_le : k * p₀ ≤ N := le_trans (Nat.mul_le_mul_right p₀ hk_I.2) (Nat.div_mul_le_self N
      p₀)
    have ht_le : T₁ * (k * p₀) ≤ H := le_trans (Nat.mul_le_mul hT₁_le hkp₀_le) hTmax_mul
    have ht_ge1 : 1 ≤ T₁ * (k * p₀) := Nat.mul_pos hT₁_pos (Nat.mul_pos hk_I.1 hp₀)
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ht_ge1, ht_le⟩, ?_, dvd_mul_right T₁ _, ?_⟩
    · rcases hd₁_dvd_T₁ with ⟨c, hc⟩
      exact ⟨c * k, by rw [hc]; ring⟩
    · rwa [Nat.mul_div_cancel_left _ hT₁_pos]
  have hinj : Set.InjOn (fun k => T₁ * (k * p₀)) (Finset.Icc 1 (N / p₀) : Set ℕ) := by
    intro k₁ _ k₂ _ hEq; dsimp only at hEq
    exact Nat.eq_of_mul_eq_mul_right hp₀ (Nat.eq_of_mul_eq_mul_left hT₁_pos hEq)
  calc N / p₀ = (Finset.Icc 1 (N / p₀)).card := by simp
    _ ≤ _ := Finset.card_le_card_of_injOn _ hmaps hinj


private lemma randomTilt_p_w_lb :
    ∀ (N J : ℕ),
      let H : ℕ := ⌊(↑N : ℝ) ^ (4 / 3 : ℝ)⌋₊;
        let P : Finset ℕ := P_win J;
        let Y : ℝ := (↑((2 : ℕ) ^ J) : ℝ);
        let q : ℕ → ℝ := fun p => Y / (↑p : ℝ);
        (∀ p ∈ P, Nat.Prime p ∧ (2 : ℕ) ^ J < p ∧ p ≤ (2 : ℕ) ^ ((2 : ℕ) * J)) →
          let μ := bernoulliMass P q;
          (∀ S ∈ P.powerset, (0 : ℝ) ≤ μ S) →
            let Tmax : ℕ := ⌊(↑N : ℝ) ^ (1 / 3 : ℝ)⌋₊;
            let GoodS := tiltSupport P Tmax;
            let w := tiltWeight N GoodS μ;
            Tmax * N ≤ H →
              let L : ℝ := Real.log (↑N : ℝ);
                let SmallS₀ : Finset (Finset ℕ) := tiltSmallSubsets P L;
                (∀ S₀ ∈ SmallS₀, (1 / 2 : ℝ) * ∏ p ∈ S₀, q p ≤ ∑ S ∈ GoodS with S₀ ⊆ S, μ S) →
                  ∀ S₀ ∈ SmallS₀,
                    ∀ p₀ ∈ tiltAuxiliaryPrimes N (∏ p ∈ S₀, p),
                      (↑(∏ p ∈ S₀, p) : ℝ) / ((4 : ℝ) * (↑N : ℝ)) * ∏ p ∈ S₀, q p ≤
                        ∑ t ∈ Finset.Icc (1 : ℕ) H with (∏ p ∈ S₀, p) * p₀ ∣ t, w t := by
  intro N J H P Y q hP_prop μ hμ_nn Tmax GoodS w hTmax_mul L SmallS₀ hcond_good
  classical
  intro S₀ hS₀ p₀ hp₀
  set d₁ := ∏ p ∈ S₀, p
  have hp₀_I := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp₀).1
  have hp₀_pr : p₀.Prime := (Finset.mem_filter.mp hp₀).2
  -- Swap sums on RHS
  have hswap : ∑ t ∈ (Finset.Icc 1 H).filter (fun t => d₁ * p₀ ∣ t), w t =
      ((N : ℝ))⁻¹ * ∑ S ∈ GoodS,
        (((Finset.Icc 1 H).filter (fun t => d₁ * p₀ ∣ t ∧ (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S,
          p) ≤ N)).card : ℝ) * μ S := by
    dsimp only [w, tiltWeight]
    rw [← Finset.mul_sum, sum_filtered_weights]
    congr 1
    refine Finset.sum_congr rfl fun S _ => ?_
    have hf_eq : ((Finset.Icc 1 H).filter (fun t => d₁ * p₀ ∣ t)).filter
          (fun t => (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S, p) ≤ N) =
        (Finset.Icc 1 H).filter (fun t => d₁ * p₀ ∣ t ∧ (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S, p) ≤ N)
          := by
      ext t; simp only [Finset.mem_filter]; tauto
    rw [hf_eq]
  rw [hswap]
  have hcount : ∀ S ∈ GoodS.filter (fun S => S₀ ⊆ S),
      N / p₀ ≤ ((Finset.Icc 1 H).filter (fun t => d₁ * p₀ ∣ t ∧ (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S,
        p) ≤ N)).card := by
    exact @randomTilt_count N J hP_prop hTmax_mul S₀ p₀ hp₀_pr.pos
  have hdiv_ge : (d₁ : ℝ) / 2 ≤ ((N / p₀ : ℕ) : ℝ) := by
    have hmul : p₀ * d₁ ≤ N :=
      (Nat.mul_le_mul_right d₁ hp₀_I.2).trans (Nat.div_mul_le_self N d₁)
    have hle : d₁ ≤ N / p₀ :=
      (Nat.le_div_iff_mul_le hp₀_pr.pos).mpr (by rwa [mul_comm])
    have hreal : (d₁ : ℝ) ≤ ((N / p₀ : ℕ) : ℝ) := by exact_mod_cast hle
    linarith [Nat.cast_nonneg (α := ℝ) d₁]
  calc ((d₁ : ℝ) / (4 * (N : ℝ))) * (∏ p ∈ S₀, q p)
      = ((N : ℝ))⁻¹ * ((d₁ : ℝ) / 2) * ((1 : ℝ) / 2 * (∏ p ∈ S₀, q p)) := by ring
    _ ≤ ((N : ℝ))⁻¹ * ((N / p₀ : ℕ) : ℝ) * ∑ S ∈ GoodS.filter (fun S => S₀ ⊆ S), μ S :=
        mul_le_mul (mul_le_mul_of_nonneg_left hdiv_ge (by positivity)) (hcond_good S₀ hS₀)
          (by positivity) (by positivity)
    _ = ((N : ℝ))⁻¹ * ∑ S ∈ GoodS.filter (fun S => S₀ ⊆ S), ((N / p₀ : ℕ) : ℝ) * μ S := by
        rw [mul_assoc, Finset.mul_sum]
    _ ≤ ((N : ℝ))⁻¹ * ∑ S ∈ GoodS.filter (fun S => S₀ ⊆ S),
          (((Finset.Icc 1 H).filter (fun t => d₁ * p₀ ∣ t ∧ (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S,
            p) ≤ N)).card : ℝ) * μ S :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun S hS =>
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcount S hS)
            (hμ_nn S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1)) (by positivity)
    _ ≤ ((N : ℝ))⁻¹ * ∑ S ∈ GoodS,
          (((Finset.Icc 1 H).filter (fun t => d₁ * p₀ ∣ t ∧ (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S,
            p) ≤ N)).card : ℝ) * μ S :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _
          _) fun S hS _ =>
          mul_nonneg (Nat.cast_nonneg _) (hμ_nn S (Finset.mem_filter.mp hS).1)) (by positivity)


private lemma randomTilt_N2d_ge :
    ∀ (N : ℕ),
      (100 : ℝ) ≤ Real.log (↑N : ℝ) →
        (0 : ℝ) < (↑N : ℝ) →
            let _L : ℝ := Real.log (↑N : ℝ);
            ∀ (S₀ : Finset ℕ),
              let d₁ : ℕ := ∏ p ∈ S₀, p;
              (0 : ℝ) < (↑d₁ : ℝ) →
                (↑N : ℝ) ^ (9 / 10 : ℝ) ≤ (↑N : ℝ) / (↑d₁ : ℝ) →
                  (↑N : ℝ) ^ (1 / 2 : ℝ) < (↑(N / ((2 : ℕ) * d₁) + (1 : ℕ)) : ℝ) := by
  intro N hlogN_ge hN_pos L S₀ d₁ hd₁_pos hdiv_ge
  classical
  have h1 : (N : ℝ) / (2 * (d₁ : ℝ)) < ((N / (2 * d₁) + 1 : ℕ) : ℝ) := by
    have hd₁_pos_nat : 0 < d₁ := by exact_mod_cast hd₁_pos
    have hmod := Nat.div_add_mod N (2 * d₁)
    have hlt := Nat.mod_lt N (by omega : 0 < 2 * d₁)
    have : N < (2 * d₁) * (N / (2 * d₁) + 1) := by nlinarith
    have hcast : (N : ℝ) < (2 * (d₁ : ℝ)) * ((N / (2 * d₁) + 1 : ℕ) : ℝ) := by exact_mod_cast this
    exact (div_lt_iff₀' (by positivity)).mpr hcast
  have hhalf : (N : ℝ) ^ ((1 : ℝ) / 2) ≤ (N : ℝ) / (2 * (d₁ : ℝ)) := by
    have h4 : (2 : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 5) := by
      have : (2 : ℝ) ≤ Real.exp (2 / 5 * L) := by linarith [Real.add_one_le_exp (2 / 5 * L)]
      have heq : Real.exp (2 / 5 * L) = (N : ℝ) ^ ((2 : ℝ) / 5) := by
        rw [Real.rpow_def_of_pos hN_pos]
        congr 1
        dsimp [L]
        ring
      rwa [heq] at this
    have hprod : (N : ℝ) ^ ((1 : ℝ) / 2) * (N : ℝ) ^ ((2 : ℝ) / 5) = (N : ℝ) ^ ((9 : ℝ) / 10) := by
      rw [← Real.rpow_add hN_pos]; norm_num
    have hmul : 2 * (N : ℝ) ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ ((9 : ℝ) / 10) := by
      calc 2 * (N : ℝ) ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ ((2 : ℝ) / 5) * (N : ℝ) ^ ((1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right h4 (by positivity)
        _ = (N : ℝ) ^ ((9 : ℝ) / 10) := by rw [mul_comm, hprod]
    have : (N : ℝ) / (2 * (d₁ : ℝ)) = ((N : ℝ) / (d₁ : ℝ)) / 2 := by ring
    linarith
  linarith


private lemma randomTilt_p₀_gt_M :
    ∀ (N J : ℕ),
      (↑((2 : ℕ) ^ ((2 : ℕ) * J)) : ℝ) ≤ (↑N : ℝ) ^ (1 / 2 : ℝ) →
        (100 : ℝ) ≤ Real.log (↑N : ℝ) →
          (0 : ℝ) < (↑N : ℝ) →
              let P : Finset ℕ := P_win J;
              (∀ p ∈ P, Nat.Prime p ∧ (2 : ℕ) ^ J < p ∧ p ≤ (2 : ℕ) ^ ((2 : ℕ) * J)) →
                let L : ℝ := Real.log (↑N : ℝ);
                let SmallS₀ : Finset (Finset ℕ) := tiltSmallSubsets P L;
                (∀ S₀ ∈ SmallS₀, (↑(∏ p ∈ S₀, p) : ℝ) ≤ (↑N : ℝ) ^ (1 / 10 : ℝ)) →
                  let P₀ : Finset ℕ → Finset ℕ := fun S₀ =>
                    tiltAuxiliaryPrimes N (∏ p ∈ S₀, p);
                  ∀ S₀ ∈ SmallS₀, ∀ p₀ ∈ P₀ S₀, (2 : ℕ) ^ ((2 : ℕ) * J) < p₀ := by
  intro N J hY_sq_small hlogN_ge hN_pos P hP_prop L SmallS₀ hS₀_prod_le P₀
  classical
  intro S₀ hS₀ p₀ hp₀
  set d₁ := ∏ p ∈ S₀, p
  have hd₁_le : (d₁ : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 10) := hS₀_prod_le S₀ hS₀
  have hd₁_pos : (0 : ℝ) < (d₁ : ℝ) := by
    exact_mod_cast Finset.prod_pos fun p hp =>
      (hP_prop p (Finset.mem_powerset.mp (Finset.mem_filter.mp hS₀).1 hp)).1.pos
  have hdiv_ge := quotient_ge_rpow hN_pos hd₁_pos hd₁_le
  have hN2d_ge : (N : ℝ) ^ ((1 : ℝ) / 2) < ((N / (2 * d₁) + 1 : ℕ) : ℝ) := by
    exact @randomTilt_N2d_ge N hlogN_ge hN_pos S₀ hd₁_pos hdiv_ge
  have hp₀_ge : N / (2 * d₁) + 1 ≤ p₀ := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp₀).1).1
  have hlt_r : ((2 ^ (2 * J) : ℕ) : ℝ) < (p₀ : ℝ) :=
    lt_of_le_of_lt hY_sq_small (lt_of_lt_of_le hN2d_ge (by exact_mod_cast hp₀_ge))
  exact_mod_cast hlt_r


private lemma randomTilt_prod_id :
    ∀ (N J : ℕ) (α : ℝ),
          (100 : ℝ) ≤ Real.log (↑N : ℝ) →
            (0 : ℝ) < (↑N : ℝ) →
                let P : Finset ℕ := P_win J;
                let Y : ℝ := (↑((2 : ℕ) ^ J) : ℝ);
                let q : ℕ → ℝ := fun p => Y / (↑p : ℝ);
                (∀ p ∈ P, Nat.Prime p ∧ (2 : ℕ) ^ J < p ∧ p ≤ (2 : ℕ) ^ ((2 : ℕ) * J)) →
                  (∀ p ∈ P, (0 : ℝ) ≤ q p) →
                    let L : ℝ := Real.log (↑N : ℝ);
                    let SmallS₀ : Finset (Finset ℕ) := tiltSmallSubsets P L;
                    let r : ℕ → ℝ := fun p => Y ^ α / (↑p : ℝ);
                    ∀ S₀ ∈ SmallS₀,
                      let d₁ : ℕ := ∏ p ∈ S₀, p;
                        (0 : ℝ) < (↑d₁ : ℝ) →
                          (4 : ℝ) ^ α ≤ (4 : ℝ) →
                            ((↑d₁ : ℝ) / ((4 : ℝ) * (↑N : ℝ)) * ∏ p ∈ S₀, q p) ^ α *
                                ((↑N : ℝ) / ((16 : ℝ) * (↑d₁ : ℝ) * L)) ≥
                              (↑N : ℝ) ^ ((1 : ℝ) - α) / ((64 : ℝ) * L) * ∏ p ∈ S₀, r p := by
  intro N J α hlogN_ge hN_pos P Y q hP_prop hq0 L SmallS₀ r S₀ hS₀ d₁
    hd₁_pos_r h4α
  classical
  have hq_prod_nn : 0 ≤ ∏ p ∈ S₀, q p := Finset.prod_nonneg fun p hp =>
    hq0 p (Finset.mem_powerset.mp (Finset.mem_filter.mp hS₀).1 hp)
  have hsplit : ((d₁ : ℝ) / (4 * (N : ℝ)) * (∏ p ∈ S₀, q p)) ^ α =
      (d₁ : ℝ) ^ α / ((4 : ℝ) ^ α * (N : ℝ) ^ α) * (∏ p ∈ S₀, (q p) ^ α) := by
    rw [Real.mul_rpow (by positivity) hq_prod_nn, Real.div_rpow (le_of_lt hd₁_pos_r) (by
      positivity),
      Real.mul_rpow (by norm_num) (le_of_lt hN_pos),
      ← Real.finsetProd_rpow S₀ q (fun p hp => hq0 p (Finset.mem_powerset.mp (Finset.mem_filter.mp
        hS₀).1 hp)) α]
  have hd₁_comb : (d₁ : ℝ) ^ α / (d₁ : ℝ) * (∏ p ∈ S₀, (q p) ^ α) = ∏ p ∈ S₀, r p := by
    have hd1_rpow : (d₁ : ℝ) ^ α / (d₁ : ℝ) = ∏ p ∈ S₀, ((p : ℝ) ^ α / (p : ℝ)) := by
      have h1 : (d₁ : ℝ) = ∏ p ∈ S₀, (p : ℝ) := by dsimp [d₁]; push_cast; rfl
      rw [h1, ← Real.finsetProd_rpow S₀ (fun p => (p : ℝ)) (fun _ _ => Nat.cast_nonneg _) α,
        ← Finset.prod_div_distrib]
    rw [hd1_rpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp_pos : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (hP_prop p (Finset.mem_powerset.mp (Finset.mem_filter.mp hS₀).1 hp)).1.pos
    dsimp [q, r]
    rw [Real.div_rpow (by positivity) (le_of_lt hp_pos)]
    have hpα_ne : (p : ℝ) ^ α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hp_pos α)
    field_simp [hpα_ne, ne_of_gt hp_pos]
  have hN_comb : (N : ℝ) / (N : ℝ) ^ α = (N : ℝ) ^ (1 - α) := by
    rw [Real.rpow_sub hN_pos, Real.rpow_one]
  rw [hsplit]
  have hrew : ((d₁ : ℝ) ^ α / ((4 : ℝ) ^ α * (N : ℝ) ^ α) * ∏ p ∈ S₀, q p ^ α) *
        ((N : ℝ) / (16 * (d₁ : ℝ) * L)) =
      ((N : ℝ) / (N : ℝ) ^ α) / (16 * (4 : ℝ) ^ α * L) *
        ((d₁ : ℝ) ^ α / (d₁ : ℝ) * ∏ p ∈ S₀, q p ^ α) := by ring
  rw [hrew, hN_comb, hd₁_comb]
  refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun p _ => by dsimp [r]; positivity)
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)


private lemma randomTilt_S₀_inner :
    ∀ (N J : ℕ) (α : ℝ),
      (0 : ℝ) < α →
          (2 : ℝ) * (10 : ℝ) ^ (9 : ℕ) ≤ (↑N : ℝ) ^ (9 / 10 : ℝ) →
            (100 : ℝ) ≤ Real.log (↑N : ℝ) →
              let H : ℕ := ⌊(↑N : ℝ) ^ (4 / 3 : ℝ)⌋₊;
              α < (1 : ℝ) →
                (0 : ℝ) < (↑N : ℝ) →
                    let P : Finset ℕ := P_win J;
                    let Y : ℝ := (↑((2 : ℕ) ^ J) : ℝ);
                    let q : ℕ → ℝ := fun p => Y / (↑p : ℝ);
                    (∀ p ∈ P, Nat.Prime p ∧ (2 : ℕ) ^ J < p ∧ p ≤ (2 : ℕ) ^ ((2 : ℕ) * J)) →
                      (∀ p ∈ P, (0 : ℝ) ≤ q p) →
                        let μ := bernoulliMass P q;
                        let Tmax : ℕ := ⌊(↑N : ℝ) ^ (1 / 3 : ℝ)⌋₊;
                        let GoodS := tiltSupport P Tmax;
                        let w := tiltWeight N GoodS μ;
                        let L : ℝ := Real.log (↑N : ℝ);
                        let SmallS₀ : Finset (Finset ℕ) := tiltSmallSubsets P L;
                        (∀ S₀ ∈ SmallS₀, (↑(∏ p ∈ S₀, p) : ℝ) ≤ (↑N : ℝ) ^ (1 / 10 : ℝ)) →
                          (∀ S₀ ∈ SmallS₀,
                              ∀ p₀ ∈ tiltAuxiliaryPrimes N (∏ p ∈ S₀, p),
                                (↑(∏ p ∈ S₀, p) : ℝ) / ((4 : ℝ) * (↑N : ℝ)) * ∏ p ∈ S₀, q p ≤
                                  ∑ t ∈ Finset.Icc (1 : ℕ) H with (∏ p ∈ S₀, p) * p₀ ∣ t, w t) →
                            let P₀ : Finset ℕ → Finset ℕ := fun S₀ =>
                              tiltAuxiliaryPrimes N (∏ p ∈ S₀, p);
                            let f_obj : ℕ → ℝ := fun d => (∑ t ∈ Finset.Icc (1 : ℕ) H with d ∣ t,
                              w t) ^ α;
                            let r : ℕ → ℝ := fun p => Y ^ α / (↑p : ℝ);
                            ∀ S₀ ∈ SmallS₀,
                              (↑N : ℝ) ^ ((1 : ℝ) - α) / ((64 : ℝ) * L) * ∏ p ∈ S₀, r p ≤
                                ∑ p₀ ∈ P₀ S₀, f_obj ((∏ p ∈ S₀, p) * p₀) := by
  intro N J α hα0 hN_big hlogN_ge H hα1 hN_pos P Y q hP_prop hq0 μ Tmax GoodS w L
    SmallS₀ hS₀_prod_le hp_w_lb P₀ f_obj r
  classical
  intro S₀ hS₀
  set d₁ := ∏ p ∈ S₀, p
  have hd₁_pos : 1 ≤ d₁ := Finset.one_le_prod₀ fun p hp =>
    (hP_prop p (Finset.mem_powerset.mp (Finset.mem_filter.mp hS₀).1 hp)).1.one_le
  have hd₁_pos_r : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast hd₁_pos
  have hN_div_big : 2 * 10 ^ 9 ≤ N / d₁ := by
    have hd₁_le := hS₀_prod_le S₀ hS₀
    have hdiv_ge := quotient_ge_rpow hN_pos hd₁_pos_r hd₁_le
    have h2e9 : (2 * 10 ^ 9 : ℝ) ≤ (N : ℝ) / (d₁ : ℝ) := by linarith
    have hmul : (2 * 10 ^ 9 : ℝ) * (d₁ : ℝ) ≤ (N : ℝ) := (le_div_iff₀ hd₁_pos_r).mp h2e9
    have hnat : 2 * 10 ^ 9 * d₁ ≤ N := by exact_mod_cast hmul
    exact (Nat.le_div_iff_mul_le hd₁_pos).mpr hnat
  have hP₀_card := prime_dyadic_div_lower N d₁ hd₁_pos hN_div_big
  have hpt : ∀ p₀ ∈ P₀ S₀,
      (((d₁ : ℝ) / (4 * (N : ℝ))) * (∏ p ∈ S₀, q p)) ^ α ≤ f_obj (d₁ * p₀) := fun p₀ hp₀ =>
    Real.rpow_le_rpow (mul_nonneg (by positivity) (Finset.prod_nonneg fun p hp =>
      hq0 p (Finset.mem_powerset.mp (Finset.mem_filter.mp hS₀).1 hp)))
      (hp_w_lb S₀ hS₀ p₀ hp₀) (le_of_lt hα0)
  have h4α : (4 : ℝ) ^ α ≤ 4 := by
    calc (4 : ℝ) ^ α ≤ (4 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt hα1)
      _ = 4 := Real.rpow_one 4
  have hprod_id : ((d₁ : ℝ) / (4 * (N : ℝ)) * (∏ p ∈ S₀, q p)) ^ α * ((N : ℝ) / (16 * (d₁ : ℝ) *
    L)) ≥
      ((N : ℝ) ^ (1 - α) / (64 * L)) * (∏ p ∈ S₀, r p) := by
    exact @randomTilt_prod_id N J α hlogN_ge hN_pos hP_prop hq0 S₀ hS₀
      hd₁_pos_r h4α
  calc ((N : ℝ) ^ (1 - α) / (64 * L)) * (∏ p ∈ S₀, r p)
      ≤ (((d₁ : ℝ) / (4 * (N : ℝ))) * (∏ p ∈ S₀, q p)) ^ α * ((N : ℝ) / (16 * (d₁ : ℝ) * L)) :=
        hprod_id
    _ ≤ (((d₁ : ℝ) / (4 * (N : ℝ))) * (∏ p ∈ S₀, q p)) ^ α * ((P₀ S₀).card : ℝ) :=
        mul_le_mul_of_nonneg_left hP₀_card (by positivity)
    _ = ∑ _p₀ ∈ P₀ S₀, (((d₁ : ℝ) / (4 * (N : ℝ))) * (∏ p ∈ S₀, q p)) ^ α := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ p₀ ∈ P₀ S₀, f_obj (d₁ * p₀) := Finset.sum_le_sum hpt


private lemma randomTilt_rlog :
    ∀ (N J : ℕ),
      ∀ α ≤ (3 / 4 : ℝ),
        (30 : ℕ) ≤ J →
          let P : Finset ℕ := P_win J;
          let Y : ℝ := (↑((2 : ℕ) ^ J) : ℝ);
          let q : ℕ → ℝ := fun p => Y / (↑p : ℝ);
          (∀ p ∈ P, Nat.Prime p ∧ (2 : ℕ) ^ J < p ∧ p ≤ (2 : ℕ) ^ ((2 : ℕ) * J)) →
            let L : ℝ := Real.log (↑N : ℝ);
            (∀ p ∈ P, (0 : ℝ) ≤ Real.log (↑p : ℝ)) →
              ∑ p ∈ P, q p * Real.log (↑p : ℝ) ≤ L / (10 : ℝ) →
                let r : ℕ → ℝ := fun p => Y ^ α / (↑p : ℝ);
                ∑ p ∈ P, r p * Real.log (↑p : ℝ) ≤ L / (10 : ℝ) / (2 : ℝ) := by
  intro N J α hα34 hJ30 P Y q hP_prop L hlogp_nn hqlog_sum r
  classical
  have hY_ge1 : (1 : ℝ) ≤ Y := by dsimp [Y]; exact_mod_cast (Nat.one_le_two_pow (n := J))
  have hr_le_q : ∀ p ∈ P, r p ≤ q p / 2 := fun p hp => by
    dsimp [r, q]
    have hY_pos : 0 < Y := by dsimp [Y]; positivity
    have h2Y : 2 * Y ^ α ≤ Y := by
      have hY_ge : (16 : ℝ) ≤ Y := by
        dsimp [Y]
        have : 16 ≤ 2 ^ J := le_trans (by norm_num : 16 ≤ 2 ^ 30) (Nat.pow_le_pow_right (by
          norm_num) hJ30)
        exact_mod_cast this
      have h2_le : (2 : ℝ) ≤ Y ^ ((1 : ℝ) / 4) := by
        have hpow4 : (2 : ℝ) ^ (4 : ℕ) ≤ (Y ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) := by
          rw [← Real.rpow_natCast (Y ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul (le_of_lt hY_pos)]
          norm_num; exact hY_ge
        by_contra hgt; push Not at hgt
        have : (Y ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) < (2 : ℝ) ^ (4 : ℕ) :=
          pow_lt_pow_left₀ hgt (by positivity) (by norm_num)
        linarith
      have hsplit : Y = Y ^ ((1 : ℝ) / 4) * Y ^ ((3 : ℝ) / 4) := by
        rw [← Real.rpow_add hY_pos]; norm_num
      have hYα : Y ^ α ≤ Y ^ ((3 : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_le hY_ge1 hα34
      calc 2 * Y ^ α ≤ Y ^ ((1 : ℝ) / 4) * Y ^ ((3 : ℝ) / 4) :=
            mul_le_mul h2_le hYα (by positivity) (by positivity)
        _ = Y := hsplit.symm
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (hP_prop p hp).1.pos
    rw [div_div, div_le_div_iff₀ hp_pos (by positivity)]
    nlinarith
  calc ∑ p ∈ P, r p * Real.log (p : ℝ)
      ≤ ∑ p ∈ P, (q p / 2) * Real.log (p : ℝ) :=
        Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right (hr_le_q p hp) (hlogp_nn p hp)
    _ = (∑ p ∈ P, q p * Real.log (p : ℝ)) / 2 := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ (L / 10) / 2 := by linarith


/-- Unified random-tilt lower bound on `∑ d ∈ Ioc (N/2) N, p_w(d)^α` for any `α ∈ (0, 1)`
using `P_win J` and `q_p = 2^J / p` (simultaneously proving Barrier 1 at `α = 2/3` and
Barrier 2a at `α = 1/2`). -/
private lemma unified_random_tilt_lower (N J : ℕ) (α : ℝ)
    (hα0 : 0 < α) (hα34 : α ≤ 3 / 4)
    (hJ30 : 30 ≤ J)
    (hY_budget : 8 * ((2 ^ J : ℕ) : ℝ) * (J : ℝ) ≤ (1 : ℝ) / 10 * Real.log (N : ℝ))
    (hY_sq_small : ((2 ^ (2 * J) : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2))
    (hN_big : (2 : ℝ) * 10 ^ 9 ≤ (N : ℝ) ^ ((9 : ℝ) / 10))
    (hlogN_ge : 100 ≤ Real.log (N : ℝ)) :
    let H := Nat.floor ((N : ℝ) ^ ((4 : ℝ) / 3))
    ∃ w : ℕ → ℝ,
      (∀ t ∈ Finset.Icc 1 H, 0 ≤ w t) ∧
      (∑ t ∈ Finset.Icc 1 H, w t ≤ 1) ∧
      ((N : ℝ) ^ (1 - α) / (128 * Real.log (N : ℝ))) *
          Real.exp ((1 : ℝ) / 32 * ((2 ^ J : ℕ) : ℝ) ^ α) ≤
        ∑ d ∈ Finset.Ioc (N / 2) N,
          (∑ t ∈ (Finset.Icc 1 H).filter (fun t => d ∣ t), w t) ^ α := by
  classical
  intro H
  have hα1 : α < 1 := by linarith
  have hN_pos : (0 : ℝ) < (N : ℝ) :=
    zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith))
  let P := P_win J
  let Y : ℝ := ((2 ^ J : ℕ) : ℝ)
  let q : ℕ → ℝ := fun p => Y / (p : ℝ)
  have hP_prop : ∀ p ∈ P, p.Prime ∧ 2 ^ J < p ∧ p ≤ 2 ^ (2 * J) := fun p hp =>
    ⟨(Finset.mem_filter.mp hp).2, (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1,
     (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2⟩
  have hq0 : ∀ p ∈ P, 0 ≤ q p := fun p _ => by dsimp [q, Y]; positivity
  have hq1 : ∀ p ∈ P, q p ≤ 1 := fun p hp => by
    dsimp [q, Y]
    apply (div_le_one (by exact_mod_cast (hP_prop p hp).1.pos)).mpr
    exact_mod_cast le_of_lt (hP_prop p hp).2.1
  let μ := bernoulliMass P q
  have hμ_nn : ∀ S ∈ P.powerset, 0 ≤ μ S := fun S hS =>
    bernoulliMass_nonneg hq0 hq1 (Finset.mem_powerset.mp hS)
  let Tmax := Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 3))
  let GoodS := tiltSupport P Tmax
  -- Sub-probability weight w(t) = (1/N) * ∑_{S ∈ GoodS, (∏ S) ∣ t, t / (∏ S) ≤ N} μ(S)
  let w := tiltWeight N GoodS μ
  have hw_nn : ∀ t ∈ Finset.Icc 1 H, 0 ≤ w t := fun t _ =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun S hS =>
      hμ_nn S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1)
  have hTmax_mul : Tmax * N ≤ H := by
    have h1 : (Tmax : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := Nat.floor_le (by positivity)
    have h2 : ((Tmax * N : ℕ) : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ) / 3) := by
      rw [Nat.cast_mul, show ((4 : ℝ) / 3) = ((1 : ℝ) / 3) + 1 by norm_num, Real.rpow_add hN_pos,
        Real.rpow_one]
      exact mul_le_mul_of_nonneg_right h1 (le_of_lt hN_pos)
    exact Nat.le_floor h2
  have hw_sum : ∑ t ∈ Finset.Icc 1 H, w t ≤ 1 := by
    exact randomTilt_w_sum N H hN_pos P q GoodS (Finset.filter_subset _ _) hμ_nn
  -- Now bound ∑_{d ∈ Ioc (N/2) N} p_w(d)^α from below!
  refine ⟨w, hw_nn, hw_sum, ?_⟩
  let L := Real.log (N : ℝ)
  have hsum_inv := sum_inv_primes_win_bounds J hJ30
  have hlogp_le : ∀ p ∈ P, Real.log (p : ℝ) ≤ 2 * (J : ℝ) := fun p hp => by
    have h1 : (p : ℝ) ≤ (2 : ℝ) ^ (2 * J) := by exact_mod_cast (hP_prop p hp).2.2
    have h2 := Real.log_le_log (by exact_mod_cast (hP_prop p hp).1.pos) h1
    rw [Real.log_pow] at h2; push_cast at h2
    have := log_two_le_one
    nlinarith [Nat.cast_nonneg (α := ℝ) J]
  have hlogp_nn : ∀ p ∈ P, 0 ≤ Real.log (p : ℝ) := fun p hp =>
    Real.log_nonneg (by exact_mod_cast (hP_prop p hp).1.one_le)
  have hqlog_sum : ∑ p ∈ P, q p * Real.log (p : ℝ) ≤ L / 10 := by
    calc ∑ p ∈ P, q p * Real.log (p : ℝ)
        ≤ ∑ p ∈ P, (Y / (p : ℝ)) * (2 * (J : ℝ)) :=
          Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hlogp_le p hp) (hq0 p hp)
      _ = 2 * Y * (J : ℝ) * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
      _ ≤ 2 * Y * (J : ℝ) * 4 := mul_le_mul_of_nonneg_left hsum_inv.2 (by positivity)
      _ = 8 * Y * (J : ℝ) := by ring
      _ ≤ L / 10 := by linarith [hY_budget]
  -- Define SmallS₀ = {S₀ ⊆ P | ∑ p ∈ S₀, log p ≤ L / 10}
  let SmallS₀ := tiltSmallSubsets P L
  -- For any S₀ ∈ SmallS₀, ∏ p ∈ S₀, p ≤ N^(1/10) and ∑_{S ∈ GoodS, S₀ ⊆ S} μ(S) ≥ (1/2) * ∏_{p ∈
  -- S₀} q p
  have hS₀_prod_le : ∀ S₀ ∈ SmallS₀, ((∏ p ∈ S₀, p : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 10) := by
    intro S₀ hS₀
    have hsum_le : ∑ p ∈ S₀, Real.log (p : ℝ) ≤ L / 10 := (Finset.mem_filter.mp hS₀).2
    exact prod_le_rpow_of_sum_log_le hN_pos
      (fun p hp => (hP_prop p (Finset.mem_powerset.mp (Finset.mem_filter.mp hS₀).1 hp)).1.pos)
      (by change _ ≤ (1 : ℝ) / 10 * L; linarith)
  have hcond_good : ∀ S₀ ∈ SmallS₀,
      (1 : ℝ) / 2 * (∏ p ∈ S₀, q p) ≤ ∑ S ∈ GoodS.filter (fun S => S₀ ⊆ S), μ S := by
    exact @randomTilt_cond_good N J hlogN_ge hN_pos hP_prop hq0 hq1 hμ_nn hlogp_nn hqlog_sum
  -- Lower bound on p_w(d₁ * p₀) for S₀ ∈ SmallS₀ and prime p₀ ∈ (N/(2*d₁), N/d₁]
  have hp_w_lb : ∀ S₀ ∈ SmallS₀, ∀ p₀ ∈ tiltAuxiliaryPrimes N (∏ p ∈ S₀, p),
      (((∏ p ∈ S₀, p : ℕ) : ℝ) / (4 * (N : ℝ))) * (∏ p ∈ S₀, q p) ≤
        ∑ t ∈ (Finset.Icc 1 H).filter (fun t => (∏ p ∈ S₀, p) * p₀ ∣ t), w t := by
    exact @randomTilt_p_w_lb N J hP_prop hμ_nn hTmax_mul hcond_good
  -- Sum over disjoint pairs (S₀, p₀) mapping injectively into Finset.Ioc (N/2) N
  let P₀ : Finset ℕ → Finset ℕ := fun S₀ =>
    tiltAuxiliaryPrimes N (∏ p ∈ S₀, p)
  let Pairs := SmallS₀.sigma P₀
  let φ : (Σ _ : Finset ℕ, ℕ) → ℕ := fun x => (∏ p ∈ x.1, p) * x.2
  have hmaps_D : ∀ x ∈ Pairs, φ x ∈ Finset.Ioc (N / 2) N := by
    intro x hx
    have hS₀ : x.1 ∈ SmallS₀ := (Finset.mem_sigma.mp hx).1
    have hp₀ : x.2 ∈ P₀ x.1 := (Finset.mem_sigma.mp hx).2
    have hI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp₀).1
    set d₁ := ∏ p ∈ x.1, p
    have hd₁_pos : 1 ≤ d₁ := Finset.one_le_prod₀ fun p hp =>
      (hP_prop p (Finset.mem_powerset.mp (Finset.mem_filter.mp hS₀).1 hp)).1.one_le
    have hhi : d₁ * x.2 ≤ N := by
      refine (Nat.mul_le_mul_left d₁ hI.2).trans ?_
      exact Nat.mul_div_le N d₁
    have hlo : N / 2 < d₁ * x.2 := by
      have hdiv : N / (2 * d₁) = (N / 2) / d₁ := (Nat.div_div_eq_div_mul N 2 d₁).symm
      have hmod := Nat.div_add_mod (N / 2) d₁
      have hlt := Nat.mod_lt (N / 2) hd₁_pos
      have : d₁ * (N / (2 * d₁) + 1) ≤ d₁ * x.2 := Nat.mul_le_mul_left d₁ (by omega)
      rw [hdiv] at this; nlinarith
    exact Finset.mem_Ioc.mpr ⟨hlo, hhi⟩
  have hp₀_gt_M : ∀ S₀ ∈ SmallS₀, ∀ p₀ ∈ P₀ S₀, 2 ^ (2 * J) < p₀ := by
    exact @randomTilt_p₀_gt_M N J hY_sq_small hlogN_ge hN_pos hP_prop hS₀_prod_le
  have hinj_D : Set.InjOn φ (Pairs : Set _) := by
    intro x₁ hx₁ x₂ hx₂ hEq
    have h1 := Finset.mem_sigma.mp hx₁
    have h2 := Finset.mem_sigma.mp hx₂
    have hres := prod_primes_mul_large_prime_inj (2 ^ (2 * J))
      (fun p hp => (hP_prop p (Finset.mem_powerset.mp (Finset.mem_filter.mp h1.1).1 hp)).1)
      (fun p hp => ⟨(hP_prop p (Finset.mem_powerset.mp (Finset.mem_filter.mp h2.1).1 hp)).1,
        (hP_prop p (Finset.mem_powerset.mp (Finset.mem_filter.mp h2.1).1 hp)).2.2⟩)
      ⟨(Finset.mem_filter.mp h1.2).2, hp₀_gt_M x₁.1 h1.1 x₁.2 h1.2⟩
      (Finset.mem_filter.mp h2.2).2 hEq
    rcases x₁ with ⟨S₁, p₁⟩; rcases x₂ with ⟨S₂, p₂⟩
    simp only at hres; rcases hres with ⟨rfl, rfl⟩; rfl
  let f_obj : ℕ → ℝ := fun d => (∑ t ∈ (Finset.Icc 1 H).filter (fun t => d ∣ t), w t) ^ α
  have hf_nn : ∀ d, 0 ≤ f_obj d := fun d =>
    Real.rpow_nonneg (Finset.sum_nonneg fun t ht => hw_nn t (Finset.mem_filter.mp ht).1) _
  have hsub_D : Pairs.image φ ⊆ Finset.Ioc (N / 2) N := by
    intro d hd; rcases Finset.mem_image.mp hd with ⟨x, hx, rfl⟩; exact hmaps_D x hx
  -- Evaluate sum over Pairs
  let r : ℕ → ℝ := fun p => Y ^ α / (p : ℝ)
  have hS₀_inner : ∀ S₀ ∈ SmallS₀,
      ((N : ℝ) ^ (1 - α) / (64 * L)) * (∏ p ∈ S₀, r p) ≤ ∑ p₀ ∈ P₀ S₀, f_obj ((∏ p ∈ S₀, p) * p₀)
        := by
    exact @randomTilt_S₀_inner N J α hα0 hN_big hlogN_ge hα1 hN_pos hP_prop hq0
      hS₀_prod_le hp_w_lb
  -- Apply truncated_euler_sum_lower to r(p) = Y^α / p on P
  have hr0 : ∀ p ∈ P, 0 ≤ r p := fun p _ => by dsimp [r]; positivity
  have hr1 : ∀ p ∈ P, r p ≤ 1 := fun p hp => by
    dsimp [r]
    have hY_ge1 : (1 : ℝ) ≤ Y := by dsimp [Y]; exact_mod_cast (Nat.one_le_two_pow (n := J))
    have hYa_le : Y ^ α ≤ Y := by
      calc Y ^ α ≤ Y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY_ge1 (le_of_lt hα1)
        _ = Y := Real.rpow_one Y
    have hp_ge : Y ≤ (p : ℝ) := by dsimp [Y]; exact_mod_cast le_of_lt (hP_prop p hp).2.1
    exact (div_le_one (by exact_mod_cast (hP_prop p hp).1.pos)).mpr (le_trans hYa_le hp_ge)
  have hrlog : ∑ p ∈ P, r p * Real.log (p : ℝ) ≤ (L / 10) / 2 := by
    exact @randomTilt_rlog N J α hα34 hJ30 hP_prop hlogp_nn hqlog_sum
  have heuler := truncated_euler_sum_lower P r (L / 10) (fun p hp => (hP_prop p hp).1.two_le) hr0
    hr1 (by linarith) hrlog
  have hsum_r_lb : (1 : ℝ) / 16 * Y ^ α ≤ ∑ p ∈ P, r p := by
    have hrew : ∑ p ∈ P, r p = Y ^ α * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by dsimp [r]; ring
    rw [hrew]
    have := hsum_inv.1
    nlinarith [Real.rpow_nonneg (show 0 ≤ Y by positivity) α]
  calc ((N : ℝ) ^ (1 - α) / (128 * L)) * Real.exp ((1 : ℝ) / 32 * Y ^ α)
      = ((N : ℝ) ^ (1 - α) / (64 * L)) * ((1 : ℝ) / 2 * Real.exp ((1 : ℝ) / 2 * ((1 : ℝ) / 16 * Y
        ^ α))) := by
        rw [show (1 : ℝ) / 32 * Y ^ α = (1 : ℝ) / 2 * ((1 : ℝ) / 16 * Y ^ α) by ring]; ring
    _ ≤ ((N : ℝ) ^ (1 - α) / (64 * L)) * ((1 : ℝ) / 2 * Real.exp ((1 : ℝ) / 2 * ∑ p ∈ P, r p)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
          (by norm_num)) (by positivity)
    _ ≤ ((N : ℝ) ^ (1 - α) / (64 * L)) * ∑ S₀ ∈ SmallS₀, ∏ p ∈ S₀, r p :=
        mul_le_mul_of_nonneg_left heuler (by positivity)
    _ = ∑ S₀ ∈ SmallS₀, ((N : ℝ) ^ (1 - α) / (64 * L)) * (∏ p ∈ S₀, r p) := by rw [Finset.mul_sum]
    _ ≤ ∑ S₀ ∈ SmallS₀, ∑ p₀ ∈ P₀ S₀, f_obj ((∏ p ∈ S₀, p) * p₀) := Finset.sum_le_sum hS₀_inner
    _ = ∑ x ∈ Pairs, f_obj (φ x) := (Finset.sum_sigma SmallS₀ P₀ (fun x => f_obj (φ x))).symm
    _ = ∑ d ∈ Pairs.image φ, f_obj d := (Finset.sum_image (fun x₁ hx₁ x₂ hx₂ hEq => hinj_D hx₁ hx₂
      hEq)).symm
    _ ≤ ∑ d ∈ Finset.Ioc (N / 2) N, f_obj d :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub_D fun d _ _ => hf_nn d

/-! ### Section 5: Shared Estimates and the Two Covering Barriers -/

/-- Auxiliary asymptotic inequalities for `N ≥ Nat.ceil (Real.exp (Real.exp 200))`. -/
private lemma large_N_barrier_bounds (N : ℕ)
    (hN : Nat.ceil (Real.exp (Real.exp 200)) ≤ N) :
    let L := Real.log (N : ℝ)
    let LL := Real.log L
    200 ≤ LL ∧ LL ^ 8 ≤ L / 160 ∧ (2 : ℝ) * 10 ^ 9 ≤ (N : ℝ) ^ ((9 : ℝ) / 10) ∧
    (4 : ℝ) * L ^ 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
  intro L LL
  have hN_ge_exp : Real.exp (Real.exp 200) ≤ (N : ℝ) := le_trans (Nat.le_ceil _) (by
    exact_mod_cast hN)
  have hN_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hN_ge_exp
  have hL_ge_exp : Real.exp 200 ≤ L := by
    have := Real.log_le_log (Real.exp_pos _) hN_ge_exp
    rwa [Real.log_exp] at this
  have hL_pos : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL_ge_exp
  have hLL : 200 ≤ LL := by
    have := Real.log_le_log (Real.exp_pos _) hL_ge_exp
    rwa [Real.log_exp] at this
  have hexp_LL : Real.exp LL = L := Real.exp_log hL_pos
  -- The fourteenth Taylor term leaves six powers of LL to absorb the factorial and 160.
  have hLL8 : LL ^ 8 ≤ L / 160 := by
    have h14 := Real.pow_div_factorial_le_exp LL (by linarith) 14
    have hfac14 : ((14 : ℕ).factorial : ℝ) = 87178291200 := by norm_num
    rw [hfac14] at h14
    have hle : LL ^ 14 / 87178291200 ≤ L := by linarith
    have hLL6 : (160 : ℝ) * 87178291200 ≤ LL ^ 6 := by
      have : (200 : ℝ) ^ 6 ≤ LL ^ 6 := pow_le_pow_left₀ (by norm_num) hLL 6
      linarith
    have hLL8_nn : 0 ≤ LL ^ 8 := by positivity
    have h14_eq : LL ^ 14 = LL ^ 8 * LL ^ 6 := by ring
    nlinarith
  have hL_ge : (10 : ℝ) ^ 18 ≤ L := by
    have : (200 : ℝ) ^ 8 ≤ LL ^ 8 := pow_le_pow_left₀ (by norm_num) hLL 8
    linarith
  have hN910 : (2 : ℝ) * 10 ^ 9 ≤ (N : ℝ) ^ ((9 : ℝ) / 10) := by
    rw [Real.rpow_def_of_pos hN_pos]
    have h1 : (2 : ℝ) * 10 ^ 9 ≤ 1 + L * ((9 : ℝ) / 10) := by linarith
    linarith [Real.add_one_le_exp (L * ((9 : ℝ) / 10))]
  have h4L2 : (4 : ℝ) * L ^ 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos hN_pos]
    have h3 := Real.pow_div_factorial_le_exp (L * ((1 : ℝ) / 2)) (by linarith) 3
    have hfac3 : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num
    rw [hfac3] at h3
    nlinarith [sq_nonneg L]
  exact ⟨hLL, hLL8, hN910, h4L2⟩

private lemma exists_primeWindow_scale (N : ℕ) (L LL : ℝ)
    (hLL : 200 ≤ LL) (hLL8 : LL ^ 8 ≤ L / 160)
    (h4L2 : 4 * L ^ 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 2))
    (hL_pos : 0 < L) (hlogL : Real.log L = LL) :
    ∃ J : ℕ, 30 ≤ J ∧
      8 * ((2 ^ J : ℕ) : ℝ) * (J : ℝ) ≤ (1 : ℝ) / 10 * L ∧
      ((2 ^ (2 * J) : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) ∧
      100 ≤ L ∧ (L / LL) / 640 ≤ ((2 ^ J : ℕ) : ℝ) := by
  have hLL_pos : 0 < LL := by linarith only [hLL]
  let X_fl := Nat.floor (L / (160 * LL))
  have hX_ge : 2 ^ 30 ≤ X_fl := by
    have h1 : ((2 ^ 30 : ℕ) : ℝ) ≤ L / (160 * LL) := by
      have hLL7 : (200 : ℝ) ^ 7 ≤ LL ^ 7 := pow_le_pow_left₀ (by norm_num) hLL 7
      have hdiv : LL ^ 7 ≤ L / (160 * LL) := by
        rw [le_div_iff₀ (by positivity)]
        have : LL ^ 8 = LL ^ 7 * LL := by ring
        nlinarith
      push_cast; linarith
    exact Nat.le_floor h1
  let J := Nat.log 2 X_fl
  have hJ30 : 30 ≤ J := Nat.le_log_of_pow_le (by norm_num) hX_ge
  have h2J_le : ((2 ^ J : ℕ) : ℝ) ≤ L / (160 * LL) := by
    have h1 : 2 ^ J ≤ X_fl := Nat.pow_log_le_self 2 (by omega)
    exact le_trans (by exact_mod_cast h1) (Nat.floor_le (by positivity))
  have hJ_le : (J : ℝ) ≤ 2 * LL := by
    have h1 : (2 : ℝ) ^ J ≤ L := le_trans (by simpa using h2J_le)
      (by rw [div_le_iff₀ (by positivity)]; nlinarith)
    have hlg := Real.log_le_log (pow_pos (by norm_num) J) h1
    rw [Real.log_pow, hlogL] at hlg
    nlinarith [half_le_log_two]
  have hY_budget : 8 * ((2 ^ J : ℕ) : ℝ) * (J : ℝ) ≤ (1 : ℝ) / 10 * L := by
    calc 8 * ((2 ^ J : ℕ) : ℝ) * (J : ℝ)
        ≤ 8 * (L / (160 * LL)) * (2 * LL) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h2J_le (by norm_num)) hJ_le (Nat.cast_nonneg _)
            (by positivity)
      _ = (1 : ℝ) / 10 * L := by field_simp [ne_of_gt hLL_pos]; ring
  have hY_sq : ((2 ^ (2 * J) : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
    have h1 : ((2 ^ (2 * J) : ℕ) : ℝ) = ((2 ^ J : ℕ) : ℝ) ^ 2 := by
      rw [mul_comm, pow_mul]; push_cast; ring
    have h2J_le_L : ((2 ^ J : ℕ) : ℝ) ≤ L := by
      refine le_trans h2J_le ?_
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    rw [h1]
    calc ((2 ^ J : ℕ) : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by positivity) h2J_le_L 2
      _ ≤ (4 : ℝ) * L ^ 2 := by nlinarith [sq_nonneg L]
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := h4L2
  have hlogN100 : 100 ≤ L := by
    have : (200 : ℝ) ^ 8 ≤ LL ^ 8 := pow_le_pow_left₀ (by norm_num) hLL 8
    linarith
  have h2J_ge : (L / LL) / 640 ≤ ((2 ^ J : ℕ) : ℝ) := by
    have hlt : X_fl < 2 ^ (J + 1) := Nat.lt_pow_succ_log_self (by norm_num) X_fl
    have hfl : L / (160 * LL) - 1 < (X_fl : ℝ) := sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)
    have h1 : L / (320 * LL) ≤ L / (160 * LL) - 1 := by
      have hLL7 : (200 : ℝ) ^ 7 ≤ LL ^ 7 := pow_le_pow_left₀ (by norm_num) hLL 7
      have : LL ^ 7 ≤ L / (160 * LL) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [show LL ^ 8 = LL ^ 7 * LL by ring]
      have : L / (320 * LL) = (L / (160 * LL)) / 2 := by ring
      linarith
    have h2 : ((2 ^ (J + 1) : ℕ) : ℝ) = 2 * ((2 ^ J : ℕ) : ℝ) := by rw [pow_succ]; push_cast; ring
    have h3 : (X_fl : ℝ) < 2 * ((2 ^ J : ℕ) : ℝ) := by rw [← h2]; exact_mod_cast hlt
    have : (L / LL) / 640 = (L / (320 * LL)) / 2 := by ring
    linarith
  exact ⟨J, hJ30, hY_budget, hY_sq, hlogN100, h2J_ge⟩

/-- Common bounds for absorbing the logarithmic prefactor in both covering estimates. -/
private lemma barrier_log_absorption {L : ℝ} (hL_pos : 0 < L) (hLL : 200 ≤ Real.log L)
    (hLL8 : Real.log L ^ 8 ≤ L / 160) :
    128 * L ≤ Real.exp (2 * Real.log L) ∧
      2 * Real.log L ≤ (1 : ℝ) / 20000 * (L / Real.log L) ^ ((1 : ℝ) / 2) := by
  let LL := Real.log L
  change 200 ≤ LL at hLL
  change LL ^ 8 ≤ L / 160 at hLL8
  have hLL_pos : 0 < LL := by linarith
  have h128L : (128 * L : ℝ) ≤ Real.exp (2 * LL) := by
    have h128 : (128 : ℝ) ≤ Real.exp LL := by linarith [Real.add_one_le_exp LL]
    calc 128 * L = 128 * Real.exp LL := by rw [Real.exp_log hL_pos]
      _ ≤ Real.exp LL * Real.exp LL := mul_le_mul_of_nonneg_right h128 (le_of_lt (Real.exp_pos _))
      _ = Real.exp (2 * LL) := by rw [← Real.exp_add]; congr 1; ring
  have hLL3 : LL ^ 3 ≤ (L / LL) ^ ((1 : ℝ) / 2) := by
    have hsq : (LL ^ 3) ^ 2 ≤ L / LL := by
      rw [le_div_iff₀ hLL_pos]
      have h1 : (LL ^ 3) ^ 2 * LL = LL ^ 7 := by ring
      have h2 : LL ^ 8 = LL ^ 7 * LL := by ring
      nlinarith [pow_nonneg (le_of_lt hLL_pos) 7]
    have h1 := Real.rpow_le_rpow (by positivity) hsq (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← Real.rpow_natCast (LL ^ 3) 2, ← Real.rpow_mul (by positivity)] at h1
    norm_num at h1; exact h1
  have hLL2 : (200 : ℝ) ^ 2 ≤ LL ^ 2 := pow_le_pow_left₀ (by norm_num) hLL 2
  refine ⟨h128L, ?_⟩
  nlinarith [show LL ^ 3 = LL * LL ^ 2 by ring]

/-- Convert the prime-window scale bound to a lower bound for a power of that scale. -/
private lemma window_rpow_lower {x y power scale : ℝ} (hx : 0 ≤ x)
    (hwindow : x / 640 ≤ y) (hpower : 0 ≤ power)
    (h640 : (640 : ℝ) ^ power ≤ scale) :
    (1 : ℝ) / scale * x ^ power ≤ y ^ power := by
  have h := Real.rpow_le_rpow (div_nonneg hx (by norm_num)) hwindow hpower
  rw [Real.div_rpow hx (by norm_num)] at h
  rw [div_mul_eq_mul_div, one_mul]
  exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hx _) (by positivity) h640).trans h

/-- Absorb a prefactor bounded by an exponential into the exponent. -/
private lemma absorb_exp_prefactor {a x y b : ℝ} (ha : 0 ≤ a) (hb : b ≤ Real.exp y) :
    a * Real.exp x * b ≤ a * Real.exp (y + x) := by
  calc a * Real.exp x * b ≤ a * Real.exp x * Real.exp y :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  _ = a * Real.exp (y + x) := by rw [mul_assoc, ← Real.exp_add, add_comm x y]

/-- Unabsorbed covering lower bound with exponent `2/3`.

There exist `c > 0` and `N₀ : ℕ` such that for every `N ≥ N₀`, setting `H := ⌊N^(4/3)⌋`,
every set-theoretic cover `Finset.Ioc (N / 2) N ⊆ idx.biUnion S` satisfies
```
∑ α ∈ idx, κ(S α, H)^(2/3) * |S α|^(1/3) ≥ N^(1/3) * exp (c * (log N / log log N)^(2/3)).
``` -/
theorem barrier1_unabsorbed_two_thirds :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      let H : ℕ := Nat.floor ((N : ℝ) ^ ((4 : ℝ) / 3))
      ∀ {ι : Type*} (idx : Finset ι) (S : ι → Finset ℕ),
        Finset.Ioc (N / 2) N ⊆ idx.biUnion S →
        (N : ℝ) ^ ((1 : ℝ) / 3) *
          Real.exp (c * (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ))) ^ ((2 : ℝ) / 3)) ≤
          ∑ α ∈ idx,
            (((Finset.Icc 1 H).sup (fun t => ((S α).filter (fun d => d ∣ t)).card) : ℕ) : ℝ) ^ ((2
              : ℝ) / 3) *
              ((S α).card : ℝ) ^ ((1 : ℝ) / 3) := by
  refine ⟨(1 : ℝ) / 4000, by norm_num, Nat.ceil (Real.exp (Real.exp 200)), fun N hN => ?_⟩
  intro H ι idx S hcover
  let L := Real.log (N : ℝ)
  let LL := Real.log L
  obtain ⟨hLL, hLL8, hN910, h4L2⟩ := large_N_barrier_bounds N hN
  change 200 ≤ LL at hLL
  change LL ^ 8 ≤ L / 160 at hLL8
  change 4 * L ^ 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 2) at h4L2
  have hL_pos : 0 < L := by
    have : (1 : ℝ) ≤ LL ^ 8 := by nlinarith [pow_le_pow_left₀ (by norm_num) hLL 8]
    linarith
  have hLL_pos : 0 < LL := by linarith
  obtain ⟨J, hJ30, hY_budget, hY_sq, hlogN100, h2J_ge⟩ :=
    exists_primeWindow_scale N L LL hLL hLL8 h4L2 hL_pos rfl
  obtain ⟨w, hw_nn, hw_sum, hw_lb⟩ := unified_random_tilt_lower N J ((2 : ℝ) / 3)
    (by norm_num) (by norm_num) hJ30 hY_budget hY_sq hN910 hlogN100
  have hpart := partition_lower_two_thirds (Finset.Ioc (N / 2) N) H w hw_nn hw_sum idx S hcover
  refine le_trans ?_ (le_trans hw_lb hpart)
  -- Show (N^(1/3) / (128 * L)) * exp ((1/32) * (2^J)^(2/3)) ≥ N^(1/3) * exp ((1/4000) *
  -- (L/LL)^(2/3))
  have h640 : (640 : ℝ) ^ ((2 : ℝ) / 3) ≤ 75 := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by decide : (3 : ℕ) ≠ 0)).mp
    rw [← Real.rpow_natCast ((640 : ℝ) ^ ((2 : ℝ) / 3)) 3, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h2J_23 := window_rpow_lower (div_nonneg hL_pos.le hLL_pos.le) h2J_ge
    (by norm_num : (0 : ℝ) ≤ 2 / 3) h640
  obtain ⟨h128L, h2LL_half⟩ := barrier_log_absorption hL_pos hLL hLL8
  have hratio : 1 ≤ L / LL := by
    rw [one_le_div hLL_pos]
    nlinarith [pow_le_pow_left₀ (by norm_num) hLL 7]
  have h2LL_le : 2 * LL ≤ (1 : ℝ) / 20000 * (L / LL) ^ ((2 : ℝ) / 3) :=
    h2LL_half.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hratio
      (by norm_num)) (by norm_num))
  have hexp_diff : 2 * LL + (1 : ℝ) / 4000 * (L / LL) ^ ((2 : ℝ) / 3) ≤
      (1 : ℝ) / 32 * ((2 ^ J : ℕ) : ℝ) ^ ((2 : ℝ) / 3) := by
    nlinarith
  have h1m : (1 : ℝ) - (2 : ℝ) / 3 = (1 : ℝ) / 3 := by norm_num
  rw [h1m]
  rw [div_mul_eq_mul_div (a := (N : ℝ) ^ ((1 : ℝ) / 3)), le_div_iff₀ (by positivity)]
  calc (N : ℝ) ^ ((1 : ℝ) / 3) * Real.exp ((1 : ℝ) / 4000 * (L / LL) ^ ((2 : ℝ) / 3)) * (128 * L)
      ≤ (N : ℝ) ^ ((1 : ℝ) / 3) * Real.exp (2 * LL + (1 : ℝ) / 4000 * (L / LL) ^ ((2 : ℝ) / 3)) :=
          absorb_exp_prefactor (by positivity) h128L
    _ ≤ (N : ℝ) ^ ((1 : ℝ) / 3) * Real.exp ((1 : ℝ) / 32 * ((2 ^ J : ℕ) : ℝ) ^ ((2 : ℝ) / 3)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_diff) (by positivity)

/-- Absorbed covering lower bound with exponent `1/2`.

There exist `c > 0` and `N₀ : ℕ` such that for every `N ≥ N₀`, setting `H := ⌊N^(4/3)⌋`,
every set-theoretic cover `Finset.Ioc (N / 2) N ⊆ idx.biUnion S` satisfies
```
∑ α ∈ idx, κ(S α, H)^(1/3) * |S α|^(1/3) ≥ N^(1/3) * exp (c * (log N / log log N)^(1/2)).
``` -/
theorem barrier2a_absorbed_half :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      let H : ℕ := Nat.floor ((N : ℝ) ^ ((4 : ℝ) / 3))
      ∀ {ι : Type*} (idx : Finset ι) (S : ι → Finset ℕ),
        Finset.Ioc (N / 2) N ⊆ idx.biUnion S →
        (N : ℝ) ^ ((1 : ℝ) / 3) *
          Real.exp (c * (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ))) ^ ((1 : ℝ) / 2)) ≤
          ∑ α ∈ idx,
            (((Finset.Icc 1 H).sup (fun t => ((S α).filter (fun d => d ∣ t)).card) : ℕ) : ℝ) ^ ((1
              : ℝ) / 3) *
              ((S α).card : ℝ) ^ ((1 : ℝ) / 3) := by
  refine ⟨(1 : ℝ) / 2000, by norm_num, Nat.ceil (Real.exp (Real.exp 200)), fun N hN => ?_⟩
  intro H ι idx S hcover
  let L := Real.log (N : ℝ)
  let LL := Real.log L
  obtain ⟨hLL, hLL8, hN910, h4L2⟩ := large_N_barrier_bounds N hN
  change 200 ≤ LL at hLL
  change LL ^ 8 ≤ L / 160 at hLL8
  change 4 * L ^ 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 2) at h4L2
  have hL_pos : 0 < L := by
    have : (1 : ℝ) ≤ LL ^ 8 := by nlinarith [pow_le_pow_left₀ (by norm_num) hLL 8]
    linarith
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    have : Real.exp (Real.exp 200) ≤ (N : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
    exact lt_of_lt_of_le (Real.exp_pos _) this
  obtain ⟨J, hJ30, hY_budget, hY_sq, hlogN100, h2J_ge⟩ :=
    exists_primeWindow_scale N L LL hLL hLL8 h4L2 hL_pos rfl
  obtain ⟨w, hw_nn, hw_sum, hw_lb⟩ := unified_random_tilt_lower N J ((1 : ℝ) / 2)
    (by norm_num) (by norm_num) hJ30 hY_budget hY_sq hN910 hlogN100
  have hpart := partition_lower_half (Finset.Ioc (N / 2) N) H w hw_nn hw_sum idx S hcover
  have hw_lb23 := Real.rpow_le_rpow (by positivity) hw_lb (by norm_num : (0 : ℝ) ≤ 2 / 3)
  refine le_trans ?_ (le_trans hw_lb23 hpart)
  have h640 : (640 : ℝ) ^ ((1 : ℝ) / 2) ≤ 26 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by norm_num)]
    norm_num
  have h2J_12 := window_rpow_lower (by positivity) h2J_ge
    (by norm_num : (0 : ℝ) ≤ 1 / 2) h640
  obtain ⟨h128L, h2LL_le⟩ := barrier_log_absorption hL_pos hLL hLL8
  have h1m : (1 : ℝ) - (1 : ℝ) / 2 = (1 : ℝ) / 2 := by norm_num
  rw [h1m]
  have hstep : (N : ℝ) ^ ((1 : ℝ) / 2) * Real.exp ((3 : ℝ) / 4000 * (L / LL) ^ ((1 : ℝ) / 2)) ≤
      (N : ℝ) ^ ((1 : ℝ) / 2) / (128 * L) * Real.exp ((1 : ℝ) / 32 * ((2 ^ J : ℕ) : ℝ) ^ ((1 : ℝ)
        / 2)) := by
    rw [div_mul_eq_mul_div (a := (N : ℝ) ^ ((1 : ℝ) / 2)), le_div_iff₀ (by positivity)]
    have hexp_diff : 2 * LL + (3 : ℝ) / 4000 * (L / LL) ^ ((1 : ℝ) / 2) ≤
        (1 : ℝ) / 32 * ((2 ^ J : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
      nlinarith
    calc (N : ℝ) ^ ((1 : ℝ) / 2) * Real.exp ((3 : ℝ) / 4000 * (L / LL) ^ ((1 : ℝ) / 2)) * (128 * L)
        ≤ (N : ℝ) ^ ((1 : ℝ) / 2) * Real.exp (2 * LL + (3 : ℝ) / 4000 * (L / LL) ^ ((1 : ℝ) / 2)) :=
            absorb_exp_prefactor (by positivity) h128L
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) * Real.exp ((1 : ℝ) / 32 * ((2 ^ J : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_diff) (by positivity)
  have hpow := Real.rpow_le_rpow (by positivity) hstep (by norm_num : (0 : ℝ) ≤ 2 / 3)
  rw [Real.mul_rpow (by positivity) (le_of_lt (Real.exp_pos _)),
    ← Real.rpow_mul (le_of_lt hN_pos), ← Real.exp_mul] at hpow
  have h13 : (1 : ℝ) / 2 * ((2 : ℝ) / 3) = (1 : ℝ) / 3 := by norm_num
  have h2000 : (3 : ℝ) / 4000 * (L / LL) ^ ((1 : ℝ) / 2) * ((2 : ℝ) / 3) =
      (1 : ℝ) / 2000 * (L / LL) ^ ((1 : ℝ) / 2) := by ring
  rw [h13, h2000] at hpow
  exact hpow

end Erdos711.Barriers
