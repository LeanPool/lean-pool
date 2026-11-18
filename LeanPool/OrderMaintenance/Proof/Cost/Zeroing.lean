/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring


/-!
# Theorem Z: the zeroing game (`docs/PROOF.md` §4.4)

Dietz–Sleator 1987, Theorem 5, scaled and with decreases. Variables `x₁, …, x_n ≥ 0` start at 0.
Each round, the player sets a maximal `x_i` to 0; then the adversary adds nonnegative amounts
summing to at most `R`, and may decrease any variables (keeping them nonnegative). Then always

    x_i ≤ R · (H_{n−1} + 1).

The proof shows by induction over rounds that the sum of any `k` variables is at most
`k·R·(H_{n−1} − H_{k−1} + 1)`.
-/


@[expose] public section

namespace OrderMaintenance.Zeroing

open Finset

variable {n : ℕ}

/-- One round: zero a maximal variable `x i`, then add amounts `a ≥ 0` with `∑ a ≤ R`, and
decrease arbitrarily (keeping every variable nonnegative). -/
def Round (R : ℝ) (x x' : Fin n → ℝ) : Prop :=
  ∃ i, (∀ j, x j ≤ x i) ∧ ∃ a : Fin n → ℝ, (∀ j, 0 ≤ a j) ∧ ∑ j, a j ≤ R ∧
    ∀ j, 0 ≤ x' j ∧ x' j ≤ (if j = i then 0 else x j) + a j

/-- The states reachable from all zeros. -/
inductive Reach (R : ℝ) : (Fin n → ℝ) → Prop
  | zero : Reach R 0
  | step {x x' : Fin n → ℝ} : Reach R x → Round R x x' → Reach R x'

/-- Harmonic numbers, in `ℝ`. -/
noncomputable def Hn (k : ℕ) : ℝ := (harmonic k : ℝ)

theorem Hn_succ (k : ℕ) : Hn (k + 1) = Hn k + 1 / (k + 1) := by
  simp [Hn, harmonic_succ]

theorem Hn_mono {k l : ℕ} (h : k ≤ l) : Hn k ≤ Hn l := by
  induction l with
  | zero => simp only [Nat.le_zero] at h; subst h; rfl
  | succ l ih =>
    rcases Nat.of_le_succ h with h | h
    · rw [Hn_succ]
      have : (0 : ℝ) ≤ 1 / (l + 1) := by positivity
      linarith [ih h]
    · rw [h]

/-- The bound on a sum of `k` variables. -/
noncomputable def bound (R : ℝ) (k : ℕ) : ℝ := k * R * (Hn (n - 1) - Hn (k - 1) + 1)

/-- The invariant: nonnegative, and every sum of `k ≥ 1` variables is within `bound R k`. -/
def Inv (R : ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ ∀ s : Finset (Fin n), 0 < s.card → ∑ j ∈ s, x j ≤ bound (n := n) R s.card

theorem inv_zero {R : ℝ} (hR : 0 ≤ R) : Inv (n := n) R 0 := by
  refine ⟨fun _ => le_rfl, fun s hs => ?_⟩
  simp only [Pi.zero_apply, sum_const_zero, bound]
  have hk : s.card ≤ n := by simpa using card_le_univ s
  have : Hn (s.card - 1) ≤ Hn (n - 1) := Hn_mono (by omega)
  have : (0 : ℝ) ≤ Hn (n - 1) - Hn (s.card - 1) + 1 := by linarith
  positivity

/-- The sum of `k` variables, none above `x i`, is at most `k · x i`. -/
theorem sum_le_card_mul {x : Fin n → ℝ} {i : Fin n} (hmax : ∀ j, x j ≤ x i) (s : Finset (Fin n)) :
    ∑ j ∈ s, x j ≤ s.card * x i := by
  have := sum_le_card_nsmul s x (x i) (fun j _ => hmax j)
  simpa [nsmul_eq_mul] using this

/-- After zeroing `x i` (maximal), a set of `k < n` variables sums to at most `k/(k+1)` of some
set of `k + 1` variables. -/
theorem zeroed_sum_le {x : Fin n → ℝ} (hx : ∀ j, 0 ≤ x j) {i : Fin n} (hmax : ∀ j, x j ≤ x i)
    (s : Finset (Fin n)) (hs : s.card < n) :
    ∃ t : Finset (Fin n), t.card = s.card + 1 ∧
      (s.card + 1 : ℝ) * ∑ j ∈ s, (if j = i then 0 else x j) ≤ s.card * ∑ j ∈ t, x j := by
  have hsx := sum_le_card_mul hmax s
  by_cases hi : i ∈ s
  · obtain ⟨j, -, hj⟩ := exists_mem_notMem_of_card_lt_card (s := s) (t := univ)
      (by simpa using hs)
    refine ⟨insert j s, card_insert_of_notMem hj, ?_⟩
    rw [sum_insert hj]
    have hy : ∑ k ∈ s, (if k = i then 0 else x k) = ∑ k ∈ s, x k - x i := by
      rw [← sum_erase_add s x hi]
      rw [← sum_erase_add s (fun k => if k = i then 0 else x k) hi]
      rw [sum_congr rfl fun k hk => (by simp [ne_of_mem_erase hk] :
        (if k = i then (0 : ℝ) else x k) = x k)]
      simp
    rw [hy]
    have := hx j
    have := hx i
    nlinarith
  · refine ⟨insert i s, card_insert_of_notMem hi, ?_⟩
    have hne : ∀ k ∈ s, k ≠ i := by rintro k hk rfl; exact hi hk
    rw [sum_insert hi, sum_congr rfl fun k hk => (by simp [hne k hk] :
      (if k = i then (0 : ℝ) else x k) = x k)]
    nlinarith

theorem inv_round {R : ℝ} {x x' : Fin n → ℝ} (h : Inv R x) (hr : Round R x x') : Inv R x' := by
  obtain ⟨hx, hS⟩ := h
  obtain ⟨i, hmax, a, ha, hsa, hx'⟩ := hr
  refine ⟨fun j => (hx' j).1, fun s hs => ?_⟩
  -- the adds to `s` total at most `R`
  have hadd : ∑ j ∈ s, x' j ≤ ∑ j ∈ s, (if j = i then 0 else x j) + R := by
    have h1 : ∑ j ∈ s, x' j ≤ ∑ j ∈ s, ((if j = i then 0 else x j) + a j) :=
      sum_le_sum fun j _ => (hx' j).2
    have h2 : ∑ j ∈ s, a j ≤ ∑ j, a j :=
      sum_le_sum_of_subset_of_nonneg (subset_univ s) fun j _ _ => ha j
    rw [sum_add_distrib] at h1
    linarith
  obtain ⟨m, hm⟩ : ∃ m, s.card = m + 1 := ⟨s.card - 1, by omega⟩
  have hcard : s.card ≤ n := by simpa using card_le_univ s
  rcases Nat.lt_or_ge s.card n with hlt | hge
  · -- k < n: compare with a set of k + 1 variables
    obtain ⟨t, ht, hst⟩ := zeroed_sum_le hx hmax s hlt
    have hT := hS t (by omega)
    rw [ht] at hT
    simp only [bound, hm, Nat.add_sub_cancel] at hT ⊢
    push_cast at hT hst ⊢
    rw [hm] at hst
    push_cast at hst
    have hk : (0 : ℝ) < (m : ℝ) + 1 + 1 := by positivity
    have hy : ∑ j ∈ s, (if j = i then 0 else x j) ≤
        ((m : ℝ) + 1) * R * (Hn (n - 1) - Hn (m + 1) + 1) := by
      have := le_trans hst (mul_le_mul_of_nonneg_left hT (by positivity))
      have h' : ((m : ℝ) + 1 + 1) * ∑ j ∈ s, (if j = i then 0 else x j) ≤
          ((m : ℝ) + 1 + 1) * (((m : ℝ) + 1) * R * (Hn (n - 1) - Hn (m + 1) + 1)) := by
        nlinarith
      exact le_of_mul_le_mul_left h' hk
    rw [Hn_succ] at hy
    have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
    have : ((m : ℝ) + 1) * R * (Hn (n - 1) - (Hn m + 1 / ((m : ℝ) + 1)) + 1) + R =
        ((m : ℝ) + 1) * R * (Hn (n - 1) - Hn m + 1) := by
      field_simp
      ring
    linarith
  · -- k = n: all variables
    have hsn : s.card = n := le_antisymm hcard hge
    have hsu : s = univ := eq_univ_of_card s (by simpa using hsn)
    subst hsu
    have hall := hS univ hs
    have hn : (univ : Finset (Fin n)).card = n := by simp
    simp only [bound, hn, sub_self, zero_add, mul_one] at hall ⊢
    have hsum := sum_le_card_mul hmax (univ : Finset (Fin n))
    rw [hn] at hsum
    have hy : ∑ j, (if j = i then 0 else x j) = ∑ j, x j - x i := by
      rw [← sum_erase_add univ x (mem_univ i)]
      rw [← sum_erase_add univ (fun k => if k = i then 0 else x k) (mem_univ i)]
      rw [sum_congr rfl fun k hk => (by simp [ne_of_mem_erase hk] :
        (if k = i then (0 : ℝ) else x k) = x k)]
      simp
    rw [hy] at hadd
    have hn0 : (0 : ℝ) < n := by
      have : 0 < n := by rw [← hn]; exact hs
      exact_mod_cast this
    -- (n - 1)/n of a sum within n R, plus R
    have hn1 : (1 : ℝ) ≤ n := by
      have : 0 < n := by rw [← hn]; exact hs
      exact_mod_cast this
    have : ((n : ℝ) - 1) * ((n : ℝ) * R - ∑ j, x j) ≥ 0 :=
      mul_nonneg (by linarith) (by linarith)
    have : ∑ j, x j - x i ≤ ((n : ℝ) - 1) * R := by
      have h' : (n : ℝ) * (∑ j, x j - x i) ≤ (n : ℝ) * (((n : ℝ) - 1) * R) := by nlinarith
      exact le_of_mul_le_mul_left h' hn0
    linarith

theorem inv_reach {R : ℝ} (hR : 0 ≤ R) {x : Fin n → ℝ} (h : Reach R x) : Inv R x := by
  induction h with
  | zero => exact inv_zero hR
  | step _ hr ih => exact inv_round ih hr

/-- **Theorem Z.** In every reachable state, every variable is at most `R·(H_{n−1} + 1)`. -/
theorem zeroing {R : ℝ} (hR : 0 ≤ R) {x : Fin n → ℝ} (h : Reach R x) (i : Fin n) :
    x i ≤ R * (Hn (n - 1) + 1) := by
  have := (inv_reach hR h).2 {i} (by simp)
  simpa [bound, Hn] using this

end OrderMaintenance.Zeroing
