/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.PrimeSums.Mertens
public import LeanPool.IwaniecLinearSieve.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Polynomial.Basic

/-!
# Mertens' product theorem with the de la Vallée Poussin error term

`R z = ∏_{p < z} (1 - 1/p) = c_R / log z + O(pntE z / log z)`.
-/

@[expose] public section

open Real Filter Topology Finset

namespace IwaniecLinearSieve

theorem one_sub_inv_pos {p : ℕ} (hp : p.Prime) : 0 < 1 - (p : ℝ)⁻¹ := by
  have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [sub_pos]
  exact inv_lt_one_of_one_lt₀ this

theorem one_sub_inv_le_one (p : ℕ) : 1 - (p : ℝ)⁻¹ ≤ 1 := by
  have : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  linarith

theorem primesLT_mono {z w : ℝ} (hzw : z ≤ w) : primesLT z ⊆ primesLT w := fun p hp ↦ by
  rw [mem_primesLT] at hp ⊢
  exact ⟨hp.1, hp.2.trans_le hzw⟩

theorem R_eq_mul_prod_sdiff {z w : ℝ} (hzw : z ≤ w) :
    R w = R z * ∏ p ∈ primesLT w \ primesLT z, (1 - (p : ℝ)⁻¹) := by
  rw [R, R, mul_comm, prod_sdiff (primesLT_mono hzw)]

theorem R_antitone : Antitone R := fun z w hzw ↦ by
  rw [R_eq_mul_prod_sdiff hzw]
  refine mul_le_of_le_one_right (R_pos z).le (prod_le_one₀ (fun p hp ↦ ?_) fun p _ ↦
    one_sub_inv_le_one p)
  exact (one_sub_inv_pos (mem_primesLT.1 (Finset.mem_sdiff.1 hp).1).1).le

/-- `∑_{p < z} 1/p`. -/
noncomputable def SLT (z : ℝ) : ℝ := ∑ p ∈ primesLT z, (p : ℝ)⁻¹

/-- `S` counts primes `p ≤ z` and `SLT` primes `p < z`; they differ by at most `1 / z`. -/
theorem S_sub_SLT {z : ℝ} (hz : 0 < z) : 0 ≤ S z - SLT z ∧ S z - SLT z ≤ z⁻¹ := by
  have hS : S z = ∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (p : ℝ)⁻¹ := by
    rw [S, primesLT, show ⌈(⌊z⌋₊ : ℝ) + 1⌉₊ = ⌊z⌋₊ + 1 by exact_mod_cast Nat.ceil_natCast _]
  have hsub : primesLT z ⊆ Nat.primesBelow (⌊z⌋₊ + 1) := fun p hp ↦ by
    rw [primesLT, Nat.mem_primesBelow] at hp
    rw [Nat.mem_primesBelow]
    exact ⟨hp.1.trans_le (Nat.ceil_le_floor_add_one z), hp.2⟩
  rw [hS, SLT, ← sum_sdiff hsub, add_sub_cancel_right]
  refine ⟨sum_nonneg fun p _ ↦ by positivity, ?_⟩
  have hmem : ∀ p ∈ Nat.primesBelow (⌊z⌋₊ + 1) \ primesLT z, (p : ℝ) = z ∧ p = ⌊z⌋₊ := by
    intro p hp
    rw [Finset.mem_sdiff, Nat.mem_primesBelow, primesLT, Nat.mem_primesBelow] at hp
    have h1 : p ≤ ⌊z⌋₊ := Nat.lt_succ_iff.1 hp.1.1
    have h2 : ⌈z⌉₊ ≤ p := by
      by_contra h
      exact hp.2 ⟨Nat.lt_of_not_le h, hp.1.2⟩
    have h3 : z ≤ p := Nat.ceil_le.1 h2
    have h4 : (p : ℝ) ≤ z := (Nat.le_floor_iff hz.le).1 h1
    exact ⟨le_antisymm h4 h3, le_antisymm h1 (Nat.floor_le_of_le h3)⟩
  have hcard : (Nat.primesBelow (⌊z⌋₊ + 1) \ primesLT z).card ≤ 1 :=
    card_le_one.2 fun a ha b hb ↦ (hmem a ha).2.trans (hmem b hb).2.symm
  calc ∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1) \ primesLT z, (p : ℝ)⁻¹
      = ∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1) \ primesLT z, z⁻¹ :=
        sum_congr rfl fun p hp ↦ by rw [(hmem p hp).1]
    _ = (Nat.primesBelow (⌊z⌋₊ + 1) \ primesLT z).card * z⁻¹ := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 1 * z⁻¹ := by gcongr; exact_mod_cast hcard
    _ = z⁻¹ := one_mul _

/-- `0 ≤ -log (1 - 1/p) - 1/p ≤ 1/(p-1) - 1/p`. -/
theorem abs_log_one_sub_inv_add_inv_le {p : ℝ} (hp : 2 ≤ p) :
    |log (1 - p⁻¹) + p⁻¹| ≤ (p - 1)⁻¹ - p⁻¹ := by
  have hp0 : 0 < p := by linarith
  have hq : 0 < 1 - p⁻¹ := by
    rw [sub_pos]; exact inv_lt_one_of_one_lt₀ (by linarith)
  have h1 : log (1 - p⁻¹) ≤ -p⁻¹ := by linarith [log_le_sub_one_of_pos hq]
  have h2 : -((1 - p⁻¹)⁻¹ - 1) ≤ log (1 - p⁻¹) := by
    have := log_le_sub_one_of_pos (inv_pos.2 hq)
    rw [log_inv] at this
    linarith
  have h3 : (1 - p⁻¹)⁻¹ - 1 = (p - 1)⁻¹ := by
    have : p - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [abs_of_nonpos (by linarith)]
  linarith

theorem sum_Ico_inv_sub_inv {m M : ℕ} (hmM : m ≤ M) :
    ∑ n ∈ Ico m M, (((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹) = ((m : ℝ) - 1)⁻¹ - ((M : ℝ) - 1)⁻¹ := by
  induction M, hmM using Nat.le_induction with
  | base => simp
  | succ M hmM ih =>
    rw [sum_Ico_succ_top hmM, ih]
    push_cast
    ring

/-- The tail of `∑_p (-log (1 - 1/p) - 1/p)` is at most `2 / z`. -/
theorem abs_sum_log_one_sub_inv_add_inv_le {z w : ℝ} (hz : 2 ≤ z) (hzw : z ≤ w) :
    |∑ p ∈ primesLT w \ primesLT z, (log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹)| ≤ 2 * z⁻¹ := by
  have hz1 : (2 : ℝ) ≤ ⌈z⌉₊ := hz.trans (Nat.le_ceil z)
  have hw1 : (2 : ℝ) ≤ ⌈w⌉₊ := hz1.trans (by exact_mod_cast Nat.ceil_mono hzw)
  have hsub : primesLT w \ primesLT z ⊆ Ico ⌈z⌉₊ ⌈w⌉₊ := fun p hp ↦ by
    rw [Finset.mem_sdiff, primesLT, primesLT, Nat.mem_primesBelow, Nat.mem_primesBelow] at hp
    rw [Finset.mem_Ico]
    exact ⟨not_lt.1 fun h ↦ hp.2 ⟨h, hp.1.2⟩, hp.1.1⟩
  have hnn : ∀ n ∈ Ico ⌈z⌉₊ ⌈w⌉₊, 0 ≤ ((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹ := fun n hn ↦ by
    have : (2 : ℝ) ≤ n := hz1.trans (by exact_mod_cast (Finset.mem_Ico.1 hn).1)
    rw [sub_nonneg]
    exact inv_anti₀ (by linarith) (by linarith)
  calc |∑ p ∈ primesLT w \ primesLT z, (log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹)|
      ≤ ∑ p ∈ primesLT w \ primesLT z, |log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ primesLT w \ primesLT z, (((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹) := by
        refine sum_le_sum fun p hp ↦ abs_log_one_sub_inv_add_inv_le ?_
        exact hz1.trans (by exact_mod_cast (Finset.mem_Ico.1 (hsub hp)).1)
    _ ≤ ∑ n ∈ Ico ⌈z⌉₊ ⌈w⌉₊, (((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹) :=
        sum_le_sum_of_subset_of_nonneg hsub fun n hn _ ↦ hnn n hn
    _ = ((⌈z⌉₊ : ℝ) - 1)⁻¹ - ((⌈w⌉₊ : ℝ) - 1)⁻¹ := sum_Ico_inv_sub_inv (Nat.ceil_mono hzw)
    _ ≤ (z - 1)⁻¹ := by
        have : 0 ≤ ((⌈w⌉₊ : ℝ) - 1)⁻¹ := inv_nonneg.2 (by linarith)
        have : ((⌈z⌉₊ : ℝ) - 1)⁻¹ ≤ (z - 1)⁻¹ :=
          inv_anti₀ (by linarith) (by linarith [Nat.le_ceil z])
        linarith
    _ ≤ 2 * z⁻¹ := by
        rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
        linarith

theorem log_R_eq (z : ℝ) : log (R z) = ∑ p ∈ primesLT z, log (1 - (p : ℝ)⁻¹) :=
  log_prod fun _ hp ↦ (one_sub_inv_pos (mem_primesLT.1 hp).1).ne'

theorem abs_exp_sub_one_le_mul_exp (d : ℝ) : |exp d - 1| ≤ |d| * exp |d| := by
  rcases le_total 0 d with hd | hd
  · rw [abs_of_nonneg hd, abs_of_nonneg (by linarith [add_one_le_exp d])]
    have h1 := add_one_le_exp (-d)
    have h2 : exp d * exp (-d) = 1 := by rw [← exp_add]; simp
    nlinarith [exp_pos d]
  · rw [abs_of_nonpos hd, abs_of_nonpos (by linarith [exp_le_one_iff.2 hd])]
    have h1 := add_one_le_exp d
    have h2 : 1 ≤ exp (-d) := one_le_exp_iff.2 (by linarith)
    nlinarith

theorem exists_abs_log_R_add_loglog_sub_le :
    ∃ K, 0 ≤ K ∧ ∀ z w, 2 ≤ z → z ≤ w →
      |(log (R w) + log (log w)) - (log (R z) + log (log z))| ≤ K * pntE z := by
  obtain ⟨c₅, C, hC⟩ := S_asymp
  have hC0 : 0 ≤ C := by
    have h := (abs_nonneg _).trans (hC 2 le_rfl)
    exact nonneg_of_mul_nonneg_left h (pntE_pos 2)
  refine ⟨2 * C + 4, by positivity, fun z w hz hzw ↦ ?_⟩
  have hw : 2 ≤ w := hz.trans hzw
  set D := primesLT w \ primesLT z
  have hR : log (R w) - log (R z) = ∑ p ∈ D, log (1 - (p : ℝ)⁻¹) := by
    rw [R_eq_mul_prod_sdiff hzw, log_mul (R_pos z).ne', log_prod]
    · ring
    · exact fun p hp ↦ (one_sub_inv_pos (mem_primesLT.1 (Finset.mem_sdiff.1 hp).1).1).ne'
    · exact (prod_pos fun p hp ↦
        one_sub_inv_pos (mem_primesLT.1 (Finset.mem_sdiff.1 hp).1).1).ne'
  have hS : SLT w - SLT z = ∑ p ∈ D, (p : ℝ)⁻¹ := by
    rw [SLT, SLT, ← sum_sdiff (primesLT_mono hzw)]
    ring
  have h1 := abs_sum_log_one_sub_inv_add_inv_le hz hzw
  rw [sum_add_distrib, ← hR, ← hS] at h1
  have h2 := S_sub_SLT (z := z) (by linarith)
  have h3 := S_sub_SLT (z := w) (by linarith)
  have h4 := hC z hz
  have h5 := hC w hw
  have hE : pntE w ≤ pntE z := pntE_le_pntE (by linarith) hzw
  have hiz := inv_le_pntE hz
  have hiw : w⁻¹ ≤ z⁻¹ := inv_anti₀ (by linarith) hzw
  rw [abs_le] at h1 h4 h5 ⊢
  constructor <;> nlinarith

/-- Mertens' product theorem with the de la Vallée Poussin error term. -/
theorem R_asymp : ∃ cR > 0, ∃ C, ∀ z ≥ 2, |R z * log z - cR| ≤ C * pntE z := by
  obtain ⟨K, hK0, hK⟩ := exists_abs_log_R_add_loglog_sub_le
  obtain ⟨L, hL⟩ := exists_abs_sub_le_of_cauchy (T := fun z ↦ log (R z) + log (log z))
    (g := fun z ↦ K * pntE z) (a := 2) hK (by simpa using tendsto_pntE.const_mul K)
  refine ⟨exp L, exp_pos L, exp L * (K * exp K), fun z hz ↦ ?_⟩
  have hlog : 0 < log z := log_pos (by linarith)
  have hRz : R z * log z = exp (log (R z) + log (log z)) := by
    rw [exp_add, exp_log (R_pos z), exp_log hlog]
  have hd := hL z hz
  have hdK : |log (R z) + log (log z) - L| ≤ K := by
    have := pntE_le_one z
    nlinarith
  rw [hRz, show exp (log (R z) + log (log z)) - exp L =
      exp L * (exp (log (R z) + log (log z) - L) - 1) by rw [mul_sub, ← exp_add]; ring_nf,
    abs_mul, abs_of_pos (exp_pos L)]
  calc exp L * |exp (log (R z) + log (log z) - L) - 1|
      ≤ exp L * (|log (R z) + log (log z) - L| * exp |log (R z) + log (log z) - L|) := by
        gcongr; exact abs_exp_sub_one_le_mul_exp _
    _ ≤ exp L * ((K * pntE z) * exp K) := by
        have := pntE_pos z
        gcongr
    _ = exp L * (K * exp K) * pntE z := by ring

/-- Lower bound `R z ≫ 1 / log z`. -/
theorem R_lower : ∃ c > 0, ∀ z ≥ 2, c / log z ≤ R z := by
  obtain ⟨cR, hcR, C, hC⟩ := R_asymp
  obtain ⟨Z, hZ⟩ := eventually_atTop.1
    ((by simpa using tendsto_pntE.const_mul C : Tendsto (fun z ↦ C * pntE z) atTop (𝓝 0)).eventually
      (eventually_lt_nhds (half_pos hcR)))
  set Z' := max Z 2
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  refine ⟨min (cR / 2) (R Z' * log 2), lt_min (half_pos hcR) (mul_pos (R_pos _) hlog2),
    fun z hz ↦ ?_⟩
  have hlog : 0 < log z := log_pos (by linarith)
  rw [div_le_iff₀ hlog]
  rcases le_or_gt Z' z with hzZ | hzZ
  · have h1 := hC z hz
    have h2 := hZ z ((le_max_left _ _).trans hzZ)
    rw [abs_le] at h1
    exact (min_le_left _ _).trans (by linarith)
  · refine (min_le_right _ _).trans ?_
    exact mul_le_mul (R_antitone hzZ.le) (log_le_log (by norm_num) hz) hlog2.le (R_pos z).le

/-- Upper bound `R z ≪ 1 / log z`. -/
theorem R_upper : ∃ C > 0, ∀ z ≥ 2, R z ≤ C / log z := by
  obtain ⟨cR, hcR, C, hC⟩ := R_asymp
  refine ⟨cR + |C|, by positivity, fun z hz ↦ ?_⟩
  have hlog : 0 < log z := log_pos (by linarith)
  rw [le_div_iff₀ hlog]
  have h1 := hC z hz
  have h2 : C * pntE z ≤ |C| :=
    (le_abs_self _).trans (by
      rw [abs_mul, abs_of_pos (pntE_pos z)]
      exact mul_le_of_le_one_right (abs_nonneg _) (pntE_le_one z))
  rw [abs_le] at h1
  linarith

end IwaniecLinearSieve
