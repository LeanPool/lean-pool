/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.RoughGapEndpoint
public import LeanPool.ShellsortMean.ModularCut
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.LinearCombination

/-! Effect of every actual gap on a threshold polynomial. A divisible word
preserves dual modes exactly. For the other modes the true outgoing
threshold error in each chain is a signed contiguous geometric sum. -/
@[expose] public noncomputable section
namespace Shellsort.RoughGapEndpoint
open Finset

/-- The polynomial evaluation of the signed threshold error at a complex frequency. -/
def amplitude {n : ℕ} (p : RankPlacement n) (T : ℕ) (z : ℂ) : ℂ :=
  ∑ i : Fin n, z ^ i.val * (slotError p T i : ℂ)

theorem divisible_word_residueError {n d : ℕ} (p : RankPlacement n) (gaps : List ℕ)
    (hg : ∀ h ∈ gaps, d ∣ h) (T r : ℕ) :
    residueError (sortWord p gaps) d T r = residueError p d T r := by
  unfold residueError
  rw [sortWord_threshold_divisor_count p gaps hg]

theorem amplitude_eq_residues {n d : ℕ} (p : RankPlacement n) (T : ℕ)
    (hT : T ≤ n) (hd : 0 < d) (z : ℂ) (hz : z ^ d = 1) :
    amplitude p T z = ∑ r : Fin d, z ^ r.val * (residueError p d T r.val : ℂ) := by
  symm
  simp_rw [residueError_eq_sum p T _ hT, Int.cast_sum, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  let a : Fin d := ⟨i.val % d, Nat.mod_lt _ hd⟩
  have he (r : Fin d) : i.val % d = r.val ↔ a = r := (Fin.ext_iff (a := a) (b := r)).symm
  simp only [he, Int.cast_ite, Int.cast_zero, mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true]
  have hp : z ^ i.val = z ^ (i.val % d) := by
    conv_lhs => rw [← Nat.mod_add_div i.val d, pow_add, pow_mul, hz, one_pow, mul_one]
  rw [hp]

theorem divisible_word_amplitude {n d : ℕ} (p : RankPlacement n) (gaps : List ℕ)
    (hg : ∀ h ∈ gaps, d ∣ h) (T : ℕ) (hT : T ≤ n) (hd : 0 < d) (z : ℂ) (hz : z ^ d = 1) :
    amplitude (sortWord p gaps) T z = amplitude p T z := by
  rw [amplitude_eq_residues _ T hT hd z hz, amplitude_eq_residues p T hT hd z hz]
  simp_rw [divisible_word_residueError p gaps hg]

private theorem prefix_geom (h r b : ℕ) (z : ℂ) :
    (∑ v ∈ range b, z ^ (r + h * v)) * (z ^ h - 1) = z ^ r * ((z ^ h) ^ b - 1) := by
  simp_rw [pow_add, pow_mul, ← mul_sum, mul_assoc, geom_sum_mul]

/-- Exact numerator for any complex evaluation point, even at resonance. -/
theorem gapSort_amplitude_numerator {n h : ℕ} (p : RankPlacement n) (T : ℕ)
    (hT : T ≤ n) (hh : 0 < h) (z : ℂ) :
    amplitude (gapSort p h) T z * (z ^ h - 1) =
    ∑ r : Fin h, z ^ r.val * ((z ^ h) ^ (chainLowerCount (thresholdSet p T) h r.val) -
      (z ^ h) ^ (residuePrefixCount h r.val T)) := by
  unfold amplitude slotError
  rw [← (positionChainEquiv n h hh).symm.sum_comp, Fintype.sum_sigma, sum_mul]
  apply sum_congr rfl
  intro r _
  simp_rw [lower_at_coord p hh T, positionChainEquiv_symm_val, ideal_ord T _ hh r.isLt]
  let b := chainLowerCount (thresholdSet p T) h r.val
  let a := residuePrefixCount h r.val T
  have bl : b ≤ sourceTrialLength (n / h) (n % h) r.val := by
    rw [← actual_chain_length n h hh r, chainPositions_card]
    exact chainLowerCount_le_length _ _ _
  have al : a ≤ sourceTrialLength (n / h) (n % h) r.val := by
    rw [← actual_chain_length n h hh r, chainPositions_card]
    unfold a residuePrefixCount
    exact sum_le_sum_of_subset_of_nonneg (range_mono hT) (by intros; positivity)
  let f := fun v : ℕ => z ^ (r.val + h * v)
  change (∑ v : Fin _, f v.val * (((if v.val < b then (1 : ℤ) else 0) -
    (if v.val < a then 1 else 0) : ℤ) : ℂ)) * _ = _
  simp_rw [Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero, mul_sub, mul_ite, mul_one,
    mul_zero]
  rw [sum_sub_distrib, prefixSum bl f, prefixSum al f, sub_mul]
  dsimp only [f]
  change _ = z ^ r.val * (z ^ h) ^ b - z ^ r.val * (z ^ h) ^ a
  linear_combination prefix_geom h r.val b z - prefix_geom h r.val a z

/-- A nonconstant phase on each h-chain: one two-endpoint error per residue. -/
theorem gapSort_amplitude_mul_norm {n h : ℕ} (p : RankPlacement n) (T : ℕ)
    (hT : T ≤ n) (hh : 0 < h) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖amplitude (gapSort p h) T z‖ * ‖z ^ h - 1‖ ≤ 2 * (h : ℝ) := by
  rw [← norm_mul, gapSort_amplitude_numerator p T hT hh z]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : Fin h, (2 : ℝ) := by
      apply sum_le_sum
      intro r _
      rw [norm_mul, norm_pow, hz, one_pow, one_mul]
      apply (norm_sub_le _ _).trans
      simp [norm_pow, hz]
      norm_num
    _ = _ := by simp; ring

theorem gapSort_amplitude_off_resonance {n h d : ℕ} (p : RankPlacement n) (T : ℕ)
    (hT : T ≤ n) (hh : 0 < h) (z : ℂ) (hz : ‖z‖ = 1)
    (hp : IsPrimitiveRoot z d) (off : ¬d ∣ h) :
    ‖amplitude (gapSort p h) T z‖ ≤ (2 * (h : ℝ))/‖z ^ h - 1‖ := by
  apply (le_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr (fun he => off ((hp.pow_eq_one_iff_dvd
    h).mp he))))).mpr
  exact gapSort_amplitude_mul_norm p T hT hh z hz

private theorem unit_geom_bound (w : ℂ) (hw : ‖w‖ = 1) (k : ℕ) :
    ‖∑ j ∈ range k, w ^ j‖ ≤ (k : ℝ) := by
  apply (norm_sum_le _ _).trans
  simp [norm_pow, hw]

/-- A nontrivial d-th root stays at least 1/d from one.
This weaker elementary bound needs neither trigonometry nor primitivity. -/
theorem root_gap_lower {d : ℕ} (hd : 0 < d) (w : ℂ) (hw : ‖w‖ = 1)
    (wd : w ^ d = 1) (hne : w ≠ 1) : 1 ≤ (d : ℝ)*‖w - 1‖ := by
  have geom := geom_sum_mul w d
  rw [wd, sub_self] at geom
  have zer := (mul_eq_zero.mp geom).resolve_right (sub_ne_zero.mpr hne)
  have ident : (∑ j ∈ range d, (1 - w ^ j)) = (d : ℂ) := by
    rw [sum_sub_distrib, zer]; simp
  have bound : ‖(d : ℂ)‖ ≤ (d : ℝ) * ((d : ℝ)*‖w - 1‖) := by
    rw [← ident]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _ ∈ range d, (d : ℝ)*‖w - 1‖ := by
        apply sum_le_sum
        intro j hj
        rw [norm_sub_rev, ← geom_sum_mul w j, norm_mul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact (unit_geom_bound w hw j).trans (by exact_mod_cast (mem_range.mp hj).le)
      _ = _ := by simp
  have D : (0 : ℝ) < d := by exact_mod_cast hd
  simpa using (le_of_mul_le_mul_left (a := (d : ℝ)) (b := 1) (c := (d : ℝ)*‖w - 1‖)
     (by simpa using bound) D)

theorem gapSort_amplitude_le_twice_gap_order {n h d : ℕ} (p : RankPlacement n) (T : ℕ)
    (hT : T ≤ n) (hh : 0 < h) (hd : 0 < d) (z : ℂ) (hz : ‖z‖ = 1)
    (hp : IsPrimitiveRoot z d) (off : ¬d ∣ h) :
    ‖amplitude (gapSort p h) T z‖ ≤ 2 * (h : ℝ) * d := by
  have wd : (z ^ h) ^ d = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hp.pow_eq_one, one_pow]
  have bound := root_gap_lower hd (z ^ h) (by simp [norm_pow, hz]) wd
    (fun he => off ((hp.pow_eq_one_iff_dvd h).mp he))
  let A := ‖amplitude (gapSort p h) T z‖
  change A ≤ _
  calc
    A ≤ A * ((d : ℝ)*‖z ^ h - 1‖) := le_mul_of_one_le_right (norm_nonneg _) bound
    _ = (A*‖z ^ h - 1‖) * (d : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (gapSort_amplitude_mul_norm p T hT hh z hz)
      (Nat.cast_nonneg _)

theorem amplitude_le_mass {n : ℕ} (p : RankPlacement n) (T : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖amplitude p T z‖ ≤ ∑ i, |(slotError p T i : ℝ)| := by
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i _
  simp [norm_pow, hz, Complex.norm_intCast]

/-- Concrete finite low-frequency certificate for two consecutive actual gaps:
clipping comes from the first gap; the d-divisible suffix preserves it. -/
theorem nondividing_then_divisible_squared {n h d : ℕ} (p : RankPlacement n)
    (T : ℕ) (hT : T ≤ n) (hh : 0 < h) (hd : 0 < d) (z : ℂ) (hz : ‖z‖ = 1)
    (hp : IsPrimitiveRoot z d) (off : ¬d ∣ h)
    (suffix : List ℕ) (hg : ∀ k ∈ suffix, d ∣ k) :
    ‖amplitude (sortWord (gapSort p h) suffix) T z‖ ^ 2 ≤
      (2 * (h : ℝ) * d) * (∑ i, |(slotError p T i : ℝ)|) := by
  rw [divisible_word_amplitude _ suffix hg T hT hd z hp.pow_eq_one, pow_two]
  have contracted : (∑ i, |slotError (gapSort p h) T i|) ≤ ∑ i, |slotError p T i| := by
    rw [gapSort_abs_error_exact p T hT hh]
    exact sum_abs_residueError_le p T hT hh
  have C : (∑ i, |(slotError (gapSort p h) T i : ℝ)|) ≤ ∑ i, |(slotError p T i : ℝ)| := by
    exact_mod_cast contracted
  exact mul_le_mul (gapSort_amplitude_le_twice_gap_order p T hT hh hd z hz hp off)
    ((amplitude_le_mass _ T z hz).trans C) (norm_nonneg _) (by positivity)






end Shellsort.RoughGapEndpoint
