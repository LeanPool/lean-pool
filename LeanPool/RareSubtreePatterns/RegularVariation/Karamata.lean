/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.RegularVariation.Potter
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.PSeries
public import Mathlib.Algebra.Order.Group.Indicator

/-!
# Karamata-type sums for regularly varying sequences

Source lines 1141–1148 and 1173–1179 (inventory B12): for a monotone sequence `a`, positive at
`n ≥ 1`, regularly varying of index `ρ`:

* `RegularlyVaryingSeq.karamata_tail` (`ρ > 0`): `∑_{m < q ≤ N} 1 / (q a_q) ≤ C / a_m` for all
  `1 ≤ m` and all `N`, with one constant `C`; `RegularlyVaryingSeq.summable_inv_mul` and
  `RegularlyVaryingSeq.karamata_tail_tsum` give summability and the bound for the full tail
  `∑_{q > m}` (a `tsum` of an indicator).
* `RegularlyVaryingSeq.karamata_sum` (`0 ≤ ρ < 1`): `∑_{h=1}^{n} 1 / a_h ≤ C n / a_n` for all
  `n`.

The source invokes "Karamata's theorem". Here the bounds follow from the global Potter bounds
(`RegularlyVaryingSeq.exists_potter_global`) by comparison with the power sums
`∑_{q > m} q^{-1-s} ≤ m^{-s}/s` and `∑_{h ≤ n} h^{-s} ≤ n^{1-s}/(1-s)`, which are proved by
telescoping.
-/

@[expose] public section

open Filter
open scoped Topology

namespace PoissonDeclumping

/-- Telescoping bound for negative powers: for `0 < y ≤ z` and `s ≥ 0`,
`s (z - y) z^(-s-1) ≤ y^(-s) - z^(-s)`. -/
theorem rpow_neg_sub_rpow_neg_ge {y z s : ℝ} (hy : 0 < y) (hyz : y ≤ z) (hs : 0 ≤ s) :
    s * (z - y) * z ^ (-s - 1) ≤ y ^ (-s) - z ^ (-s) := by
  have hz : 0 < z := hy.trans_le hyz
  set w : ℝ := y / z with hwdef
  have hw : 0 < w := div_pos hy hz
  have hyw : y = z * w := by rw [hwdef]; field_simp
  have hb : 1 + s * (1 - w) ≤ w ^ (-s) := by
    rw [Real.rpow_def_of_pos hw]
    have h1 := Real.log_le_sub_one_of_pos hw
    have h2 := Real.add_one_le_exp (Real.log w * -s)
    nlinarith [mul_nonneg hs (sub_nonneg.2 h1)]
  have hzs : 0 < z ^ (-s) := Real.rpow_pos_of_pos hz _
  rw [hyw, Real.mul_rpow hz.le hw.le, Real.rpow_sub_one hz.ne']
  have e : s * (z - z * w) * (z ^ (-s) / z) = z ^ (-s) * (s * (1 - w)) := by
    field_simp
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hb hzs.le]

/-- Telescoping bound for powers in `[0,1]`: for `0 ≤ y ≤ z`, `0 < z` and `0 ≤ p ≤ 1`,
`p (z - y) z^(p-1) ≤ z^p - y^p`. -/
theorem rpow_sub_rpow_ge {y z p : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) (hz : 0 < z) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) : p * (z - y) * z ^ (p - 1) ≤ z ^ p - y ^ p := by
  set w : ℝ := y / z with hwdef
  have hw0 : 0 ≤ w := div_nonneg hy hz.le
  have hw1 : w ≤ 1 := by rw [hwdef, div_le_one hz]; exact hyz
  have hyw : y = z * w := by rw [hwdef]; field_simp
  have hb : w ^ p ≤ 1 + p * (w - 1) := by
    have := rpow_one_add_le_one_add_mul_self (s := w - 1) (by linarith) hp0 hp1
    simpa using this
  have hzp : 0 < z ^ p := Real.rpow_pos_of_pos hz _
  rw [hyw, Real.mul_rpow hz.le hw0, Real.rpow_sub_one hz.ne']
  have e : p * (z - z * w) * (z ^ p / z) = z ^ p * (p * (1 - w)) := by
    field_simp
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hb hzp.le]

/-- `∑_{m < q ≤ N} q^(-s-1) ≤ m^(-s) / s` for `s > 0`, `m ≥ 1`. -/
theorem sum_Ioc_rpow_neg_le {s : ℝ} (hs : 0 < s) {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    ∑ q ∈ Finset.Ioc m N, (q : ℝ) ^ (-s - 1) ≤ (m : ℝ) ^ (-s) / s := by
  have key : ∀ N, m ≤ N →
      ∑ q ∈ Finset.Ioc m N, (q : ℝ) ^ (-s - 1) ≤ ((m : ℝ) ^ (-s) - (N : ℝ) ^ (-s)) / s := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp
    | succ N hmN ih =>
      rw [Finset.sum_Ioc_succ_top hmN]
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hm.trans hmN
      have h := rpow_neg_sub_rpow_neg_ge hN0 (by linarith : (N : ℝ) ≤ N + 1) hs.le
      rw [show ((N : ℝ) + 1 - N) = 1 by ring, mul_one] at h
      have ht : ((N : ℝ) + 1) ^ (-s - 1) ≤ ((N : ℝ) ^ (-s) - ((N : ℝ) + 1) ^ (-s)) / s := by
        rw [le_div_iff₀ hs]
        linarith
      push_cast
      calc ∑ q ∈ Finset.Ioc m N, (q : ℝ) ^ (-s - 1) + ((N : ℝ) + 1) ^ (-s - 1)
          ≤ ((m : ℝ) ^ (-s) - (N : ℝ) ^ (-s)) / s +
              ((N : ℝ) ^ (-s) - ((N : ℝ) + 1) ^ (-s)) / s := add_le_add ih ht
        _ = ((m : ℝ) ^ (-s) - ((N : ℝ) + 1) ^ (-s)) / s := by ring
  rcases le_total m N with h | h
  · calc ∑ q ∈ Finset.Ioc m N, (q : ℝ) ^ (-s - 1)
        ≤ ((m : ℝ) ^ (-s) - (N : ℝ) ^ (-s)) / s := key N h
      _ ≤ (m : ℝ) ^ (-s) / s := by
          have : 0 ≤ (N : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
          gcongr
          linarith
  · rw [Finset.Ioc_eq_empty_of_le h, Finset.sum_empty]
    positivity

/-- `∑_{h=1}^{n} h^(-s) ≤ n^(1-s) / (1-s)` for `0 ≤ s < 1`. -/
theorem sum_Icc_rpow_neg_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (n : ℕ) :
    ∑ h ∈ Finset.Icc 1 n, (h : ℝ) ^ (-s) ≤ (n : ℝ) ^ (1 - s) / (1 - s) := by
  induction n with
  | zero =>
    simp only [Finset.Icc_eq_empty_of_lt zero_lt_one, Finset.sum_empty, Nat.cast_zero]
    exact div_nonneg (Real.rpow_nonneg le_rfl _) (by linarith)
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    have h := rpow_sub_rpow_ge (y := n) (z := n + 1) (p := 1 - s) (Nat.cast_nonneg _)
      (by linarith) (by positivity) (by linarith) (by linarith)
    rw [show (1 - s) - 1 = -s by ring, show ((n : ℝ) + 1 - n) = 1 by ring, mul_one] at h
    have ht : ((n : ℝ) + 1) ^ (-s) ≤ (((n : ℝ) + 1) ^ (1 - s) - (n : ℝ) ^ (1 - s)) / (1 - s) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    push_cast
    calc ∑ h ∈ Finset.Icc 1 n, (h : ℝ) ^ (-s) + ((n : ℝ) + 1) ^ (-s)
        ≤ (n : ℝ) ^ (1 - s) / (1 - s) +
            (((n : ℝ) + 1) ^ (1 - s) - (n : ℝ) ^ (1 - s)) / (1 - s) := add_le_add ih ht
      _ = ((n : ℝ) + 1) ^ (1 - s) / (1 - s) := by ring

namespace RegularlyVaryingSeq

variable {ρ : ℝ} {a : ℕ → ℝ}

/-- Termwise comparison behind the Karamata tail bound: with `s = ρ/2`, there is `C > 0` with
`1 / (q a_q) ≤ (C m^s / a_m) q^(-s-1)` for all `1 ≤ m ≤ q`. -/
theorem exists_inv_mul_le (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m q : ℕ, 1 ≤ m → m ≤ q →
      1 / ((q : ℝ) * a q) ≤ (C * (m : ℝ) ^ (ρ / 2) / a m) * (q : ℝ) ^ (-(ρ / 2) - 1) := by
  obtain ⟨C, hC, hCb⟩ := hrv.exists_potter_global hmono hpos hρ.le (half_pos hρ)
  refine ⟨C, hC, fun m q hm hmq => ?_⟩
  set s : ℝ := ρ / 2 with hsdef
  have hq1 : 1 ≤ q := hm.trans hmq
  have ham := hpos m hm
  have haq := hpos q hq1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq1
  have h := (hCb m q hm hmq).2
  rw [show ρ - ρ / 2 = s by rw [hsdef]; ring, Real.div_rpow hqR.le hmR.le] at h
  have hqs : 0 < (q : ℝ) ^ s := by positivity
  have hms : 0 < (m : ℝ) ^ s := by positivity
  have h' : (q : ℝ) ^ s * a m ≤ C * a q * (m : ℝ) ^ s := by
    have := mul_le_mul_of_nonneg_right h hms.le
    rwa [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_cancel_right₀ _ hms.ne'] at this
  have e : (q : ℝ) ^ (-s - 1) = 1 / ((q : ℝ) ^ s * q) := by
    rw [Real.rpow_sub_one hqR.ne', Real.rpow_neg hqR.le]
    field_simp
  rw [e, div_le_iff₀ (by positivity)]
  have e2 : C * (m : ℝ) ^ s / a m * (1 / ((q : ℝ) ^ s * q)) * (q * a q) =
      (C * a q * (m : ℝ) ^ s) / ((q : ℝ) ^ s * a m) := by
    field_simp
  rw [e2, le_div_iff₀ (by positivity), one_mul]
  exact h'

/-- The series `∑_q 1 / (q a_q)` converges (positive index). -/
theorem summable_inv_mul (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hρ : 0 < ρ) :
    Summable (fun q : ℕ => 1 / ((q : ℝ) * a q)) := by
  obtain ⟨C, hC, hCb⟩ := hrv.exists_inv_mul_le hmono hpos hρ
  have ha1 := hpos 1 le_rfl
  have hsum : Summable (fun q : ℕ => (C * ((1 : ℕ) : ℝ) ^ (ρ / 2) / a 1) *
      (q : ℝ) ^ (-(ρ / 2) - 1)) :=
    (Real.summable_nat_rpow.2 (by linarith)).mul_left _
  refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) hsum
  · rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    · have := hpos q hq
      positivity
  · rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp only [Nat.cast_zero, zero_mul, div_zero]
      rw [Real.zero_rpow (by linarith), mul_zero]
    · exact hCb 1 q le_rfl hq

/-- **Karamata tail bound** (source lines 1141–1148): for `ρ > 0` there is `C > 0` such that
for all `m ≥ 1` and all `N`, `∑_{m < q ≤ N} 1 / (q a_q) ≤ C / a_m`. -/
theorem karamata_tail (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m N : ℕ, 1 ≤ m →
      ∑ q ∈ Finset.Ioc m N, 1 / ((q : ℝ) * a q) ≤ C / a m := by
  obtain ⟨C, hC, hCb⟩ := hrv.exists_inv_mul_le hmono hpos hρ
  have hs : 0 < ρ / 2 := half_pos hρ
  refine ⟨C / (ρ / 2), by positivity, fun m N hm => ?_⟩
  have ham := hpos m hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hK : 0 ≤ C * (m : ℝ) ^ (ρ / 2) / a m := by positivity
  calc ∑ q ∈ Finset.Ioc m N, 1 / ((q : ℝ) * a q)
      ≤ ∑ q ∈ Finset.Ioc m N, (C * (m : ℝ) ^ (ρ / 2) / a m) * (q : ℝ) ^ (-(ρ / 2) - 1) := by
        apply Finset.sum_le_sum
        intro q hq
        exact hCb m q hm (Finset.mem_Ioc.1 hq).1.le
    _ = (C * (m : ℝ) ^ (ρ / 2) / a m) * ∑ q ∈ Finset.Ioc m N, (q : ℝ) ^ (-(ρ / 2) - 1) := by
        rw [Finset.mul_sum]
    _ ≤ (C * (m : ℝ) ^ (ρ / 2) / a m) * ((m : ℝ) ^ (-(ρ / 2)) / (ρ / 2)) :=
        mul_le_mul_of_nonneg_left (sum_Ioc_rpow_neg_le hs hm N) hK
    _ = C / (ρ / 2) / a m := by
        rw [Real.rpow_neg hmR.le]
        have : (0 : ℝ) < (m : ℝ) ^ (ρ / 2) := by positivity
        field_simp

/-- **Karamata tail bound**, full-tail form: for `ρ > 0` there is `C > 0` such that for all
`m ≥ 1`, `∑_{q > m} 1 / (q a_q) ≤ C / a_m` (the series being summable, see
`summable_inv_mul`). -/
theorem karamata_tail_tsum (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      ∑' q : ℕ, (Set.Ioi m).indicator (fun q : ℕ => 1 / ((q : ℝ) * a q)) q ≤ C / a m := by
  obtain ⟨C, hC, hCb⟩ := hrv.karamata_tail hmono hpos hρ
  refine ⟨C, hC, fun m hm => ?_⟩
  set f : ℕ → ℝ := fun q : ℕ => 1 / ((q : ℝ) * a q) with hfdef
  have hf0 : ∀ q, 0 ≤ f q := by
    intro q
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp [hfdef]
    · have := hpos q hq
      simp only [hfdef]
      positivity
  have hg0 : ∀ q, 0 ≤ (Set.Ioi m).indicator f q := fun q => Set.indicator_nonneg (fun q _ => hf0
    q) q
  -- partial sums of the indicator are bounded by the finite tail sums
  have key : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), (Set.Ioi m).indicator f i ≤
      ∑ q ∈ Finset.Ioc m n, f q := by
    intro n
    induction n with
    | zero =>
      rw [Finset.sum_range_one, Set.indicator_of_notMem (by simp)]
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      rcases le_or_gt m n with hmn | hmn
      · rw [Finset.sum_Ioc_succ_top hmn, Set.indicator_of_mem (by simp; omega)]
        linarith
      · rw [Set.indicator_of_notMem (by simp; omega), add_zero,
          Finset.Ioc_eq_empty_of_le (by omega : n + 1 ≤ m)]
        rw [Finset.Ioc_eq_empty_of_le (by omega : n ≤ m)] at ih
        exact ih
  apply Real.tsum_le_of_sum_range_le hg0
  intro n
  calc ∑ i ∈ Finset.range n, (Set.Ioi m).indicator f i
      ≤ ∑ i ∈ Finset.range (n + 1), (Set.Ioi m).indicator f i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
          (fun i _ _ => hg0 i)
    _ ≤ ∑ q ∈ Finset.Ioc m n, f q := key n
    _ ≤ C / a m := hCb m n hm

/-- **Karamata partial-sum bound** (source lines 1173–1179): for `0 ≤ ρ < 1` there is `C > 0`
such that for all `n`, `∑_{h=1}^{n} 1 / a_h ≤ C n / a_n`. -/
theorem karamata_sum (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∑ h ∈ Finset.Icc 1 n, 1 / a h ≤ C * n / a n := by
  have hδ : 0 < (1 - ρ) / 2 := by linarith
  obtain ⟨C, hC, hCb⟩ := hrv.exists_potter_global hmono hpos hρ0 hδ
  set s : ℝ := ρ + (1 - ρ) / 2 with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; linarith
  have hs1 : s < 1 := by rw [hsdef]; linarith
  refine ⟨C / (1 - s), div_pos hC (by linarith), fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have han := hpos n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : 0 ≤ C * (n : ℝ) ^ s / a n := by positivity
  have hterm : ∀ h ∈ Finset.Icc 1 n, 1 / a h ≤ (C * (n : ℝ) ^ s / a n) * (h : ℝ) ^ (-s) := by
    intro h hh
    rw [Finset.mem_Icc] at hh
    have hah := hpos h hh.1
    have hhR : (0 : ℝ) < h := by exact_mod_cast hh.1
    have H := (hCb h n hh.1 hh.2).1
    rw [Real.div_rpow hnR.le hhR.le] at H
    have hhs : 0 < (h : ℝ) ^ s := by positivity
    rw [Real.rpow_neg hhR.le, div_le_iff₀ hah]
    have e : C * (n : ℝ) ^ s / a n * ((h : ℝ) ^ s)⁻¹ * a h =
        (C * (n : ℝ) ^ s * a h) / (a n * (h : ℝ) ^ s) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity), one_mul]
    calc a n * (h : ℝ) ^ s ≤ C * ((n : ℝ) ^ s / (h : ℝ) ^ s) * a h * (h : ℝ) ^ s :=
          mul_le_mul_of_nonneg_right H hhs.le
      _ = C * (n : ℝ) ^ s * a h := by field_simp
  calc ∑ h ∈ Finset.Icc 1 n, 1 / a h
      ≤ ∑ h ∈ Finset.Icc 1 n, (C * (n : ℝ) ^ s / a n) * (h : ℝ) ^ (-s) := Finset.sum_le_sum hterm
    _ = (C * (n : ℝ) ^ s / a n) * ∑ h ∈ Finset.Icc 1 n, (h : ℝ) ^ (-s) := by
        rw [Finset.mul_sum]
    _ ≤ (C * (n : ℝ) ^ s / a n) * ((n : ℝ) ^ (1 - s) / (1 - s)) :=
        mul_le_mul_of_nonneg_left (sum_Icc_rpow_neg_le hs0 hs1 n) hK
    _ = C / (1 - s) * n / a n := by
        rw [Real.rpow_sub hnR, Real.rpow_one]
        have : (0 : ℝ) < (n : ℝ) ^ s := by positivity
        have : (0 : ℝ) < 1 - s := by linarith
        field_simp

end RegularlyVaryingSeq

end PoissonDeclumping
