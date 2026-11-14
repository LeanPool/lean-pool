/-
Copyright (c) 2026 LongTails contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Tyurin, QuocViet Pham, Valentin Khrulkov, Ivan Oseledets
-/
module

public import LeanPool.LongTails.Proofs.GeneralizedMixedRate

/-!
Adapted from k3nfalt/longtails, commit 269cbc764dd36851fd0b64f2f950f329ee127de4.
Modified for Lean Pool: module visibility, namespace isolation, and current Mathlib.
-/

@[expose] public section

open Finset

namespace LongTails.OracleTemplate.GeneralizedAccelerated

open LongTails.Setups.GeneralizedSmoothAndConvex

lemma exp_sub_one_le_mul_exp (d : ℝ) :
    Real.exp d - 1 ≤ d * Real.exp d := by
  have h := Real.add_one_le_exp (-d)
  have h' := mul_le_mul_of_nonneg_right h (Real.exp_pos d).le
  rw [← Real.exp_add] at h'
  simp only [neg_add_cancel, Real.exp_zero] at h'
  nlinarith

lemma nat_cube_le_exp_two (q : ℕ) : (q : ℝ) ^ 3 ≤ 48 * (2 : ℝ) ^ q := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    norm_num [Real.log_div] at h
    linarith
  have h := Real.pow_div_factorial_le_exp (Real.log 2 * (q : ℝ))
    (show 0 ≤ Real.log 2 * (q : ℝ) by positivity) 3
  norm_num [mul_comm (Real.log 2), Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 / 2 * (q : ℝ) by positivity)
    (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg q)) 3
  nlinarith

lemma logarithmic_charge_cube {u d : ℝ} (hu : 0 < u) (hd : 0 < d)
    (q : ℕ) (h : (2 : ℝ) ^ q ≤ 64 * Real.sqrt u * (Real.exp d - 1)) :
    (max 0 ((q : ℝ) - 4 * d)) ^ 3 ≤ 262144 * u * d ^ 2 := by
  by_cases hlarge : (q : ℝ) ≤ 4 * d
  · rw [max_eq_left (by linarith), zero_pow (by decide : 3 ≠ 0)]
    positivity
  · have hsmall : 2 * d ≤ Real.log 2 * q := by
      have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
        have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
        norm_num [Real.log_div] at ht
        linarith
      nlinarith [mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg q)]
    have he : Real.exp (2 * d) ≤ (2 : ℝ) ^ q := by
      have ht := Real.exp_le_exp.mpr hsmall
      simpa [mul_comm (Real.log 2), Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)] using ht
    have ht := exp_sub_one_le_mul_exp d
    have hs : (2 : ℝ) ^ q ≤ 64 * Real.sqrt u * (d * Real.exp d) :=
      h.trans (mul_le_mul_of_nonneg_left ht (by positivity))
    have hs2 := pow_le_pow_left₀ (show 0 ≤ (2 : ℝ) ^ q by positivity) hs 2
    have hexp : (Real.exp d) ^ 2 = Real.exp (2 * d) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simp only [mul_pow, Real.sq_sqrt hu.le, hexp] at hs2
    have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 4096 * u * d ^ 2 by positivity)
    have hb : (2 : ℝ) ^ q ≤ 4096 * u * d ^ 2 := by
      apply (mul_le_mul_iff_right₀ (show 0 < (2 : ℝ) ^ q by positivity)).mp
      nlinarith only [hs2, hm]
    have hc := nat_cube_le_exp_two q
    have hpow := pow_le_pow_left₀ (show 0 ≤ (q : ℝ) - 4 * d by linarith)
      (show (q : ℝ) - 4 * d ≤ (q : ℝ) by linarith) 3
    rw [max_eq_right (by linarith)]
    nlinarith [mul_nonneg hu.le (sq_nonneg d)]

lemma ordered_log_telescope {ι : Type*}
    (s : Finset ι) (time : ι → ℕ) (w : ι → ℝ) (B : ℝ)
    (hinj : Set.InjOn time (s : Set ι)) :
    (∑ i ∈ s, (Real.log (B + ∑ j ∈ s.filter (fun j => time j ≤ time i), w j) -
      Real.log (B + ∑ j ∈ s.filter (fun j => time j < time i), w j))) =
        Real.log (B + ∑ i ∈ s, w i) - Real.log B := by
  classical
  induction s using Finset.induction_on_max_value time with
  | empty => simp
  | insert a t ha hmax ih =>
    have hinjt : Set.InjOn time (t : Set ι) :=
      hinj.mono (by exact_mod_cast (subset_insert a t))
    have hlt : ∀ i ∈ t, time i < time a := by
      intro i hi
      apply lt_of_le_of_ne (hmax i hi)
      intro he
      have heq := hinj (mem_insert_of_mem hi) (mem_insert_self a t) he
      exact ha (heq ▸ hi)
    have hle_a : (insert a t).filter (fun j => time j ≤ time a) = insert a t := by
      apply filter_eq_self.mpr
      intro i hi
      rcases mem_insert.mp hi with rfl | hi
      · exact le_rfl
      · exact hmax i hi
    have hlt_a : (insert a t).filter (fun j => time j < time a) = t := by
      ext i
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | hi, hh⟩
        · exact (lt_irrefl _ hh).elim
        · exact hi
      · intro hi
        exact ⟨Or.inr hi, hlt i hi⟩
    have hle_i (i : ι) (hi : i ∈ t) :
        (insert a t).filter (fun j => time j ≤ time i) = t.filter (fun j => time j ≤ time i) := by
      rw [filter_insert]
      simp [not_le.mpr (hlt i hi)]
    have hlt_i (i : ι) (hi : i ∈ t) :
        (insert a t).filter (fun j => time j < time i) = t.filter (fun j => time j < time i) := by
      rw [filter_insert]
      simp [not_lt.mpr (hmax i hi)]
    rw [sum_insert ha, hle_a, hlt_a]
    have heq : (∑ i ∈ t, (Real.log (B + ∑ j ∈ (insert a t).filter (fun j => time j ≤ time i), w j) -
        Real.log (B + ∑ j ∈ (insert a t).filter (fun j => time j < time i), w j))) =
        Real.log (B + ∑ i ∈ t, w i) - Real.log B := by
      convert ih hinjt using 1
      apply sum_congr rfl
      intro i hi
      rw [hle_i i hi, hlt_i i hi]
    rw [heq]
    ring

lemma ordered_log_increments {ι : Type*}
    (s : Finset ι) (time : ι → ℕ) (w : ι → ℝ) {B : ℝ}
    (hB : 0 < B) (hw : ∀ i ∈ s, 0 < w i)
    (hinj : Set.InjOn time (s : Set ι)) :
    (∑ i ∈ s, Real.log (1 + w i /
      (B + ∑ j ∈ s.filter (fun j => time j < time i), w j))) =
        Real.log ((B + ∑ i ∈ s, w i) / B) := by
  classical
  have htotal : 0 < B + ∑ i ∈ s, w i :=
    add_pos_of_pos_of_nonneg hB (sum_nonneg (fun i hi => (hw i hi).le))
  rw [Real.log_div htotal.ne' hB.ne', ← ordered_log_telescope s time w B hinj]
  apply sum_congr rfl
  intro i hi
  have hWi : 0 < B + ∑ j ∈ s.filter (fun j => time j < time i), w j :=
    add_pos_of_pos_of_nonneg hB (sum_nonneg (fun j hj => (hw j (mem_filter.mp hj).1).le))
  have hf : s.filter (fun j => time j ≤ time i) =
      insert i (s.filter (fun j => time j < time i)) := by
    ext j
    simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨hj, hji⟩
      rcases lt_or_eq_of_le hji with hlt | heq
      · exact Or.inr ⟨hj, hlt⟩
      · exact Or.inl (hinj hj hi heq)
    · rintro (rfl | ⟨hj, hji⟩)
      · exact ⟨hi, le_rfl⟩
      · exact ⟨hj, hji.le⟩
  rw [hf, sum_insert (by simp)]
  have he : 1 + w i / (B + ∑ j ∈ s.filter (fun j => time j < time i), w j) =
      (B + (w i + ∑ j ∈ s.filter (fun j => time j < time i), w j)) /
        (B + ∑ j ∈ s.filter (fun j => time j < time i), w j) := by
    field_simp
    ring
  rw [he, Real.log_div (by linarith [hw i hi]) hWi.ne']

lemma high_count_self_normalized {ι : Type*}
    (s : Finset ι) (time : ι → ℕ) (A G : ι → ℝ) (q : ι → ℕ)
    {A0 Afinal H : ℝ} (hA0 : 0 < A0) (hAF : A0 ≤ Afinal)
    (hA : ∀ i ∈ s, A0 ≤ A i) (hG : ∀ i ∈ s, 0 < G i)
    (hH : 0 ≤ H) (hinj : Set.InjOn time (s : Set ι))
    (henergy : (∑ i ∈ s, A i * G i) ≤ H)
    (hweights : (∑ i ∈ s, (2 : ℝ) ^ q i / Real.sqrt (G i)) ≤ 32 * Real.sqrt Afinal)
    (hprefix : ∀ i ∈ s,
      (∑ j ∈ s.filter (fun j => time j < time i), (2 : ℝ) ^ q j / Real.sqrt (G j)) ≤
        32 * Real.sqrt (A i)) :
    let D := Real.log (2 * Afinal / A0)
    (∑ i ∈ s, (q i : ℝ)) ≤ 4 * D + 64 * (H * D ^ 2) ^ (1 / 3 : ℝ) := by
  classical
  let w := fun i => (2 : ℝ) ^ q i / Real.sqrt (G i)
  let B := 32 * Real.sqrt A0
  let W := fun i => B + ∑ j ∈ s.filter (fun j => time j < time i), w j
  let d := fun i => Real.log (1 + w i / W i)
  let z := fun i => max 0 ((q i : ℝ) - 4 * d i)
  let D := Real.log (2 * Afinal / A0)
  have hB : 0 < B := by dsimp [B]; positivity
  have hw : ∀ i ∈ s, 0 < w i := by
    intro i hi
    exact div_pos (by positivity) (Real.sqrt_pos.mpr (hG i hi))
  have hW : ∀ i ∈ s, 0 < W i := by
    intro i hi
    exact add_pos_of_pos_of_nonneg hB
      (sum_nonneg (fun j hj => (hw j (mem_filter.mp hj).1).le))
  have hd : ∀ i ∈ s, 0 < d i := by
    intro i hi
    apply Real.log_pos
    have hh := div_pos (hw i hi) (hW i hi)
    change 1 < 1 + w i / W i
    linarith
  have hz : ∀ i ∈ s, 0 ≤ z i := fun _ _ => le_max_left _ _
  have hAi : ∀ i ∈ s, 0 < A i := fun i hi => hA0.trans_le (hA i hi)
  have hWi : ∀ i ∈ s, W i ≤ 64 * Real.sqrt (A i) := by
    intro i hi
    have hh := Real.sqrt_le_sqrt (hA i hi)
    have hp := hprefix i hi
    change (∑ j ∈ s.filter (fun j => time j < time i), w j) ≤ _ at hp
    dsimp only [W, B]
    linarith
  have hcube : ∀ i ∈ s, z i ^ 3 ≤ (262144 * (A i * G i)) * d i ^ 2 := by
    intro i hi
    have he : Real.exp (d i) - 1 = w i / W i := by
      dsimp only [d]
      rw [Real.exp_log (by linarith [div_pos (hw i hi) (hW i hi)])]
      ring
    have ht : (2 : ℝ) ^ q i ≤ 64 * Real.sqrt (A i * G i) * (Real.exp (d i) - 1) := by
      rw [he, Real.sqrt_mul (hAi i hi).le]
      dsimp only [w]
      have hGi := (Real.sqrt_pos.mpr (hG i hi)).ne'
      have hWi0 := (hW i hi).ne'
      have hid : 64 * (Real.sqrt (A i) * Real.sqrt (G i)) *
          ((2 : ℝ) ^ q i / Real.sqrt (G i) / W i) =
          (64 * Real.sqrt (A i) * (2 : ℝ) ^ q i) / W i := by
        field_simp
      rw [hid]
      apply (le_div_iff₀ (hW i hi)).mpr
      have hh := mul_le_mul_of_nonneg_left (hWi i hi) (show 0 ≤ (2 : ℝ) ^ q i by positivity)
      nlinarith only [hh]
    exact logarithmic_charge_cube (mul_pos (hAi i hi) (hG i hi)) (hd i hi) (q i) ht
  have hholder := weighted_holder_cube s (fun i => 262144 * (A i * G i)) d z
    (fun i hi => mul_nonneg (by norm_num) (mul_nonneg (hAi i hi).le (hG i hi).le)) hd hz hcube
  have hsumd : (∑ i ∈ s, d i) ≤ D := by
    rw [show (∑ i ∈ s, d i) = Real.log ((B + ∑ i ∈ s, w i) / B) from
      ordered_log_increments s time w hB hw hinj]
    have hsumw := sum_nonneg (fun i hi => (hw i hi).le)
    apply Real.log_le_log (by positivity)
    apply (div_le_div_iff₀ hB hA0).mpr
    have hp := hweights
    change (∑ i ∈ s, w i) ≤ 32 * Real.sqrt Afinal at hp
    have hs0 := Real.sq_sqrt hA0.le
    have hsF := Real.sq_sqrt (hA0.le.trans hAF)
    have hs := Real.sqrt_le_sqrt hAF
    have hm := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg Afinal)
    have ht := mul_le_mul_of_nonneg_right hp hA0.le
    dsimp only [B]
    nlinarith [Real.sqrt_nonneg A0, Real.sqrt_nonneg Afinal]
  have hD : 0 ≤ D := (sum_nonneg (fun i hi => (hd i hi).le)).trans hsumd
  have hdsq := pow_le_pow_left₀ (sum_nonneg (fun i hi => (hd i hi).le)) hsumd 2
  have hbound : (∑ i ∈ s, z i) ^ 3 ≤ 262144 * (H * D ^ 2) := by
    rw [← mul_sum] at hholder
    have hm := mul_le_mul henergy hdsq (sq_nonneg _) hH
    nlinarith only [hholder, hm]
  have hroot : ((H * D ^ 2) ^ (1 / 3 : ℝ)) ^ 3 = H * D ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ H * D ^ 2)]
    norm_num
  have hzbound : (∑ i ∈ s, z i) ≤ 64 * (H * D ^ 2) ^ (1 / 3 : ℝ) := by
    apply (pow_le_pow_iff_left₀ (sum_nonneg hz) (by positivity) (by decide : 3 ≠ 0)).mp
    rw [mul_pow, hroot]
    norm_num
    exact hbound
  have hcount : (∑ i ∈ s, (q i : ℝ)) ≤ 4 * (∑ i ∈ s, d i) + ∑ i ∈ s, z i := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro i hi
    have hh := le_max_right 0 ((q i : ℝ) - 4 * d i)
    dsimp only [z]
    linarith
  change (∑ i ∈ s, (q i : ℝ)) ≤ 4 * D + _
  linarith

end LongTails.OracleTemplate.GeneralizedAccelerated
