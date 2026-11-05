/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.ScalesConcentration.Mgf
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# MgfProduct

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Concentration for scale arrays — Step 4 helpers (`e.full.mgf.bound`)

This module collects the *generic* analytic and combinatorial lemmas feeding the
Step-4 residue-class MGF product (`full_mgf_bound`, assembled in `Chernoff.lean`),
kept free of the `expZfun` / `ColumnsIndep` machinery so they read cleanly:

* `prod_add_one_le_exp_ofReal` — `∏ (1 + c_i) ≤ exp(∑ c_i)` in `ℝ≥0∞` (sub-part (d));
* `dcol` and `sum_three_dcol_le` — the window-distance `d_j` and the two-sided
  geometric `ℤ`-sum `∑_{j∈[-N,N]} 3^{-(sp/2) d_j} ≤ 3(m+1)` (sub-part (e));
* `three_div_lam_rpow` — the `λ`-substitution algebra `(3/λ)^p = θ/K`;
* `er_npow` — the `ℝ≥0∞` `rpow` bridge `e_r^n = (B^n)^{1/r}` used by Hölder.
-/

namespace Algsuperdiff.Section4.Probability.ScalesConcentration

open MeasureTheory Finset
open scoped ENNReal NNReal

/-! ### (d) product of `1 + c_j` bounded by an exponential -/

/-- `∏_{i∈s} (1 + c_i) ≤ exp(∑_{i∈s} c_i)` for nonnegative `c`. -/
lemma prod_add_one_le_exp {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) :
    ∏ i ∈ s, (1 + c i) ≤ Real.exp (∑ i ∈ s, c i) := by
  rw [Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun i hi => by linarith [hc i hi]) (fun i _ => ?_)
  linarith [Real.add_one_le_exp (c i)]

/-- `∏_{i∈s} ofReal(1 + c_i) ≤ ofReal(exp(∑_{i∈s} c_i))` for nonnegative `c`. -/
lemma prod_add_one_le_exp_ofReal {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) :
    ∏ i ∈ s, ENNReal.ofReal (1 + c i) ≤ ENNReal.ofReal (Real.exp (∑ i ∈ s, c i)) := by
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i hi => by linarith [hc i hi])]
  exact ENNReal.ofReal_le_ofReal (prod_add_one_le_exp s c hc)

/-! ### (e) window distance `d_j` and the two-sided geometric sum -/

/-- The distance from `j` to the window `{0, …, m}`, as a natural number
(`0` inside the window, `j - m` to the right, `-j` to the left). -/
noncomputable def dcol (m : ℕ) (j : ℤ) : ℕ := (max (max (j - (m : ℤ)) (-j)) 0).toNat

/-- `d_j` lower-bounds the shell distance `|k - j|` for every `k ∈ {0,…,m}`. -/
lemma dcol_le {m : ℕ} {j k : ℤ} (hk : k ∈ Finset.Icc (0 : ℤ) (m : ℤ)) :
    dcol m j ≤ (k - j).natAbs := by
  rw [Finset.mem_Icc] at hk
  unfold dcol
  omega

/-- `d_j = 0` exactly on the window `{0,…,m}`. -/
lemma dcol_eq_zero_iff {m : ℕ} {j : ℤ} : dcol m j = 0 ↔ 0 ≤ j ∧ j ≤ (m : ℤ) := by
  unfold dcol; omega

/-- For a positive distance `ℓ`, only `j = m + ℓ` or `j = -ℓ` reach it. -/
lemma dcol_fiber_subset {m ℓ : ℕ} (hℓ : 1 ≤ ℓ) (W : Finset ℤ) :
    W.filter (fun j => dcol m j = ℓ) ⊆ ({(m : ℤ) + ℓ, -(ℓ : ℤ)} : Finset ℤ) := by
  intro j hj
  rw [Finset.mem_filter] at hj
  have hd : dcol m j = ℓ := hj.2
  unfold dcol at hd
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- At most two indices reach a given positive distance `ℓ`. -/
lemma dcol_fiber_card_le {m ℓ : ℕ} (hℓ : 1 ≤ ℓ) (W : Finset ℤ) :
    (W.filter (fun j => dcol m j = ℓ)).card ≤ 2 := by
  refine le_trans (Finset.card_le_card (dcol_fiber_subset hℓ W)) ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  simp

/-- At most `m + 1` indices reach distance `0`. -/
lemma dcol_fiber0_card_le {m : ℕ} (W : Finset ℤ) :
    (W.filter (fun j => dcol m j = 0)).card ≤ m + 1 := by
  have hsub : W.filter (fun j => dcol m j = 0) ⊆ Finset.Icc (0 : ℤ) (m : ℤ) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_Icc]
    exact dcol_eq_zero_iff.1 hj.2
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [Int.card_Icc]
  omega

/-- **Two-sided geometric window sum (raw form).**  For `q ∈ [0,1)`,
`∑_{j∈[-N,N]} q^{d_j} ≤ (m+1) + 2 q/(1-q)`. -/
lemma sum_dcol_geom_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (m N : ℕ) :
    ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), q ^ (dcol m j)
      ≤ ((m : ℝ) + 1) + 2 * (q / (1 - q)) := by
  classical
  set W := Finset.Icc (-(N : ℤ)) (N : ℤ) with hW
  set img := W.image (dcol m) with himg
  have h1q : (0 : ℝ) < 1 - q := by linarith
  -- fiberwise decomposition over the distance value
  have hfiber : ∑ j ∈ W, q ^ (dcol m j)
      = ∑ ℓ ∈ img, (W.filter (fun j => dcol m j = ℓ)).card • q ^ ℓ := by
    rw [← Finset.sum_fiberwise_of_maps_to' (g := dcol m) (t := img)
          (fun j hj => Finset.mem_image_of_mem _ hj) (fun ℓ => q ^ ℓ)]
    exact Finset.sum_congr rfl fun ℓ _ => Finset.sum_const _
  rw [hfiber, ← Finset.sum_filter_add_sum_filter_not img (fun ℓ => ℓ = 0)]
  -- ℓ = 0 part ≤ m + 1
  have hA : ∑ ℓ ∈ img.filter (fun ℓ => ℓ = 0),
        (W.filter (fun j => dcol m j = ℓ)).card • q ^ ℓ ≤ (m : ℝ) + 1 := by
    calc ∑ ℓ ∈ img.filter (fun ℓ => ℓ = 0),
            (W.filter (fun j => dcol m j = ℓ)).card • q ^ ℓ
        ≤ ∑ _ℓ ∈ img.filter (fun ℓ => ℓ = 0), ((m : ℝ) + 1) := by
          refine Finset.sum_le_sum (fun ℓ hℓ => ?_)
          obtain ⟨_, rfl⟩ := Finset.mem_filter.1 hℓ
          rw [pow_zero, nsmul_eq_mul, mul_one]
          exact_mod_cast dcol_fiber0_card_le W
      _ ≤ (m : ℝ) + 1 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          have hc1 : (img.filter (fun ℓ => ℓ = 0)).card ≤ 1 := by
            refine Finset.card_le_one.2 (fun a ha b hb => ?_)
            rw [Finset.mem_filter] at ha hb; omega
          have : ((img.filter (fun ℓ => ℓ = 0)).card : ℝ) ≤ 1 := by exact_mod_cast hc1
          nlinarith [this, (show (0 : ℝ) ≤ (m : ℝ) + 1 by positivity)]
  -- ℓ ≠ 0 part ≤ 2 q/(1-q)
  have hgeo : ∑ ℓ ∈ img.filter (fun ℓ => ¬ ℓ = 0), q ^ ℓ ≤ q / (1 - q) := by
    rcases Finset.eq_empty_or_nonempty (img.filter (fun ℓ => ¬ ℓ = 0)) with he | hne
    · rw [he, Finset.sum_empty]; positivity
    · set S := img.filter (fun ℓ => ¬ ℓ = 0) with hS
      set M := S.max' hne with hM
      have hSsub : S ⊆ Finset.Icc 1 M := by
        intro ℓ hℓ; rw [Finset.mem_Icc]
        exact ⟨Nat.one_le_iff_ne_zero.2 (Finset.mem_filter.1 hℓ).2, Finset.le_max' S ℓ hℓ⟩
      calc ∑ ℓ ∈ S, q ^ ℓ
          ≤ ∑ ℓ ∈ Finset.Icc 1 M, q ^ ℓ :=
            Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun ℓ _ _ => pow_nonneg hq0 ℓ)
        _ = ∑ i ∈ Finset.range M, q ^ (1 + i) := by
            rw [← Finset.Ico_succ_right_eq_Icc, Order.succ_eq_add_one,
              Finset.sum_Ico_eq_sum_range]
            simp
        _ = q * ∑ i ∈ Finset.range M, q ^ i := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun i _ => by rw [pow_add, pow_one, mul_comm])
        _ ≤ q * (1 - q)⁻¹ := by
            refine mul_le_mul_of_nonneg_left ?_ hq0
            calc ∑ i ∈ Finset.range M, q ^ i
                ≤ ∑' i : ℕ, q ^ i :=
                  (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _
                    (fun i _ => pow_nonneg hq0 i)
              _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0 hq1
        _ = q / (1 - q) := by rw [div_eq_mul_inv]
  have hB : ∑ ℓ ∈ img.filter (fun ℓ => ¬ ℓ = 0),
        (W.filter (fun j => dcol m j = ℓ)).card • q ^ ℓ ≤ 2 * (q / (1 - q)) := by
    have hstep : ∑ ℓ ∈ img.filter (fun ℓ => ¬ ℓ = 0),
          (W.filter (fun j => dcol m j = ℓ)).card • q ^ ℓ
        ≤ ∑ ℓ ∈ img.filter (fun ℓ => ¬ ℓ = 0), (2 : ℝ) * q ^ ℓ := by
      refine Finset.sum_le_sum (fun ℓ hℓ => ?_)
      rw [nsmul_eq_mul]
      have hℓ0 : ℓ ≠ 0 := (Finset.mem_filter.1 hℓ).2
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast dcol_fiber_card_le (Nat.one_le_iff_ne_zero.2 hℓ0) W)
        (pow_nonneg hq0 ℓ)
    rw [← Finset.mul_sum] at hstep
    exact hstep.trans (mul_le_mul_of_nonneg_left hgeo (by norm_num))
  exact add_le_add hA hB

/-- **Two-sided geometric window sum (specialized).**  For `sp ≥ 1`, `m ≥ 1`,
`∑_{j∈[-N,N]} 3^{-(sp/2) d_j} ≤ 3(m+1)` (`C₅ = 3`). -/
lemma sum_three_dcol_le {s p : ℝ} (hsp : 1 ≤ s * p)
    (m N : ℕ) (hm : 1 ≤ m) :
    ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (3 : ℝ) ^ (-(s * p / 2 * (dcol m j : ℝ)))
      ≤ 3 * ((m : ℝ) + 1) := by
  set q : ℝ := (3 : ℝ) ^ (-(s * p / 2)) with hq
  have hq0 : 0 ≤ q := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hsp2 : (1 : ℝ) / 2 ≤ s * p / 2 := by linarith
  have hq1 : q < 1 := by
    rw [hq, show (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) by norm_num]
    exact (Real.rpow_lt_rpow_left_iff (by norm_num)).2 (by nlinarith [hsp])
  have hq12 : (3 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 2 / 3 := by
    have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos (by norm_num) _).le
    have hsq : ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / 3 := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num)]; norm_num
    nlinarith [hsq, h1, sq_nonneg ((3 : ℝ) ^ (-(1 / 2 : ℝ)) - 2 / 3)]
  have hq23 : q ≤ 2 / 3 := by
    rw [hq]
    refine le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)) hq12
  have hconv : ∀ j : ℤ, (3 : ℝ) ^ (-(s * p / 2 * (dcol m j : ℝ))) = q ^ (dcol m j) := by
    intro j
    rw [hq, ← Real.rpow_natCast ((3 : ℝ) ^ (-(s * p / 2))) (dcol m j),
      ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  rw [Finset.sum_congr rfl (fun j _ => hconv j)]
  have hraw := sum_dcol_geom_le hq0 hq1 m N
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have hqdiv : q / (1 - q) ≤ 2 := by
    rw [div_le_iff₀ h1q]; nlinarith [hq23]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  nlinarith [hraw, hqdiv, hm1]

/-! ### (b/c) `λ`-substitution algebra and the `ℝ≥0∞` `rpow` bridge -/

/-- The `λ`-substitution `(3/λ)^p = θ/K` for `λ = 3 K^{1/p} θ^{-1/p}`. -/
lemma three_div_lam_rpow {K θ p : ℝ} (hK : 0 < K) (hθ : 0 < θ) (hp : 0 < p) :
    (3 / (3 * K ^ (1 / p) * θ ^ (-1 / p))) ^ p = θ / K := by
  have hKp : (0 : ℝ) < K ^ (1 / p) := Real.rpow_pos_of_pos hK _
  have hθp : (0 : ℝ) < θ ^ (-1 / p) := Real.rpow_pos_of_pos hθ _
  have hlam : (0 : ℝ) < 3 * K ^ (1 / p) * θ ^ (-1 / p) := by positivity
  have h3p : (0 : ℝ) < (3 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  have hlamp : (3 * K ^ (1 / p) * θ ^ (-1 / p)) ^ p = (3 : ℝ) ^ p * K * θ⁻¹ := by
    rw [Real.mul_rpow (by positivity) hθp.le, Real.mul_rpow (by norm_num) hKp.le,
      ← Real.rpow_mul hK.le, ← Real.rpow_mul hθ.le,
      show (1 / p) * p = 1 by field_simp, show (-1 / p) * p = -1 by field_simp,
      Real.rpow_one, Real.rpow_neg_one]
  rw [Real.div_rpow (by norm_num) hlam.le, hlamp]
  field_simp

/-- `e_r = ofReal(exp(a/r)) = B^{1/r}` with `B = ofReal(exp a)` in `ℝ≥0∞`. -/
lemma er_eq_B_rpow (a : ℝ) (r : ℕ) :
    ENNReal.ofReal (Real.exp (a / r)) = (ENNReal.ofReal (Real.exp a)) ^ ((1 : ℝ) / r) := by
  have hbase : Real.exp (a / r) = (Real.exp a) ^ ((1 : ℝ) / r) := by
    rw [← Real.exp_mul]; congr 1; field_simp
  rw [hbase, ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg a) (by positivity)]

/-- The `rpow` bridge `e_r^n = (B^n)^{1/r}` used across the Hölder classes. -/
lemma er_npow (a : ℝ) (r n : ℕ) :
    (ENNReal.ofReal (Real.exp (a / r))) ^ n
      = ((ENNReal.ofReal (Real.exp a)) ^ n) ^ ((1 : ℝ) / r) := by
  rw [er_eq_B_rpow,
    ← ENNReal.rpow_natCast ((ENNReal.ofReal (Real.exp a)) ^ ((1 : ℝ) / r)) n,
    ← ENNReal.rpow_mul,
    ← ENNReal.rpow_natCast (ENNReal.ofReal (Real.exp a)) n, ← ENNReal.rpow_mul]
  congr 1; ring

end Algsuperdiff.Section4.Probability.ScalesConcentration
