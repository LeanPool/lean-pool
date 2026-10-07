/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCGaussianPower

/-!
# Geometric cover and Gaussian decay

Arbitrarily high polynomial decay absorbs the geometric growth of the
spatial covering multiplicity.
-/

public section


noncomputable section

namespace ESS

/-- Each geometric-slab Gaussian term is bounded by a geometric series
times a high power of the original radius. -/
theorem uc_geometric_gaussian_term_le
    (K b r : ℝ) (N n : ℕ) (hK : 0 ≤ K)
    (hb : 0 < b) (hr : 0 < r) (hN : 0 < N) :
    K ^ (n + 1) *
      Real.exp (-(b / ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2))) ≤
      (K * (((N : ℝ) * (3 / 5) / b) ^ N) * r ^ (2 * N)) *
        (K * (3 / 4 : ℝ) ^ N) ^ n := by
  let t : ℝ := (3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hpow := uc_exp_neg_div_le_pow b t N hb ht hN
  calc
    K ^ (n + 1) * Real.exp (-(b / t)) ≤
        K ^ (n + 1) * (((N : ℝ) * t / b) ^ N) :=
      mul_le_mul_of_nonneg_left hpow (pow_nonneg hK _)
    _ = (K * (((N : ℝ) * (3 / 5) / b) ^ N) * r ^ (2 * N)) *
        (K * (3 / 4 : ℝ) ^ N) ^ n := by
      dsimp [t]
      ring_nf

/-- When the polynomial order absorbs the covering multiplicity, the
Gaussian slab bounds form a summable series. -/
theorem uc_geometric_gaussian_series_le
    (K b r : ℝ) (N : ℕ) (hK : 0 ≤ K)
    (hb : 0 < b) (hr : 0 < r) (hN : 0 < N)
    (hq : K * (3 / 4 : ℝ) ^ N < 1) :
    Summable (fun n : ℕ => K ^ (n + 1) *
      Real.exp (-(b / ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)))) ∧
    (∑' n : ℕ, K ^ (n + 1) *
      Real.exp (-(b / ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)))) ≤
      (K * (((N : ℝ) * (3 / 5) / b) ^ N) * r ^ (2 * N)) *
        (1 - K * (3 / 4 : ℝ) ^ N)⁻¹ := by
  let q : ℝ := K * (3 / 4 : ℝ) ^ N
  let C : ℝ := K * (((N : ℝ) * (3 / 5) / b) ^ N) * r ^ (2 * N)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hgeo : Summable (fun n : ℕ => C * q ^ n) :=
    (summable_geometric_of_lt_one hq0 hq).mul_left C
  have hterm0 (n : ℕ) : 0 ≤ K ^ (n + 1) *
      Real.exp (-(b / ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2))) := by
    positivity
  have hterm (n : ℕ) :
      K ^ (n + 1) *
        Real.exp (-(b / ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2))) ≤
          C * q ^ n :=
    uc_geometric_gaussian_term_le K b r N n hK hb hr hN
  have hsum : Summable (fun n : ℕ => K ^ (n + 1) *
      Real.exp (-(b / ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)))) :=
    Summable.of_nonneg_of_le hterm0 hterm hgeo
  refine ⟨hsum, ?_⟩
  calc
    (∑' n : ℕ, K ^ (n + 1) *
      Real.exp (-(b / ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)))) ≤
        ∑' n : ℕ, C * q ^ n := hsum.tsum_le_tsum hterm hgeo
    _ = C * (1 - q)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq]
    _ = _ := rfl

/-- Every desired vanishing order admits a polynomial exponent that also
absorbs the fixed covering multiplicity. -/
theorem uc_geometric_gaussian_order
    (K : ℝ) (hK : 0 < K) (m : ℕ) :
    ∃ N : ℕ, m + 1 ≤ N ∧
      K * (3 / 4 : ℝ) ^ N < 1 := by
  have hden : 0 < K + 1 := by linarith only [hK]
  have heps : 0 < 1 / (K + 1) := by positivity
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one heps
    (by norm_num : (3 / 4 : ℝ) < 1)
  let N := n₀ + (m + 1)
  have horder : m + 1 ≤ N := by dsimp [N]; omega
  have hpow1 : (3 / 4 : ℝ) ^ (m + 1) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hpow0 : 0 ≤ (3 / 4 : ℝ) ^ n₀ := by positivity
  have hpow : (3 / 4 : ℝ) ^ N ≤ (3 / 4 : ℝ) ^ n₀ := by
    dsimp [N]
    rw [pow_add]
    exact mul_le_of_le_one_right hpow0 hpow1
  refine ⟨N, horder, ?_⟩
  calc
    K * (3 / 4 : ℝ) ^ N ≤ K * (3 / 4 : ℝ) ^ n₀ :=
      mul_le_mul_of_nonneg_left hpow hK.le
    _ < K * (1 / (K + 1)) := mul_lt_mul_of_pos_left hn₀ hK
    _ < 1 := by
      rw [mul_one_div]
      exact (div_lt_one hden).mpr (by linarith only [hK])

end ESS
