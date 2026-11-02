/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleyMomentRecovery

/-! # Constants uniform in the Hooley moment order

After division by the exponent gap, the integrated coefficient grows at most
linearly in `q`. This is the dependence needed for the sharp optimization.
-/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial

theorem rpow_le_max_one_self {x u : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u) (hu₁ : u ≤ 1) :
    x ^ u ≤ max 1 x :=
  (Real.rpow_le_rpow hx (le_max_right _ _) hu).trans
    (Real.rpow_le_self_of_one_le (le_max_left _ _) hu₁)

/-- A pole-bound constant uniform in the permitted moment orders. -/
noncomputable def hooleyPoleUniformConstant (Q : ℤ[X]) (t C : ℝ) : ℝ :=
  max 1 ((Q.natDegree : ℝ) * (Real.log 4 * Real.exp 2)) * (4 : ℝ) ^ t *
    max 1 (2 * (Q.natDegree : ℝ) * (Real.log 4 * Real.exp 2)) * Real.exp ((2 : ℝ) ^ t * C)

theorem hooleyPoleUniformConstant_nonneg (Q : ℤ[X]) (t C : ℝ) :
    0 ≤ hooleyPoleUniformConstant Q t C := by
  unfold hooleyPoleUniformConstant
  positivity

theorem hooleyPrimeErrorConstant_rpow_le (Q : ℤ[X]) {t : ℝ} (ht : 0 ≤ t)
    {q : ℕ} (hq : 0 < q) (htq : t ≤ q) :
    hooleyPrimeErrorConstant Q q ^ (t / q) ≤
      max 1 ((Q.natDegree : ℝ) * (Real.log 4 * Real.exp 2)) * (4 : ℝ) ^ t := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hθ := div_nonneg ht hq'.le
  have hθ₁ := (div_le_one hq').mpr htq
  have H := rpow_le_max_one_self
    (by positivity : 0 ≤ (Q.natDegree : ℝ) * (Real.log 4 * Real.exp 2)) hθ hθ₁
  unfold hooleyPrimeErrorConstant
  rw [← mul_assoc, Real.mul_rpow (by positivity) (by positivity)]
  have hpow : ((4 : ℝ) ^ q) ^ (t / q) = (4 : ℝ) ^ t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    field_simp
  rw [hpow]
  exact mul_le_mul_of_nonneg_right H (Real.rpow_nonneg (by norm_num) _)

theorem hooleyPoleCoefficient_le_uniform (Q : ℤ[X]) {t C : ℝ} (ht : 0 ≤ t) (hC : 0 ≤ C)
    {q : ℕ} (hq : 2 < q) (htq : t ≤ q) :
    hooleyPoleCoefficient Q t q C ≤ hooleyPoleUniformConstant Q t C / ((q : ℝ) - 1) := by
  have hq' : (2 : ℝ) < q := by exact_mod_cast hq
  have hd : 0 < (q : ℝ) - 1 := by linarith
  have hθ₀ : 0 ≤ t / (q : ℝ) := div_nonneg ht (by linarith)
  have hθ₁ : t / (q : ℝ) ≤ 1 := (div_le_one (by linarith : (0 : ℝ) < q)).mpr htq
  have HP := rpow_le_max_one_self
    (by positivity : 0 ≤ 2 * (Q.natDegree : ℝ) * (Real.log 4 * Real.exp 2))
    (by linarith : 0 ≤ 1 - t / q) (by linarith : 1 - t / q ≤ 1)
  have hκ : ((2 : ℝ) ^ t - (2 : ℝ) ^ (t / q)) / ((q : ℝ) - 1) ≤ (2 : ℝ) ^ t := by
    calc
      _ ≤ (2 : ℝ) ^ t / ((q : ℝ) - 1) := div_le_div_of_nonneg_right
        (sub_le_self _ (Real.rpow_nonneg (by norm_num) _)) hd.le
      _ ≤ _ := div_le_self (Real.rpow_nonneg (by norm_num) _) (by linarith)
  have HE := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hκ hC)
  have HC := div_le_div_of_nonneg_right (hooleyPrimeErrorConstant_rpow_le Q ht (by omega) htq) hd.le
  unfold hooleyPoleCoefficient hooleyPoleUniformConstant
  apply (mul_le_mul (mul_le_mul HC HP (Real.rpow_nonneg (by positivity) _)
    (by positivity)) HE (Real.exp_nonneg _) (by positivity)).trans_eq
  ring

theorem hooleyPoleCoefficient_div_gap_le (Q : ℤ[X]) {t C : ℝ} (ht : 1 ≤ t) (hC : 0 ≤ C)
    {q : ℕ} (hq : 2 < q) (hqt : 2 * t ≤ q) :
    hooleyPoleCoefficient Q t q C / hooleyMomentExponentGap t q ≤
      (7 * hooleyPoleUniformConstant Q t C) * q := by
  have ht₀ : 0 < t := by linarith
  have hq' : (2 : ℝ) < q := by exact_mod_cast hq
  have hq₀ : 0 < (q : ℝ) := by linarith
  have hd : 0 < (q : ℝ) - 1 := by linarith
  have hE := hooleyPoleUniformConstant_nonneg Q t C
  have hgap := hooleyMomentExponentGap_pos ht hq hqt
  calc
    _ ≤ (hooleyPoleUniformConstant Q t C / ((q : ℝ) - 1)) / hooleyMomentExponentGap t q :=
      div_le_div_of_nonneg_right (hooleyPoleCoefficient_le_uniform Q ht₀.le hC hq (by
        linarith)) hgap.le
    _ ≤ (hooleyPoleUniformConstant Q t C / ((q : ℝ) - 1)) /
        (t / (7 * (q : ℝ) * ((q : ℝ) - 1))) :=
      div_le_div_of_nonneg_left (div_nonneg hE hd.le) (by positivity)
        (hooleyMomentExponentGap_lower ht hq hqt)
    _ = (7 * hooleyPoleUniformConstant Q t C) * q / t := by field_simp
    _ ≤ _ := div_le_self (by positivity) ht

theorem hooleyReducedMoment_le_endpoint_uniform {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t b : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 2 < q) (hb : 1 < b) :
    hooleyReducedMoment Q t q b ≤ Real.exp ((2 : ℝ) ^ t * rootPrimePowerSum Q b) := by
  have hq' : (2 : ℝ) < q := by exact_mod_cast hq
  have hd : 0 ≤ 1 / ((q : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
  have hd₁ : 1 / ((q : ℝ) - 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have Hexp : Real.exp (-(2 : ℝ) ^ (t / q) * (1 / ((q : ℝ) - 1)) * rootPrimePowerSum Q b) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.rpow_nonneg (by norm_num) _)) hd)
      (rootPrimePowerSum_nonneg Q b)
  unfold hooleyReducedMoment
  calc
    _ ≤ 1 * hooleyDirichlet Q t q b ^ (1 / ((q : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_right Hexp (Real.rpow_nonneg (hooleyDirichlet_nonneg Q t q b) _)
    _ ≤ hooleyDirichlet Q t q b := by
      rw [one_mul]
      exact Real.rpow_le_self_of_one_le (one_le_hooleyDirichlet hQ ht (by omega) hb) hd₁
    _ ≤ _ := hooleyDirichlet_le_exp_prime_sum hQ ht (by omega) hb

end NairTenenbaum
