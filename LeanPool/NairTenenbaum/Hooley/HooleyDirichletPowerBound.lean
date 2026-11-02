/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleyMomentOrderConstants

/-! # A Dirichlet moment bound uniform in the moment order

For fixed `Q,t`, the bound has the form
`L_q(σ) ≤ (Kq)^q (σ−1)^(−(2^t−t+t/q))`.
The same constants work for every eligible integer moment order.
-/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial

theorem exists_irreducible_hooley_reduced_uniform_bound {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) {t : ℝ} (ht : 1 ≤ t) :
    ∃ K C b : ℝ, 1 ≤ K ∧ 0 ≤ C ∧ 1 < b ∧ b ≤ 2 ∧
      (∀ σ : ℝ, 1 < σ → σ ≤ b → rootPrimePowerSum Q σ ≤ C - Real.log (σ - 1)) ∧
      ∀ q : ℕ, 2 < q → 2 * t ≤ q → ∀ σ : ℝ, 1 < σ → σ ≤ b →
        hooleyReducedMoment Q t q σ ≤ (K * q) * (σ - 1) ^ (-hooleyMomentExponentGap t q) := by
  obtain ⟨C, b₀, hC, hb₀, hR₀⟩ := exists_irreducible_rootPrimePowerSum_log_bound hirr
  let b := min 2 ((b₀ + 1) / 2)
  have hb : 1 < b := lt_min (by norm_num) (by linarith)
  have hb₂ : b ≤ 2 := min_le_left _ _
  have hR (σ : ℝ) (hσ : 1 < σ) (hσb : σ ≤ b) :
      rootPrimePowerSum Q σ ≤ C - Real.log (σ - 1) :=
    (hR₀ σ hσ (lt_of_le_of_lt (hσb.trans (min_le_right _ _)) (by linarith))).2
  let E := Real.exp ((2 : ℝ) ^ t * rootPrimePowerSum Q b)
  let D := 7 * hooleyPoleUniformConstant Q t C
  have hE : 0 ≤ E := Real.exp_nonneg _
  have hD : 0 ≤ D := mul_nonneg (by norm_num) (hooleyPoleUniformConstant_nonneg Q t C)
  refine ⟨1 + E + D, C, b, by linarith, hC, hb, hb₂, hR, fun q hq hqt σ hσ hσb => ?_⟩
  have ht₀ : 0 ≤ t := by linarith
  have hq' : (2 : ℝ) < q := by exact_mod_cast hq
  have hgap := hooleyMomentExponentGap_pos ht hq hqt
  have H := hooleyReducedMoment_le_endpoint_add_power hQ ht₀ hq (by linarith) hσ hσb hgap
    (fun s hs => hooleyReducedMomentMajorant_le_power hQ ht₀ hq (by linarith)
      (hσ.trans_le hs.1) (hs.2.trans hb₂) (hR s (hσ.trans_le hs.1) hs.2))
  have HE := hooleyReducedMoment_le_endpoint_uniform hQ ht₀ hq hb
  have HD := hooleyPoleCoefficient_div_gap_le Q ht hC hq hqt
  let w := (σ - 1) ^ (-hooleyMomentExponentGap t q)
  have hw : 1 ≤ w := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    (by linarith) (by linarith [hσb.trans hb₂]) (by linarith)
  have hqw : 1 ≤ (q : ℝ) * w := one_le_mul_of_one_le_of_one_le (by linarith) hw
  calc
    _ ≤ E + (D * q) * w := H.trans (add_le_add HE
      (mul_le_mul_of_nonneg_right HD (zero_le_one.trans hw)))
    _ ≤ E * ((q : ℝ) * w) + D * ((q : ℝ) * w) := by
      have HE' := mul_le_mul_of_nonneg_left hqw hE
      nlinarith
    _ = (E + D) * (q : ℝ) * w := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : E + D ≤ 1 + E + D) (Nat.cast_nonneg _))
      (zero_le_one.trans hw)

theorem exp_mul_momentPower_le {K C t : ℝ} (hK : 1 ≤ K) (hC : 0 ≤ C)
    {q : ℕ} (hq : 1 ≤ q) (htq : t ≤ q) :
    Real.exp ((2 : ℝ) ^ (t / q) * C) * (K * q) ^ ((q : ℝ) - 1) ≤
      (Real.exp (2 * C) * K * q) ^ q := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq₀ : (0 : ℝ) < q := by linarith
  have hKq : 1 ≤ K * q := one_le_mul_of_one_le_of_one_le hK hq'
  have hA : (2 : ℝ) ^ (t / q) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) ((div_le_one hq₀).mpr htq)
  have HE := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hA hC)
  have HE₁ : 1 ≤ Real.exp (2 * C) := Real.one_le_exp_iff.mpr (by linarith)
  have HEq : Real.exp (2 * C) ≤ Real.exp (2 * C) ^ (q : ℝ) :=
    Real.self_le_rpow_of_one_le HE₁ hq'
  have HK := Real.rpow_le_rpow_of_exponent_le hKq (by linarith : (q : ℝ) - 1 ≤ q)
  calc
    _ ≤ Real.exp (2 * C) ^ (q : ℝ) * (K * q) ^ (q : ℝ) :=
      mul_le_mul (HE.trans HEq) HK (Real.rpow_nonneg (by
        positivity) _) (Real.rpow_nonneg (Real.exp_nonneg _) _)
    _ = _ := by rw [Real.rpow_natCast, Real.rpow_natCast, ← mul_pow]; congr 1; ring

theorem exists_irreducible_hooleyDirichlet_power_bound {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) {t : ℝ} (ht : 1 ≤ t) :
    ∃ K b : ℝ, 1 ≤ K ∧ 1 < b ∧ b ≤ 2 ∧ ∀ q : ℕ, 2 < q → 2 * t ≤ q →
      ∀ σ : ℝ, 1 < σ → σ ≤ b →
        hooleyDirichlet Q t q σ ≤ (K * q) ^ q * (σ - 1) ^ (-((2 : ℝ) ^ t - t + t / q)) := by
  obtain ⟨K, C, b, hK, hC, hb, hb₂, hR, hU⟩ :=
    exists_irreducible_hooley_reduced_uniform_bound hQ hirr ht
  have HE : 1 ≤ Real.exp (2 * C) := Real.one_le_exp_iff.mpr (by linarith)
  refine ⟨Real.exp (2 * C) * K, b, one_le_mul_of_one_le_of_one_le HE hK, hb, hb₂, fun q hq hqt σ
      hσ hσb => ?_⟩
  have H := hooleyDirichlet_le_of_reducedMoment_bound Q (by omega : 1 < q) hσ
    (show 0 ≤ K * (q : ℝ) by positivity) (hR σ hσ hσb) (hU q hq hqt σ hσ hσb)
  apply H.trans
  exact mul_le_mul_of_nonneg_right (exp_mul_momentPower_le hK hC (by omega) (by linarith))
    (Real.rpow_nonneg (by linarith) _)

end NairTenenbaum
