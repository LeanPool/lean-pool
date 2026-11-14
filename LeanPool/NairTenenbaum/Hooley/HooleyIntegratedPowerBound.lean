/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Hooley.HooleyPowerMajorant

/-! # Integrating the explicit moment power bound

The singular power is integrated with its full dependence on the exponent
gap. For `t≥1` and `q≥2t`, positivity of the gap is already proved.
-/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial MeasureTheory

theorem intervalIntegrable_sub_one_rpow {a b r : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun s : ℝ => (s - 1) ^ r) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (continuous_id.sub continuous_const).continuousOn.rpow_const
  intro s hs
  rw [Set.uIcc_of_le hab] at hs
  exact Or.inl (by change s - 1 ≠ 0; linarith [hs.1])

theorem integral_sub_one_rpow_le {a b e : ℝ} (ha : 1 < a) (hab : a ≤ b) (he : 0 < e) :
    (∫ s in a..b, (s - 1) ^ (-1 - e)) ≤ (a - 1) ^ (-e) / e := by
  rw [intervalIntegral.integral_comp_sub_right (fun s : ℝ => s ^ (-1 - e)) 1,
    integral_rpow (Or.inr ⟨by linarith, by
      rw [Set.uIcc_of_le (sub_le_sub_right hab 1)]
      intro h
      linarith [h.1]⟩), show -1 - e + 1 = -e by ring]
  rw [show ((b - 1) ^ (-e) - (a - 1) ^ (-e)) / -e =
      ((a - 1) ^ (-e) - (b - 1) ^ (-e)) / e by ring]
  apply div_le_div_of_nonneg_right _ he.le
  exact sub_le_self _ (Real.rpow_nonneg (by linarith : 0 ≤ b - 1) _)

theorem hooleyReducedMoment_le_endpoint_add_power {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t a b C : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 2 < q) (htq : t ≤ q)
    (ha : 1 < a) (hab : a ≤ b) (hgap : 0 < hooleyMomentExponentGap t q)
    (hbound : ∀ s ∈ Set.Icc a b, hooleyReducedMomentMajorant Q t q s ≤
      hooleyPoleCoefficient Q t q C * (s - 1) ^ (-1 - hooleyMomentExponentGap t q)) :
    hooleyReducedMoment Q t q a ≤ hooleyReducedMoment Q t q b +
      (hooleyPoleCoefficient Q t q C / hooleyMomentExponentGap t q) *
        (a - 1) ^ (-hooleyMomentExponentGap t q) := by
  have HI := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_hooleyReducedMomentMajorant hQ (by omega) htq ha hab)
    ((intervalIntegrable_sub_one_rpow ha hab).const_mul (hooleyPoleCoefficient Q t q C)) hbound
  rw [intervalIntegral.integral_const_mul] at HI
  have H := mul_le_mul_of_nonneg_left (integral_sub_one_rpow_le ha hab hgap)
    (hooleyPoleCoefficient_nonneg Q t C hq)
  have H' := hooleyReducedMoment_le_endpoint_add_integral hQ ht hq htq ha hab
  have Heq : hooleyPoleCoefficient Q t q C * ((a - 1) ^ (-hooleyMomentExponentGap t q) /
      hooleyMomentExponentGap t q) =
      (hooleyPoleCoefficient Q t q C / hooleyMomentExponentGap t q) *
        (a - 1) ^ (-hooleyMomentExponentGap t q) := by ring
  rw [Heq] at H
  linarith

end NairTenenbaum
