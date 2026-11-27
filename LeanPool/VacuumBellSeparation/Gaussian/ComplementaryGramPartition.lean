/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ComplementaryGramPowers

/-!
# A bounded partition for the two complementary source weights

The partition uses only nonnegative continuous powers and the inverse of
G^a+H^a ≥ I. It therefore includes b=1/2 and singular Gram operators.
No inverse of the reserve is introduced.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Complementary gram part left given by `gramMinus B ^ (b - 1 / 2) * Ring.inverse
(complementaryGramPowerSum (b - 1 / 2) B)`. -/
noncomputable def complementaryGramPartLeft (b : ℝ) (B : E →L[ℂ] E) : E →L[ℂ] E :=
  gramMinus B ^ (b - 1 / 2) * Ring.inverse (complementaryGramPowerSum (b - 1 / 2) B)

/-- Complementary gram part right given by `gramPlus B ^ (b - 1 / 2) * Ring.inverse
(complementaryGramPowerSum (b - 1 / 2) B)`. -/
noncomputable def complementaryGramPartRight (b : ℝ) (B : E →L[ℂ] E) : E →L[ℂ] E :=
  gramPlus B ^ (b - 1 / 2) * Ring.inverse (complementaryGramPowerSum (b - 1 / 2) B)

theorem complementaryGramPart_add {B : E →L[ℂ] E}
    (hB : IsSelfAdjoint B) (hn : ‖B‖ ≤ 1) {b : ℝ} (hb : 1 / 2 ≤ b) :
    complementaryGramPartLeft b B + complementaryGramPartRight b B = 1 := by
  rw [complementaryGramPartLeft, complementaryGramPartRight, ← add_mul, add_comm]
  exact Ring.mul_inverse_cancel _
    (complementaryGramPowerSum_isStrictlyPositive hB hn (sub_nonneg.mpr hb)).isUnit

theorem gram_powers_commute {B : E →L[ℂ] E}
    (hB : IsSelfAdjoint B) (hn : ‖B‖ ≤ 1) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    Commute (gramPlus B ^ p) (gramMinus B ^ q) := by
  rw [gramPlus_rpow_eq_cfc hB hn hp, gramMinus_rpow_eq_cfc hB hn hq]
  exact cfc_commute_cfc _ _ B

theorem complementaryGramPartLeft_weight {B : E →L[ℂ] E}
    (hB : IsSelfAdjoint B) (hn : ‖B‖ ≤ 1) {b : ℝ}
    (hb : 1 / 2 ≤ b) (hb1 : b ≤ 1) :
    (gramPlus B ^ (b / 2) * gramMinus B ^ ((1 - b) / 2)) *
        complementaryGramPartLeft b B =
      reserve B ^ b * Ring.inverse (complementaryGramPowerSum (b - 1 / 2) B) := by
  have ha : 0 ≤ b - 1 / 2 := sub_nonneg.mpr hb
  have hc : 0 ≤ (1 - b) / 2 := by linarith
  have hsum : (1 - b) / 2 + (b - 1 / 2) = b / 2 := by ring
  rw [complementaryGramPartLeft, ← mul_assoc, mul_assoc (gramPlus B ^ (b / 2)),
    ← positiveOperator_rpow_add (gramMinus B) hc ha, hsum,
    ← reserve_rpow_eq_gram_powers hB hn (by linarith : 0 ≤ b)]

theorem complementaryGramPartRight_weight {B : E →L[ℂ] E}
    (hB : IsSelfAdjoint B) (hn : ‖B‖ ≤ 1) {b : ℝ}
    (hb : 1 / 2 ≤ b) (hb1 : b ≤ 1) :
    (gramPlus B ^ ((1 - b) / 2) * gramMinus B ^ (b / 2)) *
        complementaryGramPartRight b B =
      reserve B ^ b * Ring.inverse (complementaryGramPowerSum (b - 1 / 2) B) := by
  have ha : 0 ≤ b - 1 / 2 := sub_nonneg.mpr hb
  have hc : 0 ≤ (1 - b) / 2 := by linarith
  have hd : 0 ≤ b / 2 := by linarith
  have hsum : (1 - b) / 2 + (b - 1 / 2) = b / 2 := by ring
  rw [complementaryGramPartRight, ← mul_assoc, mul_assoc (gramPlus B ^ ((1 - b) / 2)),
    (gram_powers_commute hB hn ha hd).eq.symm, ← mul_assoc,
    ← positiveOperator_rpow_add (gramPlus B) hc ha, hsum,
    ← reserve_rpow_eq_gram_powers hB hn (by linarith : 0 ≤ b)]

theorem reserve_rpow_commute_complementaryGramPowerSum_inverse {B : E →L[ℂ] E}
    (hB : IsSelfAdjoint B) (hn : ‖B‖ ≤ 1) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Commute (reserve B ^ b) (Ring.inverse (complementaryGramPowerSum a B)) := by
  have hh : 0 ≤ b / 2 := div_nonneg hb (by norm_num)
  rw [reserve_rpow_eq_gram_powers hB hn hb, gramPlus_rpow_eq_cfc hB hn hh,
    gramMinus_rpow_eq_cfc hB hn hh, complementaryGramPowerSum_inverse_eq_cfc hB hn ha]
  exact (cfc_commute_cfc _ _ B).mul_left (cfc_commute_cfc _ _ B)

theorem complementaryGramPart_weight_norm_le {B : E →L[ℂ] E}
    (hB : IsSelfAdjoint B) (hn : ‖B‖ ≤ 1) {b : ℝ}
    (hb : 1 / 2 ≤ b) (hb1 : b ≤ 1) (x : E) :
    ‖(gramPlus B ^ (b / 2) * gramMinus B ^ ((1 - b) / 2))
        (complementaryGramPartLeft b B x)‖ ≤ ‖(reserve B ^ b) x‖ ∧
    ‖(gramPlus B ^ ((1 - b) / 2) * gramMinus B ^ (b / 2))
        (complementaryGramPartRight b B x)‖ ≤ ‖(reserve B ^ b) x‖ := by
  have hcommon : ‖(reserve B ^ b *
      Ring.inverse (complementaryGramPowerSum (b - 1 / 2) B)) x‖ ≤
        ‖(reserve B ^ b) x‖ := by
    rw [(reserve_rpow_commute_complementaryGramPowerSum_inverse hB hn
      (sub_nonneg.mpr hb) (by linarith : 0 ≤ b)).eq, mul_apply_eq_comp]
    exact (le_opNorm _ _).trans ((mul_le_mul_of_nonneg_right
      (norm_complementaryGramPowerSum_inverse_le_one hB hn (sub_nonneg.mpr hb))
      (norm_nonneg _)).trans_eq (one_mul _))
  constructor
  · simpa only [← mul_apply_eq_comp, complementaryGramPartLeft_weight hB hn hb hb1] using hcommon
  · simpa only [← mul_apply_eq_comp, complementaryGramPartRight_weight hB hn hb hb1] using hcommon

/-- Two genuine weighted bounds imply the reserve bound. The map need not
already be continuous, and the reserve need not have a bounded inverse. -/
theorem bound_reserve_of_complementary_weights
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {B : E →L[ℂ] E} (hB : IsSelfAdjoint B) (hn : ‖B‖ ≤ 1)
    (T : E →ₗ[ℂ] F) {b C₁ C₂ : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b ≤ 1)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h₁ : ∀ x, ‖T x‖ ≤ C₁ * ‖(gramPlus B ^ (b / 2) * gramMinus B ^ ((1 - b) / 2)) x‖)
    (h₂ : ∀ x, ‖T x‖ ≤ C₂ * ‖(gramPlus B ^ ((1 - b) / 2) * gramMinus B ^ (b / 2)) x‖) :
    ∀ x, ‖T x‖ ≤ (C₁ + C₂) * ‖(reserve B ^ b) x‖ := by
  intro x
  have hsplit : x = complementaryGramPartLeft b B x + complementaryGramPartRight b B x := by
    simpa only [add_apply, _root_.one_apply_eq_self] using
      (congrArg (fun A : E →L[ℂ] E => A x) (complementaryGramPart_add hB hn hb)).symm
  have hw := complementaryGramPart_weight_norm_le hB hn hb hb1 x
  calc
    ‖T x‖ = ‖T (complementaryGramPartLeft b B x) + T (complementaryGramPartRight b B x)‖ := by
      conv_lhs => rw [hsplit, map_add]
    _ ≤ ‖T (complementaryGramPartLeft b B x)‖ + ‖T
      (complementaryGramPartRight b B x)‖ := norm_add_le _ _
    _ ≤ C₁ * ‖(reserve B ^ b) x‖ + C₂ * ‖(reserve B ^ b) x‖ :=
      add_le_add ((h₁ _).trans (mul_le_mul_of_nonneg_left hw.1 hC₁))
        ((h₂ _).trans (mul_le_mul_of_nonneg_left hw.2 hC₂))
    _ = _ := (add_mul _ _ _).symm

end VacuumBellSeparation.Gaussian
