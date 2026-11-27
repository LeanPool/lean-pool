/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.NormalizedCommutation
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalOperator
public import LeanPool.VacuumBellSeparation.FreeField.PositiveOperatorPowers

/-!
# Bounded power calculus for complementary Gram operators

For the actual complementary pair I+B,I-B, nonnegative powers retain
zero spectral endpoints. Their sum is bounded below by I. Consequently
its inverse is a genuine bounded contraction, including exponent zero
and the zero-dimensional Hilbert space.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem gramPlus_rpow_eq_cfc {B : E →L[ℂ] E} (hB : IsSelfAdjoint B) (hn : ‖B‖ ≤ 1)
    {p : ℝ} (hp : 0 ≤ p) :
    gramPlus B ^ p = cfc (fun x : ℝ => (1 + x) ^ p) B := by
  rw [CFC.rpow_eq_cfc_real (gramPlus_nonneg hB hn)]
  change cfc (fun x : ℝ => x ^ p) (1 + B) = _
  rw [← cfc_one_add_id B hB,
    ← cfc_comp' (fun x : ℝ => x ^ p) (fun x : ℝ => 1 + x) B
      (Real.continuous_rpow_const hp).continuousOn (by fun_prop) hB]

theorem gramMinus_rpow_eq_cfc {B : E →L[ℂ] E} (hB : IsSelfAdjoint B) (hn : ‖B‖ ≤ 1)
    {p : ℝ} (hp : 0 ≤ p) :
    gramMinus B ^ p = cfc (fun x : ℝ => (1 - x) ^ p) B := by
  rw [CFC.rpow_eq_cfc_real (gramMinus_nonneg hB hn)]
  change cfc (fun x : ℝ => x ^ p) (1 - B) = _
  rw [← cfc_one_sub_id B hB,
    ← cfc_comp' (fun x : ℝ => x ^ p) (fun x : ℝ => 1 - x) B
      (Real.continuous_rpow_const hp).continuousOn (by fun_prop) hB]

theorem continuous_gramPlusPower {p : ℝ} (hp : 0 ≤ p) :
    Continuous (fun x : ℝ => (1 + x) ^ p) :=
  (continuous_const.add continuous_id).rpow_const (fun _ => Or.inr hp)

theorem continuous_gramMinusPower {p : ℝ} (hp : 0 ≤ p) :
    Continuous (fun x : ℝ => (1 - x) ^ p) :=
  (continuous_const.sub continuous_id).rpow_const (fun _ => Or.inr hp)

theorem reserve_rpow_eq_gram_powers {B : E →L[ℂ] E}
    (hB : IsSelfAdjoint B) (hn : ‖B‖ ≤ 1) {p : ℝ} (hp : 0 ≤ p) :
    reserve B ^ p = gramPlus B ^ (p / 2) * gramMinus B ^ (p / 2) := by
  have hs : ∀ x ∈ spectrum ℝ B, x ^ 2 ≤ 1 := by
    intro x hx
    have hi := spectrum_mem_Icc_of_norm_le_one hn hx
    nlinarith [hi.1, hi.2]
  have hhalf : 0 ≤ p / 2 := div_nonneg hp (by norm_num)
  have hr : reserve B ^ p = (1 - B ^ 2) ^ (p / 2) := by
    have htwice : (2 : ℝ) * (p / 2) = p := by ring
    simpa only [reserve, reserveSquare, htwice] using
      sqrt_one_sub_sq_rpow (a := B) hhalf (reserveSquare_nonneg hB hn)
  rw [hr, one_sub_sq_rpow_eq_cfc hhalf hB hs,
    gramPlus_rpow_eq_cfc hB hn hhalf, gramMinus_rpow_eq_cfc hB hn hhalf,
    ← cfc_mul _ _ B (continuous_gramPlusPower hhalf).continuousOn
      (continuous_gramMinusPower hhalf).continuousOn]
  apply cfc_congr
  intro x hx
  dsimp only
  have hi := spectrum_mem_Icc_of_norm_le_one hn hx
  rw [show 1 - x ^ 2 = (1 + x) * (1 - x) by ring,
    Real.mul_rpow (by linarith [hi.1]) (by linarith [hi.2])]

/-- Complementary power sum given by `(1 + x) ^ a + (1 - x) ^ a`. -/
noncomputable def complementaryPowerSum (a x : ℝ) : ℝ := (1 + x) ^ a + (1 - x) ^ a

theorem continuous_complementaryPowerSum {a : ℝ} (ha : 0 ≤ a) :
    Continuous (complementaryPowerSum a) :=
  (continuous_gramPlusPower ha).add (continuous_gramMinusPower ha)

theorem complementaryPowerSum_ge_one {a x : ℝ} (ha : 0 ≤ a) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    1 ≤ complementaryPowerSum a x := by
  unfold complementaryPowerSum
  rcases le_total 0 x with h | h
  · have hp := Real.one_le_rpow (show 1 ≤ 1 + x by linarith) ha
    have hm := Real.rpow_nonneg (show 0 ≤ 1 - x by linarith [hx.2]) a
    linarith
  · have hm := Real.one_le_rpow (show 1 ≤ 1 - x by linarith) ha
    have hp := Real.rpow_nonneg (show 0 ≤ 1 + x by linarith [hx.1]) a
    linarith

/-- Complementary gram power sum given by `gramPlus B ^ a + gramMinus B ^ a`. -/
noncomputable def complementaryGramPowerSum (a : ℝ) (B : E →L[ℂ] E) : E →L[ℂ] E :=
  gramPlus B ^ a + gramMinus B ^ a

theorem complementaryGramPowerSum_eq_cfc {B : E →L[ℂ] E}
    (hB : IsSelfAdjoint B) (hn : ‖B‖ ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    complementaryGramPowerSum a B = cfc (complementaryPowerSum a) B := by
  rw [complementaryGramPowerSum, gramPlus_rpow_eq_cfc hB hn ha,
    gramMinus_rpow_eq_cfc hB hn ha,
    ← cfc_add B _ _ (continuous_gramPlusPower ha).continuousOn
      (continuous_gramMinusPower ha).continuousOn]
  rfl

theorem one_le_complementaryGramPowerSum {B : E →L[ℂ] E}
    (hB : IsSelfAdjoint B) (hn : ‖B‖ ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    1 ≤ complementaryGramPowerSum a B := by
  rw [complementaryGramPowerSum_eq_cfc hB hn ha]
  simpa only [map_one] using algebraMap_le_cfc (complementaryPowerSum a) 1 B
    (fun x hx => complementaryPowerSum_ge_one ha (spectrum_mem_Icc_of_norm_le_one hn hx))
    (continuous_complementaryPowerSum ha).continuousOn hB

theorem complementaryGramPowerSum_isStrictlyPositive {B : E →L[ℂ] E}
    (hB : IsSelfAdjoint B) (hn : ‖B‖ ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    IsStrictlyPositive (complementaryGramPowerSum a B) :=
  isStrictlyPositive_one.of_le (one_le_complementaryGramPowerSum hB hn ha)

theorem complementaryGramPowerSum_inverse_eq_cfc {B : E →L[ℂ] E}
    (hB : IsSelfAdjoint B) (hn : ‖B‖ ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    Ring.inverse (complementaryGramPowerSum a B) =
      cfc (fun x => (complementaryPowerSum a x)⁻¹) B := by
  rw [complementaryGramPowerSum_eq_cfc hB hn ha]
  exact (cfc_inv _ B
    (fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one
      (complementaryPowerSum_ge_one ha (spectrum_mem_Icc_of_norm_le_one hn hx))))
    (continuous_complementaryPowerSum ha).continuousOn hB).symm

theorem norm_complementaryGramPowerSum_inverse_le_one {B : E →L[ℂ] E}
    (hB : IsSelfAdjoint B) (hn : ‖B‖ ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    ‖Ring.inverse (complementaryGramPowerSum a B)‖ ≤ 1 := by
  rw [complementaryGramPowerSum_inverse_eq_cfc hB hn ha]
  apply norm_cfc_le (by norm_num)
  intro x hx
  have hs := complementaryPowerSum_ge_one ha (spectrum_mem_Icc_of_norm_le_one hn hx)
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by linarith))]
  exact inv_le_one_of_one_le₀ hs

end VacuumBellSeparation.Gaussian
