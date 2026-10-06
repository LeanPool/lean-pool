/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop42Scalar.CorrectedTiltTransfer
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# High-contrast homogenization: Provider.Quenched.Prop42Scalar.DecayDelay

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Absorbing a decay prefactor into a polynomially bounded delay

This file turns a geometric tail with a nonnegative prefactor into a unit-
prefactor tail after an explicit integer delay.  It also shows that this delay
has a power bound whenever the prefactor and the pre-existing entry generation
have power bounds in the same base.
-/

namespace HCPolySupport.HighContrast.Quenched.Prop42Scalar

noncomputable section

/-- The extra integer delay needed to absorb a nonnegative prefactor into a
decay of rate `α`. -/
@[expose]
def prefactorDelay (A α : ℝ) : ℕ :=
  ⌈Real.logb 3 (max 1 A) / α⌉₊

/-- The defining delay makes the prefactor no larger than the recovered
positive exponential factor. -/
theorem prefactor_le_three_rpow_alpha_mul_prefactorDelay
    {A α : ℝ} (hα : 0 < α) :
    A ≤ Real.rpow (3 : ℝ) (α * (prefactorDelay A α : ℝ)) := by
  let M : ℝ := max 1 A
  have hM_one : 1 ≤ M := le_max_left _ _
  have hM_pos : 0 < M := zero_lt_one.trans_le hM_one
  have hlog_nonneg : 0 ≤ Real.logb 3 M :=
    Real.logb_nonneg (by norm_num) hM_one
  have hx_nonneg : 0 ≤ Real.logb 3 M / α := div_nonneg hlog_nonneg hα.le
  have hceil : Real.logb 3 M / α ≤ (prefactorDelay A α : ℝ) := by
    dsimp [prefactorDelay, M]
    exact Nat.le_ceil _
  have hexponent : Real.logb 3 M ≤ α * (prefactorDelay A α : ℝ) := by
    calc
      Real.logb 3 M = α * (Real.logb 3 M / α) := by
        field_simp [hα.ne']
      _ ≤ α * (prefactorDelay A α : ℝ) :=
        mul_le_mul_of_nonneg_left hceil hα.le
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexponent
  rw [Real.rpow_logb (by norm_num) (by norm_num) hM_pos] at hpow
  exact (le_max_right 1 A).trans hpow

/-- After adding `prefactorDelay`, the geometric tail has unit prefactor. -/
theorem prefactor_mul_decay_add_prefactorDelay_le
    {A α : ℝ} (hα : 0 < α) (j : ℕ) :
    A * Real.rpow (3 : ℝ)
        (-α * ((prefactorDelay A α + j : ℕ) : ℝ)) ≤
      Real.rpow (3 : ℝ) (-α * (j : ℝ)) := by
  let D := prefactorDelay A α
  have hrecover :=
    prefactor_le_three_rpow_alpha_mul_prefactorDelay (A := A) hα
  have hdecay_nonneg :
      0 ≤ Real.rpow (3 : ℝ) (-α * (((D + j : ℕ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  calc
    A * Real.rpow (3 : ℝ) (-α * (((D + j : ℕ) : ℝ)))
        ≤ Real.rpow (3 : ℝ) (α * (D : ℝ)) *
            Real.rpow (3 : ℝ) (-α * (((D + j : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_right hrecover hdecay_nonneg
    _ = Real.rpow (3 : ℝ)
          (α * (D : ℝ) + -α * (((D + j : ℕ) : ℝ))) := by
      exact (Real.rpow_add (by norm_num) _ _).symm
    _ = Real.rpow (3 : ℝ) (-α * (j : ℝ)) := by
      norm_num only [Nat.cast_add]
      congr 1
      ring

/-- The full delay combines a pre-existing entry generation with the extra
prefactor-absorption delay. -/
@[expose]
def totalDecayDelay (n₀ : ℕ) (A α : ℝ) : ℕ :=
  2 * n₀ + prefactorDelay A α

/-- A post-entry geometric bound becomes a unit-prefactor bound after the full
delay. -/
theorem unit_prefactor_decay_after_totalDecayDelay
    {F : ℕ → ℝ} {A α : ℝ} (hα : 0 < α) {n₀ : ℕ}
    (hF : ∀ n : ℕ, 2 * n₀ ≤ n →
      F n ≤ A * Real.rpow (3 : ℝ)
        (-α * ((n - 2 * n₀ : ℕ) : ℝ))) (j : ℕ) :
    F (totalDecayDelay n₀ A α + j) ≤
      Real.rpow (3 : ℝ) (-α * (j : ℝ)) := by
  have hentry : 2 * n₀ ≤ totalDecayDelay n₀ A α + j := by
    dsimp [totalDecayDelay]
    omega
  have hsub :
      totalDecayDelay n₀ A α + j - 2 * n₀ = prefactorDelay A α + j := by
    dsimp [totalDecayDelay]
    omega
  calc
    F (totalDecayDelay n₀ A α + j)
        ≤ A * Real.rpow (3 : ℝ)
            (-α * (((totalDecayDelay n₀ A α + j - 2 * n₀ : ℕ) : ℝ))) :=
      hF _ hentry
    _ = A * Real.rpow (3 : ℝ)
          (-α * (((prefactorDelay A α + j : ℕ) : ℝ))) := by rw [hsub]
    _ ≤ Real.rpow (3 : ℝ) (-α * (j : ℝ)) :=
      prefactor_mul_decay_add_prefactorDelay_le hα j

/-- If the prefactor is bounded by a power of a base at least three, then its
absorption delay is bounded by a fixed multiple of the base-three logarithm. -/
theorem prefactorDelay_cast_le_logb
    {A α base C : ℝ} (hα : 0 < α) (hbase : 3 ≤ base)
    (hC : 0 ≤ C) (hA : A ≤ Real.rpow base C) :
    (prefactorDelay A α : ℝ) ≤
      (1 + C / α) * Real.logb 3 base := by
  have hbase_one : 1 ≤ base := by linarith only [hbase]
  have hbase_pos : 0 < base := zero_lt_one.trans_le hbase_one
  have hpow_one : 1 ≤ Real.rpow base C := Real.one_le_rpow hbase_one hC
  have hmax : max 1 A ≤ Real.rpow base C := max_le hpow_one hA
  have hM_pos : 0 < max 1 A := zero_lt_one.trans_le (le_max_left _ _)
  have hlog_nonneg : 0 ≤ Real.logb 3 (max 1 A) :=
    Real.logb_nonneg (by norm_num) (le_max_left _ _)
  have hx_nonneg : 0 ≤ Real.logb 3 (max 1 A) / α :=
    div_nonneg hlog_nonneg hα.le
  have hceil :
      (prefactorDelay A α : ℝ) < Real.logb 3 (max 1 A) / α + 1 := by
    dsimp [prefactorDelay]
    exact Nat.ceil_lt_add_one hx_nonneg
  have hlog_le :
      Real.logb 3 (max 1 A) ≤ C * Real.logb 3 base := by
    calc
      Real.logb 3 (max 1 A) ≤ Real.logb 3 (Real.rpow base C) :=
        Real.logb_le_logb_of_le (by norm_num) hM_pos hmax
      _ = C * Real.logb 3 base :=
        Real.logb_rpow_eq_mul_logb_of_pos hbase_pos
  have hlog_base_one : 1 ≤ Real.logb 3 base := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hbase_pos, Real.rpow_one]
    exact hbase
  have hdiv_le :
      Real.logb 3 (max 1 A) / α ≤ C / α * Real.logb 3 base := by
    have hscaled := div_le_div_of_nonneg_right hlog_le hα.le
    calc
      Real.logb 3 (max 1 A) / α
          ≤ (C * Real.logb 3 base) / α := hscaled
      _ = C / α * Real.logb 3 base := by ring
  calc
    (prefactorDelay A α : ℝ)
        ≤ Real.logb 3 (max 1 A) / α + 1 := hceil.le
    _ ≤ C / α * Real.logb 3 base + Real.logb 3 base :=
      add_le_add hdiv_le hlog_base_one
    _ = (1 + C / α) * Real.logb 3 base := by ring

/-- Power form of the polynomial bound on the prefactor-absorption delay. -/
theorem three_pow_prefactorDelay_le_rpow
    {A α base C : ℝ} (hα : 0 < α) (hbase : 3 ≤ base)
    (hC : 0 ≤ C) (hA : A ≤ Real.rpow base C) :
    (3 : ℝ) ^ prefactorDelay A α ≤ Real.rpow base (1 + C / α) := by
  have hdelay := prefactorDelay_cast_le_logb hα hbase hC hA
  have hbase_pos : 0 < base := by linarith only [hbase]
  calc
    (3 : ℝ) ^ prefactorDelay A α =
        Real.rpow (3 : ℝ) (prefactorDelay A α : ℝ) := by
      exact (Real.rpow_natCast 3 (prefactorDelay A α)).symm
    _ ≤ Real.rpow (3 : ℝ) ((1 + C / α) * Real.logb 3 base) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hdelay
    _ = Real.rpow (3 : ℝ) (Real.logb 3 base * (1 + C / α)) := by
      congr 1
      ring
    _ = Real.rpow (Real.rpow (3 : ℝ) (Real.logb 3 base)) (1 + C / α) :=
      Real.rpow_mul (by norm_num) _ _
    _ = Real.rpow base (1 + C / α) := by
      congr 1
      exact Real.rpow_logb (by norm_num) (by norm_num) hbase_pos

/-- Combining a polynomial entry generation with a polynomial prefactor gives
a polynomial bound on the full unit-prefactor delay. -/
theorem three_pow_totalDecayDelay_le_rpow
    {n₀ : ℕ} {A α base Centry Cpref : ℝ}
    (hα : 0 < α) (hbase : 3 ≤ base) (hCpref : 0 ≤ Cpref)
    (hentry : (3 : ℝ) ^ (2 * n₀) ≤ Real.rpow base Centry)
    (hpref : A ≤ Real.rpow base Cpref) :
    (3 : ℝ) ^ totalDecayDelay n₀ A α ≤
      Real.rpow base (Centry + (1 + Cpref / α)) := by
  have hpref_delay := three_pow_prefactorDelay_le_rpow hα hbase hCpref hpref
  have hbase_pos : 0 < base := by linarith only [hbase]
  have hright_nonneg : 0 ≤ Real.rpow base Centry :=
    Real.rpow_nonneg hbase_pos.le _
  calc
    (3 : ℝ) ^ totalDecayDelay n₀ A α =
        (3 : ℝ) ^ (2 * n₀) * (3 : ℝ) ^ prefactorDelay A α := by
      dsimp [totalDecayDelay]
      rw [pow_add]
    _ ≤ Real.rpow base Centry * Real.rpow base (1 + Cpref / α) :=
      mul_le_mul hentry hpref_delay (by positivity) hright_nonneg
    _ = Real.rpow base (Centry + (1 + Cpref / α)) := by
      exact (Real.rpow_add hbase_pos _ _).symm

end
end HCPolySupport.HighContrast.Quenched.Prop42Scalar
