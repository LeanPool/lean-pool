/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Window.SuccessorDiscrete
public import LeanPool.HighContrastHomogenization.Provider.Window.SuccessorTail
public import LeanPool.HighContrastHomogenization.Provider.Window.ScaleMeasurability
public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.PsiCalculus

/-!
# High-contrast homogenization: Provider.Window.PsiShellAlgebra

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace IndependentSums

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

private theorem triangular_add_succ (m : ℕ) :
    natTriangular m + natTriangular (m + 1) = m * m := by
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_add, Nat.cast_mul, natTriangular_real_eq,
    natTriangular_real_eq]
  cases m with
  | zero => norm_num
  | succ m =>
      simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one]
      ring

/-- Iterated gauge growth, run backwards from a point above `B^m`. -/
theorem psi_lower_scaled_pow {Ψ : ℝ → ℝ} {B t : ℝ} (m : ℕ)
    (hB : 1 ≤ B) (hΨ : HasPsiGrowth Ψ B) (hAdmissible : AdmissiblePsi Ψ)
    (ht : B ^ m ≤ t) :
    B ^ natTriangular m * (t / B ^ m) ^ m ≤ Ψ t := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hBmp : 0 < B ^ m := pow_pos hBpos m
  have hu : 1 ≤ t / B ^ m := (le_div_iff₀ hBmp).2 (by simpa using ht)
  have hu0 : 0 ≤ t / B ^ m := zero_le_one.trans hu
  have hpre := hasPsiGrowth_nat_polyAbsorptionPre hB hΨ m hu
  have hψu : 1 ≤ Ψ (t / B ^ m) := hAdmissible.2 hu0
  have hupow : 0 ≤ (t / B ^ m) ^ m := pow_nonneg hu0 m
  have hbase : (t / B ^ m) ^ m ≤
      (t / B ^ m) ^ m * Ψ (t / B ^ m) := by
    calc
      (t / B ^ m) ^ m = (t / B ^ m) ^ m * 1 := by ring
      _ ≤ (t / B ^ m) ^ m * Ψ (t / B ^ m) :=
        mul_le_mul_of_nonneg_left hψu hupow
  have harg : B ^ m * (t / B ^ m) = t := by field_simp [hBmp.ne']
  have hraw : (t / B ^ m) ^ m ≤
      (B ^ natTriangular m)⁻¹ * Ψ t := by
    exact hbase.trans (by simpa only [harg] using hpre)
  have htri : 0 < B ^ natTriangular m := pow_pos hBpos _
  have hmul := mul_le_mul_of_nonneg_left hraw htri.le
  calc
    B ^ natTriangular m * (t / B ^ m) ^ m ≤
        B ^ natTriangular m *
          ((B ^ natTriangular m)⁻¹ * Ψ t) := hmul
    _ = Ψ t := by field_simp [htri.ne']

/-- On a region above `B^m`, degree `m` growth removes `m` powers from the
shifted moment quotient. -/
theorem rpow_div_psi_le {Ψ : ℝ → ℝ} {B t : ℝ} (n m : ℕ)
    (hB : 1 ≤ B) (hΨ : HasPsiGrowth Ψ B) (hAdmissible : AdmissiblePsi Ψ)
    (ht : B ^ m ≤ t) :
    t ^ ((n : ℝ) - 1) / Ψ t ≤
      B ^ natTriangular (m + 1) * t ^ ((n : ℝ) - (m : ℝ) - 1) := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have htpos : 0 < t := (pow_pos hBpos m).trans_le ht
  have hψt : 0 < Ψ t := lt_of_lt_of_le zero_lt_one (hAdmissible.2 htpos.le)
  let D : ℝ := B ^ natTriangular m * (t / B ^ m) ^ m
  have hDpos : 0 < D := by dsimp only [D]; positivity
  have hlower : D ≤ Ψ t := by
    exact psi_lower_scaled_pow m hB hΨ hAdmissible ht
  have hinv : (Ψ t)⁻¹ ≤ D⁻¹ := (inv_le_inv₀ hψt hDpos).2 hlower
  have hpow0 : 0 ≤ t ^ ((n : ℝ) - 1) := Real.rpow_nonneg htpos.le _
  have hmono : t ^ ((n : ℝ) - 1) * (Ψ t)⁻¹ ≤
      t ^ ((n : ℝ) - 1) * D⁻¹ :=
    mul_le_mul_of_nonneg_left hinv hpow0
  have htpow : t ^ ((n : ℝ) - 1) =
      t ^ m * t ^ ((n : ℝ) - (m : ℝ) - 1) := by
    calc
      t ^ ((n : ℝ) - 1) =
          t ^ ((m : ℝ) + ((n : ℝ) - (m : ℝ) - 1)) := by
            congr 1
            ring
      _ = t ^ (m : ℝ) * t ^ ((n : ℝ) - (m : ℝ) - 1) := by
        rw [Real.rpow_add htpos]
      _ = t ^ m * t ^ ((n : ℝ) - (m : ℝ) - 1) := by
        rw [Real.rpow_natCast]
  have hBpow : (B ^ m) ^ m =
      B ^ natTriangular m * B ^ natTriangular (m + 1) := by
    rw [← pow_mul, ← pow_add, triangular_add_succ]
  have hid : t ^ ((n : ℝ) - 1) * D⁻¹ =
      B ^ natTriangular (m + 1) * t ^ ((n : ℝ) - (m : ℝ) - 1) := by
    dsimp only [D]
    rw [htpow, div_pow, hBpow]
    field_simp [hBpos.ne', htpos.ne']
  calc
    t ^ ((n : ℝ) - 1) / Ψ t =
        t ^ ((n : ℝ) - 1) * (Ψ t)⁻¹ := by
          rw [div_eq_mul_inv]
    _ ≤ t ^ ((n : ℝ) - 1) * D⁻¹ := hmono
    _ = B ^ natTriangular (m + 1) *
        t ^ ((n : ℝ) - (m : ℝ) - 1) := hid

end
end IndependentSums
end HCPolySupport
