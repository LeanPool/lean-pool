/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorAnchoredMeanTelescope

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorAnchoredMeanGrowth

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Scale-linear growth of anchored corrector means

This module converts a scale-linear normalized `L²` oscillation bound into a
scale-linear bound for the centered-cube means.  The finitely many scales below
the oscillation threshold are retained as a fixed prefix.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The shifted geometric sum at triadic scales is bounded by the next
triadic scale. -/
theorem sum_range_three_pow_succ_le (n : ℕ) :
    ∑ k ∈ Finset.range n, (3 : ℝ) ^ (k + 1) ≤
      3 * (3 : ℝ) ^ n := by
  have hsum :
      ∑ k ∈ Finset.range n, (3 : ℝ) ^ (k + 1) =
        3 * (((3 : ℝ) ^ n - 1) / 2) := by
    rw [show (∑ k ∈ Finset.range n, (3 : ℝ) ^ (k + 1)) =
        3 * ∑ k ∈ Finset.range n, (3 : ℝ) ^ k by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_succ]
      ring]
    rw [geom_sum_eq (by norm_num : (3 : ℝ) ≠ 1)]
    norm_num
  rw [hsum]
  have hpow : 0 ≤ (3 : ℝ) ^ n := pow_nonneg (by norm_num) n
  linarith only [hpow]

/-- A scale-linear normalized oscillation bound above a threshold gives a
`3^n` bound for the fixed-unit-normalized outer corrector mean. -/
theorem NormalizedLocalH1Carrier.exists_abs_cubeAverage_le_three_pow_of_oscillation_bound
    {d : ℕ} (z : NormalizedLocalH1Carrier d)
    (q₀ : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hosc : ∀ q : ℕ, q₀ ≤ q →
      cubeBesovOscillation (originCube d (q : ℤ)) (2 : ℝ≥0∞)
          (z.localH1Function q).toFun ≤ M * (3 : ℝ) ^ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, q₀ ≤ n →
      |cubeAverage (originCube d (n : ℤ)) z.globalValueRepresentative| ≤
        C * (3 : ℝ) ^ n := by
  let D : ℝ := ((3 ^ d : ℕ) : ℝ)
  let P : ℝ := ∑ k ∈ Finset.range q₀, anchoredCorrectorMeanStepBound z k
  let C : ℝ := P + 3 * D * M
  have hD : 0 ≤ D := Nat.cast_nonneg _
  have hstep_nonneg : ∀ k : ℕ, 0 ≤ anchoredCorrectorMeanStepBound z k := by
    intro k
    unfold anchoredCorrectorMeanStepBound cubeBesovOscillation
    exact mul_nonneg (Nat.cast_nonneg _) (cubeLpNorm_nonneg _ _ _)
  have hP : 0 ≤ P := by
    dsimp only [P]
    exact Finset.sum_nonneg fun k _ => hstep_nonneg k
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro n hq₀n
  have htail :
      ∑ k ∈ Finset.Ico q₀ n, anchoredCorrectorMeanStepBound z k ≤
        D * M * ∑ k ∈ Finset.range n, (3 : ℝ) ^ (k + 1) := by
    calc
      ∑ k ∈ Finset.Ico q₀ n, anchoredCorrectorMeanStepBound z k ≤
          ∑ k ∈ Finset.Ico q₀ n, D * M * (3 : ℝ) ^ (k + 1) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk₀ : q₀ ≤ k := (Finset.mem_Ico.mp hk).1
        have hosck := hosc (k + 1) (hk₀.trans (Nat.le_succ k))
        unfold anchoredCorrectorMeanStepBound
        dsimp only [D]
        calc
          ((3 ^ d : ℕ) : ℝ) *
                cubeBesovOscillation (originCube d ((k + 1 : ℕ) : ℤ)) (2 : ℝ≥0∞)
                  (z.localH1Function (k + 1)).toFun
              ≤ ((3 ^ d : ℕ) : ℝ) * (M * (3 : ℝ) ^ (k + 1)) :=
            mul_le_mul_of_nonneg_left hosck (Nat.cast_nonneg _)
          _ = ((3 ^ d : ℕ) : ℝ) * M * (3 : ℝ) ^ (k + 1) := by ring
      _ ≤ ∑ k ∈ Finset.range n, D * M * (3 : ℝ) ^ (k + 1) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
        · intro k _ _
          positivity
      _ = D * M * ∑ k ∈ Finset.range n, (3 : ℝ) ^ (k + 1) := by
        rw [Finset.mul_sum]
  have hsumSplit :
      ∑ k ∈ Finset.range n, anchoredCorrectorMeanStepBound z k =
        P + ∑ k ∈ Finset.Ico q₀ n, anchoredCorrectorMeanStepBound z k := by
    dsimp only [P]
    exact (Finset.sum_range_add_sum_Ico _ hq₀n).symm
  calc
    |cubeAverage (originCube d (n : ℤ)) z.globalValueRepresentative| ≤
        ∑ k ∈ Finset.range n, anchoredCorrectorMeanStepBound z k :=
      z.abs_cubeAverage_globalValueRepresentative_le_sum n
    _ = P + ∑ k ∈ Finset.Ico q₀ n,
        anchoredCorrectorMeanStepBound z k := hsumSplit
    _ ≤ P + D * M * ∑ k ∈ Finset.range n, (3 : ℝ) ^ (k + 1) :=
      by simpa only [add_comm] using add_le_add_left htail P
    _ ≤ P + D * M * (3 * (3 : ℝ) ^ n) := by
      gcongr
      exact sum_range_three_pow_succ_le n
    _ ≤ C * (3 : ℝ) ^ n := by
      have hone : 1 ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      have hprefix : P ≤ P * (3 : ℝ) ^ n :=
        by simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hP
      dsimp only [C]
      linarith only [hprefix, mul_nonneg hD hM]

end

end HighContrast
end HCPolySupport
