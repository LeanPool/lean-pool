/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ReserveTraceInterpolation
public import LeanPool.VacuumBellSeparation.Gaussian.ReserveNuclearSeries

/-!
# Actual nuclear summation after reserve interpolation

The same explicit interpolated operators are summed in the true operator
norm. Their nuclear estimates are consequences of the proved interpolation
theorem, and the original series identifies the resulting reserve factor.
Only the numerical endpoint bounds and their genuine summability remain
inputs for the polynomial approximation application.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open scoped ENNReal

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem exists_reserve_factor_of_interpolated_series
    {R D : E →L[ℂ] E} {B G : ι → E →L[ℂ] E}
    (hR : 0 ≤ R) (hcB : ∀ i, IsCompactOperator (B i))
    (hB : ∀ i, IsSelfAdjoint (B i)) (htB : ∀ i, operatorTraceNorm (B i) < ∞)
    (hfactor : ∀ i, R ^ (1 / 2 : ℝ) * B i * R ^ (1 / 2 : ℝ) = G i)
    (hG : HasSum G D) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (ht : (∑' i, operatorTraceNorm (G i) ^ (1 - θ) * operatorTraceNorm (B i) ^ θ) < ∞) :
    ∃ Y : E →L[ℂ] E, D = R ^ (θ / 2) * Y * R ^ (θ / 2) ∧
      IsCompactOperator Y ∧ IsSelfAdjoint Y ∧
      operatorTraceNorm Y ≤ ∑' i, operatorTraceNorm (G i) ^ (1 - θ) * operatorTraceNorm (B i) ^ θ ∧
      operatorTraceNorm Y < ∞ := by
  classical
  let Z (i : ι) := R ^ ((1 - θ) / 2) * B i * R ^ ((1 - θ) / 2)
  have hS : IsSelfAdjoint (R ^ ((1 - θ) / 2)) := CFC.rpow_nonneg.isSelfAdjoint
  have hcZ (i : ι) : IsCompactOperator (Z i) :=
    ((hcB i).clm_comp (R ^ ((1 - θ) / 2))).comp_clm (R ^ ((1 - θ) / 2))
  have hsZ (i : ι) : IsSelfAdjoint (Z i) := selfAdjoint_sandwich_isSelfAdjoint (hB i) hS
  have hZi (i : ι) : operatorTraceNorm (Z i) ≤
      operatorTraceNorm (G i) ^ (1 - θ) * operatorTraceNorm (B i) ^ θ := by
    simpa only [hfactor i] using operatorTraceNorm_reserve_interpolation hR (hcB i) (hB i)
      (htB i) hθ
  have hsum : (∑' i, operatorTraceNorm (Z i)) ≤
      ∑' i, operatorTraceNorm (G i) ^ (1 - θ) * operatorTraceNorm (B i) ^ θ :=
    tsum_le_tsum hZi
  obtain ⟨Y, hf, hc, hs, hn, hfin⟩ := exists_reserve_factor_of_nuclear_series (R ^ (θ / 2))
    hG (fun i => ((reserve_power_interpolation_factorization hR (B i) ⟨hθ.1.le, hθ.2.le⟩).trans
      (hfactor i)).symm) hcZ hsZ (hsum.trans_lt ht)
  exact ⟨Y, hf, hc, hs, hn.trans hsum, hfin⟩

theorem exists_reserve_factor_of_interpolated_majorants
    {R D : E →L[ℂ] E} {B G : ι → E →L[ℂ] E}
    (hR : 0 ≤ R) (hcB : ∀ i, IsCompactOperator (B i))
    (hB : ∀ i, IsSelfAdjoint (B i)) (htB : ∀ i, operatorTraceNorm (B i) < ∞)
    (hfactor : ∀ i, R ^ (1 / 2 : ℝ) * B i * R ^ (1 / 2 : ℝ) = G i)
    (hG : HasSum G D) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (a b : ι → ℝ≥0∞) (ha : ∀ i, operatorTraceNorm (G i) ≤ a i)
    (hb : ∀ i, operatorTraceNorm (B i) ≤ b i)
    (ht : (∑' i, a i ^ (1 - θ) * b i ^ θ) < ∞) :
    ∃ Y : E →L[ℂ] E, D = R ^ (θ / 2) * Y * R ^ (θ / 2) ∧
      IsCompactOperator Y ∧ IsSelfAdjoint Y ∧
      operatorTraceNorm Y ≤ ∑' i, a i ^ (1 - θ) * b i ^ θ ∧ operatorTraceNorm Y < ∞ := by
  have hm : (∑' i, operatorTraceNorm (G i) ^ (1 - θ) * operatorTraceNorm (B i) ^ θ) ≤
      ∑' i, a i ^ (1 - θ) * b i ^ θ := by
    apply tsum_le_tsum
    intro i
    exact mul_le_mul' (ENNReal.rpow_le_rpow (ha i) (sub_nonneg.mpr hθ.2.le))
      (ENNReal.rpow_le_rpow (hb i) hθ.1.le)
  obtain ⟨Y, hf, hc, hs, hn, hfin⟩ := exists_reserve_factor_of_interpolated_series
    hR hcB hB htB hfactor hG hθ (hm.trans_lt ht)
  exact ⟨Y, hf, hc, hs, hn.trans hm, hfin⟩

end VacuumBellSeparation.Gaussian
