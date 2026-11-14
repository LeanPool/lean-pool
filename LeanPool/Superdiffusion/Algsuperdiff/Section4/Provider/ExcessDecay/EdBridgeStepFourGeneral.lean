/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EdBridgeStepFour
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundaryCompose
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepEvenBoundFinal
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddClassCornerProducer
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddCompose

/-!
# EdBridgeStepFourGeneral

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The bridge's constants at a general Schauder constant -/

/-- The one-step remainder's weight at a general Schauder constant `Cs`:
`C_r(d, Cs, k) · √((3²)^d)`.  At `Cs = schauderWindowConst d` this is `edBridgeRemWeight`. -/
def edBridgeRemWeightGen (d : ℕ) (Cs : ℝ) (k : ℕ) : ℝ :=
  triangleRemainderConst d Cs k * Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d)

theorem edBridgeRemWeightGen_nonneg (d : ℕ) {Cs : ℝ} (hCs : 0 ≤ Cs) (k : ℕ) :
    0 ≤ edBridgeRemWeightGen d Cs k :=
  mul_nonneg (triangleRemainderConst_nonneg d hCs k) (Real.sqrt_nonneg _)

/-- The `ε` constant of the bridge at a general Schauder constant `Cs`. -/
def edBridgeEpsConstGen (d : ℕ) (Cs C : ℝ) (k : ℕ) : ℝ :=
  3 * edBridgeRemWeightGen d Cs k * C * endpointConst d (1 / 9 : ℝ)

/-- ** residue 4 at a general Schauder constant.**

`EdBridgeFolds.exists_edBridgeStep` with `schauderWindowConst d` replaced by an arbitrary `Cs`:
the step size `k₀` depends on `Cs`, nothing else in the argument does.  The join runs at
`Cs = max (schauderWindowConst d) C_bdry`. -/
theorem exists_edBridgeStepGen (d : ℕ) (Cs : ℝ) :
    ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      taylorContractionConst d * Cs * windowRatioConst d 2
            * windowRatioConst d 1 * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
        ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) := by
  classical
  obtain ⟨hq0, hq1⟩ := rpow_quarter_mem
  set q : ℝ := (3 : ℝ) ^ (-(1 / 4 : ℝ)) with hqdef
  set A : ℝ := max (taylorContractionConst d * Cs * windowRatioConst d 2
    * windowRatioConst d 1) 1 with hAdef
  have hA1 : (1 : ℝ) ≤ A := le_max_right _ _
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA1
  have hAle : taylorContractionConst d * Cs * windowRatioConst d 2
      * windowRatioConst d 1 ≤ A := le_max_left _ _
  obtain ⟨k₁, hk₁⟩ := exists_pow_lt_of_lt_one (x := 1 / 2 * q / A) (y := q)
    (div_pos (by linarith only [hq0] : (0 : ℝ) < 1 / 2 * q) hApos) hq1
  refine ⟨max k₁ 3, le_max_right _ _, ?_⟩
  intro k hk
  have hk1 : k₁ ≤ k := le_trans (le_max_left _ _) hk
  have hqk : q ^ k ≤ q ^ k₁ := pow_le_pow_of_le_one hq0.le hq1.le hk1
  have hqklt : q ^ k < 1 / 2 * q / A := lt_of_le_of_lt hqk hk₁
  have hqkpos : (0 : ℝ) < q ^ k := pow_pos hq0 k
  have hkey : A * q ^ k ≤ 1 / 2 * q := by
    have h := (le_div_iff₀ hApos).1 (le_of_lt hqklt)
    linarith only [h]
  have hmul : A * q ^ k * q ^ k ≤ 1 / 2 * q * q ^ k :=
    mul_le_mul_of_nonneg_right hkey hqkpos.le
  have hL : ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) = q ^ k * q ^ k := by
    rw [zpow_neg_rpow_half_eq k, rpow_half_eq_quarter_sq, ← hqdef, mul_pow]
  have hR : (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) = q * q ^ k := by
    rw [rpow_quarter_succ_eq k, ← hqdef]
  rw [hL, hR]
  have hqq : (0 : ℝ) ≤ q ^ k * q ^ k := mul_nonneg hqkpos.le hqkpos.le
  have hleft : taylorContractionConst d * Cs * windowRatioConst d 2
        * windowRatioConst d 1 * (q ^ k * q ^ k) ≤ A * (q ^ k * q ^ k) :=
    mul_le_mul_of_nonneg_right hAle hqq
  linarith only [hleft, hmul]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
