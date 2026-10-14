/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Definitions
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeNeumannW22CZ.Regularity

/-!
# Shared sensitivity constants

Common pairing and zero-trace constants extracted from scottnarmstrong/Superdiffusion
at 7f20476385d4af418f110303085ad0740c9eba46 for the flux and difference-quotient routes.
-/

@[expose] public section

namespace Algsuperdiff.Section24.Sensitivity.Provider.PairingConstants

open HCPolySupport HCPolySupport.Book

noncomputable section

/-- The scale-free discount factor of the coarse Poincaré right-hand side at the
sensitivity gauge is positive. -/
theorem poincareDiscountFactor_sensitivity_pos :
    0 < Ch03.poincareDiscountFactor (3 / 8) (.finite 2) := by
  have hbase : 0 < Ch02.geometricDiscount (3 / 8 : ℝ) 2 := by
    have h3 : Real.rpow (3 : ℝ) (-(3 / 8 : ℝ) * 2) < 1 := by
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    simpa [Ch02.geometricDiscount] using sub_pos.2 h3
  simpa [Ch03.poincareDiscountFactor] using
    Real.rpow_pos_of_pos hbase (-(1 / 2 : ℝ))

/-- The constant of the zero-trace `L²` estimate at the gauge exponent. -/
def zeroTraceValueConst (d : ℕ) : ℝ :=
  (((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d * (3 : ℝ) ^ ((d : ℝ) + 1) *
        (d : ℝ)) + 2 * (3 : ℝ) ^ ((d : ℝ) + 1)) *
    Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - 3 / 16)))⁻¹)

theorem zeroTraceValueConst_nonneg (d : ℕ) :
    0 ≤ zeroTraceValueConst d := by
  have h1 : (0 : ℝ) ≤ Legacy.cubeNeumannW22CalderonZygmundConstant d :=
    Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d
  have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ ((d : ℝ) + 1) :=
    Real.rpow_nonneg (by norm_num) _
  have h3 : (0 : ℝ) ≤
      Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - 3 / 16)))⁻¹) :=
    Real.sqrt_nonneg _
  unfold zeroTraceValueConst
  positivity

/-- The Besov pairing constant at the shared sensitivity gauge. -/
def besovPairingConstant (d : ℕ) : ℝ :=
  (1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
    (2 * Ch03.poincareDiscountFactor (3 / 8) (.finite 2))

theorem besovPairingConstant_pos (d : ℕ) : 0 < besovPairingConstant d := by
  have h1 : (0 : ℝ) < 1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1) := by
    have : (0 : ℝ) < Real.rpow (3 : ℝ) ((d : ℝ) + 1) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    nlinarith
  have h2 : (0 : ℝ) < 2 * Ch03.poincareDiscountFactor (3 / 8) (.finite 2) := by
    have := poincareDiscountFactor_sensitivity_pos
    linarith
  exact mul_pos h1 h2

end

end Algsuperdiff.Section24.Sensitivity.Provider.PairingConstants
