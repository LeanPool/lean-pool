/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Assembly.Coulomb

/-! # Finite Coulomb forms and extended-to-real arithmetic

Elementary finite-sum and arithmetic steps for the real quadratic-form corollary.
The electron estimate is supplied by `RealFormPairs`.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.Assembly

/-- Distinct nuclear positions give finite nuclear repulsion. -/
theorem nuclearRepulsion_lt_top {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) :
    nuclearRepulsion z R < ⊤ := by
  unfold nuclearRepulsion
  apply ENNReal.sum_lt_top.mpr
  intro k _
  apply ENNReal.sum_lt_top.mpr
  intro l hl
  have hkl : k ≠ l := ne_of_lt (Finset.mem_filter.mp hl).2
  rw [coulombKernel_eq_of_ne (fun h => hkl (hR h))]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top)
    ENNReal.ofReal_lt_top

/-- An extended additive estimate with finite positive terms gives attraction
finiteness and the corresponding real energy lower bound. -/
theorem real_form_of_extended_bound {A T B U : ℝ≥0∞} (C : ℝ≥0) (K : ℕ)
    (hT : T < ⊤) (hB : B < ⊤) (hU : U < ⊤)
    (hA : A ≤ T + B + U + (C : ℝ≥0∞) * K) :
    A < ⊤ ∧ -(C : ℝ) * (K : ℝ) ≤ T.toReal + B.toReal + U.toReal - A.toReal := by
  have hTB : T + B < ⊤ := ENNReal.add_lt_top.mpr ⟨hT, hB⟩
  have hTBU : T + B + U < ⊤ := ENNReal.add_lt_top.mpr ⟨hTB, hU⟩
  have hCK : (C : ℝ≥0∞) * K < ⊤ :=
    ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.natCast_lt_top K)
  have htotal : T + B + U + (C : ℝ≥0∞) * K < ⊤ :=
    ENNReal.add_lt_top.mpr ⟨hTBU, hCK⟩
  have hAfin : A < ⊤ := hA.trans_lt htotal
  refine ⟨hAfin, ?_⟩
  have hreal := (ENNReal.toReal_le_toReal hAfin.ne htotal.ne).mpr hA
  rw [ENNReal.toReal_add hTBU.ne hCK.ne, ENNReal.toReal_add hTB.ne hU.ne,
    ENNReal.toReal_add hT.ne hB.ne, ENNReal.toReal_mul,
    ENNReal.coe_toReal, ENNReal.toReal_natCast] at hreal
  linarith only [hreal]

end LiebThirring.Assembly
end
