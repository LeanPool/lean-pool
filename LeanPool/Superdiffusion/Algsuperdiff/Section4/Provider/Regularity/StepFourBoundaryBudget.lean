/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourCollapseInterface
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFiveBoundaryDelta

/-!
# StepFourBoundaryBudget

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory

noncomputable section

/-! ## 1. The window count -/

/-- `|Icc n m| = (m-n)+1` as a real, for `n ≤ m`. -/
theorem card_Icc_cast (n m : ℤ) (hnm : n ≤ m) :
    (((Finset.Icc n m).card : ℕ) : ℝ) = ((m : ℝ) - (n : ℝ)) + 1 := by
  rw [Int.card_Icc]
  have h : (((m + 1 - n).toNat : ℤ) : ℝ) = ((m + 1 - n : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun x : ℤ => (x : ℝ)) (Int.toNat_of_nonneg (by omega))
  push_cast at h ⊢
  linarith only [h]

/-! ## 2. The boundary budget kit: legs -/

/-- **`e.sum.delta.j.bound` with the anchor's `ε`-free flat leg carried.**

`δ_j = A^g_j + (A^h_j + ε_j H + F) 𝟙` with `A^g`, `A^h` geometrically dominated
from the top scale and `F` a constant (flat) leg.  Then

```text
   ∑_{j=n}^{m} δ_j ≤ K_g/(1-r₁) + ( K_h/(1-r₂) + S_ε H + W F ) 𝟙 ,   W = (m-n)+1 .
```

The flat leg's contribution is `W`-linear: it is the only summand whose
coefficient is not bought by the `ε`-budget. -/
theorem sum_Icc_top_boundaryDelta_le_of_legs
    {δ Ag Ah ε : ℤ → ℝ} {r₁ r₂ Kg Kh Hinf Flat Se W ind : ℝ} {n m : ℤ} (hnm : n ≤ m)
    (hr₁0 : 0 < r₁) (hr₁1 : r₁ < 1) (hr₂0 : 0 < r₂) (hr₂1 : r₂ < 1)
    (hAg0 : 0 ≤ Ag m) (hAgd : ∀ j : ℤ, j ≤ m → Ag j ≤ Kg * r₁ ^ (m - j))
    (hAh0 : 0 ≤ Ah m) (hAhd : ∀ j : ℤ, j ≤ m → Ah j ≤ Kh * r₂ ^ (m - j))
    (hSe : ∑ j ∈ Finset.Icc n m, ε j ≤ Se)
    (hHinf : 0 ≤ Hinf) (hind0 : 0 ≤ ind) (hW : W = ((m : ℝ) - (n : ℝ)) + 1)
    (hδ : ∀ j : ℤ, δ j = Ag j + (Ah j + ε j * Hinf + Flat) * ind) :
    ∑ j ∈ Finset.Icc n m, δ j ≤
      Kg / (1 - r₁) + (Kh / (1 - r₂) + Se * Hinf + W * Flat) * ind := by
  have hgleg : ∑ j ∈ Finset.Icc n m, Ag j ≤ Kg / (1 - r₁) :=
    sum_Icc_top_le_of_zpow_dominated hr₁0 hr₁1 hnm hAg0 hAgd
  have hhleg : ∑ j ∈ Finset.Icc n m, Ah j ≤ Kh / (1 - r₂) :=
    sum_Icc_top_le_of_zpow_dominated hr₂0 hr₂1 hnm hAh0 hAhd
  have hflat : ∑ _j ∈ Finset.Icc n m, Flat = W * Flat := by
    rw [Finset.sum_const, nsmul_eq_mul, card_Icc_cast n m hnm, hW]
  have heq : ∑ j ∈ Finset.Icc n m, δ j
      = (∑ j ∈ Finset.Icc n m, Ag j)
        + ((∑ j ∈ Finset.Icc n m, Ah j) + (∑ j ∈ Finset.Icc n m, ε j) * Hinf
            + (∑ _j ∈ Finset.Icc n m, Flat)) * ind := by
    rw [Finset.sum_congr rfl fun j _ => hδ j]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [heq, hflat]
  have hmid : (∑ j ∈ Finset.Icc n m, Ah j) + (∑ j ∈ Finset.Icc n m, ε j) * Hinf + W * Flat
      ≤ Kh / (1 - r₂) + Se * Hinf + W * Flat := by
    have h := mul_le_mul_of_nonneg_right hSe hHinf
    linarith only [hhleg, h]
  have hmul := mul_le_mul_of_nonneg_right hmid hind0
  linarith only [hgleg, hmul]

/-! ## 3. `stepFourDeltaOut` in the boundary four-leg shape -/

/-- The single constant the Step-4 boundary output collapses to: `C_rem V_d C
(s^{-4} s^{-3/2} + 8 s^{-7} + s^{-6})`. -/
def stepFourBoundaryDeltaConst (Crem Vd Cst s : ℝ) : ℝ :=
  Crem * Vd *
    (Cst * (s ^ (-(4 : ℝ)) * s ^ (-(3 / 2 : ℝ)) + 8 * s ^ (-(7 : ℝ)) + s ^ (-(6 : ℝ))))

theorem stepFourBoundaryDeltaConst_nonneg {Crem Vd Cst s : ℝ} (hCV : 0 ≤ Crem * Vd)
    (hCst : 0 ≤ Cst) (hs : 0 < s) : 0 ≤ stepFourBoundaryDeltaConst Crem Vd Cst s := by
  have h4 : (0 : ℝ) ≤ s ^ (-(4 : ℝ)) * s ^ (-(3 / 2 : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg hs.le _) (Real.rpow_nonneg hs.le _)
  have h7 : (0 : ℝ) ≤ s ^ (-(7 : ℝ)) := Real.rpow_nonneg hs.le _
  have h6 : (0 : ℝ) ≤ s ^ (-(6 : ℝ)) := Real.rpow_nonneg hs.le _
  rw [stepFourBoundaryDeltaConst]
  exact mul_nonneg hCV (mul_nonneg hCst (by linarith only [h4, h7, h6]))

end

end Algsuperdiff.Section4.Provider.Regularity
