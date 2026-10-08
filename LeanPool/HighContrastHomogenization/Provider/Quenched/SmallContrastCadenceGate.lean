/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.FixedGridWindowAccount
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAbsorptionChoice
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAdjointMirrors
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAlignedGeometry
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAnnealedEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAverageDrops
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCenteringCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryCapsIsotropy
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryRateMean
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntrySupply
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastFusionStep
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHvarFamily
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMeanDropCarrier
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastOneStepHub
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRealClauses
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRowAtCenters
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSingleCellVariance
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSlotValue
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastTerminalComparability
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastVarianceLagged
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakValue
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormAdjointAlgebra
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungFixedGridCells
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowOscillationSum
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowSchur
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowSkewCarriers

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCadenceGate

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The cadence gates: depth reachability, the fixed margin, and the one-window dichotomy

Three gates, checked before the cadence induction.

**(a) Reachability.**  The family quantifier of rows 346-347 reaches every
fixed depth `m ≤ Hw n` (reachability, in the producers' own `ℤ`-clause form), and the window
budget `Hw n := n − b` satisfies the
producers' availability constraints exactly when the fixed bound sits at
`N₀ + b` — the β-window/tree-window bridge
is one inequality per constraint, not a construction.

**(b) The margin.**  At the tree's constants the cadence window is a FIXED
law-free depth, not the print-frame level-dependent `M_λ`: the tree's error
is already exponential (`deltaRec·ra^n`), so level-dependence was paid into
the rate, and the per-stage margin is `c_A` with `6A ≤ 3^(α·c_A)` — which
exists at `c_A ≈ log₃(6A)/α` and yields the head
attenuation `A·ra^(c_A) ≤ 1/6` (`cadence_head_margin24`).

**(c) The one-window dichotomy** (`cadence_one_window_dichotomy`): from one
family member's recursion at a window of any depth, with the drop history
split into the window's telescope and the attenuated head, EITHER the value
collapses to four times the head-plus-error floor, OR it sits a strict
`(1+1/(2A))`-factor below the window's top.  The drop share and the error
share are absorbed with the quadratic dominant — the budget every gate so
far has asked for, and here it closes law-free because the plateau branch's
quadratic is self-referential.  The disjunction is unconditional given the
standing smallness `9·A·F ≤ 1`, so a cadence induction can consume it at
every stage; and its short-window members force `δ ≤ A·δ² + err` on any flat
stretch, which is false — the class admits no plateau, consistently with the
membership finding for the staircase.
-/

namespace HCPolySupport.HighContrast.Quenched

/-- **(c) The one-window dichotomy.**  From one family member's recursion at
any window, with the drop history split into the window telescope and the
head: either the value collapses to four times the head-plus-error floor, or
it sits a strict `(1+1/(2A))` factor below the window's top. -/
theorem cadence_one_window_dichotomy {A Fn FW DS hd err : ℝ}
    (hA : 1 ≤ A) (hFn0 : 0 ≤ Fn) (hFW0 : 0 ≤ FW)
    (hsmall : 9 * A * Fn ≤ 1)
    (hrec : Fn ≤ A * DS + A * FW ^ 2 + err)
    (hDS : DS ≤ (FW - Fn) + hd) :
    Fn ≤ 4 * (A * hd + err) ∨ (1 + 1 / (2 * A)) * Fn < FW := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA
  by_cases hpl : FW ≤ (1 + 1 / (2 * A)) * Fn
  · left
    have h1 : Fn ≤ A * ((FW - Fn) + hd) + A * FW ^ 2 + err := by
      have := mul_le_mul_of_nonneg_left hDS hA0.le
      linarith only [hrec, this]
    have hAFW : A * FW ≤ (A + 1 / 2) * Fn := by
      have h2 := mul_le_mul_of_nonneg_left hpl hA0.le
      have h3 : A * ((1 + 1 / (2 * A)) * Fn) = (A + 1 / 2) * Fn := by
        field_simp
      linarith only [h2, h3.le, h3.ge]
    have h32 : FW ≤ (3 / 2) * Fn := by
      have hhalf : 1 / (2 * A) ≤ 1 / 2 := by
        have h2A : (2 : ℝ) ≤ 2 * A := by linarith only [hA]
        exact one_div_le_one_div_of_le (by norm_num) h2A
      have : (1 + 1 / (2 * A)) * Fn ≤ (3 / 2) * Fn := by
        exact mul_le_mul_of_nonneg_right (by linarith only [hhalf]) hFn0
      linarith only [hpl, this]
    have hFW2 : A * FW ^ 2 ≤ Fn / 4 := by
      have hs1 : FW ^ 2 ≤ (3 / 2 * Fn) ^ 2 := pow_le_pow_left₀ hFW0 h32 2
      have hs2 : A * FW ^ 2 ≤ A * (3 / 2 * Fn) ^ 2 :=
        mul_le_mul_of_nonneg_left hs1 hA0.le
      have hs3 : A * (3 / 2 * Fn) ^ 2 = 9 * A * Fn * (Fn / 4) := by ring
      have hs4 : 9 * A * Fn * (Fn / 4) ≤ 1 * (Fn / 4) :=
        mul_le_mul_of_nonneg_right hsmall (by linarith only [hFn0])
      linarith only [hs2, hs3.le, hs3.ge, hs4]
    linarith only [h1, hAFW, hFW2]
  · right
    exact lt_of_not_ge hpl

end HCPolySupport.HighContrast.Quenched
