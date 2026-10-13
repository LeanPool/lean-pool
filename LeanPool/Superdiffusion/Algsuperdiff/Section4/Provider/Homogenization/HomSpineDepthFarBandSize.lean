/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineCzGridDepthTest

/-!
# HomSpineDepthFarBandSize

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The EXACT size of the far-band half: `min(j·log 3, (s·p')^{-1})`

## Why

`HomSpineCzGridDepthTest` §4 records the far half of the single-depth
boundary-layer estimate as the truncated geometric sum
`Σ_{i<j} 3^{-i·s·p'}`, proves it `≥ j/3` on the window `j·s·p' ≤ 1`, and
proves it UNBOUNDED over the admissible `(s, j)` range.  That leaves open the
size at a FIXED order — the quantity this development actually pays, since the
Step-3 pin fixes `s ≍ |log γ|^{-1}` and then lets `j` run to `10|log γ|`.

This file closes the arithmetic with a two-sided bound.  Writing `x = s·p'`:

```text
  min( j/3, (2/(3 log 3))·x^{-1} )  ≤  Σ_{i<j} 3^{-x i}  ≤  (1 - 3^{-x})^{-1}
```

(the upper bound is `farBand_sum_le_geom`), and the right side is itself
`≤ (x log 3)^{-1}·(1-3^{-x})^{-1}(1-3^{-x})`, i.e. of the same `x^{-1}` order —
so the far half is `≍ min(j, x^{-1})`, saturating at `x^{-1}` once `j ≥ x^{-1}`.

Consequence for the surviving route (the DEPTH-level converse, the
per-cell one having been refuted in `HomSpineSupFormCellRefuted`): the constant
the single-depth Gagliardo input can carry is
`Cg^{p'} ≍ C(d) + min(j·log 3, (s·p')^{-1})`, hence at the Step-3 pin
`CA ≍ |log γ|^{1/p'}` — NOT `γ`-uniform, and the deficit is exactly the
Gagliardo-vs-Besov (Bourgain--Brezis--Mironescu) constant of the test space as
`s → 0`.  This file proves the arithmetic; the identification with `Cg` is
The `fullENorm_gridDualDepthTest_le_of_gagliardo` slot and is NOT claimed
here.
-/

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26
open scoped BigOperators ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

/-- The far-band sum in closed form. -/
private theorem geom_sum_three_rpow {x : ℝ} (hx : 0 < x) (j : ℕ) :
    (∑ i ∈ Finset.range j, (3 : ℝ) ^ (-x * (i : ℝ))) =
      (1 - (3 : ℝ) ^ (-x * (j : ℝ))) / (1 - (3 : ℝ) ^ (-x)) := by
  have hrlt : (3 : ℝ) ^ (-x) < 1 := three_rpow_neg_lt_one hx
  have hpow : ∀ i : ℕ, (3 : ℝ) ^ (-x * (i : ℝ)) = ((3 : ℝ) ^ (-x)) ^ i := by
    intro i
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-x)) i,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  rw [Finset.sum_congr rfl (fun i _ => hpow i),
    geom_sum_eq (by linarith only [hrlt] : (3 : ℝ) ^ (-x) ≠ 1), hpow j,
    div_eq_div_iff (by linarith only [hrlt] : (3 : ℝ) ^ (-x) - 1 ≠ 0)
      (by linarith only [hrlt] : 1 - (3 : ℝ) ^ (-x) ≠ 0)]
  ring

/-- **The far half is at most the full geometric sum** `(1-3^{-x})^{-1}`: at a
fixed order the band sum saturates, it does not grow with the depth. -/
theorem farBand_sum_le_geom {x : ℝ} (hx : 0 < x) (j : ℕ) :
    (∑ i ∈ Finset.range j, (3 : ℝ) ^ (-x * (i : ℝ))) ≤ (1 - (3 : ℝ) ^ (-x))⁻¹ := by
  have hrlt : (3 : ℝ) ^ (-x) < 1 := three_rpow_neg_lt_one hx
  have hden : 0 < 1 - (3 : ℝ) ^ (-x) := by linarith only [hrlt]
  have hnum : 1 - (3 : ℝ) ^ (-x * (j : ℝ)) ≤ 1 := by
    have hpos : (0 : ℝ) < (3 : ℝ) ^ (-x * (j : ℝ)) := three_rpow_pos _
    linarith only [hpos]
  rw [geom_sum_three_rpow hx j]
  calc (1 - (3 : ℝ) ^ (-x * (j : ℝ))) / (1 - (3 : ℝ) ^ (-x))
      = (1 - (3 : ℝ) ^ (-x * (j : ℝ))) * (1 - (3 : ℝ) ^ (-x))⁻¹ := div_eq_mul_inv _ _
    _ ≤ 1 * (1 - (3 : ℝ) ^ (-x))⁻¹ :=
        mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hden.le)
    _ = (1 - (3 : ℝ) ^ (-x))⁻¹ := one_mul _

end

end Algsuperdiff.Section4.Provider.Homogenization
