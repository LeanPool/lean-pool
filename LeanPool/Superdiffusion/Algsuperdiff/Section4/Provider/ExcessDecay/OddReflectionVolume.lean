/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionWindow
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# OddReflectionVolume

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Volume comparability of the window and its partial reflection

Since the normalized norm divides by the volume, that step needs the two
volumes to be comparable.

```text
  |V| = ∏ᵢ (windowHi i - windowLo i)₊ ,
  |reflected V| = ∏ᵢ (reflectedHi i - reflectedLo i)₊ ,
```

and using the per-coordinate edge identity of `OddReflectionWindow`
(each met coordinate doubles, each unmet coordinate is unchanged):

```text
  |V| ≤ |reflected V| ≤ 2^d · |V| .
```

The exact factor is `2^{#S}` for the met set `S`; the two-sided bound above is
the form the estimate consumes (the surplus `2^{d - #S}` is absorbed by the
dimensional constant `C(d)`), and it avoids carrying a `Finset` cardinality
through the analytic layer.

## What is not done here

The *cellwise change of variables* — that `∫_{reflected V} |oddExtend f|² =
2^{#S} ∫_V |f|²` — is **not** proved here.

## References

* Mathlib `MeasureTheory.volume_pi_pi`, `Real.volume_Ioo`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The volume of a coordinate box -/

theorem volume_coordBox (lo hi : Fin d → ℝ) :
    volume (coordBox lo hi) = ∏ i : Fin d, ENNReal.ofReal (hi i - lo i) := by
  rw [coordBox, volume_pi_pi]
  exact Finset.prod_congr rfl fun i _ => Real.volume_Ioo

theorem measurableSet_coordBox (lo hi : Fin d → ℝ) :
    MeasurableSet (coordBox lo hi) :=
  (isOpen_coordBox lo hi).measurableSet

theorem measurableSet_reflectedWindow (x : Vec d) (m k : ℤ) :
    MeasurableSet (reflectedWindow x m k) :=
  measurableSet_coordBox _ _

theorem volume_truncatedWindow_eq (x : Vec d) (m k : ℤ) :
    volume (truncatedWindow x m k) =
      ∏ i : Fin d, ENNReal.ofReal (windowHi x m k i - windowLo x m k i) := by
  rw [truncatedWindow_eq_coordBox, volume_coordBox]

theorem volume_reflectedWindow_eq (x : Vec d) (m k : ℤ) :
    volume (reflectedWindow x m k) =
      ∏ i : Fin d,
        ENNReal.ofReal (reflectedHi x m k i - reflectedLo x m k i) := by
  rw [reflectedWindow, volume_coordBox]

/-! ## 2. The two-sided volume comparison -/

theorem volume_truncatedWindow_le_volume_reflectedWindow (x : Vec d) (m k : ℤ) :
    volume (truncatedWindow x m k) ≤ volume (reflectedWindow x m k) :=
  measure_mono (truncatedWindow_subset_reflectedWindow x m k)

private theorem ofReal_edge_le {x : Vec d} {m k : ℤ} (hkm : k < m) (i : Fin d) :
    ENNReal.ofReal (reflectedHi x m k i - reflectedLo x m k i) ≤
      2 * ENNReal.ofReal (windowHi x m k i - windowLo x m k i) := by
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  by_cases hup : MeetsUpperFace x m k i
  · rw [reflectedHi_sub_reflectedLo_of_meetsUpperFace hkm hup,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), h2]
  · by_cases hlow : MeetsLowerFace x m k i
    · rw [reflectedHi_sub_reflectedLo_of_meetsLowerFace hup hlow,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), h2]
    · rw [reflectedHi_sub_reflectedLo_of_unmet hup hlow]
      calc ENNReal.ofReal (windowHi x m k i - windowLo x m k i)
          = 1 * ENNReal.ofReal (windowHi x m k i - windowLo x m k i) :=
            (one_mul _).symm
        _ ≤ 2 * ENNReal.ofReal (windowHi x m k i - windowLo x m k i) :=
            mul_le_mul' (by norm_num) (le_refl _)

/-- **The partial reflection multiplies the volume by at most `2^d`.**  The
exact factor is `2^{#S}`, `S` the met set; the doubling happens exactly in the
met coordinates (`reflectedHi_sub_reflectedLo_of_*`). -/
theorem volume_reflectedWindow_le (x : Vec d) {m k : ℤ} (hkm : k < m) :
    volume (reflectedWindow x m k) ≤
      2 ^ d * volume (truncatedWindow x m k) := by
  rw [volume_reflectedWindow_eq, volume_truncatedWindow_eq]
  calc ∏ i : Fin d, ENNReal.ofReal (reflectedHi x m k i - reflectedLo x m k i)
      ≤ ∏ i : Fin d,
          2 * ENNReal.ofReal (windowHi x m k i - windowLo x m k i) :=
        Finset.prod_le_prod fun i _ => ofReal_edge_le hkm i
    _ = (∏ _i : Fin d, (2 : ℝ≥0∞)) *
          ∏ i : Fin d, ENNReal.ofReal (windowHi x m k i - windowLo x m k i) :=
        Finset.prod_mul_distrib
    _ = 2 ^ d *
          ∏ i : Fin d, ENNReal.ofReal (windowHi x m k i - windowLo x m k i) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
