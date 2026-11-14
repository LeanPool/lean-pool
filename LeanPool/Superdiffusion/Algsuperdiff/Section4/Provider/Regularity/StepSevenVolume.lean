/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenCaccVolume
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenSelectionPackage
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryCoveringVolume

/-!
# StepSevenVolume

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 7c: the `hvol` producer at the general triadic ratio

## The gap this module closes

The composition gaps open with `hvol`: `stepSevenGradientWithShom` takes
the volume cost

```text
  gradLoc  ≤  3^{(d/2)(n'-n)} · gradCore
```

as a hypothesis, and no producer exists at that literal shape.  The
obstruction is a side condition: the manuscript asserts the inclusion

> Since `(z + □_n) ∩ □_m ⊆ U_{n'-2}`, passing to the smaller set costs a volume
> factor `3^{(d/2)(n'-n)}`

and the inclusion of the two truncated windows at scales `n+1` and `n'-2` needs
`n + 1 ≤ n' - 2`, which appears in NO binder of the printed display and in no
binder of `stepSevenGradientWithShom`.

```text
  n + 3 ≤ n'      ↔      n + 1 ≤ n' - 2 ,
```

so the unstated hypothesis is free at the consumption site.  The arithmetic is
tight: the printed selection range `[n+3, m-3]` is what makes the Caccioppoli
core at `n'-2` contain the window at `n+1`; had the manuscript written `[n+2,
m-3]` the display would be false as printed.

## What is produced

* `truncatedWindow_succ_subset_caccCore` — the tex's own inclusion
  `(z+□_{n+1}) ∩ □_m ⊆ (z+□_{n'-2}) ∩ □_m`, with the side condition discharged.
* `three_rpow_le_volume_toReal_truncatedWindow` /
  `volume_toReal_truncatedWindow_le_rpow` — the two volume bounds (b) needs,
  the lower one from the inscribed well-placed cube and the upper one from
  `truncatedWindow_subset_translate`.  The lower bound is where the shift `n+1
  ↦ n` happens: the window at scale `k` contains a full cube of scale `k-1`, so
  the window at `n+1` has volume at least `3^{dn}` — the printed `3^{dn}`
  denominator, not an approximation of it.
* `stepSevenVolumeRatio_le` — the general-ratio producer on the two masses.

The masses `IS ≤ IT` remain the caller's: `ν^{1/2}‖∇u‖_{L²(S)}` is read as the
symmetric coefficient energy, and its monotonicity in the domain is an integral
monotonicity, not an estimate.  No new estimate is derived here; every step is
a proved atom or `Real.rpow` arithmetic.

## References

* ABK26, `t.regularity` Step 7c; Step 7a.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The side condition, and the inclusion it unlocks -/

/-- **The tex's own inclusion** `(z+□_{n+1}) ∩ □_m ⊆ (z+□_{n'-2}) ∩ □_m`, at the
derived side condition. -/
theorem truncatedWindow_succ_subset_caccCore (z : Vec d) (m : ℤ) {n n' : ℤ}
    (hgap : n + 1 ≤ n' - 2) :
    truncatedWindow z m (n + 1) ⊆ truncatedWindow z m (n' - 2) :=
  truncatedWindow_mono z m hgap

/-! ## 2. The two volume bounds -/

/-- `3^{d j} = (3^j)^d` in the `rpow` spelling the volume comparison uses. -/
theorem rpow_three_dim_mul (d : ℕ) (j : ℤ) :
    Real.rpow (3 : ℝ) ((d : ℝ) * (j : ℝ)) = ((3 : ℝ) ^ j) ^ d := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have hj : Real.rpow (3 : ℝ) ((j : ℤ) : ℝ) = (3 : ℝ) ^ j := Real.rpow_intCast 3 j
  have hcomm : (d : ℝ) * (j : ℝ) = (j : ℝ) * (d : ℝ) := by ring
  have hsplit : Real.rpow (3 : ℝ) ((j : ℝ) * (d : ℝ)) =
      Real.rpow (Real.rpow (3 : ℝ) (j : ℝ)) (d : ℝ) := Real.rpow_mul h3 _ _
  have hnat : Real.rpow ((3 : ℝ) ^ j) ((d : ℕ) : ℝ) = ((3 : ℝ) ^ j) ^ d :=
    Real.rpow_natCast _ d
  rw [hcomm, hsplit, hj, hnat]

/-- **The window's volume lower bound** (lower half).  For `z ∈ □_m` and `k -
1 ≤ m`, the truncated window `(z+□_k) ∩ □_m` contains a full translate of
`□_{k-1}` — the inscribed well-placed cube — so its volume is at least
`3^{d(k-1)}`.  At `k = n+1` this is the printed `3^{dn}`. -/
theorem three_rpow_le_volume_toReal_truncatedWindow (d : ℕ) {m k : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) :
    Real.rpow (3 : ℝ) ((d : ℝ) * (((k - 1 : ℤ)) : ℝ)) ≤
      (volume (truncatedWindow z m k)).toReal := by
  have hsub := image_add_wellPlacedCentre_subset_truncatedWindow (j := k) z hz hkm
  have hle : volume ((fun y => wellPlacedCentre z m (k - 1) + y) ''
      openCubeSet (originCube d (k - 1))) ≤ volume (truncatedWindow z m k) :=
    measure_mono hsub
  have htop : volume (truncatedWindow z m k) ≠ ⊤ :=
    ne_of_lt (volume_truncatedWindow_lt_top z m k)
  have hreal : ((3 : ℝ) ^ (k - 1)) ^ d ≤ (volume (truncatedWindow z m k)).toReal := by
    rw [← volume_toReal_openCubeSet_originCube d (k - 1),
      ← volume_image_add (wellPlacedCentre z m (k - 1)) (openCubeSet (originCube d (k - 1)))]
    exact ENNReal.toReal_mono htop hle
  rw [rpow_three_dim_mul d (k - 1)]
  exact hreal

/-- **The window's volume upper bound** ((b), upper half).  The truncated window
sits inside the full translate `z + □_j`, whose volume is `3^{dj}`. -/
theorem volume_toReal_truncatedWindow_le_rpow (d : ℕ) (z : Vec d) (m j : ℤ) :
    (volume (truncatedWindow z m j)).toReal ≤ Real.rpow (3 : ℝ) ((d : ℝ) * (j : ℝ)) := by
  have hsub := truncatedWindow_subset_translate z m j
  have hle : volume (truncatedWindow z m j) ≤
      volume ((fun y => z + y) '' openCubeSet (originCube d j)) := measure_mono hsub
  have htop : volume ((fun y => z + y) '' openCubeSet (originCube d j)) ≠ ⊤ := by
    rw [volume_image_add]
    exact volume_openCubeSet_originCube_ne_top d j
  have hreal : (volume (truncatedWindow z m j)).toReal ≤ ((3 : ℝ) ^ j) ^ d := by
    rw [← volume_toReal_openCubeSet_originCube d j,
      ← volume_image_add z (openCubeSet (originCube d j))]
    exact ENNReal.toReal_mono htop hle
  rw [rpow_three_dim_mul d j]
  exact hreal

/-- The volume upper bound, moved from the core scale `n'-2` up to the printed
`n'`.
-/
theorem volume_toReal_caccCore_le_rpow (d : ℕ) (z : Vec d) (m n' : ℤ) :
    (volume (truncatedWindow z m (n' - 2))).toReal ≤
      Real.rpow (3 : ℝ) ((d : ℝ) * (n' : ℝ)) := by
  refine le_trans (volume_toReal_truncatedWindow_le_rpow d z m (n' - 2)) ?_
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hcast : (((n' - 2 : ℤ)) : ℝ) = (n' : ℝ) - 2 := by push_cast; ring
  rw [hcast]
  exact mul_le_mul_of_nonneg_left (by linarith only [] : (n' : ℝ) - 2 ≤ (n' : ℝ)) hd

/-! ## 3. The general-ratio producer -/

/-- **`hvol` at the general triadic ratio** ((b)).

For `z ∈ □_m`, `n ≤ m`, and any two masses with `IS ≤ IT` carried by the window
`(z+□_{n+1}) ∩ □_m` and the Caccioppoli core `(z+□_{n'-2}) ∩ □_m`, the
volume-normalized square roots compare at the printed factor:

```text
  √(IS/|S|)  ≤  3^{(d/2)(n'-n)} · √(IT/|T|) .
```

This is `normalizedSqrt_le_volumeRatio_mul` composed with
`sqrt_volumeRatio_le_rpow_three` at the two window volume bounds above — the
two halves, now with both of them supplied rather than assumed.  The mass
monotonicity `IS ≤ IT` is the caller's integral comparison and is the only
input. -/
theorem stepSevenVolumeRatio_le (d : ℕ) {m n n' : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) (hnm : n ≤ m) {IS IT : ℝ}
    (hmono : IS ≤ IT) :
    Real.sqrt (IS / (volume (truncatedWindow z m (n + 1))).toReal) ≤
      Real.rpow (3 : ℝ) (((d : ℝ) / 2) * ((n' : ℝ) - (n : ℝ))) *
        Real.sqrt (IT / (volume (truncatedWindow z m (n' - 2))).toReal) := by
  have hSfin : volume (truncatedWindow z m (n + 1)) ≠ ⊤ :=
    ne_of_lt (volume_truncatedWindow_lt_top z m (n + 1))
  have hTfin : volume (truncatedWindow z m (n' - 2)) ≠ ⊤ :=
    ne_of_lt (volume_truncatedWindow_lt_top z m (n' - 2))
  have hSpos : 0 < (volume (truncatedWindow z m (n + 1))).toReal :=
    ENNReal.toReal_pos (ne_of_gt (volume_truncatedWindow_pos (n + 1) hz)) hSfin
  have hTpos : 0 < (volume (truncatedWindow z m (n' - 2))).toReal :=
    ENNReal.toReal_pos (ne_of_gt (volume_truncatedWindow_pos (n' - 2) hz)) hTfin
  have hkm : (n + 1) - 1 ≤ m := by linarith only [hnm]
  have hlowRaw := three_rpow_le_volume_toReal_truncatedWindow d (k := n + 1) hz hkm
  have hcast : ((((n + 1) - 1 : ℤ)) : ℝ) = (n : ℝ) := by push_cast; ring
  rw [hcast] at hlowRaw
  have hup := volume_toReal_caccCore_le_rpow d z m n'
  have hratio := sqrt_volumeRatio_le_rpow_three d (n := n) (n' := n') hSpos hlowRaw hup
  have hmain := normalizedSqrt_le_volumeRatio_mul hSpos hTpos hmono
  refine le_trans hmain ?_
  exact mul_le_mul_of_nonneg_right hratio (Real.sqrt_nonneg _)

end

end Algsuperdiff.Section4.Provider.Regularity
