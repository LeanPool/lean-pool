/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.OscillationProbability
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.DensityBound

/-!
# BadClusterGates

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Discharging the percolation gates from the bad-cluster admissibility

ABK26's Lemma `l.percolation.bad.clusters` applies the abstract percolation
lemma `l.percolation.bound.general` to the bad events at the rate

```
T^2 = c_{e.BoscL.prob} E^{-2} gamma^{-1} ,
```

under the admissibility `e.percolation.admissibility.bad.clusters`

```
E >= exp(C sigma^{-1}) or C c_star^{-1}      and      gamma <= E^{-5} .
```

This module carries out the arithmetic that the manuscript summarises as *"the
admissibility condition ensures that `T >= C exp(C(1-sigma)^{-1})`"*, in the two
places where the formalized percolation layer needs it.

## The two consumption watches

* **.**  The printed threshold `exp(C(1-b)^{-1}) <= (8d)^{-1}T^2` of
  `e.diameter.bound` is insufficient and the printed conclusion is falsified in
  the regime `a = b -> 0`; the proved `measure_crossingEvent₂_le_exp`
  (`DiameterTwo.lean`) carries instead the gate `16 d exp(40 (1-b)^{-1}) <= T^2
  b` together with `b <= a`.  `BadClusterRate.percolationGate_of_admissible'`
  discharges that gate at `b = 1 - sigma` — the value used in the manuscript's
  own proof — from the printed admissibility at the explicit dimension-only
  constant `badClustersConst d`.

* ** /.**  The printed `for every t > 0` of `e.density.bound` is false as
  printed; the proved `measureReal_densityAverage_gt_le_exp` carries the
  corrected range `C(a^{-1}+(d-a)^{-1}) T^{-1} 3^{-am/2} <= t`.
  `densityThreshold_of_le` below verifies that range at the manuscript's own
  data `a = 3/2`, `m = h`, `t = 3^{-h/2}`, and
  `BadClusterRate.densityAmplitude_le_sqrt_siteRateSq` supplies the
  dimension-only lower bound on `T` that it needs.
  `one_le_densityExponent` is the matching verification that the resulting
  exponent dominates the printed `3^{h/2}`.

Everything here is pure arithmetic: no probability, no measurability, and no
hypothesis beyond the printed admissibility (with `E^{-2} <= c_star`, which is
`E >= C c_star^{-1}` at `C >= 1` together with `E >= 1`).

## References

* ABK26, `l.percolation.bad.clusters` (statement and proof).
* ABK26, `l.percolation.bound.general`.
-/

namespace Algsuperdiff.Section3.Provider.Percolation

open HCPolySupport
open Algsuperdiff.Section3.Provider.BadEvents

noncomputable section

/-! ## The dimension-only constants -/

/-- The amplitude of the density threshold at the manuscript's `a = 3/2`. -/
def densityAmplitude (d : ℕ) : ℝ :=
  densityBoundConst d * (((3 : ℝ) / 2)⁻¹ + ((d : ℝ) - 3 / 2)⁻¹)

/-- The reciprocal of the coefficient by which the exponent exceeds the printed
`3^{h/2}` at the manuscript's `a = 3/2`, `t = 3^{-h/2}`. -/
def densityExponentAmplitude (d : ℕ) : ℝ :=
  (densityBoundExpConst d * ((3 : ℝ) / 2) ^ 2 * ((d : ℝ) - 3 / 2) ^ 2)⁻¹


/-! ## The rate supplied by the admissibility -/


/-! ## Watch 1: the percolation gate -/


/-! ## Watch 2: the density threshold -/

theorem densityAmplitude_pos {d : ℕ} (hd : 2 ≤ d) : 0 < densityAmplitude d := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hda : (0 : ℝ) < (d : ℝ) - 3 / 2 := by linarith
  have hsum : (0 : ℝ) < ((3 : ℝ) / 2)⁻¹ + ((d : ℝ) - 3 / 2)⁻¹ :=
    add_pos (by norm_num) (inv_pos.2 hda)
  exact mul_pos (densityBoundConst_pos d) hsum

/-- **The corrected range is met at the manuscript's own data.**  At
`a = 3/2`, `m = h`, `t = 3^{-h/2}`, the corrected range of
`measureReal_densityAverage_gt_le_exp`,

```
densityBoundConst d (a^{-1} + (d-a)^{-1}) T^{-1} (3^{-a/2})^m <= t ,
```

holds for every `h` as soon as `T` exceeds the dimension-only amplitude
`densityAmplitude d`.  The whole `h`-dependence is the surplus
`3^{-3h/4} <= 3^{-h/2}`.  The threshold on `T` is supplied by
`BadClusterRate.densityAmplitude_le_sqrt_siteRateSq`. -/
theorem densityThreshold_of_le {d : ℕ} (h : ℕ) {T : ℝ} (hd : 2 ≤ d)
    (hK : densityAmplitude d ≤ T) :
    densityBoundConst d * (((3 : ℝ) / 2)⁻¹ + ((d : ℝ) - 3 / 2)⁻¹) * T⁻¹ *
        ((3 : ℝ) ^ (-((3 : ℝ) / 2) / 2)) ^ h ≤
      (3 : ℝ) ^ (-(h : ℝ) / 2) := by
  have hApos : 0 < densityAmplitude d := densityAmplitude_pos hd
  have hT0 : 0 < T := lt_of_lt_of_le hApos hK
  have hratio : densityAmplitude d * T⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hT0]
    exact hK
  have hXpos : (0 : ℝ) < ((3 : ℝ) ^ (-((3 : ℝ) / 2) / 2)) ^ h := by positivity
  have hpow : ((3 : ℝ) ^ (-((3 : ℝ) / 2) / 2)) ^ h =
      (3 : ℝ) ^ (-((3 : ℝ) / 2) / 2 * (h : ℝ)) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-((3 : ℝ) / 2) / 2)) h,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hmono : (3 : ℝ) ^ (-((3 : ℝ) / 2) / 2 * (h : ℝ)) ≤
      (3 : ℝ) ^ (-(h : ℝ) / 2) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hh : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
    linarith
  calc densityBoundConst d * (((3 : ℝ) / 2)⁻¹ + ((d : ℝ) - 3 / 2)⁻¹) * T⁻¹ *
        ((3 : ℝ) ^ (-((3 : ℝ) / 2) / 2)) ^ h
      = densityAmplitude d * T⁻¹ * ((3 : ℝ) ^ (-((3 : ℝ) / 2) / 2)) ^ h := by
        rw [densityAmplitude]
    _ ≤ 1 * ((3 : ℝ) ^ (-((3 : ℝ) / 2) / 2)) ^ h :=
        mul_le_mul_of_nonneg_right hratio hXpos.le
    _ = ((3 : ℝ) ^ (-((3 : ℝ) / 2) / 2)) ^ h := one_mul _
    _ ≤ _ := by rw [hpow]; exact hmono

/-- The matching verification that the exponent dominates the printed `3^{h/2}`: at
`a = 3/2`, `t = 3^{-h/2}` the coefficient of `3^{h/2}` in the exponent of
`measureReal_densityAverage_gt_le_exp` is at least one as soon as `T^2` exceeds
the dimension-only amplitude `densityExponentAmplitude d`. -/
theorem one_le_densityExponent {d : ℕ} {T : ℝ} (hd : 2 ≤ d)
    (hA : densityExponentAmplitude d ≤ T ^ 2) :
    1 ≤ densityBoundExpConst d * ((3 : ℝ) / 2) ^ 2 * ((d : ℝ) - 3 / 2) ^ 2 * T ^ 2 := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hda : (0 : ℝ) < (d : ℝ) - 3 / 2 := by linarith
  have h1 : 0 < densityBoundExpConst d := densityBoundExpConst_pos (by omega)
  have hB : (0 : ℝ) < densityBoundExpConst d * ((3 : ℝ) / 2) ^ 2 *
      ((d : ℝ) - 3 / 2) ^ 2 :=
    mul_pos (mul_pos h1 (by norm_num)) (pow_pos hda 2)
  rw [densityExponentAmplitude, inv_le_iff_one_le_mul₀ hB] at hA
  linarith

end

end Algsuperdiff.Section3.Provider.Percolation
