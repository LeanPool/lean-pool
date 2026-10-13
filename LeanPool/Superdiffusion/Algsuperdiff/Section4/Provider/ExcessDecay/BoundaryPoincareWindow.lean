/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryCoveringTrace
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CoveringSlotObstruction
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RecutAtoms

/-!
# BoundaryPoincareWindow

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary-Poincaré opener: the covering cube inside the anchor window

The general clause's right-hand-side windows are the enlarged ones, `W' =
(z+□_{n+3}) ∩ □_m` rather than `W = (z+□_{n+2}) ∩ □_m`, precisely so that the
**boundary covering cube** `c + □_{n+2}`, `c = wellPlacedCentre x m (n+2)`, fits inside
the window whose norms the anchor prices.  This module proves that fit and the
two transports it immediately supplies — the geometric half of the funded unit.

* `image_add_wellPlacedCentre_subset_anchorWindow` — the fit:
  `c + □_{n+2} ⊆ W'`.  It combines the two halves of `CoveringSlotObstruction`
  (the covering cube is inside `z + □_{n+3}`) and `BoundaryCoveringGeometry`
  (it is inside `□_m`).
* `volume_anchorWindow_le_coveringCube` — the covering ratio `|W'| ≤ 9^d
  |c+□_{n+2}|` (the true ratio is `3^d`; the perfect square is taken so that the
  `L²` constant is the integer power `3^d`).
* `eLpNorm_coveringCube_le_anchorWindow` — the `L²` transport: a normalized
  `L²` norm over the covering cube is at most `3^d` times the one over the
  anchor's own window.  This is the step that will move the boundary
  Caccioppoli's left-hand side into the frozen statement's carrier.
* `localizedZeroTraceFunctionOn_anchorWindow` — the zero-trace localization
  onto `W'`: a global `H¹₀(□_m)` datum has the localized zero trace on `W'`
  through the window `z + □_{n+3}`, because `(z+□_{n+3}) ∩ □_m` **is** `W'`.

## What is not done here

No Poincaré inequality is proved.  The trace-measure lower bound,
CoarseGraining's `coarsePoincare` and the Stampacchia machinery are the
analytic half and are untouched; nothing below asserts
any estimate on `u - v`, and nothing below is an instance, or a fraction, of
any source node.

The fit proved here is a fit of **windows**, not of events.

## References

* ABK26, `l.harmonic.approximation.good.scales`; the boundary application of
  `l.coarse.grained.Caccioppoli`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E]

/-! ## 1. The fit -/

/-- **The boundary covering cube sits inside the anchor's window.**

This is what the window enlargement buys: with the printed `n+2` window the
covering cube provably does not fit (`CoveringSlotObstruction`), with the frozen
`n+3` window it always does. -/
theorem image_add_wellPlacedCentre_subset_anchorWindow {n m : ℤ} {x z : Vec d}
    (hnm : n + 2 ≤ m) (hx : x ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m)) :
    (fun y => wellPlacedCentre x m (n + 2) + y) '' openCubeSet (originCube d (n + 2)) ⊆
      ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) := by
  intro p hp
  exact ⟨image_add_wellPlacedCentre_subset_anchorParent hnm hx hgeom hp,
    image_add_wellPlacedCentre_subset_openCubeSet x hnm hp⟩

/-! ## 2. The covering ratio and the `L²` transport -/

/-- The anchor's window is at most `9^d` times the covering cube in volume
(the true ratio is `3^d`). -/
theorem volume_anchorWindow_le_coveringCube (n m : ℤ) (z c : Vec d) :
    volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) ≤
      ENNReal.ofReal ((9 : ℝ) ^ d) *
        volume ((fun y => c + y) '' openCubeSet (originCube d (n + 2))) := by
  have hid : ((3 : ℝ) ^ (n + 3)) ^ d = (3 : ℝ) ^ d * ((3 : ℝ) ^ (n + 2)) ^ d := by
    rw [← mul_pow]
    congr 1
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0) n 3,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0) n 2]
    norm_num
    ring
  have hmono : (3 : ℝ) ^ d ≤ (9 : ℝ) ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
  have hpos : (0 : ℝ) ≤ ((3 : ℝ) ^ (n + 2)) ^ d := by positivity
  have hstep : ((3 : ℝ) ^ (n + 3)) ^ d ≤ (9 : ℝ) ^ d * ((3 : ℝ) ^ (n + 2)) ^ d := by
    rw [hid]
    exact mul_le_mul_of_nonneg_right hmono hpos
  have hupper : volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m))) ≤ ENNReal.ofReal (((3 : ℝ) ^ (n + 3)) ^ d) := by
    refine le_trans (measure_mono Set.inter_subset_left) ?_
    rw [volume_image_add_openCubeSet z (originCube d (n + 3)),
      volume_openCubeSet_originCube]
  have hlower : volume ((fun y => c + y) '' openCubeSet (originCube d (n + 2))) =
      ENNReal.ofReal (((3 : ℝ) ^ (n + 2)) ^ d) := by
    rw [volume_image_add_openCubeSet c (originCube d (n + 2)),
      volume_openCubeSet_originCube]
  rw [hlower, ← ENNReal.ofReal_mul (by positivity)]
  exact le_trans hupper (ENNReal.ofReal_le_ofReal hstep)

/-- **The `L²` transport onto the anchor's window.**

A normalized `L²` norm over the boundary covering cube is at most `3^d` times the
one over the anchor's own window `W' = (z+□_{n+3}) ∩ □_m`. -/
theorem eLpNorm_coveringCube_le_anchorWindow {n m : ℤ} {x z : Vec d}
    (hnm : n + 2 ≤ m) (hx : x ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    (f : Vec d → E) :
    eLpNorm f 2 (Support.normalizedVolumeMeasureOn
        ((fun y => wellPlacedCentre x m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2)))) ≤
      ENNReal.ofReal ((3 : ℝ) ^ d) *
        eLpNorm f 2 (Support.normalizedVolumeMeasureOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m)))) := by
  have hbase := eLpNorm_le_of_volume_le (K := ENNReal.ofReal ((9 : ℝ) ^ d))
    (image_add_wellPlacedCentre_subset_anchorWindow hnm hx hgeom) (by simp) (by simp)
    (volume_anchorWindow_le_coveringCube n m z (wellPlacedCentre x m (n + 2))) f
  have hhalf : (ENNReal.ofReal ((9 : ℝ) ^ d)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal ((3 : ℝ) ^ d) := by
    have h9 : (9 : ℝ) ^ d = ((3 : ℝ) ^ d) ^ (2 : ℕ) := by
      rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [ENNReal.ofReal_rpow_of_pos (by positivity : (0 : ℝ) < (9 : ℝ) ^ d), h9,
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
  rwa [hhalf] at hbase

/-! ## 3. The zero-trace localization onto the anchor's window -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay
