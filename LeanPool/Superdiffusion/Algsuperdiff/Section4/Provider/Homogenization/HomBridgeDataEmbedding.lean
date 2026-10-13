/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourSeminormComparisons

/-!
# HomBridgeDataEmbedding

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 2: the data embedding `C^{0,1/2} ↪ H^s(□_m)`

## The target

Step 2 of Theorem B prices the Step-2 solution by its data.  The datum enters
Theorem C through the Besov leg `3^{sm} [g]_{H^s(□_m)}`, while the §4.5
normalization supplies only the HÖLDER bound

```
  [g]_{C^{0,1/2}(□_m)} ≤ 1        and       ‖∇h‖_{C^{0,1/2}(□_m)} ≤ 1.
```

The missing conversion — the obstruction (4) — is

```
  [g]_{C^{0,1/2}(□_m)} ≤ K   ⟹   3^{sm} [g]_{H^s(□_m)} ≤ C(d,s) K 3^{m/2}
```

for `0 < s < 1/2`, together with the identical statement for `∇h`.  This module
gives it.

## Most of the engine is already available

The conversion is not new analysis.  Both the Gagliardo engine and its `□_m`
instance are already in this repository:

* `Provider.Regularity.normalizedGagliardoESeminormOn_le_of_holderHalf`
  (`HolderGagliardoEmbedding.lean`) — the window-free atom
  `[g]_{H^s(A)} ≤ K (C_rad(d,β) · R^d · R^{-β})^{1/2}`, `β = d + 2s - 1`, for
  any window `A` of sup-diameter `≤ R`, at the very carriers this repository uses;
* `Provider.Regularity.radialKernelConst_holderGagliardoBeta_le` /
  `stepFourGagliardoConst_le` (`HolderGagliardoRangeGuard.lean`) — the constant
  `C_rad(d, d+2s-1) ≤ 2^{d+1} 3^d (1-2s)^{-1}`, i.e. the correction's
  `(1-2s)^{-1/2}`;
* `Provider.Regularity.three_rpow_mul_normalizedGagliardoESeminormOn_cube_le`
  (`StepFourSeminormComparisons.lean`) — **the target display itself**, at the
  window `openCubeSet (originCube d m)`:
  `3^{ms}[g]_{H^s(□_m)} ≤ K · C_{S4.4}(d,s) · 3^{m/2}`, generic in `E`, so the
  `g` leg and the `∇h` leg are ONE declaration.

Nothing here re-derives any of that.  The honest residue, and the whole content
of this module, is:

1. `homDataConst` + `stepFourGagliardoConst_le_homDataConst` — the range
   guard bounds the constant only in its `s`-dependent form
   `(2^{d+1} 3^d / (1-2s))^{1/2}`, which blows up as `s → 1/2`.  §4.5 runs at
   `s = |log γ|⁻¹`, which is `≤ 1/4` but never a fixed numeral, so what is
   needed is one `γ`-free constant valid on the whole RANGE `0 < s ≤ 1/4`; it
   is supplied here.
2. `cubeSet_subset_ball_of_mem` — the window geometry a general-cube reading
   needs.  Step 2b's windows are `z + □_j` for `z ∈ 3^j ℤ^d ∩ □_m`, i.e.
   arbitrary triadic cubes, while the Support layer's correspondence anchor
   is stated at the HALF-OPEN
   realization; it is that realization which makes the ball radius exactly the
   side length `3^m` (each coordinate inequality is strict), with no
   dimensional loss.

## The constant

`stepFourGagliardoConst d s = C_rad(d, d+2s-1)^{1/2}` carries `(1-2s)^{-1/2}`
and therefore is NOT a constant as `s → 1/2`.  The §4.5 instance is protected by
's gate `s = |log γ|⁻¹ ≤ 1/4` (carried by `HomStepEnvelope`'s
`homS_le_quarter`), at which `1 - 2s ≥ 1/2` and the constant collapses to the
genuinely `γ`-free `homDataConst d = (2^{d+2} 3^d)^{1/2}`.  It is that pinned
`C(d)` form which is stated here.
-/

open HCPolySupport MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Provider.Regularity

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 1. The cube as a sup-ball about each of its points -/

theorem cubeScaleFactor_pos (Q : TriadicCube d) : 0 < cubeScaleFactor Q := by
  rw [cubeScaleFactor]
  exact zpow_pos (by norm_num) _

/-- **A triadic cube of scale `m` sits in the open sup-ball of radius `3^m`
about any of its own points.**

The half-open realization `cubeSet` gives `|x i - y i| < 3^m` STRICTLY in every
coordinate, and the ambient metric on `Vec d = Fin d → ℝ` is the supremum
metric, so the radius is the side length itself. -/
theorem cubeSet_subset_ball_of_mem {Q : TriadicCube d} {x : Vec d}
    (hx : x ∈ cubeSet Q) : cubeSet Q ⊆ Metric.ball x (cubeScaleFactor Q) := by
  intro y hy
  have hpos : 0 < cubeScaleFactor Q := cubeScaleFactor_pos Q
  rw [Metric.mem_ball]
  refine (dist_pi_lt_iff hpos).2 fun i => ?_
  have hxi := hx i
  have hyi := hy i
  have hid : (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q) -
      (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q) = cubeScaleFactor Q := by
    ring
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith only [hxi.1, hxi.2, hyi.1, hyi.2, hid]
  · linarith only [hxi.1, hxi.2, hyi.1, hyi.2, hid]

/-! ## 4. The pinned constant -/

/-- `C_data(d) = (2^{d+2} 3^d)^{1/2}`: the `γ`-free constant of the data
embedding at the §4.5 gate `s ≤ 1/4`. -/
def homDataConst (d : ℕ) : ℝ := Real.sqrt ((2 : ℝ) ^ (d + 2) * (3 : ℝ) ^ d)

/-- **The `s`-dependence removed, under the explicit gate.**

For `0 < s ≤ 1/4` we have `1 - 2s ≥ 1/2`, so the `(1-2s)^{-1/2}` is at most
`2^{1/2}` and `C_{S4.4}(d,s) ≤ C_data(d)`.  The correction is respected: the
absorption happens ONLY under the displayed hypothesis `s ≤ 1/4`. -/
theorem stepFourGagliardoConst_le_homDataConst {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 4) :
    stepFourGagliardoConst d s ≤ homDataConst d := by
  have hlt : s < 1 / 2 := by linarith only [hs]
  have hgap : (1 : ℝ) / 2 ≤ 1 - 2 * s := by linarith only [hs]
  have hpos : (0 : ℝ) < 1 - 2 * s := by linarith only [hgap]
  have hnum : (0 : ℝ) < (2 : ℝ) ^ (d + 1) * (3 : ℝ) ^ d :=
    mul_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)
  have hquot : (2 : ℝ) ^ (d + 1) * (3 : ℝ) ^ d / (1 - 2 * s) ≤
      (2 : ℝ) ^ (d + 2) * (3 : ℝ) ^ d := by
    rw [div_le_iff₀ hpos]
    have hexp : (2 : ℝ) ^ (d + 2) * (3 : ℝ) ^ d =
        2 * ((2 : ℝ) ^ (d + 1) * (3 : ℝ) ^ d) := by ring
    rw [hexp]
    have hscale : 2 * ((2 : ℝ) ^ (d + 1) * (3 : ℝ) ^ d) * (1 / 2) ≤
        2 * ((2 : ℝ) ^ (d + 1) * (3 : ℝ) ^ d) * (1 - 2 * s) :=
      mul_le_mul_of_nonneg_left hgap (by linarith only [hnum])
    linarith only [hscale]
  exact (stepFourGagliardoConst_le hs0 hlt).trans (Real.sqrt_le_sqrt hquot)

end

end Algsuperdiff.Section4.Provider.Homogenization
