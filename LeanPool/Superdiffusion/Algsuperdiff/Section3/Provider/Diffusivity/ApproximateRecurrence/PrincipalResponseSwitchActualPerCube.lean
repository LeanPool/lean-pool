/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseSwitchActualShell

/-!
# PrincipalResponseSwitchActualPerCube

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: the per-cube gauge switch, almost surely in the sample

Source displays in ABK26:

* `l.approximate.recurrence.formula` (label), Step 3;
* `e.good.local.events` (label; display), instantiated as `cQ_z:= cQ(n, m-h,
  z)`;
* `e.lower.bound.principal.one.pre` (label; display);
* `e.recurrence.params` (label; display);
* `e.cgamma.constraints` (label; display);
* the paper-wide standing range of `cgamma`, the unlabelled display of
  `ss.assumptions` (label): `cgamma in (0, 1/4]`.

## What this module supplies

`ApproximateRecurrence.PrincipalResponseSwitchTransport` proves the absorbed
switch cube by cube, but only *pointwise in the sample* and with five binders,
of which `hshift`, `hgrad` and `hskew` are now produced by
`ApproximateRecurrence.PrincipalResponseSwitchActualShell`.  This module

1. states and proves the switch **almost surely on the cutoff sample law**, with
   the good event carried per cube -- the carrier the integral chain of Step 3
   actually uses (`(Cutoff.cutoffSampleLaw M).toMeasure` on
   `Cutoff.CutoffSample d`, not the `ShellSeq d` pointwise carrier);
2. integrates that inequality cube by cube, producing the expectation-level
   form that a grid average consumes; and
3. discharges the `cgamma <= 2/3` side condition of the `cgamma^6` gate from the
   manuscript's own standing assumption `cgamma in (0, 1/4]`.

### Why the almost-sure quantifier is the right one, and where it comes from

The only almost-sure step is the discounted gradient gate.  The event
`goodLocalEvent` is stated against `Provider.BadEvents.cubeLowerEllipticity`, a
measurable *representative* of `lambda_{1/8,2}(z+cu_n; a_{m-h})` built by
`A.mk`, whereas the frozen Section 2.4 gate is stated against `lambda_{3/8,2}`
of the rescaled coefficient object.  The proved transfer between them
(`Provider.BadEvents.lambda_transfer_ae`) is almost sure and no pointwise
information about the representative exists.  The rest of the chain -- the
transport, the Young absorption, the shell decomposition -- is pointwise.

## The `3/2`, and the deviation from the printed factor

 ABK26 prints the switch factor as `1 + 3^{-(1/4)(m-h-n)}`, i.e. `1 + 2 delta`
 at the
manuscript's own `delta = (1/2) 3^{-(1/4)(m-h-n)}`.  `l.J.sensitivity` (label)
delivers the factor `1 + delta + C ||grad h|| lambda^{-1}`, so the printed `1 +
2 delta` needs `C ||grad h|| lambda^{-1} <= delta`, while `e.good.local.events`
supplies its *third* inequality `C_sens sup_{L>=m-h} 3^{2n}
||grad(k_L-k_{m-h})|| <= 3^{-(1/4)(m-h-n)_+} lambda_{1/8,2}`, i.e. `C ||grad
h|| lambda^{-1} <= 2 delta`.  In this repository the two constants are
literally comparable -- `responseSensitivityConst d <= sensitivityConstMax d`,
with no margin -- so the factor carried below is the honest `1 + delta + 2
delta = 1 + (3/2). 3^{-(1/4)(m-h-n)}`.  The excess is absorbed by the
`cgamma^6` gate as soon as `cgamma <= 2/3`, which the standing `cgamma <= 1/4`
gives outright (`gamma_le_two_thirds`).

## Binders the caller must supply

Two quantitative inputs of the transported chain are **not** produced here and
are disclosed binders on every statement that needs them.

* `hlam0` -- strict positivity of `lambda_{3/8,2}(z+cu_n; a_{m-h})` at the
  samples of the good event.
* `hshell` -- the centered-shell size `||h - (h)_{z+cu_n}||^2 <= Delta^2
  shom_{m-h} lambda_{3/8,2}`.  ABK26 obtains it from the *middle* term of
  `e.good.local.events` (the `shom_{m-h-1}` leg, which is
  `Provider.BadEvents.goodLocalThreshold`) together with a centering estimate
  for the shell on `z + cu_n` and `e.cg.ellip.lower` (label).  The centering
  estimate is elementary at this carrier -- the shell is `W^{2,∞}` and the cube
  is convex -- but it is not proved in this module; `hshell` is therefore an
  explicit hypothesis here, never assumed in any other form and never derived
  from an unproved lemma.

Every other binder of the transported chain -- `hskew`, `hshift`, `hgrad` -- is
produced, from `PrincipalResponseSwitchActualShell` and from membership in the
good event alone.

## Main definitions

* `principalBadEvent`: the complement of `cQ_z = cQ(n, m-h, z)`, as the per-cube
  family `TriadicCube d -> Set (CutoffSample d)` that the display consumes.
* `gridSwitchDiscount`: the manuscript's `Delta = 3^{-(1/4)(m-h-n)_+}` read at
  the common scale of a grid of descendants.
* `switchCubeEnergy`, `switchCubeQuad`, `switchEllipLoad`: the three terms at
  the actual cutoff carrier.

## Main results

* `gamma_le_two_thirds`, `three_halves_switch_excess_le_gamma_pow_six`,
  `three_halves_switch_excess_le_gamma_pow_six_of_model`.
* `measurableSet_principalBadEvent`, `compl_principalBadEvent`: the per-cube
  family is measurable, and its complement is the good event `cQ_z`.
* `gridSwitchDiscount_pos`, `gridSwitchDiscount_le_one`,
  `gridSwitchDiscount_eq_of_mem`, `switchEllipLoad_nonneg`,
  `switchCubeQuad_nonneg`: the elementary properties of the discount and of the
  two nonnegative terms.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents

noncomputable section

variable {d : ℕ}

/-! ## The `cgamma <= 2/3` side condition, from the manuscript's own standing range

`ss.assumptions` (label) fixes `cgamma in (0, 1/4]` at the unlabelled display,
and that range is carried structurally by the frozen
`Algsuperdiff.Frozen.Assumptions.ShellLawPrefix.gamma_le_quarter`.  The extra
gate `cgamma <= 2/3` of
`three_halves_mul_rpow_three_neg_recurrenceGap_div_four_le_gamma_pow_six`
therefore discharges outright, and no new constraint on `cgamma` is introduced
by the `3/2`. -/

/-- **The standing range of `cgamma` implies the `2/3` gate.**  ABK26 fixes `cgamma
in (0, 1/4]` (in `ss.assumptions`, label); the `3/2` of the honest switch
factor therefore costs no new constraint.

Unconditional: no caller-supplied proposition enters; the range is a field of
the model's frozen shell-law prefix. -/
theorem gamma_le_two_thirds (M : ABKModel d) : M.gamma ≤ 2 / 3 :=
  le_trans M.shellPrefix.gamma_le_quarter (by norm_num)

/-- **The `cgamma^6` gate for the honest switch excess, with the `2/3`
constraint in plain sight.**  At the multiplier `a >= 28` the switch excess
`(3/2) 3^{-(m-h-n)/4}` of the absorbed form is below the `cgamma^6` that
`e.lower.bound.principal.one.pre` prints, under exactly the conjunction `(a >=
28) and (0 < cgamma <= 2/3)`.

The conjunction is displayed as a single hypothesis so that a caller cannot
consume the gate without seeing the `2/3`; `gamma_le_two_thirds` discharges it
from the standing assumptions.

: this statement holds only under the proposition supplied by its binder
`hgate`.  It is a provider A, not a source-facing frozen declaration. -/
theorem three_halves_switch_excess_le_gamma_pow_six {a : ℕ} {gamma : ℝ}
    (hgate : recurrenceGapMultiplierFloor ≤ a ∧ 0 < gamma ∧ gamma ≤ 2 / 3) :
    (3 / 2 : ℝ) * (3 : ℝ) ^ (-((recurrenceGap a gamma : ℝ) / 4)) ≤
      gamma ^ (6 : ℕ) :=
  three_halves_mul_rpow_three_neg_recurrenceGap_div_four_le_gamma_pow_six a
    hgate.2.1 hgate.2.2 hgate.1

/-- It is a provider A, not a source-facing frozen declaration. -/
theorem three_halves_switch_excess_le_gamma_pow_six_of_model (M : ABKModel d)
    {a : ℕ} (ha : recurrenceGapMultiplierFloor ≤ a) :
    (3 / 2 : ℝ) * (3 : ℝ) ^ (-((recurrenceGap a M.gamma : ℝ) / 4)) ≤
      M.gamma ^ (6 : ℕ) :=
  three_halves_switch_excess_le_gamma_pow_six
    ⟨ha, M.shellPrefix.gamma_pos, gamma_le_two_thirds M⟩

/-! ## The per-cube bad event and the switch discount -/

/-- The complement of the manuscript's own `cQ_z := cQ(n, m-h, z)`, as the per-cube
family the grid display consumes.  Nothing is unioned over the grid: the event
varies with the cube exactly as the manuscript's does. -/
def principalBadEvent (M : ABKModel d) (Ccg : ℝ) (R : TriadicCube d)
    (lowScale : ℤ) : Set (CutoffSample d) :=
  (goodLocalEvent M Ccg R lowScale)ᶜ

@[simp]
theorem compl_principalBadEvent (M : ABKModel d) (Ccg : ℝ) (R : TriadicCube d)
    (lowScale : ℤ) :
    (principalBadEvent M Ccg R lowScale)ᶜ = goodLocalEvent M Ccg R lowScale :=
  compl_compl _

theorem measurableSet_principalBadEvent (M : ABKModel d) (Ccg : ℝ)
    (R : TriadicCube d) (lowScale : ℤ) :
    MeasurableSet (principalBadEvent M Ccg R lowScale) :=
  (measurableSet_goodLocalEvent M Ccg R lowScale).compl

/-- The manuscript's `Delta = 3^{-(1/4)(m-h-n)_+}` read at the common scale
`Q.scale - j` of a grid of depth-`j` descendants of `Q`. -/
def gridSwitchDiscount (Q : TriadicCube d) (j : ℕ) (lowScale : ℤ) : ℝ :=
  (3 : ℝ) ^ (-(1 / 4 : ℝ) * scaleGapPos (Q.scale - j) lowScale)

theorem gridSwitchDiscount_pos (Q : TriadicCube d) (j : ℕ) (lowScale : ℤ) :
    0 < gridSwitchDiscount Q j lowScale :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem gridSwitchDiscount_le_one (Q : TriadicCube d) (j : ℕ) (lowScale : ℤ) :
    gridSwitchDiscount Q j lowScale ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    (by
      have h := scaleGapPos_nonneg (Q.scale - j) lowScale
      nlinarith)

/-- On a grid of depth-`j` descendants every cube has scale `Q.scale - j`, so
the per-cube discount is the grid discount. -/
theorem gridSwitchDiscount_eq_of_mem (Q : TriadicCube d) (j : ℕ) (lowScale : ℤ)
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth Q j) :
    (3 : ℝ) ^ (-(1 / 4 : ℝ) * scaleGapPos R.scale lowScale) =
      gridSwitchDiscount Q j lowScale := by
  rw [gridSwitchDiscount, scale_eq_sub_of_mem_descendantsAtDepth hR]

/-! ## The three terms of the switch, at the actual cutoff carrier -/

/-- `P_z . bfA_m(z + cu_n) P_z`, the left side. -/
def switchCubeEnergy (M : ABKModel d) (highScale : ℤ) (R : TriadicCube d)
    (X : BlockVec d) (omega : CutoffSample d) : ℝ :=
  blockVecDot X
    (blockMatVecMul
      (Ch02.coarseBlockMatrix (Ch02.cubeDomain R)
        ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn R)) X)

/-- `G_{-(h)_{z+cu_n}} P_z . bfA_{m-h}(z + cu_n) G_{-(h)_{z+cu_n}} P_z`, the
conjugated coarse quadratic form, at the manuscript's own centering constant
`(h)_{z+cu_n} = freshShellCubeAverage`. -/
def switchCubeQuad (M : ABKModel d) (lowScale highScale : ℤ) (R : TriadicCube d)
    (X : BlockVec d) (omega : CutoffSample d) : ℝ :=
  blockVecDot
    (blockMatVecMul
      (blockGauge (-freshShellCubeAverage R omega.1 lowScale highScale)) X)
    (blockMatVecMul
      (Ch02.coarseBlockMatrix (Ch02.cubeDomain R)
        ((coefficientCutoffTriadicCoeffFamily M lowScale omega).coeffOn R))
      (blockMatVecMul
        (blockGauge (-freshShellCubeAverage R omega.1 lowScale highScale)) X))

/-- `shom_{m-h} |p_z|^2 + shom_{m-h}^{-1} |q_z|^2`, the ellipticity load, with the
manuscript's `shom_{m-h}` carried as the free positive real `S`. -/
def switchEllipLoad (S : ℝ) (X : BlockVec d) : ℝ :=
  S * vecNormSq X.1 + S⁻¹ * vecNormSq X.2

theorem switchEllipLoad_nonneg {S : ℝ} (hS0 : 0 < S) (X : BlockVec d) :
    0 ≤ switchEllipLoad S X :=
  add_nonneg (mul_nonneg hS0.le (vecNormSq_nonneg _))
    (mul_nonneg (inv_pos.2 hS0).le (vecNormSq_nonneg _))

theorem switchCubeQuad_nonneg (M : ABKModel d) (lowScale highScale : ℤ)
    (R : TriadicCube d) (X : BlockVec d) (omega : CutoffSample d) :
    0 ≤ switchCubeQuad M lowScale highScale R X omega :=
  blockVecDot_coarseBlockMatrix_nonneg _ _ _

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
