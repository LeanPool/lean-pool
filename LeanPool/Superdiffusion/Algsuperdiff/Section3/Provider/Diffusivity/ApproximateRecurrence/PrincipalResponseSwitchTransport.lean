/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseSensitivitySwitch
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LambdaTransfer
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationParams
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz.UnitCube
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.Dilation

/-!
# PrincipalResponseSwitchTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: the gauge switch of ABK26 Step 3, transported to `z + cu_n`

Source displays in ABK26:

* `l.approximate.recurrence.formula` (label), Step 3;
* the gauge-switch chain of Step 3, whose closing line is sub-step (i) of
  `e.lower.bound.principal.one.pre` (label);
* `l.J.sensitivity` (label), applied at `delta := (1/2) 3^{-(1/4)(m-h-n)}`;
* `e.J.by.means.of.bfA` (label);
* `e.good.local.events` (label; display).

## What this module supplies

`ApproximateRecurrence.PrincipalResponseSensitivitySwitch` proves the chain at
the **unit cube** `square_0`, because that is the carrier of the frozen
`Algsuperdiff.Frozen.Section24.responseJ_sensitivity`.  Its own module
docstring names two gaps.  This module closes the first of them: the transport
of that chain to the manuscript's localization cube `z + cu_n`.

The transport is an *equality* transport -- no constant is created or lost --
and it is assembled from the same two CoarseGraining interfaces that
`Provider.BadEvents.LambdaCovariance` and `Provider.Multiscale.JCarrierRescale`
already use for `lambda_{s,q}` and for `J`:

* **dilation**: `Ch02.coarseBlockMatrix_dilate` at
  `dilateCube (-m) (originCube d m) = originCube d 0`;
* **translation**: the proved one-cube covariance
  `Provider.BadEvents.coarseBlockMatrix_cutoff_translateCutoffSample`, read
  through `Ch02.coarseBlockMatrix_eq_ofAEEq` so that the carrier is the
  repository's own `Cutoff.coefficientCutoffTriadicCoeffFamily`.

The resulting identity `coarseBlockMatrix_unitRescaledCutoffCoeff` is the exact
analogue, for the doubled coarse block matrix `bfA`, of the proved
`unitCubeLambda_unitRescaledCutoffCoeff` (for `lambda`) and
`responseJ_unitRescaledCutoffCoeff` (for `J`).

The second gap it names -- absorption of the Young remainder using the size of
the centered shell and of `lambda_{3/8,2}` on the good event -- is performed in
the second half of this module, and the result is stated cube by cube, with the
good event carried as a **per-cube family**.

Nothing here asserts that the principal-response step of
`l.approximate.recurrence.formula`, its sub-step (i), or `e.lower.bound.principal.one.pre`
is closed: the composed statement is one sub-step of those displays and is itself
conditional on the two binders described under "Binders the caller must supply" below.

## The `3/2`, and why the printed `1 + 3^{-(1/4)(m-h-n)}` is optimistic

ABK26 prints the switch factor `1 + 3^{-(1/4)(m-h-n)}`, i.e. `1 + 2 delta` at
the manuscript's own `delta = (1/2) 3^{-(1/4)(m-h-n)}`.  Obtaining it needs `C
|grad h| lambda^{-1} <= delta`.  What the event `e.good.local.events` supplies
is its *second* inequality,

```
C_sens sup_{L >= n} 3^{2m} ||grad(k_L - k_n)||   <=   3^{-(1/4)(n-m)_+} lambda_{1/8,2} ,
```

i.e. `C |grad h| lambda^{-1} <= Delta = 2 delta`, because the factor `1/2` of
the display sits in the *middle* term (against `shom_{n-1}`) and not in the
`lambda` bound.  The honest switch factor is therefore `1 + delta + Delta = 1 +
(3/2) Delta`, which is what is carried below.  The discrepancy is a constant
factor `3/2` in a quantity the manuscript immediately relaxes to `cgamma^6`; it
is absorbed as soon as `gamma <= 2/3`, by
`three_halves_mul_rpow_three_neg_recurrenceGap_div_four_le_gamma_pow_six`.
This is recorded as an observation about a printed constant, not as a defect of
the argument.

## Binders the caller must supply

Two quantitative inputs are **not** proved here and are disclosed binders on
every statement that needs them.

* `hgrad` -- the discounted gradient gate `C |grad h| <= Delta
  lambda_{3/8,2}(z+cu_n; a_{m-h})` for the **centered** shell `h -
  (h)_{z+cu_n}`.  For the *literal* increment `k_m - k_{m-h}` it is proved:
  `responseSensitivityConst_mul_gradientW1Infinity_le_of_mem_goodLocalEvent_ae`
  derives it, almost surely, from membership in
  `Provider.BadEvents.goodLocalEvent` together with the proved lambda-transfer
  `Provider.BadEvents.lambda_transfer_ae`, given the caller's comparison of the
  centered field's gradient gauge with the literal one.  Centering by a
  constant does not change a gradient, but the two carriers are distinct
  objects in this repository and that identification is not available here.
* `hshell` -- the centered-shell size `||h - (h)_{z+cu_n}||^2 <= Delta^2
  shom_{m-h} lambda_{3/8,2}`.  ABK26 obtains it from the *middle* term of
  `e.good.local.events` (the `shom_{n-1}` bound) together with a Poincare
  estimate on `z + cu_n` for the centered field and `e.cg.ellip.lower` (label).
  This repository has no Poincare centering estimate on a triadic cube, so
  `hshell` stays an explicit hypothesis; it is never assumed in any other form
  and never derived from an unproved lemma.

Neither binder is a predecessor's conclusion and neither smuggles a proof step:
both are quantitative statements about the *data* (the shell increment and the
coarse ellipticity), exactly as uses them.

## Per-cube good events

No union over the grid is formed anywhere in this module.

## Carriers and readings

* The localization cube is a free `TriadicCube d`; `n = m - h - 16 ceil|log_3
  gamma|` of `e.recurrence.params` (label) is never hard-coded.
* The scale gap `G = m - h - n` is never fixed to a numeral.  It enters as
  `scaleGapPos R.scale lowScale` in
  `responseSensitivityConst_mul_gradientW1Infinity_le_of_mem_goodLocalEvent_ae`,
  and as the free `recurrenceGap a gamma` of
  `three_halves_mul_rpow_three_neg_recurrenceGap_div_four_le_gamma_pow_six`.
* Nothing about that reading is restated here: the transported statement simply
  carries `Ch02.lambdaSq Q (3/8) 2` where the unit-cube statement carries
  `unitCubeLambda (3/8) 2`.
* `cstar` does not occur in this module.

## Main results

* `coarseBlockMatrix_originCube_dilate`
* `cubeSet_eq_translateSet_originCube_triadicCubeShift`
* `coarseBlockMatrix_cutoff_family_translateCutoffSample`
* `coarseBlockMatrix_unitRescaledCutoffCoeff`
* `blockVecDot_coarseBlockMatrix_le_gauge_switch_cube_of_sensitivityGate`
* `blockVecDot_coarseBlockMatrix_nonneg`
* `abs_vecDot_le_half_weighted_vecNormSq_add`
* `gaugeSwitchYoungAbsorb`
* `principalSwitchLoadConst`, `principalSwitchLoadConst_pos`
* `blockVecDot_coarseBlockMatrix_le_switch_absorbed_cube`
* `responseSensitivityConst_mul_gradientW1Infinity_le_of_mem_goodLocalEvent_ae`
* `three_halves_mul_rpow_three_neg_recurrenceGap_div_four_le_gamma_pow_six`
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz

noncomputable section

variable {d : ℕ}

/-! ## Scale normalization of the doubled coarse block matrix -/

/-- **Scale normalization of `bfA`.**  The doubled coarse block matrix of a triadic
family on the centered scale-`m` cube is that of its `3^{-m}`-dilation on the
unit cube.  This is the `bfA` analogue of the proved
`lambdaSq_originCube_dilate` and `responseJ_originCube_dilate`.

Unconditional: no caller-supplied proposition enters. -/
theorem coarseBlockMatrix_originCube_dilate (F : Ch02.TriadicCoeffFamily d) (m : ℤ) :
    Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d 0))
        ((Ch02.TriadicCoeffFamily.dilate (-m) F).coeffOn (originCube d 0)) =
      Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d m))
        (F.coeffOn (originCube d m)) := by
  have h := Ch02.coarseBlockMatrix_dilate
    (Ch02.TriadicCoeffFamily.isDilation_dilate (-m) F (originCube d m))
  rwa [dilateCube_neg_originCube m] at h

/-! ## The triadic geometry of the base-point translation -/

/-- The half-open realization of a triadic cube `Q = z + square_m` is the
translate, by the real base point `z = triadicCubeShift Q`, of the centered
cube of the same scale.  This is the `cubeSet` counterpart of CoarseGraining's
`openCubeSet_eq_translateSet_originCube_of_triadicCube`, at arbitrary (possibly
negative) scale.

Unconditional: no caller-supplied proposition enters. -/
theorem cubeSet_eq_translateSet_originCube_triadicCubeShift (Q : TriadicCube d) :
    cubeSet Q = translateSet (triadicCubeShift Q) (cubeSet (originCube d Q.scale)) := by
  have h := cubeSet_translateCube_descendantTranslationShift (d := d) Q.index 0
    (R := originCube d Q.scale) (j := Q.scale) (by simp [originCube])
  have hQ : translateCube (descendantTranslationShift 0 Q.index)
      (originCube d Q.scale) = Q := by
    cases Q with
    | mk scale index => simp [translateCube, originCube, descendantTranslationShift]
  rw [hQ] at h
  rw [h]
  rfl

/-! ## Translation covariance at the repository's own family carrier -/

/-- One-cube translation covariance of the doubled coarse block matrix for the
actual coefficient cutoff, stated at
`Cutoff.coefficientCutoffTriadicCoeffFamily`: if the half-open realization of
`T` is the translate by `v` of that of `R`, then `bfA(T; a_m)` equals
`bfA(R; a_m)` for the translated sample.

This is the proved
`Provider.BadEvents.coarseBlockMatrix_cutoff_translateCutoffSample` read
through `Ch02.coarseBlockMatrix_eq_ofAEEq`; the two coefficient objects have the
*same* coefficient field and differ only in their ellipticity witnesses.

: this statement holds only under the proposition supplied by its binder
`hset`, the triadic geometry of the translation.  It is a provider A, not a
source-facing frozen declaration. -/
theorem coarseBlockMatrix_cutoff_family_translateCutoffSample [NeZero d]
    (M : ABKModel d) (m : ℤ) (v : Vec d) {R T : TriadicCube d}
    (hset : cubeSet T = translateSet v (cubeSet R)) (omega : CutoffSample d) :
    Ch02.coarseBlockMatrix (Ch02.cubeDomain T)
        ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn T) =
      Ch02.coarseBlockMatrix (Ch02.cubeDomain R)
        ((coefficientCutoffTriadicCoeffFamily M m
          (translateCutoffSample v omega)).coeffOn R) := by
  have hleft : Ch02.CoeffOn.AEEq
      ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn T)
      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (coefficientCutoff M.nu m omega)
        (coefficientCutoff_aeLocallyUniformlyEllipticField M m omega)).coeffOn T) :=
    Filter.EventuallyEq.rfl
  have hright : Ch02.CoeffOn.AEEq
      ((coefficientCutoffTriadicCoeffFamily M m
        (translateCutoffSample v omega)).coeffOn R)
      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (coefficientCutoff M.nu m (translateCutoffSample v omega))
        (coefficientCutoff_aeLocallyUniformlyEllipticField M m
          (translateCutoffSample v omega))).coeffOn R) :=
    Filter.EventuallyEq.rfl
  rw [Ch02.coarseBlockMatrix_eq_ofAEEq hleft, Ch02.coarseBlockMatrix_eq_ofAEEq hright]
  exact coarseBlockMatrix_cutoff_translateCutoffSample M m v hset omega

/-! ## The transport -/

/-- **The `bfA` carrier transport.**  The frozen unit-cube doubled coarse block
matrix of the rescaled coefficient object is the doubled coarse block matrix of
the cutoff on the cube `Q = z + square_m` itself:

```
bfA(square_0; a_n(z + 3^m .))  =  bfA(z + square_m; a_n) .
```

This is the exact analogue, for `bfA`, of the proved
`unitCubeLambda_unitRescaledCutoffCoeff` and
`responseJ_unitRescaledCutoffCoeff`.

Unconditional: no caller-supplied proposition enters. -/
theorem coarseBlockMatrix_unitRescaledCutoffCoeff [NeZero d] (M : ABKModel d)
    (Q : TriadicCube d) (cutoffScale : ℤ) (omega : CutoffSample d) :
    Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d 0))
        (unitRescaledCutoffCoeff M Q cutoffScale omega) =
      Ch02.coarseBlockMatrix (Ch02.cubeDomain Q)
        ((coefficientCutoffTriadicCoeffFamily M cutoffScale omega).coeffOn Q) := by
  rw [unitRescaledCutoffCoeff, coarseBlockMatrix_originCube_dilate]
  exact (coarseBlockMatrix_cutoff_family_translateCutoffSample M cutoffScale
    (triadicCubeShift Q) (cubeSet_eq_translateSet_originCube_triadicCubeShift Q)
    omega).symm

/-! ## The gauge-switch chain at `z + cu_n` -/

/-- **ABK26 at the manuscript's own cube `Q = z + cu_n`**, at a free sensitivity
parameter `delta` in `(0,1]`.

Every carrier is the localization cube: both doubled coarse block matrices are
`bfA(z + cu_n; .)`, and the ellipticity gauge is the manuscript's own
`lambda_{3/8,2}(z + cu_n; a_{lowScale})`.  The dimension-only constant
`responseSensitivityConst d` is unchanged by the transport, which is a chain of
equalities.

The manuscript's `a_m` is the cutoff at `highScale` and its `a_{m-h}` is the
cutoff at `lowScale`; the load `X` is `P_z` and the constant antisymmetric
matrix `hbar` is `(h)_{z+cu_n}` (built and proved skew in
`ApproximateRecurrence.PrincipalResponseShellAverage`).  The two `2 X_1 . X_2`
terms are the manuscript's `2 p_z . q_z`, derived in
`ApproximateRecurrence.PrincipalResponseSensitivityAlgebra`; they are kept
explicit rather than absorbed.  The Young remainder is likewise not absorbed at
this stage; the absorption is
`blockVecDot_coarseBlockMatrix_le_switch_absorbed_cube` below.

: this statement holds only under the propositions supplied by its binders --
`dimension` (the paper-wide `2 <= d`), `hskew` (antisymmetry of the averaged
shell), `hshift` (the manuscript's own field decomposition `a_{lowScale} +
hfield = a_{highScale} - hbar` at the rescaled unit-cube carrier), `hgate`
(`e.J.sensitivity.smallness.condition`, label, for the *centered* perturbation)
and the range `hdelta`, `hdelta1` of `delta`.  It is a provider A, not a
source-facing frozen declaration. -/
theorem blockVecDot_coarseBlockMatrix_le_gauge_switch_cube_of_sensitivityGate
    (dimension : 2 ≤ d) [NeZero d] (M : ABKModel d) (Q : TriadicCube d)
    (lowScale highScale : ℤ) (omega : CutoffSample d)
    (hfield : UnitCubeSkewW2Infinity d) {hbar : Mat d}
    (hskew : matTranspose hbar = -hbar)
    (hshift : ∀ x,
      (perturbCoeffOn (cubeDomain (originCube d 0))
        (unitRescaledCutoffCoeff M Q lowScale omega)
        hfield.toLInfSkewMatrixFieldOn 1).toCoeffField x =
        (unitRescaledCutoffCoeff M Q highScale omega).toCoeffField x - hbar)
    (hgate : hfield.gradientW1Infinity ≤
      (responseSensitivityConst d)⁻¹ *
        Ch02.lambdaSq Q (3 / 8) (.finite 2)
          (coefficientCutoffTriadicCoeffFamily M lowScale omega))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (X : BlockVec d) :
    blockVecDot X
        (blockMatVecMul
          (Ch02.coarseBlockMatrix (Ch02.cubeDomain Q)
            ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn Q)) X) ≤
      (1 + δ +
            responseSensitivityConst d * hfield.gradientW1Infinity *
              (Ch02.lambdaSq Q (3 / 8) (.finite 2)
                (coefficientCutoffTriadicCoeffFamily M lowScale omega))⁻¹) *
          (blockVecDot (blockMatVecMul (blockGauge (-hbar)) X)
              (blockMatVecMul
                (Ch02.coarseBlockMatrix (Ch02.cubeDomain Q)
                  ((coefficientCutoffTriadicCoeffFamily M lowScale omega).coeffOn Q))
                (blockMatVecMul (blockGauge (-hbar)) X)) +
            2 * vecDot X.1 X.2) +
        2 * (responseSensitivityConst d * δ⁻¹ *
          (vecNormSq X.1 * hfield.w1Infinity ^ 2 *
              (Ch02.lambdaSq Q (3 / 8) (.finite 2)
                (coefficientCutoffTriadicCoeffFamily M lowScale omega))⁻¹ +
            |vecDot X.1 X.2| * hfield.gradientW1Infinity ^ 2 *
              (Ch02.lambdaSq Q (3 / 8) (.finite 2)
                (coefficientCutoffTriadicCoeffFamily M lowScale omega))⁻¹ ^ 2)) -
        2 * vecDot X.1 X.2 := by
  rw [← unitCubeLambda_unitRescaledCutoffCoeff M Q lowScale (3 / 8) (.finite 2) omega,
    ← coarseBlockMatrix_unitRescaledCutoffCoeff M Q highScale omega,
    ← coarseBlockMatrix_unitRescaledCutoffCoeff M Q lowScale omega]
  rw [← unitCubeLambda_unitRescaledCutoffCoeff M Q lowScale (3 / 8) (.finite 2) omega]
    at hgate
  exact blockVecDot_coarseBlockMatrix_le_gauge_switch_of_sensitivityGate
    dimension _ hfield hskew hshift hgate hδ hδ1 X

/-! ## Two elementary facts about the doubled block form -/

/-- **The doubled coarse block quadratic form is nonnegative.**  CoarseGraining's
`Ch02.blockCoarseMatrixTheory` gives `BlockPosDef (coarseBlockMatrix U a)`,
which is strict positivity off the origin; the origin contributes `0`.

Unconditional: no caller-supplied proposition enters. -/
theorem blockVecDot_coarseBlockMatrix_nonneg (U : Ch02.Domain d) (a : Ch02.CoeffOn U)
    (X : BlockVec d) :
    0 ≤ blockVecDot X (blockMatVecMul (Ch02.coarseBlockMatrix U a) X) := by
  by_cases hX : X = 0
  · subst hX
    simp [blockVecDot, blockMatVecMul, vecDot, matVecMul]
  · exact ((Ch02.blockCoarseMatrixTheory U a).block_matrix_posDef X hX).le

/-- : this statement holds only under the proposition supplied by its binder `hS`,
positivity of the weight.  It is a provider A, not a source-facing frozen
declaration. -/
theorem abs_vecDot_le_half_weighted_vecNormSq_add {S : ℝ} (hS : 0 < S) (p q : Vec d) :
    |vecDot p q| ≤ S * vecNormSq p / 2 + S⁻¹ * vecNormSq q / 2 := by
  have hp : (0 : ℝ) ≤ vecNormSq p := vecNormSq_nonneg p
  have hq : (0 : ℝ) ≤ vecNormSq q := vecNormSq_nonneg q
  have hSinv : (0 : ℝ) < S⁻¹ := inv_pos.2 hS
  refine abs_le_add_halves_of_sq_le_mul ?_ (mul_nonneg hS.le hp) (mul_nonneg hSinv.le hq)
  have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq p q
  have hSS : S * S⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hS)
  calc vecDot p q ^ 2 ≤ vecNormSq p * vecNormSq q := hcs
    _ = S * vecNormSq p * (S⁻¹ * vecNormSq q) := by
        rw [show S * vecNormSq p * (S⁻¹ * vecNormSq q)
          = (S * S⁻¹) * (vecNormSq p * vecNormSq q) by ring, hSS, one_mul]

/-! ## The absorption, as real arithmetic -/

/-- **The absorption, as a real inequality.**

Reading the variables at the Step 3 carrier: `E` is `P_z . bfA_m(z+cu_n) P_z`,
`B` is `G_{-(h)} P_z . bfA_{m-h}(z+cu_n) G_{-(h)} P_z`, `t` is `p_z . q_z`,
`nrm1` and `nrm2` are `|p_z|^2` and `|q_z|^2`, `C` is the frozen dimension-only
sensitivity constant, `g` and `w` are the gradient and value gauges of the
centered shell, `lam` is `lambda_{3/8,2}(z+cu_n; a_{m-h})`, `S` is
`shom_{m-h}`, and `Delta` is `3^{-(1/4)(m-h-n)_+}`.  `hchain` is the conclusion
of the transported gauge switch at the manuscript's own `delta = (1/2) Delta`.

The three moves are the manuscript's: the two `2 p_z . q_z` pairings cancel down
to `2 (delta + C g lam^{-1}) (p_z . q_z)`; the pairing is folded into the load
by Young at the weight `S`; and the two remainder terms are folded in using
`hgrad` and `hshell`.

: this statement holds only under the propositions supplied by its binders --
the sign and range conditions, `hpair` (Young at weight `S`), `hgrad` (the
discounted gradient gate of `e.good.local.events`), `hshell` (the
centered-shell size), and `hchain` (the transported gauge switch).  It is a
provider A, not a source-facing frozen declaration. -/
theorem gaugeSwitchYoungAbsorb {E B t nrm1 nrm2 C g w lam S Delta : ℝ}
    (hC : 0 < C) (hlam : 0 < lam) (hS : 0 < S) (hDelta : 0 < Delta)
    (hnrm1 : 0 ≤ nrm1) (hnrm2 : 0 ≤ nrm2) (hB : 0 ≤ B) (hg : 0 ≤ g)
    (hpair : |t| ≤ S * nrm1 / 2 + S⁻¹ * nrm2 / 2)
    (hgrad : C * g ≤ Delta * lam)
    (hshell : w ^ 2 ≤ Delta ^ 2 * S * lam)
    (hchain : E ≤
      (1 + (1 / 2 : ℝ) * Delta + C * g * lam⁻¹) * (B + 2 * t) +
        2 * (C * ((1 / 2 : ℝ) * Delta)⁻¹ *
          (nrm1 * w ^ 2 * lam⁻¹ + |t| * g ^ 2 * lam⁻¹ ^ 2)) -
        2 * t) :
    E ≤ (1 + (3 / 2 : ℝ) * Delta) * B +
      ((3 / 2 : ℝ) + 4 * C + 2 * C⁻¹) * Delta * (S * nrm1 + S⁻¹ * nrm2) := by
  set L : ℝ := S * nrm1 + S⁻¹ * nrm2 with hLdef
  have hlaminv : (0 : ℝ) < lam⁻¹ := inv_pos.2 hlam
  have hCinv : (0 : ℝ) < C⁻¹ := inv_pos.2 hC
  have hDinv : (0 : ℝ) < Delta⁻¹ := inv_pos.2 hDelta
  have hL0 : (0 : ℝ) ≤ L := by
    have h1 : (0 : ℝ) ≤ S * nrm1 := mul_nonneg hS.le hnrm1
    have h2 : (0 : ℝ) ≤ S⁻¹ * nrm2 := mul_nonneg (inv_pos.2 hS).le hnrm2
    simpa [hLdef] using add_nonneg h1 h2
  have habs : |t| ≤ L / 2 := by rw [hLdef]; linarith only [hpair]
  have habs0 : (0 : ℝ) ≤ |t| := abs_nonneg t
  set eps : ℝ := C * g * lam⁻¹ with hepsdef
  have heps0 : (0 : ℝ) ≤ eps := by
    have hCg : (0 : ℝ) ≤ C * g := mul_nonneg hC.le hg
    exact mul_nonneg hCg hlaminv.le
  have hepsle : eps ≤ Delta := by
    have h := mul_le_mul_of_nonneg_right hgrad hlaminv.le
    rwa [mul_assoc Delta lam lam⁻¹, mul_inv_cancel₀ (ne_of_gt hlam), mul_one] at h
  have hterm1 : (1 + (1 / 2 : ℝ) * Delta + eps) * B ≤ (1 + (3 / 2 : ℝ) * Delta) * B :=
    mul_le_mul_of_nonneg_right (by linarith only [hepsle]) hB
  have hpairterm : 2 * ((1 / 2 : ℝ) * Delta + eps) * t ≤ (3 / 2 : ℝ) * Delta * L := by
    have hle : t ≤ |t| := le_abs_self t
    have hcoef0 : (0 : ℝ) ≤ 2 * ((1 / 2 : ℝ) * Delta + eps) := by
      linarith only [hDelta, heps0]
    have h1 : 2 * ((1 / 2 : ℝ) * Delta + eps) * t ≤
        2 * ((1 / 2 : ℝ) * Delta + eps) * |t| :=
      mul_le_mul_of_nonneg_left hle hcoef0
    have h2 : 2 * ((1 / 2 : ℝ) * Delta + eps) * |t| ≤ 3 * Delta * |t| :=
      mul_le_mul_of_nonneg_right (by linarith only [hepsle]) habs0
    have h3 : 3 * Delta * |t| ≤ 3 * Delta * (L / 2) :=
      mul_le_mul_of_nonneg_left habs (by linarith only [hDelta])
    linarith only [h1, h2, h3]
  have hwlam : w ^ 2 * lam⁻¹ ≤ Delta ^ 2 * S := by
    have h := mul_le_mul_of_nonneg_right hshell hlaminv.le
    rwa [mul_assoc (Delta ^ 2 * S) lam lam⁻¹, mul_inv_cancel₀ (ne_of_gt hlam),
      mul_one] at h
  have hA1 : nrm1 * w ^ 2 * lam⁻¹ ≤ Delta ^ 2 * (S * nrm1) := by
    have h := mul_le_mul_of_nonneg_left hwlam hnrm1
    calc nrm1 * w ^ 2 * lam⁻¹ = nrm1 * (w ^ 2 * lam⁻¹) := by ring
      _ ≤ nrm1 * (Delta ^ 2 * S) := h
      _ = Delta ^ 2 * (S * nrm1) := by ring
  have hglam : g * lam⁻¹ ≤ Delta * C⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hepsle hCinv.le
    rw [hepsdef] at h
    calc g * lam⁻¹ = C⁻¹ * (C * g * lam⁻¹) := by
          rw [show C⁻¹ * (C * g * lam⁻¹) = (C⁻¹ * C) * (g * lam⁻¹) by ring,
            inv_mul_cancel₀ (ne_of_gt hC), one_mul]
      _ ≤ C⁻¹ * Delta := h
      _ = Delta * C⁻¹ := by ring
  have hglam0 : (0 : ℝ) ≤ g * lam⁻¹ := mul_nonneg hg hlaminv.le
  have hA2 : |t| * g ^ 2 * lam⁻¹ ^ 2 ≤ Delta ^ 2 * C⁻¹ ^ 2 * |t| := by
    have hsq : (g * lam⁻¹) ^ 2 ≤ (Delta * C⁻¹) ^ 2 := by
      have hmm := mul_le_mul hglam hglam hglam0 (by positivity)
      calc (g * lam⁻¹) ^ 2 = (g * lam⁻¹) * (g * lam⁻¹) := by ring
        _ ≤ (Delta * C⁻¹) * (Delta * C⁻¹) := hmm
        _ = (Delta * C⁻¹) ^ 2 := by ring
    have h := mul_le_mul_of_nonneg_left hsq habs0
    calc |t| * g ^ 2 * lam⁻¹ ^ 2 = |t| * (g * lam⁻¹) ^ 2 := by ring
      _ ≤ |t| * (Delta * C⁻¹) ^ 2 := h
      _ = Delta ^ 2 * C⁻¹ ^ 2 * |t| := by ring
  have hinv : ((1 / 2 : ℝ) * Delta)⁻¹ = 2 * Delta⁻¹ := by
    rw [mul_inv]
    norm_num
  have hDD : Delta⁻¹ * Delta ^ 2 = Delta := by field_simp
  have hCC : C * C⁻¹ ^ 2 = C⁻¹ := by field_simp
  have hrem : 2 * (C * ((1 / 2 : ℝ) * Delta)⁻¹ *
      (nrm1 * w ^ 2 * lam⁻¹ + |t| * g ^ 2 * lam⁻¹ ^ 2)) ≤
      4 * C * Delta * L + 2 * C⁻¹ * Delta * L := by
    have hcoef0 : (0 : ℝ) ≤ 4 * (C * Delta⁻¹) := by positivity
    have hsum : nrm1 * w ^ 2 * lam⁻¹ + |t| * g ^ 2 * lam⁻¹ ^ 2 ≤
        Delta ^ 2 * (S * nrm1) + Delta ^ 2 * C⁻¹ ^ 2 * |t| := by
      linarith only [hA1, hA2]
    have hstep : 2 * (C * ((1 / 2 : ℝ) * Delta)⁻¹ *
        (nrm1 * w ^ 2 * lam⁻¹ + |t| * g ^ 2 * lam⁻¹ ^ 2)) ≤
        4 * (C * Delta⁻¹) * (Delta ^ 2 * (S * nrm1) + Delta ^ 2 * C⁻¹ ^ 2 * |t|) := by
      rw [hinv]
      calc 2 * (C * (2 * Delta⁻¹) *
            (nrm1 * w ^ 2 * lam⁻¹ + |t| * g ^ 2 * lam⁻¹ ^ 2))
          = 4 * (C * Delta⁻¹) *
              (nrm1 * w ^ 2 * lam⁻¹ + |t| * g ^ 2 * lam⁻¹ ^ 2) := by ring
        _ ≤ 4 * (C * Delta⁻¹) *
              (Delta ^ 2 * (S * nrm1) + Delta ^ 2 * C⁻¹ ^ 2 * |t|) :=
            mul_le_mul_of_nonneg_left hsum hcoef0
    have hid : 4 * (C * Delta⁻¹) * (Delta ^ 2 * (S * nrm1) + Delta ^ 2 * C⁻¹ ^ 2 * |t|) =
        4 * C * Delta * (S * nrm1) + 4 * C⁻¹ * Delta * |t| := by
      have h1 : 4 * (C * Delta⁻¹) * (Delta ^ 2 * (S * nrm1)) =
          4 * C * (Delta⁻¹ * Delta ^ 2) * (S * nrm1) := by ring
      have h2 : 4 * (C * Delta⁻¹) * (Delta ^ 2 * C⁻¹ ^ 2 * |t|) =
          4 * (C * C⁻¹ ^ 2) * (Delta⁻¹ * Delta ^ 2) * |t| := by ring
      rw [show 4 * (C * Delta⁻¹) * (Delta ^ 2 * (S * nrm1) + Delta ^ 2 * C⁻¹ ^ 2 * |t|) =
        4 * (C * Delta⁻¹) * (Delta ^ 2 * (S * nrm1)) +
          4 * (C * Delta⁻¹) * (Delta ^ 2 * C⁻¹ ^ 2 * |t|) by ring, h1, h2, hDD, hCC]
    rw [hid] at hstep
    have hSn : S * nrm1 ≤ L := by
      have hnn : (0 : ℝ) ≤ S⁻¹ * nrm2 := mul_nonneg (inv_pos.2 hS).le hnrm2
      simpa [hLdef] using hnn
    have hb1 : 4 * C * Delta * (S * nrm1) ≤ 4 * C * Delta * L :=
      mul_le_mul_of_nonneg_left hSn (by positivity)
    have hb2 : 4 * C⁻¹ * Delta * |t| ≤ 4 * C⁻¹ * Delta * (L / 2) :=
      mul_le_mul_of_nonneg_left habs (by positivity)
    linarith only [hstep, hb1, hb2]
  have hexp : (1 + (1 / 2 : ℝ) * Delta + eps) * (B + 2 * t) - 2 * t =
      (1 + (1 / 2 : ℝ) * Delta + eps) * B + 2 * ((1 / 2 : ℝ) * Delta + eps) * t := by
    ring
  linarith only [hchain, hexp, hterm1, hpairterm, hrem]

/-! ## The load constant -/

/-- The dimension-only constant multiplying the ellipticity load `shom_{m-h}|p_z|^2
+ shom_{m-h}^{-1}|q_z|^2` in the absorbed form, normalized so that it
multiplies the switch excess `(3/2) Delta` itself.  It is built from the frozen
response-sensitivity constant alone. -/
def principalSwitchLoadConst (d : ℕ) : ℝ :=
  1 + (8 / 3 : ℝ) * responseSensitivityConst d +
    (4 / 3 : ℝ) * (responseSensitivityConst d)⁻¹

/-- Positivity of the load constant.

: this statement holds only under the proposition supplied by its binder
`dimension`, the paper-wide `2 <= d`.  It is a provider A, not a source-facing
frozen declaration. -/
theorem principalSwitchLoadConst_pos (dimension : 2 ≤ d) :
    0 < principalSwitchLoadConst d := by
  have hC : 0 < responseSensitivityConst d := responseSensitivityConst_pos dimension
  have hCinv : 0 < (responseSensitivityConst d)⁻¹ := inv_pos.2 hC
  unfold principalSwitchLoadConst
  linarith only [hC, hCinv]

/-- The normalization identity behind `principalSwitchLoadConst`.

Unconditional: no caller-supplied proposition enters. -/
theorem principalSwitchLoadConst_mul (D : ℝ) :
    principalSwitchLoadConst d * ((3 / 2 : ℝ) * D) =
      ((3 / 2 : ℝ) + 4 * responseSensitivityConst d +
        2 * (responseSensitivityConst d)⁻¹) * D := by
  unfold principalSwitchLoadConst
  ring

/-! ## The absorbed switch at `z + cu_n` -/

/-- **The closing line of ABK26, at the manuscript's own cube.**

```
P_z . bfA_m(z+cu_n) P_z
  <= (1 + (3/2) Delta) G_{-(h)} P_z . bfA_{m-h}(z+cu_n) G_{-(h)} P_z
     + C_load(d) (3/2) Delta ( S |p_z|^2 + S^{-1} |q_z|^2 ) ,
```

with `Delta` the manuscript's `3^{-(1/4)(m-h-n)}` (free here) and `S` the
manuscript's `shom_{m-h}` (free here).  See the module docstring for why the
switch factor carries `3/2` rather than the printed `1`.

: this statement holds only under the propositions supplied by its binders --
`dimension`; `hskew` and `hshift`, the carrier facts of the averaged fresh
shell and the source's own field decomposition; the ranges `hDelta0`,
`hDelta1`, `hS0`, `hlam0`; and the two good-event inputs `hgrad` and `hshell`
described in the module docstring.  It is a provider A, not a source-facing
frozen declaration. -/
theorem blockVecDot_coarseBlockMatrix_le_switch_absorbed_cube
    (dimension : 2 ≤ d) [NeZero d] (M : ABKModel d) (Q : TriadicCube d)
    (lowScale highScale : ℤ) (omega : CutoffSample d)
    (hfield : UnitCubeSkewW2Infinity d) {hbar : Mat d}
    (hskew : matTranspose hbar = -hbar)
    (hshift : ∀ x,
      (perturbCoeffOn (cubeDomain (originCube d 0))
        (unitRescaledCutoffCoeff M Q lowScale omega)
        hfield.toLInfSkewMatrixFieldOn 1).toCoeffField x =
        (unitRescaledCutoffCoeff M Q highScale omega).toCoeffField x - hbar)
    {Delta S : ℝ} (hDelta0 : 0 < Delta) (hDelta1 : Delta ≤ 1) (hS0 : 0 < S)
    (hlam0 : 0 < Ch02.lambdaSq Q (3 / 8) (.finite 2)
      (coefficientCutoffTriadicCoeffFamily M lowScale omega))
    (hgrad : responseSensitivityConst d * hfield.gradientW1Infinity ≤
      Delta * Ch02.lambdaSq Q (3 / 8) (.finite 2)
        (coefficientCutoffTriadicCoeffFamily M lowScale omega))
    (hshell : hfield.w1Infinity ^ 2 ≤
      Delta ^ 2 * S * Ch02.lambdaSq Q (3 / 8) (.finite 2)
        (coefficientCutoffTriadicCoeffFamily M lowScale omega))
    (X : BlockVec d) :
    blockVecDot X
        (blockMatVecMul
          (Ch02.coarseBlockMatrix (Ch02.cubeDomain Q)
            ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn Q)) X) ≤
      (1 + (3 / 2 : ℝ) * Delta) *
          blockVecDot (blockMatVecMul (blockGauge (-hbar)) X)
            (blockMatVecMul
              (Ch02.coarseBlockMatrix (Ch02.cubeDomain Q)
                ((coefficientCutoffTriadicCoeffFamily M lowScale omega).coeffOn Q))
              (blockMatVecMul (blockGauge (-hbar)) X)) +
        principalSwitchLoadConst d * ((3 / 2 : ℝ) * Delta) *
          (S * vecNormSq X.1 + S⁻¹ * vecNormSq X.2) := by
  have hC : 0 < responseSensitivityConst d := responseSensitivityConst_pos dimension
  have hg : 0 ≤ hfield.gradientW1Infinity := gradientW1Infinity_nonneg hfield
  -- the frozen smallness gate follows from the discounted good-event gate
  have hgate : hfield.gradientW1Infinity ≤
      (responseSensitivityConst d)⁻¹ *
        Ch02.lambdaSq Q (3 / 8) (.finite 2)
          (coefficientCutoffTriadicCoeffFamily M lowScale omega) := by
    have hstep : responseSensitivityConst d * hfield.gradientW1Infinity ≤
        Ch02.lambdaSq Q (3 / 8) (.finite 2)
          (coefficientCutoffTriadicCoeffFamily M lowScale omega) := by
      refine hgrad.trans ?_
      exact (mul_le_mul_of_nonneg_right hDelta1 hlam0.le).trans_eq (one_mul _)
    have h := mul_le_mul_of_nonneg_left hstep (inv_pos.2 hC).le
    rwa [show (responseSensitivityConst d)⁻¹ *
        (responseSensitivityConst d * hfield.gradientW1Infinity) =
      ((responseSensitivityConst d)⁻¹ * responseSensitivityConst d) *
        hfield.gradientW1Infinity by ring,
      inv_mul_cancel₀ (ne_of_gt hC), one_mul] at h
  have hchain := blockVecDot_coarseBlockMatrix_le_gauge_switch_cube_of_sensitivityGate
    dimension M Q lowScale highScale omega hfield hskew hshift hgate
    (δ := (1 / 2 : ℝ) * Delta) (by linarith only [hDelta0])
    (by linarith only [hDelta1]) X
  have habsorb := gaugeSwitchYoungAbsorb (E := blockVecDot X
      (blockMatVecMul
        (Ch02.coarseBlockMatrix (Ch02.cubeDomain Q)
          ((coefficientCutoffTriadicCoeffFamily M highScale omega).coeffOn Q)) X))
    (B := blockVecDot (blockMatVecMul (blockGauge (-hbar)) X)
      (blockMatVecMul
        (Ch02.coarseBlockMatrix (Ch02.cubeDomain Q)
          ((coefficientCutoffTriadicCoeffFamily M lowScale omega).coeffOn Q))
        (blockMatVecMul (blockGauge (-hbar)) X)))
    (t := vecDot X.1 X.2) (nrm1 := vecNormSq X.1) (nrm2 := vecNormSq X.2)
    (C := responseSensitivityConst d) (g := hfield.gradientW1Infinity)
    (w := hfield.w1Infinity)
    hC hlam0 hS0 hDelta0 (vecNormSq_nonneg X.1) (vecNormSq_nonneg X.2)
    (blockVecDot_coarseBlockMatrix_nonneg _ _ _) hg
    (abs_vecDot_le_half_weighted_vecNormSq_add hS0 X.1 X.2) hgrad hshell hchain
  rw [principalSwitchLoadConst_mul]
  exact habsorb

/-! ## The discounted gradient gate, from the good event -/

/-- **The discounted gradient gate of `e.good.local.events`, transferred to the
frozen `lambda_{3/8,2}`.**

On the event `cQ(n, m-h, z)` -- here `goodLocalEvent M Ccg R lowScale` at the
localization cube `R` of scale `n` and the coarse scale `lowScale = m-h` -- the
manuscript's second inequality reads

```
C_sens 3^{2n} ||grad (k_L - k_{m-h})||_{W^{1,infinity}(z+cu_n)}
  <= 3^{-(1/4)(m-h-n)_+} lambda_{1/8,2}(z+cu_n; a_{m-h}) ,
```

and the proved lambda-transfer replaces `lambda_{1/8,2}` by the frozen
`lambda_{3/8,2}(z+cu_n; a_{m-h})`.  The hypothesis `hcentered` is the only
remaining input: it compares the gradient gauge of the caller's centered field
with that of the literal rescaled increment.

: this statement holds only under the propositions supplied by its binders --
`hL` (`m-h <= m`), membership in the good event, and `hcentered`.  It is a
provider A, not a source-facing frozen declaration. -/
theorem responseSensitivityConst_mul_gradientW1Infinity_le_of_mem_goodLocalEvent_ae
    [NeZero d] (M : ABKModel d) (Ccg : ℝ) (R : TriadicCube d)
    {lowScale highScale : ℤ} (hL : lowScale ≤ highScale)
    (hfield : CutoffSample d → UnitCubeSkewW2Infinity d) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∈ goodLocalEvent M Ccg R lowScale →
        (hfield omega).gradientW1Infinity ≤
            (incrementUnitCube₂ R lowScale highScale omega).gradientW1Infinity →
          responseSensitivityConst d * (hfield omega).gradientW1Infinity ≤
            (3 : ℝ) ^ (-(1 / 4 : ℝ) * scaleGapPos R.scale lowScale) *
              Ch02.lambdaSq R (3 / 8) (.finite 2)
                (coefficientCutoffTriadicCoeffFamily M lowScale omega) := by
  filter_upwards [lambda_transfer_ae M R lowScale] with omega htransfer homega hcentered
  have hCle : responseSensitivityConst d ≤ sensitivityConstMax d :=
    responseSensitivityConst_le_sensitivityConstMax d
  have hCpos : 0 < responseSensitivityConst d :=
    responseSensitivityConst_pos M.shellPrefix.dimension
  have hgauge : (0 : ℝ) ≤ incrementOscGauge₂ R lowScale highScale omega :=
    le_trans (gradientW1Infinity_nonneg _)
      (gradientW1Infinity_incrementUnitCube₂_le R lowScale highScale omega)
  have hfg : (hfield omega).gradientW1Infinity ≤
      incrementOscGauge₂ R lowScale highScale omega :=
    hcentered.trans (gradientW1Infinity_incrementUnitCube₂_le R lowScale highScale omega)
  have hstep : responseSensitivityConst d * (hfield omega).gradientW1Infinity ≤
      sensitivityConstMax d * incrementOscGauge₂ R lowScale highScale omega := by
    calc responseSensitivityConst d * (hfield omega).gradientW1Infinity
        ≤ responseSensitivityConst d * incrementOscGauge₂ R lowScale highScale omega :=
          mul_le_mul_of_nonneg_left hfg hCpos.le
      _ ≤ sensitivityConstMax d * incrementOscGauge₂ R lowScale highScale omega :=
          mul_le_mul_of_nonneg_right hCle hgauge
  refine hstep.trans ((incrementOscGauge₂_le_of_mem_goodLocalEvent M R homega hL).trans ?_)
  have hpow : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 / 4 : ℝ) * scaleGapPos R.scale lowScale) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  refine mul_le_mul_of_nonneg_left ?_ hpow
  rw [← unitCubeLambda_unitRescaledCutoffCoeff M R lowScale (3 / 8) (.finite 2) omega]
  exact htransfer

/-! ## The `cgamma^6` gate at the corrected recurrence gap -/

/-- **The switch-factor gate at the corrected gap, with the `3/2` of the module
docstring.**  At the multiplier `a >= 28` the switch excess `(3/2)
3^{-(1/4)(m-h-n)}` of the absorbed form is below the `cgamma^6` that
`e.lower.bound.principal.one.pre` prints, as soon as `gamma <= 2/3`.

It is a provider A, not a source-facing frozen declaration. -/
theorem three_halves_mul_rpow_three_neg_recurrenceGap_div_four_le_gamma_pow_six
    (a : ℕ) {gamma : ℝ} (hgamma0 : 0 < gamma) (hgamma23 : gamma ≤ 2 / 3)
    (ha : recurrenceGapMultiplierFloor ≤ a) :
    (3 / 2 : ℝ) * (3 : ℝ) ^ (-((recurrenceGap a gamma : ℝ) / 4)) ≤ gamma ^ (6 : ℕ) := by
  have hgamma1 : gamma ≤ 1 := by linarith only [hgamma23]
  have h7 := rpow_three_neg_recurrenceGap_div_four_le_rpow_seven a hgamma0 hgamma1 ha
  have h6 : gamma ^ (6 : ℝ) = gamma ^ (6 : ℕ) := by
    rw [← Real.rpow_natCast gamma 6]
    norm_num
  have hstep : gamma ^ (7 : ℝ) = gamma ^ (6 : ℕ) * gamma := by
    rw [show (7 : ℝ) = 6 + 1 by norm_num, Real.rpow_add hgamma0, Real.rpow_one, h6]
  rw [hstep] at h7
  have hpow6 : (0 : ℝ) ≤ gamma ^ (6 : ℕ) := by positivity
  calc (3 / 2 : ℝ) * (3 : ℝ) ^ (-((recurrenceGap a gamma : ℝ) / 4))
      ≤ (3 / 2 : ℝ) * (gamma ^ (6 : ℕ) * gamma) :=
        mul_le_mul_of_nonneg_left h7 (by norm_num)
    _ = ((3 / 2 : ℝ) * gamma) * gamma ^ (6 : ℕ) := by ring
    _ ≤ 1 * gamma ^ (6 : ℕ) :=
        mul_le_mul_of_nonneg_right (by linarith only [hgamma23]) hpow6
    _ = gamma ^ (6 : ℕ) := one_mul _

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
