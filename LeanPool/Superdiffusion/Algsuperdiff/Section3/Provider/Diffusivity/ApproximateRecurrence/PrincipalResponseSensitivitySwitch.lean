/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.DeltaOsc
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseSensitivityAlgebra

/-!
# PrincipalResponseSensitivitySwitch

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the gauged coefficient switch of ABK26 Step 3, at the unit cube

Source displays in ABK26:

* `l.J.sensitivity` (label; statement), applied at `delta:= (1/2)
  3^{-(1/4)(m-h-n)}`;
* `e.J.by.means.of.bfA` (label; display);
* the chain of Step 3 of `l.approximate.recurrence.formula`.

This module proves the *whole* chain as one inequality, at the carrier where
the frozen sensitivity lemma lives.

## What is proved

Write `U` for the unit cube domain `cubeDomain (originCube d 0)`, `a` for the
coarse field (`a_{m-h}` after rescaling), `hfield` for the perturbation
(`(k_m - k_{m-h}) - hbar`, the fresh shell with its cube average removed, after
rescaling), `am` for the field `a_m` and `hbar` for the constant antisymmetric
average.  Then, with `Y = bfG_{-hbar} X`,

```
X . bfA(U; am) X
  <= (1 + delta + C ||grad hfield||_{W^{1,inf}} lambda_{3/8,2}^{-1})
       * ( Y . bfA(U; a) Y + 2 X_1 . X_2 )
     + 2 C delta^{-1} ( |X_1|^2 ||hfield||_{W^{1,inf}}^2 lambda_{3/8,2}^{-1}
                      + |X_1 . X_2| ||grad hfield||_{W^{1,inf}}^2
                          lambda_{3/8,2}^{-2} )
     - 2 X_1 . X_2 .
```

At `X = P_z` the left-hand side is `P_z . bfA_m(z+cu_n) P_z` and the bracket is
`bfG_{-hbar} P_z . bfA_{m-h}(z+cu_n) bfG_{-hbar} P_z`; the two leftover
pairings are the manuscript's `2 p_z . q_z` terms, kept explicit rather than
absorbed.  The manuscript's own conclusion follows by bounding `2 delta |p_z.
q_z|` and the Young remainder -- an absorption step that is *not* performed
here, because it needs the size of `hfield` and of `lambda_{3/8,2}` on the good
event.

## The three readings this makes explicit

* **The pairing term.**  The second equality of Step 3 carries `- 2 p_z . q_z`;
  see the module docstring of
  `ApproximateRecurrence.PrincipalResponseSensitivityAlgebra`, where it is
  derived.  The chain below carries it, and the manuscript's absorption
  consumes it.
* The frozen statement `Algsuperdiff.Frozen.Section24.responseJ_sensitivity`
  already reflects both, and nothing is restated here.

## Why this is conditional, and on exactly what

Two hypotheses are explicit binders and the declarations are named
`..._of_sensitivityGate` accordingly.

1. `hgate` is `e.J.sensitivity.smallness.condition` for the *centered*
   perturbation.  ABK26 derives it from the good event `Q_z = Q(n, m-h, z)` of
   `e.good.local.events`.  The repository's event-wired form,
   `Provider.BadEvents.responseJ_sensitivity_of_mem_goodLocalEvent_of_lambdaTransfer`,
   opens the gate for the *literal* rescaled increment `k_L - k_n`
   (`incrementUnitCube₂`); Step 3 needs it for the increment with its cube
   average removed, which is what makes the `||hfield||_{W^{1,inf}}^2` term of
   the remainder small.  Bridging the two is a Poincare-type centering estimate
   on the localization cube that this repository does not yet have, and it is
   not assumed here in any other form.
2. The carrier is the unit cube, because that is where
   `Algsuperdiff.Frozen.Section24.responseJ_sensitivity` is stated.  Transport
   to `z + cu_n` needs the scale-and-translation covariance of `responseJ` and
   of `coarseBlockMatrix`, together with the lambda-transfer already named in
   the module header of `Provider.BadEvents.GoodLocalEvents`.  Neither is
   available here.

Everything else is a source premise: `hbar` constant antisymmetric (proved for
the actual carrier in
`ApproximateRecurrence.PrincipalResponseShellAverage`), and `hshift`, the
field decomposition `a_{m-h} + hfield = a_m - hbar`.  No proof step is carried
as a hypothesis, and no predecessor's conclusion is copied into a binder.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3.Provider.BadEvents

variable {d : ℕ}

/-- **ABK26 at the unit-cube carrier**, conditional on the smallness gate `hgate`
of `l.J.sensitivity` for the centered perturbation.

The two `2 X_1 . X_2` terms are the manuscript's `2 p_z . q_z`, derived in
`ApproximateRecurrence.PrincipalResponseSensitivityAlgebra`; they are kept
explicit rather than absorbed into the remainder. -/
theorem blockVecDot_coarseBlockMatrix_le_gauge_switch_of_sensitivityGate
    (dimension : 2 ≤ d) (a : CoeffOn (cubeDomain (originCube d 0)))
    (hfield : UnitCubeSkewW2Infinity d) {hbar : Mat d}
    (hskew : matTranspose hbar = -hbar)
    {am : CoeffOn (cubeDomain (originCube d 0))}
    (hshift : ∀ x,
      (perturbCoeffOn (cubeDomain (originCube d 0)) a
        hfield.toLInfSkewMatrixFieldOn 1).toCoeffField x =
        am.toCoeffField x - hbar)
    (hgate : hfield.gradientW1Infinity ≤
      (responseSensitivityConst d)⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (X : BlockVec d) :
    blockVecDot X
        (blockMatVecMul
          (Book.Ch02.coarseBlockMatrix (cubeDomain (originCube d 0)) am) X) ≤
      (1 + δ + responseSensitivityConst d * hfield.gradientW1Infinity *
            (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
          (blockVecDot (blockMatVecMul (blockGauge (-hbar)) X)
              (blockMatVecMul
                (Book.Ch02.coarseBlockMatrix (cubeDomain (originCube d 0)) a)
                (blockMatVecMul (blockGauge (-hbar)) X)) +
            2 * vecDot X.1 X.2) +
        2 * (responseSensitivityConst d * δ⁻¹ *
          (vecNormSq X.1 * hfield.w1Infinity ^ 2 *
              (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ +
            |vecDot X.1 X.2| * hfield.gradientW1Infinity ^ 2 *
              (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ ^ 2)) -
        2 * vecDot X.1 X.2 := by
  have hnormsq : vecNormSq (-X.1) = vecNormSq X.1 := by
    show vecDot (-X.1) (-X.1) = vecDot X.1 X.1
    rw [vecDot_neg_left, vecDot_neg_right, neg_neg]
  have hpair : vecDot (-X.1) (X.2 - matVecMul hbar X.1) = -vecDot X.1 X.2 := by
    rw [vecDot_neg_left, vecDot_sub_right,
      vecDot_matVecMul_self_eq_zero_of_transpose_eq_neg hskew X.1, sub_zero]
  have hb := (responseJ_sensitivity_const dimension).2 a hfield hgate
    (-X.1) (X.2 - matVecMul hbar X.1) δ hδ hδ1
  rw [hnormsq, hpair, abs_neg] at hb
  have h1 :=
    blockVecDot_coarseBlockMatrix_eq_two_responseJ_sub_const_skew hskew hshift X
  have h3 := blockVecDot_coarseBlockMatrix_blockGauge_eq_two_responseJ_sub
    (cubeDomain (originCube d 0)) a hskew X
  calc blockVecDot X
        (blockMatVecMul
          (Book.Ch02.coarseBlockMatrix (cubeDomain (originCube d 0)) am) X)
      = 2 * responseJ (cubeDomain (originCube d 0))
            (perturbCoeffOn (cubeDomain (originCube d 0)) a
              hfield.toLInfSkewMatrixFieldOn 1)
            (-X.1) (X.2 - matVecMul hbar X.1) -
          2 * vecDot X.1 X.2 := h1
    _ ≤ 2 * ((1 + δ + responseSensitivityConst d * hfield.gradientW1Infinity *
              (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
            responseJ (cubeDomain (originCube d 0)) a (-X.1)
              (X.2 - matVecMul hbar X.1) +
          responseSensitivityConst d * δ⁻¹ *
            (vecNormSq X.1 * hfield.w1Infinity ^ 2 *
                (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ +
              |vecDot X.1 X.2| * hfield.gradientW1Infinity ^ 2 *
                (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ ^ 2)) -
        2 * vecDot X.1 X.2 := by linarith
    _ = _ := by rw [h3]; ring

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
