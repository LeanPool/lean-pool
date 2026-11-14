/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.BigLambdaSensitivity
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.LambdaSensitivity
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.ResponseJSensitivity
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.Spine

/-!
# DeltaOsc

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The oscillation threshold `delta_osc`

ABK26 introduces, in `sss.bad.cubes`, a strictly positive constant `delta_osc`
depending only on the dimension, "chosen so that the coarse-grained sensitivity
estimates (Lemmas `l.lambda.sensitivity` and `l.J.sensitivity`) can be applied
when `B_osc(z + cu_j)` does not occur".  The manuscript's only quantitative
requirement is the displayed choice `e.delta.osc.choice`:

```
delta_osc  <=  2^{-10} C_{(e.J.sensitivity.smallness.condition)}^{-1} .
```

Both sensitivity lemmas are frozen and proved in this repository, and both
produce their constant existentially:
`Algsuperdiff.Frozen.Section24.lambda_sensitivity`,
`Algsuperdiff.Frozen.Section24.responseJ_sensitivity` and
`Algsuperdiff.Frozen.Section24.bigLambda_sensitivity` each assert
`exists C, 0 < C and <conditional estimate whose gate is
 h.gradientW1Infinity <= C^{-1} unitCubeLambda (3/8) 2 a>`.

## Why three Lean constants are normalized against one threshold

One constant `C`, one smallness condition, two conclusions.  The constant named
in `e.delta.osc.choice` is `C_{(e.J.sensitivity.smallness.condition)}` --- that
very constant --- and the surrounding sentence says `delta_osc` is "chosen so
that the coarse-grained sensitivity estimates (Lemmas `l.lambda.sensitivity`
and `l.J.sensitivity`) can be applied", i.e. so that *both* displays of
`l.J.sensitivity` are available on the complement of `B_osc`.

The Lean rendering splits the two displays into two frozen theorems, each with
its own existential constant, so the manuscript's single `C` becomes three
Lean constants.  The faithful reading of the single-constant convention is
therefore to normalize `delta_osc` against all three:

```
deltaOsc d := 2^{-10} * (max 1 (max (max C_lambda C_J) C_BigLambda))^{-1} ,
```

which is the manuscript's displayed expression with all the gates merged (so
that a single threshold opens every sensitivity lemma) and clamped below `1`.
All three constants, and hence `deltaOsc`, depend on nothing but `d`.

## Main definitions

* `lambdaSensitivityConst`, `responseSensitivityConst`,
  `bigLambdaSensitivityConst`: the extracted frozen constants, as functions of
  `d` alone.
* `sensitivityConstMax`: their maximum against `1`.
* `deltaOsc`: the manuscript's `delta_osc`.

## Main results

* `lambda_sensitivity_const`, `responseJ_sensitivity_const`,
  `bigLambda_sensitivity_const`: the frozen conclusions read at the extracted
  constants.
* `deltaOsc_le_two_pow_neg_ten_mul_inv_lambdaSensitivityConst`,
  `deltaOsc_le_two_pow_neg_ten_mul_inv_bigLambdaSensitivityConst`: the displayed
  choice `e.delta.osc.choice`, read against the `lambda`- and
  `Lambda`-sensitivity constants.

## References

* ABK26, `sss.bad.cubes` (`e.Bosc.def`,
  `e.delta.osc.choice`).
* ABK26, `l.lambda.sensitivity`; `l.J.sensitivity` (one constant, one smallness
  condition `e.J.sensitivity.smallness.condition`, two displays
  `e.J.sensitivity` and `e.big.Lambda.sensitivity`).
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02

noncomputable section

/-! ## Extraction of the three frozen sensitivity constants -/

/-- The constant furnished by the frozen `lambda`-sensitivity lemma, as a
function of the dimension alone.  Off the source range `2 <= d` the value is
the harmless placeholder `1`, which keeps the definition total without
affecting any statement below. -/
noncomputable def lambdaSensitivityConst (d : ℕ) : ℝ :=
  if h : 2 ≤ d then
    Classical.choose (Algsuperdiff.Frozen.Section24.lambda_sensitivity (d := d) h)
  else 1

/-- The constant furnished by the frozen response-sensitivity lemma, as a
function of the dimension alone. -/
noncomputable def responseSensitivityConst (d : ℕ) : ℝ :=
  if h : 2 ≤ d then
    Classical.choose (Algsuperdiff.Frozen.Section24.responseJ_sensitivity (d := d) h)
  else 1

/-- The constant furnished by the frozen `Lambda`-sensitivity lemma, as a
function of the dimension alone.  This is the second display
`e.big.Lambda.sensitivity` (ABK26) of the *same* lemma `l.J.sensitivity`
that produces `responseSensitivityConst`; the manuscript gives the two
displays one constant, so both are normalized against the same
`sensitivityConstMax` below. -/
noncomputable def bigLambdaSensitivityConst (d : ℕ) : ℝ :=
  if h : 2 ≤ d then
    Classical.choose (Algsuperdiff.Frozen.Section24.bigLambda_sensitivity (d := d) h)
  else 1

/-- The frozen `lambda`-sensitivity conclusion, read at the extracted
constant. -/
theorem lambda_sensitivity_const {d : ℕ} (hd : 2 ≤ d) :
    0 < lambdaSensitivityConst d ∧
      ∀ (a : CoeffOn (cubeDomain (originCube d 0)))
        (h : UnitCubeSkewW2Infinity d),
        h.gradientW1Infinity ≤ (lambdaSensitivityConst d)⁻¹ *
            unitCubeLambda (3 / 8) (.finite 2) a →
        ∀ (s : ℝ) (q : Ch02.MultiscaleExponent),
          0 < s → s ≤ 1 / 2 → q.IsAdmissible →
          (unitCubeLambda s q
            (perturbCoeffOn (cubeDomain (originCube d 0)) a
              h.toLInfSkewMatrixFieldOn 1))⁻¹
            ≤ (1 + lambdaSensitivityConst d * h.gradientW1Infinity *
                (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
              (unitCubeLambda s q a)⁻¹ := by
  have hspec := Classical.choose_spec
    (Algsuperdiff.Frozen.Section24.lambda_sensitivity (d := d) hd)
  rw [lambdaSensitivityConst, dite_eq_left hd]
  exact hspec

/-- The frozen response-sensitivity conclusion, read at the extracted
constant. -/
theorem responseJ_sensitivity_const {d : ℕ} (hd : 2 ≤ d) :
    0 < responseSensitivityConst d ∧
      ∀ (a : CoeffOn (cubeDomain (originCube d 0)))
        (h : UnitCubeSkewW2Infinity d),
        h.gradientW1Infinity ≤ (responseSensitivityConst d)⁻¹ *
            unitCubeLambda (3 / 8) (.finite 2) a →
        ∀ (p q : Vec d) (δ : ℝ), 0 < δ → δ ≤ 1 →
        responseJ (cubeDomain (originCube d 0))
            (perturbCoeffOn (cubeDomain (originCube d 0)) a
              h.toLInfSkewMatrixFieldOn 1) p q
          ≤ (1 + δ + responseSensitivityConst d * h.gradientW1Infinity *
              (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
              responseJ (cubeDomain (originCube d 0)) a p q +
            responseSensitivityConst d * δ⁻¹ *
              (vecNormSq p * h.w1Infinity ^ 2 *
                  (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ +
                |vecDot p q| * h.gradientW1Infinity ^ 2 *
                  (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ ^ 2) := by
  have hspec := Classical.choose_spec
    (Algsuperdiff.Frozen.Section24.responseJ_sensitivity (d := d) hd)
  rw [responseSensitivityConst, dite_eq_left hd]
  exact hspec

/-- The frozen `Lambda`-sensitivity conclusion, read at the extracted
constant. -/
theorem bigLambda_sensitivity_const {d : ℕ} (hd : 2 ≤ d) :
    0 < bigLambdaSensitivityConst d ∧
      ∀ (a : CoeffOn (cubeDomain (originCube d 0)))
        (h : UnitCubeSkewW2Infinity d),
        h.gradientW1Infinity ≤ (bigLambdaSensitivityConst d)⁻¹ *
            unitCubeLambda (3 / 8) (.finite 2) a →
        ∀ s : ℝ, 0 < s → s < 3 / 8 →
        unitCubeBigLambda s (.finite 2)
            (perturbCoeffOn (cubeDomain (originCube d 0)) a
              h.toLInfSkewMatrixFieldOn 1)
          ≤ 4 * unitCubeBigLambda s (.finite 2) a +
            bigLambdaSensitivityConst d * (3 / 8 - s)⁻¹ * h.w1Infinity ^ 2 *
              (unitCubeLambda s (.finite 2) a)⁻¹ := by
  have hspec := Classical.choose_spec
    (Algsuperdiff.Frozen.Section24.bigLambda_sensitivity (d := d) hd)
  rw [bigLambdaSensitivityConst, dite_eq_left hd]
  exact hspec

/-- Positivity of the extracted `lambda`-sensitivity constant. -/
theorem lambdaSensitivityConst_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < lambdaSensitivityConst d :=
  (lambda_sensitivity_const hd).1

/-- Positivity of the extracted response-sensitivity constant. -/
theorem responseSensitivityConst_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < responseSensitivityConst d :=
  (responseJ_sensitivity_const hd).1

/-- Positivity of the extracted `Lambda`-sensitivity constant. -/
theorem bigLambdaSensitivityConst_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < bigLambdaSensitivityConst d :=
  (bigLambda_sensitivity_const hd).1

/-! ## The threshold -/

/-- The largest of the three sensitivity constants, clamped below by `1`.  This
is the single constant against which `deltaOsc` is normalized, so that one
threshold opens every frozen sensitivity gate.

The three-way maximum is the faithful reading of ABK26's own single-constant
convention: `l.J.sensitivity` states its two displays `e.J.sensitivity` and
`e.big.Lambda.sensitivity` under one constant `C(d)` and one smallness condition
`e.J.sensitivity.smallness.condition`, and it is that `C` which
`e.delta.osc.choice` names.  Splitting the two displays into two frozen Lean
theorems produced two existential constants; the maximum restores the
manuscript's reading. -/
noncomputable def sensitivityConstMax (d : ℕ) : ℝ :=
  max 1 (max (max (lambdaSensitivityConst d) (responseSensitivityConst d))
    (bigLambdaSensitivityConst d))

theorem one_le_sensitivityConstMax (d : ℕ) : 1 ≤ sensitivityConstMax d :=
  le_max_left _ _

theorem sensitivityConstMax_pos (d : ℕ) : 0 < sensitivityConstMax d :=
  lt_of_lt_of_le zero_lt_one (one_le_sensitivityConstMax d)

theorem lambdaSensitivityConst_le_sensitivityConstMax (d : ℕ) :
    lambdaSensitivityConst d ≤ sensitivityConstMax d :=
  le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)

theorem responseSensitivityConst_le_sensitivityConstMax (d : ℕ) :
    responseSensitivityConst d ≤ sensitivityConstMax d :=
  le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)

theorem bigLambdaSensitivityConst_le_sensitivityConstMax (d : ℕ) :
    bigLambdaSensitivityConst d ≤ sensitivityConstMax d :=
  le_trans (le_max_right _ _) (le_max_right _ _)

/-- ABK26's dimension-only oscillation threshold `delta_osc`
(`e.Bosc.def`, `e.delta.osc.choice`). -/
noncomputable def deltaOsc (d : ℕ) : ℝ :=
  (2 : ℝ) ^ (-10 : ℤ) * (sensitivityConstMax d)⁻¹

theorem deltaOsc_pos (d : ℕ) : 0 < deltaOsc d :=
  mul_pos (by positivity) (inv_pos.2 (sensitivityConstMax_pos d))

/-- The same bound against the `lambda`-sensitivity constant, which is what
lets a single threshold open every frozen gate. -/
theorem deltaOsc_le_two_pow_neg_ten_mul_inv_lambdaSensitivityConst {d : ℕ}
    (hd : 2 ≤ d) :
    deltaOsc d ≤ (2 : ℝ) ^ (-10 : ℤ) * (lambdaSensitivityConst d)⁻¹ := by
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact inv_anti₀ (lambdaSensitivityConst_pos hd)
    (lambdaSensitivityConst_le_sensitivityConstMax d)

/-- The same bound against the `Lambda`-sensitivity constant, i.e. the displayed
choice `e.delta.osc.choice` read at the second display of `l.J.sensitivity`. -/
theorem deltaOsc_le_two_pow_neg_ten_mul_inv_bigLambdaSensitivityConst {d : ℕ}
    (hd : 2 ≤ d) :
    deltaOsc d ≤ (2 : ℝ) ^ (-10 : ℤ) * (bigLambdaSensitivityConst d)⁻¹ := by
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact inv_anti₀ (bigLambdaSensitivityConst_pos hd)
    (bigLambdaSensitivityConst_le_sensitivityConstMax d)

end

end Algsuperdiff.Section3.Provider.BadEvents
