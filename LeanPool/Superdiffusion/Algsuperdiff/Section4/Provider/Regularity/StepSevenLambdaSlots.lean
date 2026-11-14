/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenLambdaGoodEvent
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenCaccMatching
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenWireCgMatching

/-!
# StepSevenLambdaSlots

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 7b: the derived-slot table

## The target

The derived-slot table: from clause (A) (`StepSevenLambdaStability.lean`) and
clause (B) (`StepSevenLambdaGoodEvent.lean`) alone, every §4.4 λ/Λ slot follows
by index monotonicity and `λ ≤ Λ`.  The four slots, all on the inner cube
`□_{k-1}` (the Step-7a sandwich's `y' + □_{k'-1}` in the lattice-aligned
reading) against the outer `□_k` (`z + □_{k'}`), are:

| # | slot | consumer | constant proved here |
|---|---|---|---|
| 1 | `λ_{1/8,2}^{-1}(□_{k-1}) ≤ Clam σ^{-1}` |'s `hlambda` | `Clam = (32/7)·CB` |
| 2 | `λ_{1/8,1}(□_{k-1}) ≤ Clam σ`  |'s Cacc. L² leg | `(256/63)·CB` |
| 3 | `λ_{1/8,1}^{-1}(□_{k-1}) ≤ C σ^{-1}`  |'s Cacc. data leg | `(64/7)·CB` |
| 4 | `Θ_{1/4,1/8}(□_{k-1}) ≤ C`  | the `Theta0` cap | `(16384/441)·²` |

(row 1's consumer is `stepSevenCgLamInv`; row 4's is the `Theta0` binder of
`StepSevenCaccMatching.stepSevenCaccPrefactor_le`.)

Row 4 is the one that matters structurally: **the comparators cancel**.  The
`Λ` leg carries `σ` and the `λ^{-1}` leg carries `σ^{-1}`, so their product
is `σ·σ^{-1} = 1` and `Θ_{1/4,1/8}` is a pure dimensional constant.  That cancellation is
machine-verified below (`stepSevenThetaRatio_le_of_caps`), not asserted.

## The prefactor arithmetic (all three values machine-checked)

At `s* = 1/16` and `C = 2` the printed prefactor `C(1-2s*)^{-1}(t/(t-s*))^{2/q}`
has coefficient `2/(1-1/8) = 16/7` and takes the values

```text
  t = 1/8, q = 2 :   (16/7)·(2)^1     = 32/7    (row 1)
  t = 1/4, q = 1 :   (16/7)·(4/3)^2   = 256/63  (rows 2 and 4's Λ leg)
  t = 1/8, q = 1 :   (16/7)·(2)^2     = 64/7    (rows 3 and 4's λ leg)
```

and row 4's constant is `(256/63)·(64/7)·² = (16384/441)·²`.

## References

* ABK26, `e.lambda.stability.applied`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## 1. `rpow` at integer exponents, in the `Real.rpow` head form -/

private theorem rpow_one_eq (x : ℝ) : Real.rpow x (1 : ℝ) = x := Real.rpow_one x

private theorem rpow_two_eq (x : ℝ) : Real.rpow x (2 : ℝ) = x ^ (2 : ℕ) := by
  have h := Real.rpow_natCast x 2
  have hc : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [hc] at h
  exact h

/-! ## 2. The three prefactor values -/

/-- The printed prefactor at `(t, q) = (1/8, 2)` — row 1's constant. -/
theorem stepSevenStabilityPrefactor_cg :
    stepSevenStabilityPrefactor stepSevenStabilityConst stepSevenStabilityIndex
        (stepSevenCgS / 2) (.finite 2) = 32 / 7 := by
  have hbase :
      stepSevenCgS / 2 / (stepSevenCgS / 2 - stepSevenStabilityIndex) = 2 := by
    rw [stepSevenCgS_eq, stepSevenStabilityIndex_eq]; norm_num
  have hexp : (2 : ℝ) / 2 = 1 := by norm_num
  rw [stepSevenStabilityPrefactor, stepSevenStabilityExponentFactor_finite, hbase,
    hexp, rpow_one_eq, stepSevenStabilityConst_eq, stepSevenStabilityIndex_eq]
  norm_num

/-- The printed prefactor at `(t, q) = (1/4, 1)` — the `Λ` leg of rows 2 and 4. -/
theorem stepSevenStabilityPrefactor_caccS :
    stepSevenStabilityPrefactor stepSevenStabilityConst stepSevenStabilityIndex
        stepSevenCaccS (.finite 1) = 256 / 63 := by
  have hbase :
      stepSevenCaccS / (stepSevenCaccS - stepSevenStabilityIndex) = 4 / 3 := by
    rw [stepSevenCaccS_eq, stepSevenStabilityIndex_eq]; norm_num
  have hexp : (2 : ℝ) / 1 = 2 := by norm_num
  rw [stepSevenStabilityPrefactor, stepSevenStabilityExponentFactor_finite, hbase,
    hexp, rpow_two_eq, stepSevenStabilityConst_eq, stepSevenStabilityIndex_eq]
  norm_num

/-- The printed prefactor at `(t, q) = (1/8, 1)` — the `λ` leg of rows 3 and 4. -/
theorem stepSevenStabilityPrefactor_caccT :
    stepSevenStabilityPrefactor stepSevenStabilityConst stepSevenStabilityIndex
        stepSevenCaccT (.finite 1) = 64 / 7 := by
  have hbase :
      stepSevenCaccT / (stepSevenCaccT - stepSevenStabilityIndex) = 2 := by
    rw [stepSevenCaccT_eq, stepSevenStabilityIndex_eq]; norm_num
  have hexp : (2 : ℝ) / 1 = 2 := by norm_num
  rw [stepSevenStabilityPrefactor, stepSevenStabilityExponentFactor_finite, hbase,
    hexp, rpow_two_eq, stepSevenStabilityConst_eq, stepSevenStabilityIndex_eq]
  norm_num

/-! ## 3. The naming trap: `stepSevenCgLamInv` IS the inverse -/

/-- **`stepSevenCgLamInv Q a s = λ_{s/2,2}^{-1}(Q; a)`**, with the `rpow (-1)` of
the definition read as an honest inverse. -/
theorem stepSevenCgLamInv_eq_inv (Q : TriadicCube d)
    (a : CoeffFamily d) (s : ℝ) :
    stepSevenCgLamInv Q a s =
      (Ch02.lambdaSq Q (s / 2) (Ch02.MultiscaleExponent.finite 2) a)⁻¹ := by
  have hc :
      Real.rpow (Ch02.lambdaSq Q (s / 2) (Ch02.MultiscaleExponent.finite 2) a)
          (((-1 : ℤ) : ℝ)) =
        (Ch02.lambdaSq Q (s / 2) (Ch02.MultiscaleExponent.finite 2) a) ^ (-1 : ℤ) :=
    Real.rpow_intCast _ (-1)
  have hcast : ((-1 : ℤ) : ℝ) = (-1 : ℝ) := by norm_num
  rw [hcast] at hc
  rw [stepSevenCgLamInv, hc, zpow_neg_one]

/-! ## 4. The index inequalities of the table -/

theorem stepSevenStabilityIndex_lt_cgHalf :
    stepSevenStabilityIndex < stepSevenCgS / 2 := by
  rw [stepSevenStabilityIndex_eq, stepSevenCgS_eq]; norm_num

theorem stepSevenStabilityIndex_lt_caccS :
    stepSevenStabilityIndex < stepSevenCaccS := by
  rw [stepSevenStabilityIndex_eq, stepSevenCaccS_eq]; norm_num

theorem stepSevenStabilityIndex_lt_caccT :
    stepSevenStabilityIndex < stepSevenCaccT := by
  rw [stepSevenStabilityIndex_eq, stepSevenCaccT_eq]; norm_num

/-- **Row 1 of the derived-slot table.**  From clause (A) at `(t,q) = (1/8,2)`
and clause (B),

```text
  λ_{1/8,2}^{-1}(□_{k-1}; a) ≤ (32/7)·CB · σ^{-1} ,
```

which is the `hlambda` slot at `Clam := (32/7)·CB` and `shomMp := σ^{-1}`. -/
theorem stepSevenCgLamInv_le_of_caps [NeZero d] {k : ℤ} (a : CoeffFamily d)
    {sigma CB : ℝ}
    (hcaps : StepSevenLambdaCaps (originCube d k) a sigma CB) :
    stepSevenCgLamInv (originCube d (k - 1)) a stepSevenCgS ≤
      (32 / 7 * CB) * sigma⁻¹ := by
  have hstab :=
    (stepSevenLambdaStability_centreChild (d := d)
      (q := Ch02.MultiscaleExponent.finite 2) k a
      stepSevenStabilityIndex_lt_cgHalf (by norm_num)).1
  rw [stepSevenStabilityPrefactor_cg] at hstab
  rw [stepSevenCgLamInv_eq_inv]
  calc
    (Ch02.lambdaSq (originCube d (k - 1)) (stepSevenCgS / 2)
        (Ch02.MultiscaleExponent.finite 2) a)⁻¹
        ≤ 32 / 7 *
          (Ch02.lambdaSq (originCube d k) stepSevenStabilityIndex
            (Ch02.MultiscaleExponent.finite 2) a)⁻¹ := hstab
    _ ≤ 32 / 7 * (CB * sigma⁻¹) :=
        mul_le_mul_of_nonneg_left hcaps.lambdaInv_two (by norm_num)
    _ = (32 / 7 * CB) * sigma⁻¹ := by ring

/-! ## 6. Rows 2 and 3: the Caccioppoli slots -/

/-- **The `Λ` leg at `(t,q) = (1/4,1)`**: `Λ_{1/4,1}(□_{k-1}; a) ≤ (256/63)··σ`. -/
theorem stepSevenLambdaS_le_of_caps [NeZero d] {k : ℤ} (a : CoeffFamily d)
    {sigma CB : ℝ}
    (hcaps : StepSevenLambdaCaps (originCube d k) a sigma CB) :
    Ch02.LambdaS (originCube d (k - 1)) stepSevenCaccS a ≤
      (256 / 63 * CB) * sigma := by
  have hstab :=
    (stepSevenLambdaStability_centreChild (d := d)
      (q := Ch02.MultiscaleExponent.finite 1) k a
      stepSevenStabilityIndex_lt_caccS (by norm_num)).2
  rw [stepSevenStabilityPrefactor_caccS] at hstab
  rw [Ch02.LambdaS]
  calc
    Ch02.LambdaSq (originCube d (k - 1)) stepSevenCaccS
        (Ch02.MultiscaleExponent.finite 1) a
        ≤ 256 / 63 *
          Ch02.LambdaSq (originCube d k) stepSevenStabilityIndex
            (Ch02.MultiscaleExponent.finite 1) a := hstab
    _ ≤ 256 / 63 * (CB * sigma) :=
        mul_le_mul_of_nonneg_left hcaps.Lambda_one (by norm_num)
    _ = (256 / 63 * CB) * sigma := by ring

/-- **Row 2 of the derived-slot table.**  `λ ≤ Λ` at the two indices then gives

```text
  λ_{1/8,1}(□_{k-1}; a) ≤ (256/63)·CB · σ .
``` -/
theorem stepSevenLambdaS_lower_le_of_caps [NeZero d] {k : ℤ} (a : CoeffFamily d)
    {sigma CB : ℝ}
    (hcaps : StepSevenLambdaCaps (originCube d k) a sigma CB) :
    Ch02.lambdaS (originCube d (k - 1)) stepSevenCaccT a ≤
      (256 / 63 * CB) * sigma :=
  le_trans
    (ExcessDecay.lambdaS_le_LambdaS (originCube d (k - 1)) a stepSevenCaccS_pos
      stepSevenCaccT_pos)
    (stepSevenLambdaS_le_of_caps a hcaps)

/-- **Row 3 of the derived-slot table.**  From clause (A) at `(t,q) = (1/8,1)`
and clause (B),

```text
  λ_{1/8,1}^{-1}(□_{k-1}; a) ≤ (64/7)·CB · σ^{-1} .
``` -/
theorem stepSevenLambdaS_inv_le_of_caps [NeZero d] {k : ℤ} (a : CoeffFamily d)
    {sigma CB : ℝ}
    (hcaps : StepSevenLambdaCaps (originCube d k) a sigma CB) :
    (Ch02.lambdaS (originCube d (k - 1)) stepSevenCaccT a)⁻¹ ≤
      (64 / 7 * CB) * sigma⁻¹ := by
  have hstab :=
    (stepSevenLambdaStability_centreChild (d := d)
      (q := Ch02.MultiscaleExponent.finite 1) k a
      stepSevenStabilityIndex_lt_caccT (by norm_num)).1
  rw [stepSevenStabilityPrefactor_caccT] at hstab
  rw [Ch02.lambdaS]
  calc
    (Ch02.lambdaSq (originCube d (k - 1)) stepSevenCaccT
        (Ch02.MultiscaleExponent.finite 1) a)⁻¹
        ≤ 64 / 7 *
          (Ch02.lambdaSq (originCube d k) stepSevenStabilityIndex
            (Ch02.MultiscaleExponent.finite 1) a)⁻¹ := hstab
    _ ≤ 64 / 7 * (CB * sigma⁻¹) :=
        mul_le_mul_of_nonneg_left hcaps.lambdaInv_one (by norm_num)
    _ = (64 / 7 * CB) * sigma⁻¹ := by ring

/-! ## 7. Row 4: the `Θ` cap, and the cancellation of the comparators -/

/-- **Row 4 of the derived-slot table — the `Θ` cap is a pure dimensional
constant.**

```text
  Θ_{1/4,1/8}(□_{k-1}; a) ≤ (16384/441)·CB² .
```

The `σ` of the `Λ` leg and the `σ^{-1}` of the `λ` leg cancel; the
cancellation is performed explicitly below.  This is the `Theta0` of
`stepSevenCaccPrefactor_le`. -/
theorem stepSevenThetaRatio_le_of_caps [NeZero d] {k : ℤ} (a : CoeffFamily d)
    {sigma CB : ℝ} (hsigma : 0 < sigma)
    (hcaps : StepSevenLambdaCaps (originCube d k) a sigma CB) :
    Ch02.ThetaRatio (originCube d (k - 1)) stepSevenCaccS stepSevenCaccT a ≤
      16384 / 441 * CB ^ (2 : ℕ) := by
  have hTheta :=
    ExcessDecay.thetaRatio_le_of_caps (originCube d (k - 1)) a stepSevenCaccS_pos
      stepSevenCaccT_pos (stepSevenLambdaS_le_of_caps a hcaps)
      (stepSevenLambdaS_inv_le_of_caps a hcaps)
  have hcancel : sigma * sigma⁻¹ = 1 := mul_inv_cancel₀ hsigma.ne'
  have hprod :
      ((256 / 63 * CB) * sigma) * ((64 / 7 * CB) * sigma⁻¹) =
        16384 / 441 * CB ^ (2 : ℕ) := by
    calc ((256 / 63 * CB) * sigma) * ((64 / 7 * CB) * sigma⁻¹)
        = (256 / 63 * CB) * (64 / 7 * CB) * (sigma * sigma⁻¹) := by ring
      _ = (256 / 63 * CB) * (64 / 7 * CB) * 1 := by rw [hcancel]
      _ = 16384 / 441 * CB ^ (2 : ℕ) := by ring
  rwa [hprod] at hTheta

end

end Algsuperdiff.Section4.Provider.Regularity
