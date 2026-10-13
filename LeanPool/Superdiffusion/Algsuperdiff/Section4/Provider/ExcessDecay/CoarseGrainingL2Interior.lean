/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CoarseGrainingEnvelope
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CoarseGrainingSeminormScaling
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.NegNormToL2

/-!
# CoarseGrainingL2Interior

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The interior `L²` homogenization estimate

## What is proved

ABK26's Step 1 runs the chain

```text
  ‖u - v‖_{L²(x+□_n)}  ≤  C 3^{(1-s/2)n} ‖∇u - ∇v‖_{H_hat^{-s/2}(x+□_n)}
                        ≤  C 3^{n} σ^{-1} · (coarse-graining right-hand side) ,
```

the second step being `e.homogenization.L2.interior`, i.e.
`p.general.coarse.graining` at `p = 2`, `m = n`, flux term discarded.

`coarseGraining_scaled_l2_le` below is that chain in one inequality, at
CoarseGraining's carriers and with CoarseGraining's own right-hand side;
and the §4.3 slot reads it with every
constant explicit.  The comparator `σ₀` stays on the **left**, exactly as the
printed display writes it (`3^{-sn/2} σ_n ‖∇u − ∇v‖`); dividing by `σ₀` is
left to the consumer.

Note that the scale factor is `3^{-Q.scale}` on the left and **carries no
`s`-dependence**: CoarseGraining's negative Besov seminorm is scale-normalized,
so the printed `3^{(1-s/2)n}` and the exponent choice below differ only inside
the normalization and cancel.  Consequently the comparison exponent enters the
final bound *only* through the factor `s_prop⁻¹`.

## Honest exponents (reported)

No `γ`-exponent is touched anywhere.  See `CoarseGrainingEnvelope.lean` for the
term-by-term account.

## What this leg does NOT do

* The window here is a **triadic** cube `Q`.  §4.3 applies the estimate on the
  off-grid cube `x+□_n`; under the development's A4 convention that window is
  the origin cube `□_n` read in the `x`-translated frame, so the statement
  below is the right one — but the resulting error `𝓔(□_n; ã, σ)` then lives
  in the `x`-frame while the anchor's right-hand side carries `𝓔(□_{n+2}; ã,
  σ)` in the `z`-frame.  Nothing here assumes it.
* Consequently the good-event caps (`GoodEventCaps.lean`) are **not** applied
  here: they are stated at `□_{n+2}` in the `z`-frame.
* The `H¹₀` witness and the pointwise gradient identity are taken as given —
  they are the anchor's own binders (`v = u - w`, `∇v = ∇u - ∇w`).
* `w.v` is the auxiliary solution `v_g` of the *forced* constant-coefficient
  problem, not the harmonic replacement `v`; the passage `v_g → v` is the
  forcing correction, carried out in `ReplacementDatumHarmonic.lean`.

## References

* ABK26, `l.harmonic.approximation.good.scales`.
* ABK26, `p.general.coarse.graining`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The composed estimate -/

/-- **The interior `L²` homogenization estimate.**

For a coarse-graining datum `w` on the triadic cube `Q` with scalar background
`σ₀ Id`, and an `H¹₀` function `z` whose gradient is `∇u − ∇v`:

```text
  σ₀ · 3^{-Q.scale} ‖z‖_{L²(Q)}
      ≤ C(d) · sqrt((1 - 3^{-2(1/2 - t)})⁻¹)
          · generalCoarseGrainingL2TwoExponentRHS (coarseGrainingP2Const d) …
```

at comparison exponent `2t`.  This is the negative-norm-to-`L²` step composed
with the interior estimate, with the flux summand discarded. -/
theorem coarseGraining_scaled_l2_le [NeZero d] {Q : TriadicCube d}
    {a : Ch03.CoeffFamily d} {sigma0 : ℝ} (hsigma0 : 0 < sigma0)
    {g : Vec d → Vec d}
    (w : Ch03.CoarseGrainingComparisonDatum Q a (scalarComparator hsigma0) g)
    (z : H10Function (cubeSet Q))
    (hz : ∀ x, z.toH1Function.grad x = w.u.grad x - w.v.grad x)
    {t r r₂ : ℝ} {j : ℕ} (ht : 0 < t) (ht1 : t < 1 / 2) (hr : 0 < r) (hrt : r < t)
    (hr₂ : r ≤ r₂) (hg : Ch03.ForceBesovRegularity Q r₂ g) :
    sigma0 * (cubeBesovScaleWeight (1 : ℝ) Q *
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => z.toH1Function.toFun x)) ≤
      negNormBaseConst d *
          Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - t)))⁻¹) *
        Ch03.generalCoarseGrainingL2TwoExponentRHS (coarseGrainingP2Const d) Q a
          (scalarComparator hsigma0) (2 * t) r r₂ j g w.u := by
  set K : ℝ := negNormBaseConst d *
    Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - t)))⁻¹) with hKdef
  have hK : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg (negNormBaseConst_pos d).le (Real.sqrt_nonneg _)
  have hneg : cubeBesovScaleWeight (1 : ℝ) Q *
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => z.toH1Function.toFun x) ≤
      K * cubeBesovNegativeVectorSeminormTwo Q (2 * t)
        (fun x => z.toH1Function.grad x) := by
    rw [hKdef, negNormBaseConst]
    exact Ch03.cubeBesovScaleWeight_one_mul_cubeLpNorm_h10_le_grad_negativeBesovTwo Q z ht ht1
  have hfield : Ch03.homogenizationComparisonConstantGradientField
        (scalarComparator hsigma0) w.u w.v = fun x => sigma0 • z.toH1Function.grad x := by
    funext x
    show matVecMul (scalarComparator hsigma0).matrix (w.u.grad x - w.v.grad x) =
      sigma0 • z.toH1Function.grad x
    rw [scalarComparator_matrix, matVecMul_scalarMatrix, hz x]
  have hhom : sigma0 * cubeBesovNegativeVectorSeminormTwo Q (2 * t)
        (fun x => z.toH1Function.grad x) =
      cubeBesovNegativeVectorSeminormTwo Q (2 * t)
        (Ch03.homogenizationComparisonConstantGradientField
          (scalarComparator hsigma0) w.u w.v) := by
    rw [hfield, cubeBesovNegativeVectorSeminormTwo_smul Q (2 * t) hsigma0.le]
  calc sigma0 * (cubeBesovScaleWeight (1 : ℝ) Q *
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => z.toH1Function.toFun x))
      ≤ sigma0 * (K * cubeBesovNegativeVectorSeminormTwo Q (2 * t)
          (fun x => z.toH1Function.grad x)) :=
        mul_le_mul_of_nonneg_left hneg hsigma0.le
    _ = K * (sigma0 * cubeBesovNegativeVectorSeminormTwo Q (2 * t)
          (fun x => z.toH1Function.grad x)) := by ring
    _ = K * cubeBesovNegativeVectorSeminormTwo Q (2 * t)
          (Ch03.homogenizationComparisonConstantGradientField
            (scalarComparator hsigma0) w.u w.v) := by rw [hhom]
    _ ≤ K * Ch03.homogenizationComparisonNegativeBesovLHS Q a
          (scalarComparator hsigma0) (2 * t) w.u w.v :=
        mul_le_mul_of_nonneg_left
          (constantGradientSeminorm_le_comparisonLHS Q a (scalarComparator hsigma0)
            (2 * t) w.u w.v) hK
    _ ≤ K * Ch03.generalCoarseGrainingL2TwoExponentRHS (coarseGrainingP2Const d) Q a
          (scalarComparator hsigma0) (2 * t) r r₂ j g w.u :=
        mul_le_mul_of_nonneg_left
          (coarseGrainingP2_estimate (scalarComparator_isPositiveScalarMatrix hsigma0) w
            (by linarith only [ht]) hr (by linarith only [hrt])
            (by linarith only [ht1]) hr₂ hg) hK

/-! ## 2. The analytic tail factor at the slot -/

/-- `3^{-1/4} ≤ 4/5`. -/
private theorem rpow_three_neg_quarter_le : Real.rpow (3 : ℝ) (-(1 / 4 : ℝ)) ≤ 4 / 5 := by
  have hpow : (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ))) ^ (4 : ℕ) = 1 / 3 := by
    rw [Real.rpow_eq_pow, ← Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 4 : ℝ))) 4,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      show (-(1 / 4 : ℝ)) * ((4 : ℕ) : ℝ) = -(1 : ℝ) by norm_num,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_one]
    norm_num
  refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by norm_num) ?_
  rw [hpow]
  norm_num

/-- **The Besov-tail factor at the slot exponent `t = 3s/8` is at most `3`.** -/
theorem negNormSqrtFactor_slot_le_three {s : ℝ} (hs1 : s ≤ 1) :
    Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - 3 * s / 8)))⁻¹) ≤ 3 := by
  have hmono : Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - 3 * s / 8)) ≤
      Real.rpow (3 : ℝ) (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hs1])
  have hlow : (1 : ℝ) / 5 ≤ 1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - 3 * s / 8)) := by
    linarith only [hmono, rpow_three_neg_quarter_le]
  have hinv : (1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - 3 * s / 8)))⁻¹ ≤ 5 := by
    have h := inv_anti₀ (show (0 : ℝ) < 1 / 5 by norm_num) hlow
    rw [show ((1 : ℝ) / 5)⁻¹ = 5 by norm_num] at h
    exact h
  calc Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - 3 * s / 8)))⁻¹)
      ≤ Real.sqrt 9 := Real.sqrt_le_sqrt (by linarith only [hinv])
    _ = 3 := by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
