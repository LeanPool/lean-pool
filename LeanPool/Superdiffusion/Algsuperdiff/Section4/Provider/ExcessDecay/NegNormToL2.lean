/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Support.Book.Ch03.Theorems.CoarseCaccioppoliRHS.Theory

/-!
# NegNormToL2

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The negative-norm-to-`L²` step: the `L²` distance from the negative fractional norm

ABK26's Step 1 closes with the two-step chain

```text
  ‖u - v‖_{L²(x+□_n)} ≤ C ‖∇u - ∇v‖_{H_hat^{-1}(x+□_n)}
                       ≤ C 3^{(1 - s/2)n} ‖∇u - ∇v‖_{H_hat^{-s/2}(x+□_n)} ,
```

for `u - v ∈ H¹₀(x+□_n)`, whose second inequality the graph records as an
unexplained "Besov-scale comparison on a cube of side `3^n`".

**Finding: CoarseGraining proves the whole chain in one theorem, and the
printed scale factor comes out exactly.**  The theorem is

```text
  cubeBesovScaleWeight 1 Q · ‖u‖_{L²(Q)}
      ≤ C(d) · sqrt((1 - 3^{-2(1/2 - t)})⁻¹) · [∇u]_{B^{-2t}_{2,2}(Q)}
```

(`Homogenization.Book.Ch03.cubeBesovScaleWeight_one_mul_cubeLpNorm_h10_le_grad_`
`negativeBesovTwo`, for `u ∈ H¹₀(cubeSet Q)` and `0 < t < 1/2`).  Since
`cubeBesovScaleWeight 1 Q = 3^{-Q.scale}` and CoarseGraining's negative
seminorm carries the manuscript's own outer normalization `3^{-σ·scale}`, the
conclusion reads

```text
  ‖u‖_{L²(□_n)} ≤ C(d) 3^{n} · 3^{-2tn} [∇u]_{H_hat^{-2t}(□_n)}
                = C(d) 3^{(1-2t)n} [∇u]_{H_hat^{-2t}(□_n)} ,
```

No separate `H_hat^{-1} ← H_hat^{-s/2}` comparison is needed: the two printed
inequalities are one theorem.

This module contributes the two bounded pieces:

* `negNormSqrtFactor_le_two`: at `t = s/4` and `s ≤ 1` the analytic factor
  `sqrt((1 - 3^{-2(1/2 - s/4)})⁻¹)` is at most `2` — so the whole constant is
  `C(d)`, as printed;
* `cubeLpNorm_h10_le_negativeBesov_quarter`: the specialization at `t = s/4`,
  with the negative index displayed as `s/2` and the analytic factor absorbed.

## The norm on the right is the manuscript's own substitute (recorded)

CoarseGraining's right-hand object is the **concrete** block-average negative
seminorm `B^{-σ}_{2,2}`, not the hatted `H_hat^{-σ}` the display prints.  The
manuscript itself performs exactly this substitution — records
`‖·‖_{H_hat^{-s}(□)} ≤ C ‖·‖_{B^{-s}_{2,2}(□)} ≤ C ‖·‖_{B^{-s}_{2,1}(□)}` — so
the inequality below is the printed one with the printed norm replaced by the
dominating one, i.e. a *weaker* statement per step.  The composition with the
coarse-graining leg must therefore be made at the
`B^{-σ}_{2,2}` level, which is also the level at which CoarseGraining's
coarse-graining machinery produces its bounds.  Nothing here claims the hatted
norm.

## What is still missing (disclosed frontier)

The frozen theorem's left-hand side is `eLpNorm (u - v) 2
(normalizedVolumeMeasureOn ((x + □_n) image))`, on an **off-grid** window,
while CoarseGraining's theorem is stated at a triadic cube in the
`cubeSet`/`cubeLpNorm` carriers.  Two bridges therefore remain, neither of them
attempted here: the `normalizedVolumeMeasureOn`-vs-`normalizedCubeMeasure`
identification on the open/closed cube pair, and the A4 frame change (this leg
lives naturally in the frame translated by `x`, while the energy leg lives in
the frame translated by `z`).

## References

* ABK26, `l.harmonic.approximation.good.scales`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The analytic factor at `t = s/4` -/

/-- `3^{-1/2} ≤ 3/4`, via `√3 ≥ 4/3`. -/
private theorem rpow_three_neg_half_le : Real.rpow (3 : ℝ) (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
  have hsqrt3 : (4 : ℝ) / 3 ≤ Real.sqrt 3 := by
    have hstep : ((4 : ℝ) / 3) ^ 2 ≤ (3 : ℝ) := by norm_num
    calc (4 : ℝ) / 3 = Real.sqrt (((4 : ℝ) / 3) ^ 2) :=
          (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 3 := Real.sqrt_le_sqrt hstep
  rw [Real.rpow_eq_pow, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.sqrt_eq_rpow]
  have h := inv_anti₀ (show (0 : ℝ) < 4 / 3 by norm_num) hsqrt3
  rw [show ((4 : ℝ) / 3)⁻¹ = 3 / 4 by norm_num] at h
  exact h

/-- The Besov-tail bracket at `t = s/4` is at least `1/4` for `s ≤ 1`. -/
private theorem one_sub_rpow_tail_ge {s : ℝ} (hs1 : s ≤ 1) :
    (1 : ℝ) / 4 ≤ 1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - s / 4)) := by
  have hmono : Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - s / 4)) ≤
      Real.rpow (3 : ℝ) (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hs1])
  linarith only [hmono, rpow_three_neg_half_le]

/-- **The Besov-tail factor is bounded by `2` on the anchor's `s`-range.** -/
theorem negNormSqrtFactor_le_two {s : ℝ} (hs1 : s ≤ 1) :
    Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - s / 4)))⁻¹) ≤ 2 := by
  have hinv : (1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - s / 4)))⁻¹ ≤ 4 := by
    have h := inv_anti₀ (show (0 : ℝ) < 1 / 4 by norm_num)
      (one_sub_rpow_tail_ge hs1)
    rw [show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num] at h
    exact h
  calc Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - s / 4)))⁻¹)
      ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hinv
    _ = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The Besov-tail factor is positive. -/
private theorem negNormSqrtFactor_pos {s : ℝ} (hs1 : s ≤ 1) :
    0 < Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - s / 4)))⁻¹) := by
  refine Real.sqrt_pos.mpr (inv_pos.mpr ?_)
  linarith only [one_sub_rpow_tail_ge hs1]

/-! ## 2. The negative-norm step at the parameter choice `t = s/4` -/

/-- The dimensional constant of CoarseGraining's zero-trace value estimate. -/
def negNormBaseConst (d : ℕ) : ℝ :=
  ((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
      (3 : ℝ) ^ ((d : ℝ) + 1) * (d : ℝ)) + 2 * (3 : ℝ) ^ ((d : ℝ) + 1)

theorem negNormBaseConst_pos (d : ℕ) [NeZero d] : 0 < negNormBaseConst d := by
  have hcz : 0 ≤ Legacy.cubeNeumannW22CalderonZygmundConstant d :=
    Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d
  have h3 : (0 : ℝ) < (3 : ℝ) ^ ((d : ℝ) + 1) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h1 : (0 : ℝ) ≤ (d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
      (3 : ℝ) ^ ((d : ℝ) + 1) * (d : ℝ) := by positivity
  rw [negNormBaseConst]
  linarith only [h1, h3]

/-- **The negative-norm-to-`L²` step at `t = s/4`.**

```text
  3^{-Q.scale} ‖u‖_{L²(Q)} ≤ 2 C(d) [∇u]_{B^{-s/2}_{2,2}(Q)}      (u ∈ H¹₀(Q)) .
```

This is the printed two-step chain, in one inequality, at the negative index
`s/2` and with the analytic tail factor discharged by
`negNormSqrtFactor_le_two`.  Nonnegativity of the right-hand seminorm is
*derived* from the inequality itself (the left side is nonnegative and the
constant is positive), so no `BddAbove` hypothesis is imposed. -/
theorem cubeLpNorm_h10_le_negativeBesov_quarter [NeZero d] (Q : TriadicCube d)
    (u : H10Function (cubeSet Q)) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    cubeBesovScaleWeight 1 Q *
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u.toH1Function.toFun x) ≤
      2 * negNormBaseConst d *
        cubeBesovNegativeVectorSeminormTwo Q (s / 2)
          (fun x => u.toH1Function.grad x) := by
  have h := cubeBesovScaleWeight_one_mul_cubeLpNorm_h10_le_grad_negativeBesovTwo
    Q u (t := s / 4) (by linarith only [hs]) (by linarith only [hs1])
  rw [show (2 : ℝ) * (s / 4) = s / 2 by ring] at h
  have hbase : 0 < negNormBaseConst d := negNormBaseConst_pos d
  have hfac := negNormSqrtFactor_pos hs1
  have hLHS : 0 ≤ cubeBesovScaleWeight 1 Q *
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u.toH1Function.toFun x) :=
    mul_nonneg (cubeBesovScaleWeight_nonneg 1 Q)
      (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) _)
  have h' : cubeBesovScaleWeight 1 Q *
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u.toH1Function.toFun x) ≤
      negNormBaseConst d *
          Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - s / 4)))⁻¹) *
        cubeBesovNegativeVectorSeminormTwo Q (s / 2)
          (fun x => u.toH1Function.grad x) := by
    rw [negNormBaseConst]
    exact h
  have hN : 0 ≤ cubeBesovNegativeVectorSeminormTwo Q (s / 2)
      (fun x => u.toH1Function.grad x) := by
    by_contra hcon
    push Not at hcon
    have hneg : negNormBaseConst d * Real.sqrt
          ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - s / 4)))⁻¹) *
        cubeBesovNegativeVectorSeminormTwo Q (s / 2)
          (fun x => u.toH1Function.grad x) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hbase hfac) hcon
    linarith only [hLHS, h', hneg]
  refine le_trans h' (mul_le_mul_of_nonneg_right ?_ hN)
  have hstep : negNormBaseConst d * Real.sqrt
        ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - s / 4)))⁻¹) ≤
      negNormBaseConst d * 2 :=
    mul_le_mul_of_nonneg_left (negNormSqrtFactor_le_two hs1) hbase.le
  linarith only [hstep]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
