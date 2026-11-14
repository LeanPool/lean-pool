/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenLoadFold
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.Step5Basket

/-!
# GammaTenAssemblyMoments

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `L^p` side conditions of the Step-2 grid Hoelder fold, from three `L^4` legs

ABK26, Step 2 of `l.approximate.recurrence.formula`.

## The gap this module fills

`Closure.GammaTenLoadFold.cubeFamilyAverage_integral_fold_le_gridLoad` carries
**eight** analytic side conditions per cell --- the six `L^p` memberships

```
  F_R^2, G_R^2, H_R^2 in L^2 ,   H_R in L^4 ,   F_R G_R in L^2 ,  F_R H_R in L^2
```

and the two integrabilities of the products H` H` --- which its own docstring
records as "conditional A obligations, discharged by the caller at its
carrier".  Every one of them is a consequence of the single natural hypothesis
a moment producer delivers:

```
  F_R , G_R , H_R  in  L^4(mu)   for each cell R of the grid.
```

This module supplies the `L^p` bookkeeping that carries out that reduction.  It
is applied at the fold in
`Closure.GammaTenStripAssembly.cubeFamilyAverage_integral_fold_le_of_memLp_four_grid_load`,
so that a consumer of Step 2 has to produce three `L^4` legs and three moment
bounds, not eleven propositions.

## What is proved

* `holderTriple_four_four_two` --- the exponent arithmetic `4^{-1} + 4^{-1} =
  2^{-1}` that Hoelder needs to multiply two `L^4` functions into `L^2`.
* `memLp_ofRealTwo_mul_of_memLp_four` --- `f g in L^2` from `f, g in L^4`.
* `integrable_mul_mul_of_memLp_four` --- `f g h in L^1` from `f, g, h in L^4` on
  a finite measure (Hoelder twice: `L^4 x L^4 -> L^2`, then `L^2 x L^2 -> L^1`).
* `memLp_ofRealTwo_rpow_two_of_memLp_four` --- `f^2 in L^2` from `f in L^4`,
  which is the shape three of the fold's six membership binders take.

The capstone that consumes all of these is
`Closure.GammaTenStripAssembly.cubeFamilyAverage_integral_fold_le_of_memLp_four_grid_load`:
the grid Hoelder fold of Step 2 with its eight side conditions replaced by the
three `L^4` legs, the three *moment* hypotheses (`hell`, `hload`, `hosc`) and
the numerical gate `hthr` passed straight through, and the load leg read in the
**grid** fourth-moment-root form that
`Closure.GammaTenLoad.exists_gammaTenLoadConst_root` delivers.

## Where the three `L^4` legs come from

* **`F` (ellipticity).**  The bound `hell` is
  `LocalizationFluctuationSplitFoldArithmetic.exists_regime_gaugedEllipticitySum_pow_four_le`
  (`E[F^4] <= cgamma^{-8}`, whose fourth root is `cgamma^{-2}` by
  `Closure.GammaTenGridFold.rpowFourRoot_le_inv_sq_of_integral_rpow_four_le`);
  the membership is the sample measurability of the gauged ellipticity sum,
  proved at the origin cube as
  `LocalizationFluctuationNumericEllipticity.measurable_gaugedEllipticitySum_originCube`.
* **`G` (load).**  Both the bound and the membership are the load fourth moment
  of the parallel producer lane.
* **`H` (oscillation).**  The membership and the grid bound come from the
  pathwise Besov envelope of `Closure.GammaTenEnvelope` fed by the annealed
  depth fold, i.e. from the depth-seminorm measurability and the per-depth
  annealed input of the parallel producer lane.

None of those is assumed here: this module is pure `L^p` bookkeeping.

## Binders

Pointwise nonnegativity where a real power is taken, and `L^4` membership of
the factors.  The measure is a probability measure, as everywhere in Step 2.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2,
  `e.lower.bound.localization.terms`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The exponent arithmetic -/

/-- `4^{-1} + 4^{-1} = 2^{-1}` in `ℝ≥0∞`: the Hoelder triple that multiplies two
`L^4` functions into `L^2`. -/
theorem holderTriple_four_four_two : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
  refine ⟨?_⟩
  have h2ne : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h4 : (4 : ℝ≥0∞) = 2 * 2 := by norm_num
  rw [h4, ENNReal.mul_inv (Or.inl h2ne) (Or.inl h2top), ← two_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel h2ne h2top, one_mul]

private theorem gammaTenMoments_ofReal_two : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
  simp [ENNReal.ofReal_ofNat]

section Sample

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## The three memberships -/

/-- **The square of a nonnegative `L^4` function lies in `L^2`,** in the `ENNReal.ofReal
2` spelling the grid fold reads. -/
theorem memLp_ofRealTwo_rpow_two_of_memLp_four {mu : Measure Omega} {f : Omega → ℝ}
    (hf : ∀ w, 0 ≤ f w) (hfm : MemLp f 4 mu) :
    MemLp (fun w => f w ^ (2 : ℝ)) (ENNReal.ofReal 2) mu := by
  rw [gammaTenMoments_ofReal_two]
  exact memLp_two_rpow_two_of_memLp_four hf hfm

/-- **The product of two `L^4` functions lies in `L^2`,** in the `ENNReal.ofReal 2`
spelling the grid fold reads. -/
theorem memLp_ofRealTwo_mul_of_memLp_four {mu : Measure Omega} {f g : Omega → ℝ}
    (hfm : MemLp f 4 mu) (hgm : MemLp g 4 mu) :
    MemLp (fun w => f w * g w) (ENNReal.ofReal 2) mu := by
  have := holderTriple_four_four_two
  rw [gammaTenMoments_ofReal_two]
  exact hfm.fun_mul (r := 2) hgm

/-- **The product of three `L^4` functions is integrable** on a finite measure:
Hoelder twice, `L^4 x L^4 -> L^2` and then `L^2 x L^2 -> L^1`. -/
theorem integrable_mul_mul_of_memLp_four {mu : Measure Omega} [IsFiniteMeasure mu]
    {f g h : Omega → ℝ} (hfm : MemLp f 4 mu) (hgm : MemLp g 4 mu) (hhm : MemLp h 4 mu) :
    Integrable (fun w => f w * g w * h w) mu := by
  have := holderTriple_four_four_two
  have hfg : MemLp (fun w => f w * g w) 2 mu := hfm.fun_mul (r := 2) hgm
  have hh2 : MemLp h 2 mu := hhm.mono_exponent (by norm_num)
  exact hfg.integrable_mul hh2

end Sample

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
