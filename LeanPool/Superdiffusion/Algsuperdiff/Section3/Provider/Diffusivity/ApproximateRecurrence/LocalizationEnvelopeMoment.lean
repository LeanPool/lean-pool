/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.GammaSigma.Basic

/-!
# LocalizationEnvelopeMoment

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
NOTE: this module is an ordinary Provider helper / conditional A.  The binder
descriptions below are an informal inventory only.

# Provider: the second moment of an `O_{Gamma_1}(A)` variable

Source display in ABK26:

* `e.nablaw.in.L.eight` (label; display), whose last line reads `<= C +
  O_{Gamma_1}(cgamma^100)`.

## Why this module exists

`e.nablaw.in.L.eight` controls `‖grad w‖^2_{L8bar(cu_K)}` *pathwise* by a
deterministic head plus a fluctuation `Tfluct` which is only known to be
`O_{Gamma_1}(cgamma^100)`, i.e. to have a stretched-exponential upper tail at
amplitude `cgamma^100`.  The covering step of `e.lower.bound.oscillations` needs
an *annealed* fourth energy, so the fluctuation has to be squared and
integrated.  This module supplies that one probabilistic fact, with an explicit
constant, and nothing else.

## What is proved

* `gammaMomentConst_one` -- **unconditional**: CoarseGraining's moment-growth
  constant at `sigma = 1` is exactly `2 e`.  (The `max` in its definition is
  attained at `1`, because `2 / e <= 1`.)
* `integrable_sq_of_isBigOWith_gammaSigma_one` -- integrability of the square
  of an `O_{Gamma_1}(A)` variable.
* `integral_sq_le_of_isBigOWith_gammaSigma_one` -- **the second moment**:
  `E[T^2] <= (4 e A)^2`, i.e. `16 e^2 A^2`.  The chain of constants is
  `gammaMomentConst 1 * 2^{1} * A = 2 e * 2 * A = 4 e A`, squared.

## Where the constant comes from

CoarseGraining's `IndependentSums.integral_rpow_le_of_isBigOWith_gammaSigma`
gives, for `sigma > 0`, `K > 0`, `p >= 1` and a nonnegative a.e.-measurable `Y`
with `Y = O_{Gamma_sigma}(K)`,

```
  E[ Y^p ] <= ( gammaMomentConst sigma * p^{1/sigma} * K )^p .
```

At `sigma = 1`, `p = 2`, `K = A` the right-hand side is `(2 e * 2 * A)^2`.  No
step below improves or degrades that constant; it is reported as it falls out.

## What is not proved here

* **Measurability is a binder.**  `IndependentSums.IsBigOWith` is a statement
  about `mu.real` of upper-tail *sets*, which is defined for arbitrary sets, so
  it does not by itself make `T` measurable, and a non-measurable bounded `T`
  satisfies it.  Every statement below therefore carries `hTm: A T mu`
  explicitly.  For the fresh-shell fluctuation of `Corrector.FreshShellL8` this
  binder is open: that module produces `Tfluct` existentially and asserts
  nothing about its measurability.
* **`mu` must be a probability measure.**  This is an instance binder
  `[IsProbabilityMeasure mu]`, inherited from the CoarseGraining statement.

## References

* ABK26, `e.nablaw.in.L.eight` (the `O_{Gamma_1}(cgamma^100)` fluctuation).
* CoarseGraining,
  `Homogenization.IndependentSums.integral_rpow_le_of_isBigOWith_gammaSigma`
  and `integrable_rpow_of_isBigOWith_gammaSigma`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport

noncomputable section

/-! ## The moment-growth constant at `sigma = 1` -/

/-- **Unconditional.**  CoarseGraining's stretched-exponential moment-growth
constant at `sigma = 1` is exactly `2 e`: its `max` is attained at `1`, because
`2 / e <= 1`. -/
theorem gammaMomentConst_one : IndependentSums.gammaMomentConst 1 = 2 * Real.exp 1 := by
  have hexp : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hle : (2 : ℝ) / ((1 : ℝ) * Real.exp 1) ≤ 1 := by
    rw [one_mul, div_le_one hpos]
    exact hexp
  unfold IndependentSums.gammaMomentConst
  rw [inv_one, Real.rpow_one, max_eq_left hle, mul_one]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Integrability -/

/-- The square of an `O_{Gamma_1}(A)` variable is integrable.

: `[IsProbabilityMeasure mu]`, `hA`, `hT0`, `hTm`, `hT`. -/
theorem integrable_sq_of_isBigOWith_gammaSigma_one [IsProbabilityMeasure μ]
    {T : Ω → ℝ} {A : ℝ} (hA : 0 < A) (hT0 : ∀ ω, 0 ≤ T ω) (hTm : AEMeasurable T μ)
    (hT : IndependentSums.IsBigOWith μ (IndependentSums.gammaSigma 1) T A) :
    Integrable (fun ω => T ω ^ (2 : ℕ)) μ := by
  have h := IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma
    (μ := μ) (Y := T) (K := A) (σ := 1) (p := 2) one_pos hA (by norm_num) hT0 hTm hT
  have hfun : (fun ω => T ω ^ (2 : ℝ)) = fun ω => T ω ^ (2 : ℕ) := by
    funext ω
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rwa [hfun] at h

/-! ## The second moment -/

/-- **The second moment of an `O_{Gamma_1}(A)` variable.**

```
  E[ T^2 ]  <=  (4 e A)^2 .
```

The constant is CoarseGraining's `gammaMomentConst 1 * 2^{1} = 2 e * 2 = 4 e`,
squared; nothing below sharpens it.

: `[IsProbabilityMeasure mu]`, `hA : 0 < A`, `hT0 : forall omega, 0 <= T
omega`, `hTm : A T mu`, and `hT : IsBigOWith mu (gammaSigma 1) T A`. -/
theorem integral_sq_le_of_isBigOWith_gammaSigma_one [IsProbabilityMeasure μ]
    {T : Ω → ℝ} {A : ℝ} (hA : 0 < A) (hT0 : ∀ ω, 0 ≤ T ω) (hTm : AEMeasurable T μ)
    (hT : IndependentSums.IsBigOWith μ (IndependentSums.gammaSigma 1) T A) :
    ∫ ω, T ω ^ (2 : ℕ) ∂μ ≤ (4 * Real.exp 1 * A) ^ (2 : ℕ) := by
  have h := IndependentSums.integral_rpow_le_of_isBigOWith_gammaSigma
    (μ := μ) (Y := T) (K := A) (σ := 1) (p := 2) one_pos hA (by norm_num) hT0 hTm hT
  have hfun : (fun ω => T ω ^ (2 : ℝ)) = fun ω => T ω ^ (2 : ℕ) := by
    funext ω
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hconst : (IndependentSums.gammaMomentConst 1 * (2 : ℝ) ^ ((1 : ℝ))⁻¹ * A) ^ (2 : ℝ)
      = (4 * Real.exp 1 * A) ^ (2 : ℕ) := by
    rw [gammaMomentConst_one, inv_one, Real.rpow_one,
      show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [hfun] at h
  rw [← hconst]
  exact h

/-- The second-moment bound in expanded form: `E[T^2] <= 16 e^2 A^2`.

: the binders of `integral_sq_le_of_isBigOWith_gammaSigma_one`. -/
theorem integral_sq_le_of_isBigOWith_gammaSigma_one' [IsProbabilityMeasure μ]
    {T : Ω → ℝ} {A : ℝ} (hA : 0 < A) (hT0 : ∀ ω, 0 ≤ T ω) (hTm : AEMeasurable T μ)
    (hT : IndependentSums.IsBigOWith μ (IndependentSums.gammaSigma 1) T A) :
    ∫ ω, T ω ^ (2 : ℕ) ∂μ ≤ 16 * Real.exp 1 ^ (2 : ℕ) * A ^ (2 : ℕ) := by
  refine (integral_sq_le_of_isBigOWith_gammaSigma_one hA hT0 hTm hT).trans (le_of_eq ?_)
  ring

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
