/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.Step3BlockSplit

/-!
# MajorantSlots

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two `L`-carrying slots of Step 3's display, and the `L`-free majorant

Nothing here imports that file, and nothing here claims the anchor.

## The mechanism

`Step3BlockSplit.step3Display` is a function of the truncation index `L` only
through the two unit-cube gauges of the recentered shell
`h = k_L − k_{j−2} − (k_L − k_m)_{□_m}`:

```
(step3Shell M L m R hle ω).gradientW1Infinity      and      (step3Shell M L m R hle ω).valueL2 .
```

Every other ingredient -- `σ_m`, `σ_{j−2}`, `unitCubeLambda (2γ)` and
`unitCubeHomogenizationError` at `unitRescaledCutoffCoeff M R (R.scale − 2) ω`
-- is built from the cutoff at level `R.scale − 2` and is `L`-free.  This module
makes that structural fact usable:

* `step3DisplayAt` is Step 3's display with the two gauges replaced by abstract
  real slots; `step3Display_eq_step3DisplayAt` is the `rfl` identification;
* `step3DisplayAt_mono` is the monotonicity of the display in both slots, which
  is what converts *upper bounds on the two gauges* into an upper bound on the
  display.  Its abstract-real core keeps the two `Real.rpow` atoms opaque.

Consequently, any pair of `L`-free upper bounds for the two gauges produces an
`L`-free majorant of `step3Display`, and hence -- through
`Step3BlockSplit.exists_normalizedBlockResponseMax_step3_split`, which needs the
display at `ω` and at the negated sample `Nω` -- an `L`-free majorant of the
Step-1 endpoint's per-cube block response maximum.  That majorant is
`lFreeStep3Majorant`.

The two slot bounds themselves (the geometric shell-sum route) are the business
of `ShellSlotBounds.lean`; the composition with the expectation transport is
`MajorantTransport.lean`.

## What is a hypothesis here, and why

`step3DisplayAt_mono` needs the sign facts `0 ≤ C`, `0 < σ`, `0 ≤ λ^{-1}`,
`0 ≤ grad`, `0 ≤ val` and the nonnegativity of the two printed exponents
`2s/(1−4γ)`, `4γ/(1−4γ)`; the last is where `γ ≤ 1/8` is used, exactly the
binder `Step3BlockSplit` already carries.  The slot bounds `GB`, `VB` are
parameters: they are supplied by the caller and are *not* source premises.

## References

* ABK26, `l.bounds.mathcal.E.aL`, (Step 3).
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section4.Provider.Annular

noncomputable section

variable {d : ℕ}

/-! ## Step 3's display with abstract gauge slots -/

/-- **Step 3's display, with the two `L`-carrying gauges abstracted.**

`step3Display L m R hle ω s` is this expression at `grad = (step3Shell M L m R
hle ω).gradientW1Infinity` and `val = (step3Shell M L m R hle ω).valueL2`;
nothing else in it mentions `L`. -/
def step3DisplayAt [NeZero d] (C : ℝ) (M : ABKModel d) (m : ℤ) (R : TriadicCube d)
    (omega : Cutoff.CutoffSample d) (s grad val : ℝ) : ℝ :=
  C * ((Annealed.sigmaBar M m : ℝ)⁻¹ * (Annealed.sigmaBar M (R.scale - 2) : ℝ)) *
      Real.rpow (1 + grad *
          (unitCubeLambda (2 * M.gamma) (.finite 2)
            (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹)
        (2 * s / (1 - 4 * M.gamma)) *
      unitCubeHomogenizationError s (.finite 2) (.finite 2)
        (unitRescaledCutoffCoeff M R (R.scale - 2) omega)
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M (R.scale - 2))) ^ 2 +
    C * ((Annealed.sigmaBar M m : ℝ)⁻¹ * (Annealed.sigmaBar M (R.scale - 2) : ℝ) ^ 2) *
      (unitCubeLambda (2 * M.gamma) (.finite 2)
        (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹ *
      Real.rpow (1 + grad *
          (unitCubeLambda (2 * M.gamma) (.finite 2)
            (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹)
        (4 * M.gamma / (1 - 4 * M.gamma)) *
      ((Annealed.sigmaBar M (R.scale - 2) : ℝ)⁻¹ ^ 2 * val ^ 2 +
        ((Annealed.sigmaBar M m : ℝ) * (Annealed.sigmaBar M (R.scale - 2) : ℝ)⁻¹ - 1) ^ 2) +
    C * (((Annealed.sigmaBar M m : ℝ)⁻¹ +
        (unitCubeLambda (2 * M.gamma) (.finite 2)
          (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹) * grad) ^ 2

/-- **The slot identification.**  Step 3's display IS `step3DisplayAt` at the two
gauges of the recentered shell; the `L`-dependence of the left-hand side lives
entirely in those two slots. -/
theorem step3Display_eq_step3DisplayAt [NeZero d] (C : ℝ) (M : ABKModel d) (L m : ℤ)
    (R : TriadicCube d) (hle : R.scale - 2 ≤ L) (omega : Cutoff.CutoffSample d) (s : ℝ) :
    step3Display C M L m R hle omega s =
      step3DisplayAt C M m R omega s (step3Shell M L m R hle omega).gradientW1Infinity
        (step3Shell M L m R hle omega).valueL2 :=
  rfl

/-! ## Monotonicity in the two slots -/

/-- The abstract-real core of the slot monotonicity.  The two `Real.rpow` atoms
are opaque: they are moved only by `Real.rpow_le_rpow`, and the rest is
monotonicity of products of nonnegative reals. -/
private theorem displayAt_core_mono {C sm sj lam Err e1 e2 grad grad' val val' : ℝ}
    (hC : 0 ≤ C) (hsm : 0 < sm) (hsj : 0 < sj) (hlam : 0 ≤ lam)
    (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (hg0 : 0 ≤ grad) (hgg : grad ≤ grad')
    (hv0 : 0 ≤ val) (hvv : val ≤ val') :
    C * (sm⁻¹ * sj) * Real.rpow (1 + grad * lam) e1 * Err ^ 2 +
        C * (sm⁻¹ * sj ^ 2) * lam * Real.rpow (1 + grad * lam) e2 *
          (sj⁻¹ ^ 2 * val ^ 2 + (sm * sj⁻¹ - 1) ^ 2) +
        C * ((sm⁻¹ + lam) * grad) ^ 2 ≤
      C * (sm⁻¹ * sj) * Real.rpow (1 + grad' * lam) e1 * Err ^ 2 +
        C * (sm⁻¹ * sj ^ 2) * lam * Real.rpow (1 + grad' * lam) e2 *
          (sj⁻¹ ^ 2 * val' ^ 2 + (sm * sj⁻¹ - 1) ^ 2) +
        C * ((sm⁻¹ + lam) * grad') ^ 2 := by
  have hsm0 : (0 : ℝ) ≤ sm⁻¹ := (inv_pos.mpr hsm).le
  have hbase0 : (0 : ℝ) ≤ 1 + grad * lam := by
    have : (0 : ℝ) ≤ grad * lam := mul_nonneg hg0 hlam
    linarith only [this]
  have hbasele : 1 + grad * lam ≤ 1 + grad' * lam := by
    have : grad * lam ≤ grad' * lam := mul_le_mul_of_nonneg_right hgg hlam
    linarith only [this]
  have hr1 : Real.rpow (1 + grad * lam) e1 ≤ Real.rpow (1 + grad' * lam) e1 :=
    Real.rpow_le_rpow hbase0 hbasele he1
  have hr2 : Real.rpow (1 + grad * lam) e2 ≤ Real.rpow (1 + grad' * lam) e2 :=
    Real.rpow_le_rpow hbase0 hbasele he2
  -- first summand
  have hK1 : (0 : ℝ) ≤ C * (sm⁻¹ * sj) :=
    mul_nonneg hC (mul_nonneg hsm0 hsj.le)
  have hT1 : C * (sm⁻¹ * sj) * Real.rpow (1 + grad * lam) e1 * Err ^ 2 ≤
      C * (sm⁻¹ * sj) * Real.rpow (1 + grad' * lam) e1 * Err ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr1 hK1) (sq_nonneg Err)
  -- second summand
  have hK2 : (0 : ℝ) ≤ C * (sm⁻¹ * sj ^ 2) * lam :=
    mul_nonneg (mul_nonneg hC (mul_nonneg hsm0 (sq_nonneg sj))) hlam
  have hbr0 : (0 : ℝ) ≤ sj⁻¹ ^ 2 * val ^ 2 + (sm * sj⁻¹ - 1) ^ 2 :=
    add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  have hbr : sj⁻¹ ^ 2 * val ^ 2 + (sm * sj⁻¹ - 1) ^ 2 ≤
      sj⁻¹ ^ 2 * val' ^ 2 + (sm * sj⁻¹ - 1) ^ 2 := by
    have hval : val ^ 2 ≤ val' ^ 2 := pow_le_pow_left₀ hv0 hvv 2
    have := mul_le_mul_of_nonneg_left hval (sq_nonneg sj⁻¹)
    linarith only [this]
  have hT2 : C * (sm⁻¹ * sj ^ 2) * lam * Real.rpow (1 + grad * lam) e2 *
        (sj⁻¹ ^ 2 * val ^ 2 + (sm * sj⁻¹ - 1) ^ 2) ≤
      C * (sm⁻¹ * sj ^ 2) * lam * Real.rpow (1 + grad' * lam) e2 *
        (sj⁻¹ ^ 2 * val' ^ 2 + (sm * sj⁻¹ - 1) ^ 2) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hr2 hK2) hbr hbr0
      (mul_nonneg hK2 (Real.rpow_nonneg (by linarith only [hbase0, hbasele]) _))
  -- third summand
  have hsum0 : (0 : ℝ) ≤ sm⁻¹ + lam := by linarith only [hsm0, hlam]
  have hT3 : C * ((sm⁻¹ + lam) * grad) ^ 2 ≤ C * ((sm⁻¹ + lam) * grad') ^ 2 :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg hsum0 hg0) (mul_le_mul_of_nonneg_left hgg hsum0) 2) hC
  linarith only [hT1, hT2, hT3]

/-- The gapped-gauge exponents of the display are nonnegative in the anchor's
own ranges (`0 < s`, `0 < γ ≤ 1/8`). -/
private theorem step3_exponents_nonneg {gam s : ℝ} (hgam0 : 0 < gam) (hgam : gam ≤ 1 / 8)
    (hs : 0 < s) : 0 ≤ 2 * s / (1 - 4 * gam) ∧ 0 ≤ 4 * gam / (1 - 4 * gam) := by
  have hden : (0 : ℝ) < 1 - 4 * gam := by linarith only [hgam]
  exact ⟨div_nonneg (by linarith only [hs]) hden.le,
    div_nonneg (by linarith only [hgam0]) hden.le⟩

/-- **The display is monotone in both gauge slots.**

Enlarging the gradient gauge and the `L²` gauge enlarges Step 3's display: the
first slot occurs in the two `(1 + grad λ^{-1})`-powers (nonnegative exponents)
and in the last square, the second slot only through `val²`. -/
theorem step3DisplayAt_mono [NeZero d] {C : ℝ} (hC : 0 ≤ C) (M : ABKModel d) (m : ℤ)
    (R : TriadicCube d) (omega : Cutoff.CutoffSample d) {s grad grad' val val' : ℝ}
    (hs : 0 < s) (hgam : M.gamma ≤ 1 / 8) (hg0 : 0 ≤ grad) (hgg : grad ≤ grad')
    (hv0 : 0 ≤ val) (hvv : val ≤ val') :
    step3DisplayAt C M m R omega s grad val ≤ step3DisplayAt C M m R omega s grad' val' := by
  have hgam0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  obtain ⟨he1, he2⟩ := step3_exponents_nonneg hgam0 hgam hs
  exact displayAt_core_mono hC (Annealed.sigmaBar M m).2 (Annealed.sigmaBar M (R.scale - 2)).2
    (Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional.unitCubeLambda_inv_nonneg
      (unitRescaledCutoffCoeff M R (R.scale - 2) omega) (by linarith only [hgam0])
      Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional.isAdmissible_finite_two)
    he1 he2 hg0 hgg hv0 hvv

/-! ## The `L`-free majorant -/

/-- **The `L`-free majorant of the Step-1 endpoint's per-cube object.**

Given `L`-free upper bounds `GB R ω`, `VB R ω` for the two gauges of the
recentered shell at the cube `R`, this is Step 3's display at those bounds, read
at `ω` and at the negated sample `Nω` -- the two legs of the primal/adjoint
split of `Step3BlockSplit.exists_normalizedBlockResponseMax_step3_split`.

It does not mention `L`. -/
def lFreeStep3Majorant [NeZero d] (C : ℝ) (M : ABKModel d) (m : ℤ) (s : ℝ)
    (GB VB : TriadicCube d → Cutoff.CutoffSample d → ℝ) (R : TriadicCube d)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  step3DisplayAt C M m R omega s (GB R omega) (VB R omega) +
    step3DisplayAt C M m R (Cutoff.negateCutoffSample omega) s
      (GB R (Cutoff.negateCutoffSample omega)) (VB R (Cutoff.negateCutoffSample omega))

/-- **The two-sample display sum is dominated by the `L`-free majorant.**

The hypotheses are the two slot bounds at the two samples the split needs (`ω`
and `Nω`), each uniformly in `L ≥ m`; the conclusion is `L`-free.  This is the
step that removes `L` from Step 3's display.  The slot bounds are required at
these two samples ONLY, which is what lets a caller supply them almost surely. -/
theorem step3Display_add_negate_le_lFreeStep3Majorant [NeZero d] {C : ℝ} (hC : 0 ≤ C)
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (omega : Cutoff.CutoffSample d) {s : ℝ}
    (hs : 0 < s) (hgam : M.gamma ≤ 1 / 8)
    (GB VB : TriadicCube d → Cutoff.CutoffSample d → ℝ)
    (hGB : ∀ (L : ℤ) (hle : R.scale - 2 ≤ L), m ≤ L →
      (step3Shell M L m R hle omega).gradientW1Infinity ≤ GB R omega)
    (hGBneg : ∀ (L : ℤ) (hle : R.scale - 2 ≤ L), m ≤ L →
      (step3Shell M L m R hle (Cutoff.negateCutoffSample omega)).gradientW1Infinity ≤
        GB R (Cutoff.negateCutoffSample omega))
    (hVB : ∀ (L : ℤ) (hle : R.scale - 2 ≤ L), m ≤ L →
      (step3Shell M L m R hle omega).valueL2 ≤ VB R omega)
    (hVBneg : ∀ (L : ℤ) (hle : R.scale - 2 ≤ L), m ≤ L →
      (step3Shell M L m R hle (Cutoff.negateCutoffSample omega)).valueL2 ≤
        VB R (Cutoff.negateCutoffSample omega))
    (L : ℤ) (hle : R.scale - 2 ≤ L) (hL : m ≤ L) :
    step3Display C M L m R hle omega s +
        step3Display C M L m R hle (Cutoff.negateCutoffSample omega) s ≤
      lFreeStep3Majorant C M m s GB VB R omega := by
  rw [step3Display_eq_step3DisplayAt, step3Display_eq_step3DisplayAt]
  refine add_le_add ?_ ?_
  · exact step3DisplayAt_mono hC M m R omega hs hgam
      (gradientW1Infinity_nonneg _) (hGB L hle hL) (valueL2_nonneg _) (hVB L hle hL)
  · exact step3DisplayAt_mono hC M m R (Cutoff.negateCutoffSample omega) hs hgam
      (gradientW1Infinity_nonneg _) (hGBneg L hle hL) (valueL2_nonneg _) (hVBneg L hle hL)

end

end Algsuperdiff.Section4.Provider.BoundsEaL
