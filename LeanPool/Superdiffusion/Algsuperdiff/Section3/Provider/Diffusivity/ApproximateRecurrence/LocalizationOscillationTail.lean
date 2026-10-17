/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.TranslatedTransport
public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.GammaSigma.Basic

/-!
# LocalizationOscillationTail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the fourth moment of the forcing gauge of `e.nablaw.oscillations`

Source displays in ABK26:

* `e.nablaw.oscillations` (label; display) carries on its right the forcing
  amplitude `shom_{m-h}^{-1} (m-h-n) 3^n ‖ grad (k_m - k_{m-h})
  ‖_{L^infty(z+cu_{m-h})}`;
* `e.lower.bound.oscillations` (label; display) takes the *fourth* moment of
  exactly that quantity, `shom_{m-h}^{-1} 3^n E[ ‖grad(k_m -
  k_{m-h})‖_{L^infty(cu_{m-h})}^4 ]^{1/4}`, and claims it is at most `C
  shom_{m-h}^{-1} 3^{-(m-h-n)} 3^{gamma(m-h)} gamma^{-1}`.

This module supplies the probabilistic half of that passage: the fourth moment
of the shell-derivative gauge sum on the cube `z + cu_{m-h}`, obtained from the
already-proved weak-Orlicz tail
`Provider.Stream.isBigOWith_gammaSigma_shellDerivNormSum_Ioc_translate`
(ABK26's `e.nabla.km.kn.infty`) through CoarseGraining's layer-cake moment
bound `IndependentSums.integral_rpow_le_of_isBigOWith_gammaSigma` at `p = 4`.

## The carrier

The random variable is the one that the proved instantiation of
`e.nablaw.oscillations` at the fresh-shell correctors
(`Corrector.exists_freshShellDirichlet_gradient_oscillation_interior_mesh_localGauge`
and its Neumann counterpart) puts on the right of the display: the summed
first-derivative gauges `sum_{k in (lowScale, highScale]} localCubeDerivNorm
lowScale (translate z (omega k))` on the cube `z + cu_{lowScale}`, at `lowScale
= m - h` and `highScale = m`.  It dominates `‖grad(k_m -
k_{m-h})‖_{L^infty(z+cu_{m-h})}` by the triangle inequality over the shells,
with no loss.

## What is proved

* `integral_shellDerivNormSum_rpow_four_le` -- the fourth moment.
* `shellDerivNormSum_momentRoot_four_le` -- its fourth root, which is the shape
  the display consumes.
* `mul_shellDerivNormSum_momentRoot_four_le_gap` -- the same bound multiplied by
  the display's prefactor `3^n`, rewritten in the manuscript's two-factor gap
  form `3^{-(m-h-n)} 3^{gamma(m-h)}`.

## Divergences from the printed statement

* **The constant is absolute, and sharper than the printed one.**  The
  manuscript writes `C gamma^{-1}` for the amplitude of this term; the bound
  below has no `gamma^{-1}` and no `(m-h-n)` factor, only the dimension-free
  weak-Orlicz constants of the class `Gamma_2`.  The printed form follows from
  this one, since `gamma^{-1} >= 1` in the regime of `e.cgamma.constraints`.
  Nothing is absorbed silently: the constant appears in full as
  `gammaMomentConst 2 * 4^{1/2} * gammaTriangleConst 2`.
* **.**  The statement below is a per-base-point statement, quantified over
  `z`.
* **The gauge, not the `L^infty` norm.**  The manuscript's random variable is
  `‖grad(k_m - k_{m-h})‖_{L^infty(z+cu_{m-h})}`; the one below is the summed
  first-derivative gauge that dominates it (see the carrier note above).  The
  moment bound therefore implies the printed one and is stronger.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The random variable -/

/-- The summed first-derivative shell gauges on the cube `z + cu_ell`, over the
shell range `(lowScale, highScale]`.  At `ell = lowScale = m - h` and
`highScale = m` this is the forcing amplitude of `e.nablaw.oscillations`. -/
def shellDerivNormSum (lowScale highScale : ℤ) (z : Vec d) (omega : ShellSeq d) : ℝ :=
  ∑ k ∈ Finset.Ioc lowScale highScale,
    Provider.Stream.localCubeDerivNorm lowScale (ShellField.translate z (omega k))

theorem shellDerivNormSum_nonneg (lowScale highScale : ℤ) (z : Vec d)
    (omega : ShellSeq d) : 0 ≤ shellDerivNormSum lowScale highScale z omega :=
  Finset.sum_nonneg fun k _ =>
    Provider.Stream.localCubeDerivNorm_nonneg lowScale (ShellField.translate z (omega k))

theorem measurable_shellDerivNormSum (lowScale highScale : ℤ) (z : Vec d) :
    Measurable (shellDerivNormSum (d := d) lowScale highScale z) :=
  Finset.measurable_sum (Finset.Ioc lowScale highScale) fun k _ =>
    ((Provider.Stream.measurable_localCubeDerivNorm lowScale).comp
      (ShellField.measurable_translate z)).comp (measurable_pi_apply k)

/-! ## The fourth-moment constant -/

/-- The absolute fourth-moment constant of the class `Gamma_2`: the layer-cake
constant `gammaMomentConst 2 * 4^{1/2}` composed with the triangle constant of
the shell sum. -/
def shellDerivGammaFourthConst : ℝ :=
  IndependentSums.gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) *
    IndependentSums.gammaTriangleConst 2

theorem shellDerivGammaFourthConst_pos : 0 < shellDerivGammaFourthConst := by
  have h1 : 0 < IndependentSums.gammaMomentConst 2 :=
    IndependentSums.gammaMomentConst_pos (by norm_num)
  have h2 : (0 : ℝ) < (4 : ℝ) ^ ((2 : ℝ)⁻¹) := Real.rpow_pos_of_pos (by norm_num) _
  have h3 : 0 < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  unfold shellDerivGammaFourthConst
  positivity

/-! ## The fourth moment -/

/-- **The fourth moment of the forcing gauge of `e.nablaw.oscillations`.**  The
weak-Orlicz tail `e.nabla.km.kn.infty` at the translated cube, run through the
layer-cake moment bound at `p = 4`. -/
theorem integral_shellDerivNormSum_rpow_four_le (M : ABKModel d)
    {lowScale highScale : ℤ} (hlt : lowScale < highScale) (z : Vec d) :
    ∫ omega : ShellSeq d,
        shellDerivNormSum lowScale highScale z omega ^ (4 : ℝ) ∂M.P.toMeasure ≤
      (shellDerivGammaFourthConst *
        (3 : ℝ) ^ ((M.gamma - 1) * (lowScale : ℝ))) ^ (4 : ℝ) := by
  have hA : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 *
      (3 : ℝ) ^ ((M.gamma - 1) * (lowScale : ℝ)) := by
    have h3 : 0 < IndependentSums.gammaTriangleConst 2 :=
      IndependentSums.gammaTriangleConst_pos
    positivity
  have htail := Provider.Stream.isBigOWith_gammaSigma_shellDerivNormSum_Ioc_translate
    M hlt z
  have h := IndependentSums.integral_rpow_le_of_isBigOWith_gammaSigma
    (μ := M.P.toMeasure) (p := (4 : ℝ)) (by norm_num : (0 : ℝ) < 2) hA
    (by norm_num : (1 : ℝ) ≤ 4)
    (fun omega => shellDerivNormSum_nonneg lowScale highScale z omega)
    (measurable_shellDerivNormSum lowScale highScale z).aemeasurable htail
  refine h.trans_eq ?_
  unfold shellDerivGammaFourthConst
  ring_nf

/-! ## The fourth root, and the manuscript's gap form -/

/-- **The fourth root of the previous display**, which is the shape in which
`e.lower.bound.oscillations` consumes it. -/
theorem shellDerivNormSum_momentRoot_four_le (M : ABKModel d)
    {lowScale highScale : ℤ} (hlt : lowScale < highScale) (z : Vec d) :
    (∫ omega : ShellSeq d,
        shellDerivNormSum lowScale highScale z omega ^ (4 : ℝ) ∂M.P.toMeasure) ^
        ((4 : ℝ)⁻¹) ≤
      shellDerivGammaFourthConst * (3 : ℝ) ^ ((M.gamma - 1) * (lowScale : ℝ)) := by
  have hBnn : (0 : ℝ) ≤ shellDerivGammaFourthConst *
      (3 : ℝ) ^ ((M.gamma - 1) * (lowScale : ℝ)) := by
    have := shellDerivGammaFourthConst_pos
    positivity
  have hint : (0 : ℝ) ≤ ∫ omega : ShellSeq d,
      shellDerivNormSum lowScale highScale z omega ^ (4 : ℝ) ∂M.P.toMeasure :=
    integral_nonneg fun omega =>
      Real.rpow_nonneg (shellDerivNormSum_nonneg lowScale highScale z omega) _
  have hmono := Real.rpow_le_rpow hint
    (integral_shellDerivNormSum_rpow_four_le M hlt z) (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹)
  refine hmono.trans_eq ?_
  rw [← Real.rpow_mul hBnn]
  norm_num

/-- The manuscript writes the amplitude of this term as the product of the scale
gap and the shell gauge, `3^{-(m-h-n)} 3^{gamma(m-h)}`.  With `lowScale = n +
N` and `N = m - h - n` that is exactly the prefactor `3^n` applied to the bound
above. -/
theorem rpow_gap_factorization (gamma : ℝ) (n : ℤ) (N : ℕ) :
    (3 : ℝ) ^ ((n : ℝ)) * (3 : ℝ) ^ ((gamma - 1) * ((n : ℝ) + (N : ℝ))) =
      (3 : ℝ) ^ (-(N : ℝ)) * (3 : ℝ) ^ (gamma * ((n : ℝ) + (N : ℝ))) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- **The forcing term of `e.lower.bound.oscillations`, at one base point.**  The
prefactor `3^n` of the display times the fourth moment root of the forcing
gauge on `z + cu_{n+N}` is at most the absolute constant times the manuscript's
two-factor amplitude `3^{-N} 3^{gamma (n+N)}`. -/
theorem mul_shellDerivNormSum_momentRoot_four_le_gap (M : ABKModel d)
    {n : ℤ} {N : ℕ} {highScale : ℤ} (hlt : n + (N : ℤ) < highScale) (z : Vec d) :
    (3 : ℝ) ^ ((n : ℝ)) *
        (∫ omega : ShellSeq d,
          shellDerivNormSum (n + (N : ℤ)) highScale z omega ^ (4 : ℝ)
            ∂M.P.toMeasure) ^ ((4 : ℝ)⁻¹) ≤
      shellDerivGammaFourthConst *
        ((3 : ℝ) ^ (-(N : ℝ)) * (3 : ℝ) ^ (M.gamma * ((n : ℝ) + (N : ℝ)))) := by
  have hroot := shellDerivNormSum_momentRoot_four_le M hlt z
  have h3 : (0 : ℝ) < (3 : ℝ) ^ ((n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hcast : (((n + (N : ℤ)) : ℤ) : ℝ) = (n : ℝ) + (N : ℝ) := by push_cast; ring
  have hstep := mul_le_mul_of_nonneg_left hroot h3.le
  refine hstep.trans_eq ?_
  rw [hcast]
  rw [show (3 : ℝ) ^ ((n : ℝ)) *
      (shellDerivGammaFourthConst * (3 : ℝ) ^ ((M.gamma - 1) * ((n : ℝ) + (N : ℝ)))) =
    shellDerivGammaFourthConst *
      ((3 : ℝ) ^ ((n : ℝ)) * (3 : ℝ) ^ ((M.gamma - 1) * ((n : ℝ) + (N : ℝ)))) by ring]
  rw [rpow_gap_factorization M.gamma n N]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
