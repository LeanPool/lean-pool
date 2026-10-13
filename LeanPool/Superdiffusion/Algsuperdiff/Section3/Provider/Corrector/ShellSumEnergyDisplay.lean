/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.ShellSumConsumerTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.ShellSumLayerDilation

/-!
# ShellSumEnergyDisplay

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `e.perturb.assumption`: the fresh-shell corrector energy display

This module assembles the four proved halves into the printed display.

* the **layer decomposition**
  `ShellSumLayerFlip.integral_normSq_shellSumCorrectorRepr_eq_sum` ((J1)
  independence + (J3) negation, per ****);
* the **`k = 0` value** `ShellSumLayerZeroEnergy.norm_sq_stationaryPotentialProjection_layerForcingL2_zero`
  ((J4), `a.j.nondeg`);
* the **per-layer dilation**
  `ShellSumLayerDilation.norm_sq_stationaryPotentialProjection_layerForcingL2`
  (`e.diff.law.shift`, per ****);
* the **corrector limit** `ShellSumConsumerTransport.tendsto_integral_cutoffSample_cubeAverage_of_weakSolutions`
  (`l.corrector.limit` at the consumer's carrier).

## What is supplied

* `integral_normSq_shellSumCorrectorRepr_eq_display` — at a **unit** direction,
  the shell-sum corrector energy is `c⋆ (log 3) Σ_{k ∈ (n,m]} 3^{2γk}`.
* `shellSumForcingL2_smul`, `integral_normSq_shellSumCorrectorRepr_smul` — the
  `|e|²` bilinearity: the corrector energy is quadratic in the direction.
* `integral_normSq_shellSumCorrectorRepr_gauge_display` — the printed display at
  the gauged direction `c • e`, `|e| = 1`:
  `c² c⋆ (log 3) Σ_{k ∈ (n,m]} 3^{2γk}`.  The manuscript's gauge
  `σ_{m-h}^{-1}` is the scalar `c`, so the printed `σ_{m-h}^{-2}` is the factor
  `c²`.
* `tendsto_integral_cutoffSample_cubeAverage_display` — the same, transported
  through the corrector limit to the consumer's carrier: both the Dirichlet and
  the Neumann localized cube energies converge, as `K → ∞`, to that value.  This
  is `e.perturb.assumption` and `e.perturb.assumption.two` together.

The direction `e` is normalized by `Book.Ch02.vecNorm e = 1`, the manuscript's `e ∈ ∂B_1`;
the gauge is free.  No other binder is introduced: the corrector families enter only
through the two weak formulations of `e.def.w`, and the two `AEStronglyMeasurable` typing
binders are the ones the proved corrector limit already carries.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Probability.Stationary
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3 (ABKModel)

noncomputable section

variable {d : ℕ}

/-! ### The display at a unit direction -/

/-- **`e.perturb.assumption` at a unit direction, at the shell-sum carrier.**

The corrector energy of the shell-sum forcing over the block `(n, m]` is
`c⋆ (log 3) Σ_{k ∈ (n,m]} 3^{2γk}`.  The three inputs are the layer
decomposition, the `k = 0` value `c⋆ (log 3)` of (J4), and the per-layer
dilation `3^{2γk}` of `e.diff.law.shift`. -/
theorem integral_normSq_shellSumCorrectorRepr_eq_display (M : ABKModel d) {e : Vec d}
    (he : HCPolySupport.Book.Ch02.vecNorm e = 1) (n m : ℤ) :
    ∫ f, ‖shellSumCorrectorRepr M e n m f‖ ^ 2
        ∂(shellSumValuePathLaw M.P n m).toMeasure
      = Algsuperdiff.Section3.Disorder.cstar M * Real.log 3 *
          ∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) := by
  rw [integral_normSq_shellSumCorrectorRepr_eq_sum M e n m]
  have hk : ∀ k ∈ Finset.Ioc n m,
      ‖stationaryPotentialProjection (μ := (seqPathLaw M.P).toMeasure)
          (layerForcingL2 M e k)‖ ^ 2
        = (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
            (Algsuperdiff.Section3.Disorder.cstar M * Real.log 3) := by
    intro k _
    rw [norm_sq_stationaryPotentialProjection_layerForcingL2 M e k,
      norm_sq_stationaryPotentialProjection_layerForcingL2_zero M he]
  rw [Finset.sum_congr rfl hk, ← Finset.sum_mul]
  ring

/-! ### The `|e|²` bilinearity -/

private theorem valuePathForcing_smul_direction (c : ℝ) (e : Vec d)
    (f : C(Vec d, Mat d)) :
    valuePathForcing (c • e) f = c • valuePathForcing e f := by
  show HilbertVec.ofVec (matVecMul (f 0) (c • e)) = _
  have h : matVecMul (f 0) (c • e) = c • matVecMul (f 0) e := by
    funext i
    simp only [matVecMul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [h]
  simpa only [HilbertVec.ofVecL_apply] using!
    map_smul (HilbertVec.ofVecL d) c (matVecMul (f 0) e)

/-- The shell-sum forcing is linear in the direction. -/
theorem shellSumForcingL2_smul (M : ABKModel d) (c : ℝ) (e : Vec d) (n m : ℤ) :
    shellSumForcingL2 M (c • e) n m = c • shellSumForcingL2 M e n m := by
  have hsmul : c • shellSumForcingL2 M e n m
      = ((memLp_two_valuePathForcing_shellSum M e n m).const_smul c).toLp
          (c • valuePathForcing e) := (MemLp.toLp_const_smul _ _).symm
  rw [hsmul]
  exact (MemLp.toLp_eq_toLp_iff _ _).2
    (Filter.Eventually.of_forall fun f => valuePathForcing_smul_direction c e f)

/-- **The corrector energy is quadratic in the direction**, the `|e|²` of
`e.perturb.assumption`. -/
theorem integral_normSq_shellSumCorrectorRepr_smul (M : ABKModel d) (c : ℝ)
    (e : Vec d) (n m : ℤ) :
    ∫ f, ‖shellSumCorrectorRepr M (c • e) n m f‖ ^ 2
        ∂(shellSumValuePathLaw M.P n m).toMeasure
      = c ^ 2 * ∫ f, ‖shellSumCorrectorRepr M e n m f‖ ^ 2
          ∂(shellSumValuePathLaw M.P n m).toMeasure := by
  rw [integral_normSq_shellSumCorrectorRepr_eq_norm_sq M (c • e) n m,
    integral_normSq_shellSumCorrectorRepr_eq_norm_sq M e n m,
    shellSumPotentialCorrector, shellSumPotentialCorrector,
    shellSumForcingL2_smul M c e n m, map_smul, norm_neg, norm_neg, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs]

/-! ### The gauged display -/

/-- **`e.perturb.assumption`, the printed display.**

At the gauged direction `c • e` with `|e| = 1` the shell-sum corrector energy is
`c² c⋆ (log 3) Σ_{k ∈ (n,m]} 3^{2γk}`.  The manuscript's gauge is
`c = σ_{m-h}^{-1}`, giving its `σ_{m-h}^{-2}`. -/
theorem integral_normSq_shellSumCorrectorRepr_gauge_display (M : ABKModel d) (c : ℝ)
    {e : Vec d} (he : HCPolySupport.Book.Ch02.vecNorm e = 1) (n m : ℤ) :
    ∫ f, ‖shellSumCorrectorRepr M (c • e) n m f‖ ^ 2
        ∂(shellSumValuePathLaw M.P n m).toMeasure
      = c ^ 2 * (Algsuperdiff.Section3.Disorder.cstar M * Real.log 3 *
          ∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) := by
  rw [integral_normSq_shellSumCorrectorRepr_smul M c e n m,
    integral_normSq_shellSumCorrectorRepr_eq_display M he n m]

/-! ### The display at the consumer's carrier -/

/-- **`e.perturb.assumption` and `e.perturb.assumption.two` at the recurrence
consumer's data.**

Both localized cube energies -- the Dirichlet one and the Neumann one -- of the
solutions of `e.def.w` at the gauged forcing `-streamForcing c ω n m e` converge,
as the localization cube `□_K` exhausts space, to

`c² c⋆ (log 3) Σ_{k ∈ (n,m]} 3^{2γk}`.

The sample integral is taken over `CutoffSample d` against `cutoffSampleLaw M`,
the carrier the recurrence consumer integrates over; the corrector families are
indexed by the increment path, which is what `e.def.w` gives.  The gauge enters
as the scalar `c` of the direction `c • e` and needs no separate step
(`ShellSumConsumerTransport.toVec_realize_valuePathForcing_shellSumValuePath`
identifies the forcing here with the consumer's `streamForcing c ω n m e`).

The only binders are the frozen model, the shell pair, the unit direction, the two weak
formulations of `e.def.w`, and the two `AEStronglyMeasurable` typing binders of the proved
corrector limit. -/
theorem tendsto_integral_cutoffSample_cubeAverage_display
    (M : ABKModel d) (c : ℝ) {e : Vec d}
    (he : HCPolySupport.Book.Ch02.vecNorm e = 1) (n m : ℤ)
    (wD : ∀ K : ℕ, C(Vec d, Mat d) → H10Function (openCubeSet (originCube d (K : ℤ))))
    (wN : ∀ K : ℕ,
      C(Vec d, Mat d) → H1MeanZeroFunction (openCubeSet (originCube d (K : ℤ))))
    (hDm : ∀ K : ℕ, AEStronglyMeasurable
      (fun f => cubeAverage (originCube d (K : ℤ))
        fun x => vecDot ((wD K f).toH1Function.grad x) ((wD K f).toH1Function.grad x))
      (shellSumValuePathLaw M.P n m).toMeasure)
    (hNm : ∀ K : ℕ, AEStronglyMeasurable
      (fun f => cubeAverage (originCube d (K : ℤ))
        fun x => vecDot ((wN K f).toH1Function.grad x) ((wN K f).toH1Function.grad x))
      (shellSumValuePathLaw M.P n m).toMeasure)
    (hD : ∀ (K : ℕ) (f : C(Vec d, Mat d)),
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet (originCube d (K : ℤ))) (wD K f)
        (fun x => -(realize (valuePathForcing (c • e)) f x).toVec))
    (hN : ∀ (K : ℕ) (f : C(Vec d, Mat d)),
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet (originCube d (K : ℤ))) (wN K f)
        (fun x => -(realize (valuePathForcing (c • e)) f x).toVec)) :
    Filter.Tendsto (fun K : ℕ => ∫ omega : CutoffSample d,
        cubeAverage (originCube d (K : ℤ))
          (fun x => vecDot
            ((wD K (shellSumValuePath n m omega.val)).toH1Function.grad x)
            ((wD K (shellSumValuePath n m omega.val)).toH1Function.grad x))
        ∂(cutoffSampleLaw M).toMeasure) Filter.atTop
        (nhds (c ^ 2 * (Algsuperdiff.Section3.Disorder.cstar M * Real.log 3 *
          ∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)))))
      ∧ Filter.Tendsto (fun K : ℕ => ∫ omega : CutoffSample d,
          cubeAverage (originCube d (K : ℤ))
            (fun x => vecDot
              ((wN K (shellSumValuePath n m omega.val)).toH1Function.grad x)
              ((wN K (shellSumValuePath n m omega.val)).toH1Function.grad x))
          ∂(cutoffSampleLaw M).toMeasure) Filter.atTop
          (nhds (c ^ 2 * (Algsuperdiff.Section3.Disorder.cstar M * Real.log 3 *
            ∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))))) := by
  have h := tendsto_integral_cutoffSample_cubeAverage_of_weakSolutions M c e n m
    wD wN hDm hNm hD hN
  rwa [integral_normSq_shellSumCorrectorRepr_gauge_display M c he n m] at h

end

end Algsuperdiff.Section3.Provider.Corrector
