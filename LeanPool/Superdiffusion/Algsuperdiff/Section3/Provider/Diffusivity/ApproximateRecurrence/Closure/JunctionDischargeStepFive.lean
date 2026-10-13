/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.JunctionDischargeStepFour

/-!
# JunctionDischargeStepFive

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-5 gauge junction: the per-cube expansion and the grid assembly

This module carries `Closure.Step5GaugeEndpoint` --- the finite-`K` form of
`e.lower.bound.pre2` --- down to the *one* display the manuscript's Step 5
actually argues about, and discharges everything else.

## What is proved here

At the Step-6 branch `e' = 0` and `|e| = 1`, the Neumann forcing
`-streamForcing shom_n^{-1} omega n (n+h) 0` vanishes identically, so the
Neumann corrector's gradient is a.e.  `0` on `cu_K` and its average over every
descendant cube vanishes.  The gauge collapse
(`ClosureGaugeCollapse.blockVecDot_gaugedPrincipalLoadShell_blockDiag_flux`)
then gives, per cube and per sample, the manuscript's own four-term display

```
  | Ahom^{1/2} G_{-(h)_R} Ahom^{-1/2} P_R |^2
    = |e|^2 + |(grad w_D^{(K)})_R|^2
      + shom^{-2} |(h)_R (grad w_D^{(K)})_R|^2
      - 2 shom^{-1} e . (h)_R (grad w_D^{(K)})_R
    = 1 + step5CellExcess ,
```

which is `blockVecDot_gaugedPrincipalLoadShell_blockDiag_flux_expand`.  Averaging
over the descendant grid and integrating in the sample then reduces the endpoint
to a single inequality about `step5CellExcess`, which is
`step5GaugeEndpoint_of_cellDisplay`.

## What is charged forward: the binder `hdisplay`

`hdisplay` is exactly the manuscript's remaining Step-5 content, namely the two
displays combined:

```
  avsum_R E[ step5CellExcess ]
    <= - E|| grad w_D^{(K)} ||^2_{L2(cu_K)}
       + Fend h^2 shom_n^{-4} 3^{4 cgamma (n+h)} + cgamma^15 .
```

Its two halves have named producers, neither of which is proved at the grid
carrier yet:

* the **energy identity** `e.what.nablaw.really.is`, `|| grad w_D^{(K)} ||^2 =
  shom^{-1} avg_{cu_K} e. (h) grad w_D^{(K)}`, obtained by testing `e.def.w`
  with its own solution.  It converts the cross term `-2 shom^{-1} avsum_[e.
  (h)_R (grad w_D)_R]` into `-2 E||grad w_D||^2`, up to the difference between
  the *product of the averages* `(h)_R (grad w_D)_R` and the *average of the
  product* `(h grad w_D)_R`;
* that difference, together with Jensen for `avsum_|(grad w_D)_R|^2 <= E||grad
  w_D||^2`, is the `cgamma^15` oscillation remainder
  `e.lower.bound.oscillations`, whose proved endpoint is
  `LocalizationOscillationFullMesh.exists_gamma0_freshShellDirichlet_step5MeshOscillation_le_gamma_pow_fifteen`
  (stated as a *fourth-moment* mesh oscillation, so a Cauchy--Schwarz step is
  still needed to feed it in here);
* the positive term `shom^{-2} avsum_|(h)_R (grad w_D)_R|^2` is bounded by
  `Fend h^2 shom_n^{-4} 3^{4 cgamma (n+h)}` through
  `Closure.shellProduct_le_quadratic_error` on `l.km.kn.Lp` and
  `e.nablaw.in.L.eight`.

`hsampR` is the sample integrability of the per-cube excess; its producer is
`Corrector.CorrectorMeasurableGradient` together with the moment bounds above.

## References

* ABK26, `e.lower.bound.pre2`; `e.what.nablaw.really.is`;
  `e.lower.bound.oscillations`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector

noncomputable section

variable {d : ℕ}

/-! ## Vector algebra -/

private theorem vecNormSq_sub_expand (u w : Vec d) :
    vecNormSq (u - w) = vecNormSq u - 2 * vecDot u w + vecNormSq w := by
  have hpt : ∀ i : Fin d,
      (u - w) i * (u - w) i = u i * u i - 2 * (u i * w i) + w i * w i := by
    intro i
    simp only [Pi.sub_apply]
    ring
  simp only [vecNormSq, vecDot]
  rw [Finset.sum_congr rfl fun i _ => hpt i, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum]

/-! ## The Step-5 per-cube excess -/

/-- **The three non-constant terms of the Step-5 per-cube display**:

```
  |(grad w_D)_R|^2 - 2 shom^{-1} e . (h)_R (grad w_D)_R
    + shom^{-2} |(h)_R (grad w_D)_R|^2 .
```

This is what remains of the gauged doubled quadratic form at the Step-6 branch
`e' = 0` and `|e| = 1`, after the constant `|e|^2 = 1`. -/
def step5CellExcess (sigma : PositiveScalar) {Q : TriadicCube d} (R : TriadicCube d)
    (n m : ℤ) (e : Vec d) (wD : ShellSeq d → H10Function (openCubeSet Q))
    (omega : ShellSeq d) : ℝ :=
  vecNormSq (cubeAverageVec R (fun x => (wD omega).toH1Function.grad x))
    - 2 * ((sigma : ℝ))⁻¹ *
        vecDot e (matVecMul (freshShellCubeAverage R omega n m)
          (cubeAverageVec R (fun x => (wD omega).toH1Function.grad x)))
    + ((sigma : ℝ))⁻¹ ^ 2 *
        vecNormSq (matVecMul (freshShellCubeAverage R omega n m)
          (cubeAverageVec R (fun x => (wD omega).toH1Function.grad x)))

/-- **The per-cube collapse at the Step-5 branch, expanded**.

At `e' = 0` the Neumann forcing vanishes, so `(grad w_N)_R = 0`; the gauged
doubled quadratic form is then `1 + step5CellExcess`, which is exactly the
manuscript's four-term display. -/
theorem blockVecDot_gaugedPrincipalLoadShell_blockDiag_flux_expand
    (sigma : PositiveScalar) {Q : TriadicCube d} (R : TriadicCube d) (n m : ℤ)
    {e : Vec d} (he : vecNormSq e = 1)
    (wD : ShellSeq d → H10Function (openCubeSet Q))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet Q))
    (omega : ShellSeq d)
    (hzeroN : cubeAverageVec R (fun x => (wN omega).toH1Function.grad x) = 0) :
    blockVecDot (gaugedPrincipalLoadShell sigma R n m e 0 wD wN omega)
        (blockMatVecMul
          (Ch02.blockDiag ((sigma : ℝ) • (1 : Mat d)) (((sigma : ℝ))⁻¹ • (1 : Mat d)))
          (gaugedPrincipalLoadShell sigma R n m e 0 wD wN omega))
      = 1 + step5CellExcess sigma R n m e wD omega := by
  rw [blockVecDot_gaugedPrincipalLoadShell_blockDiag_flux sigma R n m e wD wN omega,
    hzeroN, add_zero, vecNormSq_sub_expand, vecDot_smul_right, vecNormSq_smul, he,
    step5CellExcess]
  ring

/-! ## The endpoint, from the averaged display -/

/-- **`Closure.Step5GaugeEndpoint` from the manuscript's averaged Step-5
display.**

`hdisplay` is the conjunction of the two displays --- the oscillation
replacement of `(h)_R (grad w_D)_R` by `(h grad w_D)_R` and the Hoelder product
of `Closure.shellProduct_le_quadratic_error` --- stated at the grid carrier the
closure consumes and at the finite localization cube.  `hN` is `e.def.w`,
Neumann leg, read at the Step-6 branch direction `e' = 0`; `hsampR` is the
sample integrability of the per-cube excess.

Everything else --- the gauge collapse, the vanishing of the Neumann corrector
at the zero direction, the expansion into the manuscript's four terms and the
grid arithmetic --- is discharged here. -/
theorem step5GaugeEndpoint_of_cellDisplay (M : ABKModel d) (n : ℤ) (h : ℕ)
    (K j : ℕ) {e : Vec d} (he : vecNormSq e = 1) (Fend : ℝ)
    (wD : C(Vec d, Mat d) → H10Function (openCubeSet (originCube d (K : ℤ))))
    (wN : C(Vec d, Mat d) →
      H1MeanZeroFunction (openCubeSet (originCube d (K : ℤ))))
    (hN : ∀ omega : ShellSeq d,
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet (originCube d (K : ℤ))) (alongIncrementPath n h wN omega)
        (fun x => -streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ))
          (0 : Vec d) x))
    (hsampR : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable (fun omega : CutoffSample d =>
        step5CellExcess (Annealed.sigmaBar M n) R n (n + (h : ℤ)) e
          (alongIncrementPath n h wD) omega.val) (cutoffSampleLaw M).toMeasure)
    (hdisplay : descendantsAverage (originCube d (K : ℤ)) j
        (fun R => ∫ omega : CutoffSample d,
          step5CellExcess (Annealed.sigmaBar M n) R n (n + (h : ℤ)) e
            (alongIncrementPath n h wD) omega.val ∂(cutoffSampleLaw M).toMeasure) ≤
      -dirichletCubeEnergy M n h K wD
        + Fend * ((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
            (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))
        + M.gamma ^ (15 : ℕ)) :
    Step5GaugeEndpoint M n h K j e Fend wD wN := by
  classical
  have hzeroN : ∀ (omega : ShellSeq d) {R : TriadicCube d},
      R ∈ descendantsAtDepth (originCube d (K : ℤ)) j →
      cubeAverageVec R
        (fun x => (alongIncrementPath n h wN omega).toH1Function.grad x) = 0 := by
    intro omega R hR
    exact cubeAverageVec_eq_zero_of_ae_eq_zero_openCubeSet hR
      (grad_ae_eq_zero_of_isMeanZeroNeumannRhsWeakSolution_streamForcing_zero
        (originCube d (K : ℤ)) ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ))
        (hN omega))
  show gaugeEnergyAverage M n h (K : ℤ) j e 0
      (alongIncrementPath n h wD) (alongIncrementPath n h wN) ≤
    1 - dirichletCubeEnergy M n h K wD
      + Fend * ((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
          (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))
      + M.gamma ^ (15 : ℕ)
  rw [gaugeEnergyAverage]
  calc descendantsAverage (originCube d (K : ℤ)) j
        (fun R => ∫ omega : CutoffSample d,
          blockVecDot
            (gaugedPrincipalLoadShell (Annealed.sigmaBar M n) R n (n + (h : ℤ)) e 0
              (alongIncrementPath n h wD) (alongIncrementPath n h wN) omega.val)
            (blockMatVecMul
              (Ch02.blockDiag ((Annealed.sigmaBar M n : ℝ) • (1 : Mat d))
                (((Annealed.sigmaBar M n : ℝ))⁻¹ • (1 : Mat d)))
              (gaugedPrincipalLoadShell (Annealed.sigmaBar M n) R n (n + (h : ℤ)) e 0
                (alongIncrementPath n h wD) (alongIncrementPath n h wN) omega.val))
          ∂(cutoffSampleLaw M).toMeasure)
      ≤ descendantsAverage (originCube d (K : ℤ)) j
        (fun R => (1 : ℝ) + ∫ omega : CutoffSample d,
          step5CellExcess (Annealed.sigmaBar M n) R n (n + (h : ℤ)) e
            (alongIncrementPath n h wD) omega.val
          ∂(cutoffSampleLaw M).toMeasure) := by
        refine descendantsAverage_le_descendantsAverage _ _ fun R hR => le_of_eq ?_
        rw [integral_congr_ae (Filter.Eventually.of_forall fun omega : CutoffSample d =>
            blockVecDot_gaugedPrincipalLoadShell_blockDiag_flux_expand
              (Annealed.sigmaBar M n) R n (n + (h : ℤ)) he _ _ omega.val
              (hzeroN omega.val hR)),
          integral_add (integrable_const 1) (hsampR R hR), integral_const]
        simp
    _ = 1 + descendantsAverage (originCube d (K : ℤ)) j
          (fun R => ∫ omega : CutoffSample d,
            step5CellExcess (Annealed.sigmaBar M n) R n (n + (h : ℤ)) e
              (alongIncrementPath n h wD) omega.val
            ∂(cutoffSampleLaw M).toMeasure) := by
        rw [descendantsAverage_add_real, descendantsAverage_const_real]
    _ ≤ 1 - dirichletCubeEnergy M n h K wD
          + Fend * ((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
              (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))
          + M.gamma ^ (15 : ℕ) := by linarith [hdisplay]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
