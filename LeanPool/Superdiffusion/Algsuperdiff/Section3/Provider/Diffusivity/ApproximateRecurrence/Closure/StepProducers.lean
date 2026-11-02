/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.ClosureFinal
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.JunctionDischargeStepFiveDisplay
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.JunctionDischargeStepFour
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationCorrectorRegularity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseDisplayTwoGrid
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.ShellSumCorrectorLimit

/-!
# StepProducers

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-4 endpoint at the closure families, and the Step-5 analytic basket

`Closure.ClosureFinal` names three inputs of `twoSidedClosure_of_endpoints`.
This module **produces the second**, `Closure.ClosureStep4Input`, outright, and
discharges every binder of the third that is a statement about the closure's own
corrector families rather than a display of the manuscript.

## Step 4

`Closure.JunctionDischargeStepFour.step4GaugeEndpoint_of_correctors` carries
five binders.  `hD` is `e.def.w` at the Step-6 branch direction `e = 0`,
discharged by the proved
`Closure.isZeroTraceDirichletRhsWeakSolution_alongIncrementPath`.  The other
four are analytic side conditions of the display itself:

| binder | content | route |
|---|---|---|
| `hmemN` | `grad w_N^{(K)}` is `L^2` of each descendant cube |
`memLp_two_grad_normalizedCubeMeasure_descendant`: the `H^1` membership on `cu_K`, restricted along
`memLp_normalizedCubeMeasure_of_mem_descendantsAtDepth` |
| `hintN` | `|grad w_N^{(K)}|^2` is integrable on `cu_K` | `integrableOn_cubeSet_vecNormSq_grad`,
the same membership |
| `hsampR` | the per-cube average is sample integrable | continuity of `f |-> (grad w_N(f))_R` ---
the set-integral functional `hilbertVectorL2CoordSetIntegralCLM` composed with
`Closure.continuous_gradToHilbertVectorL2_closureNeumannFamily` --- dominated by the `hsampK`
integrand through per-cube Jensen and the descendant volume ratio |
| `hsampK` | `E[||grad w_N^{(K)}||^2_{L2(cu_K)}]` exists |
`Corrector.CorrectorLimitNode.integrable_cubeAverage_neumann_energy` at the closure family |

`closureStep4Input` is the resulting `Closure.ClosureStep4Input d`.  Its
threshold is `C4 = 1`: the endpoint holds at **every** localization scale `K` and
every mesh depth, so no regime fact of `Closure.ClosureRegime` is consumed.
The input's leading dimension antecedent `2 <= d` is likewise absorbed
trivially: the Step-4 production is dimension-free.

## Step 5

`step5GaugeEndpoint_closureFamilies_of_legs` is
`Closure.JunctionDischargeStepFiveDisplay.step5GaugeEndpoint_of_correctors_gauge`
--- the **per-cube-gauge** endpoint --- at the closure families with seven
binders discharged: `hgauge0`, `hD` and `hN` (the two halves of `e.def.w`) and
the Dirichlet mirrors `hmemD`, `hintD`, `hsampN`, `hsampG` of the four Step-4
routes above.  What remains are the mathematical legs --- `hintP`, `hsampX`,
`hsampS`, `hsampDef`, `hdefect`, `hmemOsc`, `hmemGauge`, `hosc`, `hprod`,
`hshell`, `hgradM` and the two constants `hCdef`, `hgate`, `hC1`, `hgrad0`.  No
`Closure.ClosureStep5Input` is claimed.

## The per-cube base point

This module used to route through a single-window declaration
`step5GaugeEndpoint_of_correctors` (since removed), whose `hdefect` and
`hmemGauge` read the forcing gauge of `e.nablaw.oscillations` at **one** base
point `z0`:

```
  step5CrossDefect R omega n (n+h) e (grad w_D)
    <= Cdef * ( meshOscillationCell nmesh (grad w_D) R
                * (3^nmesh * shellDerivNormSum n (n+h) z0 omega) ) .
```

That binder is not dischargeable.  The left factor `meshOscillationCell nmesh u
R` is the mean square oscillation on `openCubeAtScale (triadicCubeShift R)
nmesh`, sited at the cube `R`'s own base point, whereas `shellDerivNormSum n
(n+h) z0 omega` is an `L^infty` gauge on the **single** window `z0 + cu_n`.
The per-cube step is the deterministic mean value inequality followed by
Cauchy--Schwarz on `R`, and it needs the gauge on a window containing `cubeSet
R`; as `K -> infinity` the grid tiles `cu_K`, so all but finitely many of its
cubes lie outside `z0 + cu_n`, and `Frozen.Assumptions.ShellField` is an
arbitrary `C^2` skew field.

```
  fun R omega => 3^nmesh * shellDerivNormSum n (n+h) (triadicCubeShift R) omega ,
```

for which `Closure.Step5DefectGauge.step5CrossDefect_le_meshOscillationCell`
proves `hdefect` outright at `R.scale = K - j = nmesh <= n` (carried out in
`Closure.Step5Basket`), and for which
`ApproximateRecurrence.LocalizationOscillationTail.gridFourthMoment_shellDerivNormSum_le`
is uniform in the base point, so `hosc` keeps its present strength.

## References

* ABK26, `e.lower.bound.pre1`; `e.nablaw.oscillations`;
  `e.lower.bound.oscillations`; `e.lower.bound.pre2`; `e.def.w`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Spatial regularity of an `H^1` gradient on a triadic cube -/

theorem memLp_two_grad_normalizedCubeMeasure (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) :
    MemLp u.grad (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  have h : MemLp u.grad (2 : ℝ≥0∞) (volume.restrict (openCubeSet Q)) := by
    simpa [MemVectorL2, volumeMeasureOn] using u.grad_memVectorL2
  have h2 : MemLp u.grad (2 : ℝ≥0∞) (volume.restrict (cubeSet Q)) := by
    rwa [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
  exact memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q
    (by simpa [MemVectorL2, volumeMeasureOn] using h2)

theorem memLp_two_grad_normalizedCubeMeasure_descendant {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (u : H1Function (openCubeSet Q)) :
    MemLp u.grad (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
  memLp_normalizedCubeMeasure_of_mem_descendantsAtDepth hR
    (memLp_two_grad_normalizedCubeMeasure Q u)

theorem integrableOn_cubeSet_vecNormSq_grad (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) :
    IntegrableOn (fun x => vecNormSq (u.grad x)) (cubeSet Q) volume := by
  have hmem := memLp_two_grad_normalizedCubeMeasure Q u
  have hE : MemLp (fun x => Book.Ch02.vecNorm (u.grad x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := memLp_vecNorm_eight_of_memLp_eight Q hmem
  have hint : Integrable (fun x => vecNormSq (u.grad x)) (normalizedCubeMeasure Q) := by
    have h := hE.integrable_sq
    have hfun : (fun x => Book.Ch02.vecNorm (u.grad x) ^ (2 : ℕ)) =
        fun x => vecNormSq (u.grad x) :=
      funext fun x => Book.Ch02.vecNorm_sq_eq_vecNormSq (u.grad x)
    rwa [hfun] at h
  have hne : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (cubeVolume_pos Q))).ne'
  rw [normalizedCubeMeasure] at hint
  exact (integrable_smul_measure hne ENNReal.ofReal_ne_top).1 hint

/-! ## Per-cube Jensen and the descendant volume comparison -/

theorem vecNormSq_cubeAverageVec_le_cubeAverage_vecNormSq (R : TriadicCube d)
    (g : Vec d → Vec d) (hg : MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    vecNormSq (cubeAverageVec R g) ≤ cubeAverage R (fun x => vecNormSq (g x)) := by
  have h1 := vecNormSq_cubeAverageVec_le_sum_cubeAverage_sq_of_memLp R g hg
  rw [cubeAverage_vecNormSq_eq_sum_cubeAverage_sq_of_memLp R g hg]
  exact h1

theorem cubeAverage_le_of_mem_descendantsAtDepth {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) {f : Vec d → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hint : IntegrableOn f (cubeSet Q) volume) :
    cubeAverage R f ≤ (cubeVolume Q / cubeVolume R) * cubeAverage Q f := by
  have hsub : cubeSet R ⊆ cubeSet Q := cubeSet_subset_of_mem_descendantsAtDepth hR
  have hQ : (0 : ℝ) < cubeVolume Q := cubeVolume_pos Q
  have hR0 : (0 : ℝ) < cubeVolume R := cubeVolume_pos R
  have hmono : ∫ x in cubeSet R, f x ≤ ∫ x in cubeSet Q, f x :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall hf0)
      (LE.le.eventuallyLE hsub)
  have hstep : (cubeVolume R)⁻¹ * ∫ x in cubeSet R, f x ≤
      (cubeVolume R)⁻¹ * ∫ x in cubeSet Q, f x :=
    mul_le_mul_of_nonneg_left hmono (inv_nonneg.2 hR0.le)
  have hEq : (cubeVolume R)⁻¹ * ∫ x in cubeSet Q, f x =
      (cubeVolume Q / cubeVolume R) * ((cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, f x) := by
    field_simp
  change (cubeVolume R)⁻¹ * ∫ x in cubeSet R, f x ≤
    (cubeVolume Q / cubeVolume R) * ((cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, f x)
  rw [← hEq]
  exact hstep

/-- The descendant-cube average of the squared gradient length is dominated by
the parent's energy, at the explicit volume ratio. -/
theorem vecNormSq_cubeAverageVec_le_ratio_mul_cubeAverage {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (u : H1Function (openCubeSet Q)) :
    vecNormSq (cubeAverageVec R (fun x => u.grad x)) ≤
      (cubeVolume Q / cubeVolume R) *
        cubeAverage Q (fun x => vecDot (u.grad x) (u.grad x)) :=
  le_trans
    (vecNormSq_cubeAverageVec_le_cubeAverage_vecNormSq R _
      (memLp_two_grad_normalizedCubeMeasure_descendant hR u))
    (cubeAverage_le_of_mem_descendantsAtDepth hR
      (fun x => vecNormSq_nonneg (u.grad x)) (integrableOn_cubeSet_vecNormSq_grad Q u))

/-! ## The descendant cube average as a continuous functional of the class -/

private theorem restrict_cubeSet_inter_openCubeSet {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) :
    volume.restrict (cubeSet R ∩ openCubeSet Q) = volume.restrict (cubeSet R) := by
  have hsub : cubeSet R ⊆ cubeSet Q := cubeSet_subset_of_mem_descendantsAtDepth hR
  have hinter : ((cubeSet R ∩ openCubeSet Q : Set (Vec d))) =ᵐ[volume]
      ((cubeSet R ∩ cubeSet Q : Set (Vec d))) :=
    (Filter.EventuallyEqSet.refl _ (cubeSet R)).inter (cubeSet_ae_eq_openCubeSet Q).symm
  rw [Set.inter_eq_self_of_subset_left hsub] at hinter
  exact Measure.restrict_congr_set hinter

theorem setIntegral_cubeSet_grad_coord_eq_clm (Q : TriadicCube d)
    [IsFiniteMeasure (volumeMeasureOn (openCubeSet Q))]
    {R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) (i : Fin d)
    (u : H1Function (openCubeSet Q)) :
    hilbertVectorL2CoordSetIntegralCLM (U := openCubeSet Q) (cubeSet R)
        (measurableSet_cubeSet R) i u.gradToHilbertVectorL2
      = ∫ x in cubeSet R, u.grad x i ∂volume := by
  rw [hilbertVectorL2CoordSetIntegralCLM_apply]
  have hcoord : (fun x => (u.gradToHilbertVectorL2 : Vec d → HilbertVec d) x i)
      =ᵐ[volumeMeasureOn (openCubeSet Q)] fun x => u.grad x i := by
    filter_upwards [u.coeFn_gradToHilbertVectorL2] with x hx
    rw [hx]
    simp [hilbertifyVecField]
  have hstep : ∫ x in cubeSet R, (u.gradToHilbertVectorL2 : Vec d → HilbertVec d) x i
        ∂volumeMeasureOn (openCubeSet Q)
      = ∫ x in cubeSet R, u.grad x i ∂volumeMeasureOn (openCubeSet Q) :=
    integral_congr_ae (ae_restrict_of_ae hcoord)
  rw [hstep]
  change ∫ x, u.grad x i ∂((volume.restrict (openCubeSet Q)).restrict (cubeSet R)) = _
  rw [Measure.restrict_restrict (measurableSet_cubeSet R),
    restrict_cubeSet_inter_openCubeSet hR]

/-! ## The Neumann family: continuity of the descendant cube average -/

theorem continuous_cubeAverageVec_closureNeumannFamily (c : ℝ) (e : Vec d) (K : ℕ)
    {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) j) :
    Continuous fun f : C(Vec d, Mat d) =>
      cubeAverageVec R
        (fun x => (closureNeumannFamily c e K f).toH1Function.grad x) := by
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d (K : ℤ)))) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet _
  refine continuous_pi fun i => ?_
  have hEq : (fun f : C(Vec d, Mat d) =>
        cubeAverageVec R
          (fun x => (closureNeumannFamily c e K f).toH1Function.grad x) i) =
      fun f : C(Vec d, Mat d) => (cubeVolume R)⁻¹ *
        (hilbertVectorL2CoordSetIntegralCLM (U := openCubeSet (originCube d (K : ℤ)))
          (cubeSet R) (measurableSet_cubeSet R) i
          ((closureNeumannFamily c e K f).gradToHilbertVectorL2)) := by
    funext f
    change (cubeVolume R)⁻¹ *
        ∫ x in cubeSet R, (closureNeumannFamily c e K f).toH1Function.grad x i ∂volume = _
    rw [← setIntegral_cubeSet_grad_coord_eq_clm (originCube d (K : ℤ)) hR i
      (closureNeumannFamily c e K f).toH1Function]
    rfl
  rw [hEq]
  exact continuous_const.mul
    ((hilbertVectorL2CoordSetIntegralCLM (U := openCubeSet (originCube d (K : ℤ)))
      (cubeSet R) (measurableSet_cubeSet R) i).continuous.comp
      (continuous_gradToHilbertVectorL2_closureNeumannFamily c e K))

/-! ## The two sample-integrability binders of Step 4 -/

open Algsuperdiff.Section3.Provider.Corrector (realize valuePathForcing
  shellSumValuePathLaw continuous_toVec_realize_valuePathForcing
  stronglyMeasurable_valuePathForcing memLp_two_valuePathForcing_shellSum
  integrable_cubeAverage_neumann_energy
  isSolenoidalZeroNormalTraceOn_grad_add_of_isMeanZeroNeumannRhsWeakSolution_one) in
/-- The Step-4 binder `hsampK` at the closure's Neumann family, on the increment
path law. -/
theorem integrable_cubeAverage_closureNeumannEnergy_path (M : ABKModel d) (c : ℝ)
    (e : Vec d) (n m : ℤ) (K : ℕ) :
    Integrable (fun f : C(Vec d, Mat d) => cubeAverage (originCube d (K : ℤ))
        (fun x => vecDot ((closureNeumannFamily c e K f).toH1Function.grad x)
          ((closureNeumannFamily c e K f).toH1Function.grad x)))
      (shellSumValuePathLaw M.P n m).toMeasure := by
  have := isFiniteMeasure_volumeMeasureOn_openCubeSet (originCube d (K : ℤ))
  have hmem : ∀ f : C(Vec d, Mat d),
      MemVectorL2 (openCubeSet (originCube d (K : ℤ)))
        (fun x => (realize (valuePathForcing (c • e)) f x).toVec) := fun f =>
    memVectorL2_openCubeSet_of_continuous _
      (continuous_toVec_realize_valuePathForcing (c • e) f)
  exact integrable_cubeAverage_neumann_energy (originCube d (K : ℤ))
    (Nfam := fun f => (closureNeumannFamily c e K f).toH1Function.grad)
    (stronglyMeasurable_valuePathForcing (c • e))
    (memLp_two_valuePathForcing_shellSum M (c • e) n m)
    (Filter.Eventually.of_forall fun f =>
      (closureNeumannFamily c e K f).toH1Function.isPotentialOn)
    (Filter.Eventually.of_forall fun f =>
      isSolenoidalZeroNormalTraceOn_grad_add_of_isMeanZeroNeumannRhsWeakSolution_one
        (hmem f) (isMeanZeroNeumannRhsWeakSolution_closureNeumannFamily c e K f))

open Algsuperdiff.Section3.Provider.Corrector (shellSumValuePath
  measurePreserving_shellSumValuePath_cutoffSample) in
/-- The Step-4 binder `hsampK` at the closure's Neumann family. -/
theorem integrable_cubeAverage_closureNeumannEnergy_cutoff (M : ABKModel d)
    (e : Vec d) (n : ℤ) (h : ℕ) (K : ℕ) :
    Integrable (fun omega : CutoffSample d =>
      cubeAverage (originCube d (K : ℤ))
        (fun x => vecDot
          ((alongIncrementPath n h
            (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
              omega.val).toH1Function.grad x)
          ((alongIncrementPath n h
            (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
              omega.val).toH1Function.grad x)))
      (cutoffSampleLaw M).toMeasure :=
  ((measurePreserving_shellSumValuePath_cutoffSample M n (n + (h : ℤ))).integrable_comp
      (aestronglyMeasurable_cubeAverage_closureNeumannFamily M n h e K)).2
    (integrable_cubeAverage_closureNeumannEnergy_path M
      ((Annealed.sigmaBar M n : ℝ))⁻¹ e n (n + (h : ℤ)) K)

theorem continuous_vecNormSq_cubeAverageVec_closureNeumannFamily (c : ℝ) (e : Vec d)
    (K : ℕ) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) j) :
    Continuous fun f : C(Vec d, Mat d) => vecNormSq (cubeAverageVec R
      (fun x => (closureNeumannFamily c e K f).toH1Function.grad x)) := by
  have hc := continuous_cubeAverageVec_closureNeumannFamily c e K hR
  change Continuous fun f : C(Vec d, Mat d) => ∑ i : Fin d,
      cubeAverageVec R (fun x => (closureNeumannFamily c e K f).toH1Function.grad x) i *
        cubeAverageVec R (fun x => (closureNeumannFamily c e K f).toH1Function.grad x) i
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp hc).mul ((continuous_apply i).comp hc)

open Algsuperdiff.Section3.Provider.Corrector (shellSumValuePathLaw) in
/-- The Step-4 binder `hsampR` at the closure's Neumann family, on the increment
path law: per-cube Jensen dominates the per-cube average by the cube energy. -/
theorem integrable_vecNormSq_cubeAverageVec_closureNeumannFamily_path
    (M : ABKModel d) (c : ℝ) (e : Vec d) (n m : ℤ) (K : ℕ) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) j) :
    Integrable (fun f : C(Vec d, Mat d) => vecNormSq (cubeAverageVec R
      (fun x => (closureNeumannFamily c e K f).toH1Function.grad x)))
      (shellSumValuePathLaw M.P n m).toMeasure := by
  refine Integrable.mono'
    ((integrable_cubeAverage_closureNeumannEnergy_path M c e n m K).const_mul
      (cubeVolume (originCube d (K : ℤ)) / cubeVolume R))
    (continuous_vecNormSq_cubeAverageVec_closureNeumannFamily c e K
      hR).measurable.aestronglyMeasurable ?_
  filter_upwards with f
  rw [Real.norm_eq_abs, abs_of_nonneg (vecNormSq_nonneg _)]
  exact vecNormSq_cubeAverageVec_le_ratio_mul_cubeAverage hR
    (closureNeumannFamily c e K f).toH1Function

open Algsuperdiff.Section3.Provider.Corrector (shellSumValuePath
  measurePreserving_shellSumValuePath_cutoffSample) in
/-- The Step-4 binder `hsampR` at the closure's Neumann family. -/
theorem integrable_vecNormSq_cubeAverageVec_closureNeumannFamily_cutoff
    (M : ABKModel d) (e : Vec d) (n : ℤ) (h : ℕ) (K : ℕ) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) j) :
    Integrable (fun omega : CutoffSample d => vecNormSq (cubeAverageVec R
      (fun x => (alongIncrementPath n h
        (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
          omega.val).toH1Function.grad x)))
      (cutoffSampleLaw M).toMeasure :=
  ((measurePreserving_shellSumValuePath_cutoffSample M n (n + (h : ℤ))).integrable_comp
      (continuous_vecNormSq_cubeAverageVec_closureNeumannFamily
        ((Annealed.sigmaBar M n : ℝ))⁻¹ e K hR).measurable.aestronglyMeasurable).2
    (integrable_vecNormSq_cubeAverageVec_closureNeumannFamily_path M
      ((Annealed.sigmaBar M n : ℝ))⁻¹ e n (n + (h : ℤ)) K hR)

/-! ## The Step-4 endpoint at the closure families, and the input -/

theorem step4GaugeEndpoint_closureFamilies [NeZero d] (M : ABKModel d) (n : ℤ) (h : ℕ)
    (K j : ℕ) {e : Vec d} (he : vecNormSq e = 1) :
    Step4GaugeEndpoint M n h K j e
      (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ 0 K)
      (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K) :=
  step4GaugeEndpoint_of_correctors M n h K j he _ _
    (fun omega => isZeroTraceDirichletRhsWeakSolution_alongIncrementPath
      ((Annealed.sigmaBar M n : ℝ))⁻¹ 0 K n h omega)
    (fun omega _R hR => memLp_two_grad_normalizedCubeMeasure_descendant hR
      (alongIncrementPath n h
        (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K) omega).toH1Function)
    (fun omega => integrableOn_cubeSet_vecNormSq_grad (originCube d (K : ℤ))
      (alongIncrementPath n h
        (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K) omega).toH1Function)
    (fun _R hR =>
      integrable_vecNormSq_cubeAverageVec_closureNeumannFamily_cutoff M e n h K hR)
    (integrable_cubeAverage_closureNeumannEnergy_cutoff M e n h K)

/-- **`Closure.ClosureStep4Input`, produced.** -/
theorem closureStep4Input (d : ℕ) [NeZero d] : ClosureStep4Input d := fun _hd =>
  ⟨1, one_pos, fun M n h _Ec _e he _hreg =>
    Filter.Eventually.of_forall fun K =>
      step4GaugeEndpoint_closureFamilies M n h K (closureMeshDepth M n h K) he⟩

/-! ## The Dirichlet mirror: the Step-5 analytic side conditions -/

open Algsuperdiff.Section3.Provider.Corrector (realize valuePathForcing
  shellSumValuePathLaw continuous_toVec_realize_valuePathForcing
  stronglyMeasurable_valuePathForcing memLp_two_valuePathForcing_shellSum
  integrable_cubeAverage_dirichlet_energy
  isSolenoidalOn_grad_add_of_isZeroTraceDirichletRhsWeakSolution_one) in
theorem integrable_cubeAverage_closureDirichletEnergy_path [NeZero d] (M : ABKModel d)
    (c : ℝ) (e : Vec d) (n m : ℤ) (K : ℕ) :
    Integrable (fun f : C(Vec d, Mat d) => cubeAverage (originCube d (K : ℤ))
        (fun x => vecDot ((closureDirichletFamily c e K f).toH1Function.grad x)
          ((closureDirichletFamily c e K f).toH1Function.grad x)))
      (shellSumValuePathLaw M.P n m).toMeasure := by
  have := isFiniteMeasure_volumeMeasureOn_openCubeSet (originCube d (K : ℤ))
  have hmem : ∀ f : C(Vec d, Mat d),
      MemVectorL2 (openCubeSet (originCube d (K : ℤ)))
        (fun x => (realize (valuePathForcing (c • e)) f x).toVec) := fun f =>
    memVectorL2_openCubeSet_of_continuous _
      (continuous_toVec_realize_valuePathForcing (c • e) f)
  exact integrable_cubeAverage_dirichlet_energy (originCube d (K : ℤ))
    (Dfam := fun f => (closureDirichletFamily c e K f).toH1Function.grad)
    (stronglyMeasurable_valuePathForcing (c • e))
    (memLp_two_valuePathForcing_shellSum M (c • e) n m)
    (Filter.Eventually.of_forall fun f =>
      (closureDirichletFamily c e K f).isPotentialZeroTraceOn)
    (Filter.Eventually.of_forall fun f =>
      isSolenoidalOn_grad_add_of_isZeroTraceDirichletRhsWeakSolution_one
        (hmem f) (isZeroTraceDirichletRhsWeakSolution_closureDirichletFamily c e K f))

open Algsuperdiff.Section3.Provider.Corrector (shellSumValuePath
  measurePreserving_shellSumValuePath_cutoffSample) in
/-- The Step-5 binder `hsampG` at the closure's Dirichlet family. -/
theorem integrable_cubeAverage_closureDirichletEnergy_cutoff [NeZero d] (M : ABKModel d)
    (e : Vec d) (n : ℤ) (h : ℕ) (K : ℕ) :
    Integrable (fun omega : CutoffSample d =>
      cubeAverage (originCube d (K : ℤ))
        (fun x => vecNormSq
          ((alongIncrementPath n h
            (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
              omega.val).toH1Function.grad x)))
      (cutoffSampleLaw M).toMeasure :=
  ((measurePreserving_shellSumValuePath_cutoffSample M n (n + (h : ℤ))).integrable_comp
      (aestronglyMeasurable_cubeAverage_closureDirichletFamily M n h e K)).2
    (integrable_cubeAverage_closureDirichletEnergy_path M
      ((Annealed.sigmaBar M n : ℝ))⁻¹ e n (n + (h : ℤ)) K)

theorem continuous_cubeAverageVec_closureDirichletFamily [NeZero d] (c : ℝ) (e : Vec d)
    (K : ℕ) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) j) :
    Continuous fun f : C(Vec d, Mat d) =>
      cubeAverageVec R
        (fun x => (closureDirichletFamily c e K f).toH1Function.grad x) := by
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d (K : ℤ)))) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet _
  refine continuous_pi fun i => ?_
  have hEq : (fun f : C(Vec d, Mat d) =>
        cubeAverageVec R
          (fun x => (closureDirichletFamily c e K f).toH1Function.grad x) i) =
      fun f : C(Vec d, Mat d) => (cubeVolume R)⁻¹ *
        (hilbertVectorL2CoordSetIntegralCLM (U := openCubeSet (originCube d (K : ℤ)))
          (cubeSet R) (measurableSet_cubeSet R) i
          ((closureDirichletFamily c e K f).toH1Function.gradToHilbertVectorL2)) := by
    funext f
    change (cubeVolume R)⁻¹ *
        ∫ x in cubeSet R, (closureDirichletFamily c e K f).toH1Function.grad x i ∂volume = _
    rw [← setIntegral_cubeSet_grad_coord_eq_clm (originCube d (K : ℤ)) hR i
      (closureDirichletFamily c e K f).toH1Function]
  rw [hEq]
  exact continuous_const.mul
    ((hilbertVectorL2CoordSetIntegralCLM (U := openCubeSet (originCube d (K : ℤ)))
      (cubeSet R) (measurableSet_cubeSet R) i).continuous.comp
      (continuous_gradToHilbertVectorL2_closureDirichletFamily c e K))

theorem continuous_vecNormSq_cubeAverageVec_closureDirichletFamily [NeZero d] (c : ℝ)
    (e : Vec d) (K : ℕ) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) j) :
    Continuous fun f : C(Vec d, Mat d) => vecNormSq (cubeAverageVec R
      (fun x => (closureDirichletFamily c e K f).toH1Function.grad x)) := by
  have hc := continuous_cubeAverageVec_closureDirichletFamily c e K hR
  change Continuous fun f : C(Vec d, Mat d) => ∑ i : Fin d,
      cubeAverageVec R (fun x => (closureDirichletFamily c e K f).toH1Function.grad x) i *
        cubeAverageVec R
          (fun x => (closureDirichletFamily c e K f).toH1Function.grad x) i
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp hc).mul ((continuous_apply i).comp hc)

open Algsuperdiff.Section3.Provider.Corrector (shellSumValuePathLaw) in
theorem integrable_vecNormSq_cubeAverageVec_closureDirichletFamily_path [NeZero d]
    (M : ABKModel d) (c : ℝ) (e : Vec d) (n m : ℤ) (K : ℕ) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) j) :
    Integrable (fun f : C(Vec d, Mat d) => vecNormSq (cubeAverageVec R
      (fun x => (closureDirichletFamily c e K f).toH1Function.grad x)))
      (shellSumValuePathLaw M.P n m).toMeasure := by
  refine Integrable.mono'
    ((integrable_cubeAverage_closureDirichletEnergy_path M c e n m K).const_mul
      (cubeVolume (originCube d (K : ℤ)) / cubeVolume R))
    (continuous_vecNormSq_cubeAverageVec_closureDirichletFamily c e K
      hR).measurable.aestronglyMeasurable ?_
  filter_upwards with f
  rw [Real.norm_eq_abs, abs_of_nonneg (vecNormSq_nonneg _)]
  exact vecNormSq_cubeAverageVec_le_ratio_mul_cubeAverage hR
    (closureDirichletFamily c e K f).toH1Function

open Algsuperdiff.Section3.Provider.Corrector (shellSumValuePath
  measurePreserving_shellSumValuePath_cutoffSample) in
/-- The Step-5 binder `hsampN` at the closure's Dirichlet family. -/
theorem integrable_vecNormSq_cubeAverageVec_closureDirichletFamily_cutoff [NeZero d]
    (M : ABKModel d) (e : Vec d) (n : ℤ) (h : ℕ) (K : ℕ) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) j) :
    Integrable (fun omega : CutoffSample d => vecNormSq (cubeAverageVec R
      (fun x => (alongIncrementPath n h
        (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
          omega.val).toH1Function.grad x)))
      (cutoffSampleLaw M).toMeasure :=
  ((measurePreserving_shellSumValuePath_cutoffSample M n (n + (h : ℤ))).integrable_comp
      (continuous_vecNormSq_cubeAverageVec_closureDirichletFamily
        ((Annealed.sigmaBar M n : ℝ))⁻¹ e K hR).measurable.aestronglyMeasurable).2
    (integrable_vecNormSq_cubeAverageVec_closureDirichletFamily_path M
      ((Annealed.sigmaBar M n : ℝ))⁻¹ e n (n + (h : ℤ)) K hR)

/-! ## The Step-5 endpoint at the closure families, reduced to the residual legs -/

/-- **`Closure.Step5GaugeEndpoint` at the closure's own corrector families and at
the per-cube forcing gauge, with the seven analytic side conditions of
`step5GaugeEndpoint_of_correctors_gauge` discharged.**

`hgauge0` is the nonnegativity of the gauge; `hD`, `hN` are the two halves of
`e.def.w` at the closure families; `hmemD`, `hintD`, `hsampN`, `hsampG` are the
Dirichlet mirrors of the four Step-4 routes.  What is left is exactly the
mathematical legs.

The forcing gauge is read at each cube's **own** base point, so the base-point
obstruction recorded in earlier versions of the module docstring no longer
applies: `hdefect` is dischargeable, and `Closure.Step5Basket` discharges it. -/
theorem step5GaugeEndpoint_closureFamilies_of_legs [NeZero d] (M : ABKModel d) (n : ℤ)
    (h : ℕ) (K j : ℕ) {e : Vec d} (he : vecNormSq e = 1) (nmesh : ℤ)
    {C1 C2 Cdef shellMoment gradMoment : ℝ}
    (hCdef : 0 ≤ Cdef) (hgate : Cdef * M.gamma ^ (15 : ℕ) ≤ 2)
    (hintP : ∀ omega : ShellSeq d, IntegrableOn
      (fun x => vecDot e (matVecMul (finiteShellIncrement omega n (n + (h : ℤ)) x)
        ((alongIncrementPath n h (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
          omega).toH1Function.grad x)))
      (cubeSet (originCube d (K : ℤ))) volume)
    (hsampX : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
          (fun omega : CutoffSample d =>
            vecDot e (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h (closureDirichletFamily ((Annealed.sigmaBar M n :
            ℝ))⁻¹ e K) omega.val).toH1Function.grad x))))
          (cutoffSampleLaw M).toMeasure)
    (hsampS : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
          (fun omega : CutoffSample d =>
            vecNormSq (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h (closureDirichletFamily ((Annealed.sigmaBar M n :
            ℝ))⁻¹ e K) omega.val).toH1Function.grad x))))
          (cutoffSampleLaw M).toMeasure)
    (hsampDef : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
          (fun omega : CutoffSample d =>
            step5CrossDefect R omega.val n (n + (h : ℤ)) e
          (fun x => (alongIncrementPath n h (closureDirichletFamily ((Annealed.sigmaBar M n :
            ℝ))⁻¹ e K) omega.val).toH1Function.grad x))
          (cutoffSampleLaw M).toMeasure)
    (hdefect : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j, ∀ omega : CutoffSample d,
      step5CrossDefect R omega.val n (n + (h : ℤ)) e
          (fun x => (alongIncrementPath n h (closureDirichletFamily ((Annealed.sigmaBar M n :
            ℝ))⁻¹ e K) omega.val).toH1Function.grad x) ≤ Cdef * ((meshOscillationCell nmesh
        (fun x => (alongIncrementPath n h (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹
          e K) omega.val).toH1Function.grad x) R) * ((3 : ℝ) ^ ((nmesh : ℤ) : ℝ) *
        shellDerivNormSum n (n + (h : ℤ)) (triadicCubeShift R) omega.val)))
    (hmemOsc : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      MemLp
          (fun omega : CutoffSample d =>
            meshOscillationCell nmesh
        (fun x => (alongIncrementPath n h (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹
          e K) omega.val).toH1Function.grad x) R) 4
          (cutoffSampleLaw M).toMeasure)
    (hmemGauge : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      MemLp
          (fun omega : CutoffSample d =>
            (3 : ℝ) ^ ((nmesh : ℤ) : ℝ) *
        shellDerivNormSum n (n + (h : ℤ)) (triadicCubeShift R) omega.val) 4
          (cutoffSampleLaw M).toMeasure)
    (hosc : (gridFourthMomentRoot (cutoffSampleLaw M).toMeasure (descendantsAtDepth (originCube d
      (K : ℤ)) j)
      (fun R omega => meshOscillationCell nmesh
        (fun x => (alongIncrementPath n h (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹
          e K) omega.val).toH1Function.grad x) R)) + ((Annealed.sigmaBar M n : ℝ))⁻¹ *
      gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
        (descendantsAtDepth (originCube d (K : ℤ)) j)
        (fun (R : TriadicCube d) (omega : CutoffSample d) =>
          (3 : ℝ) ^ ((nmesh : ℤ) : ℝ) *
            shellDerivNormSum n (n + (h : ℤ)) (triadicCubeShift R) omega.val) ≤
      M.gamma ^ (15 : ℕ))
    (hC1 : 0 ≤ C1) (hgrad0 : 0 ≤ gradMoment)
    (hprod : descendantsAverage (originCube d (K : ℤ)) j
          (fun R => ∫ omega : CutoffSample d,
            vecNormSq (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h (closureDirichletFamily ((Annealed.sigmaBar M n :
            ℝ))⁻¹ e K) omega.val).toH1Function.grad x)))
            ∂(cutoffSampleLaw M).toMeasure)
      ≤ shellMoment * gradMoment)
    (hshell : shellMoment ≤
      C1 * (h : ℝ) * (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)))
    (hgradM : gradMoment ≤
      C2 * (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ * (h : ℝ) *
        (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))) :
    Step5GaugeEndpoint M n h K j e (C1 * C2) (closureDirichletFamily ((Annealed.sigmaBar M n :
      ℝ))⁻¹ e K) (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ 0 K) :=
  step5GaugeEndpoint_of_correctors_gauge M n h K j he nmesh
    (fun (R : TriadicCube d) (omega : CutoffSample d) =>
      (3 : ℝ) ^ ((nmesh : ℤ) : ℝ) *
        shellDerivNormSum n (n + (h : ℤ)) (triadicCubeShift R) omega.val)
    _ _
    (fun R omega => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (shellDerivNormSum_nonneg n (n + (h : ℤ)) (triadicCubeShift R) omega.val))
    hCdef hgate
    (fun omega => isZeroTraceDirichletRhsWeakSolution_alongIncrementPath
      ((Annealed.sigmaBar M n : ℝ))⁻¹ e K n h omega)
    (fun omega => isMeanZeroNeumannRhsWeakSolution_alongIncrementPath
      ((Annealed.sigmaBar M n : ℝ))⁻¹ 0 K n h omega)
    (fun omega _R hR => memLp_two_grad_normalizedCubeMeasure_descendant hR
      (alongIncrementPath n h (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
        omega).toH1Function)
    (fun omega => integrableOn_cubeSet_vecNormSq_grad (originCube d (K : ℤ))
      (alongIncrementPath n h (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
        omega).toH1Function)
    hintP
    (fun _R hR =>
      integrable_vecNormSq_cubeAverageVec_closureDirichletFamily_cutoff M e n h K hR)
    hsampX hsampS hsampDef
    (integrable_cubeAverage_closureDirichletEnergy_cutoff M e n h K)
    hdefect hmemOsc hmemGauge hosc hC1 hgrad0 hprod hshell hgradM

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
