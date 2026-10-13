/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.Junctions
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.ClosureGaugeCollapse
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.CubeJensenVec

/-!
# JunctionDischargeStepFour

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-4 gauge junction, discharged at the finite localization cube

This module discharges `Closure.Step4GaugeEndpoint` --- the finite-`K` form of
`e.lower.bound.pre1`, i.e. the manuscript's own inner Jensen display, which is
what prescribes in place of the undischargeable `limsup` form.  The passage to
the drift is *not* here: it is the limit passage inside the assembly skeletons
of `Closure.Junctions`.

## The chain

At the Step-4 branch `e = 0` and at a unit direction `e'`:

```
  |Ahom^{1/2} G_{-(h)_R} Ahom^{-1/2} P_R|^2
    = |e' + (grad w_D)_R|^2
      + |(grad w_N + shom^{-1} h e')_R - shom^{-1}(h)_R (e' + (grad w_D)_R)|^2
    = |e'|^2 + |(grad w_N)_R|^2
```



the second equality being the conjunction of three facts, each supplied below:

* `cubeAverageVec_eq_zero_of_ae_eq_zero_openCubeSet` --- at `e = 0` the
  Dirichlet forcing vanishes identically, so the Dirichlet corrector's gradient
  is a.e. `0` on `cu_K` (`FreshShellSumZeroDirection`) and its average over every
  descendant cube of `cu_K` is `0`;
* `cubeAverageVec_streamForcing` --- **link (i)**, the cube-average/`matVecMul`
  interchange `(shom^{-1} h e')_R = shom^{-1} (h)_R e'`, which is exactly what
  cancels the shell term of `e.Pz.def` against the gauge shear of
  `ClosureGaugeCollapse`;
* `blockVecDot_gaugedPrincipalLoadShell_blockDiag_potential` --- the resulting
  per-cube identity, at the terminal's own load.

Averaging over the descendant grid and taking the sample expectation then gives
the endpoint through **link (ii)**,
`descendantsAverage_vecNormSq_cubeAverageVec_le_cubeAverage`, the descendant-
tiling Jensen step `avsum_R |(grad w)_R|^2 <= avg_{cu_K} |grad w|^2`: per-cube
Jensen, then the exact tiling identity
`cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn`.

## What is supplied

* `integrableOn_cubeSet_of_continuous` --- a continuous field is integrable on a
  triadic cube (a helper for producers discharging the `hint` binder of
  link (ii)).
* `cubeAverageVec_streamForcing` --- link (i), unconditional.
* `descendantsAverage_vecNormSq_cubeAverageVec_le_cubeAverage` --- link (ii).
* `cubeAverageVec_eq_zero_of_ae_eq_zero_openCubeSet` --- the descendant-average
  vanishing of an a.e.-zero field.
* `blockVecDot_gaugedPrincipalLoadShell_blockDiag_potential` --- the per-cube
  collapse at the Step-4 branch.
* `step4GaugeEndpoint_of_correctors` --- `Closure.Step4GaugeEndpoint`, proved.

## The binders of the endpoint, and their producers

`hD` is `e.def.w`, Dirichlet leg, read at the Step-6 branch direction `e = 0`;
it is the definition of the Dirichlet corrector, not an assumption about it.
The remaining four are analytic side conditions of the displays themselves:

| binder | content | producer |
|---|---|---|
| `hmemN` | `grad w_N^{(K)} in L^2` of each descendant cube | `H1MeanZeroFunction` membership, restricted along `openCubeSet_subset_of_mem_descendantsAtDepth` |
| `hintN` | `|grad w_N^{(K)}|^2` integrable on `cu_K` | the same membership |
| `hsampR` | the per-cube energy is sample integrable | `Corrector.CorrectorMeasurableGradient` + domination by `hsampK` |
| `hsampK` | `E[||grad w_N^{(K)}||^2_{L2(cu_K)}]` exists | `Corrector.CorrectorLimitNode.integrable_cubeAverage_neumann_energy` |

None of them is a mathematical premise of the manuscript's Step 4: each is a
measurability/finiteness statement about the very objects the display is about,
and each is charged forward to a named proved module.  No smallness, no
normalization and no bound is assumed.

## References

* ABK26, `e.lower.bound.pre1`; `e.Pz.def`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector

noncomputable section

variable {d : ℕ}

/-! ## Link (i): the cube-average/`matVecMul` interchange -/

theorem integrableOn_cubeSet_of_continuous (R : TriadicCube d) {f : Vec d → ℝ}
    (hf : Continuous f) : IntegrableOn f (cubeSet R) volume := by
  have hK : IsCompact (Metric.closedBall (cubeCenter R) (cubeRadius R)) :=
    isCompact_closedBall _ _
  exact (hf.continuousOn.integrableOn_compact hK).mono_set (cubeSet_subset_closedBall R)

theorem cubeAverageVec_streamForcing (R : TriadicCube d) (c : ℝ)
    (omega : ShellSeq d) (n m : ℤ) (e' : Vec d) :
    cubeAverageVec R (streamForcing c omega n m e')
      = c • matVecMul (freshShellCubeAverage R omega n m) e' := by
  classical
  have hcont := continuous_finiteShellIncrement omega n m
  funext i
  have hint : ∀ l : Fin d, Integrable
      (fun x => finiteShellIncrement omega n m x i l) (normalizedCubeMeasure R) := fun l =>
    (memLp_normalizedCubeMeasure_of_continuous R 1
      ((continuous_apply l).comp ((continuous_apply i).comp hcont))).integrable le_rfl
  show cubeAverage R (fun x => c * ∑ l, finiteShellIncrement omega n m x i l * e' l)
    = c * ∑ l, freshShellCubeAverage R omega n m i l * e' l
  rw [cubeAverage_const_mul]
  congr 1
  rw [show (fun x : Vec d => ∑ l, finiteShellIncrement omega n m x i l * e' l)
      = fun x : Vec d => ∑ l, e' l * finiteShellIncrement omega n m x i l from
      funext fun x => Finset.sum_congr rfl fun l _ => mul_comm _ _,
    cubeAverage_finset_sum_of_integrable R Finset.univ
      (fun l x => e' l * finiteShellIncrement omega n m x i l)
      (fun l _ => (hint l).const_mul (e' l))]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [cubeAverage_const_mul, freshShellCubeAverage_apply]
  exact mul_comm _ _

/-! ## Link (ii): the descendant-tiling Jensen step -/

theorem descendantsAverage_vecNormSq_cubeAverageVec_le_cubeAverage
    (Q : TriadicCube d) (j : ℕ) (g : Vec d → Vec d)
    (hmem : ∀ R ∈ descendantsAtDepth Q j, MemLp g 2 (normalizedCubeMeasure R))
    (hint : IntegrableOn (fun x => vecNormSq (g x)) (cubeSet Q) volume) :
    descendantsAverage Q j (fun R => vecNormSq (cubeAverageVec R g)) ≤
      cubeAverage Q (fun x => vecNormSq (g x)) := by
  have hper : ∀ R ∈ descendantsAtDepth Q j,
      vecNormSq (cubeAverageVec R g) ≤ cubeAverage R (fun x => vecNormSq (g x)) := by
    intro R hR
    have h1 := vecNormSq_cubeAverageVec_le_sum_cubeAverage_sq_of_memLp R g (hmem R hR)
    rw [cubeAverage_vecNormSq_eq_sum_cubeAverage_sq_of_memLp R g (hmem R hR)]
    exact h1
  calc descendantsAverage Q j (fun R => vecNormSq (cubeAverageVec R g))
      ≤ descendantsAverage Q j (fun R => cubeAverage R (fun x => vecNormSq (g x))) :=
        descendantsAverage_le_descendantsAverage Q j hper
    _ = cubeAverage Q (fun x => vecNormSq (g x)) :=
        (cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j _ hint).symm

/-! ## The vanishing of an a.e.-zero field's cube average -/

theorem cubeAverageVec_eq_zero_of_ae_eq_zero_openCubeSet {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) {g : Vec d → Vec d}
    (hg : g =ᵐ[volumeMeasureOn (openCubeSet Q)] 0) :
    cubeAverageVec R g = 0 := by
  have hae : g =ᵐ[volume.restrict (cubeSet R)] 0 :=
    ae_eq_cubeSet_of_mem_descendantsAtDepth_of_ae_eq_openCubeSet hR hg
  funext i
  have hcomp : (fun x => g x i) =ᵐ[volume.restrict (cubeSet R)]
      fun _ : Vec d => (0 : ℝ) := by
    filter_upwards [hae] with x hx
    exact congrFun hx i
  show cubeAverage R (fun x => g x i) = 0
  rw [cubeAverage, integral_congr_ae hcomp]
  simp

/-! ## The per-cube collapse at the Step-4 branch -/

theorem blockVecDot_gaugedPrincipalLoadShell_blockDiag_potential
    (sigma : PositiveScalar) {Q : TriadicCube d} (R : TriadicCube d) (n m : ℤ)
    (e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet Q))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet Q))
    (omega : ShellSeq d)
    (hzeroD : cubeAverageVec R (fun x => (wD omega).toH1Function.grad x) = 0)
    (hmemN : MemVectorL2 (cubeSet R) (fun x => (wN omega).toH1Function.grad x)) :
    blockVecDot (gaugedPrincipalLoadShell sigma R n m 0 e' wD wN omega)
        (blockMatVecMul
          (Ch02.blockDiag ((sigma : ℝ) • (1 : Mat d)) (((sigma : ℝ))⁻¹ • (1 : Mat d)))
          (gaugedPrincipalLoadShell sigma R n m 0 e' wD wN omega))
      = vecNormSq e' +
        vecNormSq (cubeAverageVec R (fun x => (wN omega).toH1Function.grad x)) := by
  have hforce : MemVectorL2 (cubeSet R) (streamForcing ((sigma : ℝ))⁻¹ omega n m e') :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure R
      (memLp_normalizedCubeMeasure_of_continuous R 2
        (continuous_streamForcing ((sigma : ℝ))⁻¹ omega n m e'))
  have hsplit : cubeAverageVec R (neumannFluxField sigma omega n m e' (wN omega))
      = cubeAverageVec R (fun x => (wN omega).toH1Function.grad x)
        + ((sigma : ℝ))⁻¹ • matVecMul (freshShellCubeAverage R omega n m) e' := by
    rw [show neumannFluxField sigma omega n m e' (wN omega)
        = fun x => (wN omega).toH1Function.grad x +
            streamForcing ((sigma : ℝ))⁻¹ omega n m e' x from rfl,
      cubeAverageVec_add R _ _ hmemN hforce, cubeAverageVec_streamForcing]
  rw [blockVecDot_gaugedPrincipalLoadShell_blockDiag sigma R n m 0 e' wD wN omega]
  simp only [hzeroD, add_zero, hsplit, zero_add, add_sub_cancel_right]

/-! ## Grid arithmetic used by the assembly -/

/-- The grid average of a constant is that constant. -/
theorem descendantsAverage_const_real (Q : TriadicCube d) (j : ℕ) (c : ℝ) :
    descendantsAverage Q j (fun _ => c) = c := by
  classical
  have hcard : ((descendantsAtDepth Q j).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q j)
  show ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      (descendantsAtDepth Q j).sum (fun _ => c) = c
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp

private theorem descendantsAverage_integral_comm {Omega : Type*} [MeasurableSpace Omega]
    (Q : TriadicCube d) (j : ℕ) (mu : Measure Omega) (F : TriadicCube d → Omega → ℝ)
    (hF : ∀ R ∈ descendantsAtDepth Q j, Integrable (F R) mu) :
    descendantsAverage Q j (fun R => ∫ w, F R w ∂mu)
      = ∫ w, descendantsAverage Q j (fun R => F R w) ∂mu := by
  classical
  show ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtDepth Q j, ∫ w, F R w ∂mu = _
  rw [show (fun w => descendantsAverage Q j (fun R => F R w))
      = fun w => ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth Q j, F R w from rfl,
    integral_const_mul, integral_finsetSum _ hF]

/-! ## The endpoint -/

theorem step4GaugeEndpoint_of_correctors (M : ABKModel d) (n : ℤ) (h : ℕ)
    (K j : ℕ) {e' : Vec d} (he' : vecNormSq e' = 1)
    (wD : C(Vec d, Mat d) → H10Function (openCubeSet (originCube d (K : ℤ))))
    (wN : C(Vec d, Mat d) →
      H1MeanZeroFunction (openCubeSet (originCube d (K : ℤ))))
    (hD : ∀ omega : ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet (originCube d (K : ℤ))) (alongIncrementPath n h wD omega)
        (fun x => -streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ))
          (0 : Vec d) x))
    (hmemN : ∀ (omega : ShellSeq d) (R : TriadicCube d),
      R ∈ descendantsAtDepth (originCube d (K : ℤ)) j →
      MemLp (fun x => (alongIncrementPath n h wN omega).toH1Function.grad x) 2
        (normalizedCubeMeasure R))
    (hintN : ∀ omega : ShellSeq d, IntegrableOn
      (fun x => vecNormSq ((alongIncrementPath n h wN omega).toH1Function.grad x))
      (cubeSet (originCube d (K : ℤ))) volume)
    (hsampR : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable (fun omega : CutoffSample d => vecNormSq (cubeAverageVec R
        (fun x => (alongIncrementPath n h wN omega.val).toH1Function.grad x)))
        (cutoffSampleLaw M).toMeasure)
    (hsampK : Integrable (fun omega : CutoffSample d =>
      cubeAverage (originCube d (K : ℤ))
        (fun x => vecDot ((alongIncrementPath n h wN omega.val).toH1Function.grad x)
          ((alongIncrementPath n h wN omega.val).toH1Function.grad x)))
      (cutoffSampleLaw M).toMeasure) :
    Step4GaugeEndpoint M n h K j e' wD wN := by
  classical
  have hzeroD : ∀ (omega : ShellSeq d) {R : TriadicCube d},
      R ∈ descendantsAtDepth (originCube d (K : ℤ)) j →
      cubeAverageVec R
        (fun x => (alongIncrementPath n h wD omega).toH1Function.grad x) = 0 := by
    intro omega R hR
    exact cubeAverageVec_eq_zero_of_ae_eq_zero_openCubeSet hR
      (grad_ae_eq_zero_of_isZeroTraceDirichletRhsWeakSolution_streamForcing_zero
        (originCube d (K : ℤ)) ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ))
        (hD omega))
  have hcollapse : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      ∀ omega : CutoffSample d,
      blockVecDot
          (gaugedPrincipalLoadShell (Annealed.sigmaBar M n) R n (n + (h : ℤ)) 0 e'
            (alongIncrementPath n h wD) (alongIncrementPath n h wN) omega.val)
          (blockMatVecMul
            (Ch02.blockDiag ((Annealed.sigmaBar M n : ℝ) • (1 : Mat d))
              (((Annealed.sigmaBar M n : ℝ))⁻¹ • (1 : Mat d)))
            (gaugedPrincipalLoadShell (Annealed.sigmaBar M n) R n (n + (h : ℤ)) 0 e'
              (alongIncrementPath n h wD) (alongIncrementPath n h wN) omega.val))
        = 1 + vecNormSq (cubeAverageVec R
            (fun x => (alongIncrementPath n h wN omega.val).toH1Function.grad x)) := by
    intro R hR omega
    rw [blockVecDot_gaugedPrincipalLoadShell_blockDiag_potential
      (Annealed.sigmaBar M n) R n (n + (h : ℤ)) e' _ _ omega.val (hzeroD omega.val hR)
      (memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure R (hmemN omega.val R hR)), he']
  have hLint : Integrable (fun omega : CutoffSample d =>
      descendantsAverage (originCube d (K : ℤ)) j (fun R => vecNormSq (cubeAverageVec R
        (fun x => (alongIncrementPath n h wN omega.val).toH1Function.grad x))))
      (cutoffSampleLaw M).toMeasure :=
    (integrable_finsetSum (descendantsAtDepth (originCube d (K : ℤ)) j) hsampR).const_mul _
  show gaugeEnergyAverage M n h (K : ℤ) j 0 e'
      (alongIncrementPath n h wD) (alongIncrementPath n h wN) ≤
    1 + neumannCubeEnergy M n h K wN
  rw [gaugeEnergyAverage, neumannCubeEnergy]
  calc descendantsAverage (originCube d (K : ℤ)) j
        (fun R => ∫ omega : CutoffSample d,
          blockVecDot
            (gaugedPrincipalLoadShell (Annealed.sigmaBar M n) R n (n + (h : ℤ)) 0 e'
              (alongIncrementPath n h wD) (alongIncrementPath n h wN) omega.val)
            (blockMatVecMul
              (Ch02.blockDiag ((Annealed.sigmaBar M n : ℝ) • (1 : Mat d))
                (((Annealed.sigmaBar M n : ℝ))⁻¹ • (1 : Mat d)))
              (gaugedPrincipalLoadShell (Annealed.sigmaBar M n) R n (n + (h : ℤ)) 0 e'
                (alongIncrementPath n h wD) (alongIncrementPath n h wN) omega.val))
          ∂(cutoffSampleLaw M).toMeasure)
      ≤ descendantsAverage (originCube d (K : ℤ)) j
        (fun R => (1 : ℝ) + ∫ omega : CutoffSample d,
          vecNormSq (cubeAverageVec R
            (fun x => (alongIncrementPath n h wN omega.val).toH1Function.grad x))
          ∂(cutoffSampleLaw M).toMeasure) := by
        refine descendantsAverage_le_descendantsAverage _ _ fun R hR => ?_
        refine le_of_eq ?_
        rw [integral_congr_ae (Filter.Eventually.of_forall (hcollapse R hR)),
          integral_add (integrable_const 1) (hsampR R hR), integral_const]
        simp
    _ = 1 + descendantsAverage (originCube d (K : ℤ)) j
          (fun R => ∫ omega : CutoffSample d,
            vecNormSq (cubeAverageVec R
              (fun x => (alongIncrementPath n h wN omega.val).toH1Function.grad x))
            ∂(cutoffSampleLaw M).toMeasure) := by
        rw [descendantsAverage_add_real, descendantsAverage_const_real]
    _ = 1 + ∫ omega : CutoffSample d,
          descendantsAverage (originCube d (K : ℤ)) j
            (fun R => vecNormSq (cubeAverageVec R
              (fun x => (alongIncrementPath n h wN omega.val).toH1Function.grad x)))
          ∂(cutoffSampleLaw M).toMeasure := by
        rw [descendantsAverage_integral_comm _ _ _ _ hsampR]
    _ ≤ 1 + ∫ omega : CutoffSample d,
          cubeAverage (originCube d (K : ℤ))
            (fun x => vecDot ((alongIncrementPath n h wN omega.val).toH1Function.grad x)
              ((alongIncrementPath n h wN omega.val).toH1Function.grad x))
          ∂(cutoffSampleLaw M).toMeasure := by
        have hmono := integral_mono hLint hsampK fun omega =>
          descendantsAverage_vecNormSq_cubeAverageVec_le_cubeAverage
            (originCube d (K : ℤ)) j _ (fun R hR => hmemN omega.val R hR)
            (hintN omega.val)
        linarith [hmono]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
