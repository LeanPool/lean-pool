/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.Step5Input
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationBackgroundClass

/-!
# Step5SampDefMeasurable

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Sample measurability of the Step-5 per-cube cross defect

ABK26, `l.approximate.recurrence.formula`, Step 5, `e.nablaw.oscillations`.

## The obligation this module discharges

`Closure.Step5InputSideConditions` records that the one remaining binder of
`Closure.Step5Input.closureStep5Input_of_sampDef` --- the sample integrability of
`Closure.JunctionDischargeStepFiveDisplay.step5CrossDefect` at the closure's
Dirichlet family --- is missing exactly one ingredient: the sample measurability
of the cube average of a **product**,

```
  omega |->  fint_R  e . ( (k_m - k_n)(x) grad w_D(omega)(x) ) dx .
```

The two factors are separately measurable, but the corrector gradient enters
every proved statement only through its `L^2` class, never through a jointly
measurable representative, so the product's cube average is not a composition
of proved maps.  This module supplies it.

## Method: the pairing is a Caratheodory function of the class

The cube average above is a **bilinear pairing**.  Written against the
transposed direction `(k_m - k_n)^t e` and localized to the cube by an
indicator, it is the `L^2(cu_K)` inner product

```
  fint_R e . (h(x) v(x)) dx  =  (cubeVolume R)^{-1} < W(omega) , [v] > ,
  W(omega) := 1_{cu_R} (h(omega, .)^t e) ,
```

so that, at fixed sample, it is a *continuous* function of the `L^2` class
`[v]` (it is a fixed continuous linear functional), while at fixed class it is
a *measurable* function of the sample (the weight is jointly `(omega, x)`
measurable --- the shell field's evaluation map is jointly continuous --- so
`MeasureTheory.StronglyMeasurable.integral_prod_right'` applies).
`MeasureTheory.measurable_uncurry_of_continuous_of_measurable` (Caratheodory)
then makes the two-variable pairing jointly measurable, and composing with the
proved measurable gradient class
`Corrector.measurable_freshShellDirichletGradL2` finishes.

This is the same route the joint-measurability lane uses for the doubled energy
value in `ApproximateRecurrence.LocalizationFluctuationJointField`; only the
functional changes (a linear pairing here, a quadratic form there).

**No measurable selection occurs.**  The corrector family is an arbitrary family
of weak solutions of `e.def.w`, exactly as in
`Corrector.CorrectorMeasurableGradient`, and only its gradient class is read.
Because the pairing depends on the gradient only through its class, its value at
the class is *equal* --- not merely almost surely equal --- to the cube average
of the honest representative.

## Main results

* `measurable_uncurry_finiteShellIncrement_entry` --- joint `(omega, x)`
  measurability of the entries of `k_m - k_n`.
* `step5CrossPairing`, `continuous_step5CrossPairing`,
  `step5CrossPairing_apply_class` --- the localized pairing, its continuity in
  the class, and its value at the class of any `L^2` field.
* `measurable_step5CrossPairing_apply` --- measurability in the sample at a
  fixed class.
* `measurable_cubeAverage_vecDot_matVecMul_freshShellDirichletGrad` --- the
  missing ingredient itself.
* `measurable_step5CrossDefect_freshShellDirichletGrad` and its cutoff-sample
  corollary --- sample measurability of the whole per-cube cross defect.

## Binders

Beyond the typing binders: `[NeZero d]` (for the proved gradient-class
measurability) and the zero-trace weak-solution property of `e.def.w` for the
corrector family.  No integrability, no estimate, no smallness and no
measurability of the corrector family itself is assumed.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula`, Step 5; `e.nablaw.oscillations`;
  `e.def.w`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Joint `(omega, x)` measurability of the finite shell increment -/

/-- The evaluation map of the frozen shell carrier is jointly continuous: the
carrier is a subtype of a compact-open triple whose first component is a bundled
continuous map. -/
theorem continuous_uncurry_shellField_entry (i j : Fin d) :
    Continuous fun q : Algsuperdiff.Frozen.Assumptions.ShellField d × Vec d => q.1 q.2 i j := by
  have hvalue : Continuous
      (fun q : Algsuperdiff.Frozen.Assumptions.ShellField d × Vec d => q.1 q.2) :=
    ContinuousEval.continuous_eval.comp
      (((continuous_subtype_val.comp continuous_fst).fst).prodMk continuous_snd)
  exact (continuous_apply j).comp ((continuous_apply i).comp hvalue)

/-- One shell coordinate of a sequence, jointly measurable in `(omega, x)`. -/
theorem measurable_uncurry_shellSeq_entry (k : ℤ) (i j : Fin d) :
    Measurable fun p : ShellSeq d × Vec d => p.1 k p.2 i j := by
  have hpair : Measurable fun p : ShellSeq d × Vec d =>
      ((p.1 k : Algsuperdiff.Frozen.Assumptions.ShellField d), p.2) :=
    ((measurable_pi_apply k).comp measurable_fst).prodMk measurable_snd
  exact (continuous_uncurry_shellField_entry i j).measurable.comp hpair

/-- **Joint `(omega, x)` measurability of the entries of `k_m - k_n`.**  The
increment is the finite sum of the shells with indices in `(n, m]`. -/
theorem measurable_uncurry_finiteShellIncrement_entry (n m : ℤ) (i j : Fin d) :
    Measurable fun p : ShellSeq d × Vec d => finiteShellIncrement p.1 n m p.2 i j := by
  have hrw : (fun p : ShellSeq d × Vec d => finiteShellIncrement p.1 n m p.2 i j)
      = fun p : ShellSeq d × Vec d => ∑ k ∈ Finset.Ioc n m, p.1 k p.2 i j := by
    funext p
    exact finiteShellIncrement_apply_entry p.1 n m p.2 i j
  rw [hrw]
  exact Finset.measurable_sum _ fun k _ => measurable_uncurry_shellSeq_entry k i j

/-! ## The transposed direction -/

/-- The direction `e` pushed through the transpose of a matrix. -/
def step5CrossWeightVec (e : Vec d) (A : Mat d) : Vec d := fun j => ∑ i, e i * A i j

/-- Testing a matrix-vector product against `e` is testing the vector against
the transposed direction. -/
theorem vecDot_step5CrossWeightVec (e : Vec d) (A : Mat d) (v : Vec d) :
    vecDot (step5CrossWeightVec e A) v = vecDot e (matVecMul A v) := by
  classical
  show (∑ j, (∑ i, e i * A i j) * v j) = ∑ i, e i * ∑ j, A i j * v j
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem continuous_step5CrossWeightVec_finiteShellIncrement (e : Vec d) (n m : ℤ)
    (omega : ShellSeq d) :
    Continuous fun x : Vec d => step5CrossWeightVec e (finiteShellIncrement omega n m x) :=
  continuous_pi fun j => continuous_finsetSum _ fun i _ =>
    continuous_const.mul (continuous_finiteShellIncrement_entry omega n m i j)

/-! ## The localized weight field -/

/-- The Step-5 weight: the transposed direction against the fresh shell,
localized to the cube `R`. -/
def step5CrossWeightField (R : TriadicCube d) (e : Vec d) (n m : ℤ) (omega : ShellSeq d) :
    Vec d → Vec d :=
  Set.indicator (cubeSet R)
    (fun x => step5CrossWeightVec e (finiteShellIncrement omega n m x))

theorem measurable_step5CrossWeightField (R : TriadicCube d) (e : Vec d) (n m : ℤ)
    (omega : ShellSeq d) : Measurable (step5CrossWeightField R e n m omega) :=
  Measurable.indicator
    (continuous_step5CrossWeightVec_finiteShellIncrement e n m omega).measurable
    (measurableSet_cubeSet R)

/-- The weight is bounded --- the fresh shell is continuous, hence bounded on the
closed cube --- so it is `L^2` on any localization cube. -/
theorem memVectorL2_step5CrossWeightField (Q R : TriadicCube d) (e : Vec d) (n m : ℤ)
    (omega : ShellSeq d) :
    MemVectorL2 (openCubeSet Q) (step5CrossWeightField R e n m omega) := by
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (cubeCenter R) (cubeRadius R)).exists_bound_of_continuousOn
      (continuous_step5CrossWeightVec_finiteShellIncrement e n m omega).continuousOn
  refine MemLp.of_bound
    (measurable_step5CrossWeightField R e n m omega).aestronglyMeasurable (max C 0) ?_
  filter_upwards with x
  by_cases hx : x ∈ cubeSet R
  · rw [step5CrossWeightField, Set.indicator_of_mem hx]
    exact le_trans (hC x (cubeSet_subset_closedBall R hx)) (le_max_left _ _)
  · rw [step5CrossWeightField, Set.indicator_of_notMem hx, norm_zero]
    exact le_max_right _ _

/-! ## The pairing -/

/-- Restricting the localization cube's measure to a descendant is the
descendant's own restricted measure: the two differ only inside a null
boundary. -/
theorem restrict_openCubeSet_restrict_cubeSet_descendant {Q R : TriadicCube d} {jd : ℕ}
    (hR : R ∈ descendantsAtDepth Q jd) :
    (volume.restrict (openCubeSet Q)).restrict (cubeSet R) = volume.restrict (cubeSet R) := by
  rw [Measure.restrict_restrict (measurableSet_cubeSet R)]
  refine Measure.restrict_congr_set ?_
  rw [Filter.eventuallyEqSet_iff]
  filter_upwards [Filter.eventuallyEqSet_iff.1 (cubeSet_ae_eq_openCubeSet R)] with x hx
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, openCubeSet_subset_of_mem_descendantsAtDepth hR (hx.1 h)⟩

/-- **The Step-5 cross pairing**: the normalized `L^2(cu_K)` pairing of the
localized weight with a class. -/
def step5CrossPairing (Q R : TriadicCube d) (e : Vec d) (n m : ℤ) (omega : ShellSeq d)
    (xi : HilbertVectorL2 (openCubeSet Q)) : ℝ :=
  (cubeVolume R)⁻¹ *
    (InnerProductSpace.toDual ℝ (HilbertVectorL2 (openCubeSet Q))
      (toHilbertVectorL2OfVecField (memVectorL2_step5CrossWeightField Q R e n m omega))) xi

/-- At a fixed sample the pairing is a continuous function of the class: it is a
fixed continuous linear functional. -/
theorem continuous_step5CrossPairing (Q R : TriadicCube d) (e : Vec d) (n m : ℤ)
    (omega : ShellSeq d) : Continuous (step5CrossPairing Q R e n m omega) :=
  continuous_const.mul (ContinuousLinearMap.continuous _)

/-- **The pairing computes the cube average of the product.**  No integrability
of the product is assumed: both sides are Bochner integrals of almost
everywhere equal integrands against the same measure. -/
theorem step5CrossPairing_apply_class {Q R : TriadicCube d} {jd : ℕ}
    (hR : R ∈ descendantsAtDepth Q jd) (e : Vec d) (n m : ℤ) (omega : ShellSeq d)
    {u : Vec d → Vec d} (hu : MemVectorL2 (openCubeSet Q) u) :
    step5CrossPairing Q R e n m omega (toHilbertVectorL2OfVecField hu) =
      cubeAverage R
        (fun x => vecDot e (matVecMul (finiteShellIncrement omega n m x) (u x))) := by
  classical
  rw [step5CrossPairing, InnerProductSpace.toDual_apply_apply, L2.inner_def, cubeAverage]
  congr 1
  have hW := coeFn_toHilbertVectorL2OfVecField
    (memVectorL2_step5CrossWeightField Q R e n m omega)
  have hU := coeFn_toHilbertVectorL2OfVecField hu
  have hstep : (∫ x, inner ℝ
        ((toHilbertVectorL2OfVecField (memVectorL2_step5CrossWeightField Q R e n m omega) :
          Vec d → HilbertVec d) x)
        ((toHilbertVectorL2OfVecField hu : Vec d → HilbertVec d) x)
        ∂(volumeMeasureOn (openCubeSet Q)))
      = ∫ x, Set.indicator (cubeSet R)
          (fun y => vecDot e (matVecMul (finiteShellIncrement omega n m y) (u y))) x
          ∂(volumeMeasureOn (openCubeSet Q)) := by
    refine integral_congr_ae ?_
    filter_upwards [hW, hU] with x h1 h2
    rw [h1, h2, HilbertVec.inner_def]
    by_cases hx : x ∈ cubeSet R
    · rw [Set.indicator_of_mem hx]
      show vecDot (step5CrossWeightField R e n m omega x) (u x) = _
      rw [step5CrossWeightField, Set.indicator_of_mem hx, vecDot_step5CrossWeightVec]
    · rw [Set.indicator_of_notMem hx]
      show vecDot (step5CrossWeightField R e n m omega x) (u x) = 0
      rw [step5CrossWeightField, Set.indicator_of_notMem hx]
      simp [vecDot]
  rw [hstep, integral_indicator (measurableSet_cubeSet R)]
  show ∫ x, vecDot e (matVecMul (finiteShellIncrement omega n m x) (u x))
      ∂((volume.restrict (openCubeSet Q)).restrict (cubeSet R)) = _
  rw [restrict_openCubeSet_restrict_cubeSet_descendant hR]

/-- At a fixed class the pairing is a measurable function of the sample: the
integrand is jointly `(omega, x)` measurable. -/
theorem measurable_step5CrossPairing_apply (Q R : TriadicCube d) (e : Vec d) (n m : ℤ)
    (xi : HilbertVectorL2 (openCubeSet Q)) :
    Measurable fun omega : ShellSeq d => step5CrossPairing Q R e n m omega xi := by
  classical
  simp only [step5CrossPairing]
  refine Measurable.const_mul ?_ _
  have hrw : (fun omega : ShellSeq d =>
      (InnerProductSpace.toDual ℝ (HilbertVectorL2 (openCubeSet Q))
        (toHilbertVectorL2OfVecField (memVectorL2_step5CrossWeightField Q R e n m omega))) xi)
      = fun omega : ShellSeq d =>
        ∫ x, vecDot (step5CrossWeightField R e n m omega x)
          ((xi : Vec d → HilbertVec d) x).toVec ∂(volumeMeasureOn (openCubeSet Q)) := by
    funext omega
    rw [InnerProductSpace.toDual_apply_apply, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_toHilbertVectorL2OfVecField
      (memVectorL2_step5CrossWeightField Q R e n m omega)] with x hx
    rw [hx, HilbertVec.inner_def]
    rfl
  rw [hrw]
  have hxi : Measurable fun p : ShellSeq d × Vec d =>
      ((xi : Vec d → HilbertVec d) p.2).toVec :=
    (((HilbertVec.continuousLinearEquivVec d).continuous.measurable.comp
      (Lp.stronglyMeasurable xi).measurable)).comp measurable_snd
  have hw : ∀ j : Fin d, Measurable fun p : ShellSeq d × Vec d =>
      step5CrossWeightField R e n m p.1 p.2 j := by
    intro j
    have hset : MeasurableSet {p : ShellSeq d × Vec d | p.2 ∈ cubeSet R} :=
      measurable_snd (measurableSet_cubeSet R)
    have hval : Measurable fun p : ShellSeq d × Vec d =>
        ∑ i, e i * finiteShellIncrement p.1 n m p.2 i j :=
      Finset.measurable_sum _ fun i _ =>
        (measurable_uncurry_finiteShellIncrement_entry n m i j).const_mul (e i)
    have hrw2 : (fun p : ShellSeq d × Vec d => step5CrossWeightField R e n m p.1 p.2 j)
        = fun p : ShellSeq d × Vec d =>
          if p.2 ∈ cubeSet R then (∑ i, e i * finiteShellIncrement p.1 n m p.2 i j)
            else 0 := by
      funext p
      by_cases hx : p.2 ∈ cubeSet R
      · rw [step5CrossWeightField, Set.indicator_of_mem hx, ite_eq_left hx]
        rfl
      · rw [step5CrossWeightField, Set.indicator_of_notMem hx, ite_eq_right hx]
        rfl
    rw [hrw2]
    exact Measurable.ite hset hval measurable_const
  have hexpand : (fun p : ShellSeq d × Vec d =>
      vecDot (step5CrossWeightField R e n m p.1 p.2)
        ((xi : Vec d → HilbertVec d) p.2).toVec)
      = fun p : ShellSeq d × Vec d => ∑ j, step5CrossWeightField R e n m p.1 p.2 j *
          ((xi : Vec d → HilbertVec d) p.2).toVec j := rfl
  have hjoint : Measurable fun p : ShellSeq d × Vec d =>
      vecDot (step5CrossWeightField R e n m p.1 p.2)
        ((xi : Vec d → HilbertVec d) p.2).toVec := by
    rw [hexpand]
    exact Finset.measurable_sum _ fun j _ =>
      (hw j).mul ((measurable_pi_apply j).comp hxi)
  exact (hjoint.stronglyMeasurable.integral_prod_right').measurable

/-! ## The Caratheodory composition -/

/-- **The missing ingredient of `hsampDef`, proved.**

The cube average of the product of the fresh shell and the Dirichlet corrector's
gradient, tested against a fixed direction, is a measurable function of the
sample.

only on the zero-trace weak-solution property of `e.def.w`: the corrector
family is otherwise arbitrary, and no measurable selection occurs. -/
theorem measurable_cubeAverage_vecDot_matVecMul_freshShellDirichletGrad [NeZero d]
    {Q R : TriadicCube d} {jd : ℕ} (hR : R ∈ descendantsAtDepth Q jd) (e : Vec d) (n m : ℤ)
    (sigmaInv : ℝ) (nsh msh : ℤ) (eD : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet Q))
    (hwD : ∀ omega : ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) (wD omega)
        (fun x => -streamForcing sigmaInv omega nsh msh eD x)) :
    Measurable fun omega : ShellSeq d =>
      cubeAverage R (fun x => vecDot e (matVecMul (finiteShellIncrement omega n m x)
        ((wD omega).toH1Function.grad x))) := by
  let : Fact ((1 : ENNReal) ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have : SecondCountableTopology (HilbertVectorL2 (openCubeSet Q)) := inferInstance
  have hjoint : Measurable (Function.uncurry
      (fun (xi : HilbertVectorL2 (openCubeSet Q)) (omega : ShellSeq d) =>
        step5CrossPairing Q R e n m omega xi)) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun omega => continuous_step5CrossPairing Q R e n m omega)
      (fun xi => measurable_step5CrossPairing_apply Q R e n m xi)
  have hclass : Measurable fun omega : ShellSeq d =>
      (wD omega).toH1Function.gradToHilbertVectorL2 :=
    measurable_freshShellDirichletGradL2 Q sigmaInv nsh msh eD wD hwD
  have hpair : Measurable fun omega : ShellSeq d =>
      ((wD omega).toH1Function.gradToHilbertVectorL2, omega) :=
    hclass.prodMk measurable_id
  have hcomp := hjoint.comp hpair
  simp only [Function.comp_def, Function.uncurry_apply_pair] at hcomp
  have hval : (fun omega : ShellSeq d =>
      cubeAverage R (fun x => vecDot e (matVecMul (finiteShellIncrement omega n m x)
        ((wD omega).toH1Function.grad x))))
      = fun omega : ShellSeq d =>
        step5CrossPairing Q R e n m omega
          ((wD omega).toH1Function.gradToHilbertVectorL2) := by
    funext omega
    rw [← toHilbertVectorL2OfVecField_grad (wD omega).toH1Function
      (H1Function.grad_memVectorL2 _)]
    exact (step5CrossPairing_apply_class hR e n m omega _).symm
  rw [hval]
  exact hcomp

/-! ## The defect itself -/

/-- **Sample measurability of the Step-5 per-cube cross defect.**  The cube average
of the product is the previous statement; the product of the two averages is
the proved pair of measurable factors. -/
theorem measurable_step5CrossDefect_freshShellDirichletGrad [NeZero d]
    {Q R : TriadicCube d} {jd : ℕ} (hR : R ∈ descendantsAtDepth Q jd) (e : Vec d) (n m : ℤ)
    (sigmaInv : ℝ) (nsh msh : ℤ) (eD : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet Q))
    (hwD : ∀ omega : ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) (wD omega)
        (fun x => -streamForcing sigmaInv omega nsh msh eD x)) :
    Measurable fun omega : ShellSeq d =>
      step5CrossDefect R omega n m e (fun x => (wD omega).toH1Function.grad x) := by
  have h1 := measurable_cubeAverage_vecDot_matVecMul_freshShellDirichletGrad hR e n m
    sigmaInv nsh msh eD wD hwD
  have h2 : Measurable fun omega : ShellSeq d =>
      vecDot e (matVecMul (freshShellCubeAverage R omega n m)
        (cubeAverageVec R (fun x => (wD omega).toH1Function.grad x))) :=
    measurable_vecDot_const e (measurable_matVecMul_of_measurable
      (measurable_freshShellCubeAverage hR n m)
      (measurable_cubeAverageVec_freshShellDirichletGrad hR sigmaInv nsh msh eD wD hwD))
  have hrw : (fun omega : ShellSeq d =>
      step5CrossDefect R omega n m e (fun x => (wD omega).toH1Function.grad x))
      = fun omega : ShellSeq d =>
        cubeAverage R (fun x => vecDot e (matVecMul (finiteShellIncrement omega n m x)
          ((wD omega).toH1Function.grad x))) -
          vecDot e (matVecMul (freshShellCubeAverage R omega n m)
            (cubeAverageVec R (fun x => (wD omega).toH1Function.grad x))) := rfl
  rw [hrw]
  exact h1.sub h2

/-- The cutoff-sample carrier form of the previous statement. -/
theorem measurable_cutoffSample_step5CrossDefect_freshShellDirichletGrad [NeZero d]
    {Q R : TriadicCube d} {jd : ℕ} (hR : R ∈ descendantsAtDepth Q jd) (e : Vec d) (n m : ℤ)
    (sigmaInv : ℝ) (nsh msh : ℤ) (eD : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet Q))
    (hwD : ∀ omega : ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) (wD omega)
        (fun x => -streamForcing sigmaInv omega nsh msh eD x)) :
    Measurable fun omega : CutoffSample d =>
      step5CrossDefect R omega.val n m e (fun x => (wD omega.val).toH1Function.grad x) :=
  (measurable_step5CrossDefect_freshShellDirichletGrad hR e n m sigmaInv nsh msh eD
    wD hwD).comp measurable_subtype_coe

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
