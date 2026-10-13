/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenInteriorMinkowski
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.SplitFoldCellMoments
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationNumericOctic
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationSelectionFamily

/-!
# GammaTenFluxMeasurability

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Sample-measurability and fourth-power integrability of the **flux leg's**
oscillation cell

ABK26, `e.nablaw.oscillations`, `e.Fz.def`, `e.def.w`.

## The gap this module fills

The interior Besov envelope
`exists_besovEnvelope_interiorMesoCubeGrid_of_depth_gridRoot_const`
carries the two cellwise typing binders

```
  hmeascell : Measurable fun w => meshOscillationCell nn (U w) R' ,
  hintcell  : Integrable (fun w => meshOscillationCell nn (U w) R' ^ 4) mu ,
```

and the proved producers of both --- `Closure.Step5InputOscillation` and the
octic layer of `LocalizationFluctuationNumericOctic` --- are stated only for
the corrector **gradient** families.  The Neumann leg of the gauged `bfF_z` is
read at `PrincipalResponsePz.neumannFluxField = grad w_N + streamForcing`, for
which no producer exists.  This module supplies both, without any new analytic
input.

## How

**Measurability.**  The gradient-specific measurability core of
`LocalizationFluctuationNumericOctic` (its private
`measurable_meanSquareOscillationVecOn_of_measurable`) never uses the gradient
structure of the family beyond one fact: that the sample-indexed field has a
*measurable ambient `L^2` class*.  The centring identity
`LocalizationFluctuationNumericOctic.meanSquareOscillationVecOn_eq_sub_vecNormSq_volumeAverageVec`
writes the mean-square oscillation as the window average of the squared gauge
minus the sum of the squared coordinate window averages, and both terms are
continuous window observables of that class:

* the first through the proved general
  `Closure.SplitFoldCellMoments.measurable_volumeAverage_vecNormSq_of_measurable_class`;
* the second through the proved general
  `Corrector.measurable_setIntegral_gradCoordL2`, whose family argument is an
  arbitrary measurable `HilbertVectorL2` family, together with the a.e.
  characterization `coeFn_toHilbertVectorL2OfVecField` of the class of a plain
  vector field.

So the core generalizes verbatim, and the flux family's class is measurable by
the proved
`LocalizationFluctuationBackgroundClass.measurable_toHilbertVectorL2OfVecField_neumannFluxField`.

**Integrability.**  The cellwise Minkowski split
`Closure.GammaTenInteriorMinkowski.meshOscillationCell_neumannFluxField_le`
dominates the flux cell by the gradient cell plus the deterministic forcing
gauge `3^{nn} sigma^{-1} d |e'| shellDerivNormSum`; `(a+b)^4 <= 8(a^4+b^4)` and
the proved fourth-power integrability of the forcing gauge
(`LocalizationOscillationDisplay.integrable_shellDerivNormSum_rpow_four`)
reduce the flux cell's fourth power to the gradient cell's, which the caller
supplies.

## What is proved

* `setIntegral_coordL2_eq` (private) --- the coordinate window integral of the
  ambient `L^2` class of a vector field is the Lebesgue integral of that
  coordinate.
* `measurable_meanSquareOscillationVecOn_of_measurable_class` --- the measurability
  core, for an arbitrary measurable family of ambient `L^2` classes.
* `measurable_meshOscillationCell_of_measurable_class` --- the same at the cell of
  `e.nablaw.oscillations`, read at the cell's own scale.
* `measurable_meshOscillationCell_neumannFluxField` and
  `..._neumannFluxField_cutoffSample` --- the flux leg's cell, on the shell law
  and on the closure's cutoff-sample carrier.
* `integrable_meshOscillationCell_pow_four_neumannFluxField_cutoffSample` --- the
  flux leg's `hintcell`, from the gradient leg's.

## Binders

The window data (`hS`, `hSU`, `hfin`, `hpos`) and the coordinate integrabilities
in the general core; the cell data (`hsc`, `hsub`) at the cell; the Neumann
weak-solution property `hsol` and the `L^2` memberships at the flux instances;
and for the integrability the scale gate `hnn <= lowScale`, `lowScale <
highScale`, and the gradient leg's own fourth-power integrability.  No smallness
gate on `cgamma`, no model estimate and no stationarity is assumed.

## Scope

Internal Provider infrastructure for the Step-2 fluctuation estimate.  There is
no `sorry`, no `admit`, no custom axiom and no `set_option maxHeartbeats`.

## Proof-text provenance

`setIntegral_coordL2_eq` and
`measurable_meanSquareOscillationVecOn_of_measurable_class` are adaptations of
the proof text of the private
`LocalizationFluctuationNumericOctic.setIntegral_gradCoord_eq` and
`LocalizationFluctuationNumericOctic.measurable_meanSquareOscillationVecOn_of_measurable`
(same repository), with the gradient identification `F omega = (w
omega).gradToHilbertVectorL2` replaced by the definitional class
`toHilbertVectorL2OfVecField` of a plain vector field and its a.e.
characterization, and with the quadratic window observable taken from the
proved general
`Closure.SplitFoldCellMoments.measurable_volumeAverage_vecNormSq_of_measurable_class`
rather than assumed.  Neither private declaration is consumed.

## References

* ABK26, `e.nablaw.oscillations`, `e.Fz.def`, `e.def.w`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 HCPolySupport.Book.Ch03
open MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The coordinate window integral of an ambient `L^2` class -/

/-- The coordinate window integral of the ambient `L^2` class of a vector field is
the ordinary Lebesgue integral of that coordinate over the window.

on the window data `hS`, `hSU`. -/
private theorem setIntegral_coordL2_eq {Q : TriadicCube d} {u : Vec d → Vec d}
    (hu : MemVectorL2 (openCubeSet Q) u) {S : Set (Vec d)} (hS : MeasurableSet S)
    (hSU : S ⊆ openCubeSet Q) (i : Fin d) :
    ∫ x in S, ((toHilbertVectorL2OfVecField hu :
        HilbertVectorL2 (openCubeSet Q)) : Vec d → HilbertVec d) x i
        ∂(volumeMeasureOn (openCubeSet Q)) =
      ∫ x in S, u x i ∂volume := by
  have hrestrict : (volumeMeasureOn (openCubeSet Q)).restrict S = volume.restrict S := by
    rw [volumeMeasureOn, Measure.restrict_restrict hS,
      Set.inter_eq_self_of_subset_left hSU]
  have hae : ∀ᵐ x ∂((volumeMeasureOn (openCubeSet Q)).restrict S),
      ((toHilbertVectorL2OfVecField hu :
        HilbertVectorL2 (openCubeSet Q)) : Vec d → HilbertVec d) x i = u x i := by
    refine ((coeFn_toHilbertVectorL2OfVecField hu).filter_mono
      (ae_mono Measure.restrict_le_self)).mono fun x hx => ?_
    rw [hx]
    simp [hilbertifyVecField]
  rw [integral_congr_ae hae, hrestrict]

/-! ## The measurability core, for an arbitrary measurable family of classes -/

/-- **The measurability core.**  For a family of vector fields on the cube whose
ambient `L^2` classes are measurable in the sample, the mean-square oscillation
over a measurable window is measurable in the sample.

No structure of the fields beyond the measurability of their classes is used; in
particular they need not be gradients.

: the window data `hS`, `hSU`, `hfin`, `hpos`; the `L^2` memberships `hu`; the
class measurability `hclass`; and the coordinate integrabilities on the window. -/
theorem measurable_meanSquareOscillationVecOn_of_measurable_class {Omega : Type*}
    [MeasurableSpace Omega] (Q : TriadicCube d) {S : Set (Vec d)}
    (hS : MeasurableSet S) (hSU : S ⊆ openCubeSet Q)
    (hfin : volume S ≠ ⊤) (hpos : 0 < (volume S).toReal)
    {u : Omega → Vec d → Vec d}
    (hu : ∀ omega, MemVectorL2 (openCubeSet Q) (u omega))
    (hclass : Measurable fun omega => toHilbertVectorL2OfVecField (hu omega))
    (hcoord : ∀ (omega : Omega) (k : Fin d),
      IntegrableOn (fun x => u omega x k) S volume)
    (hcoordsq : ∀ (omega : Omega) (k : Fin d),
      IntegrableOn (fun x => (u omega x k) ^ 2) S volume) :
    Measurable fun omega => Book.Ch01.meanSquareOscillationVecOn S (u omega) := by
  classical
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hcoordMeas : ∀ k : Fin d, Measurable fun omega =>
      volumeAverage S (fun x => u omega x k) := by
    intro k
    have hEq : (fun omega => volumeAverage S (fun x => u omega x k)) =
        fun omega => (volume S).toReal⁻¹ *
          ∫ x in S, ((toHilbertVectorL2OfVecField (hu omega) :
              HilbertVectorL2 (openCubeSet Q)) : Vec d → HilbertVec d) x k
            ∂(volumeMeasureOn (openCubeSet Q)) := by
      funext omega
      rw [setIntegral_coordL2_eq (hu omega) hS hSU k, volumeAverage]
    rw [hEq]
    exact measurable_const.mul (measurable_setIntegral_gradCoordL2 Q hS k hclass)
  have hsqMeas : Measurable fun omega =>
      volumeAverage S (fun x => vecNormSq (u omega x)) :=
    measurable_volumeAverage_vecNormSq_of_measurable_class hS hSU hu hclass
  have hEq : (fun omega => Book.Ch01.meanSquareOscillationVecOn S (u omega)) =
      fun omega => volumeAverage S (fun x => vecNormSq (u omega x)) -
        ∑ k : Fin d, (volumeAverage S (fun x => u omega x k)) ^ 2 := by
    funext omega
    have hnorm : vecNormSq (volumeAverageVec S (u omega)) =
        ∑ k : Fin d, (volumeAverage S (fun x => u omega x k)) ^ 2 := by
      unfold vecNormSq vecDot
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_two]
      rfl
    rw [meanSquareOscillationVecOn_eq_sub_vecNormSq_volumeAverageVec hfin hpos
      (u omega) (hcoord omega) (hcoordsq omega), hnorm]
  rw [hEq]
  exact hsqMeas.sub (Finset.measurable_sum Finset.univ
    fun k _ => (hcoordMeas k).pow_const 2)

/-- **The oscillation cell of `e.nablaw.oscillations` is measurable in the sample
for any family of fields with measurable ambient `L^2` classes.**

: the cell data `hsc`, `hsub`; the `L^2` memberships `hu`; the class
measurability `hclass`; and the two coordinate integrability families on the
cell. -/
theorem measurable_meshOscillationCell_of_measurable_class {Omega : Type*}
    [MeasurableSpace Omega] (Q : TriadicCube d) {n : ℤ} (R : TriadicCube d)
    (hsc : R.scale = n) (hsub : openCubeSet R ⊆ openCubeSet Q)
    {u : Omega → Vec d → Vec d}
    (hu : ∀ omega, MemVectorL2 (openCubeSet Q) (u omega))
    (hclass : Measurable fun omega => toHilbertVectorL2OfVecField (hu omega))
    (hcoord : ∀ (omega : Omega) (k : Fin d),
      IntegrableOn (fun x => u omega x k) (openCubeSet R) volume)
    (hcoordsq : ∀ (omega : Omega) (k : Fin d),
      IntegrableOn (fun x => (u omega x k) ^ 2) (openCubeSet R) volume) :
    Measurable fun omega => meshOscillationCell n (u omega) R := by
  have hwin : openCubeAtScale (triadicCubeShift R) n = openCubeSet R := by
    rw [← hsc]
    exact openCubeAtScale_triadicCubeShift_eq_openCubeSet R
  have hcore := measurable_meanSquareOscillationVecOn_of_measurable_class Q
    (measurableSet_openCubeSet R) hsub (volume_openCubeSet_ne_top' R)
    (volume_openCubeSet_toReal_pos' R) hu hclass hcoord hcoordsq
  have hEq : (fun omega => meshOscillationCell n (u omega) R) =
      fun omega =>
        Real.sqrt (Book.Ch01.meanSquareOscillationVecOn (openCubeSet R) (u omega)) := by
    funext omega
    rw [meshOscillationCell, hwin]
  rw [hEq]
  exact Real.continuous_sqrt.measurable.comp hcore

/-! ## The flux leg -/

/-- **The flux leg's oscillation cell is measurable on the shell law.**

: the cell data `hsc`, `hsub`, the Neumann weak-solution property `hsol`, and
the two coordinate integrability families on the cell. -/
theorem measurable_meshOscillationCell_neumannFluxField (Q : TriadicCube d)
    (sigma : PositiveScalar) (sigmaInv : ℝ) (lowScale highScale : ℤ) (eN e' : Vec d)
    {n : ℤ} (R : TriadicCube d) (hsc : R.scale = n)
    (hsub : openCubeSet R ⊆ openCubeSet Q)
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet Q))
    (hsol : ∀ omega : ShellSeq d,
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) (wN omega)
        (fun x => -streamForcing sigmaInv omega lowScale highScale eN x))
    (hcoord : ∀ (omega : ShellSeq d) (k : Fin d),
      IntegrableOn (fun x =>
        neumannFluxField sigma omega lowScale highScale e' (wN omega) x k)
        (openCubeSet R) volume)
    (hcoordsq : ∀ (omega : ShellSeq d) (k : Fin d),
      IntegrableOn (fun x =>
        (neumannFluxField sigma omega lowScale highScale e' (wN omega) x k) ^ 2)
        (openCubeSet R) volume) :
    Measurable fun omega : ShellSeq d =>
      meshOscillationCell n
        (neumannFluxField sigma omega lowScale highScale e' (wN omega)) R := by
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hmem : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet Q)
      (neumannFluxField sigma omega lowScale highScale e' (wN omega)) := fun omega =>
    (wN omega).toH1Function.grad_memVectorL2.add
      (memVectorL2_openCubeSet_of_continuous Q
        (continuous_streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e'))
  have hclass : Measurable fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hmem omega) :=
    measurable_toHilbertVectorL2OfVecField_neumannFluxField Q sigma sigmaInv lowScale
      highScale eN e' wN hsol hmem
  exact measurable_meshOscillationCell_of_measurable_class Q R hsc hsub hmem hclass
    hcoord hcoordsq

/-- **The flux leg's oscillation cell is measurable on the cutoff-sample
carrier.**  The closure reads its Besov tower there, not on the shell law.

: the binders of `measurable_meshOscillationCell_neumannFluxField`. -/
theorem measurable_meshOscillationCell_neumannFluxField_cutoffSample
    (Q : TriadicCube d) (sigma : PositiveScalar) (sigmaInv : ℝ)
    (lowScale highScale : ℤ) (eN e' : Vec d)
    {n : ℤ} (R : TriadicCube d) (hsc : R.scale = n)
    (hsub : openCubeSet R ⊆ openCubeSet Q)
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet Q))
    (hsol : ∀ omega : ShellSeq d,
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) (wN omega)
        (fun x => -streamForcing sigmaInv omega lowScale highScale eN x))
    (hcoord : ∀ (omega : ShellSeq d) (k : Fin d),
      IntegrableOn (fun x =>
        neumannFluxField sigma omega lowScale highScale e' (wN omega) x k)
        (openCubeSet R) volume)
    (hcoordsq : ∀ (omega : ShellSeq d) (k : Fin d),
      IntegrableOn (fun x =>
        (neumannFluxField sigma omega lowScale highScale e' (wN omega) x k) ^ 2)
        (openCubeSet R) volume) :
    Measurable fun omega : CutoffSample d =>
      meshOscillationCell n
        (neumannFluxField sigma omega.val lowScale highScale e' (wN omega.val)) R :=
  (measurable_meshOscillationCell_neumannFluxField Q sigma sigmaInv lowScale highScale
    eN e' R hsc hsub wN hsol hcoord hcoordsq).comp measurable_subtype_coe

/-! ## The flux leg's fourth-power integrability -/

/-- The elementary fourth-power Minkowski constant. -/
private theorem add_pow_four_le_eight_mul (a b : ℝ) :
    (a + b) ^ (4 : ℕ) ≤ 8 * (a ^ (4 : ℕ) + b ^ (4 : ℕ)) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * a - b * b),
    sq_nonneg (a * a + b * b), sq_nonneg a, sq_nonneg b]

/-- **The flux leg's `hintcell`, from the gradient leg's.**

The cellwise Minkowski split of
`Closure.GammaTenInteriorMinkowski.meshOscillationCell_neumannFluxField_le` and
the proved fourth-power integrability of the forcing gauge reduce the flux
cell's fourth power to the gradient cell's.

: the scale gates `hnn`, `hlt`, the cell data `hsc`, `hsub`, the measurability
`hmeas`, and the gradient leg's own fourth-power integrability `hoscInt`. -/
theorem integrable_meshOscillationCell_pow_four_neumannFluxField_cutoffSample
    (M : ABKModel d) {Q : TriadicCube d} (sigma : PositiveScalar)
    {lowScale highScale : ℤ} (hlt : lowScale < highScale) (e' : Vec d)
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet Q))
    {n : ℤ} (hnn : n ≤ lowScale) (R : TriadicCube d) (hsc : R.scale = n)
    (hsub : openCubeSet R ⊆ openCubeSet Q)
    (hmeas : Measurable fun omega : CutoffSample d =>
      meshOscillationCell n
        (neumannFluxField sigma omega.val lowScale highScale e' (wN omega.val)) R)
    (hoscInt : Integrable (fun omega : CutoffSample d =>
        meshOscillationCell n (wN omega.val).toH1Function.grad R ^ (4 : ℕ))
      (cutoffSampleLaw M).toMeasure) :
    Integrable (fun omega : CutoffSample d =>
        meshOscillationCell n
          (neumannFluxField sigma omega.val lowScale highScale e' (wN omega.val)) R ^
            (4 : ℕ))
      (cutoffSampleLaw M).toMeasure := by
  classical
  set cst : ℝ := (3 : ℝ) ^ n * (((sigma : ℝ))⁻¹ * (d : ℝ) * vecNorm e') with hcst
  have hcst0 : (0 : ℝ) ≤ cst := by
    rw [hcst]
    have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
    have hs : (0 : ℝ) ≤ ((sigma : ℝ))⁻¹ := (inv_pos.2 sigma.2).le
    have := vecNorm_nonneg e'
    positivity
  have hwin : openCubeAtScale (triadicCubeShift R) n = openCubeSet R := by
    rw [← hsc]
    exact openCubeAtScale_triadicCubeShift_eq_openCubeSet R
  -- the cellwise split
  have hle : ∀ omega : CutoffSample d,
      meshOscillationCell n
          (neumannFluxField sigma omega.val lowScale highScale e' (wN omega.val)) R ≤
        meshOscillationCell n (wN omega.val).toH1Function.grad R +
          cst * shellDerivNormSum lowScale highScale (triadicCubeShift R) omega.val := by
    intro omega
    have hgrad : MemVectorL2 (openCubeAtScale (triadicCubeShift R) n)
        (wN omega.val).toH1Function.grad := by
      rw [hwin]
      exact memVectorL2_of_subset hsub (wN omega.val).toH1Function.grad_memVectorL2
    have hforce : MemVectorL2 (openCubeAtScale (triadicCubeShift R) n)
        (streamForcing ((sigma : ℝ))⁻¹ omega.val lowScale highScale e') := by
      rw [hwin]
      exact memVectorL2_openCubeSet_of_continuous R
        (continuous_streamForcing ((sigma : ℝ))⁻¹ omega.val lowScale highScale e')
    refine (meshOscillationCell_neumannFluxField_le (sigma := sigma) omega.val lowScale
      highScale e' (wN omega.val) n hnn R hgrad hforce).trans (le_of_eq ?_)
    rw [hcst]
    ring
  -- the dominating integrand
  have hforceInt : Integrable (fun omega : CutoffSample d =>
      (cst * shellDerivNormSum lowScale highScale (triadicCubeShift R) omega.val) ^
        (4 : ℕ)) (cutoffSampleLaw M).toMeasure := by
    have hbase : Integrable (fun omega : CutoffSample d =>
        shellDerivNormSum lowScale highScale (triadicCubeShift R) omega.val ^ (4 : ℝ))
        (cutoffSampleLaw M).toMeasure :=
      integrable_comp_val_cutoffSampleLaw M
        (integrable_shellDerivNormSum_rpow_four M hlt (triadicCubeShift R))
    have hfun : (fun omega : CutoffSample d =>
        (cst * shellDerivNormSum lowScale highScale (triadicCubeShift R) omega.val) ^
          (4 : ℕ)) =
        fun omega : CutoffSample d => cst ^ (4 : ℕ) *
          (shellDerivNormSum lowScale highScale (triadicCubeShift R) omega.val ^
            (4 : ℝ)) := by
      funext omega
      rw [rpow_four_eq_pow_four, mul_pow]
    rw [hfun]
    exact hbase.const_mul _
  refine Integrable.mono' ((hoscInt.add hforceInt).const_mul (8 : ℝ))
    (hmeas.pow_const 4).aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  have hpow : meshOscillationCell n
        (neumannFluxField sigma omega.val lowScale highScale e' (wN omega.val)) R ^
          (4 : ℕ) ≤
      (meshOscillationCell n (wN omega.val).toH1Function.grad R +
        cst * shellDerivNormSum lowScale highScale (triadicCubeShift R) omega.val) ^
          (4 : ℕ) :=
    pow_le_pow_left₀ (meshOscillationCell_nonneg _ _ _) (hle omega) 4
  rw [Real.norm_of_nonneg (by positivity)]
  exact hpow.trans (add_pow_four_le_eight_mul _ _)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
