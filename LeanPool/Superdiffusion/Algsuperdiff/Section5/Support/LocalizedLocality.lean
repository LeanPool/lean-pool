/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LambdaLocal
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.CoefficientLocalMeasurable
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.LocalizedAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.LocalizedMeasurable

/-!
# LocalizedLocality

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The localized quantities read only the cube

The localized error and the localized regularity of `y + □_n` are built from the
solutions of Dirichlet problems on that cube for the coefficient field at scale
`n`.  The equation sees the field only on the cube, so both quantities are
functions of the restriction of the field to the closed cube, and that
restriction is a local observable of the closed cube.  This module makes both
halves precise and concludes that the two quantities, and hence the good cube
event, lie in the local information of `y + □_n`.

The first half is a change of parameter: replacing the coefficient field by the
field extended from its restriction to the closed cube changes neither the set
of solutions nor the value of either quantity, because the two fields agree on
the cube.

The second half is lower semicontinuity in that parameter.  Almost-everywhere
uniqueness collapses the supremum over the solutions of the rough-field problem
to the selected one, and the ball-average characterizations turn each remaining
inner quantity into a supremum of averages of that solution over balls inside
the cube.  Each such average is *continuous* in the coefficient field, by the
energy estimate and the zero-trace Poincaré inequality, so each inner quantity
is a supremum of continuous functions and the two quantities are suprema of
those over the whole normalized forcing class.  A supremum of lower
semicontinuous functions is lower semicontinuous, so no countable reduction of
the forcing class is needed here.

The large-scale event, by contrast, reads every shell at or above `n` and is not
an event of the cube; only the good cube event, and its intersection with any
other local event, is stated as local.

## Main definitions

* `fieldLocalizedError`, `fieldLocalizedRegularity` — the two quantities as
  functions of a continuous coefficient field on the closed cube.

## References

* ABK26, the localized error and regularity quantities, the good cube event and
  the chains of good cubes of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The two quantities as functions of the coefficient field on the cube -/

/-- The localized error of a continuous coefficient field on the closed cube. -/
def fieldLocalizedError (M : ABKModel d) (n : ℤ) (y : Vec d)
    (A : ellipticCube M.nu y n) : ℝ≥0∞ :=
  ⨆ g : Vec d → Vec d, ⨆ _ : NormalizedForceAt y n g,
  ⨆ u : H1Function (cubeSetAt y n),
  ⨆ _ : IsDirichletSolutionAt (extendCoeff y n A.1) y n u g,
  ⨆ v : H1Function (cubeSetAt y n),
  ⨆ _ : IsDirichletSolutionAt (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n v g,
    ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
      eLpNorm (fun x => u.toFun x - v.toFun x) ⊤ (volume.restrict (cubeSetAt y n))

/-- The localized regularity of a continuous coefficient field on the closed
cube. -/
def fieldLocalizedRegularity (M : ABKModel d) (n : ℤ) (y : Vec d)
    (A : ellipticCube M.nu y n) : ℝ≥0∞ :=
  ⨆ g : Vec d → Vec d, ⨆ _ : NormalizedForceAt y n g,
  ⨆ u : H1Function (cubeSetAt y n),
  ⨆ _ : IsDirichletSolutionAt (extendCoeff y n A.1) y n u g,
  ⨅ uRep : Vec d → ℝ, ⨅ _ : IsCubeRepresentative y n u uRep,
    ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
      holderSeminormOn (cubeSetAt y n) (1 / 2) uRep

/-- The cutoff coefficient field and the field extended from its restriction to
the closed cube define the same localized Dirichlet problem. -/
theorem isDirichletSolutionAt_cutoff_iff_extendCoeff (M : ABKModel d) (m n : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) {u : H1Function (cubeSetAt y n)} {g : Vec d → Vec d} :
    IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu m omega).toCoeffField) y n u g ↔
      IsDirichletSolutionAt
        (extendCoeff y n (coefficientCutoffRestrict M.nu m (closedCubeAt y n) omega)) y n u g := by
  have hagree : ∀ x ∈ cubeSetAt y n,
      (Cutoff.coefficientCutoff M.nu m omega).toCoeffField x =
        extendCoeff y n
          (coefficientCutoffRestrict M.nu m (closedCubeAt y n) omega) x := by
    intro x hx
    rw [extendCoeff_apply_of_mem _ (cubeSetAt_subset_closedCubeAt y n hx)]
    rfl
  exact ⟨isDirichletSolutionAt_congr_coeff hagree,
    isDirichletSolutionAt_congr_coeff fun x hx => (hagree x hx).symm⟩

/-- **The localized error reads the sample only through the coefficient field on
the closed cube.** -/
theorem localizedError_eq_fieldLocalizedError (M : ABKModel d) (n : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) :
    localizedError M n y omega =
      fieldLocalizedError M n y
        ⟨coefficientCutoffRestrict M.nu n (closedCubeAt y n) omega,
          coefficientCutoffRestrict_mem_ellipticCube M n y n omega⟩ := by
  refine iSup_congr fun g => iSup_congr fun _hg => iSup_congr fun u => ?_
  exact iSup_congr_Prop (isDirichletSolutionAt_cutoff_iff_extendCoeff M n n y omega) fun _ => rfl

/-- **The localized regularity reads the sample only through the coefficient
field on the closed cube.** -/
theorem localizedRegularity_eq_fieldLocalizedRegularity (M : ABKModel d) (n : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) :
    localizedRegularity M n y omega =
      fieldLocalizedRegularity M n y
        ⟨coefficientCutoffRestrict M.nu n (closedCubeAt y n) omega,
          coefficientCutoffRestrict_mem_ellipticCube M n y n omega⟩ := by
  refine iSup_congr fun g => iSup_congr fun _hg => iSup_congr fun u => ?_
  exact iSup_congr_Prop (isDirichletSolutionAt_cutoff_iff_extendCoeff M n n y omega) fun _ => rfl

/-! ## 2. The ball-average gauges see only the almost-everywhere class -/

private theorem setAverage_congr_of_ae' {U : Set (Vec d)} {f h : Vec d → ℝ}
    (hae : f =ᵐ[volume.restrict U] h) {B : Set (Vec d)} (hBU : B ⊆ U) :
    (⨍ w in B, f w ∂volume) = ⨍ w in B, h w ∂volume := by
  rw [setAverage_eq, setAverage_eq]
  congr 1
  exact integral_congr_ae (hae.filter_mono (ae_mono (Measure.restrict_mono hBU le_rfl)))

/-- The ball-average supremum gauge depends only on the almost-everywhere class
of its argument on the ambient set: every ball it reads lies in that set. -/
theorem ballAverageSupNormOn_congr_ae {U D : Set (Vec d)} {f h : Vec d → ℝ}
    (hae : f =ᵐ[volume.restrict U] h) :
    ballAverageSupNormOn U D f = ballAverageSupNormOn U D h := by
  refine iSup_congr fun x => iSup_congr fun _ => iSup_congr fun k => iSup_congr fun hb => ?_
  rw [setAverage_congr_of_ae' hae hb]

/-- The ball-average Hölder gauge depends only on the almost-everywhere class of
its argument on the ambient set. -/
theorem ballAverageHolderOn_congr_ae {U D : Set (Vec d)} {f h : Vec d → ℝ}
    (hae : f =ᵐ[volume.restrict U] h) :
    ballAverageHolderOn U D f = ballAverageHolderOn U D h := by
  refine iSup_congr fun x => iSup_congr fun _ => iSup_congr fun z => iSup_congr fun _ =>
    iSup_congr fun _ => iSup_congr fun k => iSup_congr fun hbx => iSup_congr fun hbz => ?_
  rw [setAverage_congr_of_ae' hae hbx, setAverage_congr_of_ae' hae hbz]

/-! ## 3. Collapsing the solution binder -/

/-- The normalization constant of the forcing class of `y + □_n` is
nonnegative. -/
theorem rpow_three_neg_half_nonneg (n : ℤ) :
    (0 : ℝ) ≤ Real.rpow 3 (-(n : ℝ) / 2) :=
  (Real.rpow_pos_of_pos (by norm_num) _).le

/-- **The solution binder of the localized regularity collapses.**  Two solutions
of the same problem agree almost everywhere, and the gauge sees only that class,
so the supremum over the solutions is the value at the selected one, read off
its ball averages. -/
theorem fieldLocalizedRegularity_eq_iSup (M : ABKModel d) (n : ℤ) (y : Vec d)
    {D : Set (Vec d)} (hD : Dense D) (A : ellipticCube M.nu y n) :
    fieldLocalizedRegularity M n y A =
      ⨆ g : Vec d → Vec d, ⨆ hg : NormalizedForceAt y n g,
        ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
          ballAverageHolderOn (cubeSetAt y n) D
            (solutionOfField M y n (rpow_three_neg_half_nonneg n) hg A).toFun := by
  have : NeZero d := Provider.Orlicz.neZero_of_model M
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := Provider.Orlicz.sigmaBar_pos M n
  have hKn : (0 : ℝ) < Real.rpow 3 (-(n : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hcX : ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact mul_pos hsig hKn
  obtain ⟨Lam, hEll⟩ := exists_isEllipticFieldOn_extendCoeff M.nu_pos y n A.2
  refine iSup_congr fun g => iSup_congr fun hg => ?_
  refine le_antisymm (iSup_le fun u => iSup_le fun hu => ?_) ?_
  · rw [iInf_isCubeRepresentative_eq_ballAverageHolderOn hD u hcX]
    have hae := (isDirichletSolutionAt_ae_unique (Provider.Orlicz.dim_pos_of_model M) hEll hu
      (isDirichletSolutionAt_solutionOfField M y n
        (rpow_three_neg_half_nonneg n) hg A)).2
    rw [ballAverageHolderOn_congr_ae hae]
  · refine le_iSup_of_le (solutionOfField M y n (rpow_three_neg_half_nonneg n) hg A)
      (le_iSup_of_le (isDirichletSolutionAt_solutionOfField M y n
        (rpow_three_neg_half_nonneg n) hg A) ?_)
    exact (iInf_isCubeRepresentative_eq_ballAverageHolderOn hD _ hcX).ge

/-- **The rough-field solution binder of the localized error collapses.**  The
comparator binder is kept: the comparator background does not depend on the
coefficient field. -/
theorem fieldLocalizedError_eq_iSup (M : ABKModel d) (n : ℤ) (y : Vec d)
    {D : Set (Vec d)} (hD : Dense D) (A : ellipticCube M.nu y n) :
    fieldLocalizedError M n y A =
      ⨆ g : Vec d → Vec d, ⨆ hg : NormalizedForceAt y n g,
      ⨆ v : H1Function (cubeSetAt y n),
      ⨆ _ : IsDirichletSolutionAt (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n v g,
        ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
          ballAverageSupNormOn (cubeSetAt y n) D
            (fun x => (solutionOfField M y n (rpow_three_neg_half_nonneg n) hg A).toFun x -
              v.toFun x) := by
  have : NeZero d := Provider.Orlicz.neZero_of_model M
  obtain ⟨Lam, hEll⟩ := exists_isEllipticFieldOn_extendCoeff M.nu_pos y n A.2
  refine iSup_congr fun g => iSup_congr fun hg => ?_
  refine le_antisymm (iSup_le fun u => iSup_le fun hu => iSup_le fun v => iSup_le fun hv => ?_) ?_
  · rw [eLpNorm_top_sub_eq_ballAverageSupNormOn hD u v]
    have hae := (isDirichletSolutionAt_ae_unique (Provider.Orlicz.dim_pos_of_model M) hEll hu
      (isDirichletSolutionAt_solutionOfField M y n
        (rpow_three_neg_half_nonneg n) hg A)).2
    have hsub : (fun x => u.toFun x - v.toFun x) =ᵐ[volume.restrict (cubeSetAt y n)]
        fun x => (solutionOfField M y n (rpow_three_neg_half_nonneg n) hg A).toFun x -
          v.toFun x := by
      filter_upwards [hae] with x hx
      rw [hx]
    rw [ballAverageSupNormOn_congr_ae hsub]
    exact le_iSup_of_le v (le_iSup_of_le hv le_rfl)
  · refine iSup_le fun v => iSup_le fun hv => ?_
    refine le_iSup_of_le (solutionOfField M y n (rpow_three_neg_half_nonneg n) hg A)
      (le_iSup_of_le (isDirichletSolutionAt_solutionOfField M y n
        (rpow_three_neg_half_nonneg n) hg A)
        (le_iSup_of_le v (le_iSup_of_le hv ?_)))
    rw [eLpNorm_top_sub_eq_ballAverageSupNormOn hD _ v]

/-! ## 4. Lower semicontinuity in the coefficient field -/

private theorem continuous_setAverage_ball_solutionOfField (M : ABKModel d) (y : Vec d) (n : ℤ)
    {g : Vec d → Vec d} {Kg : ℝ} (hKg : 0 ≤ Kg)
    (hg : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kg g)
    {p : Vec d} {rad : ℝ} (hB : Metric.ball p rad ⊆ cubeSetAt y n) :
    Continuous fun A : ellipticCube M.nu y n =>
      ⨍ z in Metric.ball p rad, (solutionOfField M y n hKg hg A).toFun z ∂volume := by
  have hrw : (fun A : ellipticCube M.nu y n =>
      ⨍ z in Metric.ball p rad, (solutionOfField M y n hKg hg A).toFun z ∂volume) =
      fun A => (volume.real (Metric.ball p rad))⁻¹ *
        fieldSetIntegral M y n hKg hg (Metric.ball p rad) A := by
    funext A
    rw [setAverage_eq, smul_eq_mul]
    rfl
  rw [hrw]
  exact continuous_const.mul (continuous_fieldSetIntegral M y n hKg hg hB)

/-- **The localized regularity is lower semicontinuous in the coefficient field
on the cube.** -/
theorem lowerSemicontinuous_fieldLocalizedRegularity (M : ABKModel d) (n : ℤ) (y : Vec d) :
    LowerSemicontinuous (fieldLocalizedRegularity M n y) := by
  obtain ⟨D, _hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Vec d)
  have hEq : fieldLocalizedRegularity M n y = fun A : ellipticCube M.nu y n =>
      ⨆ g : Vec d → Vec d, ⨆ hg : NormalizedForceAt y n g,
        ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
          ballAverageHolderOn (cubeSetAt y n) D
            (solutionOfField M y n (rpow_three_neg_half_nonneg n) hg A).toFun :=
    funext fun A => fieldLocalizedRegularity_eq_iSup M n y hDd A
  rw [hEq]
  have hne : ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  refine lowerSemicontinuous_biSup fun g hg => ?_
  simp only [ballAverageHolderOn, ENNReal.mul_iSup]
  refine lowerSemicontinuous_biSup fun x _hx => lowerSemicontinuous_biSup fun z _hz => ?_
  refine lowerSemicontinuous_iSup fun _hxz => lowerSemicontinuous_iSup fun k => ?_
  by_cases hbx : Metric.ball x (1 / (k + 1 : ℝ)) ⊆ cubeSetAt y n
  · by_cases hbz : Metric.ball z (1 / (k + 1 : ℝ)) ⊆ cubeSetAt y n
    · simp only [iSup_pos hbx, iSup_pos hbz]
      refine Continuous.lowerSemicontinuous ((ENNReal.continuous_const_mul hne).comp ?_)
      exact ENNReal.continuous_ofReal.comp
        (((continuous_setAverage_ball_solutionOfField M y n
            (rpow_three_neg_half_nonneg n) hg hbx).sub
          (continuous_setAverage_ball_solutionOfField M y n
            (rpow_three_neg_half_nonneg n) hg hbz)).abs.div_const _)
    · simp only [iSup_pos hbx, iSup_neg hbz]
      exact lowerSemicontinuous_const
  · simp only [iSup_neg hbx]
    exact lowerSemicontinuous_const

/-- **The localized error is lower semicontinuous in the coefficient field on the
cube.** -/
theorem lowerSemicontinuous_fieldLocalizedError (M : ABKModel d) (n : ℤ) (y : Vec d) :
    LowerSemicontinuous (fieldLocalizedError M n y) := by
  obtain ⟨D, _hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Vec d)
  have hEq : fieldLocalizedError M n y = fun A : ellipticCube M.nu y n =>
      ⨆ g : Vec d → Vec d, ⨆ hg : NormalizedForceAt y n g,
      ⨆ v : H1Function (cubeSetAt y n),
      ⨆ _ : IsDirichletSolutionAt (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n v g,
        ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
          ballAverageSupNormOn (cubeSetAt y n) D
            (fun x => (solutionOfField M y n (rpow_three_neg_half_nonneg n) hg A).toFun x -
              v.toFun x) :=
    funext fun A => fieldLocalizedError_eq_iSup M n y hDd A
  rw [hEq]
  have hne : ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  refine lowerSemicontinuous_biSup fun g hg => lowerSemicontinuous_biSup fun v _hv => ?_
  simp only [ballAverageSupNormOn, ENNReal.mul_iSup]
  refine lowerSemicontinuous_biSup fun x _hx => lowerSemicontinuous_iSup fun k => ?_
  by_cases hb : Metric.ball x (1 / (k + 1 : ℝ)) ⊆ cubeSetAt y n
  · simp only [iSup_pos hb]
    have hrw : (fun A : ellipticCube M.nu y n =>
        ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
          ENNReal.ofReal |⨍ w in Metric.ball x (1 / (k + 1 : ℝ)),
            ((solutionOfField M y n (rpow_three_neg_half_nonneg n) hg A).toFun w -
              v.toFun w) ∂volume|) =
        fun A : ellipticCube M.nu y n =>
          ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
            ENNReal.ofReal |(⨍ w in Metric.ball x (1 / (k + 1 : ℝ)),
                (solutionOfField M y n (rpow_three_neg_half_nonneg n) hg A).toFun w ∂volume) -
              ⨍ w in Metric.ball x (1 / (k + 1 : ℝ)), v.toFun w ∂volume| := by
      funext A
      rw [setAverage_ball_sub_of_h1 _ v hb]
    rw [hrw]
    refine Continuous.lowerSemicontinuous ((ENNReal.continuous_const_mul hne).comp ?_)
    exact ENNReal.continuous_ofReal.comp
      (((continuous_setAverage_ball_solutionOfField M y n
          (rpow_three_neg_half_nonneg n) hg hb).sub continuous_const).abs)
  · simp only [iSup_neg hb]
    exact lowerSemicontinuous_const

/-! ## 5. The two quantities are local observables of the closed cube -/

/-- **The localized error of `y + □_n` is measurable for the local information
of the closed cube `y + □_n`.** -/
theorem measurable_localizedError_local (M : ABKModel d) (n : ℤ) (y : Vec d) :
    Measurable[Cutoff.cutoffSampleLocalSigma M n (closedCubeAt y n)]
      (localizedError M n y) := by
  have hA : Measurable[Cutoff.cutoffSampleLocalSigma M n (closedCubeAt y n)]
      fun omega : Cutoff.CutoffSample d =>
        (⟨coefficientCutoffRestrict M.nu n (closedCubeAt y n) omega,
          coefficientCutoffRestrict_mem_ellipticCube M n y n omega⟩ :
            ellipticCube M.nu y n) :=
    Measurable.subtype_mk (measurable_coefficientCutoffRestrict_local M n y n)
  have hEq : localizedError M n y = fun omega : Cutoff.CutoffSample d =>
      fieldLocalizedError M n y
        ⟨coefficientCutoffRestrict M.nu n (closedCubeAt y n) omega,
          coefficientCutoffRestrict_mem_ellipticCube M n y n omega⟩ :=
    funext fun omega => localizedError_eq_fieldLocalizedError M n y omega
  rw [hEq]
  exact ((lowerSemicontinuous_fieldLocalizedError M n y).measurable).comp hA

/-- **The localized regularity of `y + □_n` is measurable for the local
information of the closed cube `y + □_n`.** -/
theorem measurable_localizedRegularity_local (M : ABKModel d) (n : ℤ) (y : Vec d) :
    Measurable[Cutoff.cutoffSampleLocalSigma M n (closedCubeAt y n)]
      (localizedRegularity M n y) := by
  have hA : Measurable[Cutoff.cutoffSampleLocalSigma M n (closedCubeAt y n)]
      fun omega : Cutoff.CutoffSample d =>
        (⟨coefficientCutoffRestrict M.nu n (closedCubeAt y n) omega,
          coefficientCutoffRestrict_mem_ellipticCube M n y n omega⟩ :
            ellipticCube M.nu y n) :=
    Measurable.subtype_mk (measurable_coefficientCutoffRestrict_local M n y n)
  have hEq : localizedRegularity M n y = fun omega : Cutoff.CutoffSample d =>
      fieldLocalizedRegularity M n y
        ⟨coefficientCutoffRestrict M.nu n (closedCubeAt y n) omega,
          coefficientCutoffRestrict_mem_ellipticCube M n y n omega⟩ :=
    funext fun omega => localizedRegularity_eq_fieldLocalizedRegularity M n y omega
  rw [hEq]
  exact ((lowerSemicontinuous_fieldLocalizedRegularity M n y).measurable).comp hA

/-! ## 6. The good cube event -/

/-- **The good cube event is a local event of the closed cube.** -/
theorem measurableSet_goodCubeEvent_local (M : ABKModel d) (Creg : ℝ) (n : ℤ) (y : Vec d)
    (ep : ℝ) :
    MeasurableSet[Cutoff.cutoffSampleLocalSigma M n (closedCubeAt y n)]
      (goodCubeEvent M Creg n y ep) := by
  let mLoc : MeasurableSpace (Cutoff.CutoffSample d) :=
    Cutoff.cutoffSampleLocalSigma M n (closedCubeAt y n)
  exact (measurableSet_le (measurable_localizedError_local M n y) measurable_const).inter
    (measurableSet_le (measurable_localizedRegularity_local M n y) measurable_const)

/-- **The good cube event is a local event of any region containing the closed
cube**, at any scale at least `n`. -/
theorem measurableSet_goodCubeEvent_local_of_subset (M : ABKModel d) (Creg : ℝ) (n m : ℤ)
    (y : Vec d) (ep : ℝ) (hnm : n ≤ m) {U : Set (Vec d)} (hU : closedCubeAt y n ⊆ U) :
    MeasurableSet[Cutoff.cutoffSampleLocalSigma M m U] (goodCubeEvent M Creg n y ep) :=
  Provider.BadEvents.cutoffSampleLocalSigma_mono M hnm hU _
    (measurableSet_goodCubeEvent_local M Creg n y ep)

end

end Algsuperdiff.Section5.Support
