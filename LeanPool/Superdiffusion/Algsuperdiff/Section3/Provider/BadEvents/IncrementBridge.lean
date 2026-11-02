/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity.GradientW1Infinity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.IncrementOscillation
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.BasicLemmas

/-!
# IncrementBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# From the increment oscillation gauge to the Section 2.4 sensitivity gate

The frozen Section 2.4 sensitivity lemmas gate on
`UnitCubeSkewW2Infinity.gradientW1Infinity`, the volume-normalized
`W^{1,infinity}` gradient norm on the literal unit cube.  ABK26's consumer
`p.bfA.multiscalebound` feeds the stream increment
`h := k_L - k_j`, rescaled from `z + square_j` to the unit cube, into that gate.

This module builds the rescaled object and computes the exact normalization.
For a shell field `h` the rescaled unit-cube field is `y |-> h(z + 3^j y)`,
whose derivatives carry the chain-rule factors `3^j` and `3^{2j}`; consequently

`gradientW1Infinity <= max { 3^{2j} ||grad² h||_{L∞(z+square_j)},
                            3^{j} ||grad h||_{L∞(z+square_j)} }
                     = 3^{2j} ||grad h||_{W^{1,infinity}(z+square_j)}`,

which is exactly `incrementOscGauge`.  The factors are exact: the `|U|^{-1/d}`
of ABK26 at a cube of side `3^j` is `3^{-j}`.

## Main definitions

* `shellFieldUnitCube`: the unit-cube `W^{2,infinity}` package of a shell
  field, carrying the shell's own stored derivatives.

## Main results

* `frozen_matrixDerivativeNorm_eq`, `frozen_matrixSecondDerivativeNorm_eq`: the
  frozen Section 2.4 matrix-derivative norms are the shell-field ones.
* `gradientW1Infinity_shellFieldUnitCube_le`: the gate quantity is below the raw
  unit-cube derivative gauges of the shell field.

## References

* ABK26 (volume-normalized Sobolev norms).
* ABK26, `e.Bosc.def`.
* ABK26, `e.we.can.apply.cg`.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream
open scoped ENNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## Entry and evaluation continuous linear maps -/

/-- Extract a matrix entry as a linear functional. -/
def entryLinearMap (i j : Fin d) : Mat d →ₗ[ℝ] ℝ where
  toFun A := A i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Extract a matrix entry as a continuous linear functional. -/
def entryCLM (i j : Fin d) : Mat d →L[ℝ] ℝ :=
  ⟨entryLinearMap i j, (entryLinearMap i j).continuous_of_finiteDimensional⟩

/-- Evaluate a first derivative at a fixed direction as a continuous linear map. -/
def evalCLM (v : Vec d) : (Vec d →L[ℝ] Mat d) →L[ℝ] Mat d :=
  ContinuousLinearMap.apply ℝ (Mat d) v

/-- Evaluate a second derivative at its first direction as a continuous linear map. -/
def evalCLM₂ (v : Vec d) :
    (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) →L[ℝ] (Vec d →L[ℝ] Mat d) :=
  ContinuousLinearMap.apply ℝ (Vec d →L[ℝ] Mat d) v

/-! ## Essential boundedness on the literal unit cube -/

private theorem exists_bound_on_unitCube {f : Vec d → ℝ} (hf : Continuous f) :
    ∃ C : ℝ, ∀ x ∈ openCubeSet (originCube d 0), ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (cubeCenter (originCube d 0))
      (cubeRadius (originCube d 0))).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨C, fun x hx => hC x ?_⟩
  apply Metric.ball_subset_closedBall
  rw [ball_cubeCenter_eq_openCubeSet]
  exact hx

theorem memLp_top_on_unitCube {f : Vec d → ℝ} (hf : Continuous f) :
    MemLp f ∞
      (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) := by
  obtain ⟨C, hC⟩ := exists_bound_on_unitCube hf
  refine memLp_top_of_bound hf.aestronglyMeasurable C ?_
  exact ae_restrict_of_forall_mem
    (isOpen_openCubeSet (originCube d 0)).measurableSet hC

/-! ## Regularity of the entries of a shell field -/

theorem continuous_entry (g : ShellField d) (i j : Fin d) :
    Continuous fun x : Vec d => g x i j := by
  exact (entryCLM i j).continuous.comp g.1.1.continuous

theorem continuous_deriv_entry (g : ShellField d) (k i j : Fin d) :
    Continuous fun x : Vec d => ShellField.deriv g x (basisVec k) i j := by
  exact ((entryCLM i j).continuous.comp (evalCLM (basisVec k)).continuous).comp
    (ShellField.deriv g).continuous

theorem continuous_secondDeriv_entry (g : ShellField d) (l k i j : Fin d) :
    Continuous fun x : Vec d =>
      ShellField.secondDeriv g x (basisVec l) (basisVec k) i j := by
  exact (((entryCLM i j).continuous.comp (evalCLM (basisVec k)).continuous).comp
    (evalCLM₂ (basisVec l)).continuous).comp (ShellField.secondDeriv g).continuous

theorem hasFDerivAt_entry (g : ShellField d) (i j : Fin d) (x : Vec d) :
    HasFDerivAt (fun y : Vec d => g y i j)
      ((entryCLM i j).comp (ShellField.deriv g x)) x := by
  exact (entryCLM i j).hasFDerivAt.comp x (g.hasFDerivAt x)

theorem hasFDerivAt_deriv_entry (g : ShellField d) (k i j : Fin d)
    (x : Vec d) :
    HasFDerivAt (fun y : Vec d => ShellField.deriv g y (basisVec k) i j)
      (((entryCLM i j).comp (evalCLM (basisVec k))).comp
        (ShellField.secondDeriv g x)) x := by
  exact ((entryCLM i j).comp (evalCLM (basisVec k))).hasFDerivAt.comp x
    (g.deriv_hasFDerivAt x)

theorem contDiff_one_entry (g : ShellField d) (i j : Fin d) :
    ContDiff ℝ 1 fun x : Vec d => g x i j := by
  have hle : (1 : WithTop ℕ∞) ≤ 2 := by norm_num
  have hg : ContDiff ℝ 1 fun x : Vec d => g x := g.contDiff_two.of_le hle
  have hc := ((entryCLM i j).contDiff (n := 1)).comp hg
  simpa [Function.comp_def] using! hc

theorem contDiff_one_deriv_entry (g : ShellField d) (k i j : Fin d) :
    ContDiff ℝ 1 fun x : Vec d => ShellField.deriv g x (basisVec k) i j := by
  have hc := (((entryCLM i j).comp (evalCLM (basisVec k))).contDiff (n := 1)).comp
    g.contDiff_deriv
  simpa [Function.comp_def] using! hc

/-! ## The unit-cube `W^{2,infinity}` package of a shell field -/

/-- The unit-cube `W^{2,infinity}` skew package of a shell field, carrying the
shell's own stored first and second derivatives. -/
def shellFieldUnitCube (g : ShellField d) : UnitCubeSkewW2Infinity d where
  toLInfSkewMatrixFieldOn :=
    ⟨⟨fun x => g x, fun i j => memLp_top_on_unitCube (continuous_entry g i j)⟩, by
      refine Filter.Eventually.of_forall fun x => ?_
      funext i j
      change (g x i j + g x j i) / 2 = 0
      rw [g.skew_entry x i j]
      ring⟩
  firstDeriv := fun x => ShellField.deriv g x
  secondDeriv := fun x => ShellField.secondDeriv g x
  firstDeriv_memLp := fun k i j =>
    memLp_top_on_unitCube (continuous_deriv_entry g k i j)
  secondDeriv_memLp := fun l k i j =>
    memLp_top_on_unitCube (continuous_secondDeriv_entry g l k i j)
  hasWeakPartialDeriv_value := fun k i j => by
    have h := HasWeakPartialDerivOn.of_contDiff
      (U := ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
      (i := k) (contDiff_one_entry g i j)
    have heq : (fun x : Vec d =>
        (fderiv ℝ (fun y : Vec d => g y i j) x) (basisVec k)) =
        fun x : Vec d => ShellField.deriv g x (basisVec k) i j := by
      funext x
      rw [(hasFDerivAt_entry g i j x).fderiv]
      rfl
    rw [heq] at h
    exact h
  hasWeakPartialDeriv_firstDeriv := fun l k i j => by
    have h := HasWeakPartialDerivOn.of_contDiff
      (U := ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
      (i := l) (contDiff_one_deriv_entry g k i j)
    have heq : (fun x : Vec d =>
        (fderiv ℝ (fun y : Vec d =>
          ShellField.deriv g y (basisVec k) i j) x) (basisVec l)) =
        fun x : Vec d =>
          ShellField.secondDeriv g x (basisVec l) (basisVec k) i j := by
      funext x
      rw [(hasFDerivAt_deriv_entry g k i j x).fderiv]
      rfl
    rw [heq] at h
    exact h

@[simp]
theorem shellFieldUnitCube_firstDeriv (g : ShellField d) (x : Vec d) :
    (shellFieldUnitCube g).firstDeriv x = ShellField.deriv g x :=
  rfl

@[simp]
theorem shellFieldUnitCube_secondDeriv (g : ShellField d) (x : Vec d) :
    (shellFieldUnitCube g).secondDeriv x = ShellField.secondDeriv g x :=
  rfl

@[simp]
theorem shellFieldUnitCube_value (g : ShellField d) (x : Vec d) :
    (shellFieldUnitCube g).toLInfSkewMatrixFieldOn.1.1 x = g x :=
  rfl

/-! ## The frozen Section 2.4 matrix-derivative norms are the shell-field ones -/

private theorem vecNorm_zero_le_one : vecNorm (0 : Vec d) ≤ 1 := by
  simp [vecNorm]

theorem frozen_matrixDerivativeNorm_eq (D : ShellField.MatrixDerivative d) :
    Algsuperdiff.Frozen.Section24.matrixDerivativeNorm D =
      ShellField.matrixDerivativeNorm D := by
  have hbdd : BddAbove (Set.range fun v : {v : Vec d // vecNorm v ≤ 1} =>
      matrixNorm (D v.1)) := by
    refine ⟨ShellField.matrixDerivativeNorm D, ?_⟩
    rintro r ⟨v, rfl⟩
    exact ShellField.matrixOperatorNorm_apply_le_matrixDerivativeNorm D v.1 v.2
  refine le_antisymm ?_ ?_
  · rw [Algsuperdiff.Frozen.Section24.matrixDerivativeNorm]
    refine csSup_le ⟨matrixNorm (D 0), ⟨⟨0, vecNorm_zero_le_one⟩, rfl⟩⟩ ?_
    rintro r ⟨v, rfl⟩
    exact ShellField.matrixOperatorNorm_apply_le_matrixDerivativeNorm D v.1 v.2
  · rw [matrixDerivativeNorm_le_iff]
    constructor
    · have h0 : matrixNorm (D 0) ≤
          Algsuperdiff.Frozen.Section24.matrixDerivativeNorm D := by
        rw [Algsuperdiff.Frozen.Section24.matrixDerivativeNorm]
        exact le_csSup hbdd ⟨⟨0, vecNorm_zero_le_one⟩, rfl⟩
      rwa [ContinuousLinearMap.map_zero, show matrixNorm (0 : Mat d) = 0 by
        simp [matrixNorm]] at h0
    · intro v hv
      rw [Algsuperdiff.Frozen.Section24.matrixDerivativeNorm]
      exact le_csSup hbdd ⟨⟨v, hv⟩, rfl⟩

theorem frozen_matrixSecondDerivativeNorm_eq
    (H : ShellField.MatrixSecondDerivative d) :
    Algsuperdiff.Frozen.Section24.matrixSecondDerivativeNorm H =
      ShellField.matrixSecondDerivativeNorm H := by
  have hbdd : BddAbove (Set.range fun v : {v : Vec d // vecNorm v ≤ 1} =>
      Algsuperdiff.Frozen.Section24.matrixDerivativeNorm (H v.1)) := by
    refine ⟨ShellField.matrixSecondDerivativeNorm H, ?_⟩
    rintro r ⟨v, rfl⟩
    change Algsuperdiff.Frozen.Section24.matrixDerivativeNorm (H v.1) ≤ _
    rw [frozen_matrixDerivativeNorm_eq]
    exact ShellField.matrixDerivativeNorm_apply_le_matrixSecondDerivativeNorm H v.1 v.2
  refine le_antisymm ?_ ?_
  · rw [Algsuperdiff.Frozen.Section24.matrixSecondDerivativeNorm]
    refine csSup_le
      ⟨Algsuperdiff.Frozen.Section24.matrixDerivativeNorm (H 0),
        ⟨⟨0, vecNorm_zero_le_one⟩, rfl⟩⟩ ?_
    rintro r ⟨v, rfl⟩
    change Algsuperdiff.Frozen.Section24.matrixDerivativeNorm (H v.1) ≤ _
    rw [frozen_matrixDerivativeNorm_eq]
    exact ShellField.matrixDerivativeNorm_apply_le_matrixSecondDerivativeNorm H v.1 v.2
  · rw [ShellField.matrixSecondDerivativeNorm_le_iff]
    constructor
    · have h0 : Algsuperdiff.Frozen.Section24.matrixDerivativeNorm (H 0) ≤
          Algsuperdiff.Frozen.Section24.matrixSecondDerivativeNorm H := by
        rw [Algsuperdiff.Frozen.Section24.matrixSecondDerivativeNorm]
        exact le_csSup hbdd ⟨⟨0, vecNorm_zero_le_one⟩, rfl⟩
      rw [frozen_matrixDerivativeNorm_eq, ContinuousLinearMap.map_zero] at h0
      exact le_trans (le_antisymm matrixDerivativeNorm_zero_le
        (ShellField.matrixDerivativeNorm_nonneg _)).ge h0
    · intro u hu
      rw [← frozen_matrixDerivativeNorm_eq,
        Algsuperdiff.Frozen.Section24.matrixSecondDerivativeNorm]
      exact le_csSup hbdd ⟨⟨u, hu⟩, rfl⟩

/-! ## The gate quantity of a shell field's unit-cube package -/

/-- A pointwise unit-cube bound controls the real-valued essential-supremum norm. -/
theorem toReal_eLpNorm_unitCube_le {f : Vec d → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x ∈ openCubeSet (originCube d 0), ‖f x‖ ≤ C) :
    (eLpNorm f ∞
      (volumeMeasureOn
        ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))).toReal ≤ C := by
  by_cases hf : AEStronglyMeasurable f
      (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hf, ENNReal.toReal_top]
    exact hC
  rw [eLpNorm_exponent_top hf]
  refine ENNReal.toReal_le_of_le_ofReal hC ?_
  exact eLpNormEssSup_le_of_ae_bound
    (ae_restrict_of_forall_mem
      (isOpen_openCubeSet (originCube d 0)).measurableSet hbound)

/-- The Section 2.4 gate quantity of a shell field's unit-cube package is below
the raw unit-cube derivative gauges of the shell field. -/
theorem gradientW1Infinity_shellFieldUnitCube_le (g : ShellField d) :
    (shellFieldUnitCube g).gradientW1Infinity ≤
      max (ShellField.unitCubeSecondDerivNorm g)
        (ShellField.unitCubeDerivNorm g) := by
  rw [UnitCubeSkewW2Infinity.gradientW1Infinity]
  refine max_le ?_ ?_
  · refine le_trans ?_ (le_max_left _ _)
    refine toReal_eLpNorm_unitCube_le (ShellField.unitCubeSecondDerivNorm_nonneg g)
      fun x hx => ?_
    have hval : Algsuperdiff.Frozen.Section24.matrixSecondDerivativeNorm
        ((shellFieldUnitCube g).secondDeriv x) =
        ShellField.matrixSecondDerivativeNorm (ShellField.secondDeriv g x) := by
      rw [shellFieldUnitCube_secondDeriv, frozen_matrixSecondDerivativeNorm_eq]
    rw [Real.norm_eq_abs, hval,
      abs_of_nonneg (ShellField.matrixSecondDerivativeNorm_nonneg _)]
    exact matrixSecondDerivativeNorm_secondDeriv_le_unitCubeSecondDerivNorm g hx
  · refine le_trans ?_ (le_max_right _ _)
    refine toReal_eLpNorm_unitCube_le (ShellField.unitCubeDerivNorm_nonneg g) fun x hx => ?_
    have hval : Algsuperdiff.Frozen.Section24.matrixDerivativeNorm
        ((shellFieldUnitCube g).firstDeriv x) =
        ShellField.matrixDerivativeNorm (ShellField.deriv g x) := by
      rw [shellFieldUnitCube_firstDeriv, frozen_matrixDerivativeNorm_eq]
    rw [Real.norm_eq_abs, hval,
      abs_of_nonneg (ShellField.matrixDerivativeNorm_nonneg _)]
    exact matrixDerivativeNorm_deriv_le_unitCubeDerivNorm g hx

end

end Algsuperdiff.Section3.Provider.BadEvents
