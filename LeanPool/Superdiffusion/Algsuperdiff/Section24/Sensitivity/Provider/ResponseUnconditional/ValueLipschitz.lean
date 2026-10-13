/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.BigLambda.CubeTermA
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.InputBC
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.UnitCubeSkewW2Infinity.ValueL2
public import LeanPool.HighContrastHomogenization.Support.Besov.Localization

/-!
# ValueLipschitz

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The cube-local `L²` value budget and the gradient-Lipschitz value representative

Source: ABK26, the Term A bookkeeping of the unconditional `J` estimate.

The unconditional aggregation of
`Algsuperdiff.Frozen.Section24.responseJ_sensitivity_unconditional` prices the
Term A error of every mesoscopic cube against `‖h‖²_{L²(□₀)}`, not against the
root `W^{1,∞}` norm.  Two ingredients are needed, and both live here.

* **The value budget.**  `valueBudget h R` is the normalized `L²`-square of
  `|h|` on the triadic cube `R`.  Its depth-`n` descendant average over the
  unit cube is *exactly* `‖h‖²_{L²(□₀)}` (`descendantsAverage_valueBudget`),
  by the cube-average tower identity of CoarseGraining, and it dominates the
  normalized `L¹` average of `|h|` on `R` by Cauchy-Schwarz
  (`cubeAverage_matrixNormField_le_sqrt_valueBudget`).

* **The gradient-Lipschitz representative of the value field.**  The frozen
  carrier stores a weak first derivative of the value field which is bounded by
  `‖∇h‖_{W^{1,∞}}` (*not* only by `‖h‖_{W^{1,∞}}`), so the
  `W^{1,∞}`-to-Lipschitz bridge of `Provider.DhBound.Lipschitz` produces a
  globally Lipschitz representative of the *value* field with constant
  `d ‖∇h‖_{W^{1,∞}}`.  This is what turns the Term A Besov seminorm into a
  *scale-damped* quantity on a deep cube.

The pointwise norm field `matrixNormField`, its measurability chain and the
characterization `valueL2_sq_eq_integral` are *not* here: they live in
`Algsuperdiff.Section24.UnitCubeSkewW2Infinity.ValueL2`, an ordinary A module
beside the frozen definition, so that `UnitCubeSkewW2Infinity.valueL2` is
delta-unfolded exactly once in the whole development and every consumer routes
through the characterization.

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz
open Algsuperdiff.Section24.Sensitivity.Provider.Lambda
open Algsuperdiff.Section24.UnitCubeSkewW2Infinity
open scoped BigOperators ENNReal NNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## The gradient-Lipschitz representative of the value field -/

/-- **Lipschitz representative of a frozen value entry, with the gradient
constant.**  Identical to
`Provider.DhBound.Lipschitz.exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_value`
except that the a.e. bound on the weak derivative is taken from
`‖∇h‖_{W^{1,∞}}` rather than from `‖h‖_{W^{1,∞}}`. -/
theorem exists_lipschitz_ae_eq_value_gradientW1Infinity
    (h : UnitCubeSkewW2Infinity d) (i j : Fin d) :
    ∃ v : Vec d → ℝ,
      (∀ x y : Vec d, ‖v x - v y‖ ≤ (d : ℝ) * h.gradientW1Infinity * ‖x - y‖) ∧
        v =ᵐ[volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))]
          fun x => h.toLInfSkewMatrixFieldOn.1.1 x i j :=
  exists_lipschitz_ae_eq_of_hasWeakPartialDeriv_bound
    (U := ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (u := fun x => h.toLInfSkewMatrixFieldOn.1.1 x i j)
    (g := fun k x => h.firstDeriv x (basisVec k) i j)
    (B := h.gradientW1Infinity)
    (cubeDomain (originCube d 0)).isDomain
    (gradientW1Infinity_nonneg h)
    (h.toLInfSkewMatrixFieldOn.1.2 i j)
    (fun k => h.firstDeriv_memLp k i j)
    (fun k => ae_abs_firstDeriv_le_gradientW1Infinity h k i j)
    (fun k => h.hasWeakPartialDeriv_value k i j)

/-- The entrywise globally Lipschitz representative of the frozen matrix field,
with the **gradient** Lipschitz constant. -/
def gradValueRep (h : UnitCubeSkewW2Infinity d) (i j : Fin d) : Vec d → ℝ :=
  (exists_lipschitz_ae_eq_value_gradientW1Infinity h i j).choose

theorem gradValueRep_lipschitz (h : UnitCubeSkewW2Infinity d) (i j : Fin d)
    (x y : Vec d) :
    |gradValueRep h i j x - gradValueRep h i j y| ≤
      (d : ℝ) * h.gradientW1Infinity * ‖x - y‖ := by
  simpa [Real.norm_eq_abs] using!
    (exists_lipschitz_ae_eq_value_gradientW1Infinity h i j).choose_spec.1 x y

theorem gradValueRep_ae_eq_carrier (h : UnitCubeSkewW2Infinity d) (i j : Fin d) :
    (fun x => gradValueRep h i j x)
      =ᵐ[volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))]
      fun x => h.toLInfSkewMatrixFieldOn.1.1 x i j :=
  (exists_lipschitz_ae_eq_value_gradientW1Infinity h i j).choose_spec.2

theorem gradValueRep_ae_eq_cube (h : UnitCubeSkewW2Infinity d) (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (i j : Fin d) :
    (fun x => gradValueRep h i j x)
      =ᵐ[normalizedCubeMeasure R]
      fun x => h.toLInfSkewMatrixFieldOn.1.1 x i j :=
  ae_normalizedCubeMeasure_of_ae_cubeDomain (P := fun x =>
      gradValueRep h i j x = h.toLInfSkewMatrixFieldOn.1.1 x i j) R
    (ae_restrict_of_ae_restrict_of_subset hsub (gradValueRep_ae_eq_carrier h i j))

/-- The Lipschitz representative of the Term A field, with the gradient
constant. -/
def gradTermARep (h : UnitCubeSkewW2Infinity d) (p : Vec d) : Vec d → Vec d :=
  fun x i => ∑ j : Fin d, gradValueRep h j i x * p j

theorem gradTermARep_ae_eq_cube (h : UnitCubeSkewW2Infinity d) (p : Vec d)
    (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) :
    gradTermARep h p =ᵐ[normalizedCubeMeasure R] termAField h p := by
  classical
  have hall : ∀ᵐ x ∂ normalizedCubeMeasure R, ∀ i j : Fin d,
      gradValueRep h i j x = h.toLInfSkewMatrixFieldOn.1.1 x i j := by
    rw [MeasureTheory.ae_all_iff]
    intro i
    rw [MeasureTheory.ae_all_iff]
    intro j
    exact gradValueRep_ae_eq_cube h R hsub i j
  filter_upwards [hall] with x hx
  funext i
  rw [termAField_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [hx j i]

theorem gradTermARep_lipschitz (h : UnitCubeSkewW2Infinity d) (p : Vec d)
    (x y : Vec d) :
    ‖gradTermARep h p x - gradTermARep h p y‖ ≤
      ((d : ℝ) ^ 2 * h.gradientW1Infinity * vecNorm p) * ‖x - y‖ := by
  classical
  have hw : 0 ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have hB : 0 ≤ ((d : ℝ) ^ 2 * h.gradientW1Infinity * vecNorm p) * ‖x - y‖ := by
    have := vecNorm_nonneg p
    positivity
  rw [pi_norm_le_iff_of_nonneg hB]
  intro i
  have hentry : ∀ j : Fin d,
      |(gradValueRep h j i x - gradValueRep h j i y) * p j| ≤
        ((d : ℝ) * h.gradientW1Infinity * ‖x - y‖) * vecNorm p := by
    intro j
    rw [abs_mul]
    exact mul_le_mul (gradValueRep_lipschitz h j i x y) (abs_apply_le_vecNorm p j)
      (abs_nonneg _)
      (by have := vecNorm_nonneg p; have := norm_nonneg (x - y); positivity)
  calc ‖(gradTermARep h p x - gradTermARep h p y) i‖
      = |∑ j : Fin d, (gradValueRep h j i x - gradValueRep h j i y) * p j| := by
        rw [Real.norm_eq_abs]
        congr 1
        show (∑ j : Fin d, gradValueRep h j i x * p j) -
            ∑ j : Fin d, gradValueRep h j i y * p j = _
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ j : Fin d, |(gradValueRep h j i x - gradValueRep h j i y) * p j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, ((d : ℝ) * h.gradientW1Infinity * ‖x - y‖) * vecNorm p :=
        Finset.sum_le_sum fun j _ => hentry j
    _ = ((d : ℝ) ^ 2 * h.gradientW1Infinity * vecNorm p) * ‖x - y‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ## `L^∞` bounds for the frozen matrix norm field

`matrixNormField`, its measurability chain and its `L²` membership on the
carrier live in `Algsuperdiff.Section24.UnitCubeSkewW2Infinity.ValueL2`, beside
the frozen definition they characterize; only the provider-level `L^∞` and
cube-transport bookkeeping is added here. -/

theorem ae_matrixNormField_le_carrier (h : UnitCubeSkewW2Infinity d) :
    ∀ᵐ x ∂ volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)),
      matrixNormField h x ≤ (d : ℝ) ^ 2 * h.w1Infinity := by
  classical
  have hall : ∀ᵐ x ∂ volumeMeasureOn
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)),
      ∀ i j : Fin d, |h.toLInfSkewMatrixFieldOn.1.1 x i j| ≤ h.w1Infinity := by
    rw [MeasureTheory.ae_all_iff]
    intro i
    rw [MeasureTheory.ae_all_iff]
    intro j
    exact ae_abs_value_le_w1Infinity h i j
  filter_upwards [hall] with x hx
  calc matrixNormField h x
      ≤ matNorm (h.toLInfSkewMatrixFieldOn.1.1 x) := Ch02.matrixNorm_le_matNorm _
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, |h.toLInfSkewMatrixFieldOn.1.1 x i j| :=
        Ch02.matNorm_le_sum_abs_entries _
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, h.w1Infinity := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hx i j
    _ = (d : ℝ) ^ 2 * h.w1Infinity := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem memLp_matrixNormField_top_carrier (h : UnitCubeSkewW2Infinity d) :
    MemLp (matrixNormField h) ∞
      (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) := by
  refine memLp_top_of_bound (aestronglyMeasurable_matrixNormField_carrier h)
    ((d : ℝ) ^ 2 * h.w1Infinity) ?_
  filter_upwards [ae_matrixNormField_le_carrier h,
    (Filter.Eventually.of_forall (matrixNormField_nonneg h))] with x hx hx0
  rw [Real.norm_eq_abs, abs_of_nonneg hx0]
  exact hx

theorem memLp_matrixNormField_cube (h : UnitCubeSkewW2Infinity d) (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) (r : ℝ≥0∞) :
    MemLp (matrixNormField h) r (normalizedCubeMeasure R) :=
  (memLp_normalizedCubeMeasure_of_memLp_cubeDomain (r := ∞) R
    ((memLp_matrixNormField_top_carrier h).mono_measure
      (MeasureTheory.Measure.restrict_mono hsub le_rfl))).mono_exponent le_top

/-! ## The cube-local `L²` value budget -/

/-- **The cube-local `L²` value budget.**  The normalized mean square of `|h|`
on the triadic cube `R`. -/
def valueBudget (h : UnitCubeSkewW2Infinity d) (R : TriadicCube d) : ℝ :=
  cubeAverage R (fun x => matrixNormField h x ^ 2)

theorem valueBudget_nonneg (h : UnitCubeSkewW2Infinity d) (R : TriadicCube d) :
    0 ≤ valueBudget h R := by
  rw [valueBudget, cubeAverage_eq_integral_normalizedCubeMeasure]
  exact integral_nonneg fun x => by positivity

/-- **Cauchy-Schwarz for the value budget.** -/
theorem cubeAverage_matrixNormField_le_sqrt_valueBudget (h : UnitCubeSkewW2Infinity d)
    (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) :
    cubeAverage R (matrixNormField h) ≤ Real.sqrt (valueBudget h R) := by
  have hJensen := sq_cubeAverage_le_cubeAverage_sq_of_memLp R (matrixNormField h)
    (memLp_matrixNormField_cube h R hsub 2)
  have hle : cubeAverage R (matrixNormField h) ^ 2 ≤ valueBudget h R := hJensen
  have habs : |cubeAverage R (matrixNormField h)| ≤ Real.sqrt (valueBudget h R) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hle
  exact (le_abs_self _).trans habs

/-! ## The unit cube: the budget aggregates to the frozen `L²` value norm -/

theorem cubeVolume_originCube_eq_one : cubeVolume (originCube d 0) = (1 : ℝ) := by
  show (cubeScaleFactor (originCube d 0)) ^ d = (1 : ℝ)
  rw [cubeScaleFactor_originCube]
  norm_num

theorem isFiniteMeasure_carrier (d : ℕ) :
    IsFiniteMeasure
      (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) := by
  have h := isFiniteMeasure_volumeMeasureOn_cubeSet (originCube d 0)
  rwa [volumeMeasureOn, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] at h

theorem aestronglyMeasurable_matrixNormField_sq (h : UnitCubeSkewW2Infinity d) :
    AEStronglyMeasurable (fun x => matrixNormField h x ^ 2)
      (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) :=
  (aestronglyMeasurable_matrixNormField_carrier h).pow 2

theorem memLp_matrixNormField_sq_one (h : UnitCubeSkewW2Infinity d) :
    MemLp (fun x => matrixNormField h x ^ 2) 1
      (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) := by
  let := isFiniteMeasure_carrier d
  refine MemLp.of_bound (aestronglyMeasurable_matrixNormField_sq h)
    (((d : ℝ) ^ 2 * h.w1Infinity) ^ 2) ?_
  filter_upwards [ae_matrixNormField_le_carrier h] with x hx
  have hx0 : 0 ≤ matrixNormField h x := matrixNormField_nonneg h x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ hx0 hx 2

theorem integrableOn_matrixNormField_sq (h : UnitCubeSkewW2Infinity d) :
    IntegrableOn (fun x => matrixNormField h x ^ 2) (cubeSet (originCube d 0))
      volume := by
  have hmem := memLp_matrixNormField_sq_one h
  have hint : Integrable (fun x => matrixNormField h x ^ 2)
      (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) :=
    memLp_one_iff_integrable.mp hmem
  show Integrable (fun x => matrixNormField h x ^ 2)
    (volume.restrict (cubeSet (originCube d 0)))
  rwa [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

theorem valueBudget_originCube (h : UnitCubeSkewW2Infinity d) :
    valueBudget h (originCube d 0) = h.valueL2 ^ 2 := by
  rw [valueBudget, cubeAverage, cubeVolume_originCube_eq_one, valueL2_sq_eq_integral,
    inv_one, one_mul]
  show ∫ x, matrixNormField h x ^ 2
      ∂ (volume.restrict (cubeSet (originCube d 0))) = _
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  rfl

/-- **The value budget aggregates to the frozen `L²` value norm.** -/
theorem descendantsAverage_valueBudget (h : UnitCubeSkewW2Infinity d) (n : ℕ) :
    descendantsAverage (originCube d 0) n (valueBudget h) = h.valueL2 ^ 2 := by
  have htower := cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
    (originCube d 0) n (fun x => matrixNormField h x ^ 2)
    (integrableOn_matrixNormField_sq h)
  calc descendantsAverage (originCube d 0) n (valueBudget h)
      = cubeAverage (originCube d 0) (fun x => matrixNormField h x ^ 2) := htower.symm
    _ = h.valueL2 ^ 2 := valueBudget_originCube h

end

end Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional
