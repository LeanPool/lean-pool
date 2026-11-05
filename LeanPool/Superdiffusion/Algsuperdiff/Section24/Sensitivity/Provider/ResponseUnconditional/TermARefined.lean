/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional.ValueLipschitz
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.CubeTermBC

/-!
# TermARefined

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The scale-damped Term A Besov budget on a sub-cube

Source: ABK26, together with its mesoscopic bookkeeping.

`Provider.BigLambda.CubeTermA` prices the positive Besov norm of the Term A
field `hᵀ p` against `‖h‖_{W^{1,∞}(□₀)}`, uniformly in the cube.  That bound is
*too weak* for the unconditional aggregation: the Term A error is aggregated
over `3^{dH}` mesoscopic cubes against the *root* `L²` value norm, and the
undamped `W^{1,∞}` bound loses the whole gain of the mesoscopic depth.

This module proves the sharp replacement

```
‖hᵀ p‖_{B^{3/8}_{2,2}(R)} ≤ C(d) |p| ( ‖h‖_{L²(R)} + |R| ‖∇h‖_{W^{1,∞}(□₀)} ) ,
```

whose two halves are:

* the *mean* half, bounded by the normalized `L¹` average of `|h|` on `R` and
  hence, by Cauchy-Schwarz, by the cube-local `L²` value budget
  `Provider.ResponseUnconditional.valueBudget`;
* the *oscillation* half, bounded by `cubeScaleFactor R` times the Lipschitz
  constant of the gradient-Lipschitz representative of the value field, i.e. by
  `|R| ‖∇h‖_{W^{1,∞}}`.

At a cube of depth `H` below the unit cube `cubeScaleFactor R = 3^{-H}`, so the
second half is damped exactly as the frozen statement requires.

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.BigLambda
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Besov
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz
open Algsuperdiff.Section24.Sensitivity.Provider.Lambda
open Algsuperdiff.Section24.UnitCubeSkewW2Infinity
open scoped BigOperators ENNReal NNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## The pointwise Term A bound by the Euclidean matrix norm -/

theorem abs_termAField_le_matrixNormField (h : UnitCubeSkewW2Infinity d) (p : Vec d)
    (x : Vec d) (i : Fin d) :
    |termAField h p x i| ≤ (d : ℝ) * vecNorm p * matrixNormField h x := by
  classical
  have hentry : ∀ j : Fin d,
      |h.toLInfSkewMatrixFieldOn.1.1 x j i * p j| ≤ matrixNormField h x * vecNorm p := by
    intro j
    rw [abs_mul]
    refine mul_le_mul ?_ (abs_apply_le_vecNorm p j) (abs_nonneg _)
      (matrixNormField_nonneg h x)
    rw [matrixNormField, Ch02.matrixNorm_eq_matrixOperatorNorm]
    exact Ch02.abs_entry_le_matrixOperatorNorm _ j i
  rw [termAField_apply]
  calc |∑ j : Fin d, h.toLInfSkewMatrixFieldOn.1.1 x j i * p j|
      ≤ ∑ j : Fin d, |h.toLInfSkewMatrixFieldOn.1.1 x j i * p j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, matrixNormField h x * vecNorm p :=
        Finset.sum_le_sum fun j _ => hentry j
    _ = (d : ℝ) * vecNorm p * matrixNormField h x := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ## The mean half -/

theorem abs_cubeAverage_termAField_le (h : UnitCubeSkewW2Infinity d)
    (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (p : Vec d) (i : Fin d) :
    |cubeAverage R (fun x => termAField h p x i)| ≤
      (d : ℝ) * vecNorm p * cubeAverage R (matrixNormField h) := by
  classical
  have hintF : Integrable (fun x => termAField h p x i) (normalizedCubeMeasure R) :=
    memLp_one_iff_integrable.mp (memLp_termAField_component_cube h R hsub p i 1)
  have hintG : Integrable (matrixNormField h) (normalizedCubeMeasure R) :=
    memLp_one_iff_integrable.mp (memLp_matrixNormField_cube h R hsub 1)
  have hintGc : Integrable
      (fun x => (d : ℝ) * vecNorm p * matrixNormField h x)
      (normalizedCubeMeasure R) := hintG.const_mul _
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  have hstep : |∫ x, termAField h p x i ∂ normalizedCubeMeasure R| ≤
      ∫ x, |termAField h p x i| ∂ normalizedCubeMeasure R := by
    simpa [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (μ := normalizedCubeMeasure R)
        (f := fun x => termAField h p x i))
  refine hstep.trans ?_
  have hmono : ∫ x, |termAField h p x i| ∂ normalizedCubeMeasure R ≤
      ∫ x, (d : ℝ) * vecNorm p * matrixNormField h x ∂ normalizedCubeMeasure R :=
    integral_mono hintF.abs hintGc
      (fun x => abs_termAField_le_matrixNormField h p x i)
  refine hmono.trans (le_of_eq ?_)
  rw [integral_const_mul]

theorem sqrt_vecNormSq_cubeAverageVec_termAField_le (h : UnitCubeSkewW2Infinity d)
    (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (p : Vec d) :
    Real.sqrt (vecNormSq (cubeAverageVec R (termAField h p))) ≤
      Real.sqrt (d : ℝ) * ((d : ℝ) * vecNorm p * Real.sqrt (valueBudget h R)) := by
  classical
  have hpnn : (0 : ℝ) ≤ vecNorm p := vecNorm_nonneg p
  have hVnn : (0 : ℝ) ≤ Real.sqrt (valueBudget h R) := Real.sqrt_nonneg _
  have hMnn : (0 : ℝ) ≤ (d : ℝ) * vecNorm p * Real.sqrt (valueBudget h R) := by
    positivity
  have hbound : ‖cubeAverageVec R (termAField h p)‖ ≤
      (d : ℝ) * vecNorm p * Real.sqrt (valueBudget h R) := by
    rw [pi_norm_le_iff_of_nonneg hMnn]
    intro i
    have h1 := abs_cubeAverage_termAField_le h R hsub p i
    have h2 := cubeAverage_matrixNormField_le_sqrt_valueBudget h R hsub
    have hcoef : (0 : ℝ) ≤ (d : ℝ) * vecNorm p := by positivity
    have := mul_le_mul_of_nonneg_left h2 hcoef
    calc ‖cubeAverageVec R (termAField h p) i‖
        = |cubeAverage R (fun x => termAField h p x i)| := Real.norm_eq_abs _
      _ ≤ (d : ℝ) * vecNorm p * cubeAverage R (matrixNormField h) := h1
      _ ≤ (d : ℝ) * vecNorm p * Real.sqrt (valueBudget h R) := this
  refine (sqrt_vecNormSq_le_sqrt_card_mul_norm' _).trans ?_
  exact mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg _)

/-! ## The oscillation half -/

theorem memLp_gradTermARep_top_cube (h : UnitCubeSkewW2Infinity d)
    (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (p : Vec d) :
    MemLp (gradTermARep h p) ∞ (normalizedCubeMeasure R) :=
  (memLp_termAField_cube h R hsub p ∞).ae_eq (gradTermARep_ae_eq_cube h p R hsub).symm

/-- **The scale-damped oscillation half.**  The `cubeScaleFactor` is *kept*: it
is the mesoscopic damping factor of the unconditional estimate. -/
theorem cubeBesovPositiveVectorPartialSeminormTwo_termAField_damped_le
    (h : UnitCubeSkewW2Infinity d) (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (p : Vec d) (N : ℕ) :
    cubeBesovPositiveVectorPartialSeminormTwo R (3 / 8) N (termAField h p) ≤
      besovPerturbConst (3 / 8) *
        (cubeScaleFactor R * ((d : ℝ) ^ 2 * h.gradientW1Infinity * vecNorm p)) := by
  have hB : (0 : ℝ) ≤ (d : ℝ) ^ 2 * h.gradientW1Infinity * vecNorm p := by
    have := gradientW1Infinity_nonneg h
    have := vecNorm_nonneg p
    positivity
  have hrep :=
    cubeBesovPositiveVectorPartialSeminormTwo_le_of_lipschitzOn
      R (3 / 8) N (ξ := gradTermARep h p)
      (B := (d : ℝ) ^ 2 * h.gradientW1Infinity * vecNorm p) hB (by norm_num)
      (memLp_gradTermARep_top_cube h R hsub p)
      (fun x _ y _ => gradTermARep_lipschitz h p x y)
  rwa [cubeBesovPositiveVectorPartialSeminormTwo_congr_ae R (3 / 8) N
    (gradTermARep_ae_eq_cube h p R hsub)] at hrep

theorem cubeBesovPositiveVectorSeminormTwo_termAField_damped_le
    (h : UnitCubeSkewW2Infinity d) (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (p : Vec d) :
    cubeBesovPositiveVectorSeminormTwo R (3 / 8) (termAField h p) ≤
      besovPerturbConst (3 / 8) *
        (cubeScaleFactor R * ((d : ℝ) ^ 2 * h.gradientW1Infinity * vecNorm p)) :=
  cubeBesovPositiveVectorSeminormTwo_le_of_partialBound R (3 / 8) (termAField h p)
    (fun N => cubeBesovPositiveVectorPartialSeminormTwo_termAField_damped_le
      h R hsub p N)

/-! ## The refined budget -/

/-- The constant of the scale-damped Term A budget. -/
def termARefinedConst (d : ℕ) : ℝ :=
  Real.sqrt (d : ℝ) * (d : ℝ) + besovPerturbConst (3 / 8) * (d : ℝ) ^ 2

theorem termARefinedConst_nonneg (d : ℕ) : 0 ≤ termARefinedConst d := by
  have h1 : (0 : ℝ) ≤ besovPerturbConst (3 / 8) :=
    (besovPerturbConst_pos (s := (3 / 8 : ℝ)) (by norm_num)).le
  have h2 : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  unfold termARefinedConst
  positivity

/-- **The scale-damped Term A positive Besov budget on a sub-cube.** -/
theorem scaleNormalizedPositiveBesovVectorNormTwo_termAField_refined_le
    (h : UnitCubeSkewW2Infinity d) (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (p : Vec d) :
    Ch03.scaleNormalizedPositiveBesovVectorNormTwo R (3 / 8) (termAField h p) ≤
      termARefinedConst d * vecNorm p *
        (Real.sqrt (valueBudget h R) +
          cubeScaleFactor R * h.gradientW1Infinity) := by
  have hgnn : (0 : ℝ) ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have hpnn : (0 : ℝ) ≤ vecNorm p := vecNorm_nonneg p
  have hVnn : (0 : ℝ) ≤ Real.sqrt (valueBudget h R) := Real.sqrt_nonneg _
  have hLnn : (0 : ℝ) ≤ cubeScaleFactor R := (cubeScaleFactor_pos_cube R).le
  have hbes : (0 : ℝ) ≤ besovPerturbConst (3 / 8) :=
    (besovPerturbConst_pos (s := (3 / 8 : ℝ)) (by norm_num)).le
  have hmean := sqrt_vecNormSq_cubeAverageVec_termAField_le h R hsub p
  have hsemi := cubeBesovPositiveVectorSeminormTwo_termAField_damped_le h R hsub p
  have hsum :
      Ch03.scaleNormalizedPositiveBesovVectorNormTwo R (3 / 8) (termAField h p) ≤
        Real.sqrt (d : ℝ) * ((d : ℝ) * vecNorm p * Real.sqrt (valueBudget h R)) +
          besovPerturbConst (3 / 8) *
            (cubeScaleFactor R *
              ((d : ℝ) ^ 2 * h.gradientW1Infinity * vecNorm p)) := by
    unfold Ch03.scaleNormalizedPositiveBesovVectorNormTwo
    exact add_le_add hmean hsemi
  refine hsum.trans ?_
  have hexpand : termARefinedConst d * vecNorm p *
      (Real.sqrt (valueBudget h R) + cubeScaleFactor R * h.gradientW1Infinity) =
      (Real.sqrt (d : ℝ) * (d : ℝ) * vecNorm p * Real.sqrt (valueBudget h R) +
        besovPerturbConst (3 / 8) * (d : ℝ) ^ 2 * vecNorm p *
          (cubeScaleFactor R * h.gradientW1Infinity)) +
      (Real.sqrt (d : ℝ) * (d : ℝ) * vecNorm p *
          (cubeScaleFactor R * h.gradientW1Infinity) +
        besovPerturbConst (3 / 8) * (d : ℝ) ^ 2 * vecNorm p *
          Real.sqrt (valueBudget h R)) := by
    unfold termARefinedConst
    ring
  rw [hexpand]
  have hcross1 : (0 : ℝ) ≤ Real.sqrt (d : ℝ) * (d : ℝ) * vecNorm p *
      (cubeScaleFactor R * h.gradientW1Infinity) := by positivity
  have hcross2 : (0 : ℝ) ≤ besovPerturbConst (3 / 8) * (d : ℝ) ^ 2 * vecNorm p *
      Real.sqrt (valueBudget h R) := by positivity
  have hA : Real.sqrt (d : ℝ) * ((d : ℝ) * vecNorm p * Real.sqrt (valueBudget h R)) =
      Real.sqrt (d : ℝ) * (d : ℝ) * vecNorm p * Real.sqrt (valueBudget h R) := by ring
  have hB : besovPerturbConst (3 / 8) *
      (cubeScaleFactor R * ((d : ℝ) ^ 2 * h.gradientW1Infinity * vecNorm p)) =
      besovPerturbConst (3 / 8) * (d : ℝ) ^ 2 * vecNorm p *
        (cubeScaleFactor R * h.gradientW1Infinity) := by ring
  rw [hA, hB]
  linarith

end

end Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional
