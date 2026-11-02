/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.CubeFieldData
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.InputA

/-!
# CubeTermA

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Term A of the `D_h` split on a sub-cube of the frozen carrier

Source: ABK26, the second inequality of `e.sensitivity.basic.split1`, stated at
an **arbitrary** triadic sub-cube `R` of the frozen unit cube.

`Provider.DhBound.Discharge.InputA` discharges the same two premises at the root
cube.  The only genuinely cube-dependent step is the positive Besov seminorm of
a Lipschitz vector field, which carries one factor `cubeScaleFactor R`
(`Discharge.cubeBesovPositiveVectorPartialSeminormTwo_le_of_lipschitzOn`, already
stated at a general cube).  Since `cubeScaleFactor R ≤ 1` on descendants of the
unit cube, the *same* constant `Discharge.termABesovConst d` works verbatim:

```
‖hᵀ p‖_{B^{3/8}_{2,2}(R)} ≤ termABesovConst d · |p| · ‖h‖_{W^{1,∞}(□₀)} .
```

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.BigLambda

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Section24 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Besov
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz
open Algsuperdiff.Section24.Sensitivity.Provider.Lambda
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## A globally Lipschitz representative of the value field -/

/-- The entrywise globally Lipschitz representative of the frozen matrix
field. -/
def potValueRep (h : UnitCubeSkewW2Infinity d) (i j : Fin d) : Vec d → ℝ :=
  (exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_value h i j).choose

theorem potValueRep_lipschitz (h : UnitCubeSkewW2Infinity d) (i j : Fin d)
    (x y : Vec d) :
    |potValueRep h i j x - potValueRep h i j y| ≤
      (d : ℝ) * h.w1Infinity * ‖x - y‖ := by
  simpa [Real.norm_eq_abs] using!
    (exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_value h i j).choose_spec.1 x y

theorem potValueRep_ae_eq_carrier (h : UnitCubeSkewW2Infinity d) (i j : Fin d) :
    (fun x => potValueRep h i j x)
      =ᵐ[volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))]
      fun x => h.toLInfSkewMatrixFieldOn.1.1 x i j :=
  (exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_value h i j).choose_spec.2

theorem potValueRep_ae_eq_cube (h : UnitCubeSkewW2Infinity d) (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (i j : Fin d) :
    (fun x => potValueRep h i j x)
      =ᵐ[normalizedCubeMeasure R]
      fun x => h.toLInfSkewMatrixFieldOn.1.1 x i j :=
  ae_normalizedCubeMeasure_of_ae_cubeDomain (P := fun x =>
      potValueRep h i j x = h.toLInfSkewMatrixFieldOn.1.1 x i j) R
    (ae_restrict_of_ae_restrict_of_subset hsub (potValueRep_ae_eq_carrier h i j))

/-! ## The Term A field and its representative on a sub-cube -/

/-- The Lipschitz representative of the Term A field. -/
def potTermARep (h : UnitCubeSkewW2Infinity d) (p : Vec d) : Vec d → Vec d :=
  fun x i => ∑ j : Fin d, potValueRep h j i x * p j

theorem potTermARep_ae_eq_cube (h : UnitCubeSkewW2Infinity d) (p : Vec d)
    (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) :
    potTermARep h p =ᵐ[normalizedCubeMeasure R] termAField h p := by
  classical
  have hall : ∀ᵐ x ∂ normalizedCubeMeasure R, ∀ i j : Fin d,
      potValueRep h i j x = h.toLInfSkewMatrixFieldOn.1.1 x i j := by
    rw [MeasureTheory.ae_all_iff]
    intro i
    rw [MeasureTheory.ae_all_iff]
    intro j
    exact potValueRep_ae_eq_cube h R hsub i j
  filter_upwards [hall] with x hx
  funext i
  rw [termAField_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [hx j i]

theorem potTermARep_lipschitz (h : UnitCubeSkewW2Infinity d) (p : Vec d)
    (x y : Vec d) :
    ‖potTermARep h p x - potTermARep h p y‖ ≤
      ((d : ℝ) ^ 2 * h.w1Infinity * vecNorm p) * ‖x - y‖ := by
  classical
  have hw : 0 ≤ h.w1Infinity := w1Infinity_nonneg h
  have hB : 0 ≤ ((d : ℝ) ^ 2 * h.w1Infinity * vecNorm p) * ‖x - y‖ := by
    have := vecNorm_nonneg p
    positivity
  rw [pi_norm_le_iff_of_nonneg hB]
  intro i
  have hentry : ∀ j : Fin d,
      |(potValueRep h j i x - potValueRep h j i y) * p j| ≤
        ((d : ℝ) * h.w1Infinity * ‖x - y‖) * vecNorm p := by
    intro j
    rw [abs_mul]
    exact mul_le_mul (potValueRep_lipschitz h j i x y) (abs_apply_le_vecNorm p j)
      (abs_nonneg _)
      (by have := vecNorm_nonneg p; have := norm_nonneg (x - y); positivity)
  calc ‖(potTermARep h p x - potTermARep h p y) i‖
      = |∑ j : Fin d, (potValueRep h j i x - potValueRep h j i y) * p j| := by
        rw [Real.norm_eq_abs]
        congr 1
        change (∑ j : Fin d, potValueRep h j i x * p j) -
            ∑ j : Fin d, potValueRep h j i y * p j = _
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ j : Fin d, |(potValueRep h j i x - potValueRep h j i y) * p j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, ((d : ℝ) * h.w1Infinity * ‖x - y‖) * vecNorm p :=
        Finset.sum_le_sum fun j _ => hentry j
    _ = ((d : ℝ) ^ 2 * h.w1Infinity * vecNorm p) * ‖x - y‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ## `L^p` memberships and a.e. bounds on a sub-cube -/

theorem memLp_value_entry_cube (h : UnitCubeSkewW2Infinity d) (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (i j : Fin d) (r : ℝ≥0∞) :
    MemLp (fun x => h.toLInfSkewMatrixFieldOn.1.1 x i j) r
      (normalizedCubeMeasure R) :=
  (memLp_normalizedCubeMeasure_of_memLp_cubeDomain (r := ∞) R
    ((h.toLInfSkewMatrixFieldOn.1.2 i j).mono_measure
      (MeasureTheory.Measure.restrict_mono hsub le_rfl))).mono_exponent le_top

theorem memLp_termAField_component_cube (h : UnitCubeSkewW2Infinity d)
    (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (p : Vec d) (i : Fin d) (r : ℝ≥0∞) :
    MemLp (fun x => termAField h p x i) r (normalizedCubeMeasure R) := by
  classical
  have : MemLp (fun x => ∑ j : Fin d, h.toLInfSkewMatrixFieldOn.1.1 x j i * p j) r
      (normalizedCubeMeasure R) :=
    memLp_finsetSum (s := Finset.univ)
      (f := fun j => fun x => h.toLInfSkewMatrixFieldOn.1.1 x j i * p j)
      fun j _ => (memLp_value_entry_cube h R hsub j i r).mul_const (p j)
  simpa [termAField_apply] using this

theorem memLp_termAField_cube (h : UnitCubeSkewW2Infinity d) (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (p : Vec d) (r : ℝ≥0∞) :
    MemLp (termAField h p) r (normalizedCubeMeasure R) :=
  memLp_vec_of_components fun i => memLp_termAField_component_cube h R hsub p i r

theorem memLp_potTermARep_top_cube (h : UnitCubeSkewW2Infinity d)
    (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (p : Vec d) :
    MemLp (potTermARep h p) ∞ (normalizedCubeMeasure R) :=
  (memLp_termAField_cube h R hsub p ∞).ae_eq (potTermARep_ae_eq_cube h p R hsub).symm

theorem ae_abs_termAField_le_cube (h : UnitCubeSkewW2Infinity d)
    (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (p : Vec d) (i : Fin d) :
    ∀ᵐ x ∂ normalizedCubeMeasure R,
      |termAField h p x i| ≤ (d : ℝ) * h.w1Infinity * vecNorm p := by
  classical
  have hall : ∀ᵐ x ∂ volumeMeasureOn ((cubeDomain R : Domain d) : Set (Vec d)),
      ∀ i' j' : Fin d, |h.toLInfSkewMatrixFieldOn.1.1 x i' j'| ≤ h.w1Infinity := by
    rw [MeasureTheory.ae_all_iff]
    intro i'
    rw [MeasureTheory.ae_all_iff]
    intro j'
    exact ae_restrict_of_ae_restrict_of_subset hsub (ae_abs_value_le_w1Infinity h i' j')
  refine ae_normalizedCubeMeasure_of_ae_cubeDomain R ?_
  filter_upwards [hall] with x hx
  rw [termAField_apply]
  calc |∑ j : Fin d, h.toLInfSkewMatrixFieldOn.1.1 x j i * p j|
      ≤ ∑ j : Fin d, |h.toLInfSkewMatrixFieldOn.1.1 x j i * p j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, h.w1Infinity * vecNorm p := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hx j i) (abs_apply_le_vecNorm p j) (abs_nonneg _)
          (w1Infinity_nonneg h)
    _ = (d : ℝ) * h.w1Infinity * vecNorm p := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ## The Term A Besov budget on a sub-cube -/

theorem cubeBesovPositiveVectorPartialSeminormTwo_termAField_cube_le
    (h : UnitCubeSkewW2Infinity d) (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (hL : cubeScaleFactor R ≤ 1) (p : Vec d) (N : ℕ) :
    cubeBesovPositiveVectorPartialSeminormTwo R (3 / 8) N (termAField h p) ≤
      besovPerturbConst (3 / 8) * ((d : ℝ) ^ 2 * h.w1Infinity * vecNorm p) := by
  have hB : (0 : ℝ) ≤ (d : ℝ) ^ 2 * h.w1Infinity * vecNorm p := by
    have := w1Infinity_nonneg h
    have := vecNorm_nonneg p
    positivity
  have hrep :=
    cubeBesovPositiveVectorPartialSeminormTwo_le_of_lipschitzOn
      R (3 / 8) N (ξ := potTermARep h p)
      (B := (d : ℝ) ^ 2 * h.w1Infinity * vecNorm p) hB (by norm_num)
      (memLp_potTermARep_top_cube h R hsub p)
      (fun x _ y _ => potTermARep_lipschitz h p x y)
  rw [cubeBesovPositiveVectorPartialSeminormTwo_congr_ae R (3 / 8) N
    (potTermARep_ae_eq_cube h p R hsub)] at hrep
  refine hrep.trans ?_
  have hmult : (0 : ℝ) ≤ besovPerturbConst (3 / 8) :=
    (besovPerturbConst_pos (s := (3 / 8 : ℝ)) (by norm_num)).le
  refine mul_le_mul_of_nonneg_left ?_ hmult
  calc cubeScaleFactor R * ((d : ℝ) ^ 2 * h.w1Infinity * vecNorm p)
      ≤ 1 * ((d : ℝ) ^ 2 * h.w1Infinity * vecNorm p) :=
        mul_le_mul_of_nonneg_right hL hB
    _ = (d : ℝ) ^ 2 * h.w1Infinity * vecNorm p := one_mul _

theorem forceBesovRegularity_termAField_cube (h : UnitCubeSkewW2Infinity d)
    (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (hL : cubeScaleFactor R ≤ 1) (p : Vec d) :
    Ch03.ForceBesovRegularity R (3 / 8)
      (fun x => matVecMul (matTranspose (h.toLInfSkewMatrixFieldOn.1.1 x)) p) where
  memLp := memLp_termAField_cube h R hsub p (2 : ℝ≥0∞)
  partialSeminorms_bddAbove := by
    refine ⟨besovPerturbConst (3 / 8) * ((d : ℝ) ^ 2 * h.w1Infinity * vecNorm p), ?_⟩
    rintro _ ⟨N, rfl⟩
    exact cubeBesovPositiveVectorPartialSeminormTwo_termAField_cube_le h R hsub hL p N

/-- **The Term A positive Besov budget on a sub-cube of the frozen carrier.** -/
theorem scaleNormalizedPositiveBesovVectorNormTwo_termAField_cube_le
    (h : UnitCubeSkewW2Infinity d) (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (hL : cubeScaleFactor R ≤ 1) (p : Vec d) :
    Ch03.scaleNormalizedPositiveBesovVectorNormTwo R (3 / 8)
        (fun x => matVecMul (matTranspose (h.toLInfSkewMatrixFieldOn.1.1 x)) p) ≤
      termABesovConst d * vecNorm p * h.w1Infinity := by
  have hw : 0 ≤ h.w1Infinity := w1Infinity_nonneg h
  have hp : 0 ≤ vecNorm p := vecNorm_nonneg p
  have hM : (0 : ℝ) ≤ (d : ℝ) * h.w1Infinity * vecNorm p := by positivity
  have hmean :
      Real.sqrt (vecNormSq (cubeAverageVec R (termAField h p))) ≤
        Real.sqrt (d : ℝ) * ((d : ℝ) * h.w1Infinity * vecNorm p) :=
    sqrt_vecNormSq_cubeAverageVec_le_of_ae_bound R hM
      (fun i => memLp_termAField_component_cube h R hsub p i (2 : ℝ≥0∞))
      (fun i => ae_abs_termAField_le_cube h R hsub p i)
  have hsemi :
      cubeBesovPositiveVectorSeminormTwo R (3 / 8) (termAField h p) ≤
        besovPerturbConst (3 / 8) * ((d : ℝ) ^ 2 * h.w1Infinity * vecNorm p) :=
    cubeBesovPositiveVectorSeminormTwo_le_of_partialBound R (3 / 8)
      (termAField h p)
      (fun N => cubeBesovPositiveVectorPartialSeminormTwo_termAField_cube_le
        h R hsub hL p N)
  have hsum :
      Ch03.scaleNormalizedPositiveBesovVectorNormTwo R (3 / 8) (termAField h p) ≤
        Real.sqrt (d : ℝ) * ((d : ℝ) * h.w1Infinity * vecNorm p) +
          besovPerturbConst (3 / 8) * ((d : ℝ) ^ 2 * h.w1Infinity * vecNorm p) := by
    unfold Ch03.scaleNormalizedPositiveBesovVectorNormTwo
    exact add_le_add hmean hsemi
  refine hsum.trans (le_of_eq ?_)
  unfold termABesovConst
  ring

end

end Algsuperdiff.Section24.Sensitivity.Provider.BigLambda
