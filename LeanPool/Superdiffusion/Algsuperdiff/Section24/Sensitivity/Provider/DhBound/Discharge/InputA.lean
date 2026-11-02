/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.VectorMemLp
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Definitions

/-!
# InputA

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Term A: the positive Besov budget of `x ↦ hᵀ(x) p`

Source: ABK26, the second inequality of `e.sensitivity.basic.split1`:

```
‖h‖_{B^{3/8}_{2,2}(□₀)} ≤ C ( |(h)_{□₀}| + ‖∇h‖_{L^∞(□₀)} ) ≤ C ‖h‖_{W^{1,∞}(□₀)} .
```

This module discharges the two Term-A premises of
`Provider.DhBound.Assembly.Skeleton`:

* `Ch03.ForceBesovRegularity (originCube d 0) (3/8) (fun x => hᵀ(x) p)`;
* `Ch03.scaleNormalizedPositiveBesovVectorNormTwo (originCube d 0) (3/8) … ≤
  termABesovConst d * vecNorm p * h.w1Infinity`.

The route is: each entry of `h` has a `d · w1Infinity`-Lipschitz representative
(`Provider.DhBound.Lipschitz.UnitCube`), so the vector field `hᵀ p` has a
`d² · w1Infinity · |p|`-Lipschitz representative; the positive Besov seminorm of
a Lipschitz vector field is controlled by
`Discharge.VectorPerturbation`, and the mean term by the frozen
`L^∞` half of `w1Infinity`.  All Besov quantities are a.e. insensitive
(`Discharge.BesovCongr`), so the bound transfers back to the actual field.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Section24 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Besov
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## The Lipschitz matrix representative -/

/-- The entrywise Lipschitz representative of the frozen matrix field. -/
def valueRep (h : UnitCubeSkewW2Infinity d) (x : Vec d) : Mat d :=
  fun i j =>
    (exists_lipschitz_ae_eq_cubeSet_unitCubeSkewW2Infinity_value h i j).choose x

theorem valueRep_lipschitz (h : UnitCubeSkewW2Infinity d) (i j : Fin d) (x y : Vec d) :
    |valueRep h x i j - valueRep h y i j| ≤ (d : ℝ) * h.w1Infinity * ‖x - y‖ := by
  simpa [Real.norm_eq_abs] using!
    (exists_lipschitz_ae_eq_cubeSet_unitCubeSkewW2Infinity_value h i j).choose_spec.1 x y

theorem valueRep_ae_eq (h : UnitCubeSkewW2Infinity d) (i j : Fin d) :
    (fun x => valueRep h x i j)
      =ᵐ[normalizedCubeMeasure (originCube d 0)]
      fun x => h.toLInfSkewMatrixFieldOn.1.1 x i j :=
  ae_normalizedCubeMeasure_of_ae_cubeMeasure (originCube d 0)
    (exists_lipschitz_ae_eq_cubeSet_unitCubeSkewW2Infinity_value h i j).choose_spec.2

/-! ## The Term A field and its representative -/

/-- The Term A field `x ↦ hᵀ(x) p`. -/
def termAField (h : UnitCubeSkewW2Infinity d) (p : Vec d) : Vec d → Vec d :=
  fun x => matVecMul (matTranspose (h.toLInfSkewMatrixFieldOn.1.1 x)) p

/-- The Lipschitz representative of the Term A field. -/
def termARep (h : UnitCubeSkewW2Infinity d) (p : Vec d) : Vec d → Vec d :=
  fun x => matVecMul (matTranspose (valueRep h x)) p

theorem termAField_apply (h : UnitCubeSkewW2Infinity d) (p : Vec d) (x : Vec d)
    (i : Fin d) :
    termAField h p x i = ∑ j : Fin d, h.toLInfSkewMatrixFieldOn.1.1 x j i * p j := by
  simp [termAField, matVecMul, matTranspose, Matrix.transpose_apply]

theorem termARep_apply (h : UnitCubeSkewW2Infinity d) (p : Vec d) (x : Vec d)
    (i : Fin d) :
    termARep h p x i = ∑ j : Fin d, valueRep h x j i * p j := by
  simp [termARep, matVecMul, matTranspose, Matrix.transpose_apply]

theorem termARep_ae_eq (h : UnitCubeSkewW2Infinity d) (p : Vec d) :
    termARep h p =ᵐ[normalizedCubeMeasure (originCube d 0)] termAField h p := by
  classical
  have hall : ∀ᵐ x ∂ normalizedCubeMeasure (originCube d 0), ∀ i j : Fin d,
      valueRep h x i j = h.toLInfSkewMatrixFieldOn.1.1 x i j := by
    rw [MeasureTheory.ae_all_iff]
    intro i
    rw [MeasureTheory.ae_all_iff]
    intro j
    exact valueRep_ae_eq h i j
  filter_upwards [hall] with x hx
  funext i
  rw [termARep_apply, termAField_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [hx j i]

/-! ## The Lipschitz constant of the Term A representative -/

theorem abs_apply_le_vecNorm (p : Vec d) (j : Fin d) : |p j| ≤ vecNorm p :=
  le_trans (by simpa [Real.norm_eq_abs] using norm_le_pi_norm p j) (norm_vec_le_vecNorm p)

theorem termARep_lipschitz (h : UnitCubeSkewW2Infinity d) (p : Vec d) (x y : Vec d) :
    ‖termARep h p x - termARep h p y‖ ≤
      ((d : ℝ) ^ 2 * h.w1Infinity * vecNorm p) * ‖x - y‖ := by
  classical
  have hw : 0 ≤ h.w1Infinity := w1Infinity_nonneg h
  have hB : 0 ≤ ((d : ℝ) ^ 2 * h.w1Infinity * vecNorm p) * ‖x - y‖ := by
    have := vecNorm_nonneg p
    positivity
  rw [pi_norm_le_iff_of_nonneg hB]
  intro i
  have hentry : ∀ j : Fin d,
      |(valueRep h x j i - valueRep h y j i) * p j| ≤
        ((d : ℝ) * h.w1Infinity * ‖x - y‖) * vecNorm p := by
    intro j
    rw [abs_mul]
    exact mul_le_mul (valueRep_lipschitz h j i x y) (abs_apply_le_vecNorm p j)
      (abs_nonneg _)
      (by have := vecNorm_nonneg p; have := norm_nonneg (x - y); positivity)
  calc ‖(termARep h p x - termARep h p y) i‖
      = |∑ j : Fin d, (valueRep h x j i - valueRep h y j i) * p j| := by
        rw [Real.norm_eq_abs]
        congr 1
        simp only [Pi.sub_apply, termARep_apply]
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ j : Fin d, |(valueRep h x j i - valueRep h y j i) * p j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, ((d : ℝ) * h.w1Infinity * ‖x - y‖) * vecNorm p :=
        Finset.sum_le_sum fun j _ => hentry j
    _ = ((d : ℝ) ^ 2 * h.w1Infinity * vecNorm p) * ‖x - y‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ## `L^∞` and `L²` membership -/

theorem memLp_value_entry (h : UnitCubeSkewW2Infinity d) (i j : Fin d) (q : ℝ≥0∞) :
    MemLp (fun x => h.toLInfSkewMatrixFieldOn.1.1 x i j) q
      (normalizedCubeMeasure (originCube d 0)) := by
  refine (memLp_normalizedCubeMeasure_of_memLp_frozen_carrier
    (q := ∞) (h.toLInfSkewMatrixFieldOn.1.2 i j)).mono_exponent le_top

theorem memLp_termAField_component (h : UnitCubeSkewW2Infinity d) (p : Vec d)
    (i : Fin d) (q : ℝ≥0∞) :
    MemLp (fun x => termAField h p x i) q (normalizedCubeMeasure (originCube d 0)) := by
  classical
  have : MemLp (fun x => ∑ j : Fin d, h.toLInfSkewMatrixFieldOn.1.1 x j i * p j) q
      (normalizedCubeMeasure (originCube d 0)) :=
    memLp_finsetSum (s := Finset.univ)
      (f := fun j => fun x => h.toLInfSkewMatrixFieldOn.1.1 x j i * p j)
      fun j _ => (memLp_value_entry h j i q).mul_const (p j)
  simpa [termAField_apply] using this

theorem memLp_termAField (h : UnitCubeSkewW2Infinity d) (p : Vec d) (q : ℝ≥0∞) :
    MemLp (termAField h p) q (normalizedCubeMeasure (originCube d 0)) :=
  memLp_vec_of_components fun i => memLp_termAField_component h p i q

theorem memLp_termARep_top (h : UnitCubeSkewW2Infinity d) (p : Vec d) :
    MemLp (termARep h p) ∞ (normalizedCubeMeasure (originCube d 0)) :=
  (memLp_termAField h p ∞).ae_eq (termARep_ae_eq h p).symm

/-! ## The a.e. componentwise bound -/

theorem ae_abs_termAField_le (h : UnitCubeSkewW2Infinity d) (p : Vec d) (i : Fin d) :
    ∀ᵐ x ∂ normalizedCubeMeasure (originCube d 0),
      |termAField h p x i| ≤ (d : ℝ) * h.w1Infinity * vecNorm p := by
  classical
  have hall : ∀ᵐ x ∂ normalizedCubeMeasure (originCube d 0), ∀ i' j' : Fin d,
      |h.toLInfSkewMatrixFieldOn.1.1 x i' j'| ≤ h.w1Infinity := by
    rw [MeasureTheory.ae_all_iff]
    intro i'
    rw [MeasureTheory.ae_all_iff]
    intro j'
    exact ae_normalizedCubeMeasure_of_ae_frozen_carrier
      (ae_abs_value_le_w1Infinity h i' j')
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


/-! ## The Term A Besov budget -/

/-- The explicit Term A Besov constant. -/
def termABesovConst (d : ℕ) : ℝ :=
  Real.sqrt (d : ℝ) * (d : ℝ) + besovPerturbConst (3 / 8) * (d : ℝ) ^ 2

theorem termABesovConst_nonneg (d : ℕ) : 0 ≤ termABesovConst d := by
  have := (besovPerturbConst_pos (s := (3 / 8 : ℝ)) (by norm_num)).le
  unfold termABesovConst
  positivity

theorem cubeBesovPositiveVectorPartialSeminormTwo_termAField_le
    (h : UnitCubeSkewW2Infinity d) (p : Vec d) (N : ℕ) :
    cubeBesovPositiveVectorPartialSeminormTwo (originCube d 0) (3 / 8) N
        (termAField h p) ≤
      besovPerturbConst (3 / 8) * ((d : ℝ) ^ 2 * h.w1Infinity * vecNorm p) := by
  have hB : (0 : ℝ) ≤ (d : ℝ) ^ 2 * h.w1Infinity * vecNorm p := by
    have := w1Infinity_nonneg h
    have := vecNorm_nonneg p
    positivity
  have hrep :=
    cubeBesovPositiveVectorPartialSeminormTwo_le_of_lipschitzOn
      (originCube d 0) (3 / 8) N (ξ := termARep h p)
      (B := (d : ℝ) ^ 2 * h.w1Infinity * vecNorm p) hB (by norm_num)
      (memLp_termARep_top h p)
      (fun x _ y _ => termARep_lipschitz h p x y)
  rw [cubeBesovPositiveVectorPartialSeminormTwo_congr_ae (originCube d 0) (3 / 8) N
    (termARep_ae_eq h p)] at hrep
  simpa using hrep

theorem forceBesovRegularity_termAField (h : UnitCubeSkewW2Infinity d) (p : Vec d) :
    Ch03.ForceBesovRegularity (originCube d 0) (3 / 8)
      (fun x => matVecMul (matTranspose (h.toLInfSkewMatrixFieldOn.1.1 x)) p) where
  memLp := memLp_termAField h p (2 : ℝ≥0∞)
  partialSeminorms_bddAbove := by
    refine ⟨besovPerturbConst (3 / 8) * ((d : ℝ) ^ 2 * h.w1Infinity * vecNorm p), ?_⟩
    rintro _ ⟨N, rfl⟩
    exact cubeBesovPositiveVectorPartialSeminormTwo_termAField_le h p N

theorem scaleNormalizedPositiveBesovVectorNormTwo_termAField_le
    (h : UnitCubeSkewW2Infinity d) (p : Vec d) :
    Ch03.scaleNormalizedPositiveBesovVectorNormTwo (originCube d 0) (3 / 8)
        (fun x => matVecMul (matTranspose (h.toLInfSkewMatrixFieldOn.1.1 x)) p) ≤
      termABesovConst d * vecNorm p * h.w1Infinity := by
  have hw : 0 ≤ h.w1Infinity := w1Infinity_nonneg h
  have hp : 0 ≤ vecNorm p := vecNorm_nonneg p
  have hM : (0 : ℝ) ≤ (d : ℝ) * h.w1Infinity * vecNorm p := by positivity
  have hmean :
      Real.sqrt (vecNormSq (cubeAverageVec (originCube d 0) (termAField h p))) ≤
        Real.sqrt (d : ℝ) * ((d : ℝ) * h.w1Infinity * vecNorm p) :=
    sqrt_vecNormSq_cubeAverageVec_le_of_ae_bound (originCube d 0) hM
      (fun i => memLp_termAField_component h p i (2 : ℝ≥0∞))
      (fun i => ae_abs_termAField_le h p i)
  have hsemi :
      cubeBesovPositiveVectorSeminormTwo (originCube d 0) (3 / 8) (termAField h p) ≤
        besovPerturbConst (3 / 8) * ((d : ℝ) ^ 2 * h.w1Infinity * vecNorm p) :=
    cubeBesovPositiveVectorSeminormTwo_le_of_partialBound (originCube d 0) (3 / 8)
      (termAField h p)
      (fun N => cubeBesovPositiveVectorPartialSeminormTwo_termAField_le h p N)
  have hsum :
      Ch03.scaleNormalizedPositiveBesovVectorNormTwo (originCube d 0) (3 / 8)
          (termAField h p) ≤
        Real.sqrt (d : ℝ) * ((d : ℝ) * h.w1Infinity * vecNorm p) +
          besovPerturbConst (3 / 8) * ((d : ℝ) ^ 2 * h.w1Infinity * vecNorm p) := by
    unfold Ch03.scaleNormalizedPositiveBesovVectorNormTwo
    exact add_le_add hmean hsemi
  refine hsum.trans (le_of_eq ?_)
  unfold termABesovConst
  ring

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge
