/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationMuMeasCell

/-!
# LocalizationFluctuationJointCoeff

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Joint `(omega, x)` measurability of the cutoff's doubled energy density

ABK26, `l.approximate.recurrence.formula`, Step 2, read at the recurrence pair
`(n, n+h)`.

## The obligation this module discharges

`LocalizationFluctuationMuMeasCore.stronglyMeasurable_doubledMuValue_of_jointly`
reduces sample-measurability of a doubled energy value to **joint** `(omega, x)`
strong measurability of the integrand

```
  (omega, x) |->  blockEnergyDensityAt (a omega) (Z x) x .
```

At the Step-2 carriers the coefficient is
`meshCellCoeff M m R omega = (coefficientCutoffTriadicCoeffFamily M m omega).coeffOn R`,
so the sample enters the *coefficient* leg.  This module supplies that leg, for
an arbitrary (sample-independent) block field `Z`.  The companion module
`LocalizationFluctuationJointField` then removes the sample-independence of `Z`.

## Method

Three proved facts about the genuine cutoff do all the work.

1. **Caratheodory.**  `Cutoff.continuous_cutoff_entry` (continuity in the point)
   and `Cutoff.measurable_cutoff_apply_entry` (measurability in the sample) give
   joint measurability of every entry of `k_m` by
   `measurable_uncurry_of_continuous_of_measurable`.  The corresponding
   uncurried statement inside `Cutoff.Limit` is `private`, so it is reproved
   here from the two public halves; no new mathematical content is introduced.

2. **The symmetric part is deterministic.**  `Cutoff.symmPart_coefficientCutoff`
   says `symm(a_m(omega, x)) = nu I` *identically*.  Hence the matrix inverse
   `(symm a)^{-1}` occurring in `Book.Ch02.blockMatrixField` is a **constant**
   matrix: no measurability of matrix inversion is needed anywhere below.

3. **The skew part is the cutoff.**  `skewPart_coefficientCutoff` (proved here
   from `Cutoff.cutoff_skew`) identifies `skew(a_m(omega, x)) = k_m(omega, x)`,
   whose entries are jointly measurable by 1.

Every entry of `blockMatrixField` is therefore a polynomial expression in
jointly measurable entries and constants, and the doubled energy density is a
finite sum of products of those entries with the components of `Z`.

## Main results

* `measurable_uncurry_cutoff_entry` --- the joint measurability of the cutoff
  entries in the sample and the point.
* `skewPart_coefficientCutoff`, `symmPart_meshCellCoeff` --- the two pointwise
  identities that make the block matrix field polynomial.
* `measurable_uncurry_blockMatrixField_meshCellCoeff_{upperLeft, upperRight,
  lowerLeft, lowerRight}` --- the four entry families.
* `measurable_uncurry_blockEnergyDensityAt_meshCellCoeff` --- the joint
  measurability the reduction asks for, at a fixed block field.
* `measurable_doubledMuValue_meshCellCoeff` --- its consequence: at a **fixed**
  doubled field with measurable components, the doubled energy value is a
  measurable function of the sample.

## Binders

Beyond the typing binders, only measurability of the two components of the fixed
field.  No integrability, no ellipticity, no smallness and no proposition about
the corrector or the sample law occurs.  Nothing here estimates anything.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula`, Step 2, `e.variational.mu.U.P`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The two pointwise identities of the genuine cutoff -/

/-- **The skew part of the coefficient cutoff is the cutoff itself.**  The
representative is `a_m = nu I + k_m` with `k_m` skew, so the symmetric part is
`nu I` (proved as `Cutoff.symmPart_coefficientCutoff`) and the skew part is
`k_m`.  Unconditional. -/
theorem skewPart_coefficientCutoff (nu : ℝ) (m : ℤ) (omega : CutoffSample d) (x : Vec d) :
    skewPart (coefficientCutoff nu m omega x) = cutoff m omega x := by
  have hskew := cutoff_skew m omega x
  ext i j
  have hentry : cutoff m omega x j i = -cutoff m omega x i j := by
    have := congrFun (congrFun hskew i) j
    simpa using this
  simp only [skewPart, coefficientCutoff_apply, Matrix.add_apply, Matrix.smul_apply]
  rw [hentry]
  by_cases hij : i = j
  · subst hij; simp
  · have h1 : (1 : Mat d) i j = 0 := by simp [hij]
    have h2 : (1 : Mat d) j i = 0 := by simp [Ne.symm hij]
    rw [h1, h2]
    simp

/-- The symmetric part of the cell coefficient is the deterministic `nu I`. -/
theorem symmPart_meshCellCoeff (M : ABKModel d) (m : ℤ) (R : TriadicCube d)
    (omega : CutoffSample d) (x : Vec d) :
    symmPart ((meshCellCoeff M m R omega).toCoeffField x) = M.nu • (1 : Mat d) :=
  symmPart_coefficientCutoff M.nu m omega x

/-- The skew part of the cell coefficient is the cutoff. -/
theorem skewPart_meshCellCoeff (M : ABKModel d) (m : ℤ) (R : TriadicCube d)
    (omega : CutoffSample d) (x : Vec d) :
    skewPart ((meshCellCoeff M m R omega).toCoeffField x) = cutoff m omega x :=
  skewPart_coefficientCutoff M.nu m omega x

/-! ## Joint measurability of the cutoff entries -/

/-- **Joint `(omega, x)` measurability of the genuine cutoff's entries.**
Caratheodory: continuous in the point, measurable in the sample.  The
corresponding statement inside `Cutoff.Limit` is `private`; this is the public
form, reproved from the two public halves. -/
theorem measurable_uncurry_cutoff_entry (m : ℤ) (i j : Fin d) :
    Measurable (fun p : CutoffSample d × Vec d => cutoff m p.1 p.2 i j) :=
  (measurable_uncurry_of_continuous_of_measurable
    (fun omega => continuous_cutoff_entry m omega i j)
    (fun x => measurable_cutoff_apply_entry m x i j)).comp measurable_swap

/-- Entrywise measurability of a product of two entrywise-measurable matrix
families.  Elementary. -/
theorem measurable_matMul_entry {alpha : Type*} [MeasurableSpace alpha] {A B : alpha → Mat d}
    (hA : ∀ i j, Measurable fun w => A w i j) (hB : ∀ i j, Measurable fun w => B w i j)
    (i j : Fin d) : Measurable fun w => (A w * B w) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => (hA i k).mul (hB k j)

/-! ## Joint measurability of the doubled block matrix field -/

section BlockField

variable (M : ABKModel d) (m : ℤ) (R : TriadicCube d)

/-- The skew leg of the cell coefficient, jointly measurable. -/
theorem measurable_uncurry_skewPart_meshCellCoeff (i j : Fin d) :
    Measurable fun p : CutoffSample d × Vec d =>
      skewPart ((meshCellCoeff M m R p.1).toCoeffField p.2) i j := by
  have hrw : (fun p : CutoffSample d × Vec d =>
      skewPart ((meshCellCoeff M m R p.1).toCoeffField p.2) i j)
      = fun p : CutoffSample d × Vec d => cutoff m p.1 p.2 i j := by
    funext p
    exact congrFun (congrFun (skewPart_meshCellCoeff M m R p.1 p.2) i) j
  rw [hrw]
  exact measurable_uncurry_cutoff_entry m i j

/-- The transposed skew leg, jointly measurable. -/
theorem measurable_uncurry_matTranspose_skewPart_meshCellCoeff (i j : Fin d) :
    Measurable fun p : CutoffSample d × Vec d =>
      matTranspose (skewPart ((meshCellCoeff M m R p.1).toCoeffField p.2)) i j :=
  measurable_uncurry_skewPart_meshCellCoeff M m R j i

/-- The product `k^t (nu I)^{-1}`, entrywise jointly measurable. -/
theorem measurable_uncurry_skewT_mul_invSymm_meshCellCoeff (i j : Fin d) :
    Measurable fun p : CutoffSample d × Vec d =>
      (matTranspose (skewPart ((meshCellCoeff M m R p.1).toCoeffField p.2))
        * (M.nu • (1 : Mat d))⁻¹) i j :=
  measurable_matMul_entry
    (A := fun p : CutoffSample d × Vec d =>
      matTranspose (skewPart ((meshCellCoeff M m R p.1).toCoeffField p.2)))
    (B := fun _ : CutoffSample d × Vec d => (M.nu • (1 : Mat d))⁻¹)
    (measurable_uncurry_matTranspose_skewPart_meshCellCoeff M m R)
    (fun _ _ => measurable_const) i j

/-- The product `(nu I)^{-1} k`, entrywise jointly measurable. -/
theorem measurable_uncurry_invSymm_mul_skew_meshCellCoeff (i j : Fin d) :
    Measurable fun p : CutoffSample d × Vec d =>
      ((M.nu • (1 : Mat d))⁻¹
        * skewPart ((meshCellCoeff M m R p.1).toCoeffField p.2)) i j :=
  measurable_matMul_entry
    (A := fun _ : CutoffSample d × Vec d => (M.nu • (1 : Mat d))⁻¹)
    (B := fun p : CutoffSample d × Vec d =>
      skewPart ((meshCellCoeff M m R p.1).toCoeffField p.2))
    (fun _ _ => measurable_const)
    (measurable_uncurry_skewPart_meshCellCoeff M m R) i j

/-- The `(1,1)` block of `bfA_m` is jointly measurable. -/
theorem measurable_uncurry_blockMatrixField_meshCellCoeff_upperLeft (i j : Fin d) :
    Measurable fun p : CutoffSample d × Vec d =>
      (blockMatrixField (meshCellCoeff M m R p.1) p.2).upperLeft i j := by
  have hrw : (fun p : CutoffSample d × Vec d =>
      (blockMatrixField (meshCellCoeff M m R p.1) p.2).upperLeft i j)
      = fun p : CutoffSample d × Vec d =>
        (M.nu • (1 : Mat d)) i j
          + (matTranspose (skewPart ((meshCellCoeff M m R p.1).toCoeffField p.2))
              * (M.nu • (1 : Mat d))⁻¹
              * skewPart ((meshCellCoeff M m R p.1).toCoeffField p.2)) i j := by
    funext p
    simp only [blockMatrixField, Matrix.add_apply, symmPart_meshCellCoeff M m R p.1 p.2]
  rw [hrw]
  refine measurable_const.add ?_
  exact measurable_matMul_entry
    (A := fun p : CutoffSample d × Vec d =>
      matTranspose (skewPart ((meshCellCoeff M m R p.1).toCoeffField p.2))
        * (M.nu • (1 : Mat d))⁻¹)
    (B := fun p : CutoffSample d × Vec d =>
      skewPart ((meshCellCoeff M m R p.1).toCoeffField p.2))
    (measurable_uncurry_skewT_mul_invSymm_meshCellCoeff M m R)
    (measurable_uncurry_skewPart_meshCellCoeff M m R) i j

/-- The `(1,2)` block of `bfA_m` is jointly measurable. -/
theorem measurable_uncurry_blockMatrixField_meshCellCoeff_upperRight (i j : Fin d) :
    Measurable fun p : CutoffSample d × Vec d =>
      (blockMatrixField (meshCellCoeff M m R p.1) p.2).upperRight i j := by
  have hrw : (fun p : CutoffSample d × Vec d =>
      (blockMatrixField (meshCellCoeff M m R p.1) p.2).upperRight i j)
      = fun p : CutoffSample d × Vec d =>
        -((matTranspose (skewPart ((meshCellCoeff M m R p.1).toCoeffField p.2))
              * (M.nu • (1 : Mat d))⁻¹) i j) := by
    funext p
    simp only [blockMatrixField, Matrix.neg_apply, symmPart_meshCellCoeff M m R p.1 p.2]
  rw [hrw]
  exact (measurable_uncurry_skewT_mul_invSymm_meshCellCoeff M m R i j).neg

/-- The `(2,1)` block of `bfA_m` is jointly measurable. -/
theorem measurable_uncurry_blockMatrixField_meshCellCoeff_lowerLeft (i j : Fin d) :
    Measurable fun p : CutoffSample d × Vec d =>
      (blockMatrixField (meshCellCoeff M m R p.1) p.2).lowerLeft i j := by
  have hrw : (fun p : CutoffSample d × Vec d =>
      (blockMatrixField (meshCellCoeff M m R p.1) p.2).lowerLeft i j)
      = fun p : CutoffSample d × Vec d =>
        -(((M.nu • (1 : Mat d))⁻¹
            * skewPart ((meshCellCoeff M m R p.1).toCoeffField p.2)) i j) := by
    funext p
    simp only [blockMatrixField, Matrix.neg_apply, symmPart_meshCellCoeff M m R p.1 p.2]
  rw [hrw]
  exact (measurable_uncurry_invSymm_mul_skew_meshCellCoeff M m R i j).neg

/-- The `(2,2)` block of `bfA_m` is deterministic, hence jointly measurable. -/
theorem measurable_uncurry_blockMatrixField_meshCellCoeff_lowerRight (i j : Fin d) :
    Measurable fun p : CutoffSample d × Vec d =>
      (blockMatrixField (meshCellCoeff M m R p.1) p.2).lowerRight i j := by
  have hrw : (fun p : CutoffSample d × Vec d =>
      (blockMatrixField (meshCellCoeff M m R p.1) p.2).lowerRight i j)
      = fun _ : CutoffSample d × Vec d => ((M.nu • (1 : Mat d))⁻¹) i j := by
    funext p
    simp only [blockMatrixField, symmPart_meshCellCoeff M m R p.1 p.2]
  rw [hrw]
  exact measurable_const

end BlockField

/-! ## The joint measurability of the doubled energy density -/

/-- **The doubled energy density of the cutoff, at a fixed block field, is
jointly measurable in `(omega, x)`.**

This is the hypothesis `hjoint` of
`LocalizationFluctuationMuMeasCore.stronglyMeasurable_doubledMuValue_of_jointly`
whenever the competitor field does not depend on the sample.

only on measurability of the two components of `Z`. -/
theorem measurable_uncurry_blockEnergyDensityAt_meshCellCoeff (M : ABKModel d) (m : ℤ)
    (R : TriadicCube d) {Z : Vec d → BlockVec d}
    (hZ1 : ∀ i : Fin d, Measurable fun x : Vec d => (Z x).1 i)
    (hZ2 : ∀ i : Fin d, Measurable fun x : Vec d => (Z x).2 i) :
    Measurable fun p : CutoffSample d × Vec d =>
      blockEnergyDensityAt (meshCellCoeff M m R p.1) (Z p.2) p.2 := by
  have hZ1' : ∀ i : Fin d, Measurable fun p : CutoffSample d × Vec d => (Z p.2).1 i :=
    fun i => (hZ1 i).comp measurable_snd
  have hZ2' : ∀ i : Fin d, Measurable fun p : CutoffSample d × Vec d => (Z p.2).2 i :=
    fun i => (hZ2 i).comp measurable_snd
  have hrw : (fun p : CutoffSample d × Vec d =>
      blockEnergyDensityAt (meshCellCoeff M m R p.1) (Z p.2) p.2)
      = fun p : CutoffSample d × Vec d => (1 / 2 : ℝ) *
        ((∑ i, (Z p.2).1 i *
            (∑ j, (blockMatrixField (meshCellCoeff M m R p.1) p.2).upperLeft i j * (Z p.2).1 j
              + ∑ j, (blockMatrixField (meshCellCoeff M m R p.1) p.2).upperRight i j
                  * (Z p.2).2 j))
          + ∑ i, (Z p.2).2 i *
            (∑ j, (blockMatrixField (meshCellCoeff M m R p.1) p.2).lowerLeft i j * (Z p.2).1 j
              + ∑ j, (blockMatrixField (meshCellCoeff M m R p.1) p.2).lowerRight i j
                  * (Z p.2).2 j)) := by
    funext p
    simp only [blockEnergyDensityAt, blockVecDot, blockMatVecMul, vecDot, matVecMul,
      Pi.add_apply]
  rw [hrw]
  refine measurable_const.mul (Measurable.add ?_ ?_)
  · refine Finset.measurable_sum _ fun i _ => (hZ1' i).mul (Measurable.add ?_ ?_)
    · exact Finset.measurable_sum _ fun j _ =>
        (measurable_uncurry_blockMatrixField_meshCellCoeff_upperLeft M m R i j).mul (hZ1' j)
    · exact Finset.measurable_sum _ fun j _ =>
        (measurable_uncurry_blockMatrixField_meshCellCoeff_upperRight M m R i j).mul (hZ2' j)
  · refine Finset.measurable_sum _ fun i _ => (hZ2' i).mul (Measurable.add ?_ ?_)
    · exact Finset.measurable_sum _ fun j _ =>
        (measurable_uncurry_blockMatrixField_meshCellCoeff_lowerLeft M m R i j).mul (hZ1' j)
    · exact Finset.measurable_sum _ fun j _ =>
        (measurable_uncurry_blockMatrixField_meshCellCoeff_lowerRight M m R i j).mul (hZ2' j)

/-- **The fixed-competitor sample measurability of the doubled energy value.**

For a doubled field with measurable components the energy value on the cell is a
measurable function of the sample.  This is the shape the field-slope
countable-infimum reduction of `LocalizationFluctuationMuMeasCore` consumes once
the competitor has been made sample-independent.

only on measurability of the two components of `W`. -/
theorem measurable_doubledMuValue_meshCellCoeff (M : ABKModel d) (m : ℤ) (R : TriadicCube d)
    (W : DoubledField d) (hpot : Measurable W.potential) (hflux : Measurable W.flux) :
    Measurable fun omega : CutoffSample d =>
      doubledMuValue (cubeDomain R) (meshCellCoeff M m R omega) W := by
  have hjoint : StronglyMeasurable fun p : CutoffSample d × Vec d =>
      blockEnergyDensityAt (meshCellCoeff M m R p.1) (W.eval p.2) p.2 :=
    (measurable_uncurry_blockEnergyDensityAt_meshCellCoeff M m R
      (fun i => (measurable_pi_apply i).comp hpot)
      (fun i => (measurable_pi_apply i).comp hflux)).stronglyMeasurable
  have h : StronglyMeasurable fun omega : CutoffSample d =>
      ∫ x, blockEnergyDensityAt (meshCellCoeff M m R omega) (W.eval x) x
        ∂(volume.restrict ((cubeDomain R : Domain d) : Set (Vec d))) :=
    hjoint.integral_prod_right'
  have hrw : (fun omega : CutoffSample d =>
      doubledMuValue (cubeDomain R) (meshCellCoeff M m R omega) W)
      = fun omega : CutoffSample d =>
        (volume ((cubeDomain R : Domain d) : Set (Vec d))).toReal⁻¹ *
          ∫ x, blockEnergyDensityAt (meshCellCoeff M m R omega) (W.eval x) x
            ∂(volume.restrict ((cubeDomain R : Domain d) : Set (Vec d))) := rfl
  rw [hrw]
  exact (stronglyMeasurable_const.mul h).measurable

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
