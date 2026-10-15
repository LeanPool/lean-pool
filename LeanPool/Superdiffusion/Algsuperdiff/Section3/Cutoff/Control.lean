/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Finite
public import LeanPool.Superdiffusion.Algsuperdiff.Assumptions.ShellField.Actions
public import LeanPool.Superdiffusion.Algsuperdiff.Assumptions.ShellField.J2Observable
public import LeanPool.HighContrastHomogenization.Support.Geometry.TriadicCubeTranslation
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Control

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Deterministic local control for the lower shell tail

This file contains only the deterministic, countable good-event layer for the
lower shell tail.  It does not define an infinite cutoff or assert that the
good event has full probability.
-/

open scoped BigOperators Pointwise Matrix.Norms.Elementwise

namespace Algsuperdiff.Section3.Cutoff

open Set
open HCPolySupport
open HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-- A nonnegative control of a shell on the origin-centered cube at scale
`ell`.  It is the exact unit-cube value norm after the corresponding spatial
rescaling; the source `C²` shell carrier makes this finite and Borel
measurable. -/
def localCubeControl (ell : ℤ) (j : ShellField d) : ℝ :=
  ShellField.unitCubeValueNorm
    (ShellField.spatialScale (cubeScaleFactor (originCube d ell)) j)

theorem localCubeControl_nonneg (ell : ℤ) (j : ShellField d) :
    0 ≤ localCubeControl ell j :=
  ShellField.unitCubeValueNorm_nonneg _

theorem measurable_localCubeControl (ell : ℤ) :
    Measurable (localCubeControl (d := d) ell) := by
  exact ShellField.unitCubeValueNorm_measurable.comp
    (ShellField.measurable_spatialScale _)

/-- The local control bounds the operator norm at every point of its open cube. -/
theorem matrixOperatorNorm_le_localCubeControl
    (ell : ℤ) (j : ShellField d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d ell)) :
    HCPolySupport.Book.Ch02.matrixOperatorNorm (j x) ≤ localCubeControl ell j := by
  let r : ℝ := cubeScaleFactor (originCube d ell)
  have hr_pos : 0 < r := by
    simpa [r, cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) ell)
  have hx_scaled : r⁻¹ • x ∈ openCubeSet (originCube d 0) := by
    have hx' : x ∈ cubeScaleFactor (originCube d ell) •
        openCubeSet (originCube d 0) := by
      rw [← openCubeSet_originCube_eq_smul_originCube_zero (d := d) ell]
      exact hx
    change x ∈ r • openCubeSet (originCube d 0) at hx'
    rw [Set.mem_smul_set] at hx'
    obtain ⟨y, hy, hxy⟩ := hx'
    rw [← hxy, smul_smul, inv_mul_cancel₀ (ne_of_gt hr_pos), one_smul]
    exact hy
  let y : ShellField.UnitOpenCubePoint d := ⟨r⁻¹ • x, hx_scaled⟩
  calc
    HCPolySupport.Book.Ch02.matrixOperatorNorm (j x) =
        HCPolySupport.Book.Ch02.matrixOperatorNorm
          ((ShellField.spatialScale r j) y.1) := by
      rw [ShellField.spatialScale_apply]
      congr 2
      dsimp [y]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr_pos), one_smul]
    _ ≤ ShellField.unitCubeValueNorm (ShellField.spatialScale r j) :=
      ShellField.matrixOperatorNorm_apply_le_unitCubeValueNorm _ y
    _ = localCubeControl ell j := rfl

/-- A nonnegative pointwise bound controls the exact local supremum. -/
theorem localCubeControl_le_of_pointwise
    (ell : ℤ) (j : ShellField d) (C : ℝ)
    (hC : ∀ x ∈ openCubeSet (originCube d ell),
      HCPolySupport.Book.Ch02.matrixOperatorNorm (j x) ≤ C)
    (hC_nonneg : 0 ≤ C) :
    localCubeControl ell j ≤ C := by
  unfold localCubeControl ShellField.unitCubeValueNorm
  apply csSup_le
  · exact ⟨0, none, rfl⟩
  rintro _ ⟨o, rfl⟩
  cases o with
  | none => exact hC_nonneg
  | some x =>
      let r : ℝ := cubeScaleFactor (originCube d ell)
      have hx : r • x.1 ∈ openCubeSet (originCube d ell) := by
        rw [openCubeSet_originCube_eq_smul_originCube_zero, Set.mem_smul_set]
        exact ⟨x.1, x.2, rfl⟩
      change HCPolySupport.Book.Ch02.matrixOperatorNorm
          ((ShellField.spatialScale r j) x.1) ≤ C
      rw [ShellField.spatialScale_apply]
      exact hC _ hx

/-- The local control bounds every matrix entry on its corresponding open
origin cube. -/
theorem abs_entry_le_localCubeControl (ell : ℤ) (j : ShellField d)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d ell)) (i k : Fin d) :
    |j x i k| ≤ localCubeControl ell j :=
  (abs_entry_le_matrixOperatorNorm _ _ _).trans
    (matrixOperatorNorm_le_localCubeControl ell j hx)

/-- The finite partial sum of descending-shell local controls. -/
def lowerTailPartialSum (ell m : ℤ) (q : ℕ) (omega : ShellSeq d) : ℝ :=
  ∑ r ∈ Finset.range q, localCubeControl ell (omega (m - r))

theorem measurable_lowerTailPartialSum (ell m : ℤ) (q : ℕ) :
    Measurable (lowerTailPartialSum (d := d) ell m q) := by
  unfold lowerTailPartialSum
  apply Finset.measurable_sum
  intro r hr
  exact (measurable_localCubeControl ell).comp (measurable_pi_apply _)

/-- Bounded nonnegative partial sums, the countable formulation of descending
shell summability used in the lower-tail good event. -/
def LowerTailBounded (ell m : ℤ) (omega : ShellSeq d) : Prop :=
  ∃ C : ℕ, ∀ q : ℕ, lowerTailPartialSum ell m q omega ≤ C

theorem lowerTailBounded_summable {ell m : ℤ} {omega : ShellSeq d}
    (h : LowerTailBounded ell m omega) :
    Summable (fun r : ℕ => localCubeControl ell (omega (m - r))) := by
  obtain ⟨C, hC⟩ := h
  apply summable_of_sum_range_le
  · intro r
    exact localCubeControl_nonneg ell _
  · intro q
    simpa [lowerTailPartialSum] using hC q

/-- The deterministic lower-tail good condition: for every pair of integer
scales, its nonnegative descending-shell control series has bounded partial
sums. -/
def LowerTailGood (omega : ShellSeq d) : Prop :=
  ∀ ell m : ℤ, LowerTailBounded ell m omega

/-- The measurable event on which all descending local-control tails are
summable. -/
def lowerTailGoodSet (d : ℕ) : Set (ShellSeq d) :=
  {omega | LowerTailGood omega}

theorem lowerTailGood_summable {omega : ShellSeq d}
    (h : LowerTailGood omega) (ell m : ℤ) :
    Summable (fun r : ℕ => localCubeControl ell (omega (m - r))) :=
  lowerTailBounded_summable (h ell m)

theorem measurableSet_lowerTailBounded (ell m : ℤ) :
    MeasurableSet {omega : ShellSeq d | LowerTailBounded ell m omega} := by
  change MeasurableSet {omega : ShellSeq d |
    ∃ C : ℕ, ∀ q : ℕ, lowerTailPartialSum ell m q omega ≤ C}
  rw [show {omega : ShellSeq d | ∃ C : ℕ, ∀ q : ℕ,
      lowerTailPartialSum ell m q omega ≤ C} =
      ⋃ C : ℕ, ⋂ q : ℕ, {omega | lowerTailPartialSum ell m q omega ≤ C} by
    ext omega
    simp]
  exact MeasurableSet.iUnion fun C : ℕ =>
    MeasurableSet.iInter fun q : ℕ =>
      measurableSet_le (measurable_lowerTailPartialSum ell m q)
        (measurable_const : Measurable (fun _ : ShellSeq d => (C : ℝ)))

theorem measurableSet_lowerTailGoodSet (d : ℕ) :
    MeasurableSet (lowerTailGoodSet d) := by
  change MeasurableSet {omega : ShellSeq d |
    ∀ ell m : ℤ, LowerTailBounded ell m omega}
  simpa only [Set.ofPred_forall] using
    (MeasurableSet.iInter fun ell : ℤ =>
      MeasurableSet.iInter fun m : ℤ => measurableSet_lowerTailBounded (d := d) ell m)

/-- On the good event, every matrix entry of the finite lower cutoffs converges
uniformly on each open origin cube.  The limit is only displayed as an
internal series here; no infinite cutoff is defined in this file. -/
theorem lowerTailGood_tendstoUniformlyOn_finiteLowerCutoff_entry
    {omega : ShellSeq d} (hgood : LowerTailGood omega) (ell m : ℤ)
    (i k : Fin d) :
    TendstoUniformlyOn
      (fun q x => finiteLowerCutoff m q omega x i k)
      (fun x => ∑' r : ℕ, omega (m - r) x i k)
      Filter.atTop (openCubeSet (originCube d ell)) := by
  have hsummable := lowerTailGood_summable hgood ell m
  have hbound : ∀ r : ℕ, ∀ x, x ∈ openCubeSet (originCube d ell) →
      ‖omega (m - r) x i k‖ ≤ localCubeControl ell (omega (m - r)) := by
    intro r x hx
    simpa [Real.norm_eq_abs] using
      abs_entry_le_localCubeControl ell (omega (m - r)) hx i k
  simpa only [finiteLowerCutoff_apply_entry_eq_sum_range_desc] using
    (tendstoUniformlyOn_tsum_nat hsummable hbound)

end

end Algsuperdiff.Section3.Cutoff
