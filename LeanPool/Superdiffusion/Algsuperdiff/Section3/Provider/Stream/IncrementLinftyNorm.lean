/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.OneSidedOrlicz
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.IncrementGaugeTwoIndex
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.LargeCubeLinfty
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.ConcentrationAEMeasurable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# IncrementLinftyNorm

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Exact stream-increment Linfinity norm

This module defines the literal pointwise supremum of the matrix operator norm
of a finite stream increment on an origin cube.  It then transports the
already-proved measurable small- and large-cube envelopes to that exact norm.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open scoped ENNReal Pointwise

noncomputable section

variable {d : ℕ}

/-- The literal `L∞` norm of `k_m-k_n` on the open origin cube `cu_l`, with a
zero member adjoined so the defining supremum is nonempty and nonnegative. -/
def streamIncrementLinftyNorm (l n m : ℤ) (omega : ShellSeq d) : ℝ :=
  sSup (Set.range fun o : Option {x : Vec d // x ∈ openCubeSet (originCube d l)} =>
    match o with
    | none => (0 : ℝ)
    | some x => Book.Ch02.matrixOperatorNorm (finiteShellIncrement omega n m x.1))

private theorem streamIncrementLinftyNorm_range_bddAbove
    (l n m : ℤ) (omega : ShellSeq d) :
    BddAbove (Set.range fun o : Option {x : Vec d // x ∈ openCubeSet (originCube d l)} =>
      match o with
      | none => (0 : ℝ)
      | some x => Book.Ch02.matrixOperatorNorm (finiteShellIncrement omega n m x.1)) := by
  refine ⟨largeCubeSupBound l n m omega, ?_⟩
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact largeCubeSupBound_nonneg l n m omega
  | some x =>
      exact matrixOperatorNorm_finiteShellIncrement_le_largeCubeSupBound
        omega l n m x.2

theorem streamIncrementLinftyNorm_nonneg (l n m : ℤ) (omega : ShellSeq d) :
    0 ≤ streamIncrementLinftyNorm l n m omega := by
  unfold streamIncrementLinftyNorm
  exact le_csSup (streamIncrementLinftyNorm_range_bddAbove l n m omega)
    ⟨none, rfl⟩

/-- The literal norm dominates every point value on its defining cube. -/
theorem matrixOperatorNorm_finiteShellIncrement_le_streamIncrementLinftyNorm
    (omega : ShellSeq d) (l n m : ℤ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d l)) :
    Book.Ch02.matrixOperatorNorm (finiteShellIncrement omega n m x) ≤
      streamIncrementLinftyNorm l n m omega := by
  unfold streamIncrementLinftyNorm
  exact le_csSup (streamIncrementLinftyNorm_range_bddAbove l n m omega)
    ⟨some ⟨x, hx⟩, rfl⟩

theorem streamIncrementLinftyNorm_le_largeCubeSupBound
    (omega : ShellSeq d) (l n m : ℤ) :
    streamIncrementLinftyNorm l n m omega ≤ largeCubeSupBound l n m omega := by
  unfold streamIncrementLinftyNorm
  refine csSup_le (Set.range_nonempty _) ?_
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact largeCubeSupBound_nonneg l n m omega
  | some x =>
      exact matrixOperatorNorm_finiteShellIncrement_le_largeCubeSupBound
        omega l n m x.2

theorem streamIncrementLinftyNorm_le_incrementSupBound
    (omega : ShellSeq d) (n m : ℤ) :
    streamIncrementLinftyNorm n n m omega ≤ incrementSupBound n m omega := by
  unfold streamIncrementLinftyNorm
  refine csSup_le (Set.range_nonempty _) ?_
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact incrementSupBound_nonneg n m omega
  | some x =>
      exact matrixOperatorNorm_finiteShellIncrement_le_incrementSupBound
        omega n m x.2

/-- The direct open-cube supremum is exactly the already-measurable local
control of the genuine shell-field increment. -/
theorem streamIncrementLinftyNorm_eq_localCubeControl
    (l n m : ℤ) (omega : ShellSeq d) :
    streamIncrementLinftyNorm l n m omega =
      localCubeControl l (shellIncrement omega n m) := by
  let r : ℝ := cubeScaleFactor (originCube d l)
  have hr : 0 < r := by
    simpa [r, cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) l)
  apply le_antisymm
  · unfold streamIncrementLinftyNorm
    apply csSup_le (Set.range_nonempty _)
    rintro a ⟨o, rfl⟩
    cases o with
    | none => exact localCubeControl_nonneg l (shellIncrement omega n m)
    | some x =>
        have hxscaled : x.1 ∈ r • openCubeSet (originCube d 0) := by
          dsimp only [r]
          rw [← openCubeSet_originCube_eq_smul_originCube_zero]
          exact x.2
        rw [Set.mem_smul_set] at hxscaled
        obtain ⟨y, hy, hxy⟩ := hxscaled
        have hunit := ShellField.matrixOperatorNorm_apply_le_unitCubeValueNorm
          (ShellField.spatialScale r (shellIncrement omega n m)) ⟨y, hy⟩
        change Book.Ch02.matrixOperatorNorm (finiteShellIncrement omega n m x.1) ≤
          ShellField.unitCubeValueNorm
            (ShellField.spatialScale r (shellIncrement omega n m))
        rw [ShellField.spatialScale_apply, shellIncrement_apply, hxy] at hunit
        exact hunit
  · unfold localCubeControl ShellField.unitCubeValueNorm
    apply csSup_le (Set.range_nonempty _)
    rintro a ⟨o, rfl⟩
    cases o with
    | none => exact streamIncrementLinftyNorm_nonneg l n m omega
    | some y =>
        have hyactual : r • y.1 ∈ openCubeSet (originCube d l) := by
          rw [openCubeSet_originCube_eq_smul_originCube_zero,
            Set.mem_smul_set]
          exact ⟨y.1, y.2, rfl⟩
        have hpoint := matrixOperatorNorm_finiteShellIncrement_le_streamIncrementLinftyNorm
          omega l n m hyactual
        change Book.Ch02.matrixOperatorNorm
            (ShellField.spatialScale r (shellIncrement omega n m) y) ≤
          streamIncrementLinftyNorm l n m omega
        rw [ShellField.spatialScale_apply, shellIncrement_apply]
        exact hpoint

/-- The literal stream-increment supremum is a measurable random variable on
the canonical shell-sequence carrier. -/
theorem measurable_streamIncrementLinftyNorm (l n m : ℤ) :
    Measurable (fun omega : ShellSeq d => streamIncrementLinftyNorm l n m omega) := by
  rw [show (fun omega : ShellSeq d => streamIncrementLinftyNorm l n m omega) =
      fun omega => localCubeControl l (shellIncrement omega n m) by
    funext omega
    exact streamIncrementLinftyNorm_eq_localCubeControl l n m omega]
  exact (measurable_localCubeControl l).comp
    (Algsuperdiff.Section3.Provider.BadEvents.measurable_shellIncrement n m)

/-- Exact small-cube squared-norm transport from the proved measurable
envelope. -/
theorem streamIncrementLinftyNorm_sq_isBigOWith_smallCube
    (M : ABKModel d) {n m : ℤ} (hnm : n < m) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d => streamIncrementLinftyNorm n n m omega ^ 2)
      (streamLinftyConst d ^ 2 * min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by
  refine Book.Ch04.isBigOWith_of_ae_le
    (isBigOWith_gammaSigma_one_incrementSupBound_sq M hnm) ?_
  exact Filter.Eventually.of_forall fun omega =>
    (sq_le_sq₀ (streamIncrementLinftyNorm_nonneg n n m omega)
      (incrementSupBound_nonneg n m omega)).2
        (streamIncrementLinftyNorm_le_incrementSupBound omega n m)

/-- Exact large-cube squared-norm transport from the proved covering
envelope. -/
theorem streamIncrementLinftyNorm_sq_isBigOWith_largeCube
    (M : ABKModel d) {l n m : ℤ} (hnm : n < m) (hml : m ≤ l) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d => streamIncrementLinftyNorm l n m omega ^ 2)
      (largeCubeLinftyConst d * ((l : ℝ) - (n : ℝ)) *
        min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by
  refine Book.Ch04.isBigOWith_of_ae_le
    (isBigOWith_gammaSigma_one_largeCubeSupBound_sq M hnm hml) ?_
  exact Filter.Eventually.of_forall fun omega =>
    (sq_le_sq₀ (streamIncrementLinftyNorm_nonneg l n m omega)
      (largeCubeSupBound_nonneg l n m omega)).2
        (streamIncrementLinftyNorm_le_largeCubeSupBound omega l n m)

/-- The exact small-cube squared norm satisfies the Appendix-literal
one-sided Orlicz relation, including measurability and positive scale. -/
theorem streamIncrementLinftyNorm_sq_isOneSidedOrlicz_smallCube
    (M : ABKModel d) {n m : ℤ} (hnm : n < m) :
    Probability.IsOneSidedOrlicz M.P.toMeasure
      (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d => streamIncrementLinftyNorm n n m omega ^ 2)
      (streamLinftyConst d ^ 2 * min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hmn : 0 < (m : ℝ) - (n : ℝ) := by
    have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
    linarith
  refine ⟨Probability.isAdmissibleTail_gammaSigma (by norm_num), ?_,
    (measurable_streamIncrementLinftyNorm n n m).pow_const 2,
    streamIncrementLinftyNorm_sq_isBigOWith_smallCube M hnm⟩
  exact mul_pos
    (mul_pos (sq_pos_of_pos (streamLinftyConst_pos hd))
      (lt_min (inv_pos.mpr M.shellPrefix.gamma_pos) hmn))
    (Real.rpow_pos_of_pos (by norm_num) _)

/-- The exact large-cube squared norm satisfies the Appendix-literal
one-sided Orlicz relation, including measurability and positive scale. -/
theorem streamIncrementLinftyNorm_sq_isOneSidedOrlicz_largeCube
    (M : ABKModel d) {l n m : ℤ} (hnm : n < m) (hml : m ≤ l) :
    Probability.IsOneSidedOrlicz M.P.toMeasure
      (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d => streamIncrementLinftyNorm l n m omega ^ 2)
      (largeCubeLinftyConst d * ((l : ℝ) - (n : ℝ)) *
        min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hmn : 0 < (m : ℝ) - (n : ℝ) := by
    have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
    linarith
  have hln : 0 < (l : ℝ) - (n : ℝ) := by
    have hcast : (n : ℝ) < (l : ℝ) := by exact_mod_cast hnm.trans_le hml
    linarith
  refine ⟨Probability.isAdmissibleTail_gammaSigma (by norm_num), ?_,
    (measurable_streamIncrementLinftyNorm l n m).pow_const 2,
    streamIncrementLinftyNorm_sq_isBigOWith_largeCube M hnm hml⟩
  exact mul_pos
    (mul_pos
      (mul_pos (largeCubeLinftyConst_pos hd) hln)
      (lt_min (inv_pos.mpr M.shellPrefix.gamma_pos) hmn))
    (Real.rpow_pos_of_pos (by norm_num) _)

end

end Algsuperdiff.Section3.Provider.Stream
