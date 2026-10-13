/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import LeanPool.Superdiffusion.Algsuperdiff.Assumptions.ShellField.J2Observable

/-!
# J2LInfSeal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Exact L-infinity interpretation of the J2 shell norms

This file identifies each pointwise open-cube supremum in the J2 observable
with the corresponding `L∞` seminorm for volume restricted to the literal
manuscript cube `cu₀ = (-1/2, 1/2)^d`.

The reverse inequality from essential supremum to pointwise supremum uses
continuity: a strict pointwise violation persists on a nonempty open
neighborhood, and such a neighborhood has positive volume.  The argument is
uniform in `d`, including `d = 0`.
-/

namespace Algsuperdiff.Frozen.Assumptions.ShellField

open Set
open HCPolySupport
open HCPolySupport.Book.Ch02
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem unitOpenCubeSup_eq_eLpNorm_top
    (f : Vec d → ℝ) (hf : Continuous f) (hf_nonneg : ∀ x, 0 ≤ f x) :
    sSup
        (Set.range fun o : Option (UnitOpenCubePoint d) =>
          match o with
          | none => 0
          | some x => f x.1) =
      ENNReal.toReal
        (eLpNorm f ∞
          (volume.restrict (openCubeSet (originCube d 0)))) := by
  let U : Set (Vec d) := openCubeSet (originCube d 0)
  let K : Set (Vec d) :=
    Metric.closedBall
      (cubeCenter (originCube d 0)) (cubeRadius (originCube d 0))
  let value : Option (UnitOpenCubePoint d) → ℝ := fun o =>
    match o with
    | none => 0
    | some x => f x.1
  let S : ℝ := sSup (Set.range value)
  let E : ℝ≥0∞ := eLpNorm f ∞ (volume.restrict U)
  have hU_open : IsOpen U := by
    dsimp only [U]
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.isOpen_ball
  have hU_meas : MeasurableSet U := hU_open.measurableSet
  have hK_compact : IsCompact K := by
    dsimp only [K]
    exact isCompact_closedBall
      (cubeCenter (originCube d 0)) (cubeRadius (originCube d 0))
  obtain ⟨C, hC⟩ := hK_compact.exists_bound_of_continuousOn hf.continuousOn
  have hvalue_bdd : BddAbove (Set.range value) := by
    refine ⟨max 0 C, ?_⟩
    rintro r ⟨o, rfl⟩
    cases o with
    | none =>
        exact le_max_left 0 C
    | some x =>
        have hxK : x.1 ∈ K := by
          apply Metric.ball_subset_closedBall
          rw [ball_cubeCenter_eq_openCubeSet]
          exact x.2
        have hfxC : f x.1 ≤ C := by
          simpa only [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg x.1)] using
            hC x.1 hxK
        exact hfxC.trans (le_max_right 0 C)
  have hS_nonneg : 0 ≤ S := by
    exact le_csSup hvalue_bdd ⟨none, rfl⟩
  have hpoint_le (x : UnitOpenCubePoint d) : f x.1 ≤ S := by
    exact le_csSup hvalue_bdd ⟨some x, rfl⟩
  have hae_norm_le :
      ∀ᵐ x ∂(volume.restrict U), ‖f x‖ ≤ S := by
    filter_upwards [ae_restrict_mem hU_meas] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg x)]
    exact hpoint_le ⟨x, hx⟩
  have hE_le : E ≤ ENNReal.ofReal S := by
    dsimp only [E]
    rw [eLpNorm_exponent_top hf.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound hae_norm_le
  have hE_ne_top : E ≠ ∞ := by
    exact ne_of_lt (hE_le.trans_lt ENNReal.ofReal_lt_top)
  have hE_toReal_le : E.toReal ≤ S := by
    have h :=
      (ENNReal.toReal_le_toReal hE_ne_top ENNReal.ofReal_ne_top).2 hE_le
    simpa only [ENNReal.toReal_ofReal hS_nonneg] using h
  have hS_le_E_toReal : S ≤ E.toReal := by
    dsimp only [S]
    apply csSup_le (Set.range_nonempty value)
    rintro r ⟨o, rfl⟩
    cases o with
    | none =>
        exact ENNReal.toReal_nonneg
    | some x =>
        change f x.1 ≤ E.toReal
        by_contra hle
        have hxlt : E.toReal < f x.1 := lt_of_not_ge hle
        let V : Set (Vec d) := U ∩ f ⁻¹' Set.Ioi E.toReal
        have hV_open : IsOpen V :=
          hU_open.inter (isOpen_Ioi.preimage hf)
        have hxV : x.1 ∈ V := ⟨x.2, hxlt⟩
        have hV_subset : V ⊆ U := inter_subset_left
        have hV_volume_pos : 0 < volume V :=
          hV_open.measure_pos volume ⟨x.1, hxV⟩
        have hV_restrict_pos : 0 < (volume.restrict U) V := by
          rw [Measure.restrict_apply hV_open.measurableSet]
          rw [inter_eq_left.mpr hV_subset]
          exact hV_volume_pos
        have hae_enorm_le :
            ∀ᵐ y ∂(volume.restrict U), ‖f y‖ₑ ≤ E := by
          dsimp only [E]
          simpa only [eLpNorm_exponent_top hf.aestronglyMeasurable] using!
            enorm_ae_le_eLpNormEssSup f (volume.restrict U)
        have hae_not_mem : ∀ᵐ y ∂(volume.restrict U), y ∉ V := by
          filter_upwards [hae_enorm_le] with y hy
          intro hyV
          have hylt : E.toReal < f y := hyV.2
          have hbad : E < ‖f y‖ₑ := by
            rw [← ENNReal.ofReal_toReal hE_ne_top]
            rw [Real.enorm_eq_ofReal (hf_nonneg y)]
            exact
              (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).2
                hylt
          exact (not_lt_of_ge hy) hbad
        have hV_restrict_zero : (volume.restrict U) V = 0 := by
          simpa only [not_not, Set.ofPred_mem_eq] using
            (ae_iff.mp hae_not_mem)
        exact (ne_of_gt hV_restrict_pos) hV_restrict_zero
  change S = E.toReal
  exact le_antisymm hS_le_E_toReal hE_toReal_le

private theorem matrixOperatorNorm_continuous_local :
    Continuous (matrixOperatorNorm : Mat d → ℝ) := by
  have htoEuclideanCLM :
      Continuous
        (fun A : Mat d =>
          Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A) := by
    exact LinearMap.continuous_of_finiteDimensional
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap
  exact continuous_norm.comp htoEuclideanCLM

/-- The pointwise value supremum in J2 is exactly its restricted-volume
`L∞` seminorm on the literal open unit cube. -/
theorem unitCubeValueNorm_eq_eLpNorm_top (j : ShellField d) :
    unitCubeValueNorm j =
      ENNReal.toReal
        (eLpNorm (fun x => matrixOperatorNorm (j x)) ∞
          (volume.restrict (openCubeSet (originCube d 0)))) := by
  change
    sSup
        (Set.range fun o : Option (UnitOpenCubePoint d) =>
          match o with
          | none => 0
          | some x => matrixOperatorNorm (j x.1)) = _
  refine unitOpenCubeSup_eq_eLpNorm_top
    (f := fun x : Vec d => matrixOperatorNorm (j x)) ?_ ?_
  · exact matrixOperatorNorm_continuous_local.comp j.1.1.continuous
  · intro x
    exact matrixOperatorNorm_nonneg (j x)

end

end Algsuperdiff.Frozen.Assumptions.ShellField
