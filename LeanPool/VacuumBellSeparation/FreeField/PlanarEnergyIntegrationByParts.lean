/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.PlanarWeightedPairing
public import LeanPool.VacuumBellSeparation.FreeField.CauchySpatialDerivatives

/-!
# Actual integration by parts for the planar energy

The directional derivative of the literal cutoff is evaluated explicitly.
The weighted integration by parts formula is then the ordinary Schwartz
integration by parts theorem applied to the genuine weighted Schwartz datum.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped InnerProductSpace

open MeasureTheory LineDeriv
open scoped LineDeriv

theorem lineDeriv_planarWeightedSchwartz
    (a x₀ v : EuclideanSpace ℝ (Fin 3)) (R t : ℝ) (f : SpatialSchwartz) :
    ∂_{v} (planarWeightedSchwartz a x₀ R t f) =
      planarWeightedSchwartz a x₀ R t (∂_{v} f) +
        (⟪a, v⟫_ℝ : ℂ) • planarSlopeSchwartz a x₀ R t f := by
  ext x
  have hw := Complex.ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_planarEnergyWeight a x₀ R t x)
  have hprod := hw.mul (f.hasFDerivAt x)
  change HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) =>
    (planarEnergyWeight a x₀ R t y : ℂ) * f y) _ x at hprod
  have hfun : (planarWeightedSchwartz a x₀ R t f : EuclideanSpace ℝ (Fin 3) → ℂ) =
      (fun y => (planarEnergyWeight a x₀ R t y : ℂ) * f y) :=
    funext (planarWeightedSchwartz_apply a x₀ R t f)
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hfun, hprod.fderiv]
  simp only [add_apply, smul_apply, planarWeightedSchwartz_apply,
    planarSlopeSchwartz_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, Complex.ofRealCLM_apply, innerSL_apply_apply,
    smul_eq_mul, Complex.ofReal_mul, Function.comp_apply, Complex.ofRealCLM_apply]
  ring

theorem real_inner_planarWeightedSchwartz_left
    (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ) (f g : SpatialSchwartz) :
    ⟪(planarWeightedSchwartz a x₀ R t f).toLp 2, g.toLp 2⟫_ℝ =
      planarPairing a x₀ R t f g := by
  rw [real_inner_comm]
  exact planarPairing_comm a x₀ R t g f

theorem real_inner_planarSlopeSchwartz_left
    (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ) (f g : SpatialSchwartz) :
    ⟪(planarSlopeSchwartz a x₀ R t f).toLp 2, g.toLp 2⟫_ℝ =
      planarSlopePairing a x₀ R t f g := by
  rw [real_inner_comm]
  exact planarSlopePairing_comm a x₀ R t g f

theorem real_inner_spatialSchwartz_lineDeriv
    (v : EuclideanSpace ℝ (Fin 3)) (f g : SpatialSchwartz) :
    ⟪f.toLp 2, (∂_{v} g).toLp 2⟫_ℝ = -⟪(∂_{v} f).toLp 2, g.toLp 2⟫_ℝ := by
  simp only [real_inner_spatialSchwartz_toL2]
  exact SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left f g (innerSL ℝ) v

/-- The cutoff-gradient term has the actual positive outward spatial sign.
Its negative sign here comes from integration by parts. -/
theorem planarPairing_lineDeriv_right
    (a x₀ v : EuclideanSpace ℝ (Fin 3)) (R t : ℝ) (f g : SpatialSchwartz) :
    planarPairing a x₀ R t f (∂_{v} g) =
      -planarPairing a x₀ R t (∂_{v} f) g -
        ⟪a, v⟫_ℝ * planarSlopePairing a x₀ R t f g := by
  have hsmul : (⟪a, v⟫_ℝ : ℂ) • (planarSlopeSchwartz a x₀ R t f).toLp 2 =
      ⟪a, v⟫_ℝ • (planarSlopeSchwartz a x₀ R t f).toLp 2 := by
    simpa only [RCLike.ofReal_eq_complex_ofReal] using
      (RCLike.real_smul_eq_coe_smul (K := ℂ) ⟪a, v⟫_ℝ
        ((planarSlopeSchwartz a x₀ R t f).toLp 2)).symm
  rw [← real_inner_planarWeightedSchwartz_left,
    real_inner_spatialSchwartz_lineDeriv, lineDeriv_planarWeightedSchwartz,
    spatialSchwartz_toL2_add, spatialSchwartz_toL2_smul, inner_add_left,
    hsmul, real_inner_smul_left,
    real_inner_planarWeightedSchwartz_left, real_inner_planarSlopeSchwartz_left]
  ring

end VacuumBellSeparation
