/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.PlanarWeightedL2
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The genuine weighted energy quadratic form

The forms below are real L² inner products of actual Schwartz functions and
actual planar multiplication. Their integral formulas, symmetry, positivity,
and time derivative are proved, not supplied as energy assumptions.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped InnerProductSpace

theorem real_inner_spatialSchwartz_toL2 (f g : SpatialSchwartz) :
    ⟪f.toLp 2, g.toLp 2⟫_ℝ = ∫ x, ⟪f x, g x⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2, g.coeFn_toLp 2] with x hf hg
  rw [hf, hg]

/-- Planar slope Schwartz defined as `SchwartzMap.smulLeftCLM ℂ (fun x => (planarEnergySlope a x₀ R
t x : ℂ)) f`. -/
noncomputable def planarSlopeSchwartz (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (f : SpatialSchwartz) : SpatialSchwartz :=
  SchwartzMap.smulLeftCLM ℂ (fun x => (planarEnergySlope a x₀ R t x : ℂ)) f

@[simp] theorem planarSlopeSchwartz_apply (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (f : SpatialSchwartz) (x : EuclideanSpace ℝ (Fin 3)) :
    planarSlopeSchwartz a x₀ R t f x = (planarEnergySlope a x₀ R t x : ℂ) * f x := by
  rw [planarSlopeSchwartz, SchwartzMap.smulLeftCLM_apply_apply
    (hasTemperateGrowth_complex_planarEnergySlope a x₀ R t)]
  rfl

@[simp] theorem planarWeightedSchwartzDerivative_eq_neg (a x₀ : EuclideanSpace ℝ (Fin 3))
    (R t : ℝ) (f : SpatialSchwartz) :
    planarWeightedSchwartzDerivative a x₀ R t f = -planarSlopeSchwartz a x₀ R t f := rfl

/-- Planar pairing. -/
noncomputable def planarPairing (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (f g : SpatialSchwartz) : ℝ :=
  ⟪f.toLp 2, (planarWeightedSchwartz a x₀ R t g).toLp 2⟫_ℝ

/-- Planar slope pairing. -/
noncomputable def planarSlopePairing (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (f g : SpatialSchwartz) : ℝ :=
  ⟪f.toLp 2, (planarSlopeSchwartz a x₀ R t g).toLp 2⟫_ℝ

theorem planarPairing_eq_integral (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (f g : SpatialSchwartz) :
    planarPairing a x₀ R t f g = ∫ x, planarEnergyWeight a x₀ R t x * ⟪f x, g x⟫_ℝ := by
  rw [planarPairing, real_inner_spatialSchwartz_toL2]
  congr 1
  funext x
  rw [planarWeightedSchwartz_apply, ← Complex.real_smul]
  exact inner_smul_right _ _ _

theorem planarSlopePairing_eq_integral (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (f g : SpatialSchwartz) :
    planarSlopePairing a x₀ R t f g = ∫ x, planarEnergySlope a x₀ R t x * ⟪f x, g x⟫_ℝ := by
  rw [planarSlopePairing, real_inner_spatialSchwartz_toL2]
  congr 1
  funext x
  rw [planarSlopeSchwartz_apply, ← Complex.real_smul]
  exact inner_smul_right _ _ _

theorem planarPairing_comm (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (f g : SpatialSchwartz) : planarPairing a x₀ R t f g = planarPairing a x₀ R t g f := by
  simp only [planarPairing_eq_integral, real_inner_comm]

theorem planarSlopePairing_comm (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (f g : SpatialSchwartz) :
    planarSlopePairing a x₀ R t f g = planarSlopePairing a x₀ R t g f := by
  simp only [planarSlopePairing_eq_integral, real_inner_comm]

theorem planarPairing_self_nonneg (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (f : SpatialSchwartz) : 0 ≤ planarPairing a x₀ R t f f := by
  rw [planarPairing_eq_integral]
  apply integral_nonneg
  intro x
  exact mul_nonneg (planarEnergyWeight_nonneg a x₀ R t x) (inner_self_nonneg)

theorem planarSlopePairing_self_nonneg (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (f : SpatialSchwartz) : 0 ≤ planarSlopePairing a x₀ R t f f := by
  rw [planarSlopePairing_eq_integral]
  apply integral_nonneg
  intro x
  exact mul_nonneg (planarEnergySlope_nonneg a x₀ R t x) (inner_self_nonneg)

theorem planarPairing_add_right (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (f g h : SpatialSchwartz) :
    planarPairing a x₀ R t f (g + h) =
      planarPairing a x₀ R t f g + planarPairing a x₀ R t f h := by
  simp only [planarPairing, planarWeightedSchwartz, map_add,
    spatialSchwartz_toL2_add, inner_add_right]

theorem planarPairing_sub_right (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (f g h : SpatialSchwartz) :
    planarPairing a x₀ R t f (g - h) =
      planarPairing a x₀ R t f g - planarPairing a x₀ R t f h := by
  simp only [planarPairing, planarWeightedSchwartz, map_sub,
    spatialSchwartz_toL2_sub, inner_sub_right]

theorem planarPairing_real_smul_right (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t c : ℝ)
    (f g : SpatialSchwartz) :
    planarPairing a x₀ R t f ((c : ℂ) • g) = c * planarPairing a x₀ R t f g := by
  rw [planarPairing, planarWeightedSchwartz, map_smul, spatialSchwartz_toL2_smul]
  have hs : (c : ℂ) • (planarWeightedSchwartz a x₀ R t g).toLp 2 volume =
      c • (planarWeightedSchwartz a x₀ R t g).toLp 2 volume := by
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) c _).symm
  change ⟪f.toLp 2 volume, (c : ℂ) • (planarWeightedSchwartz a x₀ R t g).toLp 2 volume⟫_ℝ = _
  rw [hs]
  exact inner_smul_right _ _ _

/-- Differentiation of the actual weighted square norm of an L²-differentiable
Schwartz curve, including the negative time derivative of the moving cutoff. -/
theorem hasDerivAt_planarPairing_self
    (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (F : ℝ → SpatialSchwartz) (G : SpatialSchwartz)
    (hF : HasDerivAt (fun s => (F s).toLp 2) (G.toLp 2) t) :
    HasDerivAt (fun s => planarPairing a x₀ R s (F s) (F s))
      (2 * planarPairing a x₀ R t (F t) G - planarSlopePairing a x₀ R t (F t) (F t)) t := by
  have hW := hasDerivAt_planarWeighted_curve_toL2 a x₀ R t F G hF
  have h := hF.inner ℝ hW
  have hvalue :
      ⟪(F t).toLp 2 volume, (planarWeightedSchwartz a x₀ R t G).toLp 2 volume +
        (planarWeightedSchwartzDerivative a x₀ R t (F t)).toLp 2 volume⟫_ℝ +
        ⟪G.toLp 2 volume, (planarWeightedSchwartz a x₀ R t (F t)).toLp 2 volume⟫_ℝ =
      2 * planarPairing a x₀ R t (F t) G - planarSlopePairing a x₀ R t (F t) (F t) := by
    rw [inner_add_right, planarWeightedSchwartzDerivative_eq_neg,
      spatialSchwartz_toL2_neg, inner_neg_right]
    change (planarPairing a x₀ R t (F t) G - planarSlopePairing a x₀ R t (F t) (F t)) +
      planarPairing a x₀ R t G (F t) = _
    rw [planarPairing_comm a x₀ R t G (F t)]
    ring
  exact hvalue ▸ h

end VacuumBellSeparation
