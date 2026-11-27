/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.PlanarEnergyIdentity

/-!
# Positivity of the actual outward energy flux

Completing the square in the actual positive weighted form proves the flux
sign for a plane moving at speed one and any normal of norm at most one.
The estimate is valid for complex Schwartz fields, so no realness theorem is
needed for finite propagation.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped InnerProductSpace

open MeasureTheory LineDeriv
open scoped LineDeriv

theorem planarSlopePairing_add_right
    (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ) (f g h : SpatialSchwartz) :
    planarSlopePairing a x₀ R t f (g + h) =
      planarSlopePairing a x₀ R t f g + planarSlopePairing a x₀ R t f h := by
  simp only [planarSlopePairing, planarSlopeSchwartz, map_add,
    spatialSchwartz_toL2_add, inner_add_right]

theorem planarSlopePairing_real_smul_right
    (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t c : ℝ) (f g : SpatialSchwartz) :
    planarSlopePairing a x₀ R t f ((c : ℂ) • g) = c * planarSlopePairing a x₀ R t f g := by
  rw [planarSlopePairing, planarSlopeSchwartz, map_smul, spatialSchwartz_toL2_smul]
  have hs : (c : ℂ) • (planarSlopeSchwartz a x₀ R t g).toLp 2 volume =
      c • (planarSlopeSchwartz a x₀ R t g).toLp 2 volume := by
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) c _).symm
  change ⟪f.toLp 2 volume, (c : ℂ) • (planarSlopeSchwartz a x₀ R t g).toLp 2 volume⟫_ℝ = _
  rw [hs]
  exact inner_smul_right _ _ _

theorem planarSlopePairing_add_left
    (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ) (f g h : SpatialSchwartz) :
    planarSlopePairing a x₀ R t (f + g) h =
      planarSlopePairing a x₀ R t f h + planarSlopePairing a x₀ R t g h := by
  rw [planarSlopePairing_comm a x₀ R t (f + g) h, planarSlopePairing_add_right,
    planarSlopePairing_comm a x₀ R t h f, planarSlopePairing_comm a x₀ R t h g]

theorem planarSlopePairing_real_smul_left
    (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t c : ℝ) (f g : SpatialSchwartz) :
    planarSlopePairing a x₀ R t ((c : ℂ) • f) g = c * planarSlopePairing a x₀ R t f g := by
  rw [planarSlopePairing_comm a x₀ R t ((c : ℂ) • f) g,
    planarSlopePairing_real_smul_right, planarSlopePairing_comm a x₀ R t g f]

theorem planarSlopePairing_complete_square
    (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t c : ℝ) (f g : SpatialSchwartz) :
    planarSlopePairing a x₀ R t (g + (c : ℂ) • f) (g + (c : ℂ) • f) =
      planarSlopePairing a x₀ R t g g +
        2 * c * planarSlopePairing a x₀ R t f g +
        c ^ 2 * planarSlopePairing a x₀ R t f f := by
  simp only [planarSlopePairing_add_right, planarSlopePairing_add_left,
    planarSlopePairing_real_smul_right, planarSlopePairing_real_smul_left]
  rw [planarSlopePairing_comm a x₀ R t g f]
  ring

/-- Exact sum-of-squares identity for the energy flux. -/
theorem planarKleinGordonFlux_eq_squares
    (a x₀ : EuclideanSpace ℝ (Fin 3)) (R m t : ℝ) (u v : SpatialSchwartz) :
    planarKleinGordonFlux a x₀ R m t u v =
      (1 / 2 : ℝ) *
        ((∑ j, planarSlopePairing a x₀ R t
          ((∂_{spatialEnergyBasis j} u) + (⟪a, spatialEnergyBasis j⟫_ℝ : ℂ) • v)
          ((∂_{spatialEnergyBasis j} u) + (⟪a, spatialEnergyBasis j⟫_ℝ : ℂ) • v)) +
          (1 - ‖a‖ ^ 2) * planarSlopePairing a x₀ R t v v +
          m ^ 2 * planarSlopePairing a x₀ R t u u) := by
  have hsum :
      (∑ j, planarSlopePairing a x₀ R t
        ((∂_{spatialEnergyBasis j} u) + (⟪a, spatialEnergyBasis j⟫_ℝ : ℂ) • v)
        ((∂_{spatialEnergyBasis j} u) + (⟪a, spatialEnergyBasis j⟫_ℝ : ℂ) • v)) =
      (∑ j, planarSlopePairing a x₀ R t (∂_{spatialEnergyBasis j} u) (∂_{spatialEnergyBasis j} u)) +
        2 * (∑ j, ⟪a, spatialEnergyBasis j⟫_ℝ *
          planarSlopePairing a x₀ R t v (∂_{spatialEnergyBasis j} u)) +
        ‖a‖ ^ 2 * planarSlopePairing a x₀ R t v v := by
    simp only [planarSlopePairing_complete_square, Finset.sum_add_distrib,
      mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul,
      spatialEnergyBasis.sum_sq_inner_left a]
  rw [hsum, planarKleinGordonFlux]
  ring

theorem planarKleinGordonFlux_nonneg
    {a : EuclideanSpace ℝ (Fin 3)} (ha : ‖a‖ ≤ 1)
    (x₀ : EuclideanSpace ℝ (Fin 3)) (R m t : ℝ) (u v : SpatialSchwartz) :
    0 ≤ planarKleinGordonFlux a x₀ R m t u v := by
  rw [planarKleinGordonFlux_eq_squares]
  have ha₂ : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  apply mul_nonneg (by norm_num)
  exact add_nonneg
    (add_nonneg (Finset.sum_nonneg fun j _ => planarSlopePairing_self_nonneg _ _ _ _ _)
      (mul_nonneg ha₂ (planarSlopePairing_self_nonneg _ _ _ _ _)))
    (mul_nonneg (sq_nonneg m) (planarSlopePairing_self_nonneg _ _ _ _ _))

/-- The energy of the actual Cauchy solution decreases for a forward-moving
plane. This theorem uses the proved PDE identity and proved flux sign. -/
theorem antitone_planarKleinGordonEnergy {m : ℝ} (hm : 0 < m)
    {a : EuclideanSpace ℝ (Fin 3)} (ha : ‖a‖ ≤ 1)
    (x₀ : EuclideanSpace ℝ (Fin 3)) (R : ℝ) (f g : SpatialSchwartz) :
    Antitone (fun t => planarKleinGordonEnergy a x₀ R m t
      (massiveSchwartzCauchy m t f g) (massiveSchwartzCauchyVelocity m t f g)) := by
  apply antitone_of_hasDerivAt_nonpos
    (fun t => hasDerivAt_planarKleinGordonEnergy hm a x₀ R t f g)
  intro t
  exact neg_nonpos.mpr (planarKleinGordonFlux_nonneg ha x₀ R m t _ _)

end VacuumBellSeparation
