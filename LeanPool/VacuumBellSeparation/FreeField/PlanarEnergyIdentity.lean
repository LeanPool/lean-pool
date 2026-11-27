/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.PlanarEnergyIntegrationByParts

/-!
# The actual Klein–Gordon planar energy identity

The energy is a finite sum of proved weighted L² forms of the literal Cauchy
solution and its actual velocity and spatial derivatives. Differentiation uses
the actual L² PDE and the spatial derivative theorem. Schwartz integration by
parts supplies the cancellation, including the correctly signed cutoff flux.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped InnerProductSpace

open MeasureTheory LineDeriv Laplacian
open scoped LineDeriv

/-- Spatial energy basis obtained from `EuclideanSpace.basisFun`. -/
noncomputable def spatialEnergyBasis : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
  EuclideanSpace.basisFun (Fin 3) ℝ

theorem planarPairing_sum_right {ι : Type*} [Fintype ι]
    (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (f : SpatialSchwartz) (g : ι → SpatialSchwartz) :
    planarPairing a x₀ R t f (∑ i, g i) = ∑ i, planarPairing a x₀ R t f (g i) := by
  change ⟪f.toLp 2, SchwartzMap.toLpCLM ℂ ℂ 2 volume
    (SchwartzMap.smulLeftCLM ℂ _ (∑ i, g i))⟫_ℝ = _
  simp only [map_sum, inner_sum]
  rfl

/-- The exact cancellation between the acceleration, gradient and mass terms. -/
theorem planarEnergy_cancellation
    (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t m : ℝ) (u v : SpatialSchwartz) :
    planarPairing a x₀ R t v (Δ u - ((m ^ 2 : ℝ) : ℂ) • u) +
        (∑ j, planarPairing a x₀ R t (∂_{spatialEnergyBasis j} u) (∂_{spatialEnergyBasis j} v)) +
        m ^ 2 * planarPairing a x₀ R t u v =
      -(∑ j, ⟪a, spatialEnergyBasis j⟫_ℝ *
        planarSlopePairing a x₀ R t v (∂_{spatialEnergyBasis j} u)) := by
  rw [planarPairing_sub_right, planarPairing_real_smul_right,
    SchwartzMap.laplacian_eq_sum spatialEnergyBasis, planarPairing_sum_right]
  have hibp :
      (∑ j, planarPairing a x₀ R t v
        (∂_{spatialEnergyBasis j} (∂_{spatialEnergyBasis j} u))) =
      -(∑ j, planarPairing a x₀ R t (∂_{spatialEnergyBasis j} v)
        (∂_{spatialEnergyBasis j} u)) -
        ∑ j, ⟪a, spatialEnergyBasis j⟫_ℝ *
          planarSlopePairing a x₀ R t v (∂_{spatialEnergyBasis j} u) := by
    calc
      _ = ∑ j, (-planarPairing a x₀ R t (∂_{spatialEnergyBasis j} v)
          (∂_{spatialEnergyBasis j} u) - ⟪a, spatialEnergyBasis j⟫_ℝ *
            planarSlopePairing a x₀ R t v (∂_{spatialEnergyBasis j} u)) := by
        apply Finset.sum_congr rfl
        intro j _
        exact planarPairing_lineDeriv_right a x₀ (spatialEnergyBasis j) R t v
          (∂_{spatialEnergyBasis j} u)
      _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [hibp]
  have hsym : (∑ j, planarPairing a x₀ R t (∂_{spatialEnergyBasis j} v)
      (∂_{spatialEnergyBasis j} u)) =
      ∑ j, planarPairing a x₀ R t (∂_{spatialEnergyBasis j} u) (∂_{spatialEnergyBasis j} v) := by
    apply Finset.sum_congr rfl
    intro j _
    exact planarPairing_comm _ _ _ _ _ _
  rw [hsym, planarPairing_comm a x₀ R t v u]
  ring

/-- Planar klein gordon energy. -/
noncomputable def planarKleinGordonEnergy
    (a x₀ : EuclideanSpace ℝ (Fin 3)) (R m t : ℝ) (u v : SpatialSchwartz) : ℝ :=
  (1 / 2 : ℝ) * (planarPairing a x₀ R t v v +
    (∑ j, planarPairing a x₀ R t (∂_{spatialEnergyBasis j} u) (∂_{spatialEnergyBasis j} u)) +
    m ^ 2 * planarPairing a x₀ R t u u)

/-- Planar klein gordon flux. -/
noncomputable def planarKleinGordonFlux
    (a x₀ : EuclideanSpace ℝ (Fin 3)) (R m t : ℝ) (u v : SpatialSchwartz) : ℝ :=
  (1 / 2 : ℝ) * (planarSlopePairing a x₀ R t v v +
    (∑ j, planarSlopePairing a x₀ R t (∂_{spatialEnergyBasis j} u) (∂_{spatialEnergyBasis j} u)) +
    m ^ 2 * planarSlopePairing a x₀ R t u u +
    2 * ∑ j, ⟪a, spatialEnergyBasis j⟫_ℝ *
      planarSlopePairing a x₀ R t v (∂_{spatialEnergyBasis j} u))

theorem planarKleinGordonEnergy_nonneg
    (a x₀ : EuclideanSpace ℝ (Fin 3)) (R m t : ℝ) (u v : SpatialSchwartz) :
    0 ≤ planarKleinGordonEnergy a x₀ R m t u v := by
  unfold planarKleinGordonEnergy
  apply mul_nonneg (by norm_num)
  exact add_nonneg (add_nonneg (planarPairing_self_nonneg _ _ _ _ _)
    (Finset.sum_nonneg fun j _ => planarPairing_self_nonneg _ _ _ _ _))
    (mul_nonneg (sq_nonneg m) (planarPairing_self_nonneg _ _ _ _ _))

/-- The weighted energy identity for the actual cosine/sine Cauchy solution.
The sign estimate for the flux, for `‖a‖ ≤ 1`, is proved in another module
(`planarKleinGordonFlux_nonneg` in `FreeField/PlanarEnergyFlux.lean`). -/
theorem hasDerivAt_planarKleinGordonEnergy {m : ℝ} (hm : 0 < m)
    (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ) (f g : SpatialSchwartz) :
    HasDerivAt
      (fun s => planarKleinGordonEnergy a x₀ R m s
        (massiveSchwartzCauchy m s f g) (massiveSchwartzCauchyVelocity m s f g))
      (-planarKleinGordonFlux a x₀ R m t
        (massiveSchwartzCauchy m t f g) (massiveSchwartzCauchyVelocity m t f g)) t := by
  let U (s : ℝ) := massiveSchwartzCauchy m s f g
  let V (s : ℝ) := massiveSchwartzCauchyVelocity m s f g
  have hU := hasDerivAt_massiveSchwartzCauchy_toL2 m t f g
  have hV : HasDerivAt (fun s => (V s).toLp 2)
      ((Δ (U t) - ((m ^ 2 : ℝ) : ℂ) • U t).toLp 2) t := by
    simpa only [spatialSchwartz_toL2_sub, spatialSchwartz_toL2_smul] using
      hasDerivAt_massiveSchwartzCauchy_kleinGordon hm t f g
  have hv := hasDerivAt_planarPairing_self a x₀ R t V _ hV
  have hu := hasDerivAt_planarPairing_self a x₀ R t U _ hU
  have hg := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    hasDerivAt_planarPairing_self a x₀ R t (fun s => ∂_{spatialEnergyBasis j} (U s))
      (∂_{spatialEnergyBasis j} (V t))
      (hasDerivAt_lineDeriv_massiveSchwartzCauchy_toL2 m t (spatialEnergyBasis j) f g))
  have h := ((hv.add hg).add (hu.const_mul (m ^ 2))).const_mul (1 / 2 : ℝ)
  have hc := planarEnergy_cancellation a x₀ R t m (U t) (V t)
  have heq :
      (1 / 2 : ℝ) *
        ((2 * planarPairing a x₀ R t (V t) (Δ (U t) - ((m ^ 2 : ℝ) : ℂ) • U t) -
          planarSlopePairing a x₀ R t (V t) (V t) +
          (∑ j, (2 * planarPairing a x₀ R t (∂_{spatialEnergyBasis j} (U t))
            (∂_{spatialEnergyBasis j} (V t)) -
            planarSlopePairing a x₀ R t (∂_{spatialEnergyBasis j} (U t))
              (∂_{spatialEnergyBasis j} (U t))))) +
          m ^ 2 * (2 * planarPairing a x₀ R t (U t) (V t) -
            planarSlopePairing a x₀ R t (U t) (U t))) =
      -planarKleinGordonFlux a x₀ R m t (U t) (V t) := by
    simp only [planarKleinGordonFlux, Finset.sum_sub_distrib, ← Finset.mul_sum]
    linarith
  exact heq ▸ h

end VacuumBellSeparation
