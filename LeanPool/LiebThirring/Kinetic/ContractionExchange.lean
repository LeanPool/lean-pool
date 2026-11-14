/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.ContractionExchangeEncoding

/-! # Exchange covariance of one-particle insertion

The concrete insertion maps intertwine simultaneous exchange with the
remaining-coordinate unitary. Pairing with an antisymmetric state then gives
equality of contraction norms across particle coordinates.
-/

public section

open MeasureTheory
open scoped InnerProduct

namespace LiebThirring

/-- Exchanging particles transports insertion into the exchanged coordinate. -/
theorem simultaneousPermutation_oneParticleInsertion {N q : ℕ} (i j : Fin N)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position))
    (v : RestState i q) :
    simultaneousPermutation (Equiv.swap i j) (oneParticleInsertion i f v) =
      oneParticleInsertion j f (restExchange i j v) := by
  apply (oneParticleCurrying j).injective
  apply Lp.ext
  have hu := Measure.ae_ae_of_ae_prod ((measurePreserving_insertParticle
    j).quasiMeasurePreserving.ae
    (simultaneousPermutation_apply_ae (Equiv.swap i j) (oneParticleInsertion i f v)))
  filter_upwards [oneParticleCurrying_ae j
      (simultaneousPermutation (Equiv.swap i j) (oneParticleInsertion i f v)),
    oneParticleCurrying_ae j (oneParticleInsertion j f (restExchange i j v)),
    hu, oneParticleInsertion_ae i f v, oneParticleInsertion_ae j f (restExchange i j v)]
    with x hc hd hx hi hj
  apply PiLp.ext
  intro s
  apply Lp.ext
  have hit := (restExchangeSpatial i j).measurePreserving.quasiMeasurePreserving.ae (hi s)
  filter_upwards [hc s, hd s, hx, hit, hj s, restExchange_ae i j v]
    with y hcy hdy hxy hiy hjy hrv
  ext t
  rw [hcy t, hdy t, hxy, permutePositions_swap_insertParticle,
    permuteSpins_swap_insertSpin, hiy, hjy, hrv]

/-- On an antisymmetric state, exchange identifies the contracted vectors up to
sign and the remaining-coordinate unitary. -/
theorem oneParticleContraction_exchange {N q : ℕ} (i j : Fin N)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position))
    (ψ : State N q) (hψ : antisymmetric ψ) (hij : i ≠ j) :
    oneParticleContraction j f ψ = -restExchange i j (oneParticleContraction i f ψ) := by
  apply ext_inner_left ℂ
  intro w
  let v := (restExchange i j).symm w
  have hw : restExchange i j v = w := (restExchange i j).apply_symm_apply w
  rw [← hw]
  have hu : statePermutationLinearIsometryEquiv (Equiv.swap i j) ψ = -ψ :=
    simultaneousPermutation_swap_eq_neg ψ hψ i j hij
  calc
    inner ℂ (restExchange i j v) (oneParticleContraction j f ψ) =
        inner ℂ (oneParticleInsertion j f (restExchange i j v)) ψ := by
      rw [← oneParticleInsertion_adjoint, ContinuousLinearMap.adjoint_inner_right]
    _ = inner ℂ (statePermutationLinearIsometryEquiv (Equiv.swap i j)
        (oneParticleInsertion i f v)) ψ := by
      rw [statePermutationLinearIsometryEquiv_apply, simultaneousPermutation_oneParticleInsertion]
    _ = -inner ℂ (oneParticleInsertion i f v) ψ := by
      have h := (statePermutationLinearIsometryEquiv (q := q) (Equiv.swap i j)).inner_map_map
        (oneParticleInsertion i f v) ψ
      rw [hu, inner_neg_right] at h
      exact neg_eq_iff_eq_neg.mp h
    _ = -inner ℂ v (oneParticleContraction i f ψ) := by
      rw [← oneParticleInsertion_adjoint, ContinuousLinearMap.adjoint_inner_right]
    _ = inner ℂ (restExchange i j v)
        (-restExchange i j (oneParticleContraction i f ψ)) := by
      rw [inner_neg_right, LinearIsometryEquiv.inner_map_map]

/-- The concrete contraction norms agree across all particle coordinates. -/
theorem oneParticleContraction_norm_eq {N q : ℕ} (i j : Fin N)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position))
    (ψ : State N q) (hψ : antisymmetric ψ) :
    ‖oneParticleContraction j f ψ‖ = ‖oneParticleContraction i f ψ‖ := by
  by_cases hij : i = j
  · subst j
    rfl
  rw [oneParticleContraction_exchange i j f ψ hψ hij, norm_neg, LinearIsometryEquiv.norm_map]

/-- Equality of unit-vector projection norms on an antisymmetric state. -/
theorem oneParticleProjection_norm_eq {N q : ℕ} (i j : Fin N)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) (hf : ‖f‖ = 1)
    (ψ : State N q) (hψ : antisymmetric ψ) :
    ‖oneParticleProjection j f ψ‖ = ‖oneParticleProjection i f ψ‖ := by
  rw [oneParticleProjection_norm j f hf, oneParticleProjection_norm i f hf]
  exact oneParticleContraction_norm_eq i j f ψ hψ

end LiebThirring

end
