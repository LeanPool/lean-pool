/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.EvolutionPointwiseDerivative

/-! # The literal Cauchy solution satisfies the massive equation pointwise -/

@[expose] public section

namespace VacuumBellSeparation

theorem hasDerivAt_massiveSchwartzCauchyVelocity_pointwise {m : ℝ} (hm : 0 < m)
    (t : ℝ) (f g : SpatialSchwartz) (x : EuclideanSpace ℝ (Fin 3)) :
    HasDerivAt (fun s => massiveSchwartzCauchyVelocity m s f g x)
      (-(massiveSchwartzPower m 2 (massiveSchwartzCauchy m t f g)) x) t := by
  have hp := (hasDerivAt_massiveSchwartzEvolution_pointwise m t
    (massiveSchwartzPower m 1 (cauchyPositiveData m f g)) x).const_mul Complex.I
  have hn := (hasDerivAt_massiveSchwartzEvolution_neg_pointwise m t
    (massiveSchwartzPower m 1 (cauchyNegativeData m f g)) x).const_mul Complex.I
  refine ((hp.sub hn).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · simp only [massiveSchwartzCauchyVelocity, sub_apply, smul_apply, smul_eq_mul,
      Pi.sub_apply]
  · simp only [← mul_assoc, Complex.I_mul_I, neg_one_mul, mul_neg, neg_neg,
      massiveSchwartzPower_add hm, show (1 : ℝ) + 1 = 2 by norm_num,
      massiveSchwartzEvolution_commute_power, massiveSchwartzCauchy_eq_phases,
      map_add, add_apply, neg_add_rev, sub_eq_add_neg, add_comm]

open Laplacian in
theorem hasDerivAt_massiveSchwartzCauchy_pointwise_kleinGordon {m : ℝ} (hm : 0 < m)
    (t : ℝ) (f g : SpatialSchwartz) (x : EuclideanSpace ℝ (Fin 3)) :
    HasDerivAt (fun s => massiveSchwartzCauchyVelocity m s f g x)
      ((Δ (massiveSchwartzCauchy m t f g)) x -
        (m ^ 2 : ℂ) * massiveSchwartzCauchy m t f g x) t := by
  simpa only [massiveSchwartzPower_two hm, sub_apply, smul_apply,
    smul_eq_mul, Complex.ofReal_pow, neg_sub] using
    hasDerivAt_massiveSchwartzCauchyVelocity_pointwise hm t f g x

end VacuumBellSeparation
