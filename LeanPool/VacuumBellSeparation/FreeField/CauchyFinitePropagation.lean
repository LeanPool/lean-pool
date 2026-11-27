/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.PlanarEnergyFlux
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Finite propagation of the literal Schwartz Cauchy solution

The proved moving-plane energy is initially zero for data supported in a
closed ball. Its positivity and monotonicity force it to remain zero. The
strictly positive massive term and the positive cutoff then give pointwise
vanishing ahead of each plane. Choosing the radial plane proves the cone
support statement. Negative times are handled by the exact time reversal of
the literal cosine/sine formula.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped InnerProductSpace

open MeasureTheory Filter LineDeriv FourierTransform
open scoped LineDeriv FourierTransform

theorem integrable_planarWeighted_norm_sq
    (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ) (f : SpatialSchwartz) :
    Integrable (fun x => planarEnergyWeight a x₀ R t x * ‖f x‖ ^ 2) := by
  have h := (SchwartzMap.pairing (innerSL ℝ) f (planarWeightedSchwartz a x₀ R t f)).integrable
    (μ := volume)
  change Integrable (fun x => ⟪f x, planarWeightedSchwartz a x₀ R t f x⟫_ℝ) at h
  simpa only [SchwartzMap.pairing_apply_apply, innerSL_apply_apply,
    planarWeightedSchwartz_apply, ← Complex.real_smul, real_inner_smul_right,
    real_inner_self_eq_norm_sq] using h

theorem planarPairing_self_eq_zero_of_support
    {a x₀ : EuclideanSpace ℝ (Fin 3)} (ha : ‖a‖ ≤ 1) {R : ℝ}
    (f : SpatialSchwartz) (hf : tsupport f ⊆ Metric.closedBall x₀ R) :
    planarPairing a x₀ R 0 f f = 0 := by
  rw [planarPairing_eq_integral]
  have hz : (fun x => planarEnergyWeight a x₀ R 0 x * ⟪f x, f x⟫_ℝ) = 0 := by
    funext x
    by_cases hx : x ∈ Metric.closedBall x₀ R
    · have hn : ‖x - x₀‖ ≤ R + 0 := by simpa only [Metric.mem_closedBall, dist_eq_norm,
        add_zero] using hx
      simp only [planarEnergyWeight_zero_of_norm_le ha hn, zero_mul, Pi.zero_apply]
    · have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hf h))
      simp only [hfx, inner_zero_left, mul_zero, Pi.zero_apply]
  rw [hz]
  change (∫ _ : EuclideanSpace ℝ (Fin 3), (0 : ℝ)) = 0
  exact integral_zero _ _

theorem planarKleinGordonEnergy_initial_zero {m : ℝ} (hm : 0 < m)
    {a x₀ : EuclideanSpace ℝ (Fin 3)} (ha : ‖a‖ ≤ 1) {R : ℝ}
    (f g : SpatialSchwartz) (hf : tsupport f ⊆ Metric.closedBall x₀ R)
    (hg : tsupport g ⊆ Metric.closedBall x₀ R) :
    planarKleinGordonEnergy a x₀ R m 0
      (massiveSchwartzCauchy m 0 f g) (massiveSchwartzCauchyVelocity m 0 f g) = 0 := by
  rw [massiveSchwartzCauchy_zero, massiveSchwartzCauchyVelocity_zero hm,
    planarKleinGordonEnergy, planarPairing_self_eq_zero_of_support ha f hf,
    planarPairing_self_eq_zero_of_support ha g hg]
  have hs : (∑ j, planarPairing a x₀ R 0 (∂_{spatialEnergyBasis j} f)
      (∂_{spatialEnergyBasis j} f)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact planarPairing_self_eq_zero_of_support ha _
      ((SchwartzMap.tsupport_lineDerivOp_subset (spatialEnergyBasis j) f).trans hf)
  rw [hs]
  ring

theorem planarPairing_self_eq_zero_of_energy_zero {m : ℝ} (hm : 0 < m)
    (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ) (u v : SpatialSchwartz)
    (he : planarKleinGordonEnergy a x₀ R m t u v = 0) :
    planarPairing a x₀ R t u u = 0 := by
  have hu := planarPairing_self_nonneg a x₀ R t u
  have hv := planarPairing_self_nonneg a x₀ R t v
  have hg : 0 ≤ ∑ j, planarPairing a x₀ R t (∂_{spatialEnergyBasis j} u)
      (∂_{spatialEnergyBasis j} u) :=
    Finset.sum_nonneg fun _ _ => planarPairing_self_nonneg _ _ _ _ _
  unfold planarKleinGordonEnergy at he
  nlinarith [sq_pos_of_pos hm]

theorem eq_zero_ahead_of_plane_of_planarPairing_zero
    {a x₀ x : EuclideanSpace ℝ (Fin 3)} {R t : ℝ} (f : SpatialSchwartz)
    (hf : planarPairing a x₀ R t f f = 0)
    (hx : R + t < ⟪a, x - x₀⟫_ℝ) : f x = 0 := by
  have hi : ∫ y, planarEnergyWeight a x₀ R t y * ‖f y‖ ^ 2 = 0 := by
    simpa only [planarPairing_eq_integral, real_inner_self_eq_norm_sq] using hf
  have hae : (fun y => planarEnergyWeight a x₀ R t y * ‖f y‖ ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun y => mul_nonneg (planarEnergyWeight_nonneg _ _ _ _ _) (sq_nonneg _))
      (integrable_planarWeighted_norm_sq a x₀ R t f)).mp hi
  have hcont : Continuous (fun y => planarEnergyWeight a x₀ R t y * ‖f y‖ ^ 2) :=
    (hasTemperateGrowth_planarEnergyWeight a x₀ R t).1.continuous.mul (f.continuous.norm.pow 2)
  have hz := congrFun (Measure.eq_of_ae_eq hae hcont continuous_const) x
  have hw := planarEnergyWeight_pos hx
  have hsq : ‖f x‖ ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_left hw.ne'
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (f x)])

/-- Actual forward-time half-space finite propagation. -/
theorem massiveSchwartzCauchy_eq_zero_ahead_of_plane {m : ℝ} (hm : 0 < m)
    {a x₀ x : EuclideanSpace ℝ (Fin 3)} (ha : ‖a‖ ≤ 1) {R t : ℝ} (ht : 0 ≤ t)
    (f g : SpatialSchwartz) (hf : tsupport f ⊆ Metric.closedBall x₀ R)
    (hg : tsupport g ⊆ Metric.closedBall x₀ R)
    (hx : R + t < ⟪a, x - x₀⟫_ℝ) : massiveSchwartzCauchy m t f g x = 0 := by
  have hle := antitone_planarKleinGordonEnergy hm ha x₀ R f g ht
  change planarKleinGordonEnergy a x₀ R m t
      (massiveSchwartzCauchy m t f g) (massiveSchwartzCauchyVelocity m t f g) ≤
    planarKleinGordonEnergy a x₀ R m 0
      (massiveSchwartzCauchy m 0 f g) (massiveSchwartzCauchyVelocity m 0 f g) at hle
  rw [planarKleinGordonEnergy_initial_zero hm ha f g hf hg] at hle
  have he := le_antisymm hle (planarKleinGordonEnergy_nonneg a x₀ R m t _ _)
  exact eq_zero_ahead_of_plane_of_planarPairing_zero _
    (planarPairing_self_eq_zero_of_energy_zero hm a x₀ R t _ _ he) hx

theorem massiveSchwartzCauchy_eq_zero_outside_forward_cone {m : ℝ} (hm : 0 < m)
    {x₀ x : EuclideanSpace ℝ (Fin 3)} {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t)
    (f g : SpatialSchwartz) (hf : tsupport f ⊆ Metric.closedBall x₀ R)
    (hg : tsupport g ⊆ Metric.closedBall x₀ R)
    (hx : R + t < ‖x - x₀‖) : massiveSchwartzCauchy m t f g x = 0 := by
  have hd : 0 < ‖x - x₀‖ := lt_of_le_of_lt (add_nonneg hR ht) hx
  let a : EuclideanSpace ℝ (Fin 3) := ‖x - x₀‖⁻¹ • (x - x₀)
  have ha : ‖a‖ ≤ 1 := by
    simp only [a, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd),
      inv_mul_cancel₀ hd.ne', le_refl]
  have hi : ⟪a, x - x₀⟫_ℝ = ‖x - x₀‖ := by
    simp only [a, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp [hd.ne']
  exact massiveSchwartzCauchy_eq_zero_ahead_of_plane hm ha ht f g hf hg (by rw [hi]; exact hx)

/-- Time reversal of the actual Cauchy solution changes only the initial velocity. -/
theorem massiveSchwartzCauchy_neg_time {m : ℝ} (hm : 0 < m) (t : ℝ)
    (f g : SpatialSchwartz) :
    massiveSchwartzCauchy m (-t) f g = massiveSchwartzCauchy m t f (-g) := by
  apply (fourierCLE ℂ SpatialSchwartz).injective
  ext ξ
  change (𝓕 (massiveSchwartzCauchy m (-t) f g)) ξ =
    (𝓕 (massiveSchwartzCauchy m t f (-g))) ξ
  have hneg : 𝓕 (-g) = -(𝓕 g) := map_neg (fourierCLE ℂ SpatialSchwartz) g
  simp only [fourier_massiveSchwartzCauchy hm, hneg, neg_apply,
    neg_mul, Real.cos_neg, Real.sin_neg, mul_neg, Complex.ofReal_neg, neg_mul]

/-- Closed cone support of the literal massive Cauchy solution, at every real
time, for actual compactly supported Schwartz initial data. -/
theorem tsupport_massiveSchwartzCauchy_subset {m : ℝ} (hm : 0 < m)
    {x₀ : EuclideanSpace ℝ (Fin 3)} {R : ℝ} (hR : 0 ≤ R) (t : ℝ)
    (f g : SpatialSchwartz) (hf : tsupport f ⊆ Metric.closedBall x₀ R)
    (hg : tsupport g ⊆ Metric.closedBall x₀ R) :
    tsupport (massiveSchwartzCauchy m t f g) ⊆ Metric.closedBall x₀ (R + |t|) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hout
  have hn : R + |t| < ‖x - x₀‖ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hout
  have hz : massiveSchwartzCauchy m t f g x = 0 := by
    by_cases ht : 0 ≤ t
    · exact massiveSchwartzCauchy_eq_zero_outside_forward_cone hm hR ht f g hf hg
        (by simpa only [abs_of_nonneg ht] using hn)
    · have ht' : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
      have hg' : tsupport (-g) ⊆ Metric.closedBall x₀ R := by simpa only [FunLike.coe_neg,
        tsupport_neg] using hg
      have hrev := massiveSchwartzCauchy_neg_time hm (-t) f g
      rw [neg_neg] at hrev
      rw [hrev]
      exact massiveSchwartzCauchy_eq_zero_outside_forward_cone hm hR ht' f (-g) hf hg'
        (by simpa only [abs_of_neg (lt_of_not_ge ht)] using hn)
  exact hx hz

end VacuumBellSeparation
