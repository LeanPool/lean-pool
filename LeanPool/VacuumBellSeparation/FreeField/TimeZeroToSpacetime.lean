/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeSliceRecovery

/-!
# Actual reverse time-slice construction for compact time-zero sources

For the physical pair `(f,g)`, choose the genuine Cauchy data `(-g,f)`.
The constructed real spacetime test function has exactly the physical
one-particle vector `f̂+iωĝ`, and lies inside the prescribed larger double
cone. This direction of the time-slice correspondence is proved from the
actual wave evolution, support theorem and one-particle integrals.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped FourierTransform
open FourierTransform

theorem tsupport_spatialSchwartz_subset (f : SpatialTestFunction) :
    tsupport (spatialSchwartz f) ⊆ tsupport f.1 :=
  tsupport_comp_subset Complex.ofReal_zero f.1

@[simp] theorem spatialSchwartzConjugate_spatialSchwartz (f : SpatialTestFunction) :
    spatialSchwartzConjugate (spatialSchwartz f) = spatialSchwartz f := by
  ext x
  simp only [spatialSchwartzConjugate_apply, spatialSchwartz_apply, Complex.conj_ofReal]

/-- Exact reverse time-slice theorem, with a quantitative support margin. -/
theorem exists_spacetimeSource_of_timeZeroSource {m r R ε : ℝ}
    (hm : 0 < m) (hr : 0 ≤ r) (hε : 0 < ε) (hR : r + 2 * ε < R)
    (x₀ : EuclideanSpace ℝ (Fin 3)) (u : TimeZeroSource)
    (hf : tsupport u.1.1 ⊆ Metric.closedBall x₀ r)
    (hg : tsupport u.2.1 ⊆ Metric.closedBall x₀ r) :
    ∃ F : RealTestFunction, tsupport F.1 ⊆ doubleCone (0, x₀) R ∧
      ∀ p, oneParticle m F p = timeZeroOneParticle m u p := by
  let f : SpatialSchwartz := -spatialSchwartz u.2
  let g : SpatialSchwartz := spatialSchwartz u.1
  have hfs : tsupport f ⊆ Metric.closedBall x₀ r := by
    simpa only [f, FunLike.coe_neg, tsupport_neg] using
      (tsupport_spatialSchwartz_subset u.2).trans hg
  have hgs : tsupport g ⊆ Metric.closedBall x₀ r :=
    (tsupport_spatialSchwartz_subset u.1).trans hf
  have hfr : spatialSchwartzConjugate f = f := by
    simp only [f, map_neg, spatialSchwartzConjugate_spatialSchwartz]
  have hgr : spatialSchwartzConjugate g = g := spatialSchwartzConjugate_spatialSchwartz u.1
  let F := timeSliceTestFunction hm hε hr x₀ f g hfs hgs
  refine ⟨F, tsupport_timeSliceTestFunction_subset_doubleCone hm hε hr hR x₀ f g hfs hgs, ?_⟩
  intro p
  let ξ : EuclideanSpace ℝ (Fin 3) := (2 * Real.pi)⁻¹ • p
  have hξ : (2 * Real.pi) • ξ = p := by
    simp only [ξ, smul_smul, mul_inv_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_smul]
  have h := oneParticle_timeSliceTestFunction hm hε hr x₀ f g hfs hgs hfr hgr ξ
  have hneg : (𝓕 (-spatialSchwartz u.2)) ξ = -(𝓕 (spatialSchwartz u.2)) ξ := by
    change (FourierTransform.fourierCLM ℂ SpatialSchwartz (-spatialSchwartz u.2)) ξ = _
    rw [map_neg, neg_apply, FourierTransform.fourierCLM_apply]
  simp only [f, g, hneg, mul_neg, sub_neg_eq_add,
    ← spatialFourier_two_pi, massiveSchwartzSymbol_one hm, hξ] at h
  exact h

/-- Any positive radius margin admits an actual compact spacetime source. -/
theorem exists_spacetimeSource_of_timeZeroSource_radius_lt {m r R : ℝ}
    (hm : 0 < m) (hr : 0 ≤ r) (hR : r < R)
    (x₀ : EuclideanSpace ℝ (Fin 3)) (u : TimeZeroSource)
    (hf : tsupport u.1.1 ⊆ Metric.closedBall x₀ r)
    (hg : tsupport u.2.1 ⊆ Metric.closedBall x₀ r) :
    ∃ F : RealTestFunction, tsupport F.1 ⊆ doubleCone (0, x₀) R ∧
      ∀ p, oneParticle m F p = timeZeroOneParticle m u p := by
  apply exists_spacetimeSource_of_timeZeroSource hm hr
    (show 0 < (R - r) / 4 by linarith) (show r + 2 * ((R - r) / 4) < R by linarith)
    x₀ u hf hg

end VacuumBellSeparation
