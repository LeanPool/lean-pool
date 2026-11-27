/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeSliceBall

/-!
# Actual real spatial test functions from compact Cauchy evolution

Finite propagation makes each fixed-time evolved compact datum a genuine
compact test function. The complexification is exactly the original Schwartz
solution, by its proved reality. These are the time-zero labels used by the
forward time-slice construction.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped ComplexConjugate FourierTransform
open FourierTransform

/-- Real Schwartz spatial test. -/
noncomputable def realSchwartzSpatialTest (f : SpatialSchwartz)
    (hc : HasCompactSupport f) : SpatialTestFunction :=
  ⟨fun x => (f x).re, Complex.reCLM.contDiff.comp (f.smooth ⊤),
    hc.comp_left (by simp)⟩

theorem spatialSchwartz_realSchwartzSpatialTest (f : SpatialSchwartz)
    (hc : HasCompactSupport f) (hr : spatialSchwartzConjugate f = f) :
    spatialSchwartz (realSchwartzSpatialTest f hc) = f := by
  ext x
  exact Complex.conj_eq_iff_re.mp (DFunLike.congr_fun hr x)

theorem tsupport_realSchwartzSpatialTest_subset (f : SpatialSchwartz)
    (hc : HasCompactSupport f) :
    tsupport (realSchwartzSpatialTest f hc).1 ⊆ tsupport f :=
  tsupport_comp_subset (g := Complex.re) (by simp) f

theorem hasCompactSupport_massiveSchwartzCauchy {m : ℝ} (hm : 0 < m)
    (t : ℝ) (f g : SpatialSchwartz)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (massiveSchwartzCauchy m t f g) := by
  obtain ⟨r, hr, hs⟩ := (hf.union hg).isBounded.subset_ball_lt 0
    (0 : EuclideanSpace ℝ (Fin 3))
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (r + |t|)).of_isClosed_subset
    (isClosed_tsupport _)
  exact tsupport_massiveSchwartzCauchy_subset hm hr.le t f g
    ((Set.subset_union_left.trans hs).trans Metric.ball_subset_closedBall)
    ((Set.subset_union_right.trans hs).trans Metric.ball_subset_closedBall)

/-- Spatial Cauchy test. -/
noncomputable def spatialCauchyTest {m : ℝ} (hm : 0 < m) (t : ℝ)
    (f g : SpatialTestFunction) : SpatialTestFunction :=
  realSchwartzSpatialTest (massiveSchwartzCauchy m t (spatialSchwartz f) (spatialSchwartz g))
    (hasCompactSupport_massiveSchwartzCauchy hm t _ _
      (f.2.2.comp_left Complex.ofReal_zero) (g.2.2.comp_left Complex.ofReal_zero))

theorem spatialSchwartz_spatialCauchyTest {m : ℝ} (hm : 0 < m) (t : ℝ)
    (f g : SpatialTestFunction) :
    spatialSchwartz (spatialCauchyTest hm t f g) =
      massiveSchwartzCauchy m t (spatialSchwartz f) (spatialSchwartz g) := by
  apply spatialSchwartz_realSchwartzSpatialTest
  rw [spatialSchwartzConjugate_massiveSchwartzCauchy,
    spatialSchwartzConjugate_spatialSchwartz, spatialSchwartzConjugate_spatialSchwartz]

theorem tsupport_spatialCauchyTest_subset {m r : ℝ} (hm : 0 < m) (hr : 0 ≤ r)
    (t : ℝ) (x₀ : EuclideanSpace ℝ (Fin 3)) (f g : SpatialTestFunction)
    (hf : tsupport f.1 ⊆ Metric.closedBall x₀ r)
    (hg : tsupport g.1 ⊆ Metric.closedBall x₀ r) :
    tsupport (spatialCauchyTest hm t f g).1 ⊆ Metric.closedBall x₀ (r + |t|) :=
  (tsupport_realSchwartzSpatialTest_subset _ _).trans
    (tsupport_massiveSchwartzCauchy_subset hm hr t _ _
      ((tsupport_spatialSchwartz_subset f).trans hf)
      ((tsupport_spatialSchwartz_subset g).trans hg))

@[simp] theorem spatialSchwartz_zero : spatialSchwartz (0 : SpatialTestFunction) = 0 := by
  ext x
  change ((0 : ℝ) : ℂ) = 0
  rfl

/-- Propagating a real spatial slice through time gives this actual pair
of compact real time-zero sources. -/
noncomputable def evolvedSpatialSource {m : ℝ} (hm : 0 < m) (t : ℝ)
    (f : SpatialTestFunction) : TimeZeroSource :=
  (spatialCauchyTest hm t f 0, spatialCauchyTest hm t 0 f)

theorem timeZeroOneParticle_evolvedSpatialSource {m : ℝ} (hm : 0 < m)
    (t : ℝ) (f : SpatialTestFunction) (ξ : EuclideanSpace ℝ (Fin 3)) :
    timeZeroOneParticle m (evolvedSpatialSource hm t f) ((2 * Real.pi) • ξ) =
      massiveEvolutionPhase m t ξ * (𝓕 (spatialSchwartz f)) ξ := by
  have hw : (dispersion m ((2 * Real.pi) • ξ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (by unfold dispersion; positivity))
  have hF0 : 𝓕 (0 : SpatialSchwartz) = 0 := by
    change FourierTransform.fourierCLM ℂ SpatialSchwartz 0 = 0
    exact map_zero _
  simp only [timeZeroOneParticle, evolvedSpatialSource, spatialFourier_two_pi,
    spatialSchwartz_spatialCauchyTest, fourier_massiveSchwartzCauchy hm,
    spatialSchwartz_zero, hF0, zero_apply, mul_zero, add_zero, zero_add]
  rw [massiveEvolutionPhase, massiveSchwartzSymbol_one hm, Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  field_simp [hw]

end VacuumBellSeparation
