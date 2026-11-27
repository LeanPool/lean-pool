/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CauchyVelocitySupport
public import LeanPool.VacuumBellSeparation.FreeField.CauchyReality
public import LeanPool.VacuumBellSeparation.FreeField.TimeSliceCutoff

/-!
# An actual smooth compactly supported time-slice source

The literal source is `χ''u + 2χ′u_t`, using the actual Cauchy solution and
actual derivatives of the switching function. Its smoothness, reality and
compact double-cone support are proved. Identifying its one-particle vector
with the initial data is a further integral identity, not a field of this
construction or a hypothesis hidden in the definition.
-/

@[expose] public section

namespace VacuumBellSeparation

open Set
open scoped ComplexConjugate

/-- Time slice complex source. -/
noncomputable def timeSliceComplexSource (ε m : ℝ) (f g : SpatialSchwartz) (x : Spacetime) : ℂ :=
  ((deriv (deriv (timeSliceCutoff ε)) x.1 : ℝ) : ℂ) * massiveSchwartzCauchy m x.1 f g x.2 +
    2 * ((deriv (timeSliceCutoff ε) x.1 : ℝ) : ℂ) * massiveSchwartzCauchyVelocity m x.1 f g x.2

theorem contDiff_timeSliceComplexSource (ε m : ℝ) (f g : SpatialSchwartz) :
    ContDiff ℝ (⊤ : ℕ∞) (timeSliceComplexSource ε m f g) := by
  exact ((Complex.ofRealCLM.contDiff.comp
    ((contDiff_deriv_twice_timeSliceCutoff ε).comp contDiff_fst)).mul
      (contDiff_massiveSchwartzCauchy_spacetime m f g)).add
    ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      ((contDiff_deriv_timeSliceCutoff ε).comp contDiff_fst))).mul
        (contDiff_massiveSchwartzCauchyVelocity_spacetime m f g))

theorem timeSliceComplexSource_real (ε m : ℝ) (f g : SpatialSchwartz)
    (hf : spatialSchwartzConjugate f = f) (hg : spatialSchwartzConjugate g = g)
    (x : Spacetime) :
    conj (timeSliceComplexSource ε m f g x) = timeSliceComplexSource ε m f g x := by
  simp only [timeSliceComplexSource, map_add, map_mul, map_ofNat, Complex.conj_ofReal,
    massiveSchwartzCauchy_real m x.1 f g hf hg x.2,
    massiveSchwartzCauchyVelocity_real m x.1 f g hf hg x.2]

theorem timeSliceComplexSource_eq_zero_outside_box {m ε r : ℝ}
    (hm : 0 < m) (hε : 0 < ε) (hr : 0 ≤ r) (x₀ : EuclideanSpace ℝ (Fin 3))
    (f g : SpatialSchwartz) (hf : tsupport f ⊆ Metric.closedBall x₀ r)
    (hg : tsupport g ⊆ Metric.closedBall x₀ r) (x : Spacetime)
    (hx : x ∉ Icc (-ε) ε ×ˢ Metric.closedBall x₀ (r + ε)) :
    timeSliceComplexSource ε m f g x = 0 := by
  by_cases ht : x.1 ∈ Icc (-ε) ε
  · have hx' : x.2 ∉ Metric.closedBall x₀ (r + ε) := fun h => hx ⟨ht, h⟩
    have ht' : |x.1| ≤ ε := abs_le.mpr ht
    have hnorm : r + |x.1| < ‖x.2 - x₀‖ := by
      have h := hx'
      simp only [Metric.mem_closedBall, dist_eq_norm, not_le] at h
      linarith
    have hu : massiveSchwartzCauchy m x.1 f g x.2 = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have h := tsupport_massiveSchwartzCauchy_subset hm hr x.1 f g hf hg hmem
      have hle : ‖x.2 - x₀‖ ≤ r + |x.1| := by
        simpa only [Metric.mem_closedBall, dist_eq_norm] using h
      exact (not_lt_of_ge hle) hnorm
    have hv := massiveSchwartzCauchyVelocity_eq_zero_outside_cone hm hr x.1 f g hf hg hnorm
    simp only [timeSliceComplexSource, hu, hv, mul_zero, add_zero]
  · have h₁ := deriv_timeSliceCutoff_eq_zero_of_not_mem hε ht
    have h₂ : deriv (deriv (timeSliceCutoff ε)) x.1 = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun h => ht (tsupport_deriv_twice_timeSliceCutoff_subset hε h))
    simp only [timeSliceComplexSource, h₁, h₂, Complex.ofReal_zero, zero_mul, mul_zero, add_zero]

theorem tsupport_timeSliceComplexSource_subset_box {m ε r : ℝ}
    (hm : 0 < m) (hε : 0 < ε) (hr : 0 ≤ r) (x₀ : EuclideanSpace ℝ (Fin 3))
    (f g : SpatialSchwartz) (hf : tsupport f ⊆ Metric.closedBall x₀ r)
    (hg : tsupport g ⊆ Metric.closedBall x₀ r) :
    tsupport (timeSliceComplexSource ε m f g) ⊆ Icc (-ε) ε ×ˢ Metric.closedBall x₀ (r + ε) := by
  apply closure_minimal _ (isClosed_Icc.prod Metric.isClosed_closedBall)
  intro x hx
  by_contra hout
  exact hx (timeSliceComplexSource_eq_zero_outside_box hm hε hr x₀ f g hf hg x hout)

theorem hasCompactSupport_timeSliceComplexSource {m ε r : ℝ}
    (hm : 0 < m) (hε : 0 < ε) (hr : 0 ≤ r) (x₀ : EuclideanSpace ℝ (Fin 3))
    (f g : SpatialSchwartz) (hf : tsupport f ⊆ Metric.closedBall x₀ r)
    (hg : tsupport g ⊆ Metric.closedBall x₀ r) :
    HasCompactSupport (timeSliceComplexSource ε m f g) :=
  (isCompact_Icc.prod (isCompact_closedBall x₀ (r + ε))).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_timeSliceComplexSource_subset_box hm hε hr x₀ f g hf hg)

/-- Time slice test function. -/
noncomputable def timeSliceTestFunction {m ε r : ℝ}
    (hm : 0 < m) (hε : 0 < ε) (hr : 0 ≤ r) (x₀ : EuclideanSpace ℝ (Fin 3))
    (f g : SpatialSchwartz) (hf : tsupport f ⊆ Metric.closedBall x₀ r)
    (hg : tsupport g ⊆ Metric.closedBall x₀ r) : RealTestFunction :=
  ⟨fun x => (timeSliceComplexSource ε m f g x).re,
    Complex.reCLM.contDiff.comp (contDiff_timeSliceComplexSource ε m f g),
    (hasCompactSupport_timeSliceComplexSource hm hε hr x₀ f g hf hg).comp_left (by simp)⟩

theorem timeSliceTestFunction_complex_eq {m ε r : ℝ}
    (hm : 0 < m) (hε : 0 < ε) (hr : 0 ≤ r) (x₀ : EuclideanSpace ℝ (Fin 3))
    (f g : SpatialSchwartz) (hf : tsupport f ⊆ Metric.closedBall x₀ r)
    (hg : tsupport g ⊆ Metric.closedBall x₀ r)
    (hfr : spatialSchwartzConjugate f = f) (hgr : spatialSchwartzConjugate g = g) (x : Spacetime) :
    ((timeSliceTestFunction hm hε hr x₀ f g hf hg).1 x : ℂ) = timeSliceComplexSource ε m f g x :=
  Complex.conj_eq_iff_re.mp (timeSliceComplexSource_real ε m f g hfr hgr x)

/-- The actual source lies strictly inside any larger double cone satisfying
the precise radius margin `r + 2ε < R`. -/
theorem tsupport_timeSliceTestFunction_subset_doubleCone {m ε r R : ℝ}
    (hm : 0 < m) (hε : 0 < ε) (hr : 0 ≤ r) (hR : r + 2 * ε < R)
    (x₀ : EuclideanSpace ℝ (Fin 3)) (f g : SpatialSchwartz)
    (hf : tsupport f ⊆ Metric.closedBall x₀ r) (hg : tsupport g ⊆ Metric.closedBall x₀ r) :
    tsupport (timeSliceTestFunction hm hε hr x₀ f g hf hg).1 ⊆ doubleCone (0, x₀) R := by
  have hsub : tsupport (timeSliceTestFunction hm hε hr x₀ f g hf hg).1 ⊆
      tsupport (timeSliceComplexSource ε m f g) :=
    tsupport_comp_subset (g := Complex.re) (by simp) _
  intro x hx
  have hb := tsupport_timeSliceComplexSource_subset_box hm hε hr x₀ f g hf hg (hsub hx)
  have ht : |x.1| ≤ ε := abs_le.mpr hb.1
  have hs : ‖x.2 - x₀‖ ≤ r + ε := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hb.2
  change |x.1 - 0| + ‖x.2 - x₀‖ < R
  rw [sub_zero]
  linarith

end VacuumBellSeparation
