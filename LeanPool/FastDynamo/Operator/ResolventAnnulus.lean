/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Operator.PointwiseResolvent
public import LeanPool.FastDynamo.Operator.DomainPencilFredholm
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Uniform annular resolvents around a resolvent circle

A pointwise two-sided inverse on a circle puts that circle in the intrinsic
resolvent set.  When the bundled domain is complete, the intrinsic resolvent
set is open.  Compactness of the circle then gives a uniform metric
thickening contained in the resolvent set, and a sufficiently thin radial
annulus lies in that thickening.

The pointwise inverses on the resulting annulus are bundled into one
continuous resolvent family using the affine-pencil propagation formula.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Complex Metric Set

namespace HasResolventOn

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  {A : DomainOperator X D}

/-- A continuous resolver on an open radial annulus about a circle, together
with positivity conditions making the annulus two-sided. -/
structure OpenAnnulusResolvent (A : DomainOperator X D) (c : ℂ) (r : ℝ) where
  /-- The half-width of the open annulus. -/
  width : ℝ
  width_pos : 0 < width
  width_lt_radius : width < r
  /-- A continuous two-sided resolver throughout the open annulus. -/
  resolvent : HasResolventOn A
    (ball c (r + width) \ closedBall c (r - width))

/-- A resolvent on a positive-radius circle extends to a resolvent on some
open annulus around the same circle.  The width is chosen smaller
than the radius, so the inner radius remains positive. -/
noncomputable def openAnnulusResolvent {c : ℂ} {r : ℝ}
    (hCircle : HasResolventOn A (sphere c r)) (hr : 0 < r) :
    OpenAnnulusResolvent A c r := by
  have hSphereResolvent : sphere c r ⊆ A.resolventSet := by
    intro z hz
    change (A.pencil z).IsInvertible
    exact ContinuousLinearMap.IsInvertible.of_inverse
      (hCircle.right_inv z hz) (hCircle.left_inv z hz)
  have hThickeningExists :=
    (isCompact_sphere c r).exists_thickening_subset_open
      A.isOpen_resolventSet hSphereResolvent
  let δ : ℝ := Classical.choose hThickeningExists
  have hδ : 0 < δ := (Classical.choose_spec hThickeningExists).1
  have hThick : thickening δ (sphere c r) ⊆ A.resolventSet :=
    (Classical.choose_spec hThickeningExists).2
  let ε : ℝ := min (δ / 2) (r / 2)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (half_pos hδ) (half_pos hr)
  have hεδ : ε < δ := by
    exact (min_le_left (δ / 2) (r / 2)).trans_lt (half_lt_self hδ)
  have hεr : ε < r := by
    exact (min_le_right (δ / 2) (r / 2)).trans_lt (half_lt_self hr)
  have hAnnulusThick :
      ball c (r + ε) \ closedBall c (r - ε) ⊆
        thickening δ (sphere c r) := by
    intro z hz
    have hzOuter : dist z c < r + ε := mem_ball.mp hz.1
    have hzInner : r - ε < dist z c := by
      exact lt_of_not_ge (fun hle ↦ hz.2 (mem_closedBall.mpr hle))
    have hRadial : |dist z c - r| < ε := by
      rw [abs_lt]
      constructor <;> linarith
    obtain ⟨q, hqNorm, hq⟩ := Complex.exists_norm_mul_eq_self (z - c)
    let w : ℂ := c + q * (r : ℂ)
    have hw : w ∈ sphere c r := by
      rw [mem_sphere, dist_eq_norm_sub]
      simp [w, hqNorm, Complex.norm_real,
        Real.norm_of_nonneg hr.le]
    rw [Metric.mem_thickening_iff]
    refine ⟨w, hw, ?_⟩
    have hzRep : z = c + q * (‖z - c‖ : ℂ) := by
      calc
        z = c + (z - c) := by abel
        _ = c + q * (‖z - c‖ : ℂ) := by rw [hq]
    have hdist : dist z w = |‖z - c‖ - r| := by
      rw [dist_eq_norm_sub]
      conv_lhs => rw [hzRep]
      simp only [w]
      rw [show c + q * (‖z - c‖ : ℂ) - (c + q * (r : ℂ)) =
          q * ((‖z - c‖ - r : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.norm_mul, hqNorm, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
    calc
      dist z w = |‖z - c‖ - r| := hdist
      _ < ε := by simpa only [dist_eq_norm_sub] using hRadial
      _ < δ := hεδ
  have hSphereNonempty : (sphere c r).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hr.le
  let z₀ : ℂ := Classical.choose hSphereNonempty
  have hz₀ : z₀ ∈ sphere c r := Classical.choose_spec hSphereNonempty
  let hAnnulus : HasResolventOn A
      (ball c (r + ε) \ closedBall c (r - ε)) :=
    A.hasResolventOnOfPointwiseTwoSidedInverses
      z₀ (hCircle.inv z₀)
      (hCircle.left_inv z₀ hz₀) (hCircle.right_inv z₀ hz₀)
      (ball c (r + ε) \ closedBall c (r - ε)) (by
        intro z hz
        have hzInv : (A.pencil z).IsInvertible :=
          hThick (hAnnulusThick hz)
        exact ⟨(A.pencil z).inverse, hzInv.inverse_comp_self,
          hzInv.self_comp_inverse⟩)
  exact ⟨ε, hε, hεr, hAnnulus⟩

omit [CompleteSpace X] [CompleteSpace D] in
/--
Two resolvent certificates for the same pencil agree at every point lying in both of their
domains: a two-sided inverse of `A.pencil z` is unique.
-/
private theorem inv_eq_on_common_set
    {S T : Set ℂ} (hS : HasResolventOn A S) (hT : HasResolventOn A T)
    {z : ℂ} (hzS : z ∈ S) (hzT : z ∈ T) :
    hS.inv z = hT.inv z := by
  calc
    hS.inv z = (hS.inv z).comp ((A.pencil z).comp (hT.inv z)) := by
      rw [hT.right_inv z hzT, ContinuousLinearMap.comp_id]
    _ = ((hS.inv z).comp (A.pencil z)).comp (hT.inv z) := by
      rw [ContinuousLinearMap.comp_assoc]
    _ = hT.inv z := by
      rw [hS.left_inv z hzS, ContinuousLinearMap.id_comp]

/-- On a complete bundled domain, a resolvent certificate on a
positive-radius circle already has an idempotent Riesz projection; no
separate annular resolver needs to be supplied. -/
theorem rieszProjection_isIdempotentElem_of_resolventSphere
    {c : ℂ} {r : ℝ} (hCircle : HasResolventOn A (sphere c r))
    (hr : 0 < r) : IsIdempotentElem hCircle.rieszProjection := by
  let hExtension := hCircle.openAnnulusResolvent hr
  let ε := hExtension.width
  have hε : 0 < ε := hExtension.width_pos
  let hAnnulus := hExtension.resolvent
  have hSphereAnnulus : sphere c r ⊆
      ball c (r + ε) \ closedBall c (r - ε) := by
    intro z hz
    refine ⟨mem_ball.mpr ((mem_sphere.mp hz).trans_lt (by linarith)), ?_⟩
    intro hzInner
    have hle := mem_closedBall.mp hzInner
    rw [mem_sphere] at hz
    linarith
  let hRestrict : HasResolventOn A (sphere c r) :=
    hAnnulus.mono hSphereAnnulus
  have hRestrictIdempotent : IsIdempotentElem hRestrict.rieszProjection := by
    let R : ℝ := r + ε / 2
    have hrR : r < R := by
      dsimp [R]
      linarith
    have hClosedAnnulus : closedBall c R \ ball c r ⊆
        ball c (r + ε) \ closedBall c (r - ε) := by
      intro z hz
      refine ⟨mem_ball.mpr ((mem_closedBall.mp hz.1).trans_lt (by
        dsimp [R]
        linarith)), ?_⟩
      intro hzInner
      have hrle : r ≤ dist z c := le_of_not_gt (fun hzlt ↦
        hz.2 (mem_ball.mpr hzlt))
      have hinner := mem_closedBall.mp hzInner
      linarith
    have hId :=
      hAnnulus.rieszProjection_isIdempotentElem_of_isOpen_common_resolvent
        hr hrR (isOpen_ball.sdiff isClosed_closedBall) hClosedAnnulus
    simpa [hRestrict, R, mono, rieszProjection, stateResolvent] using hId
  have hProjectionEq : hCircle.rieszProjection = hRestrict.rieszProjection := by
    unfold rieszProjection
    congr 1
    apply circleIntegral.integral_congr hr.le
    intro z hz
    unfold stateResolvent
    rw [inv_eq_on_common_set hCircle hRestrict hz hz]
  rw [hProjectionEq]
  exact hRestrictIdempotent

/-- A compact Riesz projection obtained from a positive-radius resolvent
circle on a complete bundled domain has finite-dimensional range. -/
theorem finiteDimensional_rieszProjection_range_of_resolventSphere_and_isCompact
    {c : ℂ} {r : ℝ} (hCircle : HasResolventOn A (sphere c r))
    (hr : 0 < r) (hCompact : IsCompactOperator hCircle.rieszProjection) :
    FiniteDimensional ℂ hCircle.rieszProjection.toLinearMap.range :=
  hCircle.finiteDimensional_rieszProjection_range_of_isCompact hCompact
    (hCircle.rieszProjection_isIdempotentElem_of_resolventSphere hr)

end HasResolventOn

end

end FastDynamo
