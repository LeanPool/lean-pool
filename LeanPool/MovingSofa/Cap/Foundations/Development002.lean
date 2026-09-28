/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Analysis.Foundations.Development003
public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development002
public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development001
public import LeanPool.MovingSofa.Infrastructure.MathlibExtensions.Foundations.Development001


public import LeanPool.MovingSofa.Geometry.Foundations.Development003
/-!
# Moving sofa: related mathematical developments

* `Cap.Contacts`.
* `Cap.ArmCoordinates`.
* `Cap.ContactIdentities`.
* `Cap.HalfPlanes`.
* `Cap.FanProjection`.
* `Cap.HallwayQuadrant`.
* `Cap.LowerNormalMeasure`.
* `Cap.ReflectionGeometry`.
* `Cap.SupportIntersections`.
* `Cap.TopCorner`.
* `Cap.Vertical`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Contacts
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Width in a normal direction, for geometric use on nonempty compact sets. -/
def directionalWidth (s : Set Point) (t : Real.Angle) : ℝ :=
  supportValue s t + supportValue s (t + ((Real.pi : ℝ) : Real.Angle))

/-- The positive/negative contacts at the two outer supporting walls. -/
def capVertices {ω : ℝ} (K : CapSpace ω) (t : ℝ) : (Point × Point) × (Point × Point) :=
  (edgeVertices K.1 (t : Real.Angle),
    edgeVertices K.1 ((t + Real.pi / 2 : ℝ) : Real.Angle))

/-- The positive/negative right and left tangent arm lengths of a right-angle cap. -/
def tangentArmLengths (K : RightAngleCapSpace) (t : ℝ) : (ℝ × ℝ) × (ℝ × ℝ) :=
  let y := (rotatingHallwayParts (K.1 : Set Point) (t : Real.Angle)).outerCorner
  let v := capVertices K t
  ((inner ℝ (y - v.1.1) (tangentVector (t : Real.Angle)),
    inner ℝ (y - v.1.2) (tangentVector (t : Real.Angle))),
    (inner ℝ (y - v.2.1) (normalVector (t : Real.Angle)),
      inner ℝ (y - v.2.2) (normalVector (t : Real.Angle))))

/-- The open inner quadrant clipped by the fan. -/
def capWedge {ω : ℝ} (K : CapSpace ω) (t : ℝ) : Set Point :=
  capFan ω ∩ (rotatingHallwayParts (K.1 : Set Point) (t : Real.Angle)).innerQuadrant

/-- The two inner-wall intersections with the lower fan boundary lines. -/
def wedgeEndpoints {ω : ℝ} (K : CapSpace ω) (t : ℝ) : Point × Point :=
  (((supportValue K.1 (t : Real.Angle) - 1) / Real.cos t) • normalVector 0,
    ((supportValue K.1 ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
      Real.cos (ω - t)) • tangentVector (ω : Real.Angle))

/-- Signed right and left gaps between the wedge endpoints and bottom cap contacts. -/
def wedgeGaps {ω : ℝ} (K : CapSpace ω) (t : ℝ) : ℝ × ℝ :=
  (inner ℝ ((capVertices K 0).1.2 - (wedgeEndpoints K t).1) (normalVector 0),
    inner ℝ ((capVertices K ω).2.1 - (wedgeEndpoints K t).2)
      (tangentVector (ω : Real.Angle)))

/-- The selected short boundary arc, including only the specified endpoints. -/
def convexBoundaryArc (K : ConvexBody Point) (a b : ℝ) : Set Point :=
  {(edgeVertices K (a : Real.Angle)).1} ∪
    (⋃ t ∈ Set.Ioo a b, exposedEdge K (t : Real.Angle)) ∪
    {(edgeVertices K (b : Real.Angle)).2}

/-- The right wedge gap in support-function coordinates. -/
theorem wedgeGaps_fst_eq_supportValue {ω : ℝ} (K : CapSpace ω) (t : ℝ) :
    (wedgeGaps K t).1 = supportValue K.val (0 : Real.Angle) -
      (supportValue K.val (t : Real.Angle) - 1) / Real.cos t := by
  have hA := (edgeVertices_snd_mem K.val (0 : Real.Angle)).2
  change inner ℝ (capVertices K 0).1.2 (normalVector (0 : Real.Angle)) =
    supportValue K.val (0 : Real.Angle) at hA
  simp only [wedgeGaps, wedgeEndpoints, inner_sub_left, real_inner_smul_left, hA]
  have hu0 : inner ℝ (normalVector (0 : Real.Angle))
      (normalVector (0 : Real.Angle)) = 1 := by
    rw [← Real.Angle.coe_zero]
    exact inner_normalVector_self 0
  rw [hu0]
  ring

/-- The left wedge gap in support-function coordinates. -/
theorem wedgeGaps_snd_eq_supportValue {ω : ℝ} (K : CapSpace ω)
    (t : ℝ) :
    (wedgeGaps K t).2 =
      supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
        (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos (ω - t) := by
  have hC := (edgeVertices_fst_mem K.val
    ((ω + Real.pi / 2 : ℝ) : Real.Angle)).2
  change inner ℝ (capVertices K ω).2.1
      (normalVector ((ω + Real.pi / 2 : ℝ) : Real.Angle)) =
    supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) at hC
  simp only [normalVector, frame, Real.Angle.coe_add, Real.Angle.cos_add_pi_div_two,
    Real.Angle.sin_coe, Real.Angle.sin_add_pi_div_two, Real.Angle.cos_coe] at hC
  change inner ℝ (capVertices K ω).2.1 (tangentVector (ω : Real.Angle)) =
    supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) at hC
  simp only [wedgeGaps, wedgeEndpoints, inner_sub_left,
    real_inner_smul_left, hC]
  rw [inner_tangentVector_self]
  ring

/-- The right wedge endpoint lies on the horizontal axis, at the horizontal intercept of the right
inner wall. -/
theorem wedgeEndpoints_fst_coords {ω : ℝ} (K : CapSpace ω) (t : ℝ) :
    (wedgeEndpoints K t).1 0 = (supportValue K.val (t : Real.Angle) - 1) / Real.cos t ∧
      (wedgeEndpoints K t).1 1 = 0 := by
  constructor <;> simp [wedgeEndpoints, normalVector, frame]

/-- For a right-angle cap the left wedge endpoint also lies on the horizontal axis, at the
horizontal intercept of the left inner wall. -/
theorem wedgeEndpoints_snd_coords (K : RightAngleCapSpace) (t : ℝ) :
    (wedgeEndpoints K t).2 0 =
        -((supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) / Real.sin t) ∧
      (wedgeEndpoints K t).2 1 = 0 := by
  constructor <;> simp [wedgeEndpoints, tangentVector, frame, Real.cos_pi_div_two_sub]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Arm Coordinates
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- Express the two positive arm lengths through support and moving-frame coordinates. -/
theorem tangentArmLengths_positive_frame (K : RightAngleCapSpace) (t : ℝ) :
    (tangentArmLengths K t).1.1 =
        supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) -
          inner ℝ (edgeVertices K.val (t : Real.Angle)).1
            (tangentVector (t : Real.Angle)) ∧
    (tangentArmLengths K t).2.1 =
        inner ℝ (edgeVertices K.val (t : Real.Angle)).1
            (normalVector (t : Real.Angle)) +
          inner ℝ (edgeVertices K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1
            (tangentVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) := by
  have hnn := inner_normalVector_self t
  have htt := inner_tangentVector_self t
  have hnt := inner_normalVector_tangentVector t
  have htn : inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (t : Real.Angle)) = 0 := by
    rw [real_inner_comm, hnt]
  have hA := (edgeVertices_fst_mem K.val (t : Real.Angle)).2
  simp only [tangentArmLengths, capVertices, outerCorner_eq_support_sum,
    inner_sub_left, inner_add_left, real_inner_smul_left, hnn, htt, hnt, htn]
  rw [hA, tangentVector_add_pi_div_two]
  simp [real_inner_comm]
  ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Contact Identities
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

theorem capTangentArm_identities (K : RightAngleCapSpace) (t : ℝ) :
    (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner =
      (capVertices K t).1.1 + (tangentArmLengths K t).1.1 • tangentVector (t : Real.Angle) ∧
    (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner =
      (capVertices K t).1.2 + (tangentArmLengths K t).1.2 • tangentVector (t : Real.Angle) ∧
    (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner =
      (capVertices K t).2.1 + (tangentArmLengths K t).2.1 • normalVector (t : Real.Angle) ∧
    (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner =
      (capVertices K t).2.2 + (tangentArmLengths K t).2.2 • normalVector (t : Real.Angle) := by
  have hrot : rotationMap (t : Real.Angle) (!₂[1, 1] : Point) =
      normalVector (t : Real.Angle) + tangentVector (t : Real.Angle) := by
    unfold rotationMap
    rw [Orientation.rotation_apply, rightAngleRotation_apply]
    ext i
    fin_cases i <;> simp [normalVector, tangentVector, frame]
    ring
  have hy : (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner =
      supportValue K.val (t : Real.Angle) • normalVector (t : Real.Angle) +
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) • tangentVector (t : Real.Angle) := by
    simp only [rotatingHallwayParts, supportingPlacement, hallwayParts, hrot, Real.Angle.coe_add]
    module
  have hnn : inner ℝ (normalVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = 1 := by
    rw [PiLp.inner_apply]
    simp [normalVector, frame, Fin.sum_univ_two, Real.cos_sq_add_sin_sq]
  have htt : inner ℝ (tangentVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 1 := by
    rw [PiLp.inner_apply]
    simp [tangentVector, frame, Fin.sum_univ_two, Real.sin_sq_add_cos_sq]
  have hnt : inner ℝ (normalVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 0 := by
    simp [normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have htn : inner ℝ (tangentVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = 0 := by
    rw [real_inner_comm, hnt]
  have hA (a b c : ℝ) :
      a • normalVector (t : Real.Angle) + b • tangentVector (t : Real.Angle) =
      (a • normalVector (t : Real.Angle) + c • tangentVector (t : Real.Angle)) +
        inner ℝ ((a • normalVector (t : Real.Angle) + b • tangentVector (t : Real.Angle)) -
          (a • normalVector (t : Real.Angle) + c • tangentVector (t : Real.Angle)))
          (tangentVector (t : Real.Angle)) • tangentVector (t : Real.Angle) := by
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left, hnt, htt]
    module
  have hC (a b c : ℝ) :
      a • normalVector (t : Real.Angle) + b • tangentVector (t : Real.Angle) =
      (b • tangentVector (t : Real.Angle) + c • -normalVector (t : Real.Angle)) +
        inner ℝ ((a • normalVector (t : Real.Angle) + b • tangentVector (t : Real.Angle)) -
          (b • tangentVector (t : Real.Angle) + c • -normalVector (t : Real.Angle)))
          (normalVector (t : Real.Angle)) • normalVector (t : Real.Angle) := by
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left, inner_neg_left, hnn, htn]
    module
  have hv : tangentVector ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle)) =
      -normalVector (t : Real.Angle) := by
    ext i
    fin_cases i <;> simp [normalVector, tangentVector, frame,
      Real.Angle.sin_add_pi_div_two, Real.Angle.cos_add_pi_div_two]
  simp only [tangentArmLengths, hy, capVertices, edgeVertices]
  refine ⟨hA _ _ _, hA _ _ _, ?_, ?_⟩ <;>
    simp only [Real.Angle.coe_add, normalVector_add_pi_div_two, hv] <;>
    exact hC _ _ _

theorem surfaceAreaMeasure_atom_length (K : ConvexBody Point) (t : Real.Angle) :
    surfaceAreaMeasure K {t} = Measure.hausdorffMeasure 1 (exposedEdge K t) ∧
    surfaceAreaMeasure K {t} = ENNReal.ofReal (dist (edgeVertices K t).1 (edgeVertices K t).2) ∧
    (edgeVertices K t).1 = (edgeVertices K t).2 +
      (surfaceAreaMeasure K {t}).toReal • tangentVector t := by
  induction t using Real.Angle.induction_on with
  | _ t =>
    have hface : surfaceAreaMeasure K {(t : Real.Angle)} =
        Measure.hausdorffMeasure 1 (exposedEdge K (t : Real.Angle)) := by
      have h := (surfaceAreaMeasure_face_union K).2.2.2.2
        {(t : Real.Angle)} (measurableSet_singleton _) (Or.inr
          ⟨t, t, le_rfl, by linarith [Real.pi_pos], by simp⟩)
      simpa using h
    have hlength : surfaceAreaMeasure K {(t : Real.Angle)} =
        ENNReal.ofReal (dist (edgeVertices K (t : Real.Angle)).1
          (edgeVertices K (t : Real.Angle)).2) := by
      rw [hface, exposedEdge_eq_segment_edgeVertices, hausdorffMeasure_segment,
        edist_dist, dist_comm]
    refine ⟨hface, hlength, ?_⟩
    let S := (fun p ↦ inner ℝ p (tangentVector (t : Real.Angle))) ''
      exposedEdge K (t : Real.Angle)
    have hcompact : IsCompact S := (isCompact_exposedEdge K _).image
      (continuous_id.inner continuous_const)
    have hnonneg : 0 ≤ sSup S - sInf S := sub_nonneg.mpr
      (csInf_le_csSup ((exposedEdge_nonempty K _).image _) hcompact.bddBelow hcompact.bddAbove)
    have hdiff : (edgeVertices K (t : Real.Angle)).1 -
        (edgeVertices K (t : Real.Angle)).2 =
        (sSup S - sInf S) • tangentVector (t : Real.Angle) := by
      simp only [edgeVertices, S]
      module
    have hnorm : ‖tangentVector (t : Real.Angle)‖ = 1 := by
      have h := inner_tangentVector_self t
      rw [real_inner_self_eq_norm_sq] at h
      nlinarith [norm_nonneg (tangentVector (t : Real.Angle))]
    have hdist : dist (edgeVertices K (t : Real.Angle)).1
        (edgeVertices K (t : Real.Angle)).2 = sSup S - sInf S := by
      rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg,
        hnorm, mul_one]
    rw [hlength, ENNReal.toReal_ofReal dist_nonneg, hdist]
    exact (sub_eq_iff_eq_add.mp hdiff).trans (add_comm _ _)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Half Planes
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- A finite set of allowed normals gives a finite supporting-half-plane representation. -/
theorem HasHalfPlaneRepresentation.finite_constraints
    {K : ConvexBody Point} {N : Set Real.Angle} (hN : N.Finite)
    (hK : HasHalfPlaneRepresentation K N) :
    ∃ constraints : Set (Real.Angle × ℝ), constraints.Finite ∧
      (∀ c ∈ constraints, c.1 ∈ N) ∧
      (K : Set Point) = ⋂ c ∈ constraints, normalHalfPlane c.1 c.2 false false := by
  obtain ⟨C, hC, hKC⟩ := hK
  refine ⟨(fun t ↦ (t, supportValue K t)) '' N, hN.image _, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact ht
  · ext x
    simp only [Set.mem_iInter]
    constructor
    · intro hx c hc
      obtain ⟨t, ht, rfl⟩ := hc
      change inner ℝ x (normalVector t) ≤ supportValue K t
      exact le_csSup ((K.isCompact.image
        (continuous_inner.comp (continuous_id.prodMk continuous_const))).bddAbove)
        ⟨x, hx, rfl⟩
    · intro hx
      rw [hKC]
      simp only [Set.mem_iInter]
      intro c hc
      have hxs := hx (c.1, supportValue K c.1) ⟨c.1, hC c hc, rfl⟩
      change inner ℝ x (normalVector c.1) ≤ supportValue K c.1 at hxs
      change inner ℝ x (normalVector c.1) ≤ c.2
      apply hxs.trans
      apply csSup_le (K.nonempty.image _)
      rintro z ⟨p, hp, rfl⟩
      rw [hKC] at hp
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hp c) hc

/-- Translation preserves a half-plane representation's allowed normals. -/
theorem HasHalfPlaneRepresentation.translate {K : ConvexBody Point}
    {N : Set Real.Angle} (hK : HasHalfPlaneRepresentation K N) (v : Point) :
    HasHalfPlaneRepresentation (ConvexBody.translate K v) N := by
  obtain ⟨C, hC, hKC⟩ := hK
  refine ⟨(fun c ↦ (c.1, c.2 + inner ℝ v (normalVector c.1))) '' C, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact hC c hc
  · ext x
    simp only [ConvexBody.translate, Set.mem_image, Set.mem_iInter]
    constructor
    · rintro ⟨y, hy, rfl⟩ c ⟨d, hd, rfl⟩
      change inner ℝ (y + v) (normalVector d.1) ≤
        d.2 + inner ℝ v (normalVector d.1)
      rw [inner_add_left]
      have hmem := Set.mem_iInter.mp (Set.mem_iInter.mp (hKC ▸ hy) d) hd
      change inner ℝ y (normalVector d.1) ≤ d.2 at hmem
      simpa [add_comm] using add_le_add_right hmem (inner ℝ v (normalVector d.1))
    · intro hx
      refine ⟨x - v, ?_, by simp⟩
      rw [hKC]
      simp only [Set.mem_iInter]
      intro c hc
      have h := hx (c.1, c.2 + inner ℝ v (normalVector c.1)) ⟨c, hc, rfl⟩
      change inner ℝ x (normalVector c.1) ≤
        c.2 + inner ℝ v (normalVector c.1) at h
      change inner ℝ (x - v) (normalVector c.1) ≤ c.2
      rw [inner_sub_left]
      linarith

/-- A normalized cap is contained in its lower fan. -/
theorem CapSpace.subset_capFan {ω : ℝ} (K : CapSpace ω) :
    (K.val : Set Point) ⊆ capFan ω := by
  intro p hp
  constructor
  · change 0 ≤ inner ℝ p (normalVector (ω : Real.Angle))
    have h := inner_le_supportValue K.val hp ((ω + Real.pi : ℝ) : Real.Angle)
    rw [K.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right] at h
    linarith
  · change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
    have h := inner_le_supportValue K.val hp ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    have hang : (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) =
        ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
      congr 1
      ring
    rw [K.property.2.2.2.2.2.1, ← hang] at h
    rw [normalVector_add_pi, inner_neg_right] at h
    linarith

/-- Fan membership and strict upper support inequalities imply cap membership. -/
theorem CapSpace.mem_of_mem_capFan_of_lt_supportValue {ω : ℝ}
    (K : CapSpace ω) {p : Point} (hp : p ∈ capFan ω)
    (hupper : ∀ t ∈ Set.Icc 0 (ω + Real.pi / 2),
      inner ℝ p (normalVector (t : Real.Angle)) < supportValue K.val (t : Real.Angle)) :
    p ∈ (K.val : Set Point) := by
  obtain ⟨C, hCN, hKC⟩ := K.property.2.2.2.2.2.2
  rw [hKC]
  simp only [Set.mem_iInter]
  intro c hc
  have hsupport : supportValue K.val c.1 ≤ c.2 := by
    apply supportValue_le_of_subset_normalHalfPlane
    intro q hq
    rw [hKC] at hq
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hq c) hc
  rcases hCN c hc with hcupper | hclower
  · obtain ⟨t, ht, heq⟩ := hcupper
    rw [← heq] at hsupport ⊢
    have htI : t ∈ Set.Icc 0 (ω + Real.pi / 2) := by
      rcases ht with ht | ht
      · exact ⟨ht.1, ht.2.trans (le_add_of_nonneg_right (by positivity))⟩
      · exact ⟨(by positivity : 0 ≤ Real.pi / 2).trans ht.1, ht.2⟩
    change inner ℝ p (normalVector (t : Real.Angle)) ≤ c.2
    exact (hupper t htI).le.trans hsupport
  · rcases hclower with hclower | hclower
    · rw [hclower] at hsupport ⊢
      change inner ℝ p (normalVector ((ω + Real.pi : ℝ) : Real.Angle)) ≤ c.2
      rw [normalVector_add_pi, inner_neg_right]
      have hpω := hp.1
      change 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)) at hpω
      rw [K.property.2.2.2.2.1] at hsupport
      linarith [hsupport]
    · rw [hclower] at hsupport ⊢
      have hang : (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) =
          ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
        congr 1
        ring
      change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ c.2
      rw [← hang, normalVector_add_pi, inner_neg_right]
      have hpT := hp.2
      change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hpT
      rw [K.property.2.2.2.2.2.1] at hsupport
      linarith [hsupport]

/-- A normalized cap lies in the intersection of its two unit strips. -/
theorem CapSpace.subset_stripParallelogram {ω : ℝ} (K : CapSpace ω) :
    (K.val : Set Point) ⊆ (stripParallelogram ω).1 := by
  intro p hp
  have hlower := inner_le_supportValue K.val hp ((ω + Real.pi : ℝ) : Real.Angle)
  have hbottom := inner_le_supportValue K.val hp ((3 * Real.pi / 2 : ℝ) : Real.Angle)
  rw [K.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right] at hlower
  rw [K.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two] at hbottom
  have hupper := inner_le_supportValue K.val hp ((Real.pi / 2 : ℝ) : Real.Angle)
  have hright := inner_le_supportValue K.val hp (ω : Real.Angle)
  rw [K.property.2.2.2.1] at hupper
  rw [K.property.2.2.1] at hright
  rw [mem_stripParallelogram_iff]
  have hlo : 0 ≤ p 1 := by linarith
  have hhi : p 1 ≤ 1 := by
    simpa [normalVector, frame, PiLp.inner_apply] using hupper
  exact ⟨⟨hlo, hhi⟩, by linarith, hright⟩

/-- A half-plane representation can be tightened at every allowed normal. -/
theorem HasHalfPlaneRepresentation.eq_iInter_supportValue {K : ConvexBody Point}
    {N : Set Real.Angle} (hK : HasHalfPlaneRepresentation K N) :
    (K : Set Point) = ⋂ t ∈ N, normalHalfPlane t (supportValue K t) false false := by
  obtain ⟨C, hCN, hKC⟩ := hK
  ext p
  simp only [Set.mem_iInter]
  constructor
  · intro hp t _
    exact inner_le_supportValue K hp t
  · intro hp
    rw [hKC]
    simp only [Set.mem_iInter]
    intro c hc
    have ht := hp c.1 (hCN c hc)
    change inner ℝ p (normalVector c.1) ≤ c.2
    apply ht.trans
    apply csSup_le (K.nonempty.image _)
    rintro _ ⟨q, hq, rfl⟩
    rw [hKC] at hq
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hq c) hc

/-- A fan point satisfying all upper supporting inequalities belongs to the cap. -/
theorem CapSpace.mem_of_mem_capFan_of_le_supportValue {ω : ℝ}
    (K : CapSpace ω) {p : Point} (hp : p ∈ capFan ω)
    (hupper : ∀ t ∈ capUpperAngles ω,
      inner ℝ p (normalVector (t : Real.Angle)) ≤ supportValue K.val (t : Real.Angle)) :
    p ∈ (K.val : Set Point) := by
  rw [K.property.2.2.2.2.2.2.eq_iInter_supportValue]
  simp only [Set.mem_iInter]
  intro a ha
  rcases ha with ⟨t, ht, rfl⟩ | ha
  · exact hupper t ht
  rcases ha with rfl | rfl
  · change inner ℝ p (normalVector ((ω + Real.pi : ℝ) : Real.Angle)) ≤
      supportValue K.val ((ω + Real.pi : ℝ) : Real.Angle)
    rw [K.property.2.2.2.2.1]
    rw [normalVector_add_pi, inner_neg_right]
    exact neg_nonpos.mpr hp.1
  · have hang : ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
        (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) := by
      congr 1
      ring
    change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤
      supportValue K.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.property.2.2.2.2.2.1]
    rw [hang, normalVector_add_pi, inner_neg_right]
    exact neg_nonpos.mpr hp.2

/-- Upper support bounds supplied by the two unit-height constraints of a cap. -/
theorem CapSpace.supportValue_upper_bounds {ω t : ℝ} (K : CapSpace ω)
    (ht : t ∈ Set.Ioo 0 ω) :
    supportValue K.val (t : Real.Angle) ≤
        Real.cos t * supportValue K.val (0 : Real.Angle) + Real.sin t ∧
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) ≤
        Real.sin (ω - t) + Real.cos (ω - t) *
          supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) := by
  have hcost : 0 ≤ Real.cos t := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_le K.property.2.1⟩).le
  have hsint : 0 ≤ Real.sin t := (Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [ht.2, K.property.2.1, Real.pi_pos])).le
  have hcosδ : 0 ≤ Real.cos (ω - t) := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [sub_pos.mpr ht.2, Real.pi_pos],
      by linarith [ht.1, K.property.2.1]⟩).le
  have hsinδ : 0 ≤ Real.sin (ω - t) := (Real.sin_pos_of_pos_of_lt_pi
    (sub_pos.mpr ht.2) (by linarith [ht.1, K.property.2.1, Real.pi_pos])).le
  constructor
  · apply csSup_le (K.val.nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    have hx := inner_le_supportValue K.val hp (0 : Real.Angle)
    have hy := inner_le_supportValue K.val hp ((Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.property.2.2.2.1] at hy
    simp [normalVector, frame, PiLp.inner_apply] at hx hy ⊢
    nlinarith
  · apply csSup_le (K.val.nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    have hu := inner_le_supportValue K.val hp (ω : Real.Angle)
    have hv := inner_le_supportValue K.val hp
      ((ω + Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.property.2.2.1] at hu
    have hvec : normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle) =
        Real.sin (ω - t) • normalVector (ω : Real.Angle) +
          Real.cos (ω - t) • tangentVector (ω : Real.Angle) := by
      have h := normalVector_add_real ω (Real.pi / 2 - (ω - t))
      rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub] at h
      simpa only [show ω + (Real.pi / 2 - (ω - t)) = t + Real.pi / 2 by ring] using h
    change inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≤ _
    rw [hvec, inner_add_right, inner_smul_right, inner_smul_right]
    have hv' : inner ℝ p (tangentVector (ω : Real.Angle)) ≤
        supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) := by
      simpa [normalVector, tangentVector, frame, Real.Angle.cos_add_pi_div_two,
        Real.Angle.sin_add_pi_div_two] using hv
    nlinarith

/-- Every point of a cap lies above the horizontal base line. -/
theorem CapSpace.inner_normalVector_pi_div_two_nonneg {ω : ℝ} (K : CapSpace ω) {q : Point}
    (hq : q ∈ (K.1 : Set Point)) :
    0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) := (K.subset_capFan hq).2

/-- Lowering a point of a right-angle cap onto the base line keeps it inside the cap: every
upper normal of such a cap has nonnegative vertical component, so no upper constraint is
tightened, and the two base constraints of the fan coincide here and hold with equality. -/
theorem CapSpace.base_projection_mem (K : CapSpace (Real.pi / 2)) {q : Point}
    (hq : q ∈ (K.val : Set Point)) :
    q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) ∈ (K.val : Set Point) := by
  have hq1 : 0 ≤ q 1 := by
    simpa only [inner_normalVector_pi_div_two] using K.inner_normalVector_pi_div_two_nonneg hq
  have hinner (s : ℝ) : inner ℝ (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      (normalVector (s : Real.Angle)) =
      inner ℝ q (normalVector (s : Real.Angle)) - q 1 * Real.sin s := by
    rw [inner_sub_left, real_inner_smul_left, inner_normalVector_normalVector,
      Real.cos_pi_div_two_sub]
  have hbase : inner ℝ (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    rw [hinner, inner_normalVector_pi_div_two, Real.sin_pi_div_two, mul_one, sub_self]
  refine K.mem_of_mem_capFan_of_le_supportValue ⟨?_, ?_⟩ ?_
  · change 0 ≤ inner ℝ _ (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
    rw [hbase]
  · change 0 ≤ inner ℝ _ (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
    rw [hbase]
  · intro s hs
    have hs' : 0 ≤ s ∧ s ≤ Real.pi := by
      rcases hs with hs | hs
      · exact ⟨hs.1, by linarith [hs.2, Real.pi_pos]⟩
      · exact ⟨by linarith [hs.1, Real.pi_pos], by linarith [hs.2]⟩
    have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs'.1 hs'.2
    rw [hinner]
    linarith [mul_nonneg hq1 hsin, inner_le_supportValue K.val hq (s : Real.Angle)]

/-- The top supporting line of a right-angle cap is the horizontal line of height one, so every
point attaining the support value at the vertical normal has height one. -/
theorem CapSpace.apply_one_eq_one (K : CapSpace (Real.pi / 2)) {p : Point}
    (hp : inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue (K.val : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle)) : p 1 = 1 := by
  rwa [inner_normalVector_pi_div_two, K.property.2.2.2.1] at hp

/-- A singleton extreme face of a right-angle cap at a horizontal normal lies on the base line.
Lowering its unique point onto the base line keeps it in the cap, and a horizontal normal does not
see that vertical displacement, so the lowered point lies in the same face; the face being a
singleton, the displacement vanishes. -/
theorem CapSpace.edgeVertices_fst_apply_one_eq_zero (K : CapSpace (Real.pi / 2)) {s : ℝ}
    (hs : Real.sin s = 0)
    (hface : (edgeVertices K.val (s : Real.Angle)).1 = (edgeVertices K.val (s : Real.Angle)).2) :
    (edgeVertices K.val (s : Real.Angle)).1 1 = 0 := by
  have hmem := edgeVertices_fst_mem K.val (s : Real.Angle)
  have hkey : inner ℝ ((edgeVertices K.val (s : Real.Angle)).1 -
      (edgeVertices K.val (s : Real.Angle)).1 1 •
        normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) (normalVector (s : Real.Angle)) =
      supportValue (K.val : Set Point) (s : Real.Angle) := by
    rw [inner_sub_left, real_inner_smul_left, inner_normalVector_normalVector,
      Real.cos_pi_div_two_sub, hs, mul_zero, sub_zero]
    exact hmem.2
  have hlow : (edgeVertices K.val (s : Real.Angle)).1 -
      (edgeVertices K.val (s : Real.Angle)).1 1 •
        normalVector ((Real.pi / 2 : ℝ) : Real.Angle) ∈
      exposedEdge K.val (s : Real.Angle) := ⟨K.base_projection_mem hmem.1, hkey⟩
  rw [exposedEdge_eq_segment_edgeVertices, ← hface, segment_same, Set.mem_singleton_iff,
    sub_eq_self] at hlow
  have h := congrArg (fun p : Point ↦ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)))
    hlow
  rwa [real_inner_smul_left, inner_normalVector_self, mul_one, inner_zero_left] at h

/-- A convex body with vanishing base support value that is stable under vertical projection to
the base line is cut out by upper half-planes together with the base half-plane. -/
theorem hasHalfPlaneRepresentation_of_base_projection (M : ConvexBody Point)
    (hbase : supportValue M ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0)
    (hproj : ∀ q ∈ (M : Set Point),
      q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) ∈ (M : Set Point)) :
    HasHalfPlaneRepresentation M
      (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles (Real.pi / 2)) ∪
        capLowerNormals (Real.pi / 2)) := by
  -- At a right angle the allowed upper normals are exactly the angles of `[0, π]`.
  have hangle : ∀ s ∈ Set.Icc (0 : ℝ) Real.pi,
      ((s : ℝ) : Real.Angle) ∈
        (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles (Real.pi / 2)) ∪
          capLowerNormals (Real.pi / 2)) := by
    intro s hs
    refine Or.inl ⟨s, ?_, rfl⟩
    rcases le_or_gt s (Real.pi / 2) with h | h
    · exact Or.inl ⟨hs.1, h⟩
    · exact Or.inr ⟨h.le, by linarith [hs.2]⟩
  -- The vertical projection keeps the horizontal coordinate and kills the vertical one.
  have hflat : ∀ q : Point,
      (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) 0 = q 0 ∧
        (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) 1 = 0 := by
    intro q
    constructor <;> simp [normalVector, frame]
  -- The two attained horizontal extrema, lowered onto the base line.
  obtain ⟨qR, hqR, hqRval⟩ := exists_mem_inner_eq_supportValue M ((0 : ℝ) : Real.Angle)
  obtain ⟨qL, hqL, hqLval⟩ := exists_mem_inner_eq_supportValue M ((Real.pi : ℝ) : Real.Angle)
  rw [inner_normalVector_zero] at hqRval
  rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi] at hqLval
  refine ⟨(fun a : Real.Angle ↦ (a, supportValue M a)) ''
    ((((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles (Real.pi / 2)) ∪
      capLowerNormals (Real.pi / 2))), ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ha
  · ext p
    simp only [Set.mem_iInter]
    refine ⟨fun hp c hc ↦ ?_, fun hp ↦ ?_⟩
    · obtain ⟨a, -, rfl⟩ := hc
      exact inner_le_supportValue M hp a
    · have hpupper : ∀ s ∈ Set.Icc (0 : ℝ) Real.pi,
          inner ℝ p (normalVector ((s : ℝ) : Real.Angle)) ≤
            supportValue M ((s : ℝ) : Real.Angle) :=
        fun s hs ↦ hp _ ⟨_, hangle s hs, rfl⟩
      have hpbase := hp _ ⟨((3 * Real.pi / 2 : ℝ) : Real.Angle),
        Or.inr (Set.mem_insert_iff.2 (Or.inr rfl)), rfl⟩
      change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤
        supportValue M ((3 * Real.pi / 2 : ℝ) : Real.Angle) at hpbase
      rw [inner_normalVector_three_pi_div_two, hbase] at hpbase
      have hp1 : 0 ≤ p 1 := by linarith
      have hpR : p 0 ≤ qR 0 := by
        have h := hpupper 0 ⟨le_rfl, Real.pi_pos.le⟩
        rw [inner_normalVector_zero, ← hqRval] at h
        exact h
      have hpL : qL 0 ≤ p 0 := by
        have h := hpupper Real.pi ⟨Real.pi_pos.le, le_rfl⟩
        rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi, ← hqLval] at h
        linarith
      rw [M.eq_iInter_halfSpaces]
      simp only [Set.mem_iInter]
      intro u hu
      obtain ⟨θ, rfl⟩ := exists_angle_normalVector_eq hu
      change inner ℝ p (normalVector θ) ≤ supportValue M θ
      rw [← Real.Angle.coe_toReal θ]
      set s : ℝ := θ.toReal
      rcases le_or_gt 0 s with hs0 | hs0
      · exact hpupper s ⟨hs0, Real.Angle.toReal_le_pi θ⟩
      · have hsin : Real.sin s < 0 :=
          Real.sin_neg_of_neg_of_neg_pi_lt hs0 (Real.Angle.neg_pi_lt_toReal θ)
        rw [inner_normalVector_real]
        rcases le_or_gt 0 (Real.cos s) with hc | hc
        · have h := inner_le_supportValue M (hproj qR hqR) ((s : ℝ) : Real.Angle)
          rw [inner_normalVector_real, (hflat qR).1, (hflat qR).2] at h
          nlinarith [mul_le_mul_of_nonneg_right hpR hc,
            mul_nonpos_of_nonneg_of_nonpos hp1 hsin.le]
        · have h := inner_le_supportValue M (hproj qL hqL) ((s : ℝ) : Real.Angle)
          rw [inner_normalVector_real, (hflat qL).1, (hflat qL).2] at h
          nlinarith [mul_le_mul_of_nonpos_right hpL hc.le,
            mul_nonpos_of_nonneg_of_nonpos hp1 hsin.le]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Fan Projection
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Support values in the upper angular range of a non-right cap are nonnegative. -/
theorem supportValue_nonneg_of_mem_capUpperAngles {ω : ℝ} (K : CapSpace ω)
    (hω : ω < Real.pi / 2) {φ : ℝ} (hφ : φ ∈ capUpperAngles ω) :
    0 ≤ supportValue K.val (φ : Real.Angle) := by
  have hcosω : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [K.property.1, Real.pi_pos], hω⟩
  rcases hφ with hφ | hφ
  · obtain ⟨p, hpK, hpnormal⟩ := exists_mem_inner_eq_supportValue K.val
      ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    have hpFan := K.subset_capFan hpK
    have hpy : p 1 = 0 := by
      change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue K.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) at hpnormal
      rw [K.property.2.2.2.2.2.1] at hpnormal
      have hang : ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
          (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) := by
        congr 1
        ring
      rw [hang, normalVector_add_pi, inner_neg_right] at hpnormal
      simpa [normalVector, frame, PiLp.inner_apply] using hpnormal
    have hpx : 0 ≤ p 0 := by
      have hpω := hpFan.1
      change 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)) at hpω
      simp [normalVector, frame, PiLp.inner_apply, hpy] at hpω
      by_contra hneg
      have := mul_neg_of_pos_of_neg hcosω (lt_of_not_ge hneg)
      linarith
    have hcosφ : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc
      ⟨(neg_nonpos.mpr (by positivity : 0 ≤ Real.pi / 2)).trans hφ.1,
        hφ.2.trans hω.le⟩
    have hinner : 0 ≤ inner ℝ p (normalVector (φ : Real.Angle)) := by
      simp only [normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe, PiLp.inner_apply,
        RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, hpy, mul_zero, add_zero]
      exact mul_nonneg hcosφ hpx
    exact hinner.trans (inner_le_supportValue K.val hpK (φ : Real.Angle))
  · obtain ⟨p, hpK, hpnormal⟩ := exists_mem_inner_eq_supportValue K.val
      ((ω + Real.pi : ℝ) : Real.Angle)
    have hpFan := K.subset_capFan hpK
    have hpu : inner ℝ p (normalVector (ω : Real.Angle)) = 0 := by
      change inner ℝ p (normalVector ((ω + Real.pi : ℝ) : Real.Angle)) =
        supportValue K.val ((ω + Real.pi : ℝ) : Real.Angle) at hpnormal
      rw [K.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right] at hpnormal
      linarith
    let μ := inner ℝ p (tangentVector (ω : Real.Angle))
    have hp : μ • tangentVector (ω : Real.Angle) = p := by
      have hframe := inner_normalVector_smul_add_inner_tangentVector_smul
        p (ω : Real.Angle)
      rw [hpu, zero_smul, zero_add] at hframe
      exact hframe
    have hμ : 0 ≤ μ := by
      have hpy := hpFan.2
      change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hpy
      have hp1 := congrArg (fun q : Point ↦ q 1) hp
      change μ * Real.cos ω = p 1 at hp1
      have hpy' : 0 ≤ p 1 := by
        simpa [normalVector, frame, PiLp.inner_apply] using hpy
      rw [← hp1] at hpy'
      by_contra hneg
      have := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hcosω
      linarith
    have hsin : 0 ≤ Real.sin (φ - ω) := Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith [hφ.1]) (by linarith [hφ.2, Real.pi_pos])
    have hinner : 0 ≤ inner ℝ p (normalVector (φ : Real.Angle)) := by
      have htv : inner ℝ (tangentVector (ω : Real.Angle))
          (normalVector (φ : Real.Angle)) = Real.sin (φ - ω) := by
        simp [tangentVector, normalVector, frame, PiLp.inner_apply, Real.sin_sub]
        ring
      have heq : inner ℝ p (normalVector (φ : Real.Angle)) = μ * Real.sin (φ - ω) := by
        rw [← hp, real_inner_smul_left, htv]
      rw [heq]
      exact mul_nonneg hμ hsin
    exact hinner.trans (inner_le_supportValue K.val hpK (φ : Real.Angle))

/-- The origin belongs to every cap of angle strictly below a right angle. -/
theorem zero_mem_cap_of_lt {ω : ℝ} (K : CapSpace ω)
    (hω : ω < Real.pi / 2) : (0 : Point) ∈ (K.val : Set Point) := by
  apply K.mem_of_mem_capFan_of_le_supportValue
  · simp [capFan, normalHalfPlane]
  · intro φ hφ
    simpa using supportValue_nonneg_of_mem_capUpperAngles K hω hφ

/-- The normal projection of the zero-angle support value belongs to the cap. -/
theorem supportValue_zero_smul_normalVector_mem {ω : ℝ} (K : CapSpace ω) :
    supportValue K.val (0 : Real.Angle) • normalVector (0 : Real.Angle) ∈
      (K.val : Set Point) := by
  obtain ⟨p, hpK, hpnormal⟩ :=
    exists_mem_inner_eq_supportValue K.val (0 : Real.Angle)
  have hpFan := K.subset_capFan hpK
  have hpx : p 0 = supportValue K.val (0 : Real.Angle) := by
    change inner ℝ p (normalVector (0 : Real.Angle)) = supportValue K.val (0 : Real.Angle)
      at hpnormal
    simpa [normalVector, frame, PiLp.inner_apply] using hpnormal
  have hpy : 0 ≤ p 1 := by
    have := hpFan.2
    change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at this
    simpa [normalVector, frame, PiLp.inner_apply] using this
  apply K.mem_of_mem_capFan_of_le_supportValue
  · constructor
    · change 0 ≤ inner ℝ (supportValue K.val (0 : Real.Angle) •
          normalVector (0 : Real.Angle)) (normalVector (ω : Real.Angle))
      by_cases hω : ω = Real.pi / 2
      · simp [normalVector, frame, PiLp.inner_apply, hω]
      · have hωlt : ω < Real.pi / 2 := K.property.2.1.lt_of_ne hω
        have hs : 0 ≤ supportValue K.val (0 : Real.Angle) :=
          supportValue_nonneg_of_mem_capUpperAngles K hωlt
            (Or.inl ⟨le_rfl, K.property.1.le⟩)
        simp only [real_inner_smul_left]
        simp only [normalVector, frame, Real.Angle.cos_zero, Real.Angle.sin_zero, neg_zero,
          Real.Angle.cos_coe, Real.Angle.sin_coe, PiLp.inner_apply, RCLike.inner_apply,
          conj_trivial, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, mul_one,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, add_zero, ge_iff_le]
        exact mul_nonneg hs (Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [K.property.1, Real.pi_pos], K.property.2.1⟩)
    · change 0 ≤ inner ℝ (supportValue K.val (0 : Real.Angle) •
          normalVector (0 : Real.Angle))
        (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      simp [normalVector, frame, PiLp.inner_apply]
  · intro φ hφ
    have hφI : φ ∈ Set.Icc 0 Real.pi := by
      rcases hφ with hφ | hφ
      · exact ⟨hφ.1, hφ.2.trans
          (K.property.2.1.trans (by linarith [Real.pi_pos]))⟩
      · exact ⟨(by positivity : 0 ≤ Real.pi / 2).trans hφ.1,
          hφ.2.trans (by linarith [K.property.2.1, Real.pi_pos])⟩
    have hsinφ : 0 ≤ Real.sin φ := Real.sin_nonneg_of_mem_Icc hφI
    have hbound := inner_le_supportValue K.val hpK (φ : Real.Angle)
    have hinner : inner ℝ
        (supportValue K.val (0 : Real.Angle) • normalVector (0 : Real.Angle))
        (normalVector (φ : Real.Angle)) ≤ inner ℝ p (normalVector (φ : Real.Angle)) := by
      simp only [normalVector, frame, Real.Angle.cos_zero, Real.Angle.sin_zero, neg_zero,
        Real.Angle.cos_coe, Real.Angle.sin_coe, PiLp.inner_apply, PiLp.smul_apply, smul_eq_mul,
        RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
        mul_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, add_zero, hpx,
        le_add_iff_nonneg_right]
      exact mul_nonneg hsinφ hpy
    exact hinner.trans hbound

/-- At a right angle, the opposite normal projection belongs to the cap. -/
theorem supportValue_pi_smul_normalVector_mem_of_eq {ω : ℝ} (K : CapSpace ω)
    (hω : ω = Real.pi / 2) :
    supportValue K.val (Real.pi : Real.Angle) • normalVector (Real.pi : Real.Angle) ∈
      (K.val : Set Point) := by
  obtain ⟨p, hpK, hpnormal⟩ :=
    exists_mem_inner_eq_supportValue K.val (Real.pi : Real.Angle)
  have hpFan := K.subset_capFan hpK
  have hpx : -p 0 = supportValue K.val (Real.pi : Real.Angle) := by
    change inner ℝ p (normalVector (Real.pi : Real.Angle)) =
      supportValue K.val (Real.pi : Real.Angle) at hpnormal
    simpa [normalVector, frame, PiLp.inner_apply] using hpnormal
  have hpy : 0 ≤ p 1 := by
    have := hpFan.2
    change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at this
    simpa [normalVector, frame, PiLp.inner_apply] using this
  apply K.mem_of_mem_capFan_of_le_supportValue
  · constructor <;>
      simp [normalHalfPlane, normalVector, frame, PiLp.inner_apply, hω]
  · intro φ hφ
    have hφI : φ ∈ Set.Icc 0 Real.pi := by
      rcases hφ with hφ | hφ
      · exact ⟨hφ.1, hφ.2.trans (by rw [hω]; linarith [Real.pi_pos])⟩
      · exact ⟨(by positivity : 0 ≤ Real.pi / 2).trans hφ.1,
          hφ.2.trans (by rw [hω]; linarith)⟩
    have hsinφ : 0 ≤ Real.sin φ := Real.sin_nonneg_of_mem_Icc hφI
    have hbound := inner_le_supportValue K.val hpK (φ : Real.Angle)
    have hinner : inner ℝ
        (supportValue K.val (Real.pi : Real.Angle) • normalVector (Real.pi : Real.Angle))
        (normalVector (φ : Real.Angle)) ≤ inner ℝ p (normalVector (φ : Real.Angle)) := by
      rw [← hpx]
      simp only [Fin.isValue, normalVector, frame, Real.Angle.cos_coe, Real.cos_pi,
        Real.Angle.sin_coe, Real.sin_pi, neg_zero, neg_smul, inner_neg_left, PiLp.inner_apply,
        PiLp.smul_apply, smul_eq_mul, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two,
        Matrix.cons_val_zero, mul_neg, mul_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        mul_zero, add_zero, neg_neg, le_add_iff_nonneg_right]
      exact mul_nonneg hsinφ hpy
    exact hinner.trans hbound

/-- For a non-right cap, the terminal tangent projection belongs to the cap. -/
theorem supportValue_add_pi_div_two_smul_tangentVector_mem_of_lt {ω : ℝ}
    (K : CapSpace ω) (hω : ω < Real.pi / 2) :
    supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) •
        tangentVector (ω : Real.Angle) ∈ (K.val : Set Point) := by
  have hcosω : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [K.property.1, Real.pi_pos], hω⟩
  let L := supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle)
  obtain ⟨p, hpK, hpnormal⟩ := exists_mem_inner_eq_supportValue K.val
    ((ω + Real.pi / 2 : ℝ) : Real.Angle)
  have hpFan := K.subset_capFan hpK
  have hpv : inner ℝ p (tangentVector (ω : Real.Angle)) = L := by
    change inner ℝ p (normalVector ((ω + Real.pi / 2 : ℝ) : Real.Angle)) = L at hpnormal
    rw [show ((ω + Real.pi / 2 : ℝ) : Real.Angle) =
      (ω : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
      normalVector_add_pi_div_two] at hpnormal
    exact hpnormal
  let a := inner ℝ p (normalVector (ω : Real.Angle))
  have ha : 0 ≤ a := hpFan.1
  have hp : a • normalVector (ω : Real.Angle) + L • tangentVector (ω : Real.Angle) = p := by
    simpa only [a, hpv] using
      inner_normalVector_smul_add_inner_tangentVector_smul p (ω : Real.Angle)
  have hL : 0 ≤ L := supportValue_nonneg_of_mem_capUpperAngles K hω
    (Or.inr ⟨by linarith [K.property.1, Real.pi_pos], le_rfl⟩)
  apply K.mem_of_mem_capFan_of_le_supportValue
  · constructor
    · change 0 ≤ inner ℝ (L • tangentVector (ω : Real.Angle))
        (normalVector (ω : Real.Angle))
      rw [real_inner_smul_left, real_inner_comm, inner_normalVector_tangentVector]
      simp
    · change 0 ≤ inner ℝ (L • tangentVector (ω : Real.Angle))
        (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      simp only [tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe, normalVector,
        Real.cos_pi_div_two, Real.sin_pi_div_two, PiLp.inner_apply, PiLp.smul_apply,
        smul_eq_mul, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue,
        Matrix.cons_val_zero, mul_neg, zero_mul, neg_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, one_mul, zero_add]
      exact mul_nonneg hL hcosω.le
  · intro φ hφ
    have hdiff : φ - ω ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      rcases hφ with hφ | hφ
      · exact ⟨by linarith [hφ.1, K.property.2.1],
          by linarith [hφ.2, Real.pi_pos]⟩
      · exact ⟨by linarith [hφ.1, K.property.2.1, Real.pi_pos],
          by linarith [hφ.2]⟩
    have hcos : 0 ≤ Real.cos (φ - ω) := Real.cos_nonneg_of_mem_Icc hdiff
    have hnu : inner ℝ (normalVector (ω : Real.Angle))
        (normalVector (φ : Real.Angle)) = Real.cos (φ - ω) := by
      rw [inner_normalVector_normalVector]
      rw [show ω - φ = -(φ - ω) by ring, Real.cos_neg]
    have hbound := inner_le_supportValue K.val hpK (φ : Real.Angle)
    have hinner : inner ℝ (L • tangentVector (ω : Real.Angle))
        (normalVector (φ : Real.Angle)) ≤ inner ℝ p (normalVector (φ : Real.Angle)) := by
      rw [← hp, inner_add_left, real_inner_smul_left, real_inner_smul_left, hnu]
      exact le_add_of_nonneg_left (mul_nonneg ha hcos)
    exact hinner.trans hbound

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Hallway Quadrant
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The inward quadrant of the supporting hallway at angle `t` is the inward quadrant of `s`
written in support-value coordinates. -/
theorem rotatingHallwayParts_innerQuadrant (s : Set Point) (t : ℝ) :
    (rotatingHallwayParts s (t : Real.Angle)).innerQuadrant = innerQuadrant s t := by
  rw [(rotatingHallwayParts_formulas s (t : Real.Angle)).2.2.2.2.2.2.2.2]
  simp only [innerQuadrant, Real.Angle.coe_add]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The surface area measure of a right-angle cap at its lower normals

A right-angle cap lies above its base line and is stable under vertical projection onto it, so
at a strictly downward normal direction the support value is attained only on the base line, at
whichever horizontal extremum the sign of the horizontal normal component selects.  Both open
quarter arcs of lower normals therefore carry faces that degenerate to a single base corner,
and the surface area measure vanishes on them
(`MovingSofa.CapSpace.surfaceAreaMeasure_image_Ioo_lower_eq_zero`).  Outside the closed upper
semicircle only the bottom normal `3π / 2` is left, so an integrand vanishing there integrates
to zero (`MovingSofa.CapSpace.setIntegral_compl_image_Icc_zero_pi_eq_zero`).
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- At a strictly downward normal direction the face of a right-angle cap degenerates to the
base point below a horizontal extremum: positive height strictly lowers the normal coordinate,
and on the base line the sign of `Real.cos t` selects a horizontal extremum. -/
theorem CapSpace.exposedEdge_subset_singleton_of_isMaxOn (K : CapSpace (Real.pi / 2))
    {q : Point} (hq : q ∈ (K.val : Set Point)) {t : ℝ} (hcos : Real.cos t ≠ 0)
    (hsin : Real.sin t < 0)
    (hmax : IsMaxOn (fun p : Point ↦ p 0 * Real.cos t) (K.val : Set Point) q) :
    exposedEdge K.val (t : Real.Angle) ⊆
      {q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)} := by
  have hflat0 : (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) 0 = q 0 := by
    simp [normalVector, frame]
  have hflat1 : (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) 1 = 0 := by
    simp [normalVector, frame]
  intro p hp
  have hpK : p ∈ (K.val : Set Point) := hp.1
  have hp1 : 0 ≤ p 1 := by
    simpa only [inner_normalVector_pi_div_two] using K.inner_normalVector_pi_div_two_nonneg hpK
  have hpsup : inner ℝ p (normalVector (t : Real.Angle)) =
    supportValue K.val (t : Real.Angle) := hp.2
  have hple : inner ℝ (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      (normalVector (t : Real.Angle)) ≤ inner ℝ p (normalVector (t : Real.Angle)) := by
    rw [hpsup]
    exact inner_le_supportValue K.val (K.base_projection_mem hq) _
  rw [inner_normalVector_real, inner_normalVector_real, hflat0, hflat1] at hple
  have h1 : p 0 * Real.cos t ≤ q 0 * Real.cos t := isMaxOn_iff.mp hmax p hpK
  have h2 : p 1 * Real.sin t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp1 hsin.le
  have he1 : p 0 * Real.cos t = q 0 * Real.cos t := by linarith
  have he2 : p 1 = 0 := by
    have h3 : p 1 * Real.sin t = 0 := by linarith
    exact (mul_eq_zero.mp h3).resolve_right hsin.ne
  have g0 : p 0 = (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) 0 := by
    rw [hflat0]; exact mul_right_cancel₀ hcos he1
  have g1 : p 1 = (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) 1 := by
    rw [hflat1]; exact he2
  have hpt : p = q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) := by
    ext i
    fin_cases i
    · exact g0
    · exact g1
  simpa only [Set.mem_singleton_iff] using hpt

/-- The two base corners of a right-angle cap: on the open lower left quarter of normals every
face degenerates to the base point below a leftmost point of the cap, and on the open lower
right quarter to the base point below a rightmost one. -/
theorem CapSpace.exists_exposedEdge_subset_singleton (K : CapSpace (Real.pi / 2)) :
    ∃ pl pr : Point,
      (∀ t : ℝ, Real.cos t < 0 → Real.sin t < 0 →
        exposedEdge K.val (t : Real.Angle) ⊆ {pl}) ∧
      ∀ t : ℝ, 0 < Real.cos t → Real.sin t < 0 →
        exposedEdge K.val (t : Real.Angle) ⊆ {pr} := by
  have hcont : Continuous fun q : Point ↦ q 0 := PiLp.continuous_apply 2 _ 0
  obtain ⟨ql, hql, hqlmin⟩ :=
    K.val.isCompact.exists_isMinOn K.val.nonempty hcont.continuousOn
  obtain ⟨qr, hqr, hqrmax⟩ :=
    K.val.isCompact.exists_isMaxOn K.val.nonempty hcont.continuousOn
  refine ⟨ql - ql 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle),
    qr - qr 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle), ?_, ?_⟩
  · exact fun t hcos hsin ↦ K.exposedEdge_subset_singleton_of_isMaxOn hql hcos.ne hsin
      (isMaxOn_iff.mpr fun p hp ↦
        mul_le_mul_of_nonpos_right (isMinOn_iff.mp hqlmin p hp) hcos.le)
  · exact fun t hcos hsin ↦ K.exposedEdge_subset_singleton_of_isMaxOn hqr hcos.ne' hsin
      (isMaxOn_iff.mpr fun p hp ↦
        mul_le_mul_of_nonneg_right (isMaxOn_iff.mp hqrmax p hp) hcos.le)

/-- The surface area measure of a right-angle cap vanishes on both open quarter arcs of lower
normals, because there every face degenerates to a single base corner. -/
theorem CapSpace.surfaceAreaMeasure_image_Ioo_lower_eq_zero (K : CapSpace (Real.pi / 2)) :
    surfaceAreaMeasure K.val
        ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo Real.pi (3 * Real.pi / 2)) = 0 ∧
      surfaceAreaMeasure K.val
        ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo (3 * Real.pi / 2) (2 * Real.pi)) = 0 := by
  have hpi := Real.pi_pos
  obtain ⟨pl, pr, hl, hr⟩ := K.exists_exposedEdge_subset_singleton
  have hsin : ∀ s : ℝ, Real.pi < s → s < 2 * Real.pi → Real.sin s < 0 := by
    intro s h1 h2
    have h := Real.sin_pos_of_pos_of_lt_pi (x := s - Real.pi) (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at h
    linarith
  have main : ∀ (a b : ℝ) (p : Point), a ≤ b → b < a + Real.pi →
      (∀ s ∈ Set.Ioo a b, exposedEdge K.val (s : Real.Angle) ⊆ {p}) →
      surfaceAreaMeasure K.val ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b) = 0 := by
    intro a b p hab hba hsub
    refine surfaceAreaMeasure_null_of_exposedEdge_subset_singleton K.val
      (Real.Angle.isOpen_image_Ioo a b).measurableSet hab hba
      (Set.image_mono Set.Ioo_subset_Icc_self) p ?_
    intro u hu
    obtain ⟨s, hs, rfl⟩ := hu
    exact hsub s hs
  refine ⟨main Real.pi (3 * Real.pi / 2) pl (by linarith) (by linarith) fun s hs ↦ ?_,
    main (3 * Real.pi / 2) (2 * Real.pi) pr (by linarith) (by linarith) fun s hs ↦ ?_⟩
  · exact hl s (Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith [hs.1]) (by linarith [hs.2]))
      (hsin s hs.1 (by linarith [hs.2]))
  · refine hr s ?_ (hsin s (by linarith [hs.1]) hs.2)
    have h := Real.cos_pos_of_mem_Ioo
      (x := s - 2 * Real.pi) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rwa [Real.cos_sub_two_pi] at h

/-- Outside the closed upper semicircle the surface area measure of a right-angle cap is carried
by the single downward normal `3π / 2`, so any integrand vanishing there integrates to zero. -/
theorem CapSpace.setIntegral_compl_image_Icc_zero_pi_eq_zero (K : CapSpace (Real.pi / 2))
    (f : Real.Angle → ℝ) (hf : f ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0) :
    ∫ t in ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi)ᶜ,
      f t ∂surfaceAreaMeasure K.val = 0 := by
  obtain ⟨hA, hB⟩ := K.surfaceAreaMeasure_image_Ioo_lower_eq_zero
  have hS : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi) :=
    (isCompact_Icc.image Real.Angle.continuous_coe).isClosed.measurableSet
  have haenot : ∀ᵐ t ∂surfaceAreaMeasure K.val,
      t ∉ ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo Real.pi (3 * Real.pi / 2)) ∪
        ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo (3 * Real.pi / 2) (2 * Real.pi)) := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using measure_union_null hA hB
  have hcongr : ∫ t in ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi)ᶜ,
      f t ∂surfaceAreaMeasure K.val =
      ∫ _t in ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi)ᶜ,
        (0 : ℝ) ∂surfaceAreaMeasure K.val := by
    refine setIntegral_congr_ae hS.compl ?_
    filter_upwards [haenot] with t ht hts
    have hcoe : ((t.toReal + 2 * Real.pi : ℝ) : Real.Angle) = t := by
      rw [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero, Real.Angle.coe_toReal]
    have hneg : t.toReal < 0 := by
      by_contra hge
      exact hts ⟨t.toReal, ⟨not_lt.mp hge, Real.Angle.toReal_le_pi t⟩, t.coe_toReal⟩
    have hlow : Real.pi < t.toReal + 2 * Real.pi :=
      by linarith [Real.Angle.neg_pi_lt_toReal t]
    have hmid : t = ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
      rcases lt_trichotomy (t.toReal + 2 * Real.pi) (3 * Real.pi / 2) with h | h | h
      · exact absurd (Or.inl ⟨t.toReal + 2 * Real.pi, ⟨hlow, h⟩, hcoe⟩) ht
      · rw [← hcoe, h]
      · exact absurd (Or.inr ⟨t.toReal + 2 * Real.pi, ⟨h, by linarith⟩, hcoe⟩) ht
    rw [hmid, hf]
  rw [hcongr, integral_zero]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Reflection Geometry
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Image of a convex body under the cap reflection. -/
def reflectedBody (ω : ℝ) (K : ConvexBody Point) : ConvexBody Point where
  carrier := capReflection ω '' (K : Set Point)
  convex' := K.convex.linear_image (capReflection ω).toLinearEquiv.toLinearMap
  isCompact' := K.isCompact.image (capReflection ω).continuous
  nonempty' := K.nonempty.image _

/-- Support values of a reflected body are indexed by reflected normal angles. -/
theorem supportValue_reflectedBody (ω : ℝ) (K : ConvexBody Point)
    (a : Real.Angle) :
    supportValue (reflectedBody ω K) a =
      supportValue K (reflectedAngle ω a) := by
  unfold supportValue
  congr 1
  ext x
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q, hq, (inner_capReflection_normalVector ω q a).symm⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨capReflection ω q, ⟨q, hq, rfl⟩,
      inner_capReflection_normalVector ω q a⟩

/-- A reflected normal remains among the allowed cap normals. -/
theorem reflectedAngle_mem_capNormals {ω : ℝ} (a : Real.Angle)
    (ha : a ∈ ((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles ω) ∪
      capLowerNormals ω) :
    reflectedAngle ω a ∈
      ((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles ω) ∪
        capLowerNormals ω := by
  rcases ha with ha | ha
  · obtain ⟨t, ht, rfl⟩ := ha
    left
    refine ⟨ω + Real.pi / 2 - t, ?_, (reflectedAngle_coe ω t).symm⟩
    rcases ht with ht | ht
    · right
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    · left
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · right
    simp only [capLowerNormals, Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl
    · right
      rw [reflectedAngle_coe]
      have hperiod :
          (((-Real.pi / 2 : ℝ) : Real.Angle)) =
            (((3 * Real.pi / 2 : ℝ) : Real.Angle)) := by
        calc
          (((-Real.pi / 2 : ℝ) : Real.Angle)) =
              (((-Real.pi / 2 + 2 * Real.pi : ℝ) : Real.Angle)) := by
                rw [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]
          _ = (((3 * Real.pi / 2 : ℝ) : Real.Angle)) := by congr 1; ring
      convert hperiod using 1
      all_goals ring_nf
    · left
      rw [reflectedAngle_coe]
      have hperiod :
          (((ω - Real.pi : ℝ) : Real.Angle)) =
            (((ω + Real.pi : ℝ) : Real.Angle)) := by
        calc
          (((ω - Real.pi : ℝ) : Real.Angle)) =
              (((ω - Real.pi + 2 * Real.pi : ℝ) : Real.Angle)) := by
                rw [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]
          _ = (((ω + Real.pi : ℝ) : Real.Angle)) := by congr 1; ring
      convert hperiod using 1
      all_goals ring_nf

/-- Reflect a half-plane presentation when its allowed normals are transported. -/
theorem HasHalfPlaneRepresentation.reflectedBody {ω : ℝ}
    {K : ConvexBody Point} {N N' : Set Real.Angle}
    (hK : HasHalfPlaneRepresentation K N)
    (hN : ∀ a ∈ N, reflectedAngle ω a ∈ N') :
    HasHalfPlaneRepresentation (reflectedBody ω K) N' := by
  obtain ⟨C, hCN, hKC⟩ := hK
  let ρ : Real.Angle × ℝ → Real.Angle × ℝ :=
    fun c ↦ (reflectedAngle ω c.1, c.2)
  refine ⟨ρ '' C, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact hN c.1 (hCN c hc)
  · ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      simp only [Set.mem_iInter]
      intro c hc
      obtain ⟨d, hd, rfl⟩ := hc
      change inner ℝ (capReflection ω q)
        (normalVector (reflectedAngle ω d.1)) ≤ d.2
      rw [inner_capReflection_normalVector, reflectedAngle_involutive]
      rw [hKC] at hq
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hq d) hd
    · intro hp
      refine ⟨capReflection ω p, ?_, capReflection_involutive ω p⟩
      rw [hKC]
      simp only [Set.mem_iInter]
      intro c hc
      have hpc := Set.mem_iInter.mp
        (Set.mem_iInter.mp hp (ρ c)) ⟨c, hc, rfl⟩
      change inner ℝ p (normalVector (reflectedAngle ω c.1)) ≤ c.2 at hpc
      change inner ℝ (capReflection ω p) (normalVector c.1) ≤ c.2
      rw [inner_capReflection_normalVector]
      exact hpc

/-- Reflection preserves the standard cap half-plane presentation. -/
theorem reflectedBody_halfPlaneRepresentation {ω : ℝ}
    (K : ConvexBody Point)
    (hK : HasHalfPlaneRepresentation K
      (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles ω) ∪
        capLowerNormals ω)) :
    HasHalfPlaneRepresentation (reflectedBody ω K)
      (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles ω) ∪
        capLowerNormals ω) :=
  hK.reflectedBody fun a ha ↦ reflectedAngle_mem_capNormals a ha

/-- Reflection exchanges the normalized upper normal at `ω` with the vertical normal. -/
theorem reflectedAngle_at_omega (ω : ℝ) :
    reflectedAngle ω (ω : Real.Angle) =
      ((Real.pi / 2 : ℝ) : Real.Angle) := by
  rw [reflectedAngle_coe]
  congr 1
  ring

/-- Reflection exchanges the vertical normal with the normalized upper normal at `ω`. -/
theorem reflectedAngle_at_pi_div_two (ω : ℝ) :
    reflectedAngle ω ((Real.pi / 2 : ℝ) : Real.Angle) =
      (ω : Real.Angle) := by
  rw [reflectedAngle_coe]
  congr 1
  ring

/-- Reflection exchanges the two lower cap normals. -/
theorem reflectedAngle_at_omega_add_pi (ω : ℝ) :
    reflectedAngle ω ((ω + Real.pi : ℝ) : Real.Angle) =
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
  rw [reflectedAngle_coe]
  have hperiod :
      (((-Real.pi / 2 : ℝ) : Real.Angle)) =
        (((3 * Real.pi / 2 : ℝ) : Real.Angle)) := by
    calc
      (((-Real.pi / 2 : ℝ) : Real.Angle)) =
          (((-Real.pi / 2 + 2 * Real.pi : ℝ) : Real.Angle)) := by
            rw [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]
      _ = (((3 * Real.pi / 2 : ℝ) : Real.Angle)) := by congr 1; ring
  convert hperiod using 1
  all_goals ring_nf

/-- Reflection exchanges the two lower cap normals. -/
theorem reflectedAngle_at_three_pi_div_two (ω : ℝ) :
    reflectedAngle ω ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
      ((ω + Real.pi : ℝ) : Real.Angle) := by
  rw [reflectedAngle_coe]
  have hperiod :
      (((ω - Real.pi : ℝ) : Real.Angle)) =
        (((ω + Real.pi : ℝ) : Real.Angle)) := by
    calc
      (((ω - Real.pi : ℝ) : Real.Angle)) =
          (((ω - Real.pi + 2 * Real.pi : ℝ) : Real.Angle)) := by
            rw [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]
      _ = (((ω + Real.pi : ℝ) : Real.Angle)) := by congr 1; ring
  convert hperiod using 1
  all_goals ring_nf

/-- Reflection preserves the normalized cap conditions. -/
theorem reflectedBody_isCap {ω : ℝ} (K : CapSpace ω) :
    IsCap ω (reflectedBody ω K.val) := by
  rcases K.property with ⟨hω0, hωle, hω, hpi, hlowω, hlowpi, hrepr⟩
  refine ⟨hω0, hωle, ?_, ?_, ?_, ?_,
    reflectedBody_halfPlaneRepresentation K.val hrepr⟩
  · rw [supportValue_reflectedBody, reflectedAngle_at_omega, hpi]
  · rw [supportValue_reflectedBody, reflectedAngle_at_pi_div_two, hω]
  · rw [supportValue_reflectedBody, reflectedAngle_at_omega_add_pi, hlowpi]
  · rw [supportValue_reflectedBody, reflectedAngle_at_three_pi_div_two, hlowω]

/-- The cap reflection preserves the lower fan. -/
theorem capReflection_image_capFan (ω : ℝ) :
    capReflection ω '' capFan ω = capFan ω := by
  unfold capFan
  rw [Set.image_inter (capReflection ω).injective,
    capReflection_image_normalHalfPlane,
    capReflection_image_normalHalfPlane,
    reflectedAngle_at_omega, reflectedAngle_at_pi_div_two,
    Set.inter_comm]

/-- Reflection sends the complementary normal to its paired normal. -/
theorem reflectedAngle_sub (ω t : ℝ) :
    reflectedAngle ω ((ω - t : ℝ) : Real.Angle) =
      ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
  rw [reflectedAngle_coe]
  congr 1
  ring

/-- Reflection sends the complementary paired normal back to the original normal. -/
theorem reflectedAngle_sub_add_pi_div_two (ω t : ℝ) :
    reflectedAngle ω ((ω - t + Real.pi / 2 : ℝ) : Real.Angle) =
      (t : Real.Angle) := by
  rw [reflectedAngle_coe]
  congr 1
  ring

/-- Reflection sends a paired normal to the complementary normal. -/
theorem reflectedAngle_add_pi_div_two (ω t : ℝ) :
    reflectedAngle ω ((t + Real.pi / 2 : ℝ) : Real.Angle) =
      ((ω - t : ℝ) : Real.Angle) := by
  rw [reflectedAngle_coe]
  congr 1
  ring

/-- Reflection transports inward quadrants at complementary angles. -/
theorem innerQuadrant_reflection (ω t : ℝ) (K : ConvexBody Point) :
    innerQuadrant (reflectedBody ω K) t =
      capReflection ω '' innerQuadrant K (ω - t) := by
  unfold innerQuadrant
  rw [Set.image_inter (capReflection ω).injective,
    capReflection_image_normalHalfPlane,
    capReflection_image_normalHalfPlane,
    supportValue_reflectedBody, supportValue_reflectedBody,
    reflectedAngle_sub, reflectedAngle_sub_add_pi_div_two,
    reflectedAngle_add_pi_div_two, reflectedAngle_coe, Set.inter_comm]
  congr 2
  congr 1
  ring_nf

/-- The preimage and image of a set agree under the involutive cap reflection. -/
theorem capReflection_preimage_eq_image (ω : ℝ) (S : Set Point) :
    capReflection ω ⁻¹' S = capReflection ω '' S := by
  ext p
  constructor
  · intro hp
    exact ⟨capReflection ω p, hp, capReflection_involutive ω p⟩
  · rintro ⟨q, hq, rfl⟩
    simpa only [Set.mem_preimage, capReflection_involutive] using hq

/-- The cap reflection preserves the real Lebesgue area of measurable sets. -/
theorem area_image_capReflection (ω : ℝ) (S : Set Point)
    (hS : MeasurableSet S) :
    ClassicalResults.area (capReflection ω '' S) = ClassicalResults.area S := by
  change (MeasureTheory.volume (capReflection ω '' S)).toReal =
    (MeasureTheory.volume S).toReal
  rw [← capReflection_preimage_eq_image]
  congr 1
  exact (LinearIsometryEquiv.measurePreserving (capReflection ω)).measure_preimage
    hS.nullMeasurableSet

/-- The vertical reflection of a body has mirrored support values. -/
theorem supportValue_reflectedBody_pi_div_two (K : ConvexBody Point) (u : ℝ) :
    supportValue (reflectedBody (Real.pi / 2) K : Set Point) (u : Real.Angle) =
      supportValue (K : Set Point) ((Real.pi - u : ℝ) : Real.Angle) := by
  have hang : ((Real.pi / 2 + Real.pi / 2 - u : ℝ) : Real.Angle) =
      ((Real.pi - u : ℝ) : Real.Angle) := by congr 1; ring
  rw [supportValue_reflectedBody, reflectedAngle_coe, hang]

/-- The vertical reflection mirrors normal projections. -/
theorem inner_capReflection_pi_div_two (p : Point) (u : ℝ) :
    inner ℝ (capReflection (Real.pi / 2) p) (normalVector (u : Real.Angle)) =
      inner ℝ p (normalVector ((Real.pi - u : ℝ) : Real.Angle)) := by
  have hang : ((Real.pi / 2 + Real.pi / 2 - u : ℝ) : Real.Angle) =
      ((Real.pi - u : ℝ) : Real.Angle) := by congr 1; ring
  rw [inner_capReflection_normalVector, reflectedAngle_coe, hang]
end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Support Intersections
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace MovingSofa

private theorem supportingIntersection_le_supportValue_of_mem_Icc_left
    (K : ConvexBody Point) {a b r : ℝ} (hab : 0 < b - a) (hpi : b - a < Real.pi)
    (hr : r ∈ Set.Icc (a - Real.pi) a) :
    inner ℝ (supportingIntersection K (a : Real.Angle) (b : Real.Angle))
        (normalVector (r : Real.Angle)) ≤ supportValue K (r : Real.Angle) := by
  let p := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  let q := (edgeVertices K (a : Real.Angle)).1
  have hsin : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi hab hpi
  have hpa : inner ℝ p (normalVector (a : Real.Angle)) =
      supportValue K (a : Real.Angle) := supportingIntersection_inner_left K a b
  have hpb : inner ℝ p (normalVector (b : Real.Angle)) =
      supportValue K (b : Real.Angle) :=
    supportingIntersection_inner_right K a b hsin.ne'
  have hqmem := edgeVertices_fst_mem K (a : Real.Angle)
  have hqa : inner ℝ q (normalVector (a : Real.Angle)) =
      supportValue K (a : Real.Angle) := hqmem.2
  have hqb : inner ℝ q (normalVector (b : Real.Angle)) ≤
      supportValue K (b : Real.Angle) := inner_le_supportValue K hqmem.1 _
  have hnormal : inner ℝ (p - q) (normalVector (a : Real.Angle)) = 0 := by
    rw [inner_sub_left, hpa, hqa, sub_self]
  have htangent : 0 ≤ inner ℝ (p - q) (tangentVector (a : Real.Angle)) := by
    have hdiff : 0 ≤ inner ℝ (p - q) (normalVector (b : Real.Angle)) := by
      rw [inner_sub_left, hpb]
      linarith
    have hnb : normalVector (b : Real.Angle) =
        Real.cos (b - a) • normalVector (a : Real.Angle) +
          Real.sin (b - a) • tangentVector (a : Real.Angle) := by
      simpa only [add_sub_cancel] using normalVector_add_real a (b - a)
    rw [hnb, inner_add_right, inner_smul_right, inner_smul_right, hnormal,
      mul_zero, zero_add] at hdiff
    nlinarith
  have hqr : inner ℝ q (normalVector (r : Real.Angle)) ≤
      supportValue K (r : Real.Angle) := inner_le_supportValue K hqmem.1 _
  have hnr : normalVector (r : Real.Angle) =
      Real.cos (r - a) • normalVector (a : Real.Angle) +
        Real.sin (r - a) • tangentVector (a : Real.Angle) := by
    simpa only [add_sub_cancel] using normalVector_add_real a (r - a)
  have hsinr : Real.sin (r - a) ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith [hr.2]) (by linarith [hr.1])
  have hdiff : inner ℝ (p - q) (normalVector (r : Real.Angle)) ≤ 0 := by
    rw [hnr, inner_add_right, inner_smul_right, inner_smul_right, hnormal,
      mul_zero, zero_add]
    exact mul_nonpos_of_nonpos_of_nonneg hsinr htangent
  rw [inner_sub_left] at hdiff
  linarith

private theorem supportingIntersection_le_supportValue_of_mem_Icc_right
    (K : ConvexBody Point) {a b r : ℝ} (hab : 0 < b - a) (hpi : b - a < Real.pi)
    (hr : r ∈ Set.Icc b (b + Real.pi)) :
    inner ℝ (supportingIntersection K (a : Real.Angle) (b : Real.Angle))
        (normalVector (r : Real.Angle)) ≤ supportValue K (r : Real.Angle) := by
  let p := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  let q := (edgeVertices K (b : Real.Angle)).2
  have hsin : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi hab hpi
  have hsina : Real.sin (a - b) < 0 := by
    rw [show a - b = -(b - a) by ring, Real.sin_neg]
    exact neg_neg_of_pos hsin
  have hpa : inner ℝ p (normalVector (a : Real.Angle)) =
      supportValue K (a : Real.Angle) := supportingIntersection_inner_left K a b
  have hpb : inner ℝ p (normalVector (b : Real.Angle)) =
      supportValue K (b : Real.Angle) :=
    supportingIntersection_inner_right K a b hsin.ne'
  have hqmem := edgeVertices_snd_mem K (b : Real.Angle)
  have hqb : inner ℝ q (normalVector (b : Real.Angle)) =
      supportValue K (b : Real.Angle) := hqmem.2
  have hqa : inner ℝ q (normalVector (a : Real.Angle)) ≤
      supportValue K (a : Real.Angle) := inner_le_supportValue K hqmem.1 _
  have hnormal : inner ℝ (p - q) (normalVector (b : Real.Angle)) = 0 := by
    rw [inner_sub_left, hpb, hqb, sub_self]
  have htangent : inner ℝ (p - q) (tangentVector (b : Real.Angle)) ≤ 0 := by
    have hdiff : 0 ≤ inner ℝ (p - q) (normalVector (a : Real.Angle)) := by
      rw [inner_sub_left, hpa]
      linarith
    have hna : normalVector (a : Real.Angle) =
        Real.cos (a - b) • normalVector (b : Real.Angle) +
          Real.sin (a - b) • tangentVector (b : Real.Angle) := by
      simpa only [add_sub_cancel] using normalVector_add_real b (a - b)
    rw [hna, inner_add_right, inner_smul_right, inner_smul_right, hnormal,
      mul_zero, zero_add] at hdiff
    nlinarith
  have hqr : inner ℝ q (normalVector (r : Real.Angle)) ≤
      supportValue K (r : Real.Angle) := inner_le_supportValue K hqmem.1 _
  have hnr : normalVector (r : Real.Angle) =
      Real.cos (r - b) • normalVector (b : Real.Angle) +
        Real.sin (r - b) • tangentVector (b : Real.Angle) := by
    simpa only [add_sub_cancel] using normalVector_add_real b (r - b)
  have hsinr : 0 ≤ Real.sin (r - b) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hr.1]) (by linarith [hr.2])
  have hdiff : inner ℝ (p - q) (normalVector (r : Real.Angle)) ≤ 0 := by
    rw [hnr, inner_add_right, inner_smul_right, inner_smul_right, hnormal,
      mul_zero, zero_add]
    exact mul_nonpos_of_nonneg_of_nonpos hsinr htangent
  rw [inner_sub_left] at hdiff
  linarith

/-- Adjacent allowed support normals meet in the represented convex body. -/
theorem HasHalfPlaneRepresentation.supportingIntersection_mem_of_gap
    (K : ConvexBody Point) (R : Set ℝ) {a b : ℝ}
    (hab : 0 < b - a) (hpi : b - a < Real.pi)
    (hK : HasHalfPlaneRepresentation K ((fun r : ℝ ↦ (r : Real.Angle)) '' R))
    (hR : ∀ r ∈ R, r ∈ Set.Icc (a - Real.pi) a ∨ r ∈ Set.Icc b (b + Real.pi)) :
    supportingIntersection K (a : Real.Angle) (b : Real.Angle) ∈ K := by
  change supportingIntersection K (a : Real.Angle) (b : Real.Angle) ∈ (K : Set Point)
  rw [hK.eq_iInter_supportValue]
  simp only [Set.mem_iInter]
  intro u hu
  obtain ⟨r, hr, rfl⟩ := hu
  rcases hR r hr with hr | hr
  · exact supportingIntersection_le_supportValue_of_mem_Icc_left K hab hpi hr
  · exact supportingIntersection_le_supportValue_of_mem_Icc_right K hab hpi hr

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Top Corner
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Every polygon cap of angle less than pi/2 contains the top parallelogram corner. -/
theorem stripParallelogram_top_mem_of_angle_lt (Θ : AngleSet)
    (hΘ : Θ.angle < Real.pi / 2) (K : PolygonCapSpace Θ) :
    (stripParallelogram Θ.angle).2.2 ∈ (K.val.val : Set Point) := by
  let o := (stripParallelogram Θ.angle).2.2
  have hc : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Θ.angle_pos, Real.pi_pos], hΘ⟩
  obtain ⟨pω, hpω, hpωeq⟩ := (K.val.val.isCompact.image
    (continuous_inner.comp (continuous_id.prodMk continuous_const))).sSup_mem
      (K.val.val.nonempty.image (fun p ↦ inner ℝ p (normalVector (Θ.angle : Real.Angle))))
  obtain ⟨pT, hpT, hpTeq⟩ := (K.val.val.isCompact.image
    (continuous_inner.comp (continuous_id.prodMk continuous_const))).sSup_mem
      (K.val.val.nonempty.image
        (fun p ↦ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))))
  have hpω' : inner ℝ pω (normalVector (Θ.angle : Real.Angle)) = 1 := by
    change inner ℝ pω (normalVector (Θ.angle : Real.Angle)) =
      supportValue K.val.val (Θ.angle : Real.Angle) at hpωeq
    simpa only [K.val.property.2.2.1] using hpωeq
  have hpT' : inner ℝ pT (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
    change inner ℝ pT (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue K.val.val ((Real.pi / 2 : ℝ) : Real.Angle) at hpTeq
    simpa only [K.val.property.2.2.2.1] using hpTeq
  have hpωT : inner ℝ pω (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤ 1 := by
    exact (inner_le_supportValue K.val.val hpω _).trans_eq K.val.property.2.2.2.1
  have hpTω : inner ℝ pT (normalVector (Θ.angle : Real.Angle)) ≤ 1 := by
    exact (inner_le_supportValue K.val.val hpT _).trans_eq K.val.property.2.2.1
  have hoω : inner ℝ o (normalVector (Θ.angle : Real.Angle)) = 1 := by
    have hgap : Real.tan (Real.pi / 4 - Θ.angle / 2) =
        (Real.cos Θ.angle)⁻¹ - Real.tan Θ.angle := by
      simpa [show Real.pi / 4 - Θ.angle / 2 =
          (Real.pi / 2 - Θ.angle) / 2 by ring]
        using Real.tan_pi_div_two_sub_div_two Θ.angle ⟨Θ.angle_pos.le, hΘ⟩
    have htan := Real.tan_eq_sin_div_cos Θ.angle
    simp [o, stripParallelogram, normalVector, frame, PiLp.inner_apply, hgap, htan]
    field_simp [hc.ne']
    ring
  have hoT : inner ℝ o (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
    simp [o, stripParallelogram, normalVector, frame, PiLp.inner_apply]
  rw [K.property.eq_iInter_supportValue]
  simp only [Set.mem_iInter]
  intro a ha
  change inner ℝ o (normalVector a) ≤ supportValue K.val.val a
  rcases ha with ⟨t, ht, rfl⟩ | ha
  · have htupper : t ∈ capUpperAngles Θ.angle := by
      rcases ht with (ht | ⟨s, hs, rfl⟩) | ht
      · exact Or.inl ⟨(Θ.interior t ht).1.le, (Θ.interior t ht).2.le⟩
      · exact Or.inr ⟨by dsimp; linarith [(Θ.interior s hs).1],
          by dsimp; linarith [(Θ.interior s hs).2]⟩
      · rcases ht with rfl | rfl
        · exact Or.inl ⟨Θ.angle_pos.le, le_rfl⟩
        · exact Or.inr ⟨le_rfl, by linarith [Θ.angle_pos]⟩
    rcases htupper with ht | ht
    · let c := Real.cos t / Real.cos Θ.angle
      let s := Real.sin (Θ.angle - t) / Real.cos Θ.angle
      have hc0 : 0 ≤ c := div_nonneg
        (Real.cos_nonneg_of_mem_Icc
          ⟨(neg_nonpos.mpr (by positivity)).trans ht.1, ht.2.trans Θ.angle_le⟩) hc.le
      have hs0 : 0 ≤ s := div_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr ht.2)
          (by linarith [ht.1, Θ.angle_le, Real.pi_pos])) hc.le
      have hdecomp : normalVector (t : Real.Angle) =
          c • normalVector (Θ.angle : Real.Angle) -
            s • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) := by
        ext i
        fin_cases i
        · simp [c, s, normalVector, frame, Real.sin_sub]
          field_simp [hc.ne']
        · simp [c, s, normalVector, frame, Real.sin_sub]
          field_simp [hc.ne']
          ring
      rw [hdecomp, inner_sub_right, inner_smul_right, inner_smul_right, hoω, hoT]
      apply (inner_le_supportValue K.val.val hpω (t : Real.Angle)).trans'
      rw [hdecomp, inner_sub_right, inner_smul_right, inner_smul_right, hpω']
      simpa only [mul_one] using
        sub_le_sub_left (mul_le_mul_of_nonneg_left hpωT hs0) c
    · let c := Real.sin (t - Θ.angle) / Real.cos Θ.angle
      let s := -Real.cos t / Real.cos Θ.angle
      have hc0 : 0 ≤ c := div_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1, Θ.angle_le])
          (by linarith [ht.2, Θ.angle_pos, Real.pi_pos])) hc.le
      have hs0 : 0 ≤ s := div_nonneg
        (neg_nonneg.mpr (Real.cos_nonpos_of_pi_div_two_le_of_le ht.1
          (by linarith [ht.2, Θ.angle_le, Real.pi_pos]))) hc.le
      have hdecomp : normalVector (t : Real.Angle) =
          c • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) -
            s • normalVector (Θ.angle : Real.Angle) := by
        ext i
        fin_cases i
        · simp [c, s, normalVector, frame, Real.sin_sub]
          field_simp [hc.ne']
        · simp [c, s, normalVector, frame, Real.sin_sub]
          field_simp [hc.ne']
          ring
      rw [hdecomp, inner_sub_right, inner_smul_right, inner_smul_right, hoT, hoω]
      apply (inner_le_supportValue K.val.val hpT (t : Real.Angle)).trans'
      rw [hdecomp, inner_sub_right, inner_smul_right, inner_smul_right, hpT']
      simpa only [mul_one] using
        sub_le_sub_left (mul_le_mul_of_nonneg_left hpTω hs0) c
  · rcases ha with rfl | rfl
    · rw [normalVector_add_pi, inner_neg_right, hoω, K.val.property.2.2.2.2.1]
      norm_num
    · rw [inner_normalVector_three_pi_div_two, K.val.property.2.2.2.2.2.1]
      simp [o, stripParallelogram]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Vertical
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- A cap is closed under downward vertical movement that remains inside its fan. -/
theorem CapSpace.mem_of_fst_eq_of_snd_le {ω : ℝ} (K : CapSpace ω)
    {p q : Point} (hp : p ∈ (K.val : Set Point)) (hq : q ∈ capFan ω)
    (hx : q 0 = p 0) (hy : q 1 ≤ p 1) : q ∈ (K.val : Set Point) := by
  apply K.mem_of_mem_capFan_of_le_supportValue hq
  intro t ht
  apply le_trans _ (inner_le_supportValue K.val hp (t : Real.Angle))
  have htI : t ∈ Set.Icc 0 Real.pi := by
    rcases ht with ht | ht
    · exact ⟨ht.1, by linarith [ht.2, K.property.2.1, Real.pi_pos]⟩
    · exact ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, K.property.2.1]⟩
  have h := mul_le_mul_of_nonneg_left hy (Real.sin_nonneg_of_mem_Icc htI)
  simp [normalVector, frame, PiLp.inner_apply, hx]
  linarith

end MovingSofa

end

end

end
