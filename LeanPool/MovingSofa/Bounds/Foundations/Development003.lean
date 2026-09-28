/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Cap.Foundations.Development002
public import LeanPool.MovingSofa.Cap.Foundations.Development003
public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development003
public import LeanPool.MovingSofa.Geometry.Foundations.Development003
public import LeanPool.MovingSofa.Polygon.Foundations.Development002
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order.ProjIcc
/-!
# Moving sofa: related mathematical developments

* `Bounds.LegComputation`.
* `Bounds.Lower.Profile`.
* `Bounds.NicheLimits`.
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
# Bounds / Leg Computation
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace MovingSofa

private theorem rightAngle_allowedReal_gap_left (n : ℕ) (hn : 2 ≤ n) {t r : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions)
    (hr : r ∈ angleDomain (rightAngleSet n hn) ∪ {3 * Real.pi / 2}) :
    r ∈ Set.Icc (t - polygonStepSize n + Real.pi / 2 - Real.pi)
        (t - polygonStepSize n + Real.pi / 2) ∨
    r ∈ Set.Icc (t + Real.pi / 2) (t + Real.pi / 2 + Real.pi) := by
  have hδpos : 0 < polygonStepSize n := by simp [polygonStepSize]; positivity
  obtain ⟨hδt, htδ⟩ := rightAngleSet_direction_bounds n hn ht
  have htI := (rightAngleSet n hn).interior t ht
  change t ∈ Set.Ioo 0 (Real.pi / 2) at htI
  obtain ⟨ht0, htT⟩ := htI
  rcases hr with hr | rfl
  · change r ∈ ((rightAngleSet n hn).directions : Set ℝ) ∪
        ((fun q : ℝ ↦ q + Real.pi / 2) ''
          ((rightAngleSet n hn).directions : Set ℝ)) ∪
        {(rightAngleSet n hn).angle, Real.pi / 2} at hr
    rcases hr with (hr | ⟨q, hq, rfl⟩) | hr
    · have hrI := (rightAngleSet n hn).interior r hr
      change r ∈ Set.Ioo 0 (Real.pi / 2) at hrI
      obtain ⟨hr0, hrT⟩ := hrI
      left
      constructor <;> linarith [Real.pi_pos]
    · have hqI := (rightAngleSet n hn).interior q hq
      change q ∈ Set.Ioo 0 (Real.pi / 2) at hqI
      obtain ⟨hq0, hqT⟩ := hqI
      simp only
      rcases rightAngleSet_direction_le_pred_or_ge n hn hq ht with hqle | hqge
      · left
        constructor
        ·
          linarith [Real.pi_pos]
        · linarith
      · right
        constructor <;> linarith [Real.pi_pos]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl <;> left
      all_goals
        change _ ≤ Real.pi / 2 ∧ Real.pi / 2 ≤ _
        constructor <;> linarith [Real.pi_pos]
  · right
    constructor <;> linarith [Real.pi_pos]

private theorem rightAngle_allowedReal_gap_right (n : ℕ) (hn : 2 ≤ n) {t r : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions)
    (hr : r ∈ angleDomain (rightAngleSet n hn) ∪ {3 * Real.pi / 2}) :
    r ∈ Set.Icc (t + Real.pi / 2 - Real.pi) (t + Real.pi / 2) ∨
      r ∈ Set.Icc (t + polygonStepSize n + Real.pi / 2)
        (t + polygonStepSize n + Real.pi / 2 + Real.pi) := by
  have hδpos : 0 < polygonStepSize n := by simp [polygonStepSize]; positivity
  obtain ⟨hδt, htδ⟩ := rightAngleSet_direction_bounds n hn ht
  have htI := (rightAngleSet n hn).interior t ht
  change t ∈ Set.Ioo 0 (Real.pi / 2) at htI
  obtain ⟨ht0, htT⟩ := htI
  rcases hr with hr | rfl
  · change r ∈ ((rightAngleSet n hn).directions : Set ℝ) ∪
        ((fun q : ℝ ↦ q + Real.pi / 2) ''
          ((rightAngleSet n hn).directions : Set ℝ)) ∪
        {(rightAngleSet n hn).angle, Real.pi / 2} at hr
    rcases hr with (hr | ⟨q, hq, rfl⟩) | hr
    · have hrI := (rightAngleSet n hn).interior r hr
      change r ∈ Set.Ioo 0 (Real.pi / 2) at hrI
      obtain ⟨hr0, hrT⟩ := hrI
      left
      constructor <;> linarith [Real.pi_pos]
    · have hqI := (rightAngleSet n hn).interior q hq
      change q ∈ Set.Ioo 0 (Real.pi / 2) at hqI
      obtain ⟨hq0, hqT⟩ := hqI
      simp only
      rcases rightAngleSet_direction_le_or_succ_le n hn hq ht with hqle | hqge
      · left
        constructor <;> linarith [Real.pi_pos]
      · right
        constructor <;> linarith [Real.pi_pos]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl <;> left
      all_goals
        change _ ≤ Real.pi / 2 ∧ Real.pi / 2 ≤ _
        constructor <;> linarith [Real.pi_pos]
  · right
    constructor <;> linarith [Real.pi_pos]

/-- The preceding shifted grid support is attained at the negative left-wall contact. -/
private theorem rightAngle_supportValue_prev_shift (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) {t : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions) :
    supportValue K.val.val
        ((t - polygonStepSize n + Real.pi / 2 : ℝ) : Real.Angle) =
      inner ℝ (capVertices K.val t).2.2
        (normalVector ((t - polygonStepSize n + Real.pi / 2 : ℝ) : Real.Angle)) := by
  let a := t - polygonStepSize n + Real.pi / 2
  let b := t + Real.pi / 2
  let R := angleDomain (rightAngleSet n hn) ∪ {3 * Real.pi / 2}
  have hδpos : 0 < polygonStepSize n := by simp [polygonStepSize]; positivity
  have hδpi : polygonStepSize n < Real.pi := by
    have hnpos : (0 : ℝ) < n := by positivity
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hδT : polygonStepSize n < Real.pi / 2 := by
      simp only [polygonStepSize]
      apply (div_lt_iff₀ hnpos).2
      nlinarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have hrepr : HasHalfPlaneRepresentation K.val.val
      ((fun r : ℝ ↦ (r : Real.Angle)) '' R) := by
    rw [← rightAngle_polygon_normals_eq n hn]
    exact K.property
  have hp : supportingIntersection K.val.val (a : Real.Angle) (b : Real.Angle) ∈ K.val.val := by
    apply hrepr.supportingIntersection_mem_of_gap K.val.val R
    · dsimp [a, b]
      linarith
    · dsimp [a, b]
      linarith
    · intro r hr
      simpa only [a, b] using rightAngle_allowedReal_gap_left n hn ht hr
  have heq := supportingIntersection_eq_edgeVertices_snd_of_mem K.val.val
    (a := a) (b := b) (by dsimp [a, b]; linarith)
    (by dsimp [a, b]; linarith) hp
  have hinter := supportingIntersection_inner_left K.val.val a b
  change inner ℝ (supportingIntersection K.val.val (a : Real.Angle) (b : Real.Angle))
      (normalVector (a : Real.Angle)) = supportValue K.val.val (a : Real.Angle) at hinter
  change supportValue K.val.val (a : Real.Angle) =
    inner ℝ (edgeVertices K.val.val (b : Real.Angle)).2 (normalVector (a : Real.Angle))
  rw [← heq, hinter]

/-- The next shifted support is attained at the positive contact, including the final grid point. -/
private theorem rightAngle_supportValue_next_shift (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) {t : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions) :
    supportValue K.val.val
        ((t + polygonStepSize n + Real.pi / 2 : ℝ) : Real.Angle) =
      inner ℝ (capVertices K.val t).2.1
        (normalVector ((t + polygonStepSize n + Real.pi / 2 : ℝ) : Real.Angle)) := by
  let a := t + Real.pi / 2
  let b := t + polygonStepSize n + Real.pi / 2
  let R := angleDomain (rightAngleSet n hn) ∪ {3 * Real.pi / 2}
  have hδpos : 0 < polygonStepSize n := by simp [polygonStepSize]; positivity
  have hδpi : polygonStepSize n < Real.pi := by
    have hnpos : (0 : ℝ) < n := by positivity
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hδT : polygonStepSize n < Real.pi / 2 := by
      simp only [polygonStepSize]
      apply (div_lt_iff₀ hnpos).2
      nlinarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have hrepr : HasHalfPlaneRepresentation K.val.val
      ((fun r : ℝ ↦ (r : Real.Angle)) '' R) := by
    rw [← rightAngle_polygon_normals_eq n hn]
    exact K.property
  have hp : supportingIntersection K.val.val (a : Real.Angle) (b : Real.Angle) ∈ K.val.val := by
    apply hrepr.supportingIntersection_mem_of_gap K.val.val R
    · dsimp [a, b]
      linarith
    · dsimp [a, b]
      linarith
    · intro r hr
      simpa only [a, b] using rightAngle_allowedReal_gap_right n hn ht hr
  have heq := supportingIntersection_eq_edgeVertices_fst_of_mem K.val.val
    (a := a) (b := b) (by dsimp [a, b]; linarith)
    (by dsimp [a, b]; linarith) hp
  have hinter := supportingIntersection_inner_right K.val.val a b
    (show Real.sin (b - a) ≠ 0 by
      apply ne_of_gt
      apply Real.sin_pos_of_pos_of_lt_pi <;> dsimp [a, b] <;> linarith)
  change inner ℝ (supportingIntersection K.val.val (a : Real.Angle) (b : Real.Angle))
      (normalVector (b : Real.Angle)) = supportValue K.val.val (b : Real.Angle) at hinter
  change supportValue K.val.val (b : Real.Angle) =
    inner ℝ (edgeVertices K.val.val (a : Real.Angle)).1 (normalVector (b : Real.Angle))
  rw [← heq, hinter]

private theorem one_sub_cos_div_cos_eq_tan_mul_tan_half {δ : ℝ}
    (hδ0 : 0 < δ) (hδT : δ < Real.pi / 2) :
    (1 - Real.cos δ) / Real.cos δ = Real.tan δ * Real.tan (δ / 2) := by
  have hc : Real.cos δ ≠ 0 := ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hδT⟩)
  have hch : Real.cos (δ / 2) ≠ 0 := ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
  field_simp [hc, hch]
  have htwo : δ = 2 * (δ / 2) := by ring
  have hcos : Real.cos δ = 1 - 2 * Real.sin (δ / 2) ^ 2 :=
    (congrArg Real.cos htwo).trans (Real.cos_two_mul_eq_one_sub _)
  have hsin : Real.sin δ = 2 * Real.sin (δ / 2) * Real.cos (δ / 2) :=
    (congrArg Real.sin htwo).trans (Real.sin_two_mul _)
  rw [hcos, hsin]
  ring

private theorem polygonStepSize_mem_Ioo (n : ℕ) (hn : 2 ≤ n) :
    polygonStepSize n ∈ Set.Ioo 0 (Real.pi / 2) := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · simp only [polygonStepSize]
    positivity
  · simp only [polygonStepSize]
    apply (div_lt_iff₀ hnpos).2
    nlinarith [Real.pi_pos]

private theorem rightAngle_bRay_prev_leg_length (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) {t : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions) :
    Measure.hausdorffMeasure 1
        ((rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay ∩
          (innerWallUpperHalfPlanes K.val (t - polygonStepSize n)).2) =
      ENNReal.ofReal (Real.tan (polygonStepSize n) *
        max 0 ((tangentArmLengths K.val t).2.2 - 1 +
          Real.tan (polygonStepSize n / 2))) := by
  let δ := polygonStepSize n
  let x := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).innerCorner
  let y := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).outerCorner
  let c := (capVertices K.val t).2.2
  let g := (tangentArmLengths K.val t).2.2
  let u := t - δ + Real.pi / 2
  have hδI : δ ∈ Set.Ioo 0 (Real.pi / 2) := polygonStepSize_mem_Ioo n hn
  have hcδ : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hδI.1, Real.pi_pos], hδI.2⟩
  have htI : t ∈ Set.Icc 0 (Real.pi / 2) := by
    have hi := (rightAngleSet n hn).interior t ht
    change t ∈ Set.Ioo 0 (Real.pi / 2) at hi
    exact ⟨hi.1.le, hi.2.le⟩
  have hnormal : normalVector (u : Real.Angle) =
      Real.sin δ • normalVector (t : Real.Angle) +
        Real.cos δ • tangentVector (t : Real.Angle) := by
    have h := normalVector_add_real t (Real.pi / 2 - δ)
    rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub] at h
    have hu : u = t + (Real.pi / 2 - δ) := by dsimp [u]; ring
    rw [hu]
    exact h
  have htrans : 0 < inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (u : Real.Angle)) := by
    rw [hnormal, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_comm, inner_normalVector_tangentVector, inner_tangentVector_self]
    simpa using hcδ
  rw [show (innerWallUpperHalfPlanes K.val (t - polygonStepSize n)).2 =
      normalHalfPlane (u : Real.Angle)
        (supportValue K.val.val (u : Real.Angle) - 1) true false by
    simp only [innerWallUpperHalfPlanes, u, δ]
    ]
  rw [hausdorffMeasure_bRay_inter_normalHalfPlane _ _ _ _ htrans]
  have hx : x = y - normalVector (t : Real.Angle) - tangentVector (t : Real.Angle) := by
    have hf := rotatingHallwayParts_formulas (K.val.val : Set Point) (t : Real.Angle)
    rw [show x = (rotatingHallwayParts (K.val.val : Set Point)
      (t : Real.Angle)).innerCorner by rfl, hf.2.1]
    rw [show y = (rotatingHallwayParts (K.val.val : Set Point)
      (t : Real.Angle)).outerCorner by rfl, hf.2.2.1]
    module
  have hy : y = c + g • normalVector (t : Real.Angle) := by
    change (rotatingHallwayParts (K.val.val : Set Point)
      (t : Real.Angle)).outerCorner =
        (capVertices K.val t).2.2 +
          (tangentArmLengths K.val t).2.2 • normalVector (t : Real.Angle)
    exact (capTangentArm_identities K.val t).2.2.2
  have hsupport : supportValue K.val.val (u : Real.Angle) =
      inner ℝ c (normalVector (u : Real.Angle)) := by
    simpa only [u, δ, c] using rightAngle_supportValue_prev_shift n hn K ht
  have hd : inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (u : Real.Angle)) = Real.cos δ := by
    rw [hnormal, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_comm, inner_normalVector_tangentVector, inner_tangentVector_self]
    ring
  have hnum : inner ℝ x (normalVector (u : Real.Angle)) -
      (supportValue K.val.val (u : Real.Angle) - 1) =
      (g - 1) * Real.sin δ + 1 - Real.cos δ := by
    rw [hx, hy, hsupport, hnormal]
    simp only [inner_sub_left, inner_add_left,
      inner_add_right, inner_smul_right, inner_normalVector_self,
      inner_normalVector_tangentVector, real_inner_comm, inner_tangentVector_self]
    ring
  have hratio :
      (inner ℝ x (normalVector (u : Real.Angle)) -
          (supportValue K.val.val (u : Real.Angle) - 1)) /
          inner ℝ (tangentVector (t : Real.Angle)) (normalVector (u : Real.Angle)) =
        Real.tan δ * (g - 1 + Real.tan (δ / 2)) := by
    rw [hnum, hd]
    calc
      ((g - 1) * Real.sin δ + 1 - Real.cos δ) / Real.cos δ =
          Real.tan δ * (g - 1) + (1 - Real.cos δ) / Real.cos δ := by
            rw [Real.tan_eq_sin_div_cos]
            field_simp [hcδ.ne']
            ring
      _ = Real.tan δ * (g - 1) + Real.tan δ * Real.tan (δ / 2) := by
        rw [one_sub_cos_div_cos_eq_tan_mul_tan_half hδI.1 hδI.2]
      _ = Real.tan δ * (g - 1 + Real.tan (δ / 2)) := by ring
  change ENNReal.ofReal (max 0 _) = ENNReal.ofReal (_ * max 0 _)
  rw [hratio]
  congr 1
  rw [mul_max_of_nonneg _ _ (Real.tan_pos_of_pos_of_lt_pi_div_two hδI.1 hδI.2).le,
    mul_zero]

private theorem rightAngle_bRay_next_leg_length (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) {t : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions) :
    Measure.hausdorffMeasure 1
        ((rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay ∩
          (innerWallUpperHalfPlanes K.val (t + polygonStepSize n)).2) =
      ENNReal.ofReal (Real.tan (polygonStepSize n) *
        max 0 (1 - (tangentArmLengths K.val t).2.1 +
          Real.tan (polygonStepSize n / 2))) := by
  let δ := polygonStepSize n
  let x := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).innerCorner
  let y := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).outerCorner
  let c := (capVertices K.val t).2.1
  let g := (tangentArmLengths K.val t).2.1
  let u := t + δ + Real.pi / 2
  have hδI : δ ∈ Set.Ioo 0 (Real.pi / 2) := polygonStepSize_mem_Ioo n hn
  have hcδ : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hδI.1, Real.pi_pos], hδI.2⟩
  have htI : t ∈ Set.Icc 0 (Real.pi / 2) := by
    have hi := (rightAngleSet n hn).interior t ht
    change t ∈ Set.Ioo 0 (Real.pi / 2) at hi
    exact ⟨hi.1.le, hi.2.le⟩
  have hnormal : normalVector (u : Real.Angle) =
      (-Real.sin δ) • normalVector (t : Real.Angle) +
        Real.cos δ • tangentVector (t : Real.Angle) := by
    have h := normalVector_add_real t (Real.pi / 2 + δ)
    simp only [Real.cos_add, Real.sin_add, Real.cos_pi_div_two,
      Real.sin_pi_div_two, zero_mul, one_mul, zero_sub, add_zero] at h
    have hu : u = t + (Real.pi / 2 + δ) := by dsimp [u]; ring
    rw [hu]
    exact h
  have htrans : 0 < inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (u : Real.Angle)) := by
    rw [hnormal, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_comm, inner_normalVector_tangentVector, inner_tangentVector_self]
    simpa using hcδ
  rw [show (innerWallUpperHalfPlanes K.val (t + polygonStepSize n)).2 =
      normalHalfPlane (u : Real.Angle)
        (supportValue K.val.val (u : Real.Angle) - 1) true false by
    simp only [innerWallUpperHalfPlanes, u, δ]
    ]
  rw [hausdorffMeasure_bRay_inter_normalHalfPlane _ _ _ _ htrans]
  have hx : x = y - normalVector (t : Real.Angle) - tangentVector (t : Real.Angle) := by
    have hf := rotatingHallwayParts_formulas (K.val.val : Set Point) (t : Real.Angle)
    rw [show x = (rotatingHallwayParts (K.val.val : Set Point)
      (t : Real.Angle)).innerCorner by rfl, hf.2.1]
    rw [show y = (rotatingHallwayParts (K.val.val : Set Point)
      (t : Real.Angle)).outerCorner by rfl, hf.2.2.1]
    module
  have hy : y = c + g • normalVector (t : Real.Angle) := by
    change (rotatingHallwayParts (K.val.val : Set Point)
      (t : Real.Angle)).outerCorner =
        (capVertices K.val t).2.1 +
          (tangentArmLengths K.val t).2.1 • normalVector (t : Real.Angle)
    exact (capTangentArm_identities K.val t).2.2.1
  have hsupport : supportValue K.val.val (u : Real.Angle) =
      inner ℝ c (normalVector (u : Real.Angle)) := by
    simpa only [u, δ, c] using rightAngle_supportValue_next_shift n hn K ht
  have hd : inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (u : Real.Angle)) = Real.cos δ := by
    rw [hnormal, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_comm, inner_normalVector_tangentVector, inner_tangentVector_self]
    ring
  have hnum : inner ℝ x (normalVector (u : Real.Angle)) -
      (supportValue K.val.val (u : Real.Angle) - 1) =
      (1 - g) * Real.sin δ + 1 - Real.cos δ := by
    rw [hx, hy, hsupport, hnormal]
    simp only [inner_sub_left, inner_add_left, inner_add_right, inner_smul_right,
      inner_normalVector_self, inner_normalVector_tangentVector, real_inner_comm,
      inner_tangentVector_self]
    ring
  have hratio :
      (inner ℝ x (normalVector (u : Real.Angle)) -
          (supportValue K.val.val (u : Real.Angle) - 1)) /
          inner ℝ (tangentVector (t : Real.Angle)) (normalVector (u : Real.Angle)) =
        Real.tan δ * (1 - g + Real.tan (δ / 2)) := by
    rw [hnum, hd]
    calc
      ((1 - g) * Real.sin δ + 1 - Real.cos δ) / Real.cos δ =
          Real.tan δ * (1 - g) + (1 - Real.cos δ) / Real.cos δ := by
            rw [Real.tan_eq_sin_div_cos]
            field_simp [hcδ.ne']
            ring
      _ = Real.tan δ * (1 - g) + Real.tan δ * Real.tan (δ / 2) := by
        rw [one_sub_cos_div_cos_eq_tan_mul_tan_half hδI.1 hδI.2]
      _ = Real.tan δ * (1 - g + Real.tan (δ / 2)) := by ring
  change ENNReal.ofReal (max 0 _) = ENNReal.ofReal (_ * max 0 _)
  rw [hratio]
  congr 1
  rw [mul_max_of_nonneg _ _ (Real.tan_pos_of_pos_of_lt_pi_div_two hδI.1 hδI.2).le,
    mul_zero]

theorem maximumPolygonCap_leg_lengths (n : ℕ) (hn : 2 ≤ n) (hdyadic : ∃ k : ℕ, n = 2 ^ k)
    (K : PolygonCapSpace (rightAngleSet n hn))
    (hK : IsMaximumPolygonCap (rightAngleSet n hn) K)
    (t : ℝ) (ht : t ∈ (rightAngleSet n hn).directions) :
    MeasureTheory.Measure.hausdorffMeasure 1
      ((rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay ∩
        (innerWallUpperHalfPlanes K.val (t - polygonStepSize n)).2) =
      ENNReal.ofReal (Real.tan (polygonStepSize n) *
        max 0 ((tangentArmLengths K.val t).2.2 - 1 +
          Real.tan (polygonStepSize n / 2))) ∧
    MeasureTheory.Measure.hausdorffMeasure 1
      ((rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay ∩
        (innerWallUpperHalfPlanes K.val (t + polygonStepSize n)).2) =
      ENNReal.ofReal (Real.tan (polygonStepSize n) *
        max 0 (1 - (tangentArmLengths K.val t).2.1 +
          Real.tan (polygonStepSize n / 2))) := by
  exact ⟨rightAngle_bRay_prev_leg_length n hn K ht,
    rightAngle_bRay_next_leg_length n hn K ht⟩

/-- The face line of a convex body meets the two adjacent inner-wall half-planes in a set whose
length is at most `2 tan(δ/2)` less the face length. -/
theorem hausdorffMeasure_faceLine_inter_innerWalls_le (K : ConvexBody Point)
    (t δ : ℝ) (hδ0 : 0 < δ) (hδ : δ < Real.pi) :
    Measure.hausdorffMeasure 1
        ({p : Point | inner ℝ p (normalVector (t : Real.Angle)) =
            supportValue (K : Set Point) (t : Real.Angle) - 1} ∩
          (normalHalfPlane ((t - δ : ℝ) : Real.Angle)
              (supportValue (K : Set Point) ((t - δ : ℝ) : Real.Angle) - 1) true false ∩
            normalHalfPlane ((t + δ : ℝ) : Real.Angle)
              (supportValue (K : Set Point) ((t + δ : ℝ) : Real.Angle) - 1) true false)) ≤
      ENNReal.ofReal (max 0 (2 * Real.tan (δ / 2) -
        (surfaceAreaMeasure K {(t : Real.Angle)}).toReal)) := by
  have hpi := Real.pi_pos
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ0 hδ
  have hhalfcos : 0 < Real.cos (δ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hhalfsin : 0 < Real.sin (δ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have htanhalf : (1 - Real.cos δ) / Real.sin δ = Real.tan (δ / 2) := by
    have h1 : Real.sin δ = 2 * Real.sin (δ / 2) * Real.cos (δ / 2) := by
      have h := Real.sin_two_mul (δ / 2)
      rwa [show 2 * (δ / 2) = δ by ring] at h
    have h2 : Real.cos δ = 2 * Real.cos (δ / 2) ^ 2 - 1 := by
      have h := Real.cos_two_mul (δ / 2)
      rwa [show 2 * (δ / 2) = δ by ring] at h
    rw [Real.tan_eq_sin_div_cos, h1, h2, div_eq_div_iff (by positivity) hhalfcos.ne']
    nlinarith [Real.sin_sq_add_cos_sq (δ / 2)]
  have hneg : t - (t + δ) = -δ := by ring
  have hpos : t - (t - δ) = δ := by ring
  have hAn : inner ℝ (edgeVertices K (t : Real.Angle)).1 (normalVector (t : Real.Angle)) =
      supportValue (K : Set Point) (t : Real.Angle) := (edgeVertices_fst_mem K _).2
  have hBn : inner ℝ (edgeVertices K (t : Real.Angle)).2 (normalVector (t : Real.Angle)) =
      supportValue (K : Set Point) (t : Real.Angle) := (edgeVertices_snd_mem K _).2
  have hApb := inner_le_supportValue K (edgeVertices_fst_mem K (t : Real.Angle)).1
    ((t + δ : ℝ) : Real.Angle)
  have hBmb := inner_le_supportValue K (edgeVertices_snd_mem K (t : Real.Angle)).1
    ((t - δ : ℝ) : Real.Angle)
  rw [inner_normalVector_eq_frame_rotate _ t (t + δ), hneg, Real.cos_neg, Real.sin_neg,
    hAn] at hApb
  rw [inner_normalVector_eq_frame_rotate _ t (t - δ), hpos, hBn] at hBmb
  have hAB := (surfaceAreaMeasure_atom_length K (t : Real.Angle)).2.2
  have hgap : inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) =
      inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle)) +
        (surfaceAreaMeasure K {(t : Real.Angle)}).toReal := by
    rw [hAB, inner_add_left, real_inner_smul_left, inner_tangentVector_self, mul_one]
  refine le_trans (hausdorffMeasure_le_of_frame_bounds (t := t)
    (e := supportValue (K : Set Point) (t : Real.Angle) - 1)
    (lo := inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) -
      Real.tan (δ / 2))
    (hi := inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle)) +
      Real.tan (δ / 2)) ?_) (le_of_eq ?_)
  · rintro p ⟨hline, hprev, hnext⟩
    have hpn : inner ℝ p (normalVector (t : Real.Angle)) =
        supportValue (K : Set Point) (t : Real.Angle) - 1 := hline
    change supportValue (K : Set Point) ((t - δ : ℝ) : Real.Angle) - 1 ≤
      inner ℝ p (normalVector ((t - δ : ℝ) : Real.Angle)) at hprev
    change supportValue (K : Set Point) ((t + δ : ℝ) : Real.Angle) - 1 ≤
      inner ℝ p (normalVector ((t + δ : ℝ) : Real.Angle)) at hnext
    rw [inner_normalVector_eq_frame_rotate p t (t - δ), hpos, hpn] at hprev
    rw [inner_normalVector_eq_frame_rotate p t (t + δ), hneg, Real.cos_neg, Real.sin_neg,
      hpn] at hnext
    have hkeyU : (inner ℝ p (tangentVector (t : Real.Angle)) -
        inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle))) *
          Real.sin δ ≤ 1 - Real.cos δ := by nlinarith [hprev, hBmb]
    have hkeyL : (inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) -
        inner ℝ p (tangentVector (t : Real.Angle))) * Real.sin δ ≤ 1 - Real.cos δ := by
      nlinarith [hnext, hApb]
    have hU := (le_div_iff₀ hsin).mpr hkeyU
    have hL := (le_div_iff₀ hsin).mpr hkeyL
    rw [htanhalf] at hU hL
    exact ⟨hpn, by linarith, by linarith⟩
  · have hlen : inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle)) +
        Real.tan (δ / 2) -
        (inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) -
          Real.tan (δ / 2)) =
        2 * Real.tan (δ / 2) - (surfaceAreaMeasure K {(t : Real.Angle)}).toReal := by
      rw [hgap]
      ring
    rw [hlen]

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
# Bounds / Lower / Profile
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Integrate the reflected arm profile through the second magic function and add one. -/
def armIntegralOperator (f : C(Set.Icc (0 : ℝ) (Real.pi / 2), NNReal)) :
    C(Set.Icc (0 : ℝ) (Real.pi / 2), ℝ) where
  toFun x := 1 + ∫ u in (0 : ℝ)..(x : ℝ),
    magicFunctions.2 (f (Set.projIcc 0 (Real.pi / 2) (by positivity) (Real.pi / 2 - u)))
  continuous_toFun := by
    have hf : Continuous (fun u : ℝ ↦
        magicFunctions.2 (f (Set.projIcc 0 (Real.pi / 2) (by positivity)
          (Real.pi / 2 - u)))) := by
      unfold magicFunctions
      fun_prop
    exact continuous_const.add
      ((intervalIntegral.differentiable_integral_of_continuous hf).continuous.comp
        continuous_subtype_val)

/-- Iteratively improve the nonnegative arm lower bound by taking the maximum with its
integral update. -/
def armLowerBoundSequence : ℕ → C(Set.Icc (0 : ℝ) (Real.pi / 2), NNReal)
  | 0 => ⟨fun _ ↦ 0, continuous_const⟩
  | n + 1 =>
      ⟨fun x ↦ max (armLowerBoundSequence n x)
          (Real.toNNReal (armIntegralOperator (armLowerBoundSequence n) x)),
        (armLowerBoundSequence n).continuous.max
          (continuous_real_toNNReal.comp (armIntegralOperator (armLowerBoundSequence
            n)).continuous)⟩

/-- The continuous profile `max (1 - x) c` on the quarter-turn interval. -/
def lowerBoundProfile (c : Set.Icc (0 : ℝ) 1) :
    C(Set.Icc (0 : ℝ) (Real.pi / 2), ℝ) where
  toFun x := max (1 - (x : ℝ)) (c : ℝ)
  continuous_toFun := (continuous_const.sub continuous_subtype_val).max continuous_const

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
# Bounds / Niche Limits
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace MovingSofa

/-- Support values converge under Hausdorff convergence of caps. -/
theorem tendsto_supportValue_of_hausdorff {ω : ℝ}
    (K : ℕ → CapSpace ω) (L : CapSpace ω)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun i ↦ supportValue (K i).val (t : Real.Angle)) atTop
      (𝓝 (supportValue L.val (t : Real.Angle))) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ dist_nonneg) _ hlim
  intro i
  simpa only [Real.dist_eq, vectorSupport, supportValue] using
    (compactSet_support_continuity (K i).val L.val (K i).val.nonempty
      (K i).val.isCompact L.val.nonempty L.val.isCompact).2.1
        (normalVector (t : Real.Angle)) (norm_normalVector_real t)

private theorem volume_normalLine_eq_zero (t c : ℝ) :
    volume {p : Point | inner ℝ p (normalVector (t : Real.Angle)) = c} = 0 := by
  let u := normalVector (t : Real.Angle)
  let f : Point →ᵃ[ℝ] ℝ := (innerSL ℝ u).toLinearMap.toAffineMap
  let A := (AffineSubspace.mk' c (⊥ : Submodule ℝ ℝ)).comap f
  have hA : (A : Set Point) = {p : Point | inner ℝ p u = c} := by
    ext p
    simp [A, f, AffineSubspace.mem_mk', real_inner_comm, sub_eq_zero]
  rw [← hA]
  apply Measure.addHaar_affineSubspace
  intro htop
  have hp : (c + 1) • u ∈ A := by rw [htop]; trivial
  rw [← SetLike.mem_coe, hA] at hp
  have hu : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_normalVector_real]
    norm_num
  change inner ℝ ((c + 1) • u) u = c at hp
  rw [real_inner_smul_left, hu, mul_one] at hp
  linarith

private theorem eventually_lt_iff_of_ne {f : ℕ → ℝ} {a x : ℝ}
    (hf : Tendsto f atTop (𝓝 a)) (hxa : x ≠ a) :
    ∀ᶠ i in atTop, (x < f i ↔ x < a) := by
  rcases lt_or_gt_of_ne hxa with h | h
  · filter_upwards [hf.eventually_const_lt h] with i hi
    exact iff_of_true hi h
  · filter_upwards [hf.eventually_lt_const h] with i hi
    exact iff_of_false (not_lt_of_ge hi.le) (not_lt_of_ge h.le)

private theorem ae_eventually_mem_polygonNiche_iff (Θ : AngleSet)
    (K : ℕ → CapSpace Θ.angle) (L : CapSpace Θ.angle)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) :
    ∀ᵐ p ∂volume, ∀ᶠ i in atTop, (p ∈ polygonNiche Θ (K i) ↔ p ∈ polygonNiche Θ L) := by
  have hae (t : ℝ) : ∀ᵐ p ∂volume,
      inner ℝ p (normalVector (t : Real.Angle)) ≠ supportValue L.val (t : Real.Angle) - 1 := by
    apply ae_iff.mpr
    simpa only [not_not] using volume_normalLine_eq_zero t
      (supportValue L.val (t : Real.Angle) - 1)
  have hall : ∀ᵐ p ∂volume, ∀ t ∈ Θ.directions,
      inner ℝ p (normalVector (t : Real.Angle)) ≠ supportValue L.val (t : Real.Angle) - 1 ∧
      inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≠
        supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 :=
    Θ.directions.eventually_all.mpr fun t _ ↦ (hae t).and (hae (t + Real.pi / 2))
  filter_upwards [hall] with p hp
  have hq (t : ℝ) (ht : t ∈ Θ.directions) : ∀ᶠ i in atTop,
      (p ∈ innerQuadrant (K i).val t ↔ p ∈ innerQuadrant L.val t) := by
    have h₁ := eventually_lt_iff_of_ne
      ((tendsto_supportValue_of_hausdorff K L hlim t).sub_const 1) (hp t ht).1
    have h₂ := eventually_lt_iff_of_ne
      ((tendsto_supportValue_of_hausdorff K L hlim (t + Real.pi / 2)).sub_const 1)
      (hp t ht).2
    filter_upwards [h₁, h₂] with i h₁ h₂
    exact and_congr h₁ h₂
  filter_upwards [Θ.directions.eventually_all.mpr hq] with i hi
  simp only [polygonNiche, Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨hf, t, ht, hqt⟩
    exact ⟨hf, t, ht, (hi t ht).mp hqt⟩
  · rintro ⟨hf, t, ht, hqt⟩
    exact ⟨hf, t, ht, (hi t ht).mpr hqt⟩

private theorem eventually_le_iff_of_ne {f : ℕ → ℝ} {a x : ℝ}
    (hf : Tendsto f atTop (𝓝 a)) (hxa : x ≠ a) :
    ∀ᶠ i in atTop, (x ≤ f i ↔ x ≤ a) := by
  rcases lt_or_gt_of_ne hxa with h | h
  · filter_upwards [hf.eventually_const_lt h] with i hi
    exact iff_of_true hi.le h.le
  · filter_upwards [hf.eventually_lt_const h] with i hi
    exact iff_of_false (not_le_of_gt hi) (not_le_of_gt h)

private theorem ae_eventually_mem_angleCap_iff (Θ : AngleSet)
    (K : ℕ → CapSpace Θ.angle) (L : CapSpace Θ.angle)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) :
    ∀ᵐ p ∂volume, ∀ᶠ i in atTop, (p ∈ angleCap Θ (K i) ↔ p ∈ angleCap Θ L) := by
  have hae (t : ℝ) : ∀ᵐ p ∂volume,
      inner ℝ p (normalVector (t : Real.Angle)) ≠ supportValue L.val (t : Real.Angle) := by
    apply ae_iff.mpr
    simpa only [not_not] using volume_normalLine_eq_zero t
      (supportValue L.val (t : Real.Angle))
  have hall : ∀ᵐ p ∂volume, ∀ t ∈ Θ.directions,
      inner ℝ p (normalVector (t : Real.Angle)) ≠ supportValue L.val (t : Real.Angle) ∧
      inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≠
        supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle) :=
    Θ.directions.eventually_all.mpr fun t _ ↦ (hae t).and (hae (t + Real.pi / 2))
  filter_upwards [hall] with p hp
  have hq (t : ℝ) (ht : t ∈ Θ.directions) : ∀ᶠ i in atTop,
      (inner ℝ p (normalVector (t : Real.Angle)) ≤ supportValue (K i).val (t : Real.Angle) ↔
        inner ℝ p (normalVector (t : Real.Angle)) ≤ supportValue L.val (t : Real.Angle)) ∧
      (inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≤
          supportValue (K i).val ((t + Real.pi / 2 : ℝ) : Real.Angle) ↔
        inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≤
          supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle)) :=
    (eventually_le_iff_of_ne (tendsto_supportValue_of_hausdorff K L hlim t) (hp t ht).1).and
      (eventually_le_iff_of_ne (tendsto_supportValue_of_hausdorff K L hlim
        (t + Real.pi / 2)) (hp t ht).2)
  filter_upwards [Θ.directions.eventually_all.mpr hq] with i hi
  simp only [mem_angleCap_iff]
  apply and_congr_right
  intro _
  exact forall_congr' fun t ↦ forall_congr' fun ht ↦ and_congr (hi t ht).1 (hi t ht).2

private theorem exists_angleCap_norm_bound (Θ : AngleSet)
    (K : ℕ → CapSpace Θ.angle) (L : CapSpace Θ.angle)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) :
    ∃ R : ℝ, ∀ i p, p ∈ angleCap Θ (K i) → ‖p‖ ≤ R := by
  obtain ⟨t, ht⟩ := Θ.nonempty
  have hti := Θ.interior t ht
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, hti.1], hti.2.trans_le Θ.angle_le⟩
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi hti.1
    (by linarith [hti.2, Θ.angle_le, Real.pi_pos])
  obtain ⟨A, hA⟩ := (Metric.isBounded_range_of_tendsto _
    (tendsto_supportValue_of_hausdorff K L hlim t)).exists_norm_le
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _
    (tendsto_supportValue_of_hausdorff K L hlim (t + Real.pi / 2))).exists_norm_le
  let l := -|B| / Real.sin t
  let r := |A| / Real.cos t
  let M := |l| + |r|
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M + 1, fun i p hp ↦ ?_⟩
  have haBound : supportValue (K i).val (t : Real.Angle) ≤ |A| :=
    (le_abs_self _).trans ((hA _ (Set.mem_range_self i)).trans (le_abs_self A))
  have hbBound : supportValue (K i).val ((t + Real.pi / 2 : ℝ) : Real.Angle) ≤ |B| :=
    (le_abs_self _).trans ((hB _ (Set.mem_range_self i)).trans (le_abs_self B))
  obtain ⟨⟨hy, _⟩, hnormals⟩ := (mem_angleCap_iff Θ (K i) p).mp hp
  obtain ⟨ha, hb⟩ := hnormals t ht
  simp [normalVector, frame, PiLp.inner_apply, Real.cos_add, Real.sin_add,
    -Real.Angle.coe_add] at ha hb
  have hl : l ≤ p 0 := by
    apply (div_le_iff₀ hs).mpr
    nlinarith [mul_nonneg hc.le hy.1]
  have hr : p 0 ≤ r := by
    apply (le_div_iff₀ hc).mpr
    nlinarith [mul_nonneg hs.le hy.1]
  have hx : |p 0| ≤ M := by
    apply abs_le.mpr
    dsimp [M]
    constructor <;> linarith [neg_abs_le l, le_abs_self r, abs_nonneg l, abs_nonneg r]
  have hx2 := (sq_le_sq₀ (abs_nonneg (p 0)) hM).mpr hx
  have hy2 : (p 1) ^ 2 ≤ 1 := by nlinarith [hy.1, hy.2]
  have hn := EuclideanSpace.norm_sq_eq p
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hn hx2
  nlinarith [norm_nonneg p]

private theorem tendsto_polygonNiche_area (Θ : AngleSet)
    (K : ℕ → CapSpace Θ.angle) (L : CapSpace Θ.angle)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ ClassicalResults.area (polygonNiche Θ (K i))) atTop
      (𝓝 (ClassicalResults.area (polygonNiche Θ L))) := by
  obtain ⟨R, hR, _, hpoly⟩ := niche_uniform_bounds.2.2 (fun _ ↦ Θ.angle) K L.val hlim
  let C := Metric.closedBall (0 : Point) (2 * R)
  have hcompact : IsCompact C := isCompact_closedBall _ _
  have hsubset (i : ℕ) : polygonNiche Θ (K i) ⊆ C := by
    intro p hp
    obtain ⟨hx, hy, hh⟩ := hpoly i Θ (K i) rfl hp
    change dist p 0 ≤ 2 * R
    rw [dist_zero_right]
    have hx2 := (sq_le_sq₀ (abs_nonneg (p 0)) hR).mpr hx
    have hy2 := (sq_le_sq₀ hy hR).mpr hh
    have hn := EuclideanSpace.norm_sq_eq p
    simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hn hx2
    nlinarith [norm_nonneg p, sq_nonneg R]
  have hCint : Integrable (C.indicator fun _ ↦ (1 : ℝ)) :=
    (integrableOn_const hcompact.measure_lt_top.ne).integrable_indicator hcompact.measurableSet
  have hpointwise : ∀ᵐ p ∂volume,
      Tendsto (fun i ↦ (polygonNiche Θ (K i)).indicator (fun _ ↦ (1 : ℝ)) p)
        atTop (𝓝 ((polygonNiche Θ L).indicator (fun _ ↦ (1 : ℝ)) p)) := by
    filter_upwards [ae_eventually_mem_polygonNiche_iff Θ K L hlim] with p hp
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [hp] with i hi
    by_cases h : p ∈ polygonNiche Θ L
    · simp [h, hi.mpr h]
    · have hn : p ∉ polygonNiche Θ (K i) := fun hk ↦ h (hi.mp hk)
      simp [h, hn]
  have hconv := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (F := fun i ↦ (polygonNiche Θ (K i)).indicator fun _ ↦ (1 : ℝ))
    (f := (polygonNiche Θ L).indicator fun _ ↦ (1 : ℝ))
    (C.indicator fun _ ↦ (1 : ℝ))
    (Eventually.of_forall fun i ↦
      (measurable_const.indicator (measurableSet_polygonNiche Θ (K i))).aestronglyMeasurable)
    (Eventually.of_forall fun i ↦ Eventually.of_forall fun p ↦ by
      by_cases hp : p ∈ polygonNiche Θ (K i)
      · simp [hp, hsubset i hp]
      · by_cases hpc : p ∈ C <;> simp [hp, hpc]) hCint hpointwise
  have harea (P : CapSpace Θ.angle) :
      (∫ p, (polygonNiche Θ P).indicator (fun _ ↦ (1 : ℝ)) p) =
        ClassicalResults.area (polygonNiche Θ P) := by
    exact integral_indicator_one (measurableSet_polygonNiche Θ P)
  simpa only [harea] using hconv

private theorem tendsto_angleCap_area (Θ : AngleSet)
    (K : ℕ → CapSpace Θ.angle) (L : CapSpace Θ.angle)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ ClassicalResults.area (angleCap Θ (K i))) atTop
      (𝓝 (ClassicalResults.area (angleCap Θ L))) := by
  obtain ⟨R, hR⟩ := exists_angleCap_norm_bound Θ K L hlim
  let C := Metric.closedBall (0 : Point) R
  have hcompact : IsCompact C := isCompact_closedBall _ _
  have hsubset (i : ℕ) : angleCap Θ (K i) ⊆ C := by
    intro p hp
    simpa only [C, Metric.mem_closedBall, dist_zero_right] using hR i p hp
  have hCint : Integrable (C.indicator fun _ ↦ (1 : ℝ)) :=
    (integrableOn_const hcompact.measure_lt_top.ne).integrable_indicator hcompact.measurableSet
  have hpointwise : ∀ᵐ p ∂volume,
      Tendsto (fun i ↦ (angleCap Θ (K i)).indicator (fun _ ↦ (1 : ℝ)) p)
        atTop (𝓝 ((angleCap Θ L).indicator (fun _ ↦ (1 : ℝ)) p)) := by
    filter_upwards [ae_eventually_mem_angleCap_iff Θ K L hlim] with p hp
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [hp] with i hi
    by_cases h : p ∈ angleCap Θ L
    · simp [h, hi.mpr h]
    · have hn : p ∉ angleCap Θ (K i) := fun hk ↦ h (hi.mp hk)
      simp [h, hn]
  have hconv := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (F := fun i ↦ (angleCap Θ (K i)).indicator fun _ ↦ (1 : ℝ))
    (f := (angleCap Θ L).indicator fun _ ↦ (1 : ℝ))
    (C.indicator fun _ ↦ (1 : ℝ))
    (Eventually.of_forall fun i ↦
      (measurable_const.indicator (isClosed_angleCap Θ (K i)).measurableSet).aestronglyMeasurable)
    (Eventually.of_forall fun i ↦ Eventually.of_forall fun p ↦ by
      by_cases hp : p ∈ angleCap Θ (K i)
      · simp [hp, hsubset i hp]
      · by_cases hpc : p ∈ C <;> simp [hp, hpc]) hCint hpointwise
  have harea (P : CapSpace Θ.angle) :
      (∫ p, (angleCap Θ P).indicator (fun _ ↦ (1 : ℝ)) p) =
        ClassicalResults.area (angleCap Θ P) := by
    exact integral_indicator_one (isClosed_angleCap Θ P).measurableSet
  simpa only [harea] using hconv

theorem polygonArea_continuity (Θ : AngleSet)
    (K : ℕ → CapSpace Θ.angle) (L : CapSpace Θ.angle)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ ClassicalResults.area (polygonNiche Θ (K i)))
      atTop (𝓝 (ClassicalResults.area (polygonNiche Θ L))) ∧
    Tendsto (fun i ↦ polygonAreaFunctional Θ (K i))
      atTop (𝓝 (polygonAreaFunctional Θ L)) := by
  exact ⟨tendsto_polygonNiche_area Θ K L hlim,
    (tendsto_angleCap_area Θ K L hlim).sub (tendsto_polygonNiche_area Θ K L hlim)⟩

private theorem polygonNiche_mono_directions (Θ Ψ : AngleSet)
    (K : CapSpace Θ.angle) (L : CapSpace Ψ.angle)
    (hangle : Θ.angle = Ψ.angle) (hcarrier : (K.val : Set Point) = (L.val : Set Point))
    (hsub : Θ.directions ⊆ Ψ.directions) :
    polygonNiche Θ K ⊆ polygonNiche Ψ L := by
  rintro p ⟨hp, hq⟩
  obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hq
  refine ⟨?_, Set.mem_iUnion₂.mpr ⟨t, hsub ht, ?_⟩⟩
  · simpa only [hangle] using hp
  · simpa only [hcarrier] using hpt

/-- Every niche point belongs to all sufficiently fine uniform polygon niches. -/
theorem eventually_mem_polygonNiche_of_mem_capNiche (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (hmono : StrictMono n) (K : CapSpace ω) {p : Point} (hp : p ∈ capNiche K) :
    ∀ᶠ i in atTop, p ∈ polygonNiche (uniformAngleSet ω hω hω' (n i) (hn i)) K := by
  obtain ⟨hfan, hq⟩ := hp
  obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hq
  have hopen : IsOpen {s : ℝ | p ∈ innerQuadrant K.val s} := by
    apply IsOpen.inter
    · exact isOpen_lt (continuous_const.inner continuous_normalVector_real)
        ((continuous_supportValue_real K.val).sub continuous_const)
    · exact isOpen_lt
        (continuous_const.inner (continuous_normalVector_real.comp
          (continuous_id.add continuous_const)))
        (((continuous_supportValue_real K.val).comp
          (continuous_id.add continuous_const)).sub continuous_const)
  obtain ⟨a, b, ⟨hat, htb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds hpt)
  have hat' : max 0 a < t := max_lt ht.1 hat
  have htb' : t < min ω b := lt_min ht.2 htb
  filter_upwards [eventually_exists_uniformAngleSet_mem_Ioo ω hω hω' n hn hmono
    (le_max_left 0 a) (hat'.trans htb') (min_le_left ω b)] with i hi
  obtain ⟨s, hs, hsa, hsb⟩ := hi
  refine ⟨hfan, Set.mem_iUnion₂.mpr ⟨s, hs, hab ?_⟩⟩
  exact ⟨(le_max_right 0 a).trans_lt hsa, hsb.trans_le (min_le_right ω b)⟩

private theorem iUnion_uniform_polygonNiche (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (hmono : StrictMono n) (K : CapSpace ω) :
    (⋃ i, polygonNiche (uniformAngleSet ω hω hω' (n i) (hn i)) K) = capNiche K := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun i ↦
      polygonNiche_subset_capNiche (uniformAngleSet ω hω hω' (n i) (hn i)) K
  · intro p hp
    obtain ⟨i, hi⟩ := (eventually_mem_polygonNiche_of_mem_capNiche ω hω hω' n hn hmono K hp).exists
    exact Set.mem_iUnion.mpr ⟨i, hi⟩

private theorem tendsto_uniform_polygonNiche_area (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (hmono : StrictMono n) (hdyadic : ∀ i, ∃ k : ℕ, n i = 2 ^ k) (K : CapSpace ω) :
    Tendsto (fun i ↦ ClassicalResults.area
      (polygonNiche (uniformAngleSet ω hω hω' (n i) (hn i)) K)) atTop
      (𝓝 (ClassicalResults.area (capNiche K))) := by
  have hmon : Monotone (fun i ↦ polygonNiche (uniformAngleSet ω hω hω' (n i) (hn i)) K) := by
    intro i j hij
    exact polygonNiche_mono_directions
      (uniformAngleSet ω hω hω' (n i) (hn i))
      (uniformAngleSet ω hω hω' (n j) (hn j)) K K rfl rfl
      (uniformAngleSet_directions_mono_of_dyadic ω hω hω' n hn hmono.monotone hdyadic hij)
  have hlim := tendsto_measure_iUnion_atTop (μ := volume) hmon
  rw [iUnion_uniform_polygonNiche ω hω hω' n hn hmono K] at hlim
  exact (ENNReal.tendsto_toReal (niche_uniform_bounds.1 ω K).2.2.1.ne).comp hlim

theorem maximizingPolygon_nicheArea_limit (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (hmono : StrictMono n) (hdyadic : ∀ i, ∃ k : ℕ, n i = 2 ^ k)
    (P : ∀ i, PolygonCapSpace (uniformAngleSet ω hω hω' (n i) (hn i)))
    (hmax : ∀ i, IsMaximumPolygonCap _ (P i)) (K : CapSpace ω)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((P i).val.val : Set Point)
      (K.val : Set Point)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ ClassicalResults.area
      (polygonNiche (uniformAngleSet ω hω hω' (n i) (hn i)) (P i).val))
      atTop (𝓝 (ClassicalResults.area (capNiche K))) := by
  let Θ (i : ℕ) := uniformAngleSet ω hω hω' (n i) (hn i)
  have hupper (i : ℕ) :
      ClassicalResults.area (polygonNiche (Θ i) (P i).val) ≤
        ClassicalResults.area ((P i).val.val : Set Point) - capAreaFunctional K := by
    have hmax' := polygonAreaFunctional_le_maximum (Θ i) (P i) (hmax i) K
    have hbound := (polygonArea_upperBound (Θ i)).2 K
    have harea := (polygonArea_upperBound (Θ i)).1 (P i)
    have h := hbound.trans hmax'
    rw [harea] at h
    exact le_sub_comm.mp h
  have hupperlim : Tendsto
      (fun i ↦ ClassicalResults.area ((P i).val.val : Set Point) - capAreaFunctional K)
      atTop (𝓝 (ClassicalResults.area (capNiche K))) := by
    convert (convexArea_hausdorff_continuity (fun i ↦ (P i).val.val) K.val hlim).sub_const
      (capAreaFunctional K) using 1
    simp only [capAreaFunctional, sub_sub_cancel]
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hex := (tendsto_uniform_polygonNiche_area ω hω hω' n hn hmono hdyadic
      K).eventually_const_lt ha
    obtain ⟨m, hm⟩ := hex.exists
    have hfixed := (polygonArea_continuity (Θ m) (fun i ↦ (P i).val) K hlim).1
    filter_upwards [hfixed.eventually_const_lt hm, eventually_ge_atTop m] with i hi hmi
    have hsub : polygonNiche (Θ m) (P i).val ⊆ polygonNiche (Θ i) (P i).val :=
      polygonNiche_mono_directions (Θ m) (Θ i) (P i).val (P i).val rfl rfl
        (uniformAngleSet_directions_mono_of_dyadic ω hω hω' n hn hmono.monotone hdyadic hmi)
    have hle : ClassicalResults.area (polygonNiche (Θ m) (P i).val) ≤
        ClassicalResults.area (polygonNiche (Θ i) (P i).val) :=
      ENNReal.toReal_mono (niche_uniform_bounds.2.1 (Θ i) (P i).val).2.2.1.ne (measure_mono hsub)
    exact hi.trans_le hle
  · intro b hb
    filter_upwards [hupperlim.eventually_lt_const hb] with i hi
    exact (hupper i).trans_lt hi

end MovingSofa

end

end

end
