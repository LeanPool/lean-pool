/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Area.Foundations.Development004
public import LeanPool.MovingSofa.Area.Applications.Development001
public import LeanPool.MovingSofa.Bounds.Foundations.Development006
/-!
# Moving sofa: related mathematical developments

* `Area.Mamikon.Tails`.
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
# Area / Mamikon / Tails
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The signed area between a convex boundary arc and its endpoint tangent segments. -/
def tangentMamikonValue (K : ConvexBody Point) (a b : ℝ) : ℝ :=
  segmentArea (edgeVertices K (a : Real.Angle)).1
      (supportingIntersection K (a : Real.Angle) (b : Real.Angle)) +
    segmentArea (supportingIntersection K (a : Real.Angle) (b : Real.Angle))
      (edgeVertices K (b : Real.Angle)).2 - convexArcArea K a b

/-- The Mamikon value of the right tail on its Gerver angle interval. -/
def rightTailMamikon (B : ConvexBody Point) : ℝ :=
  tangentMamikonValue B (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2)

/-- The Mamikon value of the left tail on its Gerver angle interval. -/
def leftTailMamikon (D : ConvexBody Point) : ℝ :=
  tangentMamikonValue D (3 * Real.pi / 2) (3 * Real.pi / 2 + paperGerverConstants.2.2)

/-- Bundle the right and left tail Mamikon functionals. -/
def tailMamikonFunctionals : (ConvexBody Point → ℝ) × (ConvexBody Point → ℝ) :=
  (rightTailMamikon, leftTailMamikon)

/-- The support and endpoint identities of a cap-tail triple, in segment-area form. -/
theorem tailFanPoint_identities
    (K : RightAngleCapSpace) (B D : ConvexBody Point) {r l : ℝ}
    (hr : r ∈ Set.Ioo 0 (Real.pi / 2)) (hl : l ∈ Set.Ioo 0 (Real.pi / 2))
    (hB1 : supportValue (B : Set Point) ((Real.pi + r : ℝ) : Real.Angle) =
      1 - supportValue (K.1 : Set Point) ((r : ℝ) : Real.Angle))
    (hB2 : supportValue (B : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0)
    (hD1 : supportValue (D : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0)
    (hD2 : supportValue (D : Set Point) ((3 * Real.pi / 2 + l : ℝ) : Real.Angle) =
      1 - supportValue (K.1 : Set Point) ((Real.pi / 2 + l : ℝ) : Real.Angle)) :
    supportingIntersection B ((Real.pi + r : ℝ) : Real.Angle)
        ((3 * Real.pi / 2 : ℝ) : Real.Angle) = (wedgeEndpoints K r).1 ∧
    supportingIntersection D ((3 * Real.pi / 2 : ℝ) : Real.Angle)
        ((3 * Real.pi / 2 + l : ℝ) : Real.Angle) = (wedgeEndpoints K l).2 ∧
    segmentArea (wedgeEndpoints K r).1
        (edgeVertices B ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2 = 0 ∧
    segmentArea (edgeVertices D ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1
        (wedgeEndpoints K l).2 = 0 ∧
    segmentArea (capInnerCorner K r) (wedgeEndpoints K r).1 -
        segmentArea (edgeVertices B ((Real.pi + r : ℝ) : Real.Angle)).1
          (wedgeEndpoints K r).1 =
      segmentArea (capInnerCorner K r)
        (edgeVertices B ((Real.pi + r : ℝ) : Real.Angle)).1 ∧
    segmentArea (wedgeEndpoints K l).2 (capInnerCorner K l) -
        segmentArea (wedgeEndpoints K l).2
          (edgeVertices D ((3 * Real.pi / 2 + l : ℝ) : Real.Angle)).2 =
      segmentArea (edgeVertices D ((3 * Real.pi / 2 + l : ℝ) : Real.Angle)).2
        (capInnerCorner K l) := by
  obtain ⟨hr0, hr2⟩ := hr
  obtain ⟨hl0, hl2⟩ := hl
  have hpi := Real.pi_pos
  have hcosr : 0 < Real.cos r := Real.cos_pos_of_mem_Ioo ⟨by linarith, hr2⟩
  have hsinl : 0 < Real.sin l := Real.sin_pos_of_pos_of_lt_pi hl0 (by linarith)
  have hcast : ∀ a b : ℝ, a = b → ((a : ℝ) : Real.Angle) = ((b : ℝ) : Real.Angle) :=
    fun a b h => by rw [h]
  -- opposite normals
  have hnr : normalVector ((Real.pi + r : ℝ) : Real.Angle) =
      -normalVector ((r : ℝ) : Real.Angle) := by
    rw [hcast _ _ (show Real.pi + r = r + Real.pi by ring), normalVector_add_pi]
  have hn32 : normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
      -normalVector ((Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [hcast _ _ (show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring), normalVector_add_pi]
  have hn32l : normalVector ((3 * Real.pi / 2 + l : ℝ) : Real.Angle) =
      -normalVector ((Real.pi / 2 + l : ℝ) : Real.Angle) := by
    rw [hcast _ _ (show 3 * Real.pi / 2 + l = (Real.pi / 2 + l) + Real.pi by ring),
      normalVector_add_pi]
  have hnl : normalVector ((Real.pi / 2 + l : ℝ) : Real.Angle) =
      tangentVector ((l : ℝ) : Real.Angle) := by
    rw [hcast _ _ (show Real.pi / 2 + l = l + Real.pi / 2 by ring),
      normalVector_add_pi_div_two_real]
  have hKl : supportValue (K.1 : Set Point) ((l + Real.pi / 2 : ℝ) : Real.Angle) =
      supportValue (K.1 : Set Point) ((Real.pi / 2 + l : ℝ) : Real.Angle) := by
    rw [hcast _ _ (show l + Real.pi / 2 = Real.pi / 2 + l by ring)]
  -- the two fan points
  have h1 : inner ℝ (wedgeEndpoints K r).1 (normalVector ((r : ℝ) : Real.Angle)) =
      supportValue (K.1 : Set Point) ((r : ℝ) : Real.Angle) - 1 := by
    show inner ℝ (((supportValue (K.1 : Set Point) ((r : ℝ) : Real.Angle) - 1) /
      Real.cos r) • normalVector 0) _ = _
    rw [real_inner_smul_left, ← Real.Angle.coe_zero, inner_normalVector_normalVector,
      zero_sub, Real.cos_neg]
    field_simp
  have h2 : inner ℝ (wedgeEndpoints K r).1
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    show inner ℝ (((supportValue (K.1 : Set Point) ((r : ℝ) : Real.Angle) - 1) /
      Real.cos r) • normalVector 0) _ = _
    rw [real_inner_smul_left, ← Real.Angle.coe_zero, inner_normalVector_normalVector,
      zero_sub, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
  have h5 : inner ℝ (wedgeEndpoints K l).2
      (normalVector ((Real.pi / 2 + l : ℝ) : Real.Angle)) =
      supportValue (K.1 : Set Point) ((Real.pi / 2 + l : ℝ) : Real.Angle) - 1 := by
    show inner ℝ (((supportValue (K.1 : Set Point) ((l + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
      Real.cos (Real.pi / 2 - l)) • tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) _ = _
    rw [real_inner_smul_left, inner_tangentVector_normalVector_real,
      Real.cos_pi_div_two_sub, hKl, show Real.pi / 2 + l - Real.pi / 2 = l by ring]
    field_simp
  have h6 : inner ℝ (wedgeEndpoints K l).2
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    show inner ℝ (((supportValue (K.1 : Set Point) ((l + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
      Real.cos (Real.pi / 2 - l)) • tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) _ = _
    rw [real_inner_smul_left, inner_tangentVector_normalVector_real, sub_self,
      Real.sin_zero, mul_zero]
  -- the two supporting intersections
  have hs1 : Real.sin (3 * Real.pi / 2 - (Real.pi + r)) ≠ 0 := by
    rw [show 3 * Real.pi / 2 - (Real.pi + r) = Real.pi / 2 - r by ring, Real.sin_pi_div_two_sub]
    exact ne_of_gt hcosr
  have hs2 : Real.sin (3 * Real.pi / 2 + l - 3 * Real.pi / 2) ≠ 0 := by
    rw [show 3 * Real.pi / 2 + l - 3 * Real.pi / 2 = l by ring]
    exact ne_of_gt hsinl
  have h3 : inner ℝ (supportingIntersection B ((Real.pi + r : ℝ) : Real.Angle)
      ((3 * Real.pi / 2 : ℝ) : Real.Angle)) (normalVector ((r : ℝ) : Real.Angle)) =
      supportValue (K.1 : Set Point) ((r : ℝ) : Real.Angle) - 1 := by
    have h := supportingIntersection_inner_left B (Real.pi + r) (3 * Real.pi / 2)
    rw [hnr, inner_neg_right, hB1] at h
    linarith
  have h4 : inner ℝ (supportingIntersection B ((Real.pi + r : ℝ) : Real.Angle)
      ((3 * Real.pi / 2 : ℝ) : Real.Angle))
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    have h := supportingIntersection_inner_right B (Real.pi + r) (3 * Real.pi / 2) hs1
    rw [hn32, inner_neg_right, hB2] at h
    linarith
  have h7 : inner ℝ (supportingIntersection D ((3 * Real.pi / 2 : ℝ) : Real.Angle)
      ((3 * Real.pi / 2 + l : ℝ) : Real.Angle))
      (normalVector ((Real.pi / 2 + l : ℝ) : Real.Angle)) =
      supportValue (K.1 : Set Point) ((Real.pi / 2 + l : ℝ) : Real.Angle) - 1 := by
    have h := supportingIntersection_inner_right D (3 * Real.pi / 2)
      (3 * Real.pi / 2 + l) hs2
    rw [hn32l, inner_neg_right, hD2] at h
    linarith
  have h8 : inner ℝ (supportingIntersection D ((3 * Real.pi / 2 : ℝ) : Real.Angle)
      ((3 * Real.pi / 2 + l : ℝ) : Real.Angle))
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    have h := supportingIntersection_inner_left D (3 * Real.pi / 2) (3 * Real.pi / 2 + l)
    rw [hn32, inner_neg_right, hD1] at h
    linarith
  -- the cap corners and the tail vertices
  have h9 : inner ℝ (capInnerCorner K r) (normalVector ((r : ℝ) : Real.Angle)) =
      supportValue (K.1 : Set Point) ((r : ℝ) : Real.Angle) - 1 := (inner_capInnerCorner K r).1
  have h13 : inner ℝ (capInnerCorner K l)
      (normalVector ((Real.pi / 2 + l : ℝ) : Real.Angle)) =
      supportValue (K.1 : Set Point) ((Real.pi / 2 + l : ℝ) : Real.Angle) - 1 := by
    rw [hnl, (inner_capInnerCorner K l).2, hKl]
  have h10 : inner ℝ (edgeVertices B ((Real.pi + r : ℝ) : Real.Angle)).1
      (normalVector ((r : ℝ) : Real.Angle)) =
      supportValue (K.1 : Set Point) ((r : ℝ) : Real.Angle) - 1 := by
    have h : inner ℝ (edgeVertices B ((Real.pi + r : ℝ) : Real.Angle)).1
        (normalVector ((Real.pi + r : ℝ) : Real.Angle)) =
        supportValue (B : Set Point) ((Real.pi + r : ℝ) : Real.Angle) :=
      (edgeVertices_fst_mem B ((Real.pi + r : ℝ) : Real.Angle)).2
    rw [hnr, inner_neg_right, hB1] at h
    linarith
  have h11 : inner ℝ (edgeVertices B ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    have h : inner ℝ (edgeVertices B ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2
        (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue (B : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) :=
      (edgeVertices_snd_mem B ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2
    rw [hn32, inner_neg_right, hB2] at h
    linarith
  have h12 : inner ℝ (edgeVertices D ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    have h : inner ℝ (edgeVertices D ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1
        (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue (D : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) :=
      (edgeVertices_fst_mem D ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2
    rw [hn32, inner_neg_right, hD1] at h
    linarith
  have h14 : inner ℝ (edgeVertices D ((3 * Real.pi / 2 + l : ℝ) : Real.Angle)).2
      (normalVector ((Real.pi / 2 + l : ℝ) : Real.Angle)) =
      supportValue (K.1 : Set Point) ((Real.pi / 2 + l : ℝ) : Real.Angle) - 1 := by
    have h : inner ℝ (edgeVertices D ((3 * Real.pi / 2 + l : ℝ) : Real.Angle)).2
        (normalVector ((3 * Real.pi / 2 + l : ℝ) : Real.Angle)) =
        supportValue (D : Set Point) ((3 * Real.pi / 2 + l : ℝ) : Real.Angle) :=
      (edgeVertices_snd_mem D ((3 * Real.pi / 2 + l : ℝ) : Real.Angle)).2
    rw [hn32l, inner_neg_right, hD2] at h
    linarith
  refine ⟨?_, ?_, segmentArea_eq_zero_of_inner_normalVector_eq_zero h2 h11,
    segmentArea_eq_zero_of_inner_normalVector_eq_zero h12 h6,
    segmentArea_sub_segmentArea_of_inner_normalVector_eq h9 h10 h1, ?_⟩
  · refine eq_of_inner_normalVector_eq (s := r) (t := Real.pi / 2) ?_
      (h3.trans h1.symm) (h4.trans h2.symm)
    rw [show r - Real.pi / 2 = -(Real.pi / 2 - r) by ring, Real.sin_neg,
      Real.sin_pi_div_two_sub]
    exact neg_ne_zero.mpr (ne_of_gt hcosr)
  · refine eq_of_inner_normalVector_eq (s := Real.pi / 2 + l) (t := Real.pi / 2) ?_
      (h7.trans h5.symm) (h8.trans h6.symm)
    rw [show Real.pi / 2 + l - Real.pi / 2 = l by ring]
    exact ne_of_gt hsinl
  · have h := segmentArea_sub_segmentArea_of_inner_normalVector_eq h13 h14 h5
    linarith [segmentArea_swap (wedgeEndpoints K l).2 (capInnerCorner K l),
      segmentArea_swap (wedgeEndpoints K l).2
        (edgeVertices D ((3 * Real.pi / 2 + l : ℝ) : Real.Angle)).2,
      segmentArea_swap (capInnerCorner K l)
        (edgeVertices D ((3 * Real.pi / 2 + l : ℝ) : Real.Angle)).2]

theorem upperBoundQ_decomposition (X : CapTailSpace) :
    upperBoundQ X = upperBoundMiddle X.cap - rightTailMamikon X.rightBody -
      leftTailMamikon X.leftBody := by
  obtain ⟨hr, hl, -⟩ := paperGerverConstants_snd_mem_Ioo
  have hcast : ∀ a b : ℝ, a = b → ((a : ℝ) : Real.Angle) = ((b : ℝ) : Real.Angle) :=
    fun a b h => by rw [h]
  have htop : supportValue (X.cap.1.1 : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle) = 1 :=
    X.cap.1.property.2.2.2.1
  have hB1 : supportValue (X.rightBody : Set Point)
      ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle) =
      1 - supportValue (X.cap.1.1 : Set Point)
        ((paperGerverConstants.2.1 : ℝ) : Real.Angle) := by
    have h := X.right_eq paperGerverConstants.2.1 (by simp)
    linarith
  have hB2 : supportValue (X.rightBody : Set Point)
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    have h := X.right_eq (Real.pi / 2) (by simp)
    rw [hcast _ _ (show Real.pi + Real.pi / 2 = 3 * Real.pi / 2 by ring), htop] at h
    linarith
  have hD1 : supportValue (X.leftBody : Set Point)
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    have h := X.left_eq 0 (by simp)
    rw [hcast _ _ (show Real.pi / 2 + (0 : ℝ) = Real.pi / 2 by ring),
      hcast _ _ (show 3 * Real.pi / 2 + (0 : ℝ) = 3 * Real.pi / 2 by ring), htop] at h
    linarith
  have hD2 : supportValue (X.leftBody : Set Point)
      ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) =
      1 - supportValue (X.cap.1.1 : Set Point)
        ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) := by
    have h := X.left_eq paperGerverConstants.2.2 (by simp)
    linarith
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ :=
    tailFanPoint_identities X.cap.val X.rightBody X.leftBody hr hl hB1 hB2 hD1 hD2
  simp only [upperBoundQ, upperBoundMiddle, rightTailMamikon, leftTailMamikon,
    tangentMamikonValue, rightLeftTailArcs, distinguishedCapSides]
  rw [e1, e2]
  linarith

end MovingSofa

end

end

end
