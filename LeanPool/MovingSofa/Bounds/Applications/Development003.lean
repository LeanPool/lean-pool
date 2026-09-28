/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Area.Applications.Development004
public import LeanPool.MovingSofa.Area.Foundations.Development003
public import LeanPool.MovingSofa.Cap.Applications.Development006
public import LeanPool.MovingSofa.Cap.Foundations.Development007
public import LeanPool.MovingSofa.Gerver.Applications.Development004
/-!
# Moving sofa: related mathematical developments

* `Bounds.Upper.Properties`.
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
# Bounds / Upper / Properties
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem upperBoundQ_quadratic_concave :
    IsQuadraticFunctional capTailCombination upperBoundQ ∧
      IsConvexFunctional capTailCombination upperBoundQ true := by
  obtain ⟨hcomb, -⟩ := capTail_isConvexDomain
  obtain ⟨hmidConv, hmidQuad, hrConv, hrQuad, hlConv, hlQuad⟩ := sofaMamikon_quadratic_convex
  -- ### The three coordinate projections preserve the interpolation
  have hcapval : ∀ t X Y, (capTailCombination t X Y).cap = specialCapCombination t X.cap Y.cap :=
    fun t X Y ↦ Subtype.ext (Subtype.ext
      ((hcomb t X Y).1.trans (specialCap_isConvexDomain.1 t X.cap Y.cap).symm))
  have hcap : IsConvexLinear capTailCombination specialCapCombination
      fun X : CapTailSpace ↦ X.cap := hcapval
  have hright : IsConvexLinear capTailCombination convexBodyCombination
      fun X : CapTailSpace ↦ X.rightBody := fun t X Y ↦ (hcomb t X Y).2.1
  have hleft : IsConvexLinear capTailCombination convexBodyCombination
      fun X : CapTailSpace ↦ X.leftBody := fun t X Y ↦ (hcomb t X Y).2.2
  -- ### The middle equivalence exhibits the affine part of the cap term
  have hAlin : IsConvexLinear capTailCombination realCombination
      fun X : CapTailSpace ↦ middleMamikon X.cap + upperBoundMiddle X.cap := by
    intro t X Y
    have h := middleMamikon_equivalent_neg_upperBoundMiddle t X.cap Y.cap
    simp only [sub_neg_eq_add, realCombination] at h
    show middleMamikon (capTailCombination t X Y).cap +
      upperBoundMiddle (capTailCombination t X Y).cap = realCombination t _ _
    rw [hcapval t X Y]
    simp only [realCombination]
    linarith
  -- ### The exact decomposition, with the cap term split as affine minus convex
  have hQ : upperBoundQ = fun X : CapTailSpace ↦
      ((middleMamikon X.cap + upperBoundMiddle X.cap + -middleMamikon X.cap) +
        -rightTailMamikon X.rightBody) + -leftTailMamikon X.leftBody := by
    funext X
    rw [upperBoundQ_decomposition X]
    ring
  rw [hQ]
  exact ⟨((hAlin.isQuadraticFunctional.add (hmidQuad.comp_isConvexLinear hcap).neg).add
        (hrQuad.comp_isConvexLinear hright).neg).add (hlQuad.comp_isConvexLinear hleft).neg,
    (((hAlin.isConvexFunctional true).add (hmidConv.comp_isConvexLinear hcap).neg).add
        (hrConv.comp_isConvexLinear hright).neg).add (hlConv.comp_isConvexLinear hleft).neg⟩

/-- The right tail's initial vertex, the right fan point and the right inner corner all lie on the
right distinguished inner wall `b_K(φᴿ)`, so the two signed segment areas along it add. -/
private theorem segmentArea_add_segmentArea_rightWall (X : CapTailSpace) :
    segmentArea (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint
        (distinguishedCapSides X.cap.val).1.fanPoint +
      segmentArea (distinguishedCapSides X.cap.val).1.fanPoint
        (distinguishedCapSides X.cap.val).1.corner =
    segmentArea (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint
      (distinguishedCapSides X.cap.val).1.corner := by
  obtain ⟨hrIoo, -, -⟩ := paperGerverConstants_snd_mem_Ioo
  have hcosr : 0 < Real.cos paperGerverConstants.2.1 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hrIoo.1], hrIoo.2⟩
  have hXBdef : (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint =
      (edgeVertices X.rightBody ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).1 := rfl
  have hWdef : (distinguishedCapSides X.cap.val).1.fanPoint =
      (wedgeEndpoints X.cap.val paperGerverConstants.2.1).1 := rfl
  have hxRdef : (distinguishedCapSides X.cap.val).1.corner =
      capInnerCorner X.cap.val paperGerverConstants.2.1 := rfl
  have hXB : inner ℝ
      (edgeVertices X.rightBody ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).1
      (normalVector ((paperGerverConstants.2.1 : ℝ) : Real.Angle)) =
      supportValue (X.cap.val.val : Set Point)
        ((paperGerverConstants.2.1 : ℝ) : Real.Angle) - 1 := by
    have hmem : inner ℝ
        (edgeVertices X.rightBody ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).1
        (normalVector ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)) =
        supportValue (X.rightBody : Set Point)
          ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle) :=
      (edgeVertices_fst_mem X.rightBody _).2
    have hneg : normalVector ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle) =
        -normalVector ((paperGerverConstants.2.1 : ℝ) : Real.Angle) := by
      rw [show (Real.pi + paperGerverConstants.2.1 : ℝ) =
        paperGerverConstants.2.1 + Real.pi from by ring]
      exact normalVector_add_pi _
    rw [hneg, inner_neg_right] at hmem
    have heq := X.right_eq paperGerverConstants.2.1 (by simp)
    linarith
  have hW : inner ℝ (wedgeEndpoints X.cap.val paperGerverConstants.2.1).1
      (normalVector ((paperGerverConstants.2.1 : ℝ) : Real.Angle)) =
      supportValue (X.cap.val.val : Set Point)
        ((paperGerverConstants.2.1 : ℝ) : Real.Angle) - 1 := by
    show inner ℝ (((supportValue (X.cap.val.val : Set Point)
        ((paperGerverConstants.2.1 : ℝ) : Real.Angle) - 1) /
        Real.cos paperGerverConstants.2.1) • normalVector 0)
        (normalVector ((paperGerverConstants.2.1 : ℝ) : Real.Angle)) = _
    have h0 : normalVector (0 : Real.Angle) 0 = 1 := by simp [normalVector, frame]
    have h1 : normalVector (0 : Real.Angle) 1 = 0 := by simp [normalVector, frame]
    rw [real_inner_smul_left, inner_normalVector_real, h0, h1, one_mul, zero_mul, add_zero,
      div_mul_cancel₀ _ hcosr.ne']
  rw [hXBdef, hWdef, hxRdef]
  linarith [segmentArea_sub_segmentArea_of_inner_normalVector_eq hXB hW
    (inner_capInnerCorner_normalVector X.cap.val paperGerverConstants.2.1)]

/-- The left inner corner, the left fan point and the left tail's final vertex all lie on the
left distinguished inner wall `d_K(φᴸ)`, so the two signed segment areas along it add. -/
private theorem segmentArea_add_segmentArea_leftWall (X : CapTailSpace) :
    segmentArea (distinguishedCapSides X.cap.val).2.corner
        (distinguishedCapSides X.cap.val).2.fanPoint +
      segmentArea (distinguishedCapSides X.cap.val).2.fanPoint
        (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint =
    segmentArea (distinguishedCapSides X.cap.val).2.corner
      (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint := by
  obtain ⟨-, hlIoo, -⟩ := paperGerverConstants_snd_mem_Ioo
  have hsinl : 0 < Real.sin paperGerverConstants.2.2 :=
    Real.sin_pos_of_pos_of_lt_pi hlIoo.1 (by linarith [Real.pi_pos, hlIoo.2])
  have hZdef : (distinguishedCapSides X.cap.val).2.fanPoint =
      (wedgeEndpoints X.cap.val paperGerverConstants.2.2).2 := rfl
  have hxLdef : (distinguishedCapSides X.cap.val).2.corner =
      capInnerCorner X.cap.val paperGerverConstants.2.2 := rfl
  have hYDdef : (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint =
      (edgeVertices X.leftBody
        ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2 := rfl
  have hxL : inner ℝ (capInnerCorner X.cap.val paperGerverConstants.2.2)
      (normalVector ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue (X.cap.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    rw [normalVector_add_pi_div_two_real]
    exact inner_capInnerCorner_tangentVector X.cap.val paperGerverConstants.2.2
  have hZ : inner ℝ (wedgeEndpoints X.cap.val paperGerverConstants.2.2).2
      (normalVector ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue (X.cap.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    show inner ℝ (((supportValue (X.cap.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
        Real.cos (Real.pi / 2 - paperGerverConstants.2.2)) •
        tangentVector ((Real.pi / 2 : ℝ) : Real.Angle))
        (normalVector ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle)) = _
    rw [real_inner_smul_left, inner_tangentVector_normalVector_real,
      show paperGerverConstants.2.2 + Real.pi / 2 - Real.pi / 2 = paperGerverConstants.2.2 from
        by ring, Real.cos_pi_div_two_sub, div_mul_cancel₀ _ hsinl.ne']
  have hYD : inner ℝ (edgeVertices X.leftBody
      ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2
      (normalVector ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue (X.cap.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    have hmem : inner ℝ (edgeVertices X.leftBody
        ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2
        (normalVector ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)) =
        supportValue (X.leftBody : Set Point)
          ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) :=
      (edgeVertices_snd_mem X.leftBody _).2
    have hneg : normalVector ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) =
        -normalVector ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) := by
      rw [show (3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) =
        paperGerverConstants.2.2 + Real.pi / 2 + Real.pi from by ring]
      exact normalVector_add_pi _
    rw [hneg, inner_neg_right] at hmem
    have heq := X.left_eq paperGerverConstants.2.2 (by simp)
    rw [show (Real.pi / 2 + paperGerverConstants.2.2 : ℝ) =
      paperGerverConstants.2.2 + Real.pi / 2 from by ring] at heq
    linarith
  rw [hZdef, hxLdef, hYDdef]
  linarith [segmentArea_sub_segmentArea_of_inner_normalVector_eq hxL hZ hYD]

theorem areaFunctional_le_upperBoundQ (X : CapTailSpace)
    (hB : (X.rightBody : Set Point) = (canonicalTailSets X.cap).1)
    (hD : (X.leftBody : Set Point) = (canonicalTailSets X.cap).2) :
    rightAngleAreaFunctional X.cap.val ≤ upperBoundQ X := by
  have hsplit := (niche_three_regions_area X.cap _ _ _ rfl rfl rfl).2.2.2.2.2.2.2.2.2.2
  have hmid := capMiddle_area_lower_bound X.cap
  rw [Set.sdiff_sdiff] at hmid
  obtain ⟨hrightTail, hleftTail⟩ :=
    canonicalTail_niche_area_lower_bounds X.cap X.rightBody X.leftBody hB hD
  have hwallR := segmentArea_add_segmentArea_rightWall X
  have hwallL := segmentArea_add_segmentArea_leftWall X
  have hswapR := segmentArea_swap (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint
    (distinguishedCapSides X.cap.val).1.corner
  have hswapL := segmentArea_swap (distinguishedCapSides X.cap.val).2.corner
    (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint
  simp only [rightAngleAreaFunctional, capAreaFunctional, upperBoundQ]
  linarith

theorem gerver_upperBoundQ_maximum :
    ∃ X : CapTailSpace,
      (X.cap.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2) ∧
      (X.rightBody : Set Point) = (canonicalTailSets X.cap).1 ∧
      (X.leftBody : Set Point) = (canonicalTailSets X.cap).2 ∧
      ∀ Y : CapTailSpace, upperBoundQ Y ≤ upperBoundQ X := by
  -- ### The special-cap space contains Gerver's cap, and the canonical tails extend it to `𝓛`
  obtain ⟨K, hK⟩ := specialCap_isConvexDomain.2.2.2
  obtain ⟨X, hXcap, hB, hD⟩ := exists_canonicalCapTail K
  subst K
  refine ⟨X, hK, hB, hD, ?_⟩
  -- ### `𝒬` is quadratic and concave, so nonpositive variation is exactly maximality
  obtain ⟨hquad, hconcave⟩ := upperBoundQ_quadratic_concave
  exact (quadratic_maximum_iff capTailCombination capTail_isConvexDomain.2 upperBoundQ hquad
    hconcave X).mpr fun Y ↦ gerver_upperBoundQ_variation X Y hK hB hD

end MovingSofa

end

end

end
