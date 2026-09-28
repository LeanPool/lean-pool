/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Analysis.Foundations.Development003
public import LeanPool.MovingSofa.Area.Applications.Development002
public import LeanPool.MovingSofa.Area.Applications.Development003
public import LeanPool.MovingSofa.Bounds.Foundations.Development006
public import LeanPool.MovingSofa.Cap.Applications.Development006

public import LeanPool.MovingSofa.Cap.Applications.Development005


public import LeanPool.MovingSofa.Convex.Foundations.Development002
public import LeanPool.MovingSofa.Convex.Foundations.Development003
/-!
# Moving sofa: related mathematical developments

* `Area.Mamikon.Middle`.
* `Area.Mamikon.TangentValues`.
* `Area.Mamikon.SofaConvex`.
* `Area.QVariation`.
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
# The middle Mamikon functional of a special cap

`middleMamikon` is the evaluated four-term Mamikon decomposition of the part of a special cap's
niche cut out by the two straight tangent paths on `[0, φᴿ]` and `[φᴸ, π / 2]`, the outer-corner arc
on the middle window `[φᴿ, φᴸ]` and the terminal tangent path on `[π / 2, π]`.  This module proves
that it agrees with `-upperBoundMiddle` modulo convex-linear functionals of the cap.

The four summands already express their straight paths as endpoint segment areas, so the whole
functional is a sum of eleven signed segment areas, one curve area and four convex arc areas.  The
four arc areas add up to the cap area modulo a convex-linear functional
(`specialCapArea_equivalent_upper_arcs`), which supplies the `-|K|` of the upper bound.  Of the
eleven segments, five are convex-linear and therefore discarded
(`middleMamikon_segments_isConvexLinear`): all their endpoints move convex-linearly with the cap and
stay on the two fixed horizontal lines `y = 0` and `y = 1`, the latter being the top supporting
line, so no determinant of two moving coordinates ever appears.  Two more pairs collapse at the two
Gerver angles, where the extreme faces are singletons: at `φᴿ` the tangent-line intersection, the
face and the outer corner are collinear, so the two segments merge
(`middleMamikon_segments_merge_right`), and at `φᴸ` the tangent-line intersection *is* the outer
corner, so the two segments cancel (`middleMamikon_segments_cancel_left`).  What remains are exactly
the three comparisons of `cornerArea_equivalent_modulo_linear`, the last of them reversed.
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The signed area between a convex boundary arc and the specified broken straight path. -/
def straightMamikonValue (K : ConvexBody Point) (a b : ℝ) (p q : Point) : ℝ :=
  segmentArea (edgeVertices K (a : Real.Angle)).1 p + segmentArea p q +
    segmentArea q (edgeVertices K (b : Real.Angle)).2 - convexArcArea K a b

/-- The middle Mamikon functional constructed from the special cap’s hallway-corner geometry. -/
def middleMamikon (K : SpecialCapSpace) : ℝ :=
  let B := K.val.val
  let r := paperGerverConstants.2.1
  let l := paperGerverConstants.2.2
  let T := Real.pi / 2
  let y := fun t : ℝ ↦ (rotatingHallwayParts (B : Set Point) (t : Real.Angle)).outerCorner
  straightMamikonValue B 0 r
      (supportingIntersection B 0 (T : Real.Angle))
      (supportingIntersection B (r : Real.Angle) (T : Real.Angle)) +
    (segmentArea (edgeVertices B (r : Real.Angle)).1 (y r) +
      curveAreaFunctional (capOuterMiddleBV K) +
      segmentArea (y l) (edgeVertices B (l : Real.Angle)).2 - convexArcArea B r l) +
    straightMamikonValue B l T
      (supportingIntersection B (l : Real.Angle) ((T + l : ℝ) : Real.Angle))
      (supportingIntersection B (T : Real.Angle) ((T + l : ℝ) : Real.Angle)) +
    tangentMamikonValue B T Real.pi

/-! ### The singleton faces of a special cap and their positions -/

/-- The extreme faces of a special cap at the upper normals other than the vertical one are
singletons, because its injectivity condition supplies angular densities. -/
private theorem specialCap_edgeVertices_eq (K : SpecialCapSpace) {t : ℝ}
    (ht : t ∈ Set.Icc 0 Real.pi) (htop : t ≠ Real.pi / 2) :
    (edgeVertices K.val.val (t : Real.Angle)).1 =
      (edgeVertices K.val.val (t : Real.Angle)).2 := by
  obtain ⟨r, s, hdens, -⟩ := K.property.1.1
  exact capDensities_edgeVertices_eq K.val ⟨r, s, hdens⟩ ht htop

/-- Both horizontal extreme faces of a special cap lie on the base line: they are singletons, and a
singleton horizontal face of a right-angle cap cannot have positive height. -/
private theorem specialCap_horizontal_edgeVertices_apply_one (K : SpecialCapSpace) :
    (edgeVertices K.val.val ((0 : ℝ) : Real.Angle)).1 1 = 0 ∧
      (edgeVertices K.val.val ((Real.pi : ℝ) : Real.Angle)).2 1 = 0 := by
  have hpi := Real.pi_pos
  have h0 := specialCap_edgeVertices_eq K (t := 0) ⟨le_rfl, hpi.le⟩
    (by positivity : (0 : ℝ) < Real.pi / 2).ne
  have hp := specialCap_edgeVertices_eq K (t := Real.pi) ⟨hpi.le, le_rfl⟩
    (by linarith : Real.pi / 2 < Real.pi).ne'
  refine ⟨K.val.edgeVertices_fst_apply_one_eq_zero Real.sin_zero h0, ?_⟩
  rw [← hp]
  exact K.val.edgeVertices_fst_apply_one_eq_zero Real.sin_pi hp

/-- At the left Gerver angle the two supporting lines of the middle Mamikon loop are at angular
difference `π / 2`, so they meet at the outer corner of the supporting hallway. -/
private theorem specialCap_supportingIntersection_left_eq_outerCorner (K : SpecialCapSpace) :
    supportingIntersection K.val.val (paperGerverConstants.2.2 : Real.Angle)
        ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) =
      (rotatingHallwayParts (K.val.val : Set Point)
        (paperGerverConstants.2.2 : Real.Angle)).outerCorner := by
  rw [show (Real.pi / 2 + paperGerverConstants.2.2 : ℝ) =
    paperGerverConstants.2.2 + Real.pi / 2 from by ring]
  exact supportingIntersection_add_pi_div_two_eq_outerCorner _ _

/-! ### The convex-linear segments -/

/-- The signed area of the segment between two convex-linear point functionals of a special cap
that both keep a constant height is convex-linear. -/
private theorem segmentArea_isConvexLinear_of_apply_one_eq (P Q : SpecialCapSpace → Point)
    {a b : ℝ}
    (hP : ∀ (t : unitInterval) (K L : SpecialCapSpace),
      P (specialCapCombination t K L) = (1 - (t : ℝ)) • P K + (t : ℝ) • P L)
    (hQ : ∀ (t : unitInterval) (K L : SpecialCapSpace),
      Q (specialCapCombination t K L) = (1 - (t : ℝ)) • Q K + (t : ℝ) • Q L)
    (hPa : ∀ K, P K 1 = a) (hQb : ∀ K, Q K 1 = b) :
    IsConvexLinear specialCapCombination realCombination fun K ↦ segmentArea (P K) (Q K) :=
  fun t K L ↦ by
    show segmentArea (P (specialCapCombination t K L)) (Q (specialCapCombination t K L)) =
      realCombination t (segmentArea (P K) (Q K)) (segmentArea (P L) (Q L))
    rw [hP, hQ, realCombination]
    exact segmentArea_combination_of_apply_one_eq _ ((hPa K).trans (hPa L).symm)
      ((hQb K).trans (hQb L).symm)

/-- The five straight segments that the reductions leave in place have convex-linear total signed
area.  In the order of the four-term definition they are the bottom segment at the horizontal normal
`0`, the chord of the top supporting line from `l_K^T(0)` to `l_K^T(φᴿ)`, the chord from
`l_K^{T + φᴸ}(T)` to the negative top vertex `v_K^-(T)`, the chord from the positive top vertex
`v_K^+(T)` to `l_K^π(T)`, and the bottom segment at the normal `π`.  All ten endpoints are
convex-linear in the cap, and each lies on one of the two fixed horizontal lines `y = 0` — the two
singleton horizontal contacts — and `y = 1` — the top supporting line. -/
private theorem middleMamikon_segments_isConvexLinear :
    IsConvexLinear specialCapCombination realCombination fun K ↦
      segmentArea (edgeVertices K.val.val ((0 : ℝ) : Real.Angle)).1
          (supportingIntersection K.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle)) +
        segmentArea (supportingIntersection K.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle))
          (supportingIntersection K.val.val (paperGerverConstants.2.1 : Real.Angle)
            ((Real.pi / 2 : ℝ) : Real.Angle)) +
        segmentArea (supportingIntersection K.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
            ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle))
          (edgeVertices K.val.val ((Real.pi / 2 : ℝ) : Real.Angle)).2 +
        segmentArea (edgeVertices K.val.val ((Real.pi / 2 : ℝ) : Real.Angle)).1
          (supportingIntersection K.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
            ((Real.pi : ℝ) : Real.Angle)) +
        segmentArea (supportingIntersection K.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
            ((Real.pi : ℝ) : Real.Angle))
          (edgeVertices K.val.val ((Real.pi : ℝ) : Real.Angle)).2 := by
  have hpi := Real.pi_pos
  obtain ⟨hr, hl, -⟩ := paperGerverConstants_snd_mem_Ioo
  -- ### The endpoints move convex-linearly
  have hev := fun (a : Real.Angle) (t : unitInterval) (M N : SpecialCapSpace) ↦
    (specialCap_maps_linear t M N).1 a
  have hsi := fun (a b : ℝ) (hab : a < b) (hba : b < a + Real.pi) (t : unitInterval)
    (M N : SpecialCapSpace) ↦ (specialCap_maps_linear t M N).2 a b hab hba
  have hsi0 : ∀ (t : unitInterval) (M N : SpecialCapSpace),
      supportingIntersection (specialCapCombination t M N).val.val 0
          ((Real.pi / 2 : ℝ) : Real.Angle) =
        (1 - (t : ℝ)) • supportingIntersection M.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle) +
          (t : ℝ) • supportingIntersection N.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle) :=
    fun t M N ↦ by
      simpa only [Real.Angle.coe_zero] using
        hsi 0 (Real.pi / 2) (by positivity) (by linarith) t M N
  -- ### The endpoints keep their heights
  have htop : ∀ (M : SpecialCapSpace) (p : Point),
      inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue (M.val.val : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle) → p 1 = 1 :=
    fun M _ hp ↦ M.val.apply_one_eq_one hp
  have hsiL : ∀ (M : SpecialCapSpace) (s : ℝ),
      supportingIntersection M.val.val ((Real.pi / 2 : ℝ) : Real.Angle) (s : Real.Angle) 1 = 1 :=
    fun M s ↦ htop M _ (supportingIntersection_inner_left _ _ s)
  have hsiR : ∀ (M : SpecialCapSpace) (s : ℝ), Real.sin (Real.pi / 2 - s) ≠ 0 →
      supportingIntersection M.val.val (s : Real.Angle) ((Real.pi / 2 : ℝ) : Real.Angle) 1 = 1 :=
    fun M s hs ↦ htop M _ (supportingIntersection_inner_right _ s _ hs)
  have hsi0h : ∀ M : SpecialCapSpace,
      supportingIntersection M.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle) 1 = 1 := fun M ↦ by
    simpa only [Real.Angle.coe_zero] using
      hsiR M 0 (by rw [sub_zero, Real.sin_pi_div_two]; norm_num)
  have hvtop : ∀ M : SpecialCapSpace,
      (edgeVertices M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)).1 1 = 1 ∧
        (edgeVertices M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)).2 1 = 1 :=
    fun M ↦ ⟨htop M _ (edgeVertices_fst_mem _ _).2, htop M _ (edgeVertices_snd_mem _ _).2⟩
  have hsinr : Real.sin (Real.pi / 2 - paperGerverConstants.2.1) ≠ 0 := by
    rw [Real.sin_pi_div_two_sub]
    exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [hr.1], hr.2⟩).ne'
  -- ### The five segments
  have h1 := segmentArea_isConvexLinear_of_apply_one_eq
    (fun M ↦ (edgeVertices M.val.val ((0 : ℝ) : Real.Angle)).1)
    (fun M ↦ supportingIntersection M.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle))
    (fun t M N ↦ (hev _ t M N).1) hsi0
    (fun M ↦ (specialCap_horizontal_edgeVertices_apply_one M).1) hsi0h
  have h2 := segmentArea_isConvexLinear_of_apply_one_eq
    (fun M ↦ supportingIntersection M.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle))
    (fun M ↦ supportingIntersection M.val.val (paperGerverConstants.2.1 : Real.Angle)
      ((Real.pi / 2 : ℝ) : Real.Angle))
    hsi0 (hsi paperGerverConstants.2.1 (Real.pi / 2) hr.2 (by linarith [hr.1]))
    hsi0h (fun M ↦ hsiR M paperGerverConstants.2.1 hsinr)
  have h3 := segmentArea_isConvexLinear_of_apply_one_eq
    (fun M ↦ supportingIntersection M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
      ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle))
    (fun M ↦ (edgeVertices M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)).2)
    (hsi (Real.pi / 2) (Real.pi / 2 + paperGerverConstants.2.2) (by linarith [hl.1])
      (by linarith [hl.2]))
    (fun t M N ↦ (hev _ t M N).2)
    (fun M ↦ hsiL M (Real.pi / 2 + paperGerverConstants.2.2)) (fun M ↦ (hvtop M).2)
  have h4 := segmentArea_isConvexLinear_of_apply_one_eq
    (fun M ↦ (edgeVertices M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)).1)
    (fun M ↦ supportingIntersection M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
      ((Real.pi : ℝ) : Real.Angle))
    (fun t M N ↦ (hev _ t M N).1) (hsi (Real.pi / 2) Real.pi (by linarith) (by linarith))
    (fun M ↦ (hvtop M).1) (fun M ↦ hsiL M Real.pi)
  have h5 := segmentArea_isConvexLinear_of_apply_one_eq
    (fun M ↦ supportingIntersection M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
      ((Real.pi : ℝ) : Real.Angle))
    (fun M ↦ (edgeVertices M.val.val ((Real.pi : ℝ) : Real.Angle)).2)
    (hsi (Real.pi / 2) Real.pi (by linarith) (by linarith)) (fun t M N ↦ (hev _ t M N).2)
    (fun M ↦ hsiL M Real.pi)
    (fun M ↦ (specialCap_horizontal_edgeVertices_apply_one M).2)
  intro t M N
  have e1 := h1 t M N
  have e2 := h2 t M N
  have e3 := h3 t M N
  have e4 := h4 t M N
  have e5 := h5 t M N
  simp only [realCombination] at e1 e2 e3 e4 e5 ⊢
  linear_combination e1 + e2 + e3 + e4 + e5

/-! ### The two collapsing pairs at the Gerver angles -/

/-- At the right Gerver angle the tangent-line intersection, the singleton extreme face and the
outer corner all lie on the same supporting line, so the two segments through the face merge into a
single chord. -/
private theorem middleMamikon_segments_merge_right (K : SpecialCapSpace) :
    segmentArea (supportingIntersection K.val.val (paperGerverConstants.2.1 : Real.Angle)
          ((Real.pi / 2 : ℝ) : Real.Angle))
        (edgeVertices K.val.val (paperGerverConstants.2.1 : Real.Angle)).2 +
      segmentArea (edgeVertices K.val.val (paperGerverConstants.2.1 : Real.Angle)).1
        (rotatingHallwayParts (K.val.val : Set Point)
          (paperGerverConstants.2.1 : Real.Angle)).outerCorner =
    segmentArea (supportingIntersection K.val.val (paperGerverConstants.2.1 : Real.Angle)
        ((Real.pi / 2 : ℝ) : Real.Angle))
      (rotatingHallwayParts (K.val.val : Set Point)
        (paperGerverConstants.2.1 : Real.Angle)).outerCorner := by
  have hpi := Real.pi_pos
  obtain ⟨hr, -, -⟩ := paperGerverConstants_snd_mem_Ioo
  have h1 := supportingIntersection_inner_left K.val.val paperGerverConstants.2.1 (Real.pi / 2)
  have h2 : inner ℝ (edgeVertices K.val.val (paperGerverConstants.2.1 : Real.Angle)).2
      (normalVector (paperGerverConstants.2.1 : Real.Angle)) =
      supportValue (K.val.val : Set Point) (paperGerverConstants.2.1 : Real.Angle) :=
    (edgeVertices_snd_mem _ _).2
  have h3 : inner ℝ (rotatingHallwayParts (K.val.val : Set Point)
      (paperGerverConstants.2.1 : Real.Angle)).outerCorner
      (normalVector (paperGerverConstants.2.1 : Real.Angle)) =
      supportValue (K.val.val : Set Point) (paperGerverConstants.2.1 : Real.Angle) := by
    rw [outerCorner_eq_support_sum, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_normalVector_self, inner_tangentVector_normalVector_real, sub_self, Real.sin_zero]
    ring
  have h := segmentArea_sub_segmentArea_of_inner_normalVector_eq h1 h3 h2
  rw [specialCap_edgeVertices_eq K ⟨hr.1.le, by linarith [hr.2]⟩ hr.2.ne]
  linarith [segmentArea_swap (edgeVertices K.val.val
    (paperGerverConstants.2.1 : Real.Angle)).2
    (rotatingHallwayParts (K.val.val : Set Point)
      (paperGerverConstants.2.1 : Real.Angle)).outerCorner]

/-- At the left Gerver angle the extreme face is a single point and the tangent-line intersection is
the outer corner, so the two segments through the face cancel by antisymmetry. -/
private theorem middleMamikon_segments_cancel_left (K : SpecialCapSpace) :
    segmentArea (rotatingHallwayParts (K.val.val : Set Point)
          (paperGerverConstants.2.2 : Real.Angle)).outerCorner
        (edgeVertices K.val.val (paperGerverConstants.2.2 : Real.Angle)).2 +
      segmentArea (edgeVertices K.val.val (paperGerverConstants.2.2 : Real.Angle)).1
        (supportingIntersection K.val.val (paperGerverConstants.2.2 : Real.Angle)
          ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)) = 0 := by
  have hpi := Real.pi_pos
  obtain ⟨-, hl, -⟩ := paperGerverConstants_snd_mem_Ioo
  rw [specialCap_supportingIntersection_left_eq_outerCorner,
    specialCap_edgeVertices_eq K ⟨hl.1.le, by linarith [hl.2]⟩ hl.2.ne]
  linarith [segmentArea_swap (rotatingHallwayParts (K.val.val : Set Point)
    (paperGerverConstants.2.2 : Real.Angle)).outerCorner
    (edgeVertices K.val.val (paperGerverConstants.2.2 : Real.Angle)).2]

/-! ### The equivalence -/

theorem middleMamikon_equivalent_neg_upperBoundMiddle :
    EquivalentModuloConvexLinear specialCapCombination middleMamikon
      (fun K ↦ -upperBoundMiddle K) := by
  obtain ⟨F, hFval, hmid, hright, hleft⟩ := cornerArea_equivalent_modulo_linear
  have hF : ∀ M : SpecialCapSpace, F M = capOuterMiddleBV M := fun M ↦
    Subtype.ext ((hFval M).trans (funext (capOuterMiddleBV_val M)).symm)
  -- The chord closing the third straight path reverses the left comparison chord.
  have hrev : ∀ M : SpecialCapSpace,
      segmentArea (supportingIntersection M.val.val (paperGerverConstants.2.2 : Real.Angle)
            ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle))
          (supportingIntersection M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
            ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)) =
        -segmentArea (supportingIntersection M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
            ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle))
          (rotatingHallwayParts (M.val.val : Set Point)
            (paperGerverConstants.2.2 : Real.Angle)).outerCorner := fun M ↦ by
    rw [specialCap_supportingIntersection_left_eq_outerCorner]
    exact segmentArea_swap _ _
  -- The right wedge segment of the upper bound runs in the opposite orientation.
  have hswap : ∀ M : SpecialCapSpace,
      segmentArea (distinguishedCapSides M.val).1.corner
          (distinguishedCapSides M.val).1.fanPoint =
        -segmentArea (distinguishedCapSides M.val).1.fanPoint
          (distinguishedCapSides M.val).1.corner := fun M ↦ segmentArea_swap _ _
  intro t K L
  have e1 := specialCapArea_equivalent_upper_arcs t K L
  have e2 := hmid t K L
  have e3 := hright t K L
  have e4 := hleft t K L
  have f := middleMamikon_segments_isConvexLinear t K L
  simp only [hF, realCombination] at e1 e2 e3 e4 f
  simp only [middleMamikon, straightMamikonValue, tangentMamikonValue, upperBoundMiddle,
    realCombination, hrev, hswap]
  linear_combination f + e1 + e2 + e3 - e4 +
    middleMamikon_segments_merge_right (specialCapCombination t K L) +
    middleMamikon_segments_cancel_left (specialCapCombination t K L) -
    (1 - (t : ℝ)) * (middleMamikon_segments_merge_right K +
      middleMamikon_segments_cancel_left K) -
    (t : ℝ) * (middleMamikon_segments_merge_right L +
      middleMamikon_segments_cancel_left L)

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
# Mamikon values of tangent-line chords

For a fixed tangent normal `q`, the tangent-line parametrization of a convex body is a
continuous bounded-variation path, convex-linear in the body, each of whose values lies on the
supporting line at its own path parameter.  Mamikon convexity therefore makes the enclosed area
`straightMamikonValue` a convex quadratic functional of the body, and the terminal case `q = b`
does the same for `tangentMamikonValue`.
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The Mamikon value of a straight tangent-line chord is a convex quadratic functional of the
body. -/
theorem straightMamikon_quadratic_convex (t a b : ℝ)
    (ha : a ∈ Set.Ioc (t - Real.pi) t) (hb : b ∈ Set.Ioc (t - Real.pi) t)
    (hab : a < b) (hba : b < a + Real.pi) :
    IsQuadraticFunctional convexBodyCombination
        (fun K ↦ straightMamikonValue K a b (tangentLinePath K t ⟨a, ha⟩)
          (tangentLinePath K t ⟨b, hb⟩)) ∧
      IsConvexFunctional convexBodyCombination
        (fun K ↦ straightMamikonValue K a b (tangentLinePath K t ⟨a, ha⟩)
          (tangentLinePath K t ⟨b, hb⟩)) false := by
  obtain ⟨F, hFval, hFlin⟩ := tangentLinePath_convexLinear t a b ha hb hab.le
  have hF : ∀ (K : ConvexBody Point) (s : Set.Icc a b),
      (F K).val s ∈ (supportingLineHalfPlane (K : Set Point) ((s : ℝ) : Real.Angle)).1 := by
    intro K s
    rw [hFval K]
    exact tangentLinePath_mem_supportingLine K t
      ⟨(s : ℝ), lt_of_lt_of_le ha.1 s.property.1, le_trans s.property.2 hb.2⟩
  have hval : ∀ K : ConvexBody Point,
      mamikonFunctional K a b hab hba (F K) (hF K) =
        straightMamikonValue K a b (tangentLinePath K t ⟨a, ha⟩)
          (tangentLinePath K t ⟨b, hb⟩) := by
    intro K
    have hchoose : F K = (tangentLinePath_segment_area K t a b ha hb hab.le).choose :=
      Subtype.ext ((hFval K).trans
        (tangentLinePath_segment_area K t a b ha hb hab.le).choose_spec.1.symm)
    have hstart : (F K).val ⟨a, le_rfl, hab.le⟩ = tangentLinePath K t ⟨a, ha⟩ := by
      rw [hFval K]; rfl
    have hend : (F K).val ⟨b, hab.le, le_rfl⟩ = tangentLinePath K t ⟨b, hb⟩ := by
      rw [hFval K]; rfl
    have harea : curveAreaFunctional (F K) =
        segmentArea (tangentLinePath K t ⟨a, ha⟩) (tangentLinePath K t ⟨b, hb⟩) := by
      rw [hchoose]
      exact (tangentLinePath_segment_area K t a b ha hb hab.le).choose_spec.2.2.2
    unfold mamikonFunctional straightMamikonValue
    rw [hstart, hend, harea]
  have hmain := mamikon_quadratic_convex a b hab hba F hF hFlin
  rw [funext hval] at hmain
  exact hmain

/-- The Mamikon value of a terminal tangent normal is a convex quadratic functional of the body. -/
theorem tangentMamikon_quadratic_convex (a b : ℝ) (hab : a < b) (hba : b < a + Real.pi) :
    IsQuadraticFunctional convexBodyCombination (fun K ↦ tangentMamikonValue K a b) ∧
      IsConvexFunctional convexBodyCombination (fun K ↦ tangentMamikonValue K a b) false := by
  have ha : a ∈ Set.Ioc (b - Real.pi) b := ⟨by linarith, hab.le⟩
  have hb : b ∈ Set.Ioc (b - Real.pi) b := ⟨by linarith [Real.pi_pos], le_rfl⟩
  have hmain := straightMamikon_quadratic_convex b a b ha hb hab hba
  have hval : ∀ K : ConvexBody Point,
      straightMamikonValue K a b (tangentLinePath K b ⟨a, ha⟩) (tangentLinePath K b ⟨b, hb⟩) =
        tangentMamikonValue K a b := by
    intro K
    have hstart : tangentLinePath K b ⟨a, ha⟩ =
        supportingIntersection K (a : Real.Angle) (b : Real.Angle) := by
      unfold tangentLinePath
      rw [ite_eq_left hab]
    have hend : tangentLinePath K b ⟨b, hb⟩ = (edgeVertices K (b : Real.Angle)).2 := by
      unfold tangentLinePath
      rw [ite_eq_right (lt_irrefl b)]
    have hdeg : segmentArea (edgeVertices K (b : Real.Angle)).2
        (edgeVertices K (b : Real.Angle)).2 = 0 := by
      have h := segmentArea_swap (edgeVertices K (b : Real.Angle)).2
        (edgeVertices K (b : Real.Angle)).2
      linarith
    unfold straightMamikonValue tangentMamikonValue
    rw [hstart, hend, hdeg]
    ring
  rw [funext hval] at hmain
  exact hmain

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
# Area / Mamikon / Sofa Convex
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem sofaMamikon_quadratic_convex :
    IsConvexFunctional specialCapCombination middleMamikon false ∧
    IsQuadraticFunctional specialCapCombination middleMamikon ∧
    IsConvexFunctional convexBodyCombination rightTailMamikon false ∧
    IsQuadraticFunctional convexBodyCombination rightTailMamikon ∧
    IsConvexFunctional convexBodyCombination leftTailMamikon false ∧
    IsQuadraticFunctional convexBodyCombination leftTailMamikon := by
  obtain ⟨hrIoo, hlIoo, hsum⟩ := paperGerverConstants_snd_mem_Ioo
  have hpi := Real.pi_pos
  have hrl := paperGerverConstants_snd_fst_lt_snd_snd
  have hr0 := hrIoo.1
  have hr2 := hrIoo.2
  have hl0 := hlIoo.1
  have hl2 := hlIoo.2
  -- ### The two tail functionals are terminal tangent Mamikon values
  have htailR := tangentMamikon_quadratic_convex (Real.pi + paperGerverConstants.2.1)
    (3 * Real.pi / 2) (by linarith) (by linarith)
  have htailL := tangentMamikon_quadratic_convex (3 * Real.pi / 2)
    (3 * Real.pi / 2 + paperGerverConstants.2.2) (by linarith) (by linarith)
  -- ### The first middle summand
  have ha1 : (0 : ℝ) ∈ Set.Ioc (Real.pi / 2 - Real.pi) (Real.pi / 2) :=
    ⟨by linarith, by linarith⟩
  have hb1 : paperGerverConstants.2.1 ∈ Set.Ioc (Real.pi / 2 - Real.pi) (Real.pi / 2) :=
    ⟨by linarith, by linarith⟩
  have hmid1 := straightMamikon_quadratic_convex (Real.pi / 2) 0 paperGerverConstants.2.1
    ha1 hb1 (by linarith) (by linarith)
  -- ### The third middle summand
  have ha3 : paperGerverConstants.2.2 ∈
      Set.Ioc (Real.pi / 2 + paperGerverConstants.2.2 - Real.pi)
        (Real.pi / 2 + paperGerverConstants.2.2) := ⟨by linarith, by linarith⟩
  have hb3 : (Real.pi / 2 : ℝ) ∈
      Set.Ioc (Real.pi / 2 + paperGerverConstants.2.2 - Real.pi)
        (Real.pi / 2 + paperGerverConstants.2.2) := ⟨by linarith, by linarith⟩
  have hmid3 := straightMamikon_quadratic_convex (Real.pi / 2 + paperGerverConstants.2.2)
    paperGerverConstants.2.2 (Real.pi / 2) ha3 hb3 (by linarith) (by linarith)
  -- ### The fourth middle summand
  have hmid4 := tangentMamikon_quadratic_convex (Real.pi / 2) Real.pi (by linarith) (by linarith)
  -- ### The second middle summand, the Mamikon value of the outer-corner path
  obtain ⟨γ, hγ, hγlin⟩ := exists_outerCornerBV_convexLinear paperGerverConstants.2.1
    paperGerverConstants.2.2
  have hγmem : ∀ (B : ConvexBody Point)
      (s : Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2),
      (γ B).val s ∈ (supportingLineHalfPlane (B : Set Point) ((s : ℝ) : Real.Angle)).1 := by
    intro B s
    rw [hγ B s]
    show inner ℝ (rotatingHallwayParts (B : Set Point) ((s : ℝ) : Real.Angle)).outerCorner
      (normalVector ((s : ℝ) : Real.Angle)) = supportValue (B : Set Point) ((s : ℝ) : Real.Angle)
    rw [outerCorner_eq_support_sum B (s : ℝ), inner_add_left, real_inner_smul_left,
      real_inner_smul_left, inner_normalVector_self, real_inner_comm,
      inner_normalVector_tangentVector]
    ring
  have hmid2 := mamikon_quadratic_convex paperGerverConstants.2.1 paperGerverConstants.2.2
    hrl (by linarith) γ hγmem hγlin
  -- ### The four middle summands assemble to the middle functional on all bodies
  have hquadAll := ((hmid1.1.add hmid2.1).add hmid3.1).add hmid4.1
  have hconvAll := ((hmid1.2.add hmid2.2).add hmid3.2).add hmid4.2
  have hbody : IsConvexLinear specialCapCombination convexBodyCombination
      fun K : SpecialCapSpace ↦ K.val.val := specialCap_isConvexDomain.1
  have hquad := hquadAll.comp_isConvexLinear hbody
  have hconv := hconvAll.comp_isConvexLinear hbody
  have hmideq : (fun K : SpecialCapSpace ↦
      ((straightMamikonValue K.val.val 0 paperGerverConstants.2.1
          (tangentLinePath K.val.val (Real.pi / 2) ⟨0, ha1⟩)
          (tangentLinePath K.val.val (Real.pi / 2) ⟨paperGerverConstants.2.1, hb1⟩) +
        mamikonFunctional K.val.val paperGerverConstants.2.1 paperGerverConstants.2.2 hrl
          (by linarith) (γ K.val.val) (hγmem K.val.val)) +
        straightMamikonValue K.val.val paperGerverConstants.2.2 (Real.pi / 2)
          (tangentLinePath K.val.val (Real.pi / 2 + paperGerverConstants.2.2)
            ⟨paperGerverConstants.2.2, ha3⟩)
          (tangentLinePath K.val.val (Real.pi / 2 + paperGerverConstants.2.2)
            ⟨Real.pi / 2, hb3⟩)) +
        tangentMamikonValue K.val.val (Real.pi / 2) Real.pi) = middleMamikon := by
    funext K
    have hpath1 : tangentLinePath K.val.val (Real.pi / 2) ⟨0, ha1⟩ =
        supportingIntersection K.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle) := by
      unfold tangentLinePath
      rw [ite_eq_left (show (0 : ℝ) < Real.pi / 2 by linarith), Real.Angle.coe_zero]
    have hpath2 : tangentLinePath K.val.val (Real.pi / 2)
        ⟨paperGerverConstants.2.1, hb1⟩ =
        supportingIntersection K.val.val ((paperGerverConstants.2.1 : ℝ) : Real.Angle)
          ((Real.pi / 2 : ℝ) : Real.Angle) := by
      unfold tangentLinePath
      rw [ite_eq_left hr2]
    have hpath3 : tangentLinePath K.val.val (Real.pi / 2 + paperGerverConstants.2.2)
        ⟨paperGerverConstants.2.2, ha3⟩ =
        supportingIntersection K.val.val ((paperGerverConstants.2.2 : ℝ) : Real.Angle)
          ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) := by
      unfold tangentLinePath
      rw [ite_eq_left (by linarith)]
    have hpath4 : tangentLinePath K.val.val (Real.pi / 2 + paperGerverConstants.2.2)
        ⟨Real.pi / 2, hb3⟩ =
        supportingIntersection K.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
          ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) := by
      unfold tangentLinePath
      rw [ite_eq_left (by linarith)]
    have hγeq : γ K.val.val = capOuterMiddleBV K :=
      Subtype.ext (funext fun s ↦ (hγ K.val.val s).trans (capOuterMiddleBV_val K s).symm)
    have hmam : mamikonFunctional K.val.val paperGerverConstants.2.1
        paperGerverConstants.2.2 hrl (by linarith) (γ K.val.val) (hγmem K.val.val) =
        segmentArea (edgeVertices K.val.val ((paperGerverConstants.2.1 : ℝ) : Real.Angle)).1
            ((rotatingHallwayParts (K.val.val : Set Point)
              ((paperGerverConstants.2.1 : ℝ) : Real.Angle)).outerCorner) +
          curveAreaFunctional (capOuterMiddleBV K) +
          segmentArea ((rotatingHallwayParts (K.val.val : Set Point)
              ((paperGerverConstants.2.2 : ℝ) : Real.Angle)).outerCorner)
            (edgeVertices K.val.val ((paperGerverConstants.2.2 : ℝ) : Real.Angle)).2 -
          convexArcArea K.val.val paperGerverConstants.2.1 paperGerverConstants.2.2 := by
      unfold mamikonFunctional
      rw [hγ K.val.val ⟨paperGerverConstants.2.1, le_rfl, hrl.le⟩,
        hγ K.val.val ⟨paperGerverConstants.2.2, hrl.le, le_rfl⟩, hγeq]
    show _ = middleMamikon K
    unfold middleMamikon
    rw [hpath1, hpath2, hpath3, hpath4, hmam]
  rw [hmideq] at hquad hconv
  exact ⟨hconv, hquad, htailR.2, htailR.1, htailL.2, htailL.1⟩

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
# The directional derivative of the upper bound `𝒬`

`upperBoundQ` is a signed sum of six area functionals of a cap-tail triple: the cap area, the two
tail arc areas, the inner-corner curve area and the two areas of the segments joining a tail
endpoint to the corresponding cap corner.  Each summand is quadratic along the barycentric
interpolation of cap-tail triples, so each segment function is differentiable at the base point
with the summand's `convexDirectionalDerivative` as its derivative; adding those six derivatives
computes the derivative of the segment function of `𝒬` itself.

Five of the twelve endpoint contributions cancel in pairs.  The remaining two are the segment
areas at the far ends of the two tails, and they vanish because the cap-tail constraints force the
support value of both tails in the direction `3π/2` to be zero, so all four points involved lie on
the horizontal axis.  What survives is `qVariationIntegral`: the cap surface integral, the
inner-corner integral, and the two tail integrals rewritten in opposite-angle coordinates.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- The support-function variation integral for the cap and its two tail bodies. -/
def qVariationIntegral (X Y : CapTailSpace) : ℝ :=
  (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi,
    (supportValue Y.cap.val.val t - supportValue X.cap.val.val t)
      ∂surfaceAreaMeasure X.cap.val.val) -
  (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
        Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
          (Real.pi / 2 + paperGerverConstants.2.2)),
    (supportValue Y.cap.val.val t - supportValue X.cap.val.val t)
      ∂capCornerAngleMeasure X.cap) +
  (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
      Set.Ioo paperGerverConstants.2.1 (Real.pi / 2),
    ((oppositeSurfaceData Y.rightBody).2 t - (oppositeSurfaceData X.rightBody).2 t)
      ∂(oppositeSurfaceData X.rightBody).1) +
  (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
      Set.Ioo (Real.pi / 2) (Real.pi / 2 + paperGerverConstants.2.2),
    ((oppositeSurfaceData Y.leftBody).2 t - (oppositeSurfaceData X.leftBody).2 t)
      ∂(oppositeSurfaceData X.leftBody).1)

private theorem capTail_leftPair_isConvexLinear :
    IsConvexLinear capTailCombination pointPairCombination
      (fun Z : CapTailSpace ↦ ((rightLeftTailArcs Z.rightBody Z.leftBody).2.endPoint,
        (distinguishedCapSides Z.cap.val).2.corner)) := by
  obtain ⟨hcomb, -⟩ := capTail_isConvexDomain
  intro t Z W
  have hvertex : (rightLeftTailArcs (capTailCombination t Z W).rightBody
      (capTailCombination t Z W).leftBody).2.endPoint =
      (1 - (t : ℝ)) • (rightLeftTailArcs Z.rightBody Z.leftBody).2.endPoint +
        (t : ℝ) • (rightLeftTailArcs W.rightBody W.leftBody).2.endPoint := by
    show (edgeVertices (capTailCombination t Z W).leftBody
      ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2 = _
    rw [(hcomb t Z W).2.2]
    exact ((convexBody_maps_linear t Z.leftBody W.leftBody).2.1 _).2
  have hcorner : (distinguishedCapSides (capTailCombination t Z W).cap.val).2.corner =
      (1 - (t : ℝ)) • (distinguishedCapSides Z.cap.val).2.corner +
        (t : ℝ) • (distinguishedCapSides W.cap.val).2.corner :=
    capInnerCorner_of_eq_convexBodyCombination (hcomb t Z W).1 paperGerverConstants.2.2
  show ((rightLeftTailArcs (capTailCombination t Z W).rightBody
    (capTailCombination t Z W).leftBody).2.endPoint,
    (distinguishedCapSides (capTailCombination t Z W).cap.val).2.corner) = _
  rw [hvertex, hcorner]
  rfl

private theorem capTail_rightPair_isConvexLinear :
    IsConvexLinear capTailCombination pointPairCombination
      (fun Z : CapTailSpace ↦ ((distinguishedCapSides Z.cap.val).1.corner,
        (rightLeftTailArcs Z.rightBody Z.leftBody).1.startPoint)) := by
  obtain ⟨hcomb, -⟩ := capTail_isConvexDomain
  intro t Z W
  have hcorner : (distinguishedCapSides (capTailCombination t Z W).cap.val).1.corner =
      (1 - (t : ℝ)) • (distinguishedCapSides Z.cap.val).1.corner +
        (t : ℝ) • (distinguishedCapSides W.cap.val).1.corner :=
    capInnerCorner_of_eq_convexBodyCombination (hcomb t Z W).1 paperGerverConstants.2.1
  have hvertex : (rightLeftTailArcs (capTailCombination t Z W).rightBody
      (capTailCombination t Z W).leftBody).1.startPoint =
      (1 - (t : ℝ)) • (rightLeftTailArcs Z.rightBody Z.leftBody).1.startPoint +
        (t : ℝ) • (rightLeftTailArcs W.rightBody W.leftBody).1.startPoint := by
    show (edgeVertices (capTailCombination t Z W).rightBody
      ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).1 = _
    rw [(hcomb t Z W).2.1]
    exact ((convexBody_maps_linear t Z.rightBody W.rightBody).2.1 _).1
  show ((distinguishedCapSides (capTailCombination t Z W).cap.val).1.corner,
    (rightLeftTailArcs (capTailCombination t Z W).rightBody
      (capTailCombination t Z W).leftBody).1.startPoint) = _
  rw [hcorner, hvertex]
  rfl

private theorem capTail_far_segmentAreas (X Y : CapTailSpace) :
    (segmentArea (rightLeftTailArcs X.rightBody X.leftBody).1.endPoint
      (rightLeftTailArcs Y.rightBody Y.leftBody).1.endPoint = 0) ∧
    (segmentArea (rightLeftTailArcs X.rightBody X.leftBody).2.startPoint
      (rightLeftTailArcs Y.rightBody Y.leftBody).2.startPoint = 0) := by
  -- ### The far endpoints of the two tails lie on the horizontal axis
  have hsupp : ∀ Z : CapTailSpace,
      supportValue (Z.rightBody : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 ∧
        supportValue (Z.leftBody : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    intro Z
    have hcapval :
        supportValue (Z.cap.val.val : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle) = 1 :=
      Z.cap.val.property.2.2.2.1
    have hr := Z.right_eq (Real.pi / 2) (by simp)
    have hl := Z.left_eq 0 (by simp)
    rw [show ((Real.pi + Real.pi / 2 : ℝ) : Real.Angle) =
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) from by congr 1; ring] at hr
    rw [show ((Real.pi / 2 + (0 : ℝ) : ℝ) : Real.Angle) =
        ((Real.pi / 2 : ℝ) : Real.Angle) from by congr 1; ring,
      show ((3 * Real.pi / 2 + (0 : ℝ) : ℝ) : Real.Angle) =
        ((3 * Real.pi / 2 : ℝ) : Real.Angle) from by congr 1; ring] at hl
    exact ⟨by linarith, by linarith⟩
  have hheight : ∀ K : ConvexBody Point,
      supportValue (K : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 →
      (edgeVertices K ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 1 = 0 ∧
        (edgeVertices K ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2 1 = 0 := by
    intro K hK
    have hn : normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
        -normalVector ((Real.pi / 2 : ℝ) : Real.Angle) := by
      rw [show ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
        ((Real.pi / 2 + Real.pi : ℝ) : Real.Angle) from by congr 1; ring]
      exact normalVector_add_pi _
    have key : ∀ p : Point,
        inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) = 0 → p 1 = 0 := by
      intro p hp
      rw [hn, inner_neg_right, inner_normalVector_real, Real.cos_pi_div_two,
        Real.sin_pi_div_two] at hp
      linarith
    have hfst : inner ℝ (edgeVertices K ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1
        (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue (K : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) :=
      (edgeVertices_fst_mem K _).2
    have hsnd : inner ℝ (edgeVertices K ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2
        (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue (K : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) :=
      (edgeVertices_snd_mem K _).2
    exact ⟨key _ (hfst.trans hK), key _ (hsnd.trans hK)⟩
  have hzeroSegment : ∀ p q : Point, p 1 = 0 → q 1 = 0 → segmentArea p q = 0 := by
    intro p q hp hq
    simp [segmentArea, planeCrossProduct, hp, hq]
  have hrightFar : segmentArea (rightLeftTailArcs X.rightBody X.leftBody).1.endPoint
      (rightLeftTailArcs Y.rightBody Y.leftBody).1.endPoint = 0 :=
    hzeroSegment _ _ (hheight X.rightBody (hsupp X).1).2 (hheight Y.rightBody (hsupp Y).1).2
  have hleftFar : segmentArea (rightLeftTailArcs X.rightBody X.leftBody).2.startPoint
      (rightLeftTailArcs Y.rightBody Y.leftBody).2.startPoint = 0 :=
    hzeroSegment _ _ (hheight X.leftBody (hsupp X).2).1 (hheight Y.leftBody (hsupp Y).2).1
  exact ⟨hrightFar, hleftFar⟩

private theorem capTail_left_segment_variation (X Y : CapTailSpace)
    (hL : (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint =
      (distinguishedCapSides X.cap.val).2.corner) :
    convexDirectionalDerivative capTailCombination
     (fun Z : CapTailSpace ↦ segmentArea (rightLeftTailArcs Z.rightBody Z.leftBody).2.endPoint
       (distinguishedCapSides Z.cap.val).2.corner) X Y =
     segmentArea (distinguishedCapSides X.cap.val).2.corner
         (distinguishedCapSides Y.cap.val).2.corner -
       segmentArea (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint
         (rightLeftTailArcs Y.rightBody Y.leftBody).2.endPoint := by
  have hleftPair := capTail_leftPair_isConvexLinear
  have hvar := segmentArea_variation.2
    (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint
    (distinguishedCapSides X.cap.val).2.corner
    (rightLeftTailArcs Y.rightBody Y.leftBody).2.endPoint
    (distinguishedCapSides Y.cap.val).2.corner
  have hbulk : (planeCrossProduct
      ((rightLeftTailArcs Y.rightBody Y.leftBody).2.endPoint +
        (distinguishedCapSides Y.cap.val).2.corner)
      ((distinguishedCapSides X.cap.val).2.corner -
        (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint) -
      2 * planeCrossProduct (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint
        (distinguishedCapSides X.cap.val).2.corner) / 2 = 0 := by
    rw [← hL]
    simp only [planeCrossProduct, sub_self, WithLp.ofLp_zero, Pi.zero_apply, mul_zero]
    ring
  rw [hbulk, zero_add] at hvar
  exact (convexDirectionalDerivative_comp_isConvexLinear hleftPair
    (fun x : Point × Point ↦ segmentArea x.1 x.2) X Y).trans hvar

theorem upperBoundQ_variation (X Y : CapTailSpace)
    (hR : (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint =
      (distinguishedCapSides X.cap.val).1.corner)
    (hL : (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint =
      (distinguishedCapSides X.cap.val).2.corner) :
    convexDirectionalDerivative capTailCombination upperBoundQ X Y = qVariationIntegral X Y := by
  obtain ⟨hcomb, -⟩ := capTail_isConvexDomain
  obtain ⟨hrIoo, hlIoo, -⟩ := paperGerverConstants_snd_mem_Ioo
  have hpi := Real.pi_pos
  -- ### The three components of a cap-tail triple depend convex-linearly on it
  have hcap : IsConvexLinear capTailCombination specialCapCombination
      (fun Z : CapTailSpace ↦ Z.cap) := fun t Z W ↦
    Subtype.ext (Subtype.ext ((hcomb t Z W).1.trans
      (specialCap_isConvexDomain.1 t Z.cap W.cap).symm))
  have hright : IsConvexLinear capTailCombination convexBodyCombination
      (fun Z : CapTailSpace ↦ Z.rightBody) := fun t Z W ↦ (hcomb t Z W).2.1
  have hleft : IsConvexLinear capTailCombination convexBodyCombination
      (fun Z : CapTailSpace ↦ Z.leftBody) := fun t Z W ↦ (hcomb t Z W).2.2
  -- ### The two segment endpoint pairs depend convex-linearly on the triple
  have hleftPair := capTail_leftPair_isConvexLinear
  have hrightPair := capTail_rightPair_isConvexLinear
  -- ### Quadraticity of the six summands of `𝒬`
  have hq1 : IsQuadraticFunctional capTailCombination
      (fun Z : CapTailSpace ↦ ClassicalResults.area (Z.cap.val.val : Set Point)) :=
    specialCapArea_variation.1.comp_isConvexLinear hcap
  have hq2 : IsQuadraticFunctional capTailCombination
      (fun Z : CapTailSpace ↦ convexArcArea Z.leftBody (3 * Real.pi / 2)
        (3 * Real.pi / 2 + paperGerverConstants.2.2)) :=
    (convexArcArea_variation _ _ (by linarith [hlIoo.1]) (by linarith [hlIoo.2])).1
      |>.comp_isConvexLinear hleft
  have hq3 : IsQuadraticFunctional capTailCombination
      (fun Z : CapTailSpace ↦ segmentArea (rightLeftTailArcs Z.rightBody Z.leftBody).2.endPoint
        (distinguishedCapSides Z.cap.val).2.corner) :=
    segmentArea_variation.1.comp_isConvexLinear hleftPair
  have hq4 : IsQuadraticFunctional capTailCombination
      (fun Z : CapTailSpace ↦ curveAreaFunctional (capMiddleBV Z.cap)) :=
    capInnerCorner_variation.2.1.comp_isConvexLinear hcap
  have hq5 : IsQuadraticFunctional capTailCombination
      (fun Z : CapTailSpace ↦ segmentArea (distinguishedCapSides Z.cap.val).1.corner
        (rightLeftTailArcs Z.rightBody Z.leftBody).1.startPoint) :=
    segmentArea_variation.1.comp_isConvexLinear hrightPair
  have hq6 : IsQuadraticFunctional capTailCombination
      (fun Z : CapTailSpace ↦ convexArcArea Z.rightBody (Real.pi + paperGerverConstants.2.1)
        (3 * Real.pi / 2)) :=
    (convexArcArea_variation _ _ (by linarith [hrIoo.2]) (by linarith [hrIoo.1])).1
      |>.comp_isConvexLinear hright
  -- ### The four summands whose derivatives contribute an integral
  have hd1 : convexDirectionalDerivative capTailCombination
      (fun Z : CapTailSpace ↦ ClassicalResults.area (Z.cap.val.val : Set Point)) X Y =
      ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi,
        (supportValue Y.cap.val.val t - supportValue X.cap.val.val t)
          ∂surfaceAreaMeasure X.cap.val.val :=
    (convexDirectionalDerivative_comp_isConvexLinear hcap
      (fun K : SpecialCapSpace ↦ ClassicalResults.area (K.val.val : Set Point)) X Y).trans
      (specialCapArea_variation.2 X.cap Y.cap)
  have hd2 : convexDirectionalDerivative capTailCombination
      (fun Z : CapTailSpace ↦ convexArcArea Z.leftBody (3 * Real.pi / 2)
        (3 * Real.pi / 2 + paperGerverConstants.2.2)) X Y =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
          Set.Ioo (3 * Real.pi / 2) (3 * Real.pi / 2 + paperGerverConstants.2.2),
        (supportValue Y.leftBody t - supportValue X.leftBody t)
          ∂surfaceAreaMeasure X.leftBody) +
        (segmentArea (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint
            (rightLeftTailArcs Y.rightBody Y.leftBody).2.endPoint -
          segmentArea (rightLeftTailArcs X.rightBody X.leftBody).2.startPoint
            (rightLeftTailArcs Y.rightBody Y.leftBody).2.startPoint) :=
    (convexDirectionalDerivative_comp_isConvexLinear hleft
      (fun M : ConvexBody Point ↦ convexArcArea M (3 * Real.pi / 2)
        (3 * Real.pi / 2 + paperGerverConstants.2.2)) X Y).trans
      ((convexArcArea_variation _ _ (by linarith [hlIoo.1]) (by linarith [hlIoo.2])).2
        X.leftBody Y.leftBody)
  have hd4 : convexDirectionalDerivative capTailCombination
      (fun Z : CapTailSpace ↦ curveAreaFunctional (capMiddleBV Z.cap)) X Y =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
          (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
            Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
              (Real.pi / 2 + paperGerverConstants.2.2)),
        (supportValue Y.cap.val.val t - supportValue X.cap.val.val t)
          ∂capCornerAngleMeasure X.cap) +
        (segmentArea (distinguishedCapSides X.cap.val).2.corner
            (distinguishedCapSides Y.cap.val).2.corner -
          segmentArea (distinguishedCapSides X.cap.val).1.corner
            (distinguishedCapSides Y.cap.val).1.corner) :=
    (convexDirectionalDerivative_comp_isConvexLinear hcap
      (fun M : SpecialCapSpace ↦ curveAreaFunctional (capMiddleBV M)) X Y).trans
      (capInnerCorner_variation.2.2 X.cap Y.cap)
  have hd6 : convexDirectionalDerivative capTailCombination
      (fun Z : CapTailSpace ↦ convexArcArea Z.rightBody (Real.pi + paperGerverConstants.2.1)
        (3 * Real.pi / 2)) X Y =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
          Set.Ioo (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2),
        (supportValue Y.rightBody t - supportValue X.rightBody t)
          ∂surfaceAreaMeasure X.rightBody) +
        (segmentArea (rightLeftTailArcs X.rightBody X.leftBody).1.endPoint
            (rightLeftTailArcs Y.rightBody Y.leftBody).1.endPoint -
          segmentArea (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint
            (rightLeftTailArcs Y.rightBody Y.leftBody).1.startPoint) :=
    (convexDirectionalDerivative_comp_isConvexLinear hright
      (fun M : ConvexBody Point ↦ convexArcArea M (Real.pi + paperGerverConstants.2.1)
        (3 * Real.pi / 2)) X Y).trans
      ((convexArcArea_variation _ _ (by linarith [hrIoo.2]) (by linarith [hrIoo.1])).2
        X.rightBody Y.rightBody)
  -- ### The two segment summands: their bulk terms vanish because the base endpoints coincide
  have hd3 := capTail_left_segment_variation X Y hL
  have hd5 : convexDirectionalDerivative capTailCombination
      (fun Z : CapTailSpace ↦ segmentArea (distinguishedCapSides Z.cap.val).1.corner
        (rightLeftTailArcs Z.rightBody Z.leftBody).1.startPoint) X Y =
      segmentArea (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint
          (rightLeftTailArcs Y.rightBody Y.leftBody).1.startPoint -
        segmentArea (distinguishedCapSides X.cap.val).1.corner
          (distinguishedCapSides Y.cap.val).1.corner := by
    have hvar := segmentArea_variation.2
      (distinguishedCapSides X.cap.val).1.corner
      (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint
      (distinguishedCapSides Y.cap.val).1.corner
      (rightLeftTailArcs Y.rightBody Y.leftBody).1.startPoint
    have hbulk : (planeCrossProduct
        ((distinguishedCapSides Y.cap.val).1.corner +
          (rightLeftTailArcs Y.rightBody Y.leftBody).1.startPoint)
        ((rightLeftTailArcs X.rightBody X.leftBody).1.startPoint -
          (distinguishedCapSides X.cap.val).1.corner) -
        2 * planeCrossProduct (distinguishedCapSides X.cap.val).1.corner
          (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint) / 2 = 0 := by
      rw [hR]
      simp only [planeCrossProduct, sub_self, WithLp.ofLp_zero, Pi.zero_apply, mul_zero]
      ring
    rw [hbulk, zero_add] at hvar
    exact (convexDirectionalDerivative_comp_isConvexLinear hrightPair
      (fun x : Point × Point ↦ segmentArea x.1 x.2) X Y).trans hvar
  -- ### The derivative of `𝒬` is the signed sum of the six derivatives
  have hsplit : ∀ t : ℝ, segmentFunctional capTailCombination upperBoundQ X Y t =
      segmentFunctional capTailCombination
            (fun Z : CapTailSpace ↦ ClassicalResults.area (Z.cap.val.val : Set Point)) X Y t +
          segmentFunctional capTailCombination
            (fun Z : CapTailSpace ↦ convexArcArea Z.leftBody (3 * Real.pi / 2)
              (3 * Real.pi / 2 + paperGerverConstants.2.2)) X Y t +
          segmentFunctional capTailCombination
            (fun Z : CapTailSpace ↦ segmentArea
              (rightLeftTailArcs Z.rightBody Z.leftBody).2.endPoint
              (distinguishedCapSides Z.cap.val).2.corner) X Y t -
          segmentFunctional capTailCombination
            (fun Z : CapTailSpace ↦ curveAreaFunctional (capMiddleBV Z.cap)) X Y t +
          segmentFunctional capTailCombination
            (fun Z : CapTailSpace ↦ segmentArea (distinguishedCapSides Z.cap.val).1.corner
              (rightLeftTailArcs Z.rightBody Z.leftBody).1.startPoint) X Y t +
          segmentFunctional capTailCombination
            (fun Z : CapTailSpace ↦ convexArcArea Z.rightBody
              (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2)) X Y t := by
    intro t
    simp only [segmentFunctional]
    split_ifs with ht
    · rfl
    · norm_num
  have hD1 := hq1.hasDerivWithinAt_segmentFunctional X Y
  have hD2 := hq2.hasDerivWithinAt_segmentFunctional X Y
  have hD3 := hq3.hasDerivWithinAt_segmentFunctional X Y
  have hD4 := hq4.hasDerivWithinAt_segmentFunctional X Y
  have hD5 := hq5.hasDerivWithinAt_segmentFunctional X Y
  have hD6 := hq6.hasDerivWithinAt_segmentFunctional X Y
  rw [hd1] at hD1
  rw [hd2] at hD2
  rw [hd3] at hD3
  rw [hd4] at hD4
  rw [hd5] at hD5
  rw [hd6] at hD6
  have hderiv := convexDirectionalDerivative_eq_of_hasDerivWithinAt capTailCombination
    upperBoundQ X Y ((((((hD1.add hD2).add hD3).sub hD4).add hD5).add hD6).congr
      (fun t _ ↦ hsplit t) (hsplit 0))
  obtain ⟨hrightFar, hleftFar⟩ := capTail_far_segmentAreas X Y
  -- ### The two tail integrals in opposite-angle coordinates
  have hrightTail : (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
        Set.Ioo (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2),
      (supportValue Y.rightBody t - supportValue X.rightBody t)
        ∂surfaceAreaMeasure X.rightBody) =
      ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
          Set.Ioo paperGerverConstants.2.1 (Real.pi / 2),
        ((oppositeSurfaceData Y.rightBody).2 t - (oppositeSurfaceData X.rightBody).2 t)
          ∂(oppositeSurfaceData X.rightBody).1 :=
    (setIntegral_oppositeSurfaceData_angleImage_Ioo X.rightBody
      (a := paperGerverConstants.2.1) (b := Real.pi / 2) (by ring) (by ring)
      (f := fun u : Real.Angle ↦ supportValue Y.rightBody u - supportValue X.rightBody u)
      ((continuous_supportValue Y.rightBody).sub
        (continuous_supportValue X.rightBody)).measurable).symm
  have hleftTail : (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
        Set.Ioo (3 * Real.pi / 2) (3 * Real.pi / 2 + paperGerverConstants.2.2),
      (supportValue Y.leftBody t - supportValue X.leftBody t)
        ∂surfaceAreaMeasure X.leftBody) =
      ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
          Set.Ioo (Real.pi / 2) (Real.pi / 2 + paperGerverConstants.2.2),
        ((oppositeSurfaceData Y.leftBody).2 t - (oppositeSurfaceData X.leftBody).2 t)
          ∂(oppositeSurfaceData X.leftBody).1 :=
    (setIntegral_oppositeSurfaceData_angleImage_Ioo X.leftBody
      (a := Real.pi / 2) (b := Real.pi / 2 + paperGerverConstants.2.2) (by ring) (by ring)
      (f := fun u : Real.Angle ↦ supportValue Y.leftBody u - supportValue X.leftBody u)
      ((continuous_supportValue Y.leftBody).sub
        (continuous_supportValue X.leftBody)).measurable).symm
  -- ### Collecting the six contributions
  rw [hderiv]
  simp only [qVariationIntegral]
  linarith [hrightTail, hleftTail, hrightFar, hleftFar]

end MovingSofa

end

end

end
