/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Bounds.Applications.Development001
public import LeanPool.MovingSofa.Bounds.Foundations.Development003
public import LeanPool.MovingSofa.ForMathlib.Analysis.Foundations.Development001
public import LeanPool.MovingSofa.ForMathlib.MeasureTheory.Foundations.Development001
/-!
# Moving sofa: related mathematical developments

* `Polygon.BalancedInequalities`.
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
# Polygon / Balanced Inequalities
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- A real angle strictly inside one full turn is not the zero angle. -/
private theorem coe_ne_zero_of_pos_of_lt_two_pi {x : ℝ} (h0 : 0 < x)
    (h2 : x < 2 * Real.pi) : ((x : ℝ) : Real.Angle) ≠ (0 : Real.Angle) := by
  rw [← Real.Angle.coe_zero]
  refine Real.Angle.coe_ne_coe_of_abs_sub_lt (by linarith) ?_
  rw [abs_lt]
  constructor <;> linarith [Real.pi_pos]

/-- Adding half a turn keeps a small positive angle away from zero. -/
private theorem coe_add_pi_ne_zero_of_pos_of_lt_pi {x : ℝ} (h0 : 0 < x)
    (h1 : x < Real.pi) :
    ((x : ℝ) : Real.Angle) + ((Real.pi : ℝ) : Real.Angle) ≠ (0 : Real.Angle) := by
  rw [← Real.Angle.coe_add]
  exact coe_ne_zero_of_pos_of_lt_two_pi (by linarith) (by linarith)

/-- A right-angle polygon cap has no face with horizontal outward normal. -/
private theorem rightAngle_edgeVertices_zero_eq (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) :
    (edgeVertices K.val.val (0 : Real.Angle)).1 =
      (edgeVertices K.val.val (0 : Real.Angle)).2 := by
  by_contra hne
  have hpi := Real.pi_pos
  have hangle : (rightAngleSet n hn).angle = Real.pi / 2 := rfl
  have hlow : ∀ u ∈ capLowerNormals (rightAngleSet n hn).angle,
      u = ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    intro u hu
    simp only [capLowerNormals, hangle, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · congr 1
      ring
    · rfl
  have h3zero : ((3 * Real.pi / 2 : ℝ) : Real.Angle) ≠ (0 : Real.Angle) :=
    coe_ne_zero_of_pos_of_lt_two_pi (by linarith) (by linarith)
  have h3pi : ((3 * Real.pi / 2 : ℝ) : Real.Angle) + ((Real.pi : ℝ) : Real.Angle) ≠
      (0 : Real.Angle) := by
    have hshift : ((3 * Real.pi / 2 : ℝ) : Real.Angle) + ((Real.pi : ℝ) : Real.Angle) =
        ((Real.pi / 2 : ℝ) : Real.Angle) := by
      rw [← Real.Angle.coe_add, Real.Angle.angle_eq_iff_two_pi_dvd_sub]
      exact ⟨1, by push_cast; ring⟩
    rw [hshift]
    exact coe_ne_zero_of_pos_of_lt_two_pi (by linarith) (by linarith)
  have hmain := K.properEdgeNormal_mem_allowed_or_antipodal (0 : Real.Angle) hne
  rcases hmain with (⟨r, hr, hr0⟩ | hlowmem) | ⟨u, huN, hu0⟩
  · exact coe_ne_zero_of_pos_of_lt_two_pi
      (angleDomain_subset_Ioo _ hr).1
      (by linarith [(angleDomain_subset_Ioo _ hr).2]) hr0
  · exact h3zero (hlow _ hlowmem).symm
  · rcases huN with ⟨r, hr, rfl⟩ | hlowmem
    · exact coe_add_pi_ne_zero_of_pos_of_lt_pi
        (angleDomain_subset_Ioo _ hr).1 (angleDomain_subset_Ioo _ hr).2 hu0
    · rw [hlow _ hlowmem] at hu0
      exact h3pi hu0

/-- The surface measure of a right-angle polygon cap has no horizontal-normal atom. -/
private theorem rightAngle_surfaceAreaMeasure_zero (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) :
    surfaceAreaMeasure K.val.val {((0 : ℝ) : Real.Angle)} = 0 := by
  rw [Real.Angle.coe_zero, (surfaceAreaMeasure_atom_length K.val.val (0 : Real.Angle)).2.1,
    rightAngle_edgeVertices_zero_eq n hn K]
  simp

/-- The real-arithmetic core of the discrete balancing inequality. -/
private theorem magicBound_of_le {δ T c s gp gm : ℝ} (hδpos : 0 < δ) (hδ45 : δ ≤ 4 / 5)
    (hTub : T ≤ δ + 4 / 3 * δ ^ 3) (hTpos : 0 < T)
    (hcub : c ≤ δ / 2 + 4 / 3 * (δ / 2) ^ 3) (hcpos : 0 < c)
    (hgp5 : gp ≤ 5) (hgm0 : 0 ≤ gm) (hgle : gm ≤ gp)
    (hsum : s ≤ T * max 0 (gm - 1 + c) + T * max 0 (1 - gp + c) + max 0 (2 * c - s)) :
    s ≤ max |gp - 1| ((|gp - 1| + 1) / 2) * δ + 8 * δ ^ 2 := by
  have hW0 : 0 ≤ max 0 (gm - 1) + max 0 (1 - gp) := by positivity
  have hMsum : max 0 (gm - 1) + max 0 (1 - gp) ≤ |gp - 1| := by
    rcases le_total gp 1 with hg | hg
    · rw [abs_of_nonpos (by linarith), max_eq_left (show gm - 1 ≤ 0 by linarith),
        max_eq_right (show (0 : ℝ) ≤ 1 - gp by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith), max_eq_left (show (1 : ℝ) - gp ≤ 0 by linarith)]
      rcases le_total gm 1 with h2 | h2
      · rw [max_eq_left (show gm - 1 ≤ 0 by linarith)]
        linarith
      · rw [max_eq_right (show (0 : ℝ) ≤ gm - 1 by linarith)]
        linarith
  have hMsum4 : max 0 (gm - 1) + max 0 (1 - gp) ≤ 4 := by
    rcases le_total gm 1 with h2 | h2
    · rw [max_eq_left (show gm - 1 ≤ 0 by linarith)]
      have h3 : max 0 (1 - gp) ≤ 1 := max_le (by norm_num) (by linarith)
      linarith
    · rw [max_eq_left (show (1 : ℝ) - gp ≤ 0 by linarith),
        max_eq_right (show (0 : ℝ) ≤ gm - 1 by linarith)]
      linarith
  have hstep1 : max 0 (gm - 1 + c) ≤ max 0 (gm - 1) + c := by
    rcases le_total (gm - 1 + c) 0 with h | h
    · rw [max_eq_left h]
      linarith [le_max_left (0 : ℝ) (gm - 1)]
    · rw [max_eq_right h]
      linarith [le_max_right (0 : ℝ) (gm - 1)]
  have hstep2 : max 0 (1 - gp + c) ≤ max 0 (1 - gp) + c := by
    rcases le_total (1 - gp + c) 0 with h | h
    · rw [max_eq_left h]
      linarith [le_max_left (0 : ℝ) (1 - gp)]
    · rw [max_eq_right h]
      linarith [le_max_right (0 : ℝ) (1 - gp)]
  have e1 : T * max 0 (gm - 1 + c) ≤ T * (max 0 (gm - 1) + c) :=
    mul_le_mul_of_nonneg_left hstep1 hTpos.le
  have e2 : T * max 0 (1 - gp + c) ≤ T * (max 0 (1 - gp) + c) :=
    mul_le_mul_of_nonneg_left hstep2 hTpos.le
  have hcombine : s ≤ T * (max 0 (gm - 1) + max 0 (1 - gp)) + 2 * (T * c) +
      max 0 (2 * c - s) := by nlinarith only [e1, e2, hsum]
  have p3 : δ ^ 3 ≤ 4 / 5 * δ ^ 2 := by
    nlinarith only [mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr hδ45)]
  have hδsq : δ ^ 2 ≤ 16 / 25 := by nlinarith only [hδpos, hδ45]
  have p4 : δ ^ 4 ≤ 16 / 25 * δ ^ 2 := by
    nlinarith only [mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr hδsq)]
  have p6 : δ ^ 6 ≤ 1 / 2 * δ ^ 2 := by
    nlinarith only [mul_nonneg (sq_nonneg δ)
      (show (0 : ℝ) ≤ 1 / 2 - δ ^ 4 by nlinarith only [p4, hδsq])]
  have f1 : T * (max 0 (gm - 1) + max 0 (1 - gp)) ≤
      (δ + 4 / 3 * δ ^ 3) * (max 0 (gm - 1) + max 0 (1 - gp)) :=
    mul_le_mul_of_nonneg_right hTub hW0
  have f2 : δ * (max 0 (gm - 1) + max 0 (1 - gp)) ≤ δ * |gp - 1| :=
    mul_le_mul_of_nonneg_left hMsum hδpos.le
  have f3 : 4 / 3 * δ ^ 3 * (max 0 (gm - 1) + max 0 (1 - gp)) ≤ 4 / 3 * δ ^ 3 * 4 :=
    mul_le_mul_of_nonneg_left hMsum4 (by positivity)
  have f4 : T * c ≤ (δ + 4 / 3 * δ ^ 3) * (δ / 2 + 4 / 3 * (δ / 2) ^ 3) :=
    mul_le_mul hTub hcub hcpos.le (by positivity)
  have hE : T * (max 0 (gm - 1) + max 0 (1 - gp)) + 2 * (T * c) ≤
      |gp - 1| * δ + 7 * δ ^ 2 := by
    nlinarith only [f1, f2, f3, f4, p3, p4, p6]
  have hak1 : |gp - 1| * δ ≤ max |gp - 1| ((|gp - 1| + 1) / 2) * δ :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hδpos.le
  have hak2 : (|gp - 1| + 1) / 2 * δ ≤ max |gp - 1| ((|gp - 1| + 1) / 2) * δ :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hδpos.le
  have h2c : 2 * c ≤ δ + 1 / 3 * δ ^ 3 := by nlinarith only [hcub]
  rcases le_total (2 * c - s) 0 with hcase | hcase
  · rw [max_eq_left hcase] at hcombine
    nlinarith only [hcombine, hE, hak1, sq_nonneg δ]
  · rw [max_eq_right hcase] at hcombine
    nlinarith only [hcombine, hE, hak2, h2c, p3, sq_nonneg δ]

private theorem bRay_horizontal_boundary_measure_zero (K : ConvexBody Point)
    (t : ℝ) (htIoo : t ∈ Set.Ioo 0 (Real.pi / 2)) :
    Measure.hausdorffMeasure 1
       ((rotatingHallwayParts (K : Set Point) (t : Real.Angle)).bRay ∩
         {p : Point | inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0}) = 0 := by
  have hpi := Real.pi_pos
  have hns : NullSingletonClass (Measure.hausdorffMeasure 1 : Measure Point) :=
    Measure.nullSingletonClass_hausdorff Point one_pos
  refine Set.Subsingleton.measure_zero ?_ _
  intro x hx y hy
  by_contra hxy
  have h1 : inner ℝ (x - y) (normalVector (t : Real.Angle)) = 0 := by
    rw [inner_sub_left, ((mem_rotatingHallwayParts_bRay_iff _ _ x).mp hx.1).1,
      ((mem_rotatingHallwayParts_bRay_iff _ _ y).mp hy.1).1, sub_self]
  have hx2 : inner ℝ x (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := hx.2
  have hy2 : inner ℝ y (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := hy.2
  have h2 : inner ℝ (x - y) (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    rw [inner_sub_left, hx2, hy2, sub_self]
  rcases normalVector_eq_or_eq_add_pi_of_orthogonal (sub_ne_zero.mpr hxy) h1 h2 with hA | hA
  · exact Real.Angle.coe_ne_coe_of_abs_sub_lt (by linarith [htIoo.2])
      (by rw [abs_lt]; constructor <;> linarith [htIoo.1, htIoo.2]) hA
  · rw [← Real.Angle.coe_add] at hA
    exact Real.Angle.coe_ne_coe_of_abs_sub_lt (by linarith [htIoo.2])
      (by rw [abs_lt]; constructor <;> linarith [htIoo.1, htIoo.2]) hA

/-- The magic function `k₀` read as a function on all reals through truncation. -/
def magicDensity (x : ℝ) : ℝ := magicFunctions.1 x.toNNReal

theorem maximumPolygonCap_surfaceAtom_bound (n : ℕ) (hn : 2 ≤ n)
    (K : RightAngleCapSpace) (hK : IsMaximumPolygonCapSteps n K) (t : ℝ)
    (ht : t = 0 ∨ t ∈ (rightAngleSet n hn).directions) :
    surfaceAreaMeasure K.val {(t : Real.Angle)} ≤
      ENNReal.ofReal (magicFunctions.1 (Real.toNNReal (tangentArmLengths K t).2.1) *
        polygonStepSize n + 8 * polygonStepSize n ^ 2) := by
  classical
  obtain ⟨hn2, hdy, P, hPK, hmax⟩ := hK
  subst hPK
  have hpi := Real.pi_pos
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hδpos : 0 < polygonStepSize n := by
    have hn0 : (0 : ℝ) < n := by linarith
    simp only [polygonStepSize]
    positivity
  have hδle : polygonStepSize n ≤ Real.pi / 4 := by
    have hn0 : (0 : ℝ) < n := by linarith
    rw [polygonStepSize, div_le_iff₀ hn0]
    nlinarith
  rcases ht with rfl | ht
  · rw [rightAngle_surfaceAreaMeasure_zero n hn2 P]
    exact zero_le
  · have htIoo : t ∈ Set.Ioo 0 (Real.pi / 2) := (rightAngleSet n hn2).interior t ht
    have hcap : supportValue (P.val.val : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle) = 1 :=
      P.val.property.2.2.2.1
    have htdom : t ∈ angleDomain (rightAngleSet n hn2) :=
      Set.mem_union_left _ (Set.mem_union_left _ (Finset.mem_coe.mpr ht))
    have hatom : surfaceAreaMeasure P.val.val {(t : Real.Angle)} =
        ENNReal.ofReal (polygonCapPolylineLength P ⟨t, htdom⟩) :=
      maximumPolygonCap_balanced P hmax ⟨t, htdom⟩
    have hlenat : polygonPolylineLengthAt P t = polygonCapPolylineLength P ⟨t, htdom⟩ := by
      simp only [polygonPolylineLengthAt, htdom, ↓reduceDIte]
    have hwall : (Measure.hausdorffMeasure 1
        (frontier (polygonNiche (rightAngleSet n hn2) P.val) ∩
          (rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).bRay)).toReal =
        polygonPolylineLengthAt P t := (polygonNiche_wall_lengths P ht).2.1
    have hτnonneg : 0 ≤ polygonCapPolylineLength P ⟨t, htdom⟩ := by
      rw [← hlenat, ← hwall]
      exact ENNReal.toReal_nonneg
    -- the three pieces
    have hlegs := maximumPolygonCap_leg_lengths n hn2 hdy P hmax t ht
    have hsubset : frontier (polygonNiche (rightAngleSet n hn2) P.val) ∩
          (rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).bRay ⊆
        (((rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).bRay ∩
            {p : Point | inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0}) ∪
          ((rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).bRay ∩
            (innerWallUpperHalfPlanes P.val (t - polygonStepSize n)).2)) ∪
          ((rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).bRay ∩
            (innerWallUpperHalfPlanes P.val (t + polygonStepSize n)).2) ∪
          ({p : Point | inner ℝ p (normalVector (t : Real.Angle)) =
              supportValue (P.val.val : Set Point) (t : Real.Angle) - 1} ∩
            ((innerWallUpperHalfPlanes P.val (t - polygonStepSize n)).1 ∩
              (innerWallUpperHalfPlanes P.val (t + polygonStepSize n)).1)) := by
      rintro p ⟨hpfront, hpray⟩
      have hpline : inner ℝ p (normalVector (t : Real.Angle)) =
          supportValue (P.val.val : Set Point) (t : Real.Angle) - 1 :=
        ((mem_rotatingHallwayParts_bRay_iff _ _ p).mp hpray).1
      by_cases hzero : inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0
      · exact Or.inl (Or.inl (Or.inl ⟨hpray, hzero⟩))
      · have hclos : p ∈ capFan (rightAngleSet n hn2).angle := by
          have hsub : closure (polygonNiche (rightAngleSet n hn2) P.val) ⊆
              capFan (rightAngleSet n hn2).angle :=
            (isClosed_capFan _).closure_subset_iff.mpr (fun q hq ↦ hq.1)
          exact hsub hpfront.1
        have hppos : 0 < inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) :=
          lt_of_le_of_ne hclos.2 (Ne.symm hzero)
        have hnotN : p ∉ polygonNiche (rightAngleSet n hn2) P.val := by
          intro hpN
          refine hpfront.2 ?_
          have hUopen : IsOpen {q : Point |
              0 < inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))} :=
            isOpen_lt continuous_const (by fun_prop)
          have hVopen : IsOpen (⋃ u ∈ (rightAngleSet n hn2).directions,
              innerQuadrant (P.val.val : Set Point) u) :=
            isOpen_biUnion (fun u _ ↦ isOpen_innerQuadrant _ u)
          refine interior_maximal ?_ (hUopen.inter hVopen) ⟨hppos, hpN.2⟩
          rintro q ⟨hq1, hq2⟩
          have hq1' : (0 : ℝ) < inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) := hq1
          exact ⟨⟨hq1'.le, hq1'.le⟩, hq2⟩
        have hquad : ∀ u : ℝ,
            (u = 0 ∨ u = Real.pi / 2 ∨ u ∈ (rightAngleSet n hn2).directions) →
            p ∉ innerQuadrant (P.val.val : Set Point) u := by
          rintro u (rfl | rfl | hu)
          · intro hq
            have h2 : inner ℝ p (normalVector ((0 + Real.pi / 2 : ℝ) : Real.Angle)) <
                supportValue (P.val.val : Set Point)
                  ((0 + Real.pi / 2 : ℝ) : Real.Angle) - 1 := hq.2
            rw [show (0 + Real.pi / 2 : ℝ) = Real.pi / 2 by ring, hcap] at h2
            linarith
          · intro hq
            have h1 : inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) <
                supportValue (P.val.val : Set Point)
                  ((Real.pi / 2 : ℝ) : Real.Angle) - 1 := hq.1
            rw [hcap] at h1
            linarith
          · intro hq
            exact hnotN ⟨hclos, Set.mem_biUnion hu hq⟩
        have hq1 : p ∉ innerQuadrant (P.val.val : Set Point) (t - polygonStepSize n) :=
          hquad _ ((rightAngleSet_sub_step n hn2 ht).imp id Or.inr)
        have hq2 : p ∉ innerQuadrant (P.val.val : Set Point) (t + polygonStepSize n) :=
          hquad _ (Or.inr ((rightAngleSet_add_step n hn2 ht).imp id id))
        rcases (notMem_innerQuadrant_iff _ _ _).mp hq1 with hb1 | hd1
        · rcases (notMem_innerQuadrant_iff _ _ _).mp hq2 with hb2 | hd2
          · exact Or.inr ⟨hpline, hb1, hb2⟩
          · exact Or.inl (Or.inr ⟨hpray, hd2⟩)
        · exact Or.inl (Or.inl (Or.inr ⟨hpray, hd1⟩))
    have hz := bRay_horizontal_boundary_measure_zero P.val.val t htIoo
    have hslice := hausdorffMeasure_faceLine_inter_innerWalls_le P.val.val t
      (polygonStepSize n) hδpos (by linarith)
    have hbound : Measure.hausdorffMeasure 1
        (frontier (polygonNiche (rightAngleSet n hn2) P.val) ∩
          (rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).bRay) ≤
        ENNReal.ofReal (Real.tan (polygonStepSize n) *
            max 0 ((tangentArmLengths P.val t).2.2 - 1 +
              Real.tan (polygonStepSize n / 2))) +
          ENNReal.ofReal (Real.tan (polygonStepSize n) *
            max 0 (1 - (tangentArmLengths P.val t).2.1 +
              Real.tan (polygonStepSize n / 2))) +
          ENNReal.ofReal (max 0 (2 * Real.tan (polygonStepSize n / 2) -
            (surfaceAreaMeasure P.val.val {(t : Real.Angle)}).toReal)) := by
      have hAB : Measure.hausdorffMeasure 1
          (((rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).bRay ∩
              {p : Point | inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0}) ∪
            ((rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).bRay ∩
              (innerWallUpperHalfPlanes P.val (t - polygonStepSize n)).2)) ≤
          ENNReal.ofReal (Real.tan (polygonStepSize n) *
            max 0 ((tangentArmLengths P.val t).2.2 - 1 +
              Real.tan (polygonStepSize n / 2))) := by
        refine (measure_union_le _ _).trans ?_
        rw [hz, hlegs.1, zero_add]
      exact (measure_mono hsubset).trans ((measure_union_le _ _).trans
        (add_le_add ((measure_union_le _ _).trans
          (add_le_add hAB (le_of_eq hlegs.2))) hslice))
    have harm := (maximumPolygonCap_arm_bound n P.val ⟨hn2, hdy, P, rfl, hmax⟩).2 t
      ⟨htIoo.1.le, htIoo.2.le⟩
    have hgp0 : 0 ≤ (tangentArmLengths P.val t).2.1 := harm.2.2.1.1
    have hgp5 : (tangentArmLengths P.val t).2.1 ≤ 5 := harm.2.2.1.2
    have hgm0 : 0 ≤ (tangentArmLengths P.val t).2.2 := harm.2.2.2.1
    have harm1 : (tangentArmLengths P.val t).2.1 =
        inner ℝ ((rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).outerCorner -
          (edgeVertices P.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1)
          (normalVector (t : Real.Angle)) := rfl
    have harm2 : (tangentArmLengths P.val t).2.2 =
        inner ℝ ((rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).outerCorner -
          (edgeVertices P.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).2)
          (normalVector (t : Real.Angle)) := rfl
    have hgle : (tangentArmLengths P.val t).2.2 ≤ (tangentArmLengths P.val t).2.1 := by
      have hC : (edgeVertices P.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1 =
          (edgeVertices P.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).2 -
            (surfaceAreaMeasure P.val.val {((t + Real.pi / 2 : ℝ) : Real.Angle)}).toReal •
              normalVector (t : Real.Angle) := by
        rw [(surfaceAreaMeasure_atom_length P.val.val
          ((t + Real.pi / 2 : ℝ) : Real.Angle)).2.2, tangentVector_add_pi_div_two]
        module
      rw [harm1, harm2, hC, show (rotatingHallwayParts (P.val.val : Set Point)
            (t : Real.Angle)).outerCorner -
          ((edgeVertices P.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).2 -
            (surfaceAreaMeasure P.val.val {((t + Real.pi / 2 : ℝ) : Real.Angle)}).toReal •
              normalVector (t : Real.Angle)) =
          ((rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).outerCorner -
            (edgeVertices P.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).2) +
            (surfaceAreaMeasure P.val.val {((t + Real.pi / 2 : ℝ) : Real.Angle)}).toReal •
              normalVector (t : Real.Angle) from by module,
        inner_add_left, real_inner_smul_left, inner_normalVector_self, mul_one]
      have := ENNReal.toReal_nonneg (a := surfaceAreaMeasure P.val.val
        {((t + Real.pi / 2 : ℝ) : Real.Angle)})
      linarith
    have hstoReal : (surfaceAreaMeasure P.val.val {(t : Real.Angle)}).toReal =
        polygonCapPolylineLength P ⟨t, htdom⟩ := by
      rw [hatom, ENNReal.toReal_ofReal hτnonneg]
    have hXeq : (surfaceAreaMeasure P.val.val {(t : Real.Angle)}).toReal =
        (Measure.hausdorffMeasure 1
          (frontier (polygonNiche (rightAngleSet n hn2) P.val) ∩
            (rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).bRay)).toReal := by
      rw [hstoReal, ← hlenat]
      exact hwall.symm
    have hTpos : 0 < Real.tan (polygonStepSize n) :=
      Real.tan_pos_of_pos_of_lt_pi_div_two hδpos (by linarith)
    have hcpos : 0 < Real.tan (polygonStepSize n / 2) :=
      Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (le_max_left _ _)] at hbound
    have hsum : (surfaceAreaMeasure P.val.val {(t : Real.Angle)}).toReal ≤
        Real.tan (polygonStepSize n) *
            max 0 ((tangentArmLengths P.val t).2.2 - 1 + Real.tan (polygonStepSize n / 2)) +
          Real.tan (polygonStepSize n) *
            max 0 (1 - (tangentArmLengths P.val t).2.1 + Real.tan (polygonStepSize n / 2)) +
          max 0 (2 * Real.tan (polygonStepSize n / 2) -
            (surfaceAreaMeasure P.val.val {(t : Real.Angle)}).toReal) := by
      conv_lhs => rw [hXeq]
      refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq ?_
      exact ENNReal.toReal_ofReal (by positivity)
    have hmagic : magicFunctions.1 (Real.toNNReal (tangentArmLengths P.val t).2.1) =
        max |(tangentArmLengths P.val t).2.1 - 1|
          ((|(tangentArmLengths P.val t).2.1 - 1| + 1) / 2) := by
      simp only [magicFunctions, Real.coe_toNNReal _ hgp0]
    rw [hatom]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← hstoReal, hmagic]
    refine magicBound_of_le hδpos ?_ ?_ hTpos ?_ hcpos hgp5 hgm0 hgle hsum
    · linarith [Real.pi_lt_d2]
    · exact Real.tan_le_self_add_cube hδpos.le (by linarith [Real.pi_le_four])
    · exact Real.tan_le_self_add_cube (by linarith) (by linarith [Real.pi_le_four])

section Domination

open Filter Set
open scoped Topology

/-! ### The magic density -/

private theorem magicDensity_eq (x : ℝ) :
    magicDensity x = max |max x 0 - 1| ((|max x 0 - 1| + 1) / 2) := by
  simp [magicDensity, magicFunctions]

/-- The magic function `k₀` is nonnegative. -/
theorem magicDensity_nonneg (x : ℝ) : 0 ≤ magicDensity x := by
  rw [magicDensity_eq]
  exact (abs_nonneg _).trans (le_max_left _ _)

private theorem continuous_magicDensity : Continuous magicDensity := by
  unfold magicDensity magicFunctions
  fun_prop

/-- The magic function `k₀` is `1`-Lipschitz. -/
private theorem abs_magicDensity_sub_le (x y : ℝ) :
    |magicDensity x - magicDensity y| ≤ |x - y| := by
  rw [magicDensity_eq, magicDensity_eq]
  have hxy : |max x 0 - max y 0| ≤ |x - y| := by
    calc
      |max x 0 - max y 0| ≤ max |x - y| |(0 : ℝ) - 0| :=
        abs_max_sub_max_le_max x 0 y 0
      _ = |x - y| := by simp
  have habs : abs (|max x 0 - 1| - |max y 0 - 1|) ≤ |x - y| := by
    calc
      abs (|max x 0 - 1| - |max y 0 - 1|) ≤
          |(max x 0 - 1) - (max y 0 - 1)| := abs_abs_sub_abs_le_abs_sub _ _
      _ = |max x 0 - max y 0| := by ring_nf
      _ ≤ |x - y| := hxy
  have hhalf :
      |((|max x 0 - 1| + 1) / 2) - ((|max y 0 - 1| + 1) / 2)| ≤ |x - y| := by
    rw [show ((|max x 0 - 1| + 1) / 2) - ((|max y 0 - 1| + 1) / 2) =
      (|max x 0 - 1| - |max y 0 - 1|) / 2 by ring, abs_div]
    norm_num
    linarith [abs_nonneg (|max x 0 - 1| - |max y 0 - 1|)]
  calc
    |max |max x 0 - 1| ((|max x 0 - 1| + 1) / 2) -
        max |max y 0 - 1| ((|max y 0 - 1| + 1) / 2)| ≤
        max (abs (|max x 0 - 1| - |max y 0 - 1|))
          |((|max x 0 - 1| + 1) / 2) - ((|max y 0 - 1| + 1) / 2)| :=
      abs_max_sub_max_le_max _ _ _ _
    _ ≤ |x - y| := max_le habs hhalf

/-- The magic function `k₀` grows at most linearly: `k₀ x ≤ |x| + 1`. -/
theorem magicDensity_le_abs_add_one (x : ℝ) : magicDensity x ≤ |x| + 1 := by
  have hzero : magicDensity 0 = 1 := by norm_num [magicDensity, magicFunctions]
  have h := abs_magicDensity_sub_le x 0
  rw [hzero, sub_zero] at h
  linarith [le_abs_self (magicDensity x - 1)]

/-! ### Integrability of the magic density -/

/-- The magic density of the positive tangent arm length is almost everywhere strongly
measurable on the rotation interval. -/
theorem aestronglyMeasurable_magicDensity_tangentArm_fst (C : RightAngleCapSpace) :
    AEStronglyMeasurable (fun t ↦ magicDensity (tangentArmLengths C t).2.1)
      (volume.restrict (Ioc 0 (Real.pi / 2))) :=
  continuous_magicDensity.comp_aestronglyMeasurable (aestronglyMeasurable_tangentArm_fst C)

/-- The magic density of the positive tangent arm length is integrable on the rotation
interval. -/
private theorem intervalIntegrable_magicDensity_tangentArm_fst (C : RightAngleCapSpace) :
    IntervalIntegrable (fun t ↦ magicDensity (tangentArmLengths C t).2.1)
      volume 0 (Real.pi / 2) := by
  have hdensity' : AEStronglyMeasurable
      (fun t ↦ magicDensity (tangentArmLengths C t).2.1)
      (volume.restrict (uIoc 0 (Real.pi / 2))) := by
    simpa only [uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using
      aestronglyMeasurable_magicDensity_tangentArm_fst C
  have harmInt := intervalIntegrable_tangentArm_fst C
  apply (harmInt.norm.add (intervalIntegrable_const (c := (1 : ℝ)))).mono_fun hdensity'
  filter_upwards [] with t
  change |magicDensity (tangentArmLengths C t).2.1| ≤
    abs (|(tangentArmLengths C t).2.1| + 1)
  rw [abs_of_nonneg (magicDensity_nonneg _),
    abs_of_nonneg (add_nonneg (abs_nonneg (tangentArmLengths C t).2.1) zero_le_one)]
  exact magicDensity_le_abs_add_one _

private theorem integrableOn_magicDensity_tangentArm_fst (C : RightAngleCapSpace)
    {S : Set ℝ} (hS : S ⊆ Icc (0 : ℝ) (Real.pi / 2)) :
    IntegrableOn (fun t ↦ magicDensity (tangentArmLengths C t).2.1) S volume := by
  have hIoc := (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by positivity : (0 : ℝ) ≤ Real.pi / 2)).1
      (intervalIntegrable_magicDensity_tangentArm_fst C)
  have hIcc : IntegrableOn (fun t ↦ magicDensity (tangentArmLengths C t).2.1)
      (Icc (0 : ℝ) (Real.pi / 2)) volume := by
    rwa [IntegrableOn, Measure.restrict_congr_set Ioc_ae_eq_Icc] at hIoc
  exact hIcc.mono_set hS

/-! ### The density measure of a cap -/

/-- The measure `k₀(g⁺_K(t)) dt` on the rotation interval. -/
private def armDensityMeasure (C : RightAngleCapSpace) : Measure ℝ :=
  (volume.restrict (Ioc 0 (Real.pi / 2))).withDensity
    (fun t ↦ ENNReal.ofReal (magicDensity (tangentArmLengths C t).2.1))

private theorem armDensityMeasure_apply (C : RightAngleCapSpace) {S : Set ℝ}
    (hS : MeasurableSet S) :
    armDensityMeasure C S = ∫⁻ t in S ∩ Ioc 0 (Real.pi / 2),
      ENNReal.ofReal (magicDensity (tangentArmLengths C t).2.1) := by
  rw [armDensityMeasure, withDensity_apply _ hS, Measure.restrict_restrict hS]

private theorem lintegral_magicDensity_eq_ofReal (C : RightAngleCapSpace) {S : Set ℝ}
    (hS : S ⊆ Icc (0 : ℝ) (Real.pi / 2)) :
    ∫⁻ t in S, ENNReal.ofReal (magicDensity (tangentArmLengths C t).2.1) =
      ENNReal.ofReal (∫ t in S, magicDensity (tangentArmLengths C t).2.1) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_magicDensity_tangentArm_fst C hS)
    (Filter.Eventually.of_forall fun t ↦ magicDensity_nonneg _)]

private theorem armDensityMeasure_ne_top (C : RightAngleCapSpace) :
    armDensityMeasure C Set.univ ≠ ⊤ := by
  rw [armDensityMeasure_apply C MeasurableSet.univ, Set.univ_inter,
    lintegral_magicDensity_eq_ofReal C Ioc_subset_Icc_self]
  exact ENNReal.ofReal_ne_top

private theorem armDensityMeasure_eq_ofReal_integral (C : RightAngleCapSpace) {S : Set ℝ}
    (hSm : MeasurableSet S) (hS : S ⊆ Ico (0 : ℝ) (Real.pi / 2)) :
    armDensityMeasure C S =
      ENNReal.ofReal (∫ t in S, magicDensity (tangentArmLengths C t).2.1) := by
  have hnull : S ∩ Ioc 0 (Real.pi / 2) =ᵐ[volume] S := by
    have hsub : S \ (S ∩ Ioc 0 (Real.pi / 2)) ⊆ {0} := by
      intro x hx
      have hxS := hx.1
      have hx2 : x ∉ Ioc 0 (Real.pi / 2) := fun h ↦ hx.2 ⟨hxS, h⟩
      have hxIco := hS hxS
      have : x = 0 := by
        by_contra hne
        exact hx2 ⟨lt_of_le_of_ne hxIco.1 (Ne.symm hne), hxIco.2.le⟩
      simp [this]
    refine (Filter.EventuallyEq.symm ?_)
    refine (ae_eq_set.mpr ⟨?_, ?_⟩)
    · exact measure_mono_null hsub (measure_singleton 0)
    · simp [Set.sdiff_eq_empty.2 Set.inter_subset_left]
  rw [armDensityMeasure_apply C hSm, setLIntegral_congr hnull,
    lintegral_magicDensity_eq_ofReal C (hS.trans Ico_subset_Icc_self)]

/-- Comparing two cap densities costs at most the `L¹` distance of their arm lengths. -/
private theorem armDensityMeasure_le_add_l1 (C D : RightAngleCapSpace) {S : Set ℝ}
    (hS : MeasurableSet S) :
    armDensityMeasure C S ≤ armDensityMeasure D S +
      ENNReal.ofReal (∫ t in (0 : ℝ)..(Real.pi / 2),
        |magicDensity (tangentArmLengths C t).2.1 -
          magicDensity (tangentArmLengths D t).2.1|) := by
  have hT : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hdiff : IntervalIntegrable (fun t ↦ |magicDensity (tangentArmLengths C t).2.1 -
      magicDensity (tangentArmLengths D t).2.1|) volume 0 (Real.pi / 2) := by
    simpa only [Real.norm_eq_abs] using
      ((intervalIntegrable_magicDensity_tangentArm_fst C).sub
        (intervalIntegrable_magicDensity_tangentArm_fst D)).norm
  have hdiffIoc := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hdiff
  have hmeasD : AEMeasurable
      (fun t ↦ ENNReal.ofReal (magicDensity (tangentArmLengths D t).2.1))
      (volume.restrict (S ∩ Ioc 0 (Real.pi / 2))) := by
    refine (ENNReal.measurable_ofReal.comp_aemeasurable ?_)
    exact ((continuous_magicDensity.comp_aestronglyMeasurable
      (aestronglyMeasurable_tangentArm_fst D)).aemeasurable).mono_measure
        (Measure.restrict_mono Set.inter_subset_right le_rfl)
  rw [armDensityMeasure_apply C hS, armDensityMeasure_apply D hS]
  calc
    ∫⁻ t in S ∩ Ioc 0 (Real.pi / 2),
        ENNReal.ofReal (magicDensity (tangentArmLengths C t).2.1) ≤
        ∫⁻ t in S ∩ Ioc 0 (Real.pi / 2),
          (ENNReal.ofReal (magicDensity (tangentArmLengths D t).2.1) +
            ENNReal.ofReal |magicDensity (tangentArmLengths C t).2.1 -
              magicDensity (tangentArmLengths D t).2.1|) := by
      refine lintegral_mono fun t ↦ ?_
      rw [← ENNReal.ofReal_add (magicDensity_nonneg _) (abs_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      linarith [le_abs_self (magicDensity (tangentArmLengths C t).2.1 -
        magicDensity (tangentArmLengths D t).2.1)]
    _ = (∫⁻ t in S ∩ Ioc 0 (Real.pi / 2),
          ENNReal.ofReal (magicDensity (tangentArmLengths D t).2.1)) +
        ∫⁻ t in S ∩ Ioc 0 (Real.pi / 2),
          ENNReal.ofReal |magicDensity (tangentArmLengths C t).2.1 -
            magicDensity (tangentArmLengths D t).2.1| := lintegral_add_left' hmeasD _
    _ ≤ (∫⁻ t in S ∩ Ioc 0 (Real.pi / 2),
          ENNReal.ofReal (magicDensity (tangentArmLengths D t).2.1)) +
        ∫⁻ t in Ioc 0 (Real.pi / 2),
          ENNReal.ofReal |magicDensity (tangentArmLengths C t).2.1 -
            magicDensity (tangentArmLengths D t).2.1| := by
      gcongr
      exact Set.inter_subset_right
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hdiffIoc
        (Filter.Eventually.of_forall fun t ↦ abs_nonneg _),
        intervalIntegral.integral_of_le hT]

/-! ### Surface measure support of a right-angle polygon cap -/

/-- Angular images of Borel subsets of the half-open rotation interval are Borel. -/
private theorem measurableSet_coe_image_of_subset_Ico {E : Set ℝ} (hE : MeasurableSet E)
    (hET : E ⊆ Ico (0 : ℝ) (Real.pi / 2)) :
    MeasurableSet ((fun t : ℝ ↦ (t : Real.Angle)) '' E) :=
  Real.Angle.measurableSet_image_of_subset_Ioc (a := -Real.pi) (b := Real.pi)
    (by linarith [Real.pi_pos]) hE fun t ht ↦
      ⟨by linarith [Real.pi_pos, (hET ht).1],
        (hET ht).2.le.trans (half_le_self Real.pi_pos.le)⟩

private theorem rightAngle_properEdgeNormal_real (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) {s : ℝ} (hs : s ∈ Ioc (-Real.pi) Real.pi)
    (hedge : (edgeVertices K.val.val (s : Real.Angle)).1 ≠
      (edgeVertices K.val.val (s : Real.Angle)).2) :
    s ∈ angleDomain (rightAngleSet n hn) ∨ s = -(Real.pi / 2) := by
  have hpi := Real.pi_pos
  have h := K.properEdgeNormal_mem_allowed (s : Real.Angle) hedge
  rw [rightAngle_polygon_normals_eq n hn] at h
  obtain ⟨r, hr, hrs⟩ := h
  rcases hr with hr | rfl
  · left
    have hrb := angleDomain_subset_Ioo (rightAngleSet n hn) hr
    have hsr : s = r := Real.Angle.injOn_coe_Ioc (a := -Real.pi) (b := Real.pi)
      (by linarith) hs ⟨by linarith [hrb.1], hrb.2.le⟩ hrs.symm
    exact hsr ▸ hr
  · right
    have hrs' : ((3 * Real.pi / 2 : ℝ) : Real.Angle) = ((s : ℝ) : Real.Angle) := hrs
    refine Real.Angle.injOn_coe_Ioc (a := -Real.pi) (b := Real.pi) (by linarith) hs
      ⟨by linarith, by linarith⟩ ?_
    show ((s : ℝ) : Real.Angle) = ((-(Real.pi / 2) : ℝ) : Real.Angle)
    rw [← hrs', Real.Angle.angle_eq_iff_two_pi_dvd_sub]
    exact ⟨1, by push_cast; ring⟩

private theorem rightAngle_properEdgeNormal_mem_directions (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) (Real.pi / 2))
    (hedge : (edgeVertices K.val.val (s : Real.Angle)).1 ≠
      (edgeVertices K.val.val (s : Real.Angle)).2) :
    s ∈ (rightAngleSet n hn).directions := by
  have hpi := Real.pi_pos
  have hsIoc : s ∈ Ioc (-Real.pi) Real.pi :=
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  rcases rightAngle_properEdgeNormal_real n hn K hsIoc hedge with hdom | hneg
  · rcases hdom with (hd | ⟨r, hr, hrs⟩) | hd
    · exact hd
    · exact absurd hs.2 (by
        have hr0 := ((rightAngleSet n hn).interior r hr).1
        rw [← hrs]
        push Not
        linarith)
    · exfalso
      have hangle : (rightAngleSet n hn).angle = Real.pi / 2 := rfl
      simp only [hangle, Set.mem_insert_iff, Set.mem_singleton_iff] at hd
      rcases hd with hd | hd <;> (rw [hd] at hs; linarith [hs.2])
  · exfalso
    rw [hneg] at hs
    linarith [hs.1]

private theorem rightAngle_edgeVertices_eq_of_mem_Ioo_neg (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) {s : ℝ}
    (hs : s ∈ Ioo (-(Real.pi / 2)) 0) :
    (edgeVertices K.val.val (s : Real.Angle)).1 =
      (edgeVertices K.val.val (s : Real.Angle)).2 := by
  have hpi := Real.pi_pos
  by_contra hne
  have hsIoc : s ∈ Ioc (-Real.pi) Real.pi :=
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  rcases rightAngle_properEdgeNormal_real n hn K hsIoc hne with hdom | hneg
  · have hrb := angleDomain_subset_Ioo (rightAngleSet n hn) hdom
    linarith [hrb.1, hs.2]
  · rw [hneg] at hs
    linarith [hs.1]

private theorem surfaceAreaMeasure_rightAngle_compl_grid_eq_zero (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) :
    surfaceAreaMeasure K.val.val
      (((fun s : ℝ ↦ (s : Real.Angle)) '' Ico (0 : ℝ) (Real.pi / 2)) \
        ((fun s : ℝ ↦ (s : Real.Angle)) ''
          ({0} ∪ ((rightAngleSet n hn).directions : Set ℝ)))) = 0 := by
  apply measure_mono_null _ K.surfaceAreaMeasure_compl_properEdgeNormals_eq_zero
  rintro u ⟨⟨s, hs, rfl⟩, hnot⟩
  by_contra hne
  exact hnot ⟨s, Or.inr (rightAngle_properEdgeNormal_mem_directions n hn K hs hne), rfl⟩

private theorem surfaceAreaMeasure_rightAngle_Ioo_neg_eq_zero (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) :
    surfaceAreaMeasure K.val.val
      ((fun s : ℝ ↦ (s : Real.Angle)) '' Ioo (-(Real.pi / 2)) 0) = 0 := by
  apply measure_mono_null _ K.surfaceAreaMeasure_compl_properEdgeNormals_eq_zero
  rintro u ⟨s, hs, rfl⟩
  exact rightAngle_edgeVertices_eq_of_mem_Ioo_neg n hn K hs

/-! ### Discrete cell bounds -/

private theorem maximumPolygonCap_arm_cell_abs_le (n : ℕ) (hn : 2 ≤ n)
    (K : RightAngleCapSpace) (hK : IsMaximumPolygonCapSteps n K) (t u : ℝ)
    (ht : t = 0 ∨ t ∈ (rightAngleSet n hn).directions)
    (hu : u ∈ Ioo t (t + polygonStepSize n)) :
    |(tangentArmLengths K u).2.1 - (tangentArmLengths K t).2.1| ≤
      5 * polygonStepSize n := by
  obtain ⟨hcell, hdrop⟩ := maximumPolygonCap_arm_cell n hn K hK t ht
  have hu' := hcell u hu
  have hlower :
      (tangentArmLengths K t).2.1 - 5 * polygonStepSize n ≤
        (tangentArmLengths K u).2.1 := by
    rw [hu'.2.1]
    linarith [hu'.2.2]
  rw [abs_le]
  constructor <;> linarith [hu'.1]

private theorem magicDensity_mul_le_integral_add_of_cell_bound
    (f : ℝ → ℝ) (t δ c : ℝ) (hδ : 0 ≤ δ)
    (hint : IntervalIntegrable (fun u ↦ magicDensity (f u)) volume t (t + δ))
    (hvar : ∀ᵐ u ∂volume.restrict (Icc t (t + δ)), |f u - f t| ≤ c) :
    magicDensity (f t) * δ ≤
      (∫ u in t..(t + δ), magicDensity (f u)) + c * δ := by
  have hp : ∀ᵐ u ∂volume.restrict (Icc t (t + δ)),
      magicDensity (f t) ≤ magicDensity (f u) + c := by
    filter_upwards [hvar] with u hu
    have hle : magicDensity (f t) - magicDensity (f u) ≤ c := by
      calc
        magicDensity (f t) - magicDensity (f u) ≤
            |magicDensity (f t) - magicDensity (f u)| := le_abs_self _
        _ ≤ |f t - f u| := abs_magicDensity_sub_le _ _
        _ = |f u - f t| := abs_sub_comm _ _
        _ ≤ c := hu
    linarith
  have hc : IntervalIntegrable (fun _ : ℝ ↦ c) volume t (t + δ) :=
    intervalIntegrable_const
  have hi := intervalIntegral.integral_mono_ae_restrict
    (show t ≤ t + δ by linarith)
    (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ ↦ magicDensity (f t)) volume t (t + δ))
    (hint.add hc) hp
  rw [intervalIntegral.integral_add hint hc, intervalIntegral.integral_const,
    intervalIntegral.integral_const] at hi
  simpa only [add_sub_cancel_left, smul_eq_mul, mul_comm] using hi

private theorem maximumPolygonCap_magicDensity_cell_bound
    (n : ℕ) (hn : 2 ≤ n) (K : RightAngleCapSpace)
    (hK : IsMaximumPolygonCapSteps n K) (t : ℝ)
    (ht : t = 0 ∨ t ∈ (rightAngleSet n hn).directions)
    (hint : IntervalIntegrable
      (fun u ↦ magicDensity (tangentArmLengths K u).2.1)
      volume t (t + polygonStepSize n)) :
    magicDensity (tangentArmLengths K t).2.1 * polygonStepSize n ≤
      (∫ u in t..(t + polygonStepSize n),
        magicDensity (tangentArmLengths K u).2.1) +
        5 * polygonStepSize n ^ 2 := by
  have haeIoo : ∀ᵐ u ∂volume.restrict
      (Icc t (t + polygonStepSize n)), u ∈ Ioo t (t + polygonStepSize n) := by
    rw [ae_iff]
    change (volume.restrict (Icc t (t + polygonStepSize n)))
      (Ioo t (t + polygonStepSize n))ᶜ = 0
    rw [Measure.restrict_apply measurableSet_Ioo.compl]
    have hsub : (Ioo t (t + polygonStepSize n))ᶜ ∩
        Icc t (t + polygonStepSize n) ⊆ {t, t + polygonStepSize n} := by
      intro x hx
      simp only [mem_inter_iff, mem_Icc, mem_compl_iff, mem_Ioo, not_and_or,
        not_lt, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with ⟨hxt | hux, htx, hxu⟩
      · exact Or.inl (le_antisymm hxt htx)
      · exact Or.inr (le_antisymm hxu hux)
    exact measure_mono_null hsub
      ((Set.finite_singleton (t + polygonStepSize n)).insert t |>.measure_zero volume)
  have hvar : ∀ᵐ u ∂volume.restrict (Icc t (t + polygonStepSize n)),
      |(tangentArmLengths K u).2.1 - (tangentArmLengths K t).2.1| ≤
        5 * polygonStepSize n := by
    filter_upwards [haeIoo] with u hu
    exact maximumPolygonCap_arm_cell_abs_le n hn K hK t u ht hu
  have hδ : 0 ≤ polygonStepSize n := by
    simp only [polygonStepSize]
    positivity
  have h := magicDensity_mul_le_integral_add_of_cell_bound
    (fun u ↦ (tangentArmLengths K u).2.1) t (polygonStepSize n)
      (5 * polygonStepSize n) hδ hint hvar
  nlinarith [sq_nonneg (polygonStepSize n)]

private theorem maximumPolygonCap_surfaceAtom_le_lintegral_cell
    (n : ℕ) (hn : 2 ≤ n) (K : RightAngleCapSpace)
    (hK : IsMaximumPolygonCapSteps n K) (t : ℝ)
    (ht : t = 0 ∨ t ∈ (rightAngleSet n hn).directions)
    (hmem : Icc t (t + polygonStepSize n) ⊆ Icc (0 : ℝ) (Real.pi / 2)) :
    surfaceAreaMeasure K.val {(t : Real.Angle)} ≤
      (∫⁻ u in Ioc t (t + polygonStepSize n),
        ENNReal.ofReal (magicDensity (tangentArmLengths K u).2.1)) +
      ENNReal.ofReal (13 * polygonStepSize n ^ 2) := by
  have hnR : (0 : ℝ) < n := by
    have : 0 < n := lt_of_lt_of_le zero_lt_two hn
    exact_mod_cast this
  have hδ : 0 < polygonStepSize n :=
    div_pos (by linarith [Real.pi_pos]) hnR
  have hle : t ≤ t + polygonStepSize n := by linarith
  have hint : IntervalIntegrable
      (fun u ↦ magicDensity (tangentArmLengths K u).2.1) volume t (t + polygonStepSize n) := by
    apply (intervalIntegrable_magicDensity_tangentArm_fst K).mono_set
    rw [uIcc_of_le hle, uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    exact hmem
  have hcell := maximumPolygonCap_magicDensity_cell_bound n hn K hK t ht hint
  have hnonneg : 0 ≤ ∫ u in t..(t + polygonStepSize n),
      magicDensity (tangentArmLengths K u).2.1 :=
    intervalIntegral.integral_nonneg hle fun u _ ↦ magicDensity_nonneg _
  have hlint : ENNReal.ofReal (∫ u in t..(t + polygonStepSize n),
        magicDensity (tangentArmLengths K u).2.1) =
      ∫⁻ u in Ioc t (t + polygonStepSize n),
        ENNReal.ofReal (magicDensity (tangentArmLengths K u).2.1) := by
    rw [intervalIntegral.integral_of_le hle]
    exact ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1 hint)
      (Filter.Eventually.of_forall fun u ↦ magicDensity_nonneg _)
  calc
    surfaceAreaMeasure K.val {(t : Real.Angle)} ≤
        ENNReal.ofReal (magicFunctions.1 (Real.toNNReal (tangentArmLengths K t).2.1) *
          polygonStepSize n + 8 * polygonStepSize n ^ 2) :=
      maximumPolygonCap_surfaceAtom_bound n hn K hK t ht
    _ ≤ ENNReal.ofReal ((∫ u in t..(t + polygonStepSize n),
          magicDensity (tangentArmLengths K u).2.1) + 13 * polygonStepSize n ^ 2) := by
      refine ENNReal.ofReal_le_ofReal ?_
      change magicDensity (tangentArmLengths K t).2.1 * polygonStepSize n +
        8 * polygonStepSize n ^ 2 ≤ _
      linarith
    _ = _ := by rw [ENNReal.ofReal_add hnonneg (by positivity), hlint]

/-! ### The per-level grid bound -/

private theorem maximumPolygonCap_surface_image_le_thickening
    (n : ℕ) (hn : 2 ≤ n) (K : RightAngleCapSpace) (hK : IsMaximumPolygonCapSteps n K)
    (S : Set ℝ) (hSm : MeasurableSet S) (hST : S ⊆ Ico (0 : ℝ) (Real.pi / 2))
    {ε : ℝ} (hε : polygonStepSize n < ε) :
    surfaceAreaMeasure K.val ((fun t : ℝ ↦ (t : Real.Angle)) '' S) ≤
      armDensityMeasure K (Metric.thickening ε S) +
        ENNReal.ofReal (13 * (Real.pi / 2) * polygonStepSize n) := by
  classical
  have hpi := Real.pi_pos
  have hK0 := hK
  obtain ⟨hn', hdy, P, hPK, hmax⟩ := hK
  have hnR : (0 : ℝ) < n := by
    have : 0 < n := lt_of_lt_of_le zero_lt_two hn
    exact_mod_cast this
  have hδpos : 0 < polygonStepSize n := div_pos (by linarith) hnR
  have hnδ : (n : ℝ) * polygonStepSize n = Real.pi / 2 := by
    rw [polygonStepSize]
    field_simp
  have hinj : Set.InjOn (fun t : ℝ ↦ (t : Real.Angle)) (Ico (0 : ℝ) (Real.pi / 2)) := by
    apply (Real.Angle.injOn_coe_Ioc (a := -Real.pi) (b := Real.pi) (by linarith)).mono
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hgridmem : ∀ i : ℕ, i < n →
      (i : ℝ) * polygonStepSize n ∈ Ico (0 : ℝ) (Real.pi / 2) := by
    intro i hi
    have hin : (i : ℝ) < n := by exact_mod_cast hi
    refine ⟨mul_nonneg (Nat.cast_nonneg i) hδpos.le, ?_⟩
    calc (i : ℝ) * polygonStepSize n < (n : ℝ) * polygonStepSize n := by
          exact mul_lt_mul_of_pos_right hin hδpos
      _ = Real.pi / 2 := hnδ
  have hcellIcc : ∀ i : ℕ, i < n →
      Icc ((i : ℝ) * polygonStepSize n) ((i : ℝ) * polygonStepSize n + polygonStepSize n) ⊆
        Icc (0 : ℝ) (Real.pi / 2) := by
    intro i hi x hx
    have hsucc : ((i : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hi
    refine ⟨le_trans (mul_nonneg (Nat.cast_nonneg i) hδpos.le) hx.1, hx.2.trans ?_⟩
    calc (i : ℝ) * polygonStepSize n + polygonStepSize n =
          ((i : ℝ) + 1) * polygonStepSize n := by ring
      _ ≤ (n : ℝ) * polygonStepSize n := mul_le_mul_of_nonneg_right hsucc hδpos.le
      _ = Real.pi / 2 := hnδ
  have hgriddir : ∀ i : ℕ, i < n →
      (i : ℝ) * polygonStepSize n = 0 ∨
        (i : ℝ) * polygonStepSize n ∈ (rightAngleSet n hn').directions := by
    intro i hi
    by_cases hi0 : i = 0
    · exact Or.inl (by simp [hi0])
    · exact Or.inr ((mem_rightAngleSet_directions_iff n hn' _).2
        ⟨i, Finset.mem_Ioo.2 ⟨Nat.pos_of_ne_zero hi0, hi⟩, rfl⟩)
  -- the surface measure restricted to the arc of interest
  have hSimage : MeasurableSet ((fun t : ℝ ↦ (t : Real.Angle)) '' S) :=
    measurableSet_coe_image_of_subset_Ico hSm hST
  have hμS : ((surfaceAreaMeasure K.val).restrict
        ((fun t : ℝ ↦ (t : Real.Angle)) '' Ico (0 : ℝ) (Real.pi / 2)))
        ((fun t : ℝ ↦ (t : Real.Angle)) '' S) =
      surfaceAreaMeasure K.val ((fun t : ℝ ↦ (t : Real.Angle)) '' S) := by
    rw [Measure.restrict_apply hSimage,
      Set.inter_eq_left.2 (Set.image_mono hST)]
  -- the atom decomposition over the grid
  have hbound := measure_le_sum_of_measure_compl_image_eq_zero
    ((surfaceAreaMeasure K.val).restrict
      ((fun t : ℝ ↦ (t : Real.Angle)) '' Ico (0 : ℝ) (Real.pi / 2)))
    (Finset.range n)
    ((Finset.range n).filter (fun i : ℕ ↦ ((i : ℝ) * polygonStepSize n) ∈ S))
    (fun i : ℕ ↦ (((i : ℝ) * polygonStepSize n : ℝ) : Real.Angle))
    (fun i : ℕ ↦ (∫⁻ u in Ioc ((i : ℝ) * polygonStepSize n)
        ((i : ℝ) * polygonStepSize n + polygonStepSize n),
        ENNReal.ofReal (magicDensity (tangentArmLengths K u).2.1)) +
      ENNReal.ofReal (13 * polygonStepSize n ^ 2))
    ?_ ?_ ?_ ((fun t : ℝ ↦ (t : Real.Angle)) '' S) hSimage ?_
  · rw [hμS] at hbound
    refine hbound.trans ?_
    rw [Finset.sum_add_distrib]
    have hdisj : ((Finset.range n).filter
          (fun i : ℕ ↦ ((i : ℝ) * polygonStepSize n) ∈ S) : Set ℕ).PairwiseDisjoint
        (fun i : ℕ ↦ Ioc ((i : ℝ) * polygonStepSize n)
          ((i : ℝ) * polygonStepSize n + polygonStepSize n)) := by
      intro i _ j _ hij
      simp only [Function.onFun, Set.disjoint_left]
      intro x hx hx'
      rcases lt_or_gt_of_ne hij with h | h
      · have hle : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
        have : (i : ℝ) * polygonStepSize n + polygonStepSize n ≤
            (j : ℝ) * polygonStepSize n := by
          nlinarith [hδpos]
        linarith [hx.2, hx'.1]
      · have hle : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
        have : (j : ℝ) * polygonStepSize n + polygonStepSize n ≤
            (i : ℝ) * polygonStepSize n := by
          nlinarith [hδpos]
        linarith [hx.1, hx'.2]
    have hsumlint : ∑ i ∈ (Finset.range n).filter
          (fun i : ℕ ↦ ((i : ℝ) * polygonStepSize n) ∈ S),
          (∫⁻ u in Ioc ((i : ℝ) * polygonStepSize n)
            ((i : ℝ) * polygonStepSize n + polygonStepSize n),
            ENNReal.ofReal (magicDensity (tangentArmLengths K u).2.1)) =
        ∫⁻ u in ⋃ i ∈ (Finset.range n).filter
          (fun i : ℕ ↦ ((i : ℝ) * polygonStepSize n) ∈ S),
            Ioc ((i : ℝ) * polygonStepSize n)
              ((i : ℝ) * polygonStepSize n + polygonStepSize n),
          ENNReal.ofReal (magicDensity (tangentArmLengths K u).2.1) :=
      (lintegral_biUnion_finset hdisj (fun i _ ↦ measurableSet_Ioc) _).symm
    have hsubset : (⋃ i ∈ (Finset.range n).filter
          (fun i : ℕ ↦ ((i : ℝ) * polygonStepSize n) ∈ S),
            Ioc ((i : ℝ) * polygonStepSize n)
              ((i : ℝ) * polygonStepSize n + polygonStepSize n)) ⊆
        Metric.thickening ε S ∩ Ioc 0 (Real.pi / 2) := by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨hiR, hiS⟩ := Finset.mem_filter.1 hi
      have hi' : i < n := Finset.mem_range.1 hiR
      refine ⟨?_, ?_⟩
      · refine Metric.mem_thickening_iff.2 ⟨(i : ℝ) * polygonStepSize n, hiS, ?_⟩
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hxi.1])]
        linarith [hxi.2]
      · exact ⟨lt_of_le_of_lt (hgridmem i hi').1 hxi.1,
          (hcellIcc i hi' ⟨hxi.1.le, hxi.2⟩).2⟩
    have hcard : (((Finset.range n).filter
          (fun i : ℕ ↦ ((i : ℝ) * polygonStepSize n) ∈ S)).card : ENNReal) ≤
        (n : ENNReal) := by
      have := Finset.card_filter_le (Finset.range n)
        (fun i : ℕ ↦ ((i : ℝ) * polygonStepSize n) ∈ S)
      rw [Finset.card_range] at this
      exact_mod_cast this
    have hconst : ∑ _i ∈ (Finset.range n).filter
          (fun i : ℕ ↦ ((i : ℝ) * polygonStepSize n) ∈ S),
          ENNReal.ofReal (13 * polygonStepSize n ^ 2) ≤
        ENNReal.ofReal (13 * (Real.pi / 2) * polygonStepSize n) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      calc
        (((Finset.range n).filter
            (fun i : ℕ ↦ ((i : ℝ) * polygonStepSize n) ∈ S)).card : ENNReal) *
              ENNReal.ofReal (13 * polygonStepSize n ^ 2) ≤
            (n : ENNReal) * ENNReal.ofReal (13 * polygonStepSize n ^ 2) := by
          gcongr
        _ = ENNReal.ofReal (13 * (Real.pi / 2) * polygonStepSize n) := by
          rw [show ((n : ENNReal)) = ENNReal.ofReal ((n : ℝ)) by
            simp [ENNReal.ofReal_natCast],
            ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
          congr 1
          nlinarith [hnδ]
    refine add_le_add ?_ hconst
    rw [hsumlint, armDensityMeasure_apply K Metric.isOpen_thickening.measurableSet]
    exact lintegral_mono_set hsubset
  · -- injectivity of the grid map
    intro i hi j hj hij
    have hi' : i < n := Finset.mem_range.1 (Finset.mem_coe.1 hi)
    have hj' : j < n := Finset.mem_range.1 (Finset.mem_coe.1 hj)
    have heq : (i : ℝ) * polygonStepSize n = (j : ℝ) * polygonStepSize n :=
      hinj (hgridmem i hi') (hgridmem j hj') hij
    have hij' : (i : ℝ) = (j : ℝ) := mul_right_cancel₀ hδpos.ne' heq
    exact_mod_cast hij'
  · -- the surface measure is carried by the grid
    have himagegrid :
        (fun i : ℕ ↦ (((i : ℝ) * polygonStepSize n : ℝ) : Real.Angle)) ''
            (Finset.range n : Set ℕ) =
          (fun s : ℝ ↦ (s : Real.Angle)) ''
            ({0} ∪ ((rightAngleSet n hn').directions : Set ℝ)) := by
      ext u
      constructor
      · rintro ⟨i, hi, rfl⟩
        have hi' : i < n := Finset.mem_range.1 (Finset.mem_coe.1 hi)
        rcases hgriddir i hi' with h0 | hdir
        · exact ⟨(i : ℝ) * polygonStepSize n, Or.inl h0, rfl⟩
        · exact ⟨(i : ℝ) * polygonStepSize n, Or.inr hdir, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        rcases hs with hs | hs
        · refine ⟨0, Finset.mem_coe.2 (Finset.mem_range.2 (by omega)), ?_⟩
          simp only [Set.mem_singleton_iff] at hs
          simp [hs]
        · obtain ⟨i, hi, rfl⟩ := (mem_rightAngleSet_directions_iff n hn' s).1 hs
          exact ⟨i, Finset.mem_coe.2 (Finset.mem_range.2 (Finset.mem_Ioo.1 hi).2), rfl⟩
    rw [himagegrid, Measure.restrict_apply
      (((Set.finite_singleton (0 : ℝ)).union
        (rightAngleSet n hn').directions.finite_toSet).image
          (fun s : ℝ ↦ (s : Real.Angle))).measurableSet.compl,
      Set.inter_comm]
    have hsupp := surfaceAreaMeasure_rightAngle_compl_grid_eq_zero n hn' P
    rw [hPK] at hsupp
    exact hsupp
  · -- the atom bound at each grid point
    intro i hi
    have hi' : i < n := Finset.mem_range.1 hi
    refine le_trans (Measure.restrict_apply_le _ _) ?_
    exact maximumPolygonCap_surfaceAtom_le_lintegral_cell n hn' K hK0
      ((i : ℝ) * polygonStepSize n) (hgriddir i hi') (hcellIcc i hi')
  · -- only grid points inside `S` contribute
    intro i hi hmem
    have hi' : i < n := Finset.mem_range.1 hi
    obtain ⟨s, hsS, hseq⟩ := hmem
    have hs : s = (i : ℝ) * polygonStepSize n :=
      hinj (hST hsS) (hgridmem i hi') hseq
    exact Finset.mem_filter.2 ⟨hi, hs ▸ hsS⟩

/-! ### Passing to the limit -/

private theorem tendsto_integral_abs_magicDensity_sub_of_dominated
    (f g : ℕ → ℝ → ℝ) (hfi : ∀ i, IntervalIntegrable (f i) volume 0 (Real.pi / 2))
    (hgi : ∀ i, IntervalIntegrable (g i) volume 0 (Real.pi / 2))
    (hlim : Tendsto (fun i ↦ ∫ t in (0 : ℝ)..(Real.pi / 2), |f i t - g i t|)
      atTop (𝓝 0)) :
    Tendsto (fun i ↦ ∫ t in (0 : ℝ)..(Real.pi / 2),
      |magicDensity (f i t) - magicDensity (g i t)|) atTop (𝓝 0) := by
  have hsource (i : ℕ) :
      IntervalIntegrable (fun t ↦ |f i t - g i t|) volume 0 (Real.pi / 2) :=
    ((hfi i).sub (hgi i)).norm
  have htarget (i : ℕ) : IntervalIntegrable
      (fun t ↦ |magicDensity (f i t) - magicDensity (g i t)|)
      volume 0 (Real.pi / 2) := by
    apply (hsource i).mono_fun
    · rw [uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
      convert ((continuous_magicDensity.comp_aestronglyMeasurable
        (hfi i).aestronglyMeasurable).sub
        (continuous_magicDensity.comp_aestronglyMeasurable
          (hgi i).aestronglyMeasurable)).norm using 1
    · filter_upwards [] with t
      simpa only [Real.norm_eq_abs, abs_abs] using abs_magicDensity_sub_le (f i t) (g i t)
  apply squeeze_zero
  · intro i
    exact intervalIntegral.integral_nonneg (by positivity) (fun _ _ ↦ abs_nonneg _)
  · intro i
    apply intervalIntegral.integral_mono_on (by positivity) (htarget i) (hsource i)
    intro t _
    exact abs_magicDensity_sub_le (f i t) (g i t)
  · exact hlim

private theorem IsBalancedMaximumCap.approximatingPolygonCaps
    (K : RightAngleCapSpace) (hK : IsBalancedMaximumCap K) :
    ∃ (n : ℕ → ℕ) (P : ℕ → RightAngleCapSpace), StrictMono n ∧
      (∀ i, IsMaximumPolygonCapSteps (n i) (P i)) ∧
      Tendsto (fun i ↦ Metric.hausdorffDist ((P i).val : Set Point) (K.val : Set Point))
        atTop (𝓝 0) ∧
      Tendsto (fun i ↦ ∫ t in (0 : ℝ)..(Real.pi / 2),
        |magicDensity (tangentArmLengths (P i) t).2.1 -
          magicDensity (tangentArmLengths K t).2.1|) atTop (𝓝 0) := by
  obtain ⟨n, hn, hmono, hdyadic, Q, hQmax, hQlim⟩ := hK
  refine ⟨n, fun i ↦ (Q i).val, hmono, fun i ↦ ⟨hn i, hdyadic i, Q i, rfl, hQmax i⟩,
    hQlim, ?_⟩
  apply tendsto_integral_abs_magicDensity_sub_of_dominated
    (fun i t ↦ (tangentArmLengths ((Q i).val) t).2.1)
    (fun _ t ↦ (tangentArmLengths K t).2.1)
    (fun i ↦ intervalIntegrable_tangentArm_fst _)
    (fun i ↦ intervalIntegrable_tangentArm_fst K)
  apply polygonCap_arm_integral_limit (fun i ↦ (Q i).val) K
  · intro i
    exact ⟨rightAngleSet (n i) (hn i), Q i, rfl, rfl⟩
  · exact hQlim

/-- The limit of the discrete inequalities on a compact subset of the rotation interval. -/
private theorem balancedMaximumCap_surface_isCompact_le (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) {C : Set ℝ} (hC : IsCompact C)
    (hCT : C ⊆ Ico (0 : ℝ) (Real.pi / 2)) :
    surfaceAreaMeasure K.val ((fun t : ℝ ↦ (t : Real.Angle)) '' C) ≤
      armDensityMeasure K C := by
  have hpi := Real.pi_pos
  obtain ⟨n, P, hmono, hPmax, hPlim, hL1⟩ :=
    IsBalancedMaximumCap.approximatingPolygonCaps K hK
  set err : ℕ → ℝ := fun i ↦ ∫ t in (0 : ℝ)..(Real.pi / 2),
    |magicDensity (tangentArmLengths (P i) t).2.1 -
      magicDensity (tangentArmLengths K t).2.1| with herrdef
  have herr0 : ∀ i, 0 ≤ err i := fun i ↦
    intervalIntegral.integral_nonneg (by positivity) fun t _ ↦ abs_nonneg _
  have hδpos : ∀ i, 0 < polygonStepSize (n i) := by
    intro i
    obtain ⟨hn', _⟩ := hPmax i
    have hnR : (0 : ℝ) < n i := by
      have : 0 < n i := lt_of_lt_of_le zero_lt_two hn'
      exact_mod_cast this
    exact div_pos (by linarith) hnR
  have hδtend : Tendsto (fun i ↦ polygonStepSize (n i)) atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (Real.pi / 2)).comp
      hmono.tendsto_atTop
    simpa only [polygonStepSize, Function.comp_def] using h
  -- weak convergence of the surface measures
  let μs : ℕ → FiniteMeasure Real.Angle := fun i ↦
    ⟨surfaceAreaMeasure (P i).val, (surfaceAreaMeasure_face_union (P i).val).1⟩
  let μ : FiniteMeasure Real.Angle :=
    ⟨surfaceAreaMeasure K.val, (surfaceAreaMeasure_face_union K.val).1⟩
  have hweak : Tendsto μs atTop (𝓝 μ) := by
    apply MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro f
    exact surfaceAreaMeasure_weak_continuity (fun i ↦ (P i).val) K.val hPlim f f.continuous
  -- the estimate at every positive thickening radius
  have hkey : ∀ η : ℝ, 0 < η →
      surfaceAreaMeasure K.val ((fun t : ℝ ↦ (t : Real.Angle)) '' C) ≤
        armDensityMeasure K (Metric.thickening (2 * η) C) := by
    intro η hη
    set V := (Metric.thickening η C ∩ Ioo (-(Real.pi / 2)) (Real.pi / 2)) ∪
      Ioo (-(Real.pi / 2)) 0 with hVdef
    have hVopen : IsOpen V :=
      (Metric.isOpen_thickening.inter isOpen_Ioo).union isOpen_Ioo
    have hCV : C ⊆ V := by
      intro x hx
      exact Or.inl ⟨Metric.self_subset_thickening hη C hx,
        ⟨by linarith [(hCT hx).1], (hCT hx).2⟩⟩
    have hVsubIoo : V ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      rintro x (hx | hx)
      · exact hx.2
      · exact ⟨hx.1, by linarith [hx.2]⟩
    have hVsubThick : V ∩ Ico (0 : ℝ) (Real.pi / 2) ⊆ Metric.thickening η C := by
      rintro x ⟨hxV, hxI⟩
      rcases hxV with hx | hx
      · exact hx.1
      · exact absurd hxI.1 (by simpa using hx.2)
    have hVmeas : MeasurableSet (V ∩ Ico (0 : ℝ) (Real.pi / 2)) :=
      hVopen.measurableSet.inter measurableSet_Ico
    have hφVopen : IsOpen ((fun t : ℝ ↦ (t : Real.Angle)) '' V) :=
      QuotientAddGroup.isOpenMap_coe _ hVopen
    have hstep1 : surfaceAreaMeasure K.val ((fun t : ℝ ↦ (t : Real.Angle)) '' C) ≤
        Filter.liminf (fun i ↦ surfaceAreaMeasure (P i).val
          ((fun t : ℝ ↦ (t : Real.Angle)) '' V)) atTop := by
      refine le_trans (measure_mono (Set.image_mono hCV)) ?_
      exact FiniteMeasure.le_liminf_measure_open_of_tendsto (μ := μ) (μs := μs)
        hweak hφVopen
    have hev : ∀ᶠ i in atTop, surfaceAreaMeasure (P i).val
        ((fun t : ℝ ↦ (t : Real.Angle)) '' V) ≤
        armDensityMeasure K (Metric.thickening (2 * η) C) +
          ENNReal.ofReal (err i + 13 * (Real.pi / 2) * polygonStepSize (n i)) := by
      filter_upwards [hδtend.eventually (gt_mem_nhds (show (0 : ℝ) < η / 2 by positivity))]
        with i hi
      obtain ⟨hn', hdy, Q, hQK, hQmax⟩ := hPmax i
      have hQval : Q.val.val = (P i).val := by rw [hQK]
      have hneg : surfaceAreaMeasure (P i).val
          ((fun s : ℝ ↦ (s : Real.Angle)) '' Ioo (-(Real.pi / 2)) 0) = 0 := by
        rw [← hQval]
        exact surfaceAreaMeasure_rightAngle_Ioo_neg_eq_zero (n i) hn' Q
      have hsplit : ((fun t : ℝ ↦ (t : Real.Angle)) '' V) ⊆
          ((fun t : ℝ ↦ (t : Real.Angle)) '' (V ∩ Ico (0 : ℝ) (Real.pi / 2))) ∪
            ((fun s : ℝ ↦ (s : Real.Angle)) '' Ioo (-(Real.pi / 2)) 0) := by
        rintro u ⟨x, hxV, rfl⟩
        rcases lt_or_ge x 0 with hx | hx
        · exact Or.inr ⟨x, ⟨(hVsubIoo hxV).1, hx⟩, rfl⟩
        · exact Or.inl ⟨x, ⟨hxV, ⟨hx, (hVsubIoo hxV).2⟩⟩, rfl⟩
      have hthick : Metric.thickening (2 * polygonStepSize (n i))
          (V ∩ Ico (0 : ℝ) (Real.pi / 2)) ⊆ Metric.thickening (2 * η) C := by
        calc
          Metric.thickening (2 * polygonStepSize (n i))
              (V ∩ Ico (0 : ℝ) (Real.pi / 2)) ⊆
              Metric.thickening (2 * polygonStepSize (n i))
                (Metric.thickening η C) :=
            Metric.thickening_subset_of_subset _ hVsubThick
          _ ⊆ Metric.thickening (2 * polygonStepSize (n i) + η) C :=
            Metric.thickening_thickening_subset _ _ _
          _ ⊆ Metric.thickening (2 * η) C :=
            Metric.thickening_mono (by linarith) C
      calc
        surfaceAreaMeasure (P i).val ((fun t : ℝ ↦ (t : Real.Angle)) '' V) ≤
            surfaceAreaMeasure (P i).val
                ((fun t : ℝ ↦ (t : Real.Angle)) '' (V ∩ Ico (0 : ℝ) (Real.pi / 2))) +
              surfaceAreaMeasure (P i).val
                ((fun s : ℝ ↦ (s : Real.Angle)) '' Ioo (-(Real.pi / 2)) 0) :=
          (measure_mono hsplit).trans (measure_union_le _ _)
        _ = surfaceAreaMeasure (P i).val
            ((fun t : ℝ ↦ (t : Real.Angle)) '' (V ∩ Ico (0 : ℝ) (Real.pi / 2))) := by
          rw [hneg, add_zero]
        _ ≤ armDensityMeasure (P i) (Metric.thickening (2 * polygonStepSize (n i))
              (V ∩ Ico (0 : ℝ) (Real.pi / 2))) +
            ENNReal.ofReal (13 * (Real.pi / 2) * polygonStepSize (n i)) :=
          maximumPolygonCap_surface_image_le_thickening (n i) hn' (P i) (hPmax i)
            (V ∩ Ico (0 : ℝ) (Real.pi / 2)) hVmeas Set.inter_subset_right
            (by linarith [hδpos i])
        _ ≤ armDensityMeasure (P i) (Metric.thickening (2 * η) C) +
            ENNReal.ofReal (13 * (Real.pi / 2) * polygonStepSize (n i)) := by
          gcongr
        _ ≤ (armDensityMeasure K (Metric.thickening (2 * η) C) +
              ENNReal.ofReal (err i)) +
            ENNReal.ofReal (13 * (Real.pi / 2) * polygonStepSize (n i)) := by
          gcongr
          exact armDensityMeasure_le_add_l1 (P i) K Metric.isOpen_thickening.measurableSet
        _ = armDensityMeasure K (Metric.thickening (2 * η) C) +
            ENNReal.ofReal (err i + 13 * (Real.pi / 2) * polygonStepSize (n i)) := by
          rw [ENNReal.ofReal_add (herr0 i)
            (mul_nonneg (by positivity) (hδpos i).le), add_assoc]
    have htend : Tendsto (fun i ↦ armDensityMeasure K (Metric.thickening (2 * η) C) +
        ENNReal.ofReal (err i + 13 * (Real.pi / 2) * polygonStepSize (n i))) atTop
        (𝓝 (armDensityMeasure K (Metric.thickening (2 * η) C))) := by
      have hsum : Tendsto (fun i ↦ err i + 13 * (Real.pi / 2) * polygonStepSize (n i))
          atTop (𝓝 0) := by
        have h13 : Tendsto (fun i ↦ 13 * (Real.pi / 2) * polygonStepSize (n i))
            atTop (𝓝 0) := by
          simpa using (tendsto_const_nhds (x := 13 * (Real.pi / 2))
            (f := atTop (α := ℕ))).mul hδtend
        simpa using hL1.add h13
      have h0 : Tendsto (fun i ↦ ENNReal.ofReal
          (err i + 13 * (Real.pi / 2) * polygonStepSize (n i))) atTop (𝓝 0) := by
        simpa using ENNReal.tendsto_ofReal hsum
      simpa using (tendsto_const_nhds
        (x := armDensityMeasure K (Metric.thickening (2 * η) C))
        (f := atTop (α := ℕ))).add h0
    exact hstep1.trans ((Filter.liminf_le_liminf hev).trans (le_of_eq htend.liminf_eq))
  -- shrink the radius to zero
  have hinter : (⋂ m : ℕ, Metric.thickening (2 * (1 / (m + 1) : ℝ)) C) = C := by
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      have hclos : x ∈ closure C := by
        rw [Metric.mem_closure_iff]
        intro r hr
        obtain ⟨m, hm⟩ := exists_nat_gt (2 / r)
        obtain ⟨y, hyC, hy⟩ := Metric.mem_thickening_iff.1 (Set.mem_iInter.1 hx m)
        refine ⟨y, hyC, lt_of_lt_of_le hy ?_⟩
        have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
        rw [mul_one_div, div_le_iff₀ hmpos]
        have h2r : 2 / r < (m : ℝ) := hm
        have : 2 < r * (m : ℝ) := by
          rw [div_lt_iff₀ hr] at h2r
          linarith
        nlinarith
      rwa [hC.isClosed.closure_eq] at hclos
    · exact Set.subset_iInter fun m ↦
        Metric.self_subset_thickening (by positivity) C
  have hanti : Antitone (fun m : ℕ ↦ Metric.thickening (2 * (1 / (m + 1) : ℝ)) C) := by
    intro a b hab
    refine Metric.thickening_mono ?_ C
    have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    have hb : (0 : ℝ) < (b : ℝ) + 1 := by positivity
    have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    rw [mul_one_div, mul_one_div]
    gcongr
  have hfin : ∃ m : ℕ, armDensityMeasure K
      (Metric.thickening (2 * (1 / (m + 1) : ℝ)) C) ≠ ⊤ := by
    refine ⟨0, ?_⟩
    exact ne_top_of_le_ne_top (armDensityMeasure_ne_top K)
      (measure_mono (Set.subset_univ _))
  have hseq := tendsto_measure_iInter_atTop
    (μ := armDensityMeasure K)
    (s := fun m : ℕ ↦ Metric.thickening (2 * (1 / (m + 1) : ℝ)) C)
    (fun m ↦ Metric.isOpen_thickening.measurableSet.nullMeasurableSet) hanti hfin
  rw [hinter] at hseq
  refine ge_of_tendsto hseq (Filter.Eventually.of_forall fun m ↦ ?_)
  exact hkey _ (by positivity)

private theorem exists_isCompact_preimage {E : Set ℝ}
    (hET : E ⊆ Ico (0 : ℝ) (Real.pi / 2)) {F : Set Real.Angle} (hF : IsCompact F)
    (hFE : F ⊆ (fun t : ℝ ↦ (t : Real.Angle)) '' E) :
    ∃ C : Set ℝ, IsCompact C ∧ C ⊆ E ∧ F ⊆ (fun t : ℝ ↦ (t : Real.Angle)) '' C := by
  have hpi := Real.pi_pos
  have hinj : Set.InjOn (fun t : ℝ ↦ (t : Real.Angle)) (Icc (0 : ℝ) (Real.pi / 2)) := by
    apply (Real.Angle.injOn_coe_Ioc (a := -Real.pi) (b := Real.pi)
      (by linarith)).mono
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hclosed : IsClosed ((fun t : ℝ ↦ (t : Real.Angle)) ⁻¹' F) :=
    hF.isClosed.preimage Real.Angle.continuous_coe
  refine ⟨(fun t : ℝ ↦ (t : Real.Angle)) ⁻¹' F ∩ Icc 0 (Real.pi / 2),
    isCompact_Icc.inter_left hclosed, ?_, ?_⟩
  · rintro t ⟨htF, htI⟩
    obtain ⟨e, heE, het⟩ := hFE htF
    have : e = t := hinj (Ico_subset_Icc_self (hET heE)) htI het
    exact this ▸ heE
  · intro u hu
    obtain ⟨e, heE, rfl⟩ := hFE hu
    exact ⟨e, ⟨hu, Ico_subset_Icc_self (hET heE)⟩, rfl⟩

end Domination

theorem balancedMaximumCap_surface_domination (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) (E : Set ℝ) (hE : MeasurableSet E)
    (hET : E ⊆ Set.Ico (0 : ℝ) (Real.pi / 2)) :
    surfaceAreaMeasure K.val ((fun t : ℝ ↦ (t : Real.Angle)) '' E) ≤
      ENNReal.ofReal (∫ t in E,
        magicFunctions.1 (Real.toNNReal (tangentArmLengths K t).2.1)) := by
  classical
  let _ : IsFiniteMeasure (surfaceAreaMeasure K.val) :=
    (surfaceAreaMeasure_face_union K.val).1
  have hEimage : MeasurableSet ((fun t : ℝ ↦ (t : Real.Angle)) '' E) :=
    measurableSet_coe_image_of_subset_Ico hE hET
  rw [show ENNReal.ofReal (∫ t in E, magicFunctions.1
      (Real.toNNReal (tangentArmLengths K t).2.1)) = armDensityMeasure K E from
    (armDensityMeasure_eq_ofReal_integral K hE hET).symm,
    MeasurableSet.measure_eq_iSup_isCompact hEimage (surfaceAreaMeasure K.val)]
  refine iSup_le fun F ↦ iSup_le fun hFE ↦ iSup_le fun hFcomp ↦ ?_
  obtain ⟨C, hCcomp, hCE, hFC⟩ := exists_isCompact_preimage hET hFcomp hFE
  exact (measure_mono hFC).trans
    ((balancedMaximumCap_surface_isCompact_le K hK hCcomp (hCE.trans hET)).trans
      (measure_mono hCE))

end MovingSofa

end

end

end
