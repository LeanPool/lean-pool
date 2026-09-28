/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Bounds.Foundations.Development002
public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development002
public import LeanPool.MovingSofa.Cap.Foundations.Development004
public import LeanPool.MovingSofa.Cap.Foundations.Development002
public import LeanPool.MovingSofa.Infrastructure.MathlibExtensions.Foundations.Development001


public import LeanPool.MovingSofa.Geometry.Foundations.Development003


public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Hausdorff
/-!
# Moving sofa: related mathematical developments

* `Polygon.Approximation`.
* `Polygon.CapWidthBound`.
* `Polygon.DiscreteCapData`.
* `Polygon.Height.Properties`.
* `Polygon.Nef.Slices`.
* `Polygon.Nef.Variation.LocalSlices`.
* `Polygon.Nef.Variation.Area`.
* `Polygon.Nef.Variation.Boundary`.
* `Polygon.Nef.Variation`.
* `Polygon.Nef.SignedVariation`.
* `Polygon.Height.WallVariation`.
* `Polygon.RightAngleGrid`.
* `Polygon.Translation`.
* `Polygon.Height.Reconstruction`.
* `Polygon.Height.PositiveIncrement.Contacts`.
* `Polygon.Height.PositiveIncrement`.
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
# Polygon / Approximation
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Membership in a polygon cap is given by the strip and selected support inequalities. -/
theorem mem_angleCap_iff (Θ : AngleSet) (K : CapSpace Θ.angle) (p : Point) :
    p ∈ angleCap Θ K ↔
      ((0 ≤ p 1 ∧ p 1 ≤ 1) ∧
        (0 ≤ inner ℝ p (normalVector (Θ.angle : Real.Angle)) ∧
          inner ℝ p (normalVector (Θ.angle : Real.Angle)) ≤ 1)) ∧
      ∀ t ∈ Θ.directions,
        inner ℝ p (normalVector (t : Real.Angle)) ≤ supportValue K.val (t : Real.Angle) ∧
        inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≤
          supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
  simp only [angleCap, Set.mem_inter_iff, Set.mem_iInter, mem_stripParallelogram_iff]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro t
  apply forall_congr'
  intro _
  rw [(rotatingHallwayParts_formulas (K.val : Set Point) (t : Real.Angle)).2.2.2.2.2.2.2.1]
  rfl

/-- The polygon-cap approximation contains the original cap. -/
theorem subset_angleCap (Θ : AngleSet) (K : CapSpace Θ.angle) :
    (K.val : Set Point) ⊆ angleCap Θ K := by
  intro p hp
  apply (mem_angleCap_iff Θ K p).mpr
  refine ⟨(mem_stripParallelogram_iff _ _).mp (K.subset_stripParallelogram hp), ?_⟩
  intro t _
  exact ⟨inner_le_supportValue K.val hp _, inner_le_supportValue K.val hp _⟩

/-- A polygon cap is the intersection of its selected support half-planes. -/
theorem angleCap_eq_iInter_supportValue (Θ : AngleSet) (K : CapSpace Θ.angle) :
    angleCap Θ K = ⋂ t ∈
      ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle,
        normalHalfPlane t (supportValue K.val t) false false := by
  ext p
  simp only [Set.mem_iInter, mem_angleCap_iff]
  constructor
  · rintro ⟨⟨hy, hw⟩, ht⟩ u hu
    change inner ℝ p (normalVector u) ≤ supportValue K.val u
    rcases hu with ⟨u, hu, rfl⟩ | hu
    · rcases hu with (hu | ⟨t, ht', rfl⟩) | hu
      · exact (ht u hu).1
      · exact (ht t ht').2
      · rcases hu with rfl | hu
        · rw [K.property.2.2.1]
          exact hw.2
        · have heq : u = Real.pi / 2 := hu
          subst u
          rw [K.property.2.2.2.1]
          simpa [normalVector, frame, PiLp.inner_apply] using hy.2
    · rcases hu with rfl | hu
      · rw [K.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right]
        exact neg_nonpos.mpr hw.1
      · have heq : u = ((3 * Real.pi / 2 : ℝ) : Real.Angle) := hu
        subst u
        rw [K.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two]
        exact neg_nonpos.mpr hy.1
  · intro hp
    have ht (t : ℝ) (ht : t ∈ Θ.directions) :=
      hp (t : Real.Angle) (Or.inl ⟨t, Or.inl (Or.inl ht), rfl⟩)
    have ht' (t : ℝ) (ht : t ∈ Θ.directions) :=
      hp ((t + Real.pi / 2 : ℝ) : Real.Angle)
        (Or.inl ⟨t + Real.pi / 2, Or.inl (Or.inr ⟨t, ht, rfl⟩), rfl⟩)
    have hw := hp (Θ.angle : Real.Angle)
      (Or.inl ⟨Θ.angle, Or.inr (Or.inl rfl), rfl⟩)
    have hy := hp ((Real.pi / 2 : ℝ) : Real.Angle)
      (Or.inl ⟨Real.pi / 2, Or.inr (Or.inr rfl), rfl⟩)
    have hl := hp ((Θ.angle + Real.pi : ℝ) : Real.Angle) (Or.inr (Or.inl rfl))
    have hb := hp ((3 * Real.pi / 2 : ℝ) : Real.Angle) (Or.inr (Or.inr rfl))
    change inner ℝ p (normalVector _) ≤ supportValue K.val _ at hw hy hl hb
    rw [K.property.2.2.1] at hw
    rw [K.property.2.2.2.1] at hy
    rw [K.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right] at hl
    rw [K.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two] at hb
    have hy' : p 1 ≤ 1 := by simpa [normalVector, frame, PiLp.inner_apply] using hy
    exact ⟨⟨⟨by linarith, hy'⟩, by linarith, hw⟩, fun t h ↦ ⟨ht t h, ht' t h⟩⟩

/-- Polygon-cap approximations are closed. -/
theorem isClosed_angleCap (Θ : AngleSet) (K : CapSpace Θ.angle) :
    IsClosed (angleCap Θ K) := by
  rw [angleCap_eq_iInter_supportValue]
  apply isClosed_iInter
  intro t
  apply isClosed_iInter
  intro _
  exact isClosed_le (by fun_prop) continuous_const

/-- Polygon-cap approximations are convex. -/
theorem convex_angleCap (Θ : AngleSet) (K : CapSpace Θ.angle) :
    Convex ℝ (angleCap Θ K) := by
  rw [angleCap_eq_iInter_supportValue]
  apply convex_iInter
  intro t
  apply convex_iInter
  intro _
  apply convex_halfSpace_le
  exact ⟨fun x y ↦ inner_add_left x y _, fun a x ↦ by simp [real_inner_smul_left]⟩

/-- Polygon-cap approximation preserves support at every selected normal. -/
theorem supportValue_angleCap (Θ : AngleSet) (K : CapSpace Θ.angle)
    {t : Real.Angle}
    (ht : t ∈ ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle) :
    supportValue (angleCap Θ K) t = supportValue K.val t := by
  have hbound : ∀ p ∈ angleCap Θ K, inner ℝ p (normalVector t) ≤ supportValue K.val t := by
    intro p hp
    rw [angleCap_eq_iInter_supportValue] at hp
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hp t) ht
  have hbd : BddAbove ((fun p ↦ inner ℝ p (normalVector t)) '' angleCap Θ K) := by
    refine ⟨supportValue K.val t, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact hbound p hp
  apply le_antisymm
  · apply csSup_le ((K.val.nonempty.mono (subset_angleCap Θ K)).image _)
    rintro _ ⟨p, hp, rfl⟩
    exact hbound p hp
  · apply csSup_le (K.val.nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    exact le_csSup hbd ⟨p, subset_angleCap Θ K hp, rfl⟩

/-- Polygon-cap approximation fixes caps with the prescribed normals. -/
theorem angleCap_eq_self (Θ : AngleSet) (P : PolygonCapSpace Θ) :
    angleCap Θ P.val = (P.val.val : Set Point) := by
  rw [angleCap_eq_iInter_supportValue, ← P.property.eq_iInter_supportValue]

/-- An interior selected direction bounds the polygon cap, including at right angle. -/
theorem isBounded_angleCap (Θ : AngleSet) (K : CapSpace Θ.angle) :
    Bornology.IsBounded (angleCap Θ K) := by
  obtain ⟨t, ht⟩ := Θ.nonempty
  have hti := Θ.interior t ht
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, hti.1], hti.2.trans_le Θ.angle_le⟩
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi hti.1
    (by linarith [hti.2, Θ.angle_le, Real.pi_pos])
  let l := -supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) / Real.sin t
  let r := supportValue K.val (t : Real.Angle) / Real.cos t
  let M := |l| + |r|
  have hM : 0 ≤ M := by dsimp [M]; positivity
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨M + 1, ?_⟩
  intro p hp
  obtain ⟨⟨hy, _⟩, hnormals⟩ := (mem_angleCap_iff Θ K p).mp hp
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

/-- Polygon-cap approximations are compact. -/
theorem isCompact_angleCap (Θ : AngleSet) (K : CapSpace Θ.angle) :
    IsCompact (angleCap Θ K) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_angleCap Θ K, isBounded_angleCap Θ K⟩

theorem angleCap_properties (Θ : AngleSet) (K : CapSpace Θ.angle) :
    (∃ P : PolygonCapSpace Θ, (P.val.val : Set Point) = angleCap Θ K) ∧
    (K.val : Set Point) ⊆ angleCap Θ K ∧
    (∀ t ∈ ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle,
      supportValue (angleCap Θ K) t = supportValue (K.val : Set Point) t) ∧
    (∀ P : PolygonCapSpace Θ, angleCap Θ P.val = (P.val.val : Set Point)) := by
  refine ⟨?_, subset_angleCap Θ K, fun _ ht ↦ supportValue_angleCap Θ K ht,
    angleCap_eq_self Θ⟩
  let L : ConvexBody Point := ⟨angleCap Θ K, convex_angleCap Θ K,
    isCompact_angleCap Θ K, K.val.nonempty.mono (subset_angleCap Θ K)⟩
  let N := ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle
  have hrepr : HasHalfPlaneRepresentation L N := by
    refine ⟨(fun t ↦ (t, supportValue K.val t)) '' N, ?_, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact ht
    · simp only [Set.biInter_image]
      exact angleCap_eq_iInter_supportValue Θ K
  have hdomain : angleDomain Θ ⊆ capUpperAngles Θ.angle := by
    rintro t ((ht | ⟨s, hs, rfl⟩) | ht)
    · exact Or.inl ⟨(Θ.interior t ht).1.le, (Θ.interior t ht).2.le⟩
    · right
      constructor <;> linarith [(Θ.interior s hs).1, (Θ.interior s hs).2]
    · rcases ht with rfl | rfl
      · exact Or.inl ⟨Θ.angle_pos.le, le_rfl⟩
      · exact Or.inr ⟨le_rfl, le_add_of_nonneg_left Θ.angle_pos.le⟩
  have hrepr' : HasHalfPlaneRepresentation L
      (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles Θ.angle) ∪ capLowerNormals Θ.angle) := by
    obtain ⟨C, hC, hLC⟩ := hrepr
    refine ⟨C, ?_, hLC⟩
    intro c hc
    rcases hC c hc with ⟨t, ht, heq⟩ | ht
    · exact Or.inl ⟨t, hdomain ht, heq⟩
    · exact Or.inr ht
  have hsupp (t : Real.Angle) (ht : t ∈ N) : supportValue L t = supportValue K.val t :=
    supportValue_angleCap Θ K ht
  have hcap : IsCap Θ.angle L := by
    refine ⟨Θ.angle_pos, Θ.angle_le, ?_, ?_, ?_, ?_, hrepr'⟩
    · rw [hsupp _ (Or.inl ⟨Θ.angle, Or.inr (Or.inl rfl), rfl⟩)]
      exact K.property.2.2.1
    · rw [hsupp _ (Or.inl ⟨Real.pi / 2, Or.inr (Or.inr rfl), rfl⟩)]
      exact K.property.2.2.2.1
    · rw [hsupp _ (Or.inr (Or.inl rfl))]
      exact K.property.2.2.2.2.1
    · rw [hsupp _ (Or.inr (Or.inr rfl))]
      exact K.property.2.2.2.2.2.1
  exact ⟨⟨⟨L, hcap⟩, hrepr⟩, rfl⟩

theorem polygonNiche_angleCap (Θ : AngleSet) (K P : CapSpace Θ.angle)
    (hP : (P.val : Set Point) = angleCap Θ K) :
    polygonNiche Θ K = polygonNiche Θ P ∧ polygonNiche Θ K ⊆ capNiche K := by
  refine ⟨?_, polygonNiche_subset_capNiche Θ K⟩
  have hs := (angleCap_properties Θ K).2.2.1
  have hq (t : ℝ) (ht : t ∈ Θ.directions) :
      innerQuadrant (K.val : Set Point) t = innerQuadrant (P.val : Set Point) t := by
    unfold innerQuadrant
    rw [hP, hs (t : Real.Angle) (Or.inl ⟨t, Or.inl (Or.inl ht), rfl⟩),
      hs ((t + Real.pi / 2 : ℝ) : Real.Angle)
        (Or.inl ⟨t + Real.pi / 2, Or.inl (Or.inr ⟨t, ht, rfl⟩), rfl⟩)]
  unfold polygonNiche
  congr 1
  exact Set.iUnion_congr fun t ↦ Set.iUnion_congr fun ht ↦ hq t ht

theorem polygonArea_upperBound (Θ : AngleSet) :
    (∀ K : PolygonCapSpace Θ, polygonAreaFunctional Θ K.val =
      ClassicalResults.area (K.val.val : Set Point) -
        ClassicalResults.area (polygonNiche Θ K.val)) ∧
    (∀ K : CapSpace Θ.angle, capAreaFunctional K ≤ polygonAreaFunctional Θ K) := by
  constructor
  · intro K
    unfold polygonAreaFunctional
    rw [(angleCap_properties Θ K.val).2.2.2 K]
  · intro K
    obtain ⟨P, hP⟩ := (angleCap_properties Θ K).1
    have hcap : ClassicalResults.area (K.val : Set Point) ≤
        ClassicalResults.area (angleCap Θ K) := by
      apply ENNReal.toReal_mono
      · rw [← hP]
        exact P.val.val.isCompact.measure_ne_top
      · exact MeasureTheory.measure_mono (angleCap_properties Θ K).2.1
    have hniche : ClassicalResults.area (polygonNiche Θ K) ≤
        ClassicalResults.area (capNiche K) := by
      apply ENNReal.toReal_mono (niche_uniform_bounds.1 Θ.angle K).2.2.1.ne
      exact MeasureTheory.measure_mono (polygonNiche_angleCap Θ K P.val hP).2
    exact sub_le_sub hcap hniche

/-- A maximum polygon cap dominates every cap under the polygon area functional. -/
theorem polygonAreaFunctional_le_maximum (Θ : AngleSet) (P : PolygonCapSpace Θ)
    (hP : IsMaximumPolygonCap Θ P) (K : CapSpace Θ.angle) :
    polygonAreaFunctional Θ K ≤ polygonAreaFunctional Θ P.val := by
  obtain ⟨Q, hQ⟩ := (angleCap_properties Θ K).1
  have hn := (polygonNiche_angleCap Θ K Q.val hQ).1
  have harea : polygonAreaFunctional Θ Q.val = polygonAreaFunctional Θ K := by
    unfold polygonAreaFunctional
    rw [(angleCap_properties Θ Q.val).2.2.2 Q, hQ, hn]
  rw [← harea]
  exact hP.2 Q

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
# Polygon / Cap Width Bound
-/

@[expose] public section

noncomputable section

namespace MovingSofa

open MeasureTheory
open scoped Pointwise

private theorem directionalWidth_zero (K : ConvexBody Point) :
    directionalWidth K 0 = horizontalMax K - horizontalMin K := by
  simp only [directionalWidth, zero_add]
  rw [← Real.Angle.coe_zero, supportValue_zero_eq_horizontalMax,
    supportValue_pi_eq_neg_horizontalMin, ← sub_eq_add_neg]

private theorem volume_coordinate_open_rectangle (l r b t : ℝ) :
    volume {p : Point | p 0 ∈ Set.Ioo l r ∧ p 1 ∈ Set.Ioo b t} =
      ENNReal.ofReal (r - l) * ENNReal.ofReal (t - b) := by
  have h := EuclideanSpace.volume_preserving_finTwoCoordinates.measure_preimage
    ((measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet :
      NullMeasurableSet (Set.Ioo l r ×ˢ Set.Ioo b t) (volume : Measure (ℝ × ℝ)))
  simpa [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Set.preimage, Set.prod] using h

private theorem cap_horizontalWidth_le_of_cos_pos {ω : ℝ} (K : CapSpace ω)
    (hc : 0 < Real.cos ω) :
    directionalWidth (K.val : Set Point) 0 ≤ (1 + Real.sin ω) / Real.cos ω := by
  have hs : 0 ≤ Real.sin ω := Real.sin_nonneg_of_nonneg_of_le_pi K.property.1.le
    (K.property.2.1.trans (by linarith [Real.pi_pos]))
  have hx (p : Point) (hp : p ∈ (K.val : Set Point)) :
      -Real.sin ω / Real.cos ω ≤ p 0 ∧ p 0 ≤ 1 / Real.cos ω := by
    obtain ⟨hy, hv⟩ := (mem_stripParallelogram_iff ω p).mp (K.subset_stripParallelogram hp)
    simp [normalVector, frame, PiLp.inner_apply] at hv
    constructor
    · apply (div_le_iff₀ hc).mpr
      nlinarith [mul_nonneg hs (sub_nonneg.mpr hy.2)]
    · apply (le_div_iff₀ hc).mpr
      nlinarith [mul_nonneg hs hy.1]
  have hmax : horizontalMax K.val ≤ 1 / Real.cos ω :=
    csSup_le (K.val.nonempty.image _) (by rintro _ ⟨p, hp, rfl⟩; exact (hx p hp).2)
  have hmin : -Real.sin ω / Real.cos ω ≤ horizontalMin K.val :=
    le_csInf (K.val.nonempty.image _) (by rintro _ ⟨p, hp, rfl⟩; exact (hx p hp).1)
  rw [directionalWidth_zero]
  calc
    horizontalMax K.val - horizontalMin K.val ≤
        1 / Real.cos ω - -Real.sin ω / Real.cos ω := sub_le_sub hmax hmin
    _ = (1 + Real.sin ω) / Real.cos ω := by ring

private theorem wedge_rectangle_inequalities {s c a b x y : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hs1 : s ≤ 1) (hc1 : c ≤ 1)
    (hL : 0 < a / c + b / s)
    (hx : x ∈ Set.Ioo (-b / s + (a / c + b / s) / 4)
      (a / c - (a / c + b / s) / 4))
    (hy : y ∈ Set.Ioo 0 ((a / c + b / s) * s * c / 4)) :
    0 ≤ y ∧ c * x + s * y < a ∧ -s * x + c * y < b := by
  let L := a / c + b / s
  have hLc : 0 ≤ L * c / 4 := by dsimp [L]; positivity
  have hLs : 0 ≤ L * s / 4 := by dsimp [L]; positivity
  have hyc : y < L * c / 4 := by
    apply hy.2.trans_le
    calc
      L * s * c / 4 = s * (L * c / 4) := by ring
      _ ≤ 1 * (L * c / 4) := mul_le_mul_of_nonneg_right hs1 hLc
      _ = L * c / 4 := one_mul _
  have hys : y < L * s / 4 := by
    apply hy.2.trans_le
    calc
      L * s * c / 4 = c * (L * s / 4) := by ring
      _ ≤ 1 * (L * s / 4) := mul_le_mul_of_nonneg_right hc1 hLs
      _ = L * s / 4 := one_mul _
  have hsy : s * y ≤ y := by nlinarith [mul_nonneg (sub_nonneg.mpr hs1) hy.1.le]
  have hcy : c * y ≤ y := by nlinarith [mul_nonneg (sub_nonneg.mpr hc1) hy.1.le]
  have hright : (x + L / 4) * c < a :=
    (lt_div_iff₀ hc).mp (by dsimp [L]; linarith [hx.2])
  have hleft : -b < (x - L / 4) * s :=
    (div_lt_iff₀ hs).mp (by dsimp [L]; linarith [hx.1])
  exact ⟨hy.1.le, by nlinarith, by nlinarith⟩

private theorem polygonNiche_area_ge_rectangle (Θ : AngleSet)
    (hΘ : Θ.angle = Real.pi / 2) {t : ℝ} (ht : t ∈ Θ.directions)
    (K : CapSpace Θ.angle) (hs : 0 < Real.sin t) (hc : 0 < Real.cos t)
    (hL : 0 < (supportValue K.val (t : Real.Angle) - 1) / Real.cos t +
      (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) / Real.sin t) :
    ((supportValue K.val (t : Real.Angle) - 1) / Real.cos t +
      (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) / Real.sin t) ^ 2 *
      Real.sin t * Real.cos t / 8 ≤ ClassicalResults.area (polygonNiche Θ K) := by
  let a := supportValue K.val (t : Real.Angle) - 1
  let b := supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1
  let L := a / Real.cos t + b / Real.sin t
  let R : Set Point := {p | p 0 ∈ Set.Ioo (-b / Real.sin t + L / 4)
    (a / Real.cos t - L / 4) ∧ p 1 ∈ Set.Ioo 0 (L * Real.sin t * Real.cos t / 4)}
  have hsub : R ⊆ polygonNiche Θ K := by
    intro p hp
    have hineq := wedge_rectangle_inequalities hs hc (Real.sin_le_one t) (Real.cos_le_one t)
      hL hp.1 hp.2
    refine ⟨?_, Set.mem_iUnion₂.mpr ⟨t, ht, ?_⟩⟩
    · rw [hΘ]
      simpa [capFan, normalHalfPlane, normalVector, frame, PiLp.inner_apply] using hineq.1
    · simpa [innerQuadrant, normalHalfPlane, normalVector, frame, PiLp.inner_apply,
        Real.sin_add, Real.cos_add, -Real.Angle.coe_add, a, b] using hineq.2
  have hwidth : a / Real.cos t - L / 4 - (-b / Real.sin t + L / 4) = L / 2 := by
    dsimp [L]
    ring
  have harea : ClassicalResults.area R = L ^ 2 * Real.sin t * Real.cos t / 8 := by
    change (volume R).toReal = _
    rw [volume_coordinate_open_rectangle, hwidth, sub_zero, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (show 0 ≤ L / 2 by dsimp [L, a, b]; positivity),
      ENNReal.toReal_ofReal (show 0 ≤ L * Real.sin t * Real.cos t / 4 by
        dsimp [L, a, b]; positivity)]
    ring
  rw [← harea]
  exact ENNReal.toReal_mono (niche_uniform_bounds.2.1 Θ K).2.2.1.ne (measure_mono hsub)

theorem polygonCap_width_bound (ω t : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (ht : t ∈ Set.Ioo 0 ω) :
    ∃ c : ℝ, 0 < c ∧ ∀ (Θ : AngleSet), Θ.angle = ω → t ∈ Θ.directions →
      ∀ K : PolygonCapSpace Θ, 0 ≤ polygonAreaFunctional Θ K.val →
        directionalWidth (K.val.val : Set Point) (0 : Real.Angle) ≤ c := by
  rcases lt_or_eq_of_le hω' with hlt | rfl
  · have hc : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], hlt⟩
    have hs : 0 ≤ Real.sin ω := Real.sin_nonneg_of_nonneg_of_le_pi hω.le
      (by linarith [Real.pi_pos])
    refine ⟨(1 + Real.sin ω) / Real.cos ω, div_pos (by linarith) hc, ?_⟩
    intro Θ hΘ _ K _
    have hcΘ : 0 < Real.cos Θ.angle := by simpa only [hΘ] using hc
    simpa only [hΘ] using cap_horizontalWidth_le_of_cos_pos K.val hcΘ
  · have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
      (by linarith [ht.2, Real.pi_pos])
    have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
    let D := 1 / Real.cos t + 1 / Real.sin t
    let C := max (2 * D) (32 / (Real.sin t * Real.cos t))
    have hC : 0 < C := lt_of_lt_of_le (div_pos (by norm_num) (mul_pos hs hc)) (le_max_right _ _)
    refine ⟨C, hC, ?_⟩
    intro Θ hΘ htΘ K hnonneg
    by_contra hwidth
    have hdC : C < directionalWidth (K.val.val : Set Point) 0 := lt_of_not_ge hwidth
    rw [directionalWidth_zero] at hdC
    let d := horizontalMax K.val.val - horizontalMin K.val.val
    have hd0 : 0 < d := hC.trans hdC
    let a := supportValue K.val.val (t : Real.Angle) - 1
    let b := supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1
    let L := a / Real.cos t + b / Real.sin t
    have hsupport := CapSpace.horizontal_le_supportValue K.val hs.le hc.le
    simp only [Real.Angle.coe_add] at hsupport
    have ha : horizontalMax K.val.val - 1 / Real.cos t ≤ a / Real.cos t := by
      apply (le_div_iff₀ hc).mpr
      rw [sub_mul, div_mul_cancel₀ _ hc.ne']
      dsimp [a]
      linarith [hsupport.1]
    have hb : -horizontalMin K.val.val - 1 / Real.sin t ≤ b / Real.sin t := by
      apply (le_div_iff₀ hs).mpr
      rw [sub_mul, div_mul_cancel₀ _ hs.ne']
      dsimp [b]
      linarith [hsupport.2]
    have hLd : d - D ≤ L := by dsimp [L, d, D]; linarith
    have hdD : 2 * D < d := (le_max_left _ _).trans_lt hdC
    have hdlarge : 32 / (Real.sin t * Real.cos t) < d := (le_max_right _ _).trans_lt hdC
    have hhalf : d / 2 < L := by linarith
    have hL : 0 < L := (half_pos hd0).trans hhalf
    have hlower := polygonNiche_area_ge_rectangle Θ hΘ htΘ K.val hs hc hL
    have hsq : (d / 2) ^ 2 < L ^ 2 := (sq_lt_sq₀ (half_pos hd0).le hL.le).mpr hhalf
    have hsq' := mul_lt_mul_of_pos_right hsq (mul_pos hs hc)
    have hdlarge' : 32 < d * (Real.sin t * Real.cos t) :=
      (div_lt_iff₀ (mul_pos hs hc)).mp hdlarge
    have hquad : d < L ^ 2 * Real.sin t * Real.cos t / 8 := by
      nlinarith [mul_pos hd0 (sub_pos.mpr hdlarge')]
    have harea := K.val.area_le_horizontalWidth
    have hidentity := (polygonArea_upperBound Θ).1 K
    change L ^ 2 * Real.sin t * Real.cos t / 8 ≤ _ at hlower
    change ClassicalResults.area (K.val.val : Set Point) ≤ d at harea
    rw [hidentity] at hnonneg
    linarith

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
# Polygon / Discrete Cap Data
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The uniformly spaced interior directions for a right-angle polygonal approximation. -/
def rightAngleSet (n : ℕ) (hn : 2 ≤ n) : AngleSet :=
  uniformAngleSet (Real.pi / 2) (by positivity) le_rfl n hn

/-- The angular mesh size `π/(2n)`. -/
def polygonStepSize (n : ℕ) : ℝ := (Real.pi / 2) / n

/-- The cap maximizes the polygonal functional on a uniform mesh with a power-of-two step
count. -/
def IsMaximumPolygonCapSteps (n : ℕ) (K : RightAngleCapSpace) : Prop :=
  ∃ hn : 2 ≤ n, (∃ k : ℕ, n = 2 ^ k) ∧
    ∃ P : PolygonCapSpace (rightAngleSet n hn),
      P.val = K ∧ IsMaximumPolygonCap (rightAngleSet n hn) P

/-- The two piecewise scalar functions used in the arm-length inequalities. -/
def magicFunctions : (NNReal → ℝ) × (NNReal → ℝ) :=
  (fun x ↦ max |(x : ℝ) - 1| ((|(x : ℝ) - 1| + 1) / 2),
   fun x ↦ (x : ℝ) - max |(x : ℝ) - 1| ((|(x : ℝ) - 1| + 1) / 2))

/-- The magic function `m₀` is nondecreasing: it is `3 * x / 2 - 1` on `[0, 1]`, `x / 2` on
`[1, 2]`, and constant equal to `1` afterwards. -/
theorem magicFunctions_snd_monotone : Monotone magicFunctions.2 := by
  intro a b hab
  have hab' : (a : ℝ) ≤ (b : ℝ) := hab
  simp only [magicFunctions, max_def]
  rcases abs_cases ((a : ℝ) - 1) with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;>
    rcases abs_cases ((b : ℝ) - 1) with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;>
      rw [ha1, hb1] <;> split_ifs <;> linarith

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
# Polygon / Height / Properties
-/

@[expose] public section

noncomputable section

namespace MovingSofa

private theorem polygonHeightValue_supportValue {Θ : AngleSet} (K : PolygonCapSpace Θ)
    {t : ℝ} (ht : t ∈ angleDomain Θ) :
    polygonHeightValue (Θ := Θ)
      (fun s ↦ supportValue (K.val.val : Set Point) (s.val : Real.Angle)) t =
      supportValue K.val.val (t : Real.Angle) := by
  simp [polygonHeightValue, ht]

private theorem polygonHeightFan_supportValue {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    polygonHeightFan (Θ := Θ)
      (fun s ↦ supportValue (K.val.val : Set Point) (s.val : Real.Angle)) =
      capFan Θ.angle := by
  have hω : Θ.angle ∈ angleDomain Θ := by simp [angleDomain]
  have hT : Real.pi / 2 ∈ angleDomain Θ := by simp [angleDomain]
  ext q
  simp only [polygonHeightFan, Set.mem_iInter, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  rw [polygonHeightValue_supportValue K hω, polygonHeightValue_supportValue K hT,
    K.val.property.2.2.1, K.val.property.2.2.2.1]
  simp [capFan]

private theorem polygonHeightNiche_supportValue {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    polygonHeightNiche (Θ := Θ)
      (fun s ↦ supportValue (K.val.val : Set Point) (s.val : Real.Angle)) =
      polygonNiche Θ K.val := by
  unfold polygonHeightNiche polygonNiche
  rw [polygonHeightFan_supportValue K]
  congr 1
  apply Set.iUnion_congr
  intro t
  apply Set.iUnion_congr
  intro ht
  have htD : t ∈ angleDomain Θ := by simp [angleDomain, ht]
  have htTD : t + Real.pi / 2 ∈ angleDomain Θ := by
    exact Or.inl (Or.inr ⟨t, ht, rfl⟩)
  rw [polygonHeightValue_supportValue K htD, polygonHeightValue_supportValue K htTD]
  rfl

private theorem polygonHeightParallelogram_supportValue {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    polygonHeightParallelogram (Θ := Θ)
      (fun s ↦ supportValue (K.val.val : Set Point) (s.val : Real.Angle)) =
      (stripParallelogram Θ.angle).1 := by
  have hω : Θ.angle ∈ angleDomain Θ := by simp [angleDomain]
  have hT : Real.pi / 2 ∈ angleDomain Θ := by simp [angleDomain]
  ext p
  simp only [polygonHeightParallelogram, Set.mem_iInter, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  rw [polygonHeightValue_supportValue K hω, polygonHeightValue_supportValue K hT,
    K.val.property.2.2.1, K.val.property.2.2.2.1, mem_stripParallelogram_iff]
  simp [normalHalfPlane, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
  tauto

private theorem polygonHeightCap_supportValue {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    polygonHeightCap (Θ := Θ)
      (fun s ↦ supportValue (K.val.val : Set Point) (s.val : Real.Angle)) =
      angleCap Θ K.val := by
  unfold polygonHeightCap
  rw [polygonHeightParallelogram_supportValue K]
  ext p
  rw [mem_angleCap_iff]
  simp only [Set.mem_inter_iff, mem_stripParallelogram_iff, Set.mem_iInter]
  apply and_congr_right
  intro _
  constructor
  · intro h t ht
    have htD : t ∈ angleDomain Θ := Or.inl (Or.inl ht)
    have htTD : t + Real.pi / 2 ∈ angleDomain Θ := Or.inl (Or.inr ⟨t, ht, rfl⟩)
    have h₁ := h t (Or.inl ht)
    have h₂ := h (t + Real.pi / 2) (Or.inr ⟨t, ht, rfl⟩)
    rw [polygonHeightValue_supportValue K htD] at h₁
    rw [polygonHeightValue_supportValue K htTD] at h₂
    exact ⟨h₁, h₂⟩
  · intro h t ht
    have htD : t ∈ angleDomain Θ := Or.inl ht
    rw [polygonHeightValue_supportValue K htD]
    rcases ht with ht | ⟨s, hs, rfl⟩
    · exact (h t ht).1
    · exact (h s hs).2

private theorem mem_polygonHeightCap_supportValue_image_add {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (q p : Point) :
    p + q ∈ polygonHeightCap (Θ := Θ)
      (fun t ↦ supportValue ((fun x ↦ x + q) '' (K.val.val : Set Point))
        (t.val : Real.Angle)) ↔
    p ∈ polygonHeightCap (Θ := Θ)
      (fun t ↦ supportValue (K.val.val : Set Point) (t.val : Real.Angle)) := by
  have hval (t : ℝ) (ht : t ∈ angleDomain Θ) :
      polygonHeightValue (Θ := Θ)
        (fun t ↦ supportValue ((fun x ↦ x + q) '' (K.val.val : Set Point))
          (t.val : Real.Angle)) t =
      polygonHeightValue (Θ := Θ)
        (fun t ↦ supportValue (K.val.val : Set Point) (t.val : Real.Angle)) t +
          inner ℝ q (normalVector (t : Real.Angle)) := by
    simp only [polygonHeightValue, dite_eq_left ht]
    exact supportValue_image_add K.val.val q (t : Real.Angle)
  simp only [polygonHeightCap, polygonHeightParallelogram, Set.mem_inter_iff,
    Set.mem_iInter]
  apply and_congr
  · apply forall_congr'
    intro t
    apply forall_congr'
    intro ht
    rw [hval t (Or.inr ht)]
    simp [normalHalfPlane, inner_add_left, add_sub_right_comm]
  · apply forall_congr'
    intro t
    apply forall_congr'
    intro ht
    rw [hval t (Or.inl ht)]
    simp [normalHalfPlane, inner_add_left]

private theorem polygonHeightNiche_supportValue_image_add {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (q : Point) :
    polygonHeightNiche (Θ := Θ)
      (fun t ↦ supportValue ((fun x ↦ x + q) '' (K.val.val : Set Point))
        (t.val : Real.Angle)) =
      (fun p ↦ p + q) '' polygonNiche Θ K.val := by
  have hval (t : ℝ) (ht : t ∈ angleDomain Θ) :
      polygonHeightValue (Θ := Θ)
        (fun t ↦ supportValue ((fun x ↦ x + q) '' (K.val.val : Set Point))
          (t.val : Real.Angle)) t =
      polygonHeightValue (Θ := Θ)
        (fun t ↦ supportValue (K.val.val : Set Point) (t.val : Real.Angle)) t +
          inner ℝ q (normalVector (t : Real.Angle)) := by
    simp only [polygonHeightValue, dite_eq_left ht]
    exact supportValue_image_add K.val.val q (t : Real.Angle)
  ext x
  obtain ⟨p, rfl⟩ : ∃ p : Point, x = p + q := ⟨x - q, by simp⟩
  rw [← polygonHeightNiche_supportValue K]
  simp only [Set.mem_image, add_left_inj, exists_eq_right]
  simp only [polygonHeightNiche, polygonHeightFan, Set.mem_inter_iff,
    Set.mem_iInter, Set.mem_iUnion]
  apply and_congr
  · apply forall_congr'
    intro t
    apply forall_congr'
    intro ht
    rw [hval t (Or.inr ht)]
    simp [normalHalfPlane, inner_add_left, add_sub_right_comm]
  · apply exists_congr
    intro t
    apply exists_congr
    intro ht
    rw [hval t (Or.inl (Or.inl ht)),
      hval (t + Real.pi / 2) (Or.inl (Or.inr ⟨t, ht, rfl⟩))]
    simp [normalHalfPlane, inner_add_left, add_sub_right_comm]

theorem polygonHeightCap_of_translate {Θ : AngleSet} (K : PolygonCapTranslateSpace Θ) :
    polygonHeightCap (polygonTranslateHeight K) = K.val := by
  obtain ⟨P, q, hK⟩ := K.property
  unfold polygonTranslateHeight
  rw [hK]
  ext x
  obtain ⟨p, rfl⟩ : ∃ p : Point, x = p + q := ⟨x - q, by simp⟩
  rw [mem_polygonHeightCap_supportValue_image_add, polygonHeightCap_supportValue, angleCap_eq_self]
  simp

theorem polygonTranslateHeight_injective (Θ : AngleSet) :
    Function.Injective (polygonTranslateHeight (Θ := Θ)) := by
  intro K L h
  apply Subtype.ext
  rw [← polygonHeightCap_of_translate K, ← polygonHeightCap_of_translate L, h]

theorem polygonHeightNiche_of_cap {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    polygonHeightNiche (Θ := Θ) (fun t ↦ supportValue (K.val.val : Set Point) (t.val :
      Real.Angle)) =
      polygonNiche Θ K.val ∧
    polygonHeightArea (Θ := Θ) (fun t ↦ supportValue (K.val.val : Set Point) (t.val : Real.Angle)) =
      polygonAreaFunctional Θ K.val := by
  refine ⟨polygonHeightNiche_supportValue K, ?_⟩
  unfold polygonHeightArea polygonAreaFunctional
  rw [polygonHeightCap_supportValue K, polygonHeightNiche_supportValue K]

theorem polygonTranslateExtensions_eq {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (q : Point) (K' : PolygonCapTranslateSpace Θ)
    (hK : K'.val = (fun p ↦ p + q) '' (K.val.val : Set Point)) :
    (polygonTranslateExtensions K').1 = (fun p ↦ p + q) '' polygonNiche Θ K.val ∧
    (polygonTranslateExtensions K').2 = polygonAreaFunctional Θ K.val := by
  have hn : polygonHeightNiche (polygonTranslateHeight K') =
      (fun p ↦ p + q) '' polygonNiche Θ K.val := by
    unfold polygonTranslateHeight
    rw [hK]
    exact polygonHeightNiche_supportValue_image_add K q
  refine ⟨hn, ?_⟩
  change ClassicalResults.area (polygonHeightCap (polygonTranslateHeight K')) -
    ClassicalResults.area (polygonHeightNiche (polygonTranslateHeight K')) = _
  rw [polygonHeightCap_of_translate K', hn, hK, ClassicalResults.area_image_add,
    ClassicalResults.area_image_add]
  unfold polygonAreaFunctional
  rw [angleCap_eq_self]

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
# Polygon / Nef / Slices
-/

@[expose] public section

noncomputable section

namespace MovingSofa.Nef

open Filter Topology

/-- Convert normal and tangent coordinates into a point in the frame at angle `a`. -/
def framePoint (a : Real.Angle) (x y : ℝ) : Point :=
  rotationMap a !₂[x, y]

lemma framePoint_eq (a : Real.Angle) (x y : ℝ) :
    framePoint a x y = x • normalVector a + y • tangentVector a := by
  ext j
  fin_cases j <;>
    simp [framePoint, rotationMap, Orientation.rotation_apply,
      rightAngleRotation_apply, normalVector, tangentVector, frame]
  <;> ring

@[simp] lemma inner_framePoint_normalVector (a : Real.Angle) (x y : ℝ) :
    inner ℝ (framePoint a x y) (normalVector a) = x := by
  rw [framePoint, inner_rotationMap_normalVector]
  rfl

@[simp] lemma inner_framePoint_tangentVector (a : Real.Angle) (x y : ℝ) :
    inner ℝ (framePoint a x y) (tangentVector a) = y := by
  rw [framePoint, inner_rotationMap_tangentVector]
  rfl

@[simp] lemma norm_tangentVector_angle (a : Real.Angle) : ‖tangentVector a‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [EuclideanSpace.norm_sq_eq]
  simp [tangentVector, frame, Fin.sum_univ_two]
  nlinarith [Real.Angle.cos_sq_add_sin_sq a]

/-- The normal-normal coefficient for changing between two oriented frames. -/
def frameNormalCoeff (a b : Real.Angle) : ℝ :=
  inner ℝ (normalVector a) (normalVector b)

/-- The tangent-normal coefficient for changing between two oriented frames. -/
def frameTangentCoeff (a b : Real.Angle) : ℝ :=
  inner ℝ (tangentVector a) (normalVector b)

lemma inner_framePoint_normalVector_eq (a b : Real.Angle) (x y : ℝ) :
    inner ℝ (framePoint a x y) (normalVector b) =
      frameNormalCoeff a b * x + frameTangentCoeff a b * y := by
  rw [framePoint_eq, inner_add_left, real_inner_smul_left,
    real_inner_smul_left]
  simp only [frameNormalCoeff, frameTangentCoeff]
  ring

/-- Select the half-plane side required by a Boolean cell’s membership pattern. -/
def cellUpper {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) (j : Fin n) : Bool :=
  if P j then (H j).upper else !(H j).upper

/-- Solve the wall equation for the tangent coordinate at a fixed normal coordinate. -/
def frameBoundaryValue (a : Real.Angle) (H : PlanarHalfPlaneData) (x : ℝ) : ℝ :=
  (H.height - frameNormalCoeff a H.angle * x) / frameTangentCoeff a H.angle

lemma frameBoundaryValue_sub (a : Real.Angle) (H : PlanarHalfPlaneData)
    (x z : ℝ) :
    frameBoundaryValue a H x - frameBoundaryValue a H z =
      -(frameNormalCoeff a H.angle / frameTangentCoeff a H.angle) * (x - z) := by
  simp only [frameBoundaryValue]
  ring

lemma abs_frameBoundaryValue_sub (a : Real.Angle) (H : PlanarHalfPlaneData)
    (x z : ℝ) :
    |frameBoundaryValue a H x - frameBoundaryValue a H z| =
      |frameNormalCoeff a H.angle / frameTangentCoeff a H.angle| * |x - z| := by
  rw [frameBoundaryValue_sub, abs_mul, abs_neg]

/-- The wall bounds a Boolean cell’s slice from above in the selected frame. -/
def isUpperEndpoint {n : ℕ} (a : Real.Angle) (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) (j : Fin n) : Prop :=
  (cellUpper H P j = false ∧ 0 < frameTangentCoeff a (H j).angle) ∨
    (cellUpper H P j = true ∧ frameTangentCoeff a (H j).angle < 0)

/-- The wall bounds a Boolean cell’s slice from below in the selected frame. -/
def isLowerEndpoint {n : ℕ} (a : Real.Angle) (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) (j : Fin n) : Prop :=
  (cellUpper H P j = false ∧ frameTangentCoeff a (H j).angle < 0) ∨
    (cellUpper H P j = true ∧ 0 < frameTangentCoeff a (H j).angle)

/-- The affine wall functions imposing upper bounds on the slice. -/
def upperBoundaryFunctions {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) : List (ℝ → ℝ) := by
  classical
  exact ((Finset.univ.filter (isUpperEndpoint a H P)).toList.map fun j x ↦
    frameBoundaryValue a (H j) x)

/-- The affine wall functions imposing lower bounds on the slice. -/
def lowerBoundaryFunctions {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) : List (ℝ → ℝ) := by
  classical
  exact ((Finset.univ.filter (isLowerEndpoint a H P)).toList.map fun j x ↦
    frameBoundaryValue a (H j) x)

/-- The minimum of all upper wall functions, capped by the truncation height `R`. -/
def upperEnvelope {n : ℕ} (a : Real.Angle) (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) (R x : ℝ) : ℝ :=
  (upperBoundaryFunctions a H P).foldr (fun f r ↦ min (f x) r) R

/-- The maximum of all lower wall functions, bounded below by `-R`. -/
def lowerEnvelope {n : ℕ} (a : Real.Angle) (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) (R x : ℝ) : ℝ :=
  (lowerBoundaryFunctions a H P).foldr (fun f r ↦ max (f x) r) (-R)

/-- The sum of absolute wall slopes, bounding the variation of slice envelopes. -/
def slopeBound {n : ℕ} (a : Real.Angle) (H : Fin n → PlanarHalfPlaneData) : ℝ :=
  ∑ j, |frameNormalCoeff a (H j).angle / frameTangentCoeff a (H j).angle|

lemma slopeBound_nonneg {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) : 0 ≤ slopeBound a H := by
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

lemma abs_upperEnvelope_sub_le {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x z : ℝ) :
    |upperEnvelope a H P R x - upperEnvelope a H P R z| ≤
      slopeBound a H * |x - z| := by
  apply List.abs_foldr_min_apply_sub_le
  · exact slopeBound_nonneg a H
  · intro f hf
    simp only [upperBoundaryFunctions, List.mem_map, Finset.mem_toList,
      Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨j, _, rfl⟩ := hf
    rw [abs_frameBoundaryValue_sub]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    simpa only [slopeBound] using
      (Finset.single_le_sum (s := Finset.univ)
        (f := fun k : Fin n ↦
          |frameNormalCoeff a (H k).angle / frameTangentCoeff a (H k).angle|)
        (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j))

lemma abs_lowerEnvelope_sub_le {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x z : ℝ) :
    |lowerEnvelope a H P R x - lowerEnvelope a H P R z| ≤
      slopeBound a H * |x - z| := by
  apply List.abs_foldr_max_apply_sub_le
  · exact slopeBound_nonneg a H
  · intro f hf
    simp only [lowerBoundaryFunctions, List.mem_map, Finset.mem_toList,
      Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨j, _, rfl⟩ := hf
    rw [abs_frameBoundaryValue_sub]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    simpa only [slopeBound] using
      (Finset.single_le_sum (s := Finset.univ)
        (f := fun k : Fin n ↦
          |frameNormalCoeff a (H k).angle / frameTangentCoeff a (H k).angle|)
        (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j))

/-- The nonnegative difference between the truncated upper and lower slice envelopes. -/
def cellSliceLength {n : ℕ} (a : Real.Angle) (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) (R x : ℝ) : ℝ :=
  max (upperEnvelope a H P R x - lowerEnvelope a H P R x) 0

lemma abs_cellSliceLength_sub_le {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x z : ℝ) :
    |cellSliceLength a H P R x - cellSliceLength a H P R z| ≤
      (2 * slopeBound a H) * |x - z| := by
  unfold cellSliceLength
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · calc
      |(upperEnvelope a H P R x - lowerEnvelope a H P R x) -
          (upperEnvelope a H P R z - lowerEnvelope a H P R z)| ≤
          |upperEnvelope a H P R x - upperEnvelope a H P R z| +
            |lowerEnvelope a H P R x - lowerEnvelope a H P R z| := by
              rw [sub_sub_sub_comm]
              exact abs_sub _ _
      _ ≤ slopeBound a H * |x - z| + slopeBound a H * |x - z| :=
        add_le_add (abs_upperEnvelope_sub_le a H P R x z)
          (abs_lowerEnvelope_sub_le a H P R x z)
      _ = (2 * slopeBound a H) * |x - z| := by ring
  · simp only [sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (slopeBound_nonneg a H))
      (abs_nonneg _)

lemma continuous_cellSliceLength {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R : ℝ) :
    Continuous (cellSliceLength a H P R) := by
  let K : NNReal :=
    ⟨2 * slopeBound a H, mul_nonneg (by norm_num) (slopeBound_nonneg a H)⟩
  apply (LipschitzWith.of_dist_le_mul (K := K) fun x z ↦ ?_).continuous
  change |cellSliceLength a H P R x - cellSliceLength a H P R z| ≤
    (2 * slopeBound a H) * |x - z|
  exact abs_cellSliceLength_sub_le a H P R x z

/-- The closed Boolean cell’s slice at a fixed normal coordinate, truncated to `[-R, R]`. -/
def closedCellSlice {n : ℕ} (a : Real.Angle) (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) (R x : ℝ) : Set ℝ :=
  {y | framePoint a x y ∈ closedBooleanCell H P} ∩ Set.Icc (-R) R

/-- Every wall parallel to the slice is satisfied at the selected normal coordinate. -/
def parallelCellFeasible {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (x : ℝ) : Prop :=
  ∀ j, frameTangentCoeff a (H j).angle = 0 →
    framePoint a x 0 ∈ normalHalfPlane (H j).angle (H j).height
      (cellUpper H P j) false

lemma mem_closedCellSlice_iff {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x y : ℝ)
    (hparallel : parallelCellFeasible a H P x) :
    y ∈ closedCellSlice a H P R x ↔
      lowerEnvelope a H P R x ≤ y ∧ y ≤ upperEnvelope a H P R x := by
  classical
  rw [closedCellSlice, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc,
    lowerEnvelope, upperEnvelope, List.foldr_max_apply_le_iff, List.le_foldr_min_apply_iff]
  constructor
  · rintro ⟨hycell, hyR⟩
    simp only [closedBooleanCell, Set.mem_iInter] at hycell
    refine ⟨⟨hyR.1, ?_⟩, hyR.2, ?_⟩
    · intro f hf
      simp only [lowerBoundaryFunctions, List.mem_map, Finset.mem_toList,
        Finset.mem_filter, Finset.mem_univ, true_and] at hf
      obtain ⟨j, hj, rfl⟩ := hf
      have hjcell := hycell j
      change framePoint a x y ∈ normalHalfPlane (H j).angle (H j).height
        (cellUpper H P j) false at hjcell
      rcases hj with ⟨hu, hb⟩ | ⟨hu, hb⟩
      · simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
          Set.mem_ofPred_eq] at hjcell
        rw [inner_framePoint_normalVector_eq] at hjcell
        simp only [frameBoundaryValue]
        apply (div_le_iff_of_neg hb).2
        nlinarith
      · simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
          Set.mem_ofPred_eq] at hjcell
        rw [inner_framePoint_normalVector_eq] at hjcell
        simp only [frameBoundaryValue]
        apply (div_le_iff₀ hb).2
        nlinarith
    · intro f hf
      simp only [upperBoundaryFunctions, List.mem_map, Finset.mem_toList,
        Finset.mem_filter, Finset.mem_univ, true_and] at hf
      obtain ⟨j, hj, rfl⟩ := hf
      have hjcell := hycell j
      change framePoint a x y ∈ normalHalfPlane (H j).angle (H j).height
        (cellUpper H P j) false at hjcell
      rcases hj with ⟨hu, hb⟩ | ⟨hu, hb⟩
      · simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
          Set.mem_ofPred_eq] at hjcell
        rw [inner_framePoint_normalVector_eq] at hjcell
        simp only [frameBoundaryValue]
        apply (le_div_iff₀ hb).2
        nlinarith
      · simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
          Set.mem_ofPred_eq] at hjcell
        rw [inner_framePoint_normalVector_eq] at hjcell
        simp only [frameBoundaryValue]
        apply (le_div_iff_of_neg hb).2
        nlinarith
  · rintro ⟨⟨hyRneg, hylower⟩, hyR, hyupper⟩
    refine ⟨?_, hyRneg, hyR⟩
    simp only [closedBooleanCell, Set.mem_iInter]
    intro j
    change framePoint a x y ∈ normalHalfPlane (H j).angle (H j).height
      (cellUpper H P j) false
    by_cases hb0 : frameTangentCoeff a (H j).angle = 0
    · have hj := hparallel j hb0
      cases hu : cellUpper H P j <;>
        simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
          Set.mem_ofPred_eq] at hj ⊢ <;>
        rw [inner_framePoint_normalVector_eq] at hj ⊢ <;>
        simp only [hb0, mul_zero, zero_mul, add_zero] at hj ⊢ <;>
        exact hj
    · rcases lt_or_gt_of_ne hb0 with hb | hb
      · by_cases hu : cellUpper H P j = false
        · have hjindex : isLowerEndpoint a H P j := Or.inl ⟨hu, hb⟩
          have hjfun : (fun x ↦ frameBoundaryValue a (H j) x) ∈
              lowerBoundaryFunctions a H P := by
            simp only [lowerBoundaryFunctions, List.mem_map, Finset.mem_toList,
              Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨j, hjindex, rfl⟩
          have hjbound := hylower _ hjfun
          simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
            Set.mem_ofPred_eq, inner_framePoint_normalVector_eq,
            frameBoundaryValue] at hjbound ⊢
          have := (div_le_iff_of_neg hb).mp hjbound
          nlinarith
        · have hu' : cellUpper H P j = true := Bool.eq_true_of_not_eq_false hu
          have hjindex : isUpperEndpoint a H P j := Or.inr ⟨hu', hb⟩
          have hjfun : (fun x ↦ frameBoundaryValue a (H j) x) ∈
              upperBoundaryFunctions a H P := by
            simp only [upperBoundaryFunctions, List.mem_map, Finset.mem_toList,
              Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨j, hjindex, rfl⟩
          have hjbound := hyupper _ hjfun
          simp only [normalHalfPlane, hu', Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq,
            inner_framePoint_normalVector_eq, frameBoundaryValue,
            ] at hjbound ⊢
          have := (le_div_iff_of_neg hb).mp hjbound
          nlinarith
      · by_cases hu : cellUpper H P j = false
        · have hjindex : isUpperEndpoint a H P j := Or.inl ⟨hu, hb⟩
          have hjfun : (fun x ↦ frameBoundaryValue a (H j) x) ∈
              upperBoundaryFunctions a H P := by
            simp only [upperBoundaryFunctions, List.mem_map, Finset.mem_toList,
              Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨j, hjindex, rfl⟩
          have hjbound := hyupper _ hjfun
          simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
            Set.mem_ofPred_eq, inner_framePoint_normalVector_eq,
            frameBoundaryValue] at hjbound ⊢
          have := (le_div_iff₀ hb).mp hjbound
          nlinarith
        · have hu' : cellUpper H P j = true := Bool.eq_true_of_not_eq_false hu
          have hjindex : isLowerEndpoint a H P j := Or.inr ⟨hu', hb⟩
          have hjfun : (fun x ↦ frameBoundaryValue a (H j) x) ∈
              lowerBoundaryFunctions a H P := by
            simp only [lowerBoundaryFunctions, List.mem_map, Finset.mem_toList,
              Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨j, hjindex, rfl⟩
          have hjbound := hylower _ hjfun
          simp only [normalHalfPlane, hu', Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq,
            inner_framePoint_normalVector_eq, frameBoundaryValue,
            ] at hjbound ⊢
          have := (div_le_iff₀ hb).mp hjbound
          nlinarith

lemma volume_closedCellSlice_toReal {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ)
    (hparallel : parallelCellFeasible a H P x) :
    (MeasureTheory.volume (closedCellSlice a H P R x)).toReal =
      cellSliceLength a H P R x := by
  have hset : closedCellSlice a H P R x =
      Set.Icc (lowerEnvelope a H P R x) (upperEnvelope a H P R x) := by
    ext y
    simpa [Set.mem_Icc] using mem_closedCellSlice_iff a H P R x y hparallel
  rw [hset, Real.volume_Icc]
  unfold cellSliceLength
  by_cases h : 0 ≤ upperEnvelope a H P R x - lowerEnvelope a H P R x
  · rw [ENNReal.toReal_ofReal h, max_eq_left h]
  · have h' : upperEnvelope a H P R x - lowerEnvelope a H P R x ≤ 0 := le_of_not_ge h
    rw [ENNReal.ofReal_of_nonpos h', max_eq_right h']
    rfl

/-- The actual Boolean membership cell’s slice, truncated to `[-R, R]`. -/
def booleanCellSlice {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ) : Set ℝ :=
  {y | framePoint a x y ∈ booleanCell (fun j ↦ (H j).carrier) P} ∩ Set.Icc (-R) R

/-- No wall parallel to the slice has its boundary at the selected normal coordinate. -/
def noParallelBoundaryAt {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (x : ℝ) : Prop :=
  ∀ j, frameTangentCoeff a (H j).angle = 0 →
    frameNormalCoeff a (H j).angle * x ≠ (H j).height

/-- The tangent coordinates at which the slice meets a wall boundary. -/
def cellSliceBoundaryExceptions {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (x : ℝ) : Set ℝ :=
  ⋃ j, {y | inner ℝ (framePoint a x y) (normalVector (H j).angle) = (H j).height}

lemma finite_cellSliceBoundaryExceptions {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (x : ℝ) (hx : noParallelBoundaryAt a H x) :
    (cellSliceBoundaryExceptions a H x).Finite := by
  classical
  unfold cellSliceBoundaryExceptions
  apply Set.Finite.iUnion Set.finite_univ
  · intro j _
    apply Set.Subsingleton.finite
    intro y hy z hz
    simp only [Set.mem_ofPred_eq, inner_framePoint_normalVector_eq] at hy hz
    by_cases hb : frameTangentCoeff a (H j).angle = 0
    · exact (hx j hb (by simpa [hb] using hy)).elim
    · rcases lt_or_gt_of_ne hb with hb | hb <;> nlinarith
  · simp

lemma volume_booleanCellSlice_eq_closedCellSlice {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ)
    (hx : noParallelBoundaryAt a H x) :
    MeasureTheory.volume (booleanCellSlice a H P R x) =
      MeasureTheory.volume (closedCellSlice a H P R x) := by
  apply MeasureTheory.measure_congr
  rw [MeasureTheory.ae_eq_set]
  have hzero :=
    (finite_cellSliceBoundaryExceptions a H x hx).measure_zero MeasureTheory.volume
  constructor <;> apply MeasureTheory.measure_mono_null _ hzero
  · intro y hy
    by_contra hyexception
    have hyne : ∀ j, inner ℝ (framePoint a x y) (normalVector (H j).angle) ≠
        (H j).height := by
      intro j hj
      apply hyexception
      exact Set.mem_iUnion.mpr ⟨j, hj⟩
    have heq := mem_booleanCell_iff_mem_closedBooleanCell_of_ne H P _ hyne
    rcases hy.1 with ⟨hycell, hyR⟩
    exact hy.2 ⟨heq.mp hycell, hyR⟩
  · intro y hy
    by_contra hyexception
    have hyne : ∀ j, inner ℝ (framePoint a x y) (normalVector (H j).angle) ≠
        (H j).height := by
      intro j hj
      apply hyexception
      exact Set.mem_iUnion.mpr ⟨j, hj⟩
    have heq := mem_booleanCell_iff_mem_closedBooleanCell_of_ne H P _ hyne
    rcases hy.1 with ⟨hycell, hyR⟩
    exact hy.2 ⟨heq.mpr hycell, hyR⟩

lemma volume_booleanCellSlice_toReal {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ)
    (hparallel : parallelCellFeasible a H P x)
    (hx : noParallelBoundaryAt a H x) :
    (MeasureTheory.volume (booleanCellSlice a H P R x)).toReal =
      cellSliceLength a H P R x := by
  rw [volume_booleanCellSlice_eq_closedCellSlice a H P R x hx]
  exact volume_closedCellSlice_toReal a H P R x hparallel

lemma normalVector_eq_frameCombination (a b : Real.Angle) :
    normalVector b = frameNormalCoeff a b • normalVector a +
      frameTangentCoeff a b • tangentVector a := by
  symm
  simpa only [frameNormalCoeff, frameTangentCoeff, real_inner_comm] using
    inner_normalVector_smul_add_inner_tangentVector_smul (normalVector b) a

lemma normalLine_eq_of_frameTangentCoeff_eq_zero {a b : Real.Angle} {h k : ℝ}
    (hb : frameTangentCoeff a b = 0) (hk : frameNormalCoeff a b * h = k) :
    normalLine b k = normalLine a h := by
  have hvec : normalVector b = frameNormalCoeff a b • normalVector a := by
    rw [normalVector_eq_frameCombination a b, hb, zero_smul, add_zero]
  have hcoeff : frameNormalCoeff a b ≠ 0 := by
    intro hc
    have : normalVector b = 0 := by simp [hvec, hc]
    have hnorm : ‖normalVector b‖ = 1 := by
      simpa only [b.coe_toReal] using norm_normalVector_real b.toReal
    rw [this, norm_zero] at hnorm
    norm_num at hnorm
  ext p
  simp only [normalLine, Set.mem_ofPred_eq, hvec, inner_smul_right]
  rw [← hk]
  constructor <;> intro hp
  · exact (mul_left_cancel₀ hcoeff hp)
  · exact congrArg (frameNormalCoeff a b * ·) hp

@[simp] lemma frameNormalCoeff_self (a : Real.Angle) : frameNormalCoeff a a = 1 := by
  simpa only [frameNormalCoeff, a.coe_toReal] using inner_normalVector_self a.toReal

lemma measurableSet_booleanCellSlice {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ) :
    MeasurableSet (booleanCellSlice a H P R x) := by
  apply MeasurableSet.inter _ measurableSet_Icc
  have hcont : Continuous (fun y ↦ framePoint a x y) := by
    simp_rw [framePoint_eq]
    fun_prop
  exact (measurableSet_booleanCell H P).preimage hcont.measurable

/-- The envelope slice length when parallel walls are feasible, and zero otherwise. -/
def actualCellSliceLength {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ) : ℝ := by
  classical
  exact if parallelCellFeasible a H P x then cellSliceLength a H P R x else 0

lemma closedCellSlice_eq_empty_of_not_parallelCellFeasible {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ)
    (hparallel : ¬parallelCellFeasible a H P x) :
    closedCellSlice a H P R x = ∅ := by
  classical
  unfold parallelCellFeasible at hparallel
  push Not at hparallel
  obtain ⟨j, hb, hj⟩ := hparallel
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hycell := hy.1
  simp only [closedBooleanCell, Set.mem_iInter] at hycell
  have hjy := hycell j
  change framePoint a x y ∈ normalHalfPlane (H j).angle (H j).height
    (cellUpper H P j) false at hjy
  cases hu : cellUpper H P j <;>
    simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
      Set.mem_ofPred_eq, inner_framePoint_normalVector_eq, hb, zero_mul, add_zero]
      at hj hjy
  · exact hj hjy
  · exact hj hjy

lemma volume_booleanCellSlice_toReal_eq_actual {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ)
    (_hx : noParallelBoundaryAt a H x) :
    (MeasureTheory.volume (booleanCellSlice a H P R x)).toReal =
      actualCellSliceLength a H P R x := by
  by_cases hp : parallelCellFeasible a H P x
  · simp only [actualCellSliceLength, hp, ↓reduceIte]
    exact volume_booleanCellSlice_toReal a H P R x hp _hx
  · simp only [actualCellSliceLength, hp, ↓reduceIte]
    rw [volume_booleanCellSlice_eq_closedCellSlice a H P R x _hx,
      closedCellSlice_eq_empty_of_not_parallelCellFeasible a H P R x hp,
      MeasureTheory.measure_empty]
    rfl

/-- The measurable equivalence between the Euclidean plane and a pair of real coordinates. -/
def frameCoordinates : Point ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

lemma frameCoordinates_measurePreserving :
    MeasureTheory.MeasurePreserving frameCoordinates MeasureTheory.volume
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume) := by
  rw [← MeasureTheory.Measure.volume_eq_prod]
  convert EuclideanSpace.volume_preserving_finTwoCoordinates using 1
  funext p
  rfl

lemma framePoint_measurePreserving (a : Real.Angle) :
    MeasureTheory.MeasurePreserving (fun p : ℝ × ℝ ↦ framePoint a p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume)
      MeasureTheory.volume := by
  have hcoordinates : MeasureTheory.MeasurePreserving frameCoordinates.symm
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume)
      MeasureTheory.volume :=
    frameCoordinates_measurePreserving.symm frameCoordinates
  have hrotation : MeasureTheory.MeasurePreserving
      (EuclideanGeometry.o.rotation a : Point → Point) :=
    LinearIsometryEquiv.measurePreserving _
  convert hrotation.comp hcoordinates using 1
  funext p
  rfl

lemma volume_toReal_eq_integral_frameSlice (a : Real.Angle) {S : Set Point}
    (hS : MeasurableSet S) (hSfinite : MeasureTheory.volume S ≠ ⊤) :
    (MeasureTheory.volume S).toReal =
      ∫ x : ℝ, (MeasureTheory.volume {y : ℝ | framePoint a x y ∈ S}).toReal := by
  let f : ℝ × ℝ → Point := fun p ↦ framePoint a p.1 p.2
  have hf := framePoint_measurePreserving a
  have hpre : MeasurableSet (f ⁻¹' S) := hS.preimage hf.measurable
  have hmeasure : MeasureTheory.volume (f ⁻¹' S) = MeasureTheory.volume S :=
    hf.measure_preimage hS.nullMeasurableSet
  have hprod : ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
      MeasureTheory.volume) (f ⁻¹' S) =
      ∫⁻ x : ℝ, MeasureTheory.volume (Prod.mk x ⁻¹' (f ⁻¹' S)) :=
    MeasureTheory.Measure.prod_apply hpre
  have hsectionMeas : Measurable
      (fun x : ℝ ↦ MeasureTheory.volume (Prod.mk x ⁻¹' (f ⁻¹' S))) :=
    measurable_measure_prodMk_left hpre
  have hsectionFinite : ∀ᵐ x : ℝ ∂MeasureTheory.volume,
      MeasureTheory.volume (Prod.mk x ⁻¹' (f ⁻¹' S)) < ⊤ :=
    MeasureTheory.Measure.ae_measure_lt_top hpre (by
      rw [← MeasureTheory.Measure.volume_eq_prod, hmeasure]
      exact hSfinite)
  rw [← hmeasure]
  calc
    (MeasureTheory.volume (f ⁻¹' S)).toReal =
        (((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          MeasureTheory.volume) (f ⁻¹' S)).toReal := by
      rw [← MeasureTheory.Measure.volume_eq_prod]
    _ = (∫⁻ x : ℝ,
        MeasureTheory.volume (Prod.mk x ⁻¹' (f ⁻¹' S))).toReal :=
      congrArg ENNReal.toReal hprod
    _ = ∫ x : ℝ,
        (MeasureTheory.volume (Prod.mk x ⁻¹' (f ⁻¹' S))).toReal :=
      (MeasureTheory.integral_toReal hsectionMeas.aemeasurable hsectionFinite).symm
    _ = ∫ x : ℝ,
        (MeasureTheory.volume {y : ℝ | framePoint a x y ∈ S}).toReal := by
      rfl

end MovingSofa.Nef

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
# Polygon / Nef / Variation / Local Slices
-/

@[expose] public section

noncomputable section

namespace MovingSofa.Nef

open Filter Topology

/-- Replace one wall by a closed upper-bound wall at auxiliary height `M`. -/
def auxiliaryHalfPlaneFamily {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (M : ℝ) : Fin n → PlanarHalfPlaneData :=
  Function.update H i
    { angle := (H i).angle, height := M, upper := false, strict := false }

@[simp] lemma auxiliaryHalfPlaneFamily_self {n : ℕ}
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (M : ℝ) :
    auxiliaryHalfPlaneFamily H i M i =
      { angle := (H i).angle, height := M, upper := false, strict := false } := by
  simp [auxiliaryHalfPlaneFamily]

lemma auxiliaryHalfPlaneFamily_of_ne {n : ℕ}
    (H : Fin n → PlanarHalfPlaneData) (i j : Fin n) (M : ℝ) (hji : j ≠ i) :
    auxiliaryHalfPlaneFamily H i M j = H j := by
  simp [auxiliaryHalfPlaneFamily, Function.update_of_ne hji]

lemma noParallelBoundaryAt_auxiliary {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (hLines : Function.Injective (fun j ↦ (H j).boundaryLine))
    (R ε₀ : ℝ) (hR : 0 < R) (hε₀ : 0 < ε₀) :
    noParallelBoundaryAt (H i).angle
      (auxiliaryHalfPlaneFamily H i (|(H i).height| + ε₀ + R + 1)) (H i).height := by
  intro j hb
  by_cases hji : j = i
  · subst j
    simp only [auxiliaryHalfPlaneFamily_self, frameNormalCoeff_self]
    have hh : (H i).height < |(H i).height| + ε₀ + R + 1 := by
      linarith [le_abs_self (H i).height]
    simpa only [one_mul] using ne_of_lt hh
  · rw [auxiliaryHalfPlaneFamily_of_ne H i j _ hji] at hb ⊢
    intro heq
    have hline : (H j).boundaryLine = (H i).boundaryLine := by
      exact normalLine_eq_of_frameTangentCoeff_eq_zero hb heq
    exact hji (hLines hline)

lemma eventually_parallel_inequalities_iff {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (h : ℝ) (hh : noParallelBoundaryAt a H h) :
    ∀ᶠ x in 𝓝 h, ∀ j, frameTangentCoeff a (H j).angle = 0 →
      (frameNormalCoeff a (H j).angle * x ≤ (H j).height ↔
          frameNormalCoeff a (H j).angle * h ≤ (H j).height) ∧
        ((H j).height ≤ frameNormalCoeff a (H j).angle * x ↔
          (H j).height ≤ frameNormalCoeff a (H j).angle * h) := by
  suffices ∀ᶠ x in 𝓝 h, ∀ j ∈ (Set.univ : Set (Fin n)),
      frameTangentCoeff a (H j).angle = 0 →
        (frameNormalCoeff a (H j).angle * x ≤ (H j).height ↔
            frameNormalCoeff a (H j).angle * h ≤ (H j).height) ∧
          ((H j).height ≤ frameNormalCoeff a (H j).angle * x ↔
            (H j).height ≤ frameNormalCoeff a (H j).angle * h) by
    exact this.mono fun x hx j ↦ hx j (Set.mem_univ j)
  apply (Filter.eventually_all_finite Set.finite_univ).2
  intro j _
  by_cases hb : frameTangentCoeff a (H j).angle = 0
  · have hne := hh j hb
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hev : ∀ᶠ x in 𝓝 h,
          frameNormalCoeff a (H j).angle * x < (H j).height :=
        (continuousAt_const.mul continuousAt_id).eventually_lt continuousAt_const hlt
      filter_upwards [hev] with x hx
      intro _
      constructor <;> constructor <;> intro <;> linarith
    · have hev : ∀ᶠ x in 𝓝 h,
          (H j).height < frameNormalCoeff a (H j).angle * x :=
        continuousAt_const.eventually_lt (continuousAt_const.mul continuousAt_id) hgt
      filter_upwards [hev] with x hx
      intro _
      constructor <;> constructor <;> intro <;> linarith
  · exact Filter.Eventually.of_forall fun _ hb' ↦ (hb hb').elim

lemma eventually_parallelCellFeasible_iff {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (h : ℝ) (hh : noParallelBoundaryAt a H h) :
    ∀ᶠ x in 𝓝 h, ∀ P : Fin n → Bool,
      parallelCellFeasible a H P x ↔ parallelCellFeasible a H P h := by
  filter_upwards [eventually_parallel_inequalities_iff a H h hh] with x hx
  intro P
  constructor <;> intro hp j hb
  · have hj := hp j hb
    have hiff := hx j hb
    cases hu : cellUpper H P j <;>
      simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
        Set.mem_ofPred_eq, inner_framePoint_normalVector_eq, hb, mul_zero, add_zero]
        at hj ⊢
    · exact hiff.1.mp hj
    · exact hiff.2.mp hj
  · have hj := hp j hb
    have hiff := hx j hb
    cases hu : cellUpper H P j <;>
      simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
        Set.mem_ofPred_eq, inner_framePoint_normalVector_eq, hb, mul_zero, add_zero]
        at hj ⊢
    · exact hiff.1.mpr hj
    · exact hiff.2.mpr hj

lemma exists_parallel_stability_radius {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (h : ℝ) (hh : noParallelBoundaryAt a H h) :
    ∃ ε > 0, ∀ x, |x - h| ≤ ε →
      noParallelBoundaryAt a H x ∧
        ∀ P : Fin n → Bool,
          (parallelCellFeasible a H P x ↔ parallelCellFeasible a H P h) := by
  have hev : ∀ᶠ x in 𝓝 h,
      (∀ j, frameTangentCoeff a (H j).angle = 0 →
        (frameNormalCoeff a (H j).angle * x ≤ (H j).height ↔
            frameNormalCoeff a (H j).angle * h ≤ (H j).height) ∧
          ((H j).height ≤ frameNormalCoeff a (H j).angle * x ↔
            (H j).height ≤ frameNormalCoeff a (H j).angle * h)) ∧
        ∀ P : Fin n → Bool,
          (parallelCellFeasible a H P x ↔ parallelCellFeasible a H P h) :=
    (eventually_parallel_inequalities_iff a H h hh).and
      (eventually_parallelCellFeasible_iff a H h hh)
  rcases (Metric.mem_nhds_iff.mp hev) with ⟨r, hr, hball⟩
  refine ⟨r / 2, by positivity, ?_⟩
  intro x hx
  have hxr : x ∈ Metric.ball h r := by
    rw [Metric.mem_ball, Real.dist_eq]
    calc
      |x - h| ≤ r / 2 := hx
      _ < r := by linarith
  have hstable := hball hxr
  refine ⟨?_, hstable.2⟩
  intro j hb heq
  have hj := hstable.1 j hb
  apply hh j hb
  apply le_antisymm
  · exact hj.1.mp (by rw [heq])
  · exact hj.2.mp (by rw [heq])

lemma setMembershipPattern_auxiliary {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (M : ℝ) (p : Point)
    (hp : p ∈ (auxiliaryHalfPlaneFamily H i M i).carrier) :
    setMembershipPattern (fun j ↦ (auxiliaryHalfPlaneFamily H i M j).carrier) p =
      Function.update (setMembershipPattern (fun j ↦ (H j).carrier) p) i true := by
  classical
  funext j
  by_cases hji : j = i
  · subst j
    rw [auxiliaryHalfPlaneFamily_self] at hp
    simp [setMembershipPattern, hp]
  · simp [setMembershipPattern, auxiliaryHalfPlaneFamily_of_ne H i j M hji,
      Function.update_of_ne hji]

lemma mem_activeBooleanRegion_iff_mem_booleanCell_auxiliary {n : ℕ}
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (M : ℝ) (p : Point) (hp : p ∈ (auxiliaryHalfPlaneFamily H i M i).carrier) :
    p ∈ activeBooleanRegion E H i ↔
      ∃ P ∈ activeBooleanPatterns E i,
        p ∈ booleanCell (fun j ↦ (auxiliaryHalfPlaneFamily H i M j).carrier) P := by
  classical
  rw [mem_activeBooleanRegion_iff]
  constructor
  · intro hactive
    unfold IsActiveBooleanPattern at hactive
    let P := setMembershipPattern
      (fun j ↦ (auxiliaryHalfPlaneFamily H i M j).carrier) p
    have hP : P = Function.update
        (setMembershipPattern (fun j ↦ (H j).carrier) p) i true :=
      setMembershipPattern_auxiliary H i M p hp
    refine ⟨P, ?_, (mem_booleanCell_iff _ _ _).mpr rfl⟩
    simp only [activeBooleanPatterns, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold IsActiveBooleanPattern
    rw [hP]
    simpa only [Function.update_idem] using hactive
  · rintro ⟨P, hP, hcell⟩
    simp only [activeBooleanPatterns, Finset.mem_filter, Finset.mem_univ,
      true_and] at hP
    have hpattern := (mem_booleanCell_iff _ P p).mp hcell
    have haux := setMembershipPattern_auxiliary H i M p hp
    unfold IsActiveBooleanPattern at hP ⊢
    rw [hpattern] at haux
    rw [haux] at hP
    simpa only [Function.update_idem] using hP

/-- The slice of the region where the selected Boolean wall is active, truncated to `[-R, R]`. -/
def activeRegionSlice {n : ℕ} (a : Real.Angle) (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (R x : ℝ) : Set ℝ :=
  {y | framePoint a x y ∈ activeBooleanRegion E H i} ∩ Set.Icc (-R) R

lemma frameSlice_perturbSdiff_eq {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (hSide : (H i).upper = false) (R ε₀ δ ε x : ℝ)
    (hδ : |δ| ≤ ε₀)
    (hBound : ∀ z : ℝ, |z| ≤ ε₀ →
      perturbNefHeight E H i z ⊆ Metric.closedBall 0 R) :
    (x ∈ heightInterval (H i).strict (H i).height δ ε →
      {y : ℝ | framePoint (H i).angle x y ∈
          perturbNefHeight E H i δ \ perturbNefHeight E H i ε} =
        activeRegionSlice (H i).angle E H i R x) ∧
    (x ∉ heightInterval (H i).strict (H i).height δ ε →
      {y : ℝ | framePoint (H i).angle x y ∈
          perturbNefHeight E H i δ \ perturbNefHeight E H i ε} = ∅) := by
  constructor
  · intro hx
    rw [perturbNefHeight_sdiff_eq_heightInterval hE H i hSide]
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff,
      inner_framePoint_normalVector, hx, true_and, activeRegionSlice]
    constructor
    · intro hy
      refine ⟨hy, ?_⟩
      have hdiff : framePoint (H i).angle x y ∈
          perturbNefHeight E H i δ \ perturbNefHeight E H i ε := by
        rw [perturbNefHeight_sdiff_eq_heightInterval hE H i hSide]
        exact ⟨by simpa using hx, hy⟩
      have hball := hBound δ hδ hdiff.1
      have hynorm := abs_real_inner_le_norm (framePoint (H i).angle x y)
        (tangentVector (H i).angle)
      rw [inner_framePoint_tangentVector, norm_tangentVector_angle, mul_one] at hynorm
      have hpR : ‖framePoint (H i).angle x y‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_zero_left] using hball
      exact abs_le.mp (hynorm.trans hpR)
    · exact fun hy ↦ hy.1
  · intro hx
    rw [perturbNefHeight_sdiff_eq_heightInterval hE H i hSide]
    ext y
    simp [hx]

lemma activeRegionSlice_eq_biUnion_booleanCellSlice_auxiliary {n : ℕ}
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (M R x : ℝ) (hxM : x ≤ M) :
    activeRegionSlice (H i).angle E H i R x =
      ⋃ P ∈ activeBooleanPatterns E i,
        booleanCellSlice (H i).angle (auxiliaryHalfPlaneFamily H i M) P R x := by
  classical
  ext y
  have haux : framePoint (H i).angle x y ∈
      (auxiliaryHalfPlaneFamily H i M i).carrier := by
    simp [PlanarHalfPlaneData.carrier, normalHalfPlane, hxM]
  rw [activeRegionSlice, Set.mem_inter_iff, Set.mem_ofPred_eq,
    mem_activeBooleanRegion_iff_mem_booleanCell_auxiliary E H i M _ haux]
  simp only [Set.mem_iUnion, booleanCellSlice, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨P, hP, hyP⟩, hyR⟩
    exact ⟨P, ⟨hP, hyP, hyR⟩⟩
  · rintro ⟨P, hP, hyP, hyR⟩
    exact ⟨⟨P, hP, hyP⟩, hyR⟩

lemma measure_activeRegionSlice_eq_sum {n : ℕ}
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (M R x : ℝ) (hxM : x ≤ M) :
    MeasureTheory.volume (activeRegionSlice (H i).angle E H i R x) =
      ∑ P ∈ activeBooleanPatterns E i,
        MeasureTheory.volume
          (booleanCellSlice (H i).angle (auxiliaryHalfPlaneFamily H i M) P R x) := by
  rw [activeRegionSlice_eq_biUnion_booleanCellSlice_auxiliary E H i M R x hxM]
  apply MeasureTheory.measure_biUnion_finset
  · intro P hP Q hQ hPQ
    change Disjoint
      (booleanCellSlice (H i).angle (auxiliaryHalfPlaneFamily H i M) P R x)
      (booleanCellSlice (H i).angle (auxiliaryHalfPlaneFamily H i M) Q R x)
    rw [Set.disjoint_left]
    intro y hyP hyQ
    apply hPQ
    have hcellP := hyP.1
    have hcellQ := hyQ.1
    have hp := (mem_booleanCell_iff _ P _).mp hcellP
    have hq := (mem_booleanCell_iff _ Q _).mp hcellQ
    exact hp.symm.trans hq
  · intro P _
    exact measurableSet_booleanCellSlice _ _ _ _ _

/-- Sum the feasible slice lengths over patterns where the selected wall is active. -/
def activeSliceLength {n : ℕ} (a : Real.Angle) (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (R x : ℝ) : ℝ :=
  ∑ P ∈ activeBooleanPatterns E i, actualCellSliceLength a H P R x

/-- Sum slice lengths while freezing all parallel-wall feasibility decisions at the reference
height. -/
def frozenActiveSliceLength {n : ℕ} (a : Real.Angle) (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (R h x : ℝ) : ℝ := by
  classical
  exact ∑ P ∈ activeBooleanPatterns E i,
    if parallelCellFeasible a H P h then cellSliceLength a H P R x else 0

lemma continuous_frozenActiveSliceLength {n : ℕ} (a : Real.Angle)
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (R h : ℝ) :
    Continuous (frozenActiveSliceLength a E H i R h) := by
  classical
  unfold frozenActiveSliceLength
  apply continuous_finsetSum
  intro P hP
  by_cases hp : parallelCellFeasible a H P h
  · simpa [hp] using continuous_cellSliceLength a H P R
  · simpa [hp] using (continuous_const : Continuous (fun _ : ℝ ↦ (0 : ℝ)))

lemma activeSliceLength_eq_frozen_of_stable {n : ℕ} (a : Real.Angle)
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (R h x : ℝ)
    (hstable : ∀ P : Fin n → Bool,
      parallelCellFeasible a H P x ↔ parallelCellFeasible a H P h) :
    activeSliceLength a E H i R x = frozenActiveSliceLength a E H i R h x := by
  classical
  unfold activeSliceLength frozenActiveSliceLength
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hp : parallelCellFeasible a H P h
  · have hpx := (hstable P).mpr hp
    simp [actualCellSliceLength, hp, hpx]
  · have hpx : ¬parallelCellFeasible a H P x := fun hx ↦ hp ((hstable P).mp hx)
    simp [actualCellSliceLength, hp, hpx]

lemma abs_frozenActiveSliceLength_sub_le {n : ℕ} (a : Real.Angle)
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (R h x z : ℝ) :
    |frozenActiveSliceLength a E H i R h x -
        frozenActiveSliceLength a E H i R h z| ≤
      ((activeBooleanPatterns E i).card : ℝ) * (2 * slopeBound a H) * |x - z| := by
  classical
  unfold frozenActiveSliceLength
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ P ∈ activeBooleanPatterns E i,
        ((if parallelCellFeasible a H P h then cellSliceLength a H P R x else 0) -
          if parallelCellFeasible a H P h then cellSliceLength a H P R z else 0)| ≤
        ∑ P ∈ activeBooleanPatterns E i,
          |(if parallelCellFeasible a H P h then cellSliceLength a H P R x else 0) -
            if parallelCellFeasible a H P h then cellSliceLength a H P R z else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _P ∈ activeBooleanPatterns E i,
        (2 * slopeBound a H) * |x - z| := by
      apply Finset.sum_le_sum
      intro P hP
      by_cases hp : parallelCellFeasible a H P h
      · simpa [hp] using abs_cellSliceLength_sub_le a H P R x z
      · simp only [hp, ↓reduceIte, sub_self, abs_zero]
        exact mul_nonneg (mul_nonneg (by norm_num) (slopeBound_nonneg a H))
          (abs_nonneg _)
    _ = ((activeBooleanPatterns E i).card : ℝ) * (2 * slopeBound a H) *
        |x - z| := by
      simp
      ring

lemma volume_activeRegionSlice_toReal_eq_activeSliceLength {n : ℕ}
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (M R x : ℝ) (hxM : x ≤ M)
    (hx : noParallelBoundaryAt (H i).angle (auxiliaryHalfPlaneFamily H i M) x) :
    (MeasureTheory.volume (activeRegionSlice (H i).angle E H i R x)).toReal =
      activeSliceLength (H i).angle E (auxiliaryHalfPlaneFamily H i M) i R x := by
  rw [measure_activeRegionSlice_eq_sum E H i M R x hxM]
  unfold activeSliceLength
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro P hP
    exact volume_booleanCellSlice_toReal_eq_actual _ _ _ _ _ hx
  · intro P hP
    apply ne_of_lt
    calc
      MeasureTheory.volume
          (booleanCellSlice (H i).angle (auxiliaryHalfPlaneFamily H i M) P R x) ≤
          MeasureTheory.volume (Set.Icc (-R) R) :=
        MeasureTheory.measure_mono Set.inter_subset_right
      _ = ENNReal.ofReal (R - -R) := Real.volume_Icc
      _ < ⊤ := ENNReal.ofReal_lt_top

end MovingSofa.Nef

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
# Polygon / Nef / Variation / Area
-/

@[expose] public section

noncomputable section

namespace MovingSofa.Nef

open Filter Topology

lemma volume_perturbSdiff_toReal_eq_integral_slice {n : ℕ}
    {E : BooleanFunction n} (hE : IsMonotoneBooleanFunction E)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hSide : (H i).upper = false) (R ε₀ δ ε : ℝ) (hδ : |δ| ≤ ε₀)
    (hBound : ∀ z : ℝ, |z| ≤ ε₀ →
      perturbNefHeight E H i z ⊆ Metric.closedBall 0 R) :
    (MeasureTheory.volume
      (perturbNefHeight E H i δ \ perturbNefHeight E H i ε)).toReal =
      ∫ x in heightInterval (H i).strict (H i).height δ ε,
        (MeasureTheory.volume
          (activeRegionSlice (H i).angle E H i R x)).toReal := by
  let S := perturbNefHeight E H i δ \ perturbNefHeight E H i ε
  have hS : MeasurableSet S :=
    MeasurableSet.diff (measurableSet_perturbNefHeight E H i δ)
      (measurableSet_perturbNefHeight E H i ε)
  have hSfinite : MeasureTheory.volume S ≠ ⊤ := by
    apply ne_of_lt
    calc
      MeasureTheory.volume S ≤ MeasureTheory.volume (perturbNefHeight E H i δ) :=
        MeasureTheory.measure_mono Set.sdiff_subset
      _ ≤ MeasureTheory.volume (Metric.closedBall (0 : Point) R) :=
        MeasureTheory.measure_mono (hBound δ hδ)
      _ < ⊤ := MeasureTheory.measure_closedBall_lt_top
  rw [show (MeasureTheory.volume S).toReal =
      ∫ x : ℝ, (MeasureTheory.volume
        {y : ℝ | framePoint (H i).angle x y ∈ S}).toReal by
    exact volume_toReal_eq_integral_frameSlice (H i).angle hS hSfinite]
  rw [← MeasureTheory.integral_indicator
    (measurableSet_heightInterval (H i).strict (H i).height δ ε)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ heightInterval (H i).strict (H i).height δ ε
  · rw [(frameSlice_perturbSdiff_eq hE H i hSide R ε₀ δ ε x hδ hBound).1 hx]
    simp [hx]
  · rw [(frameSlice_perturbSdiff_eq hE H i hSide R ε₀ δ ε x hδ hBound).2 hx]
    simp [hx]

lemma area_perturb_sub_eq_integral_activeSliceLength {n : ℕ}
    {E : BooleanFunction n} (hE : IsMonotoneBooleanFunction E)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hSide : (H i).upper = false) (R ε₀ M δ ε : ℝ)
    (hεδ : ε ≤ δ) (hδ : |δ| ≤ ε₀) (hε : |ε| ≤ ε₀)
    (hBound : ∀ z : ℝ, |z| ≤ ε₀ →
      perturbNefHeight E H i z ⊆ Metric.closedBall 0 R)
    (hxM : ∀ x ∈ heightInterval (H i).strict (H i).height δ ε, x ≤ M)
    (hxregular : ∀ x ∈ heightInterval (H i).strict (H i).height δ ε,
      noParallelBoundaryAt (H i).angle (auxiliaryHalfPlaneFamily H i M) x) :
    ClassicalResults.area (perturbNefHeight E H i δ) -
        ClassicalResults.area (perturbNefHeight E H i ε) =
      ∫ x in heightInterval (H i).strict (H i).height δ ε,
        activeSliceLength (H i).angle E (auxiliaryHalfPlaneFamily H i M) i R x := by
  rw [area_perturb_sub_eq_volume_sdiff hE H i hSide R ε₀ δ ε hεδ hδ hε hBound,
    volume_perturbSdiff_toReal_eq_integral_slice hE H i hSide R ε₀ δ ε hδ hBound]
  apply MeasureTheory.setIntegral_congr_fun
    (measurableSet_heightInterval (H i).strict (H i).height δ ε)
  intro x hx
  exact volume_activeRegionSlice_toReal_eq_activeSliceLength E H i M R x
    (hxM x hx) (hxregular x hx)

lemma area_perturb_sub_eq_intervalIntegral_activeSliceLength {n : ℕ}
    {E : BooleanFunction n} (hE : IsMonotoneBooleanFunction E)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hSide : (H i).upper = false) (R ε₀ M ρ : ℝ)
    (hε₀ : 0 < ε₀) (hρ : 0 < ρ)
    (hM : (H i).height + ε₀ ≤ M)
    (hBound : ∀ z : ℝ, |z| ≤ ε₀ →
      perturbNefHeight E H i z ⊆ Metric.closedBall 0 R)
    (hregular : ∀ x, |x - (H i).height| ≤ ρ →
      noParallelBoundaryAt (H i).angle (auxiliaryHalfPlaneFamily H i M) x) :
    ∀ δ : ℝ, |δ| ≤ min ε₀ ρ →
      ClassicalResults.area (perturbNefHeight E H i δ) -
          ClassicalResults.area (perturbNefHeight E H i 0) =
        ∫ x in (H i).height..(H i).height + δ,
          activeSliceLength (H i).angle E
            (auxiliaryHalfPlaneFamily H i M) i R x := by
  intro δ hδ
  have hδε₀ : |δ| ≤ ε₀ := hδ.trans (min_le_left _ _)
  have hδρ : |δ| ≤ ρ := hδ.trans (min_le_right _ _)
  have hzero : |(0 : ℝ)| ≤ ε₀ := by simpa using hε₀.le
  by_cases hδ0 : 0 ≤ δ
  · have hformula := area_perturb_sub_eq_integral_activeSliceLength
      hE H i hSide R ε₀ M δ 0 hδ0 hδε₀ hzero hBound
      (fun x hx ↦ by
        have hxb := mem_heightInterval_bounds hx
        linarith [le_abs_self δ])
      (fun x hx ↦ by
        apply hregular
        have hxb := mem_heightInterval_bounds hx
        rw [abs_le]
        constructor <;> linarith [le_abs_self δ, neg_le_abs δ])
    rw [integral_heightInterval_eq_intervalIntegral _ _ _ _ _ hδ0] at hformula
    simpa using hformula
  · have hδle : δ ≤ 0 := le_of_not_ge hδ0
    have hformula := area_perturb_sub_eq_integral_activeSliceLength
      hE H i hSide R ε₀ M 0 δ hδle hzero hδε₀ hBound
      (fun x hx ↦ by
        have hxb := mem_heightInterval_bounds hx
        linarith)
      (fun x hx ↦ by
        apply hregular
        have hxb := mem_heightInterval_bounds hx
        rw [abs_le]
        constructor <;> linarith [le_abs_self δ, neg_le_abs δ])
    rw [integral_heightInterval_eq_intervalIntegral _ _ _ _ _ hδle] at hformula
    simp only [add_zero] at hformula
    rw [intervalIntegral.integral_symm] at hformula
    linarith

lemma area_perturb_remainder_le {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (hSide : (H i).upper = false) (R ε₀ M ρ : ℝ)
    (hε₀ : 0 < ε₀) (hρ : 0 < ρ) (hM : (H i).height + ε₀ ≤ M)
    (hBound : ∀ z : ℝ, |z| ≤ ε₀ →
      perturbNefHeight E H i z ⊆ Metric.closedBall 0 R)
    (hstable : ∀ x, |x - (H i).height| ≤ ρ →
      noParallelBoundaryAt (H i).angle (auxiliaryHalfPlaneFamily H i M) x ∧
        ∀ P : Fin n → Bool,
          (parallelCellFeasible (H i).angle (auxiliaryHalfPlaneFamily H i M) P x ↔
            parallelCellFeasible (H i).angle (auxiliaryHalfPlaneFamily H i M) P
              (H i).height)) :
    ∀ δ : ℝ, |δ| ≤ min ε₀ ρ →
      |ClassicalResults.area (perturbNefHeight E H i δ) -
          ClassicalResults.area (perturbNefHeight E H i 0) -
          activeSliceLength (H i).angle E (auxiliaryHalfPlaneFamily H i M) i R
            (H i).height * δ| ≤
        (((activeBooleanPatterns E i).card : ℝ) *
          (2 * slopeBound (H i).angle (auxiliaryHalfPlaneFamily H i M))) * δ ^ 2 := by
  intro δ hδ
  let a := (H i).angle
  let h := (H i).height
  let G := frozenActiveSliceLength a E (auxiliaryHalfPlaneFamily H i M) i R h
  let L := ((activeBooleanPatterns E i).card : ℝ) *
    (2 * slopeBound a (auxiliaryHalfPlaneFamily H i M))
  have hδρ : |δ| ≤ ρ := hδ.trans (min_le_right _ _)
  have harea := area_perturb_sub_eq_intervalIntegral_activeSliceLength
    hE H i hSide R ε₀ M ρ hε₀ hρ hM hBound (fun x hx ↦ (hstable x hx).1) δ hδ
  have hGh : activeSliceLength a E (auxiliaryHalfPlaneFamily H i M) i R h = G h := by
    apply activeSliceLength_eq_frozen_of_stable
    intro P
    rfl
  have hFG : (∫ x in h..h + δ,
      activeSliceLength a E (auxiliaryHalfPlaneFamily H i M) i R x) =
      ∫ x in h..h + δ, G x := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply activeSliceLength_eq_frozen_of_stable
    apply (hstable x ?_).2
    rw [abs_le]
    rcases Set.mem_uIcc.mp hx with hx | hx <;>
      constructor <;> linarith [le_abs_self δ, neg_le_abs δ]
  rw [show (H i).angle = a by rfl, show (H i).height = h by rfl] at harea ⊢
  rw [hFG] at harea
  rw [hGh]
  have hGint : IntervalIntegrable G MeasureTheory.volume h (h + δ) :=
    (continuous_frozenActiveSliceLength a E
      (auxiliaryHalfPlaneFamily H i M) i R h).intervalIntegrable h (h + δ)
  have hcint : IntervalIntegrable (fun _ : ℝ ↦ G h) MeasureTheory.volume h (h + δ) :=
    continuous_const.intervalIntegrable h (h + δ)
  have hremainder :
      ClassicalResults.area (perturbNefHeight E H i δ) -
          ClassicalResults.area (perturbNefHeight E H i 0) - G h * δ =
        ∫ x in h..h + δ, (G x - G h) := by
    rw [intervalIntegral.integral_sub hGint hcint,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    rw [← harea]
    ring
  have hL : 0 ≤ L :=
    mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (by norm_num) (slopeBound_nonneg _ _))
  rw [hremainder, ← Real.norm_eq_abs]
  calc
    ‖∫ x in h..h + δ, (G x - G h)‖ ≤ (L * |δ|) * |(h + δ) - h| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Real.norm_eq_abs]
      calc
        |G x - G h| ≤ L * |x - h| := by
          exact abs_frozenActiveSliceLength_sub_le a E
            (auxiliaryHalfPlaneFamily H i M) i R h x h
        _ ≤ L * |δ| := by
          apply mul_le_mul_of_nonneg_left _ hL
          rw [abs_le]
          rcases Set.mem_uIoc.mp hx with hx | hx <;>
            constructor <;> linarith [le_abs_self δ, neg_le_abs δ]
    _ = L * δ ^ 2 := by
      rw [show (h + δ) - h = δ by ring]
      calc
        L * |δ| * |δ| = L * |δ| ^ 2 := by ring
        _ = L * δ ^ 2 := by rw [sq_abs]
    _ = (((activeBooleanPatterns E i).card : ℝ) *
          (2 * slopeBound a (auxiliaryHalfPlaneFamily H i M))) * δ ^ 2 := rfl

end MovingSofa.Nef

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
# Polygon / Nef / Variation / Boundary
-/

@[expose] public section

noncomputable section

namespace MovingSofa.Nef

open Filter Topology

lemma tendsto_sub_one_div_normalVector (p : Point) (a : Real.Angle) :
    Filter.Tendsto
      (fun k : ℕ ↦ p - (1 / ((k + 1 : ℕ) : ℝ)) • normalVector a)
      Filter.atTop (𝓝 p) := by
  simpa using tendsto_const_nhds.sub
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const
      (normalVector a))

lemma tendsto_add_one_div_normalVector (p : Point) (a : Real.Angle) :
    Filter.Tendsto
      (fun k : ℕ ↦ p + (1 / ((k + 1 : ℕ) : ℝ)) • normalVector a)
      Filter.atTop (𝓝 p) := by
  simpa using tendsto_const_nhds.add
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const
      (normalVector a))

lemma sub_smul_normalVector_mem_carrier (H : PlanarHalfPlaneData)
    (hupper : H.upper = false) {p : Point} (hp : p ∈ H.boundaryLine)
    {t : ℝ} (ht : 0 < t) :
    p - t • normalVector H.angle ∈ H.carrier := by
  change inner ℝ p (normalVector H.angle) = H.height at hp
  rw [PlanarHalfPlaneData.carrier, normalHalfPlane, hupper]
  simp only [Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq]
  rw [inner_sub_left, real_inner_smul_left, hp]
  rw [show inner ℝ (normalVector H.angle) (normalVector H.angle) = 1 by
    simpa using inner_normalVector_self H.angle.toReal]
  cases H.strict <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith

lemma add_smul_normalVector_not_mem_carrier (H : PlanarHalfPlaneData)
    (hupper : H.upper = false) {p : Point} (hp : p ∈ H.boundaryLine)
    {t : ℝ} (ht : 0 < t) :
    p + t • normalVector H.angle ∉ H.carrier := by
  change inner ℝ p (normalVector H.angle) = H.height at hp
  rw [PlanarHalfPlaneData.carrier, normalHalfPlane, hupper]
  simp only [Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq]
  rw [inner_add_left, real_inner_smul_left, hp]
  rw [show inner ℝ (normalVector H.angle) (normalVector H.angle) = 1 by
    simpa using inner_normalVector_self H.angle.toReal]
  cases H.strict <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith

lemma mem_frontier_booleanSet_of_active {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hupper : (H i).upper = false) (p : Point)
    (hline : p ∈ (H i).boundaryLine)
    (hother : ∀ j, j ≠ i → p ∉ (H j).boundaryLine)
    (hactive : IsActiveBooleanPattern E i
      (setMembershipPattern (fun j ↦ (H j).carrier) p)) :
    p ∈ frontier (booleanSet E (fun j ↦ (H j).carrier)) := by
  let P := setMembershipPattern (fun j ↦ (H j).carrier) p
  let qminus : ℕ → Point := fun k ↦
    p - (1 / ((k + 1 : ℕ) : ℝ)) • normalVector (H i).angle
  let qplus : ℕ → Point := fun k ↦
    p + (1 / ((k + 1 : ℕ) : ℝ)) • normalVector (H i).angle
  have hminus_lim : Filter.Tendsto qminus Filter.atTop (𝓝 p) :=
    tendsto_sub_one_div_normalVector p (H i).angle
  have hplus_lim : Filter.Tendsto qplus Filter.atTop (𝓝 p) :=
    tendsto_add_one_div_normalVector p (H i).angle
  have hlocal := eventually_setMembershipPattern_eq_of_ne H i p hother
  have hminus_local : ∀ᶠ k in Filter.atTop, ∀ j, j ≠ i →
      setMembershipPattern (fun r ↦ (H r).carrier) (qminus k) j = P j :=
    hminus_lim.eventually hlocal
  have hplus_local : ∀ᶠ k in Filter.atTop, ∀ j, j ≠ i →
      setMembershipPattern (fun r ↦ (H r).carrier) (qplus k) j = P j :=
    hplus_lim.eventually hlocal
  have hminus_mem : ∀ᶠ k in Filter.atTop,
      qminus k ∈ booleanSet E (fun j ↦ (H j).carrier) := by
    filter_upwards [hminus_local] with k hk
    have hki : qminus k ∈ (H i).carrier :=
      sub_smul_normalVector_mem_carrier (H i) hupper hline (by positivity)
    have hpattern : setMembershipPattern (fun r ↦ (H r).carrier) (qminus k) =
        Function.update P i true := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [setMembershipPattern, hki]
      · simpa [Function.update_of_ne hji] using hk j hji
    change E (setMembershipPattern (fun r ↦ (H r).carrier) (qminus k)) = true
    rw [hpattern]
    exact hactive.2
  have hplus_mem : ∀ᶠ k in Filter.atTop,
      qplus k ∈ (booleanSet E (fun j ↦ (H j).carrier))ᶜ := by
    filter_upwards [hplus_local] with k hk
    have hki : qplus k ∉ (H i).carrier :=
      add_smul_normalVector_not_mem_carrier (H i) hupper hline (by positivity)
    have hpattern : setMembershipPattern (fun r ↦ (H r).carrier) (qplus k) =
        Function.update P i false := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [setMembershipPattern, hki]
      · simpa [Function.update_of_ne hji] using hk j hji
    change E (setMembershipPattern (fun r ↦ (H r).carrier) (qplus k)) ≠ true
    rw [hpattern, hactive.1]
    decide
  rw [frontier_eq_closure_inter_closure]
  exact ⟨mem_closure_of_tendsto hminus_lim hminus_mem,
    mem_closure_of_tendsto hplus_lim hplus_mem⟩

lemma not_mem_frontier_booleanSet_of_not_active {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (p : Point)
    (hother : ∀ j, j ≠ i → p ∉ (H j).boundaryLine)
    (hinactive : ¬IsActiveBooleanPattern E i
      (setMembershipPattern (fun j ↦ (H j).carrier) p)) :
    p ∉ frontier (booleanSet E (fun j ↦ (H j).carrier)) := by
  let P := setMembershipPattern (fun j ↦ (H j).carrier) p
  let X := booleanSet E (fun j ↦ (H j).carrier)
  have heq : E (Function.update P i false) = E (Function.update P i true) :=
    (not_isActiveBooleanPattern_iff hE i P).mp hinactive
  have hlocal := eventually_setMembershipPattern_eq_of_ne H i p hother
  have hevent : ∀ᶠ q in 𝓝 p,
      (q ∈ X ↔ E (Function.update P i false) = true) := by
    filter_upwards [hlocal] with q hq
    have hpattern : setMembershipPattern (fun r ↦ (H r).carrier) q =
        Function.update P i
          (setMembershipPattern (fun r ↦ (H r).carrier) q i) := by
      funext j
      by_cases hji : j = i
      · subst j
        simp
      · simpa [Function.update_of_ne hji] using hq j hji
    change (E (setMembershipPattern (fun r ↦ (H r).carrier) q) = true ↔ _)
    rw [hpattern]
    cases hqi : setMembershipPattern (fun r ↦ (H r).carrier) q i
    · rfl
    · simp [heq]
  cases hvalue : E (Function.update P i false)
  · have hcompl : Xᶜ ∈ 𝓝 p := by
      filter_upwards [hevent] with q hq
      simpa [hvalue] using hq
    have hinter : p ∈ interior Xᶜ := mem_interior_iff_mem_nhds.mpr hcompl
    have hpcompl : p ∈ Xᶜ := interior_subset hinter
    have hnot : p ∉ frontier Xᶜ :=
      (mem_interior_iff_notMem_frontier hpcompl).mp hinter
    simpa [X] using hnot
  · have hset : X ∈ 𝓝 p := by
      filter_upwards [hevent] with q hq
      simpa [hvalue] using hq
    have hinter : p ∈ interior X := mem_interior_iff_mem_nhds.mpr hset
    have hp : p ∈ X := interior_subset hinter
    exact (mem_interior_iff_notMem_frontier hp).mp hinter

lemma mem_frontier_booleanSet_iff_mem_activeBooleanRegion {n : ℕ}
    {E : BooleanFunction n} (hE : IsMonotoneBooleanFunction E)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hupper : (H i).upper = false) (p : Point)
    (hline : p ∈ (H i).boundaryLine)
    (hother : ∀ j, j ≠ i → p ∉ (H j).boundaryLine) :
    p ∈ frontier (booleanSet E (fun j ↦ (H j).carrier)) ↔
      p ∈ activeBooleanRegion E H i := by
  rw [mem_activeBooleanRegion_iff]
  constructor
  · intro hfrontier
    by_contra hinactive
    exact (not_mem_frontier_booleanSet_of_not_active hE H i p hother hinactive)
      hfrontier
  · intro hactive
    exact mem_frontier_booleanSet_of_active E H i hupper p hline hother hactive

/-- The truncated slice of the Boolean set’s frontier along a selected wall boundary. -/
def frontierLineSlice {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (R : ℝ) : Set ℝ :=
  {y | framePoint (H i).angle (H i).height y ∈
    frontier (booleanSet E (fun j ↦ (H j).carrier))} ∩ Set.Icc (-R) R

lemma volume_frontierLineSlice_eq_activeRegionSlice {n : ℕ}
    {E : BooleanFunction n} (hE : IsMonotoneBooleanFunction E)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hupper : (H i).upper = false) (M R : ℝ)
    (hno : noParallelBoundaryAt (H i).angle
      (auxiliaryHalfPlaneFamily H i M) (H i).height) :
    MeasureTheory.volume (frontierLineSlice E H i R) =
      MeasureTheory.volume (activeRegionSlice (H i).angle E H i R (H i).height) := by
  apply MeasureTheory.measure_congr
  rw [MeasureTheory.ae_eq_set]
  have hzero := (finite_cellSliceBoundaryExceptions (H i).angle
    (auxiliaryHalfPlaneFamily H i M) (H i).height hno).measure_zero
      MeasureTheory.volume
  have heq : ∀ y,
      y ∉ cellSliceBoundaryExceptions (H i).angle
          (auxiliaryHalfPlaneFamily H i M) (H i).height →
        (y ∈ frontierLineSlice E H i R ↔
          y ∈ activeRegionSlice (H i).angle E H i R (H i).height) := by
    intro y hy
    let p := framePoint (H i).angle (H i).height y
    have hline : p ∈ (H i).boundaryLine := by
      change inner ℝ p (normalVector (H i).angle) = (H i).height
      exact inner_framePoint_normalVector _ _ _
    have hother : ∀ j, j ≠ i → p ∉ (H j).boundaryLine := by
      intro j hji hj
      apply hy
      apply Set.mem_iUnion.mpr
      refine ⟨j, ?_⟩
      change inner ℝ p (normalVector (H j).angle) = (H j).height at hj
      simpa [p, auxiliaryHalfPlaneFamily_of_ne H i j M hji] using hj
    have hfrontier := mem_frontier_booleanSet_iff_mem_activeBooleanRegion
      hE H i hupper p hline hother
    constructor
    · rintro ⟨hyfrontier, hyR⟩
      exact ⟨hfrontier.mp hyfrontier, hyR⟩
    · rintro ⟨hyactive, hyR⟩
      exact ⟨hfrontier.mpr hyactive, hyR⟩
  constructor <;> apply MeasureTheory.measure_mono_null _ hzero
  · intro y hy
    by_contra hyexception
    exact hy.2 ((heq y hyexception).mp hy.1)
  · intro y hy
    by_contra hyexception
    exact hy.2 ((heq y hyexception).mpr hy.1)

lemma lineMap_framePoint (a : Real.Angle) (h y : ℝ) :
    AffineMap.lineMap (framePoint a h 0) (framePoint a h 1) y =
      framePoint a h y := by
  simp only [AffineMap.lineMap_apply_module', framePoint_eq, zero_smul,
    add_zero, one_smul]
  module

lemma dist_framePoint_zero_one (a : Real.Angle) (h : ℝ) :
    dist (framePoint a h 0) (framePoint a h 1) = 1 := by
  rw [dist_eq_norm]
  simp only [framePoint_eq, zero_smul, add_zero, one_smul]
  rw [show h • normalVector a - (h • normalVector a + tangentVector a) =
      -tangentVector a by module]
  simp [norm_tangentVector_angle]

lemma frontier_booleanSet_inter_boundaryLine_eq_image_frontierLineSlice {n : ℕ}
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (R : ℝ)
    (hBound : booleanSet E (fun j ↦ (H j).carrier) ⊆ Metric.closedBall 0 R) :
    frontier (booleanSet E (fun j ↦ (H j).carrier)) ∩ (H i).boundaryLine =
      AffineMap.lineMap
        (framePoint (H i).angle (H i).height 0)
        (framePoint (H i).angle (H i).height 1) ''
          frontierLineSlice E H i R := by
  ext p
  constructor
  · rintro ⟨hpfrontier, hpline⟩
    let y := inner ℝ p (tangentVector (H i).angle)
    have hpnormal : inner ℝ p (normalVector (H i).angle) = (H i).height := hpline
    have hparam : framePoint (H i).angle (H i).height y = p := by
      rw [framePoint_eq, ← hpnormal]
      exact inner_normalVector_smul_add_inner_tangentVector_smul p (H i).angle
    have hpball : p ∈ Metric.closedBall (0 : Point) R := by
      have hpclosure : p ∈ closure (booleanSet E (fun j ↦ (H j).carrier)) :=
        frontier_subset_closure hpfrontier
      exact (closure_minimal hBound Metric.isClosed_closedBall) hpclosure
    have hynorm := abs_real_inner_le_norm p (tangentVector (H i).angle)
    rw [norm_tangentVector_angle, mul_one] at hynorm
    have hpnorm : ‖p‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_left] using hpball
    have hyR : y ∈ Set.Icc (-R) R := abs_le.mp (hynorm.trans hpnorm)
    refine ⟨y, ⟨?_, ?_⟩⟩
    · exact ⟨by simpa [frontierLineSlice, hparam] using hpfrontier, hyR⟩
    · rw [lineMap_framePoint, hparam]
  · rintro ⟨y, hy, rfl⟩
    rw [lineMap_framePoint]
    refine ⟨hy.1, ?_⟩
    change inner ℝ (framePoint (H i).angle (H i).height y)
      (normalVector (H i).angle) = (H i).height
    exact inner_framePoint_normalVector _ _ _

lemma hausdorffMeasure_frontier_inter_boundaryLine_eq_volume_slice {n : ℕ}
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (R : ℝ)
    (hBound : booleanSet E (fun j ↦ (H j).carrier) ⊆ Metric.closedBall 0 R) :
    MeasureTheory.Measure.hausdorffMeasure 1
        (frontier (booleanSet E (fun j ↦ (H j).carrier)) ∩ (H i).boundaryLine) =
      MeasureTheory.volume (frontierLineSlice E H i R) := by
  rw [frontier_booleanSet_inter_boundaryLine_eq_image_frontierLineSlice
    E H i R hBound, MeasureTheory.hausdorffMeasure_lineMap_image,
    MeasureTheory.hausdorffMeasure_real]
  have hdist := dist_framePoint_zero_one (H i).angle (H i).height
  have hnndist : nndist
      (framePoint (H i).angle (H i).height 0)
      (framePoint (H i).angle (H i).height 1) = 1 := by
    apply NNReal.eq
    simpa using hdist
  rw [hnndist, one_smul]

lemma hausdorffMeasure_frontier_toReal_eq_activeSliceLength {n : ℕ}
    {E : BooleanFunction n} (hE : IsMonotoneBooleanFunction E)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hupper : (H i).upper = false) (M R : ℝ)
    (hM : (H i).height ≤ M)
    (hBound : booleanSet E (fun j ↦ (H j).carrier) ⊆ Metric.closedBall 0 R)
    (hno : noParallelBoundaryAt (H i).angle
      (auxiliaryHalfPlaneFamily H i M) (H i).height) :
    (MeasureTheory.Measure.hausdorffMeasure 1
      (frontier (booleanSet E (fun j ↦ (H j).carrier)) ∩
        (H i).boundaryLine)).toReal =
      activeSliceLength (H i).angle E
        (auxiliaryHalfPlaneFamily H i M) i R (H i).height := by
  rw [hausdorffMeasure_frontier_inter_boundaryLine_eq_volume_slice E H i R hBound,
    volume_frontierLineSlice_eq_activeRegionSlice hE H i hupper M R hno]
  exact volume_activeRegionSlice_toReal_eq_activeSliceLength E H i M R
    (H i).height hM hno

end MovingSofa.Nef

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
# Polygon / Nef / Variation
-/

@[expose] public section

noncomputable section

namespace MovingSofa

open Filter Topology
open Nef

theorem simpleNefPolygon_area_variation {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hE : IsMonotoneBooleanFunction E)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine))
    (hSide : (H i).upper = false) (R ε₀ : ℝ) (hR : 0 < R) (hε₀ : 0 < ε₀)
    (hBound : ∀ δ : ℝ, |δ| ≤ ε₀ →
      perturbNefHeight E H i δ ⊆ Metric.closedBall 0 R) :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ε ≤ ε₀ ∧
      ∀ δ : ℝ, |δ| ≤ ε →
        |ClassicalResults.area (perturbNefHeight E H i δ) -
          ClassicalResults.area (perturbNefHeight E H i 0) -
          (MeasureTheory.Measure.hausdorffMeasure 1
            (frontier (perturbNefHeight E H i 0) ∩ (H i).boundaryLine)).toReal * δ| ≤
          C * δ ^ 2 := by
  let M := |(H i).height| + ε₀ + R + 1
  have hno : noParallelBoundaryAt (H i).angle
      (auxiliaryHalfPlaneFamily H i M) (H i).height := by
    exact noParallelBoundaryAt_auxiliary H i hLines R ε₀ hR hε₀
  rcases exists_parallel_stability_radius (H i).angle
      (auxiliaryHalfPlaneFamily H i M) (H i).height hno with
    ⟨ρ, hρ, hstable⟩
  let C := ((activeBooleanPatterns E i).card : ℝ) *
    (2 * slopeBound (H i).angle (auxiliaryHalfPlaneFamily H i M))
  let ε := min ε₀ ρ
  refine ⟨C, ε, ?_, ?_, ?_, ?_⟩
  · exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (by norm_num) (slopeBound_nonneg _ _))
  · exact lt_min hε₀ hρ
  · exact min_le_left _ _
  · intro δ hδ
    have hM : (H i).height + ε₀ ≤ M := by
      dsimp [M]
      linarith [le_abs_self (H i).height]
    have hzero : |(0 : ℝ)| ≤ ε₀ := by simpa using hε₀.le
    have hBoundZero := hBound 0 hzero
    rw [perturbNefHeight_zero] at hBoundZero
    have hcoefficient :
        (MeasureTheory.Measure.hausdorffMeasure 1
          (frontier (perturbNefHeight E H i 0) ∩ (H i).boundaryLine)).toReal =
        activeSliceLength (H i).angle E
          (auxiliaryHalfPlaneFamily H i M) i R (H i).height := by
      rw [perturbNefHeight_zero]
      exact hausdorffMeasure_frontier_toReal_eq_activeSliceLength
        hE H i hSide M R (le_trans (le_add_of_nonneg_right hε₀.le) hM)
          hBoundZero hno
    have hremainder := area_perturb_remainder_le hE H i hSide R ε₀ M ρ
      hε₀ hρ hM hBound hstable δ hδ
    rw [hcoefficient]
    exact hremainder

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
# Polygon / Nef / Signed Variation
-/

@[expose] public section

noncomputable section
namespace MovingSofa

private def PlanarHalfPlaneData.reverseOrientation
    (H : PlanarHalfPlaneData) : PlanarHalfPlaneData :=
  ⟨H.angle + ((Real.pi : ℝ) : Real.Angle), -H.height, !H.upper, H.strict⟩

private theorem PlanarHalfPlaneData.carrier_reverseOrientation (H : PlanarHalfPlaneData) :
    H.reverseOrientation.carrier = H.carrier := by
  ext p
  simp only [reverseOrientation, carrier, normalHalfPlane, Set.mem_ofPred_eq,
    normalVector_add_pi_angle, inner_neg_right]
  cases H.upper <;> cases H.strict <;> simp

private theorem PlanarHalfPlaneData.boundaryLine_reverseOrientation (H : PlanarHalfPlaneData) :
    H.reverseOrientation.boundaryLine = H.boundaryLine := by
  ext p
  simp [reverseOrientation, boundaryLine, normalLine, normalVector_add_pi_angle]

private theorem PlanarHalfPlaneData.carrier_reverseOrientation_add_height
    (H : PlanarHalfPlaneData) (δ : ℝ) :
    ({H.reverseOrientation with height := H.reverseOrientation.height + δ}).carrier =
      ({H with height := H.height + -δ}).carrier := by
  have heq : {H.reverseOrientation with height := H.reverseOrientation.height + δ} =
      ({H with height := H.height + -δ}).reverseOrientation := by
    cases H
    simp [reverseOrientation, add_comm]
  rw [heq, carrier_reverseOrientation]

private theorem perturbNefHeight_reverseOrientation {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (δ : ℝ) :
    perturbNefHeight E (fun j ↦ (H j).reverseOrientation) i δ =
      perturbNefHeight E H i (-δ) := by
  unfold perturbNefHeight
  congr 1
  funext j
  split_ifs
  · exact PlanarHalfPlaneData.carrier_reverseOrientation_add_height _ _
  · exact PlanarHalfPlaneData.carrier_reverseOrientation _

/-- Quadratic area variation when the moved half-plane is a lower constraint. -/
theorem simpleNefPolygon_area_variation_lower {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hE : IsMonotoneBooleanFunction E)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine))
    (hSide : (H i).upper = true) (R ε₀ : ℝ) (hR : 0 < R) (hε₀ : 0 < ε₀)
    (hBound : ∀ δ : ℝ, |δ| ≤ ε₀ →
      perturbNefHeight E H i δ ⊆ Metric.closedBall 0 R) :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ε ≤ ε₀ ∧
      ∀ δ : ℝ, |δ| ≤ ε →
        |ClassicalResults.area (perturbNefHeight E H i δ) -
          ClassicalResults.area (perturbNefHeight E H i 0) +
          (MeasureTheory.Measure.hausdorffMeasure 1
            (frontier (perturbNefHeight E H i 0) ∩ (H i).boundaryLine)).toReal * δ| ≤
          C * δ ^ 2 := by
  have hLines' : Function.Injective (fun j ↦ (H j).reverseOrientation.boundaryLine) := by
    simpa only [PlanarHalfPlaneData.boundaryLine_reverseOrientation] using hLines
  have hSide' : (H i).reverseOrientation.upper = false := by
    simp [PlanarHalfPlaneData.reverseOrientation, hSide]
  obtain ⟨C, ε, hC, hε, hε₀', h⟩ := simpleNefPolygon_area_variation E
    (fun j ↦ (H j).reverseOrientation) i hE hLines' hSide' R ε₀ hR hε₀ (by
      intro δ hδ
      rw [perturbNefHeight_reverseOrientation]
      exact hBound (-δ) (by simpa only [abs_neg] using hδ))
  refine ⟨C, ε, hC, hε, hε₀', fun δ hδ ↦ ?_⟩
  have hb := h (-δ) (by simpa only [abs_neg] using hδ)
  simpa only [perturbNefHeight_reverseOrientation, neg_neg, neg_zero,
    PlanarHalfPlaneData.boundaryLine_reverseOrientation, mul_neg, sub_neg_eq_add,
    neg_sq] using hb
/-- Signed quadratic area variation for either orientation of a simple Nef wall. -/
theorem simpleNefPolygon_area_variation_signed {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hE : IsMonotoneBooleanFunction E)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine))
    (R ε₀ : ℝ) (hR : 0 < R) (hε₀ : 0 < ε₀)
    (hBound : ∀ δ : ℝ, |δ| ≤ ε₀ →
      perturbNefHeight E H i δ ⊆ Metric.closedBall 0 R) :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ε ≤ ε₀ ∧
      ∀ δ : ℝ, |δ| ≤ ε →
        |ClassicalResults.area (perturbNefHeight E H i δ) -
          ClassicalResults.area (perturbNefHeight E H i 0) -
          (if (H i).upper then -1 else 1) *
            (MeasureTheory.Measure.hausdorffMeasure 1
              (frontier (perturbNefHeight E H i 0) ∩ (H i).boundaryLine)).toReal * δ| ≤
          C * δ ^ 2 := by
  cases hs : (H i).upper
  · simpa only [hs, Bool.false_eq_true, ite_false, one_mul] using
      simpleNefPolygon_area_variation E H i hE hLines hs R ε₀ hR hε₀ hBound
  · simpa only [hs, ite_true, neg_one_mul, neg_mul, one_mul, sub_neg_eq_add] using
      simpleNefPolygon_area_variation_lower E H i hE hLines hs R ε₀ hR hε₀ hBound

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
# Polygon / Height / Wall Variation
-/

@[expose] public section

noncomputable section
namespace MovingSofa

private theorem endpoint_wall_changes_disjoint (a : Real.Angle) (h ε : ℝ)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1) (p : Point) :
    (p ∈ normalHalfPlane a (h + ε) false false ↔
      p ∈ normalHalfPlane a h false false) ∨
    (p ∈ normalHalfPlane a (h - 1 + ε) true false ↔
      p ∈ normalHalfPlane a (h - 1) true false) := by
  change (inner ℝ p (normalVector a) ≤ h + ε ↔ inner ℝ p (normalVector a) ≤ h) ∨
    (h - 1 + ε ≤ inner ℝ p (normalVector a) ↔ h - 1 ≤ inner ℝ p (normalVector a))
  by_cases hp : inner ℝ p (normalVector a) ≤ h
  · left
    constructor <;> intro _ <;> linarith
  · right
    constructor <;> intro _ <;> linarith

private theorem area_add_of_indicator_add_eq (A B C D : Set Point)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hAfin : MeasureTheory.volume A ≠ ⊤) (hBfin : MeasureTheory.volume B ≠ ⊤)
    (hCfin : MeasureTheory.volume C ≠ ⊤) (hDfin : MeasureTheory.volume D ≠ ⊤)
    (h : ∀ p, A.indicator (fun _ ↦ (1 : ℝ)) p + B.indicator (fun _ ↦ (1 : ℝ)) p =
      C.indicator (fun _ ↦ (1 : ℝ)) p + D.indicator (fun _ ↦ (1 : ℝ)) p) :
    ClassicalResults.area A + ClassicalResults.area B =
      ClassicalResults.area C + ClassicalResults.area D := by
  have hint (S : Set Point) (hm : MeasurableSet S) (hf : MeasureTheory.volume S ≠ ⊤) :
      MeasureTheory.Integrable (S.indicator (fun _ ↦ (1 : ℝ))) :=
    (MeasureTheory.integrableOn_const hf).integrable_indicator hm
  have heq := congrArg (fun f : Point → ℝ ↦ ∫ p, f p) (funext h)
  rw [MeasureTheory.integral_add (hint A hA hAfin) (hint B hB hBfin),
    MeasureTheory.integral_add (hint C hC hCfin) (hint D hD hDfin)] at heq
  have harea (S : Set Point) (hm : MeasurableSet S) :
      (∫ p, S.indicator (fun _ ↦ (1 : ℝ)) p) = ClassicalResults.area S :=
    MeasureTheory.integral_indicator_one hm
  simpa only [harea A hA, harea B hB, harea C hC, harea D hD] using heq
private def BooleanFunction.all (n : ℕ) : BooleanFunction n :=
  fun P ↦ decide (∀ i, P i = true)

private theorem BooleanFunction.all_monotone (n : ℕ) :
    IsMonotoneBooleanFunction (BooleanFunction.all n) := by
  intro P Q hPQ hP
  simp only [BooleanFunction.all, decide_eq_true_eq] at hP ⊢
  exact fun i ↦ hPQ i (hP i)

private theorem booleanSet_all {n : ℕ} (H : Fin n → Set Point) :
    booleanSet (BooleanFunction.all n) H = ⋂ i, H i := by
  classical
  ext p
  simp [booleanSet, BooleanFunction.all]

private theorem independentWallCap_eq_booleanSet {Θ : AngleSet}
    (h upper lower : PolygonHeightSpace Θ) {n : ℕ}
    (H : Fin n → PlanarHalfPlaneData) (hH : Set.range H = polygonCapWalls h)
    (F : PlanarHalfPlaneData → Set Point)
    (hupper : ∀ t ∈ angleDomain Θ,
      F ⟨(t : Real.Angle), polygonHeightValue h t, false, false⟩ =
        normalHalfPlane (t : Real.Angle) (polygonHeightValue upper t) false false)
    (hlower : ∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      F ⟨(t : Real.Angle), polygonHeightValue h t - 1, true, false⟩ =
        normalHalfPlane (t : Real.Angle) (polygonHeightValue lower t) true false) :
    independentWallCap upper lower =
      booleanSet (BooleanFunction.all n) (fun i ↦ F (H i)) := by
  rw [booleanSet_all]
  ext p
  have hrange : (∀ i, p ∈ F (H i)) ↔ ∀ W ∈ polygonCapWalls h, p ∈ F W := by
    rw [← hH]
    simp
  simp only [Set.mem_iInter]
  rw [hrange]
  simp only [independentWallCap, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · rintro ⟨hend, hint⟩ W hW
    rcases hW with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · rw [hupper t ht]
      rcases ht with ht | ht
      · exact hint t ht
      · exact (hend t ht).1
    · rw [hlower t ht]
      exact (hend t ht).2
  · intro hall
    constructor
    · intro t ht
      constructor
      · rw [← hupper t (Or.inr ht)]
        exact hall _ (Or.inl ⟨t, Or.inr ht, rfl⟩)
      · rw [← hlower t ht]
        exact hall _ (Or.inr ⟨t, ht, rfl⟩)
    · intro t ht
      rw [← hupper t (Or.inl ht)]
      exact hall _ (Or.inl ⟨t, Or.inl ht, rfl⟩)

private def BooleanFunction.niche (Θ : AngleSet) {n : ℕ}
    (endpoint : {t : ℝ // t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)} → Fin n)
    (left right : {t : ℝ // t ∈ Θ.directions} → Fin n) : BooleanFunction n := by
  classical
  exact fun P ↦ decide ((∀ t, P (endpoint t) = true) ∧
    ∃ t, P (left t) = true ∧ P (right t) = true)

private theorem BooleanFunction.niche_monotone (Θ : AngleSet) {n : ℕ}
    (endpoint : {t : ℝ // t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)} → Fin n)
    (left right : {t : ℝ // t ∈ Θ.directions} → Fin n) :
    IsMonotoneBooleanFunction (BooleanFunction.niche Θ endpoint left right) := by
  classical
  intro P Q hPQ hP
  simp only [BooleanFunction.niche, decide_eq_true_eq] at hP ⊢
  obtain ⟨he, t, hl, hr⟩ := hP
  exact ⟨fun s ↦ hPQ _ (he s), t, hPQ _ hl, hPQ _ hr⟩

private theorem independentWallNiche_eq_booleanSet {Θ : AngleSet}
    (lower : PolygonHeightSpace Θ) {n : ℕ} (H : Fin n → Set Point)
    (endpoint : {t : ℝ // t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)} → Fin n)
    (left right : {t : ℝ // t ∈ Θ.directions} → Fin n)
    (he : ∀ t, H (endpoint t) =
      normalHalfPlane (t.val : Real.Angle) (polygonHeightValue lower t.val) true false)
    (hl : ∀ t, H (left t) =
      normalHalfPlane (t.val : Real.Angle) (polygonHeightValue lower t.val) false true)
    (hr : ∀ t, H (right t) =
      normalHalfPlane ((t.val + Real.pi / 2 : ℝ) : Real.Angle)
        (polygonHeightValue lower (t.val + Real.pi / 2)) false true) :
    independentWallNiche lower =
      booleanSet (BooleanFunction.niche Θ endpoint left right) H := by
  classical
  ext p
  simp only [independentWallNiche, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_iUnion, booleanSet, Set.mem_ofPred_eq, BooleanFunction.niche,
    decide_eq_true_eq, he, hl, hr]
  constructor
  · rintro ⟨he, t, ht, hl, hr⟩
    exact ⟨fun s ↦ he s.val s.property, ⟨t, ht⟩, hl, hr⟩
  · rintro ⟨he, t, hl, hr⟩
    exact ⟨fun s hs ↦ he ⟨s, hs⟩, t.val, t.property, hl, hr⟩

private theorem exists_polygonNiche_wall_indices {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonNicheWalls h) :
    ∃ (endpoint : {t : ℝ // t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)} → Fin n)
      (left right : {t : ℝ // t ∈ Θ.directions} → Fin n),
      (∀ t, H (endpoint t) =
        ⟨(t.val : Real.Angle), polygonHeightValue h t.val - 1, true, false⟩) ∧
      (∀ t, H (left t) =
        ⟨(t.val : Real.Angle), polygonHeightValue h t.val - 1, false, true⟩) ∧
      (∀ t, H (right t) =
        ⟨((t.val + Real.pi / 2 : ℝ) : Real.Angle),
          polygonHeightValue h (t.val + Real.pi / 2) - 1, false, true⟩) := by
  classical
  have hpre (W : PlanarHalfPlaneData) (hW : W ∈ polygonNicheWalls h) :
      ∃ i, H i = W := by
    change W ∈ Set.range H
    rwa [hH]
  have he (t : {t : ℝ // t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)}) :
      ∃ i, H i = ⟨(t.val : Real.Angle), polygonHeightValue h t.val - 1, true, false⟩ :=
    hpre _ (Or.inr ⟨t.val, t.property, rfl⟩)
  have hl (t : {t : ℝ // t ∈ Θ.directions}) :
      ∃ i, H i = ⟨(t.val : Real.Angle), polygonHeightValue h t.val - 1, false, true⟩ :=
    hpre _ (Or.inl ⟨t.val, Or.inl t.property, rfl⟩)
  have hr (t : {t : ℝ // t ∈ Θ.directions}) :
      ∃ i, H i = ⟨((t.val + Real.pi / 2 : ℝ) : Real.Angle),
        polygonHeightValue h (t.val + Real.pi / 2) - 1, false, true⟩ :=
    hpre _ (Or.inl ⟨t.val + Real.pi / 2, Or.inr ⟨t.val, t.property, rfl⟩, rfl⟩)
  choose endpoint he using he
  choose left hl using hl
  choose right hr using hr
  exact ⟨endpoint, left, right, he, hl, hr⟩

private def PlanarHalfPlaneData.moveWall (W : PlanarHalfPlaneData) (δ : ℝ)
    (V : PlanarHalfPlaneData) : PlanarHalfPlaneData := by
  classical
  exact if V = W then {V with height := V.height + δ} else V

private theorem perturbNefHeight_eq_moveWall {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (hH : Function.Injective H) (i : Fin n) (δ : ℝ) :
    perturbNefHeight E H i δ =
      booleanSet E (fun j ↦ ((H i).moveWall δ (H j)).carrier) := by
  classical
  unfold perturbNefHeight
  congr 1
  funext j
  simp only [PlanarHalfPlaneData.moveWall, hH.eq_iff]

/-- Angles in a polygon angle domain have distinct classes modulo a full turn. -/
theorem angleDomain_coe_injective (Θ : AngleSet) :
    Function.Injective (fun t : angleDomain Θ ↦ (t.val : Real.Angle)) := by
  intro s t hst
  apply Subtype.ext
  have hs := angleDomain_subset_Ioo Θ s.property
  have ht := angleDomain_subset_Ioo Θ t.property
  exact ((normalLine_eq_iff_of_mem_Ioo (c := 0) (d := 0) hs ht).mp
    (congrArg (fun a ↦ normalLine a 0) hst)).1

private theorem polygonHeightValue_update {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (t : angleDomain Θ) (δ : ℝ) (s : ℝ) (hs : s ∈ angleDomain Θ) :
    polygonHeightValue (Function.update h t (h t + δ)) s =
      polygonHeightValue h s + if s = t.val then δ else 0 := by
  classical
  by_cases hst : s = t.val
  · subst s
    simp [polygonHeightValue, Function.update]
  · have hne : (⟨s, hs⟩ : angleDomain Θ) ≠ t := by
      intro heq
      exact hst (congrArg Subtype.val heq)
    simp [polygonHeightValue, Function.update, hs, hst, hne]

private theorem perturbNefHeight_cap_upper {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonCapWalls h) (hHinj : Function.Injective H)
    (i : Fin n) (t : angleDomain Θ)
    (hi : H i = ⟨(t.val : Real.Angle), h t, false, false⟩) (δ : ℝ) :
    perturbNefHeight (BooleanFunction.all n) H i δ =
      independentWallCap (Function.update h t (h t + δ)) (fun s ↦ h s - 1) := by
  classical
  rw [perturbNefHeight_eq_moveWall _ _ hHinj]
  symm
  apply independentWallCap_eq_booleanSet h _ _ H hH
    (fun W ↦ ((H i).moveWall δ W).carrier)
  · intro s hs
    have heq : (⟨(s : Real.Angle), polygonHeightValue h s, false, false⟩ :
        PlanarHalfPlaneData) = H i ↔ s = t.val := by
      rw [hi]
      constructor
      · intro heq
        have ha := congrArg PlanarHalfPlaneData.angle heq
        exact congrArg Subtype.val (angleDomain_coe_injective Θ
          (a₁ := ⟨s, hs⟩) (a₂ := t) ha)
      · intro hst
        subst s
        simp [polygonHeightValue]
    simp only [PlanarHalfPlaneData.moveWall, heq, polygonHeightValue_update h t δ s hs]
    split_ifs with hst
    · rfl
    · simp only [add_zero]
      rfl
  · intro s hs
    have hsD : s ∈ angleDomain Θ := Or.inr hs
    have hne : (⟨(s : Real.Angle), polygonHeightValue h s - 1, true, false⟩ :
        PlanarHalfPlaneData) ≠ H i := by
      rw [hi]
      intro heq
      have hb := congrArg PlanarHalfPlaneData.upper heq
      cases hb
    simp only [PlanarHalfPlaneData.moveWall, hne, ite_false]
    simp [PlanarHalfPlaneData.carrier, polygonHeightValue, hsD]

private theorem perturbNefHeight_cap_lower {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonCapWalls h) (hHinj : Function.Injective H)
    (i : Fin n) (t : angleDomain Θ)
    (hi : H i = ⟨(t.val : Real.Angle), h t - 1, true, false⟩) (δ : ℝ) :
    perturbNefHeight (BooleanFunction.all n) H i δ =
      independentWallCap h (Function.update (fun s ↦ h s - 1) t (h t - 1 + δ)) := by
  classical
  rw [perturbNefHeight_eq_moveWall _ _ hHinj]
  symm
  apply independentWallCap_eq_booleanSet h _ _ H hH
    (fun W ↦ ((H i).moveWall δ W).carrier)
  · intro s hs
    have hne : (⟨(s : Real.Angle), polygonHeightValue h s, false, false⟩ :
        PlanarHalfPlaneData) ≠ H i := by
      rw [hi]
      intro heq
      have hb := congrArg PlanarHalfPlaneData.upper heq
      cases hb
    simp only [PlanarHalfPlaneData.moveWall, hne, ite_false]
    rfl
  · intro s hs
    have hsD : s ∈ angleDomain Θ := Or.inr hs
    have heq : (⟨(s : Real.Angle), polygonHeightValue h s - 1, true, false⟩ :
        PlanarHalfPlaneData) = H i ↔ s = t.val := by
      rw [hi]
      constructor
      · intro heq
        have ha := congrArg PlanarHalfPlaneData.angle heq
        exact congrArg Subtype.val (angleDomain_coe_injective Θ
          (a₁ := ⟨s, hsD⟩) (a₂ := t) ha)
      · intro hst
        subst s
        simp [polygonHeightValue]
    simp only [PlanarHalfPlaneData.moveWall, heq,
      polygonHeightValue_update (fun s ↦ h s - 1) t δ s hsD]
    split_ifs <;> simp [PlanarHalfPlaneData.carrier, polygonHeightValue, hsD]

private theorem polygonCap_singleWall_uniform_bounds {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    ∃ R ε₀ : ℝ, 0 < R ∧ 0 < ε₀ ∧
      ∀ (n : ℕ) (H : Fin n → PlanarHalfPlaneData),
        Set.range H = polygonCapWalls h → Function.Injective H →
        ∀ (i : Fin n) (t : angleDomain Θ),
          (H i = ⟨(t.val : Real.Angle), h t, false, false⟩ ∨
            H i = ⟨(t.val : Real.Angle), h t - 1, true, false⟩) →
          ∀ δ : ℝ, |δ| ≤ ε₀ →
            perturbNefHeight (BooleanFunction.all n) H i δ ⊆ Metric.closedBall 0 R := by
  classical
  obtain ⟨R, ε₀, hR, hε₀, hb⟩ := polygonPerturbation_uniform_bounds Θ h
  refine ⟨R, ε₀, hR, hε₀, ?_⟩
  intro n H hH hHinj i t hi δ hδ
  have hupdate (f : PolygonHeightSpace Θ) :
      ∀ s, |Function.update f t (f t + δ) s - f s| ≤ ε₀ := by
    intro s
    by_cases hst : s = t
    · subst s
      simpa [Function.update] using hδ
    · simp [Function.update, hst, le_of_lt hε₀]
  rcases hi with hi | hi
  · rw [perturbNefHeight_cap_upper h H hH hHinj i t hi δ]
    exact (hb _ _ (hupdate h) (by intro s; simpa using le_of_lt hε₀)).1
  · rw [perturbNefHeight_cap_lower h H hH hHinj i t hi δ]
    exact (hb _ _ (by intro s; simpa using le_of_lt hε₀)
      (hupdate (fun s ↦ h s - 1))).1

private theorem perturbNefHeight_niche {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hangle : Function.Injective (fun j ↦ (H j).angle))
    (endpoint : {t : ℝ // t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)} → Fin n)
    (left right : {t : ℝ // t ∈ Θ.directions} → Fin n)
    (he : ∀ t, H (endpoint t) =
      ⟨(t.val : Real.Angle), polygonHeightValue h t.val - 1, true, false⟩)
    (hl : ∀ t, H (left t) =
      ⟨(t.val : Real.Angle), polygonHeightValue h t.val - 1, false, true⟩)
    (hr : ∀ t, H (right t) =
      ⟨((t.val + Real.pi / 2 : ℝ) : Real.Angle),
        polygonHeightValue h (t.val + Real.pi / 2) - 1, false, true⟩)
    (i : Fin n) (t : angleDomain Θ) (hi : (H i).angle = (t.val : Real.Angle)) (δ : ℝ) :
    perturbNefHeight (BooleanFunction.niche Θ endpoint left right) H i δ =
      independentWallNiche (Function.update (fun s ↦ h s - 1) t (h t - 1 + δ)) := by
  classical
  have hwall (j : Fin n) (s : ℝ) (hs : s ∈ angleDomain Θ) (upper strict : Bool)
      (hj : H j = ⟨(s : Real.Angle), polygonHeightValue h s - 1, upper, strict⟩) :
      (if j = i then {H j with height := (H j).height + δ} else H j).carrier =
        normalHalfPlane (s : Real.Angle)
          (polygonHeightValue (Function.update (fun s ↦ h s - 1) t (h t - 1 + δ)) s)
          upper strict := by
    have hji : j = i ↔ s = t.val := by
      constructor
      · intro hji
        have ha : (s : Real.Angle) = (t.val : Real.Angle) := by
          rw [← hi, ← hji, hj]
        exact congrArg Subtype.val (angleDomain_coe_injective Θ
          (a₁ := ⟨s, hs⟩) (a₂ := t) ha)
      · intro hst
        apply hangle
        simp only [hj, hi, hst]
    simp only [hji, hj, polygonHeightValue_update (fun s ↦ h s - 1) t δ s hs]
    split_ifs <;> simp [PlanarHalfPlaneData.carrier, polygonHeightValue, hs]
  unfold perturbNefHeight
  symm
  apply independentWallNiche_eq_booleanSet _ _ endpoint left right
  · intro s
    exact hwall _ s.val (Or.inr s.property) true false (he s)
  · intro s
    exact hwall _ s.val (Or.inl (Or.inl s.property)) false true (hl s)
  · intro s
    exact hwall _ (s.val + Real.pi / 2)
      (Or.inl (Or.inr ⟨s.val, s.property, rfl⟩)) false true (hr s)

private theorem exists_angle_of_mem_polygonNicheWalls {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (W : PlanarHalfPlaneData) (hW : W ∈ polygonNicheWalls h) :
    ∃ s : angleDomain Θ, W.angle = (s.val : Real.Angle) ∧ W.height = h s - 1 := by
  rcases hW with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
  · refine ⟨⟨s, Or.inl hs⟩, rfl, ?_⟩
    simp [polygonHeightValue, show s ∈ angleDomain Θ from Or.inl hs]
  · refine ⟨⟨s, Or.inr hs⟩, rfl, ?_⟩
    simp [polygonHeightValue, show s ∈ angleDomain Θ from Or.inr hs]

private theorem polygonNicheWalls_angle_injective {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonNicheWalls h)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine)) :
    Function.Injective (fun j ↦ (H j).angle) := by
  intro i j hij
  obtain ⟨s, hs, hsheight⟩ := exists_angle_of_mem_polygonNicheWalls h
    (H i) (hH ▸ Set.mem_range_self i)
  obtain ⟨t, ht, htheight⟩ := exists_angle_of_mem_polygonNicheWalls h
    (H j) (hH ▸ Set.mem_range_self j)
  have hst : s = t := angleDomain_coe_injective Θ (hs.symm.trans (hij.trans ht))
  apply hLines
  simp only [PlanarHalfPlaneData.boundaryLine, hij, hsheight, htheight, hst]

private theorem exists_polygonNiche_perturbation_formula {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonNicheWalls h)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine)) :
    ∃ E : BooleanFunction n, IsMonotoneBooleanFunction E ∧
      ∀ i, ∃ t : angleDomain Θ, (H i).angle = (t.val : Real.Angle) ∧
        ∀ δ : ℝ, perturbNefHeight E H i δ =
          independentWallNiche (Function.update (fun s ↦ h s - 1) t (h t - 1 + δ)) := by
  obtain ⟨endpoint, left, right, he, hl, hr⟩ := exists_polygonNiche_wall_indices h H hH
  refine ⟨BooleanFunction.niche Θ endpoint left right,
    BooleanFunction.niche_monotone Θ endpoint left right, ?_⟩
  intro i
  obtain ⟨t, ht, _⟩ := exists_angle_of_mem_polygonNicheWalls h
    (H i) (hH ▸ Set.mem_range_self i)
  refine ⟨t, ht, fun δ ↦ ?_⟩
  exact perturbNefHeight_niche h H (polygonNicheWalls_angle_injective h H hH hLines)
    endpoint left right he hl hr i t ht δ

/-- The niche with every lower wall shifted by one is the height-defined niche. -/
theorem independentWallNiche_sub_one {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    independentWallNiche (fun s ↦ h s - 1) = polygonHeightNiche h := by
  have hv (s : ℝ) (hs : s ∈ angleDomain Θ) :
      polygonHeightValue (fun s ↦ h s - 1) s = polygonHeightValue h s - 1 := by
    simp [polygonHeightValue, hs]
  unfold independentWallNiche polygonHeightNiche polygonHeightFan
  congr 1
  · apply Set.iInter_congr
    intro s
    apply Set.iInter_congr
    intro hs
    rw [hv s (Or.inr hs)]
  · apply Set.iUnion_congr
    intro s
    apply Set.iUnion_congr
    intro hs
    rw [hv s (Or.inl (Or.inl hs)),
      hv (s + Real.pi / 2) (Or.inl (Or.inr ⟨s, hs, rfl⟩))]

private theorem exists_polygonNiche_stable_presentation {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonNicheWalls h)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine)) :
    ∃ (E : BooleanFunction n) (R ε₀ : ℝ),
      IsMonotoneBooleanFunction E ∧ 0 < R ∧ 0 < ε₀ ∧
      polygonHeightNiche h = booleanSet E (fun j ↦ (H j).carrier) ∧
      (∀ i, ∃ t : angleDomain Θ, (H i).angle = (t.val : Real.Angle) ∧
        ∀ δ : ℝ, perturbNefHeight E H i δ =
          independentWallNiche (Function.update (fun s ↦ h s - 1) t (h t - 1 + δ))) ∧
      ∀ i δ, |δ| ≤ ε₀ → perturbNefHeight E H i δ ⊆ Metric.closedBall 0 R := by
  classical
  obtain ⟨E, hE, htransport⟩ := exists_polygonNiche_perturbation_formula h H hH hLines
  obtain ⟨R, ε₀, hR, hε₀, hb⟩ := polygonPerturbation_uniform_bounds Θ h
  refine ⟨E, R, ε₀, hE, hR, hε₀, ?_, htransport, ?_⟩
  · have hW : (⟨(Θ.angle : Real.Angle), polygonHeightValue h Θ.angle - 1,
        true, false⟩ : PlanarHalfPlaneData) ∈ Set.range H := by
      rw [hH]
      exact Or.inr ⟨Θ.angle, by simp, rfl⟩
    obtain ⟨i, _⟩ := hW
    obtain ⟨t, _, ht⟩ := htransport i
    have hz := ht 0
    simpa [perturbNefHeight, independentWallNiche_sub_one] using hz.symm
  · intro i δ hδ
    obtain ⟨t, _, ht⟩ := htransport i
    rw [ht δ]
    apply (hb h _ (by intro s; simpa using le_of_lt hε₀) ?_).2
    intro s
    by_cases hst : s = t
    · subst s
      simpa [Function.update] using hδ
    · simp [Function.update, hst, le_of_lt hε₀]

end MovingSofa

namespace MovingSofa

/-- Quadratic area variation for any wall in a polygon-height niche presentation. -/
theorem polygonNiche_wall_area_variation {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonNicheWalls h)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine)) (i : Fin n) :
    ∃ (t : angleDomain Θ) (C η : ℝ), (H i).angle = (t.val : Real.Angle) ∧
      0 ≤ C ∧ 0 < η ∧ ∀ δ : ℝ, |δ| ≤ η →
        |ClassicalResults.area
            (independentWallNiche (Function.update (fun s ↦ h s - 1) t (h t - 1 + δ))) -
          ClassicalResults.area (polygonHeightNiche h) -
          (if (H i).upper then -1 else 1) *
            (MeasureTheory.Measure.hausdorffMeasure 1
              (frontier (polygonHeightNiche h) ∩ (H i).boundaryLine)).toReal * δ| ≤
          C * δ ^ 2 := by
  classical
  obtain ⟨E, R, ε₀, hE, hR, hε₀, hbase, htransport, hbound⟩ :=
    exists_polygonNiche_stable_presentation h H hH hLines
  obtain ⟨t, ht, hmove⟩ := htransport i
  have hz : perturbNefHeight E H i 0 = polygonHeightNiche h := by
    simpa [perturbNefHeight] using hbase.symm
  obtain ⟨C, η, hC, hη, _, hvar⟩ := simpleNefPolygon_area_variation_signed
    E H i hE hLines R ε₀ hR hε₀ (hbound i)
  refine ⟨t, C, η, ht, hC, hη, ?_⟩
  intro δ hδ
  have hv := hvar δ hδ
  rw [hz, hmove δ] at hv
  exact hv

end MovingSofa

namespace MovingSofa

/-- The cap with every lower endpoint wall shifted by one is the height-defined cap. -/
theorem independentWallCap_sub_one {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    independentWallCap h (fun s ↦ h s - 1) = polygonHeightCap h := by
  unfold independentWallCap polygonHeightCap polygonHeightParallelogram
  congr 1
  apply Set.iInter_congr
  intro s
  apply Set.iInter_congr
  intro hs
  have hsD : s ∈ angleDomain Θ := Or.inr hs
  simp [polygonHeightValue, hsD]

/-- Quadratic area variation for one upper wall of a polygon-height cap. -/
theorem polygonCap_upper_wall_area_variation {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonCapWalls h)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine))
    (i : Fin n) (t : angleDomain Θ)
    (hi : H i = ⟨(t.val : Real.Angle), h t, false, false⟩) :
    ∃ C η : ℝ, 0 ≤ C ∧ 0 < η ∧ ∀ δ : ℝ, |δ| ≤ η →
      |ClassicalResults.area
          (independentWallCap (Function.update h t (h t + δ)) (fun s ↦ h s - 1)) -
        ClassicalResults.area (polygonHeightCap h) -
        (MeasureTheory.Measure.hausdorffMeasure 1
          (frontier (polygonHeightCap h) ∩ (H i).boundaryLine)).toReal * δ| ≤
        C * δ ^ 2 := by
  classical
  have hHinj : Function.Injective H := by
    intro j k hjk
    exact hLines (congrArg PlanarHalfPlaneData.boundaryLine hjk)
  obtain ⟨R, ε₀, hR, hε₀, hbound⟩ := polygonCap_singleWall_uniform_bounds h
  have hmove := perturbNefHeight_cap_upper h H hH hHinj i t hi
  have hz : perturbNefHeight (BooleanFunction.all n) H i 0 = polygonHeightCap h := by
    rw [hmove 0]
    have hu : Function.update h t (h t + 0) = h := by
      funext s
      simp [Function.update]
      rintro rfl
      rfl
    rw [hu, independentWallCap_sub_one]
  obtain ⟨C, η, hC, hη, _, hvar⟩ := simpleNefPolygon_area_variation
    (BooleanFunction.all n) H i (BooleanFunction.all_monotone n) hLines
    (by rw [hi]) R ε₀ hR hε₀ (hbound n H hH hHinj i t (Or.inl hi))
  refine ⟨C, η, hC, hη, ?_⟩
  intro δ hδ
  have hv := hvar δ hδ
  rw [hz, hmove δ] at hv
  exact hv

end MovingSofa

namespace MovingSofa

/-- Quadratic area variation for one lower endpoint wall of a polygon-height cap. -/
theorem polygonCap_lower_wall_area_variation {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonCapWalls h)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine))
    (i : Fin n) (t : angleDomain Θ)
    (hi : H i = ⟨(t.val : Real.Angle), h t - 1, true, false⟩) :
    ∃ C η : ℝ, 0 ≤ C ∧ 0 < η ∧ ∀ δ : ℝ, |δ| ≤ η →
      |ClassicalResults.area
          (independentWallCap h (Function.update (fun s ↦ h s - 1) t (h t - 1 + δ))) -
        ClassicalResults.area (polygonHeightCap h) +
        (MeasureTheory.Measure.hausdorffMeasure 1
          (frontier (polygonHeightCap h) ∩ (H i).boundaryLine)).toReal * δ| ≤
        C * δ ^ 2 := by
  classical
  have hHinj : Function.Injective H := by
    intro j k hjk
    exact hLines (congrArg PlanarHalfPlaneData.boundaryLine hjk)
  obtain ⟨R, ε₀, hR, hε₀, hbound⟩ := polygonCap_singleWall_uniform_bounds h
  have hmove := perturbNefHeight_cap_lower h H hH hHinj i t hi
  have hz : perturbNefHeight (BooleanFunction.all n) H i 0 = polygonHeightCap h := by
    simpa [independentWallCap_sub_one] using hmove 0
  obtain ⟨C, η, hC, hη, _, hvar⟩ := simpleNefPolygon_area_variation_lower
    (BooleanFunction.all n) H i (BooleanFunction.all_monotone n) hLines
    (by rw [hi]) R ε₀ hR hε₀ (hbound n H hH hHinj i t (Or.inr hi))
  refine ⟨C, η, hC, hη, ?_⟩
  intro δ hδ
  have hv := hvar δ hδ
  rw [hz, hmove δ] at hv
  exact hv

end MovingSofa

namespace MovingSofa

private theorem mem_independentWallCap_congr {Θ : AngleSet}
    (upper upper' lower lower' : PolygonHeightSpace Θ) (p : Point)
    (hu : ∀ s : angleDomain Θ,
      (inner ℝ p (normalVector (s.val : Real.Angle)) ≤ upper s ↔
        inner ℝ p (normalVector (s.val : Real.Angle)) ≤ upper' s))
    (hl : ∀ s : angleDomain Θ,
      (lower s ≤ inner ℝ p (normalVector (s.val : Real.Angle)) ↔
        lower' s ≤ inner ℝ p (normalVector (s.val : Real.Angle)))) :
    p ∈ independentWallCap upper lower ↔ p ∈ independentWallCap upper' lower' := by
  have hu' (s : ℝ) (hs : s ∈ angleDomain Θ) :
      p ∈ normalHalfPlane (s : Real.Angle) (polygonHeightValue upper s) false false ↔
        p ∈ normalHalfPlane (s : Real.Angle) (polygonHeightValue upper' s) false false := by
    simpa [normalHalfPlane, polygonHeightValue, hs] using hu ⟨s, hs⟩
  have hl' (s : ℝ) (hs : s ∈ angleDomain Θ) :
      p ∈ normalHalfPlane (s : Real.Angle) (polygonHeightValue lower s) true false ↔
        p ∈ normalHalfPlane (s : Real.Angle) (polygonHeightValue lower' s) true false := by
    simpa [normalHalfPlane, polygonHeightValue, hs] using hl ⟨s, hs⟩
  simp only [independentWallCap, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · rintro ⟨he, hi⟩
    exact ⟨fun s hs ↦ ⟨(hu' s (Or.inr hs)).mp (he s hs).1,
      (hl' s (Or.inr hs)).mp (he s hs).2⟩,
      fun s hs ↦ (hu' s (Or.inl hs)).mp (hi s hs)⟩
  · rintro ⟨he, hi⟩
    exact ⟨fun s hs ↦ ⟨(hu' s (Or.inr hs)).mpr (he s hs).1,
      (hl' s (Or.inr hs)).mpr (he s hs).2⟩,
      fun s hs ↦ (hu' s (Or.inl hs)).mpr (hi s hs)⟩

private theorem independentWallCap_indicator_update_add {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (t : angleDomain Θ) (ε : ℝ)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1) (p : Point) :
    (independentWallCap (Function.update h t (h t + ε))
        (Function.update (fun s ↦ h s - 1) t (h t - 1 + ε))).indicator
        (fun _ ↦ (1 : ℝ)) p +
      (independentWallCap h (fun s ↦ h s - 1)).indicator (fun _ ↦ (1 : ℝ)) p =
      (independentWallCap (Function.update h t (h t + ε))
        (fun s ↦ h s - 1)).indicator (fun _ ↦ (1 : ℝ)) p +
      (independentWallCap h
        (Function.update (fun s ↦ h s - 1) t (h t - 1 + ε))).indicator
        (fun _ ↦ (1 : ℝ)) p := by
  classical
  have hsplit := endpoint_wall_changes_disjoint (t.val : Real.Angle) (h t) ε hε hε' p
  have hI (A B : Set Point) (hab : p ∈ A ↔ p ∈ B) :
      A.indicator (fun _ ↦ (1 : ℝ)) p = B.indicator (fun _ ↦ (1 : ℝ)) p := by
    by_cases ha : p ∈ A
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem (hab.mp ha)]
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem (fun hb ↦ ha (hab.mpr hb))]
  change (_ ↔ _) ∨ (_ ↔ _) at hsplit
  rcases hsplit with hu | hl
  · have hu' (s : angleDomain Θ) :
        inner ℝ p (normalVector (s.val : Real.Angle)) ≤ Function.update h t (h t + ε) s ↔
          inner ℝ p (normalVector (s.val : Real.Angle)) ≤ h s := by
      by_cases hst : s = t
      · subst s
        simpa [Function.update, normalHalfPlane] using hu
      · simp [Function.update, hst]
    have heq (lower : PolygonHeightSpace Θ) :=
      mem_independentWallCap_congr (Function.update h t (h t + ε)) h lower lower p
        hu' (fun _ ↦ Iff.rfl)
    exact (congrArg₂ (fun a b : ℝ ↦ a + b)
      (hI _ _ (heq (Function.update (fun s ↦ h s - 1) t (h t - 1 + ε)))) rfl).trans
      ((add_comm _ _).trans (congrArg₂ (fun a b : ℝ ↦ a + b)
        (hI _ _ (heq (fun s ↦ h s - 1))).symm rfl))
  · have hl' (s : angleDomain Θ) :
        Function.update (fun s ↦ h s - 1) t (h t - 1 + ε) s ≤
            inner ℝ p (normalVector (s.val : Real.Angle)) ↔
          h s - 1 ≤ inner ℝ p (normalVector (s.val : Real.Angle)) := by
      by_cases hst : s = t
      · subst s
        simpa [Function.update, normalHalfPlane] using hl
      · simp [Function.update, hst]
    have heq (upper : PolygonHeightSpace Θ) :=
      mem_independentWallCap_congr upper upper
        (Function.update (fun s ↦ h s - 1) t (h t - 1 + ε)) (fun s ↦ h s - 1) p
        (fun _ ↦ Iff.rfl) hl'
    exact congrArg₂ (fun a b : ℝ ↦ a + b)
      (hI _ _ (heq (Function.update h t (h t + ε)))) (hI _ _ (heq h)).symm

end MovingSofa

namespace MovingSofa

private theorem isClosed_independentWallCap {Θ : AngleSet} (upper lower : PolygonHeightSpace Θ) :
    IsClosed (independentWallCap upper lower) := by
  have hu (a : Real.Angle) (c : ℝ) : IsClosed (normalHalfPlane a c false false) :=
    isClosed_le (by fun_prop) continuous_const
  have hl (a : Real.Angle) (c : ℝ) : IsClosed (normalHalfPlane a c true false) :=
    isClosed_le continuous_const (by fun_prop)
  unfold independentWallCap
  exact (isClosed_iInter fun s ↦ isClosed_iInter fun _ ↦ (hu _ _).inter (hl _ _)).inter
    (isClosed_iInter fun s ↦ isClosed_iInter fun _ ↦ hu _ _)

/-- Simultaneous endpoint-wall variation is the sum of the two independent variations. -/
theorem independentWallCap_area_update_add {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (t : angleDomain Θ) (ε R : ℝ)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1)
    (hbound : ∀ (upper lower : PolygonHeightSpace Θ),
      (upper = h ∨ upper = Function.update h t (h t + ε)) →
      (lower = (fun s ↦ h s - 1) ∨
        lower = Function.update (fun s ↦ h s - 1) t (h t - 1 + ε)) →
      independentWallCap upper lower ⊆ Metric.closedBall 0 R) :
    ClassicalResults.area (independentWallCap (Function.update h t (h t + ε))
        (Function.update (fun s ↦ h s - 1) t (h t - 1 + ε))) +
      ClassicalResults.area (independentWallCap h (fun s ↦ h s - 1)) =
      ClassicalResults.area (independentWallCap (Function.update h t (h t + ε))
        (fun s ↦ h s - 1)) +
      ClassicalResults.area (independentWallCap h
        (Function.update (fun s ↦ h s - 1) t (h t - 1 + ε))) := by
  have hf (upper lower : PolygonHeightSpace Θ)
      (hu : upper = h ∨ upper = Function.update h t (h t + ε))
      (hl : lower = (fun s ↦ h s - 1) ∨
        lower = Function.update (fun s ↦ h s - 1) t (h t - 1 + ε)) :
      MeasureTheory.volume (independentWallCap upper lower) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono (hbound upper lower hu hl))
      MeasureTheory.measure_closedBall_lt_top)
  apply area_add_of_indicator_add_eq
  · exact (isClosed_independentWallCap _ _).measurableSet
  · exact (isClosed_independentWallCap _ _).measurableSet
  · exact (isClosed_independentWallCap _ _).measurableSet
  · exact (isClosed_independentWallCap _ _).measurableSet
  · exact hf _ _ (Or.inr rfl) (Or.inr rfl)
  · exact hf _ _ (Or.inl rfl) (Or.inl rfl)
  · exact hf _ _ (Or.inr rfl) (Or.inl rfl)
  · exact hf _ _ (Or.inl rfl) (Or.inr rfl)
  · exact independentWallCap_indicator_update_add h t ε hε hε'

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
# Polygon / Right Angle Grid
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace MovingSofa

/-- Directions in the right-angle grid are positive integer multiples of its step size. -/
theorem mem_rightAngleSet_directions_iff (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    t ∈ (rightAngleSet n hn).directions ↔
      ∃ i : ℕ, i ∈ Finset.Ioo 0 n ∧ t = i * polygonStepSize n := by
  simp only [rightAngleSet, uniformAngleSet, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, hi, ?_⟩
    simp only [polygonStepSize]
    ring
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, hi, ?_⟩
    simp only [polygonStepSize]
    ring

/-- No grid direction lies strictly between the predecessor of a grid point and the point. -/
theorem rightAngleSet_direction_le_pred_or_ge (n : ℕ) (hn : 2 ≤ n) {r t : ℝ}
    (hr : r ∈ (rightAngleSet n hn).directions)
    (ht : t ∈ (rightAngleSet n hn).directions) :
    r ≤ t - polygonStepSize n ∨ t ≤ r := by
  obtain ⟨j, hj, rfl⟩ := (mem_rightAngleSet_directions_iff n hn r).mp hr
  obtain ⟨i, hi, rfl⟩ := (mem_rightAngleSet_directions_iff n hn t).mp ht
  have hnpos : (0 : ℝ) < n := by positivity
  have hδ : 0 < polygonStepSize n := by simp [polygonStepSize]; positivity
  by_cases hji : j < i
  · left
    have hnat : j + 1 ≤ i := hji
    have hcast : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hnat
    nlinarith
  · right
    have hij : i ≤ j := Nat.le_of_not_gt hji
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hδ.le

/-- No grid direction lies strictly between a grid point and its successor. -/
theorem rightAngleSet_direction_le_or_succ_le (n : ℕ) (hn : 2 ≤ n) {r t : ℝ}
    (hr : r ∈ (rightAngleSet n hn).directions)
    (ht : t ∈ (rightAngleSet n hn).directions) :
    r ≤ t ∨ t + polygonStepSize n ≤ r := by
  obtain ⟨j, hj, rfl⟩ := (mem_rightAngleSet_directions_iff n hn r).mp hr
  obtain ⟨i, hi, rfl⟩ := (mem_rightAngleSet_directions_iff n hn t).mp ht
  have hδ : 0 < polygonStepSize n := by simp [polygonStepSize]; positivity
  by_cases hji : j ≤ i
  · left
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hji) hδ.le
  · right
    have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by
      exact_mod_cast (Nat.add_one_le_iff.mpr (Nat.lt_of_not_ge hji))
    nlinarith

/-- Every interior grid direction stays at least one step from both endpoints. -/
theorem rightAngleSet_direction_bounds (n : ℕ) (hn : 2 ≤ n) {t : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions) :
    polygonStepSize n ≤ t ∧ t ≤ Real.pi / 2 - polygonStepSize n := by
  obtain ⟨i, hi, rfl⟩ := (mem_rightAngleSet_directions_iff n hn t).mp ht
  obtain ⟨hi0, hin⟩ := Finset.mem_Ioo.mp hi
  have hnpos : (0 : ℝ) < n := by positivity
  have hδ : 0 < polygonStepSize n := by simp [polygonStepSize]; positivity
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi0
  have hin1 : (i : ℝ) + 1 ≤ n := by exact_mod_cast hin
  constructor
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hi1 hδ.le
  · have hstep : (n : ℝ) * polygonStepSize n = Real.pi / 2 := by
      simp only [polygonStepSize]
      field_simp
    nlinarith

/-- The two lower normals of a right-angle polygon cap coincide at `3π/2`. -/
theorem rightAngle_polygon_normals_eq (n : ℕ) (hn : 2 ≤ n) :
    ((fun r : ℝ ↦ (r : Real.Angle)) '' angleDomain (rightAngleSet n hn)) ∪
        capLowerNormals (rightAngleSet n hn).angle =
      (fun r : ℝ ↦ (r : Real.Angle)) ''
        (angleDomain (rightAngleSet n hn) ∪ {3 * Real.pi / 2}) := by
  ext a
  simp only [Set.mem_union, Set.mem_image, Set.mem_singleton_iff]
  constructor
  · rintro (⟨r, hr, rfl⟩ | ha)
    · exact ⟨r, Or.inl hr, rfl⟩
    · simp only [capLowerNormals, rightAngleSet, uniformAngleSet,
        Set.mem_insert_iff] at ha
      rcases ha with ha | ha
      · subst a
        refine ⟨3 * Real.pi / 2, Or.inr rfl, ?_⟩
        congr 1
        ring
      · subst a
        exact ⟨3 * Real.pi / 2, Or.inr rfl, rfl⟩
  · rintro ⟨r, hr | rfl, rfl⟩
    · exact Or.inl ⟨r, hr, rfl⟩
    · right
      simp [capLowerNormals, rightAngleSet, uniformAngleSet]

/-- The predecessor of a right-angle grid direction is zero or again a grid direction. -/
theorem rightAngleSet_sub_step (n : ℕ) (hn : 2 ≤ n) {t : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions) :
    t - polygonStepSize n = 0 ∨
      t - polygonStepSize n ∈ (rightAngleSet n hn).directions := by
  obtain ⟨i, hi, rfl⟩ := (mem_rightAngleSet_directions_iff n hn t).mp ht
  obtain ⟨hi0, hin⟩ := Finset.mem_Ioo.mp hi
  by_cases hi1 : i = 1
  · left
    subst hi1
    push_cast
    ring
  · right
    refine (mem_rightAngleSet_directions_iff n hn _).mpr ⟨i - 1, Finset.mem_Ioo.mpr ⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · rw [Nat.cast_sub (by omega)]
      push_cast
      ring

/-- The successor of a right-angle grid direction is the terminal angle or a grid direction. -/
theorem rightAngleSet_add_step (n : ℕ) (hn : 2 ≤ n) {t : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions) :
    t + polygonStepSize n = Real.pi / 2 ∨
      t + polygonStepSize n ∈ (rightAngleSet n hn).directions := by
  obtain ⟨i, hi, rfl⟩ := (mem_rightAngleSet_directions_iff n hn t).mp ht
  obtain ⟨hi0, hin⟩ := Finset.mem_Ioo.mp hi
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  by_cases hi1 : i + 1 = n
  · left
    have : ((i : ℝ) + 1) = (n : ℝ) := by exact_mod_cast congrArg (fun m : ℕ ↦ (m : ℝ)) hi1
    simp only [polygonStepSize]
    field_simp
    linarith [this]
  · right
    refine (mem_rightAngleSet_directions_iff n hn _).mpr ⟨i + 1, Finset.mem_Ioo.mpr ⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · push_cast
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
# Polygon / Translation
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem polygonCapTranslate_iff (Θ : AngleSet) (K : ConvexBody Point) :
    (∃ K' : PolygonCapTranslateSpace Θ, K'.val = (K : Set Point)) ↔
      (supportValue K (Θ.angle : Real.Angle) +
        supportValue K ((Θ.angle + Real.pi : ℝ) : Real.Angle) = 1) ∧
      (supportValue K ((Real.pi / 2 : ℝ) : Real.Angle) +
        supportValue K ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 1) ∧
      ∃ constraints : Set (Real.Angle × ℝ), constraints.Finite ∧
        (∀ c ∈ constraints, c.1 ∈
          ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle) ∧
        (K : Set Point) = ⋂ c ∈ constraints, normalHalfPlane c.1 c.2 false false := by
  classical
  let N : Set Real.Angle :=
    ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle
  have hNfinite : N.Finite := by
    apply Set.Finite.union
    · apply Set.Finite.image
      simp only [angleDomain]
      exact ((Θ.directions.finite_toSet.union
        (Θ.directions.finite_toSet.image (fun t : ℝ ↦ t + Real.pi / 2))).union
          ((Set.finite_singleton (Real.pi / 2)).insert Θ.angle))
    · simp [capLowerNormals]
  constructor
  · rintro ⟨K', hK'eq⟩
    obtain ⟨P, q, hPq⟩ := K'.property
    have hKeq : (K : Set Point) = (fun p ↦ p + q) '' (P.val.val : Set Point) := by
      rw [← hK'eq, hPq]
    have hsupp (t : Real.Angle) :
        supportValue K t = supportValue P.val.val t + inner ℝ q (normalVector t) := by
      rw [show (K : Set Point) = (ConvexBody.translate P.val.val q : Set Point) from hKeq]
      exact supportValue_image_add P.val.val q t
    have hopen := P.val.property
    refine ⟨?_, ?_, ?_⟩
    · rw [hsupp, hsupp, hopen.2.2.1, hopen.2.2.2.2.1, normalVector_add_pi]
      simp only [inner_neg_right]
      ring
    · have hang : (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) =
          ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
        congr 1
        ring
      rw [hsupp]
      rw [← hang]
      rw [hsupp, hopen.2.2.2.1]
      rw [show supportValue P.val.val (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) = 0 by
        rw [hang]; exact hopen.2.2.2.2.2.1]
      rw [normalVector_add_pi]
      simp only [inner_neg_right]
      ring
    · have hrepr : HasHalfPlaneRepresentation K N := by
        rw [show (K : Set Point) = (ConvexBody.translate P.val.val q : Set Point) from hKeq]
        exact P.property.translate q
      exact hrepr.finite_constraints hNfinite
  · rintro ⟨hwidthω, hwidthT, C, hCfinite, hCN, hKC⟩
    let v : Point := if h : Θ.angle = Real.pi / 2 then
      !₂[0, 1 - supportValue K ((Real.pi / 2 : ℝ) : Real.Angle)]
    else
      !₂[(1 - supportValue K (Θ.angle : Real.Angle) -
          (1 - supportValue K ((Real.pi / 2 : ℝ) : Real.Angle)) * Real.sin Θ.angle) /
          Real.cos Θ.angle,
        1 - supportValue K ((Real.pi / 2 : ℝ) : Real.Angle)]
    have hvT : inner ℝ v (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
        1 - supportValue K ((Real.pi / 2 : ℝ) : Real.Angle) := by
      by_cases h : Θ.angle = Real.pi / 2
      · simp [v, h, normalVector, frame, PiLp.inner_apply]
      · simp [v, h, normalVector, frame, PiLp.inner_apply]
    have hvω : inner ℝ v (normalVector (Θ.angle : Real.Angle)) =
        1 - supportValue K (Θ.angle : Real.Angle) := by
      by_cases h : Θ.angle = Real.pi / 2
      · simpa [h] using hvT
      · have hlt : Θ.angle < Real.pi / 2 := lt_of_le_of_ne Θ.angle_le h
        have hcos : Real.cos Θ.angle ≠ 0 := (Real.cos_pos_of_mem_Ioo
          ⟨lt_trans (neg_neg_of_pos (by positivity : 0 < Real.pi / 2)) Θ.angle_pos,
            hlt⟩).ne'
        simp [v, h, normalVector, frame, PiLp.inner_apply]
        field_simp [hcos]
        ring
    let L := ConvexBody.translate K v
    have hsupp (t : Real.Angle) :
        supportValue L t = supportValue K t + inner ℝ v (normalVector t) :=
      supportValue_image_add K v t
    have htopω : supportValue L (Θ.angle : Real.Angle) = 1 := by
      rw [hsupp, hvω]
      ring
    have htopT : supportValue L ((Real.pi / 2 : ℝ) : Real.Angle) = 1 := by
      rw [hsupp, hvT]
      ring
    have hbotω : supportValue L ((Θ.angle + Real.pi : ℝ) : Real.Angle) = 0 := by
      rw [hsupp, normalVector_add_pi, inner_neg_right]
      rw [hvω]
      linarith
    have hang : (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) =
        ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
      congr 1
      ring
    have hbotT : supportValue L ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
      rw [← hang, hsupp, normalVector_add_pi, inner_neg_right]
      rw [hang, hvT]
      linarith
    have hKrepr : HasHalfPlaneRepresentation K N := ⟨C, hCN, hKC⟩
    have hLrepr : HasHalfPlaneRepresentation L N := hKrepr.translate v
    have hangleDomain : angleDomain Θ ⊆ capUpperAngles Θ.angle := by
      rintro t ((ht | ⟨s, hs, rfl⟩) | ht)
      · left
        exact ⟨(Θ.interior t ht).1.le, (Θ.interior t ht).2.le⟩
      · right
        constructor <;> linarith [(Θ.interior s hs).1, (Θ.interior s hs).2]
      · rcases ht with (rfl | rfl)
        · exact Or.inl ⟨Θ.angle_pos.le, le_rfl⟩
        · exact Or.inr ⟨le_rfl, le_add_of_nonneg_left Θ.angle_pos.le⟩
    have hNsubset : N ⊆
        ((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles Θ.angle) ∪
          capLowerNormals Θ.angle := by
      rintro t (ht | ht)
      · obtain ⟨s, hs, rfl⟩ := ht
        exact Or.inl ⟨s, hangleDomain hs, rfl⟩
      · exact Or.inr ht
    have hLcapRepr : HasHalfPlaneRepresentation L
        (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles Θ.angle) ∪
          capLowerNormals Θ.angle) := by
      obtain ⟨D, hDN, hLD⟩ := hLrepr
      exact ⟨D, fun c hc ↦ hNsubset (hDN c hc), hLD⟩
    have hLcap : IsCap Θ.angle L :=
      ⟨Θ.angle_pos, Θ.angle_le, htopω, htopT, hbotω, hbotT, hLcapRepr⟩
    let P : PolygonCapSpace Θ := ⟨⟨L, hLcap⟩, hLrepr⟩
    refine ⟨⟨(K : Set Point), ?_⟩, rfl⟩
    refine ⟨P, -v, ?_⟩
    ext x
    constructor
    · intro hx
      exact ⟨x + v, ⟨x, hx, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa using hy

theorem polygonHeightArea_le_translateArea {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (K : PolygonCapTranslateSpace Θ) (hK : polygonHeightCap h = K.val) :
    polygonHeightArea h ≤ (polygonTranslateExtensions K).2 := by
  obtain ⟨P, q, hPq⟩ := K.property
  let C := ConvexBody.translate P.val.val q
  have hC : (C : Set Point) = K.val := hPq.symm
  have hBody : polygonHeightCap h = (C : Set Point) := hK.trans hC.symm
  have hw := (polygonCapTranslate_iff Θ C).1 ⟨K, hC.symm⟩
  let g := polygonTranslateHeight K
  have hle : ∀ t, g t ≤ h t := by
    intro t
    change supportValue K.val (t.val : Real.Angle) ≤ h t
    rw [← hC]
    simpa only [polygonHeightValue, dite_eq_left t.property] using
      supportValue_le_polygonHeightValue h C hBody t.property
  have heq : ∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      polygonHeightValue g t = polygonHeightValue h t := by
    intro t ht
    have htD : t ∈ angleDomain Θ := Or.inr ht
    have hg : polygonHeightValue g t = supportValue C (t : Real.Angle) := by
      simp only [g, polygonTranslateHeight, polygonHeightValue, dite_eq_left htD]
      rw [hC]
    rw [hg]
    apply supportValue_eq_polygonHeightValue_of_width_one h C hBody ht
    rcases ht with rfl | ht
    · exact hw.1
    · have ht : t = Real.pi / 2 := ht
      subst t
      simpa only [show Real.pi / 2 + Real.pi = 3 * Real.pi / 2 by ring] using hw.2.1
  have hsub := polygonHeightNiche_mono_of_eq_endpoints hle heq
  have harea : ClassicalResults.area (polygonHeightNiche g) ≤
      ClassicalResults.area (polygonHeightNiche h) := by
    apply ENNReal.toReal_mono (isBounded_polygonHeightNiche h).measure_lt_top.ne
    exact MeasureTheory.measure_mono hsub
  change ClassicalResults.area (polygonHeightCap h) -
      ClassicalResults.area (polygonHeightNiche h) ≤
    ClassicalResults.area (polygonHeightCap g) - ClassicalResults.area (polygonHeightNiche g)
  rw [hK, polygonHeightCap_of_translate K]
  exact sub_le_sub_left harea _

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
# Polygon / Height / Reconstruction
-/

@[expose] public section

noncomputable section

namespace MovingSofa

private theorem isClosed_polygonHeightCap {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    IsClosed (polygonHeightCap h) := by
  unfold polygonHeightCap polygonHeightParallelogram
  apply IsClosed.inter
  · exact isClosed_iInter fun t ↦ isClosed_iInter fun _ ↦
      (isClosed_normalHalfPlane _ _ false).inter (isClosed_normalHalfPlane _ _ true)
  · exact isClosed_iInter fun t ↦ isClosed_iInter fun _ ↦
      isClosed_normalHalfPlane _ _ false

private theorem convex_polygonHeightCap {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    Convex ℝ (polygonHeightCap h) := by
  unfold polygonHeightCap polygonHeightParallelogram
  apply Convex.inter
  · exact convex_iInter fun t ↦ convex_iInter fun _ ↦
      (convex_normalHalfPlane _ _ false).inter (convex_normalHalfPlane _ _ true)
  · exact convex_iInter fun t ↦ convex_iInter fun _ ↦
      convex_normalHalfPlane _ _ false

private theorem normalHalfPlane_upper_eq_lower_add_pi (t c : ℝ) :
    normalHalfPlane (t : Real.Angle) c true false =
      normalHalfPlane ((t + Real.pi : ℝ) : Real.Angle) (-c) false false := by
  ext p
  change c ≤ inner ℝ p (normalVector (t : Real.Angle)) ↔
    inner ℝ p (normalVector ((t + Real.pi : ℝ) : Real.Angle)) ≤ -c
  rw [normalVector_add_pi, inner_neg_right]
  constructor <;> intro h <;> linarith

private theorem polygonHeightCap_halfPlaneRepresentation {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) :
    HasHalfPlaneRepresentation (polygonHeightCap h)
      (((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle) := by
  let C : Set (Real.Angle × ℝ) :=
    ((fun t : ℝ ↦ ((t : Real.Angle), polygonHeightValue h t)) '' angleDomain Θ) ∪
      ((fun t : ℝ ↦ (((t + Real.pi : ℝ) : Real.Angle),
        -(polygonHeightValue h t - 1))) '' ({Θ.angle, Real.pi / 2} : Set ℝ))
  refine ⟨C, ?_, ?_⟩
  · rintro c (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact Or.inl ⟨t, ht, rfl⟩
    · right
      rcases ht with rfl | rfl
      · exact Or.inl rfl
      · change (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) ∈ capLowerNormals Θ.angle
        rw [show Real.pi / 2 + Real.pi = 3 * Real.pi / 2 by ring]
        simp [capLowerNormals]
  · ext p
    simp only [polygonHeightCap, polygonHeightParallelogram, Set.mem_inter_iff,
      Set.mem_iInter, C, Set.mem_union, Set.mem_image]
    constructor
    · rintro ⟨hendpoint, hinterior⟩ c (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · rcases ht with (ht | ht) | ht
        · exact (hinterior t (Or.inl ht))
        · obtain ⟨s, hs, rfl⟩ := ht
          exact hinterior (s + Real.pi / 2) (Or.inr ⟨s, hs, rfl⟩)
        · exact (hendpoint t ht).1
      · rw [← normalHalfPlane_upper_eq_lower_add_pi]
        exact (hendpoint t ht).2
    · intro hall
      constructor
      · intro t ht
        constructor
        · exact hall ((t : Real.Angle), polygonHeightValue h t)
            (Or.inl ⟨t, Or.inr ht, rfl⟩)
        · rw [normalHalfPlane_upper_eq_lower_add_pi]
          exact hall (((t + Real.pi : ℝ) : Real.Angle), -(polygonHeightValue h t - 1))
            (Or.inr ⟨t, ht, rfl⟩)
      · intro t ht
        exact hall ((t : Real.Angle), polygonHeightValue h t)
          (Or.inl ⟨t, Or.inl ht, rfl⟩)

private theorem polygonHeightCap_upper_bound {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {p : Point} (hp : p ∈ polygonHeightCap h) {t : ℝ} (ht : t ∈ angleDomain Θ) :
    inner ℝ p (normalVector (t : Real.Angle)) ≤ polygonHeightValue h t := by
  exact polygonHeightCap_subset_normalHalfPlane h ht hp

private theorem polygonHeightCap_lower_bound {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {p : Point} (hp : p ∈ polygonHeightCap h) {t : ℝ}
    (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    polygonHeightValue h t - 1 ≤ inner ℝ p (normalVector (t : Real.Angle)) := by
  change p ∈ polygonHeightParallelogram h ∩ _ at hp
  exact (Set.mem_iInter.mp (Set.mem_iInter.mp hp.1 t) ht).2

/-- Attainment of both endpoint strip bounds reconstructs a translated polygon cap. -/
theorem exists_polygonCapTranslate_eq_polygonHeightCap {Θ : AngleSet}
    (h : PolygonHeightSpace Θ)
    (hbounded : Bornology.IsBounded (polygonHeightCap h))
    (hupper : ∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      ∃ p ∈ polygonHeightCap h,
        inner ℝ p (normalVector (t : Real.Angle)) = polygonHeightValue h t)
    (hlower : ∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      ∃ p ∈ polygonHeightCap h,
        inner ℝ p (normalVector (t : Real.Angle)) = polygonHeightValue h t - 1) :
    ∃ K' : PolygonCapTranslateSpace Θ, K'.val = polygonHeightCap h := by
  obtain ⟨p, hp, _⟩ := hupper (Real.pi / 2) (by simp)
  let L : ConvexBody Point := {
    carrier := polygonHeightCap h
    convex' := convex_polygonHeightCap h
    isCompact' := Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_polygonHeightCap h, hbounded⟩
    nonempty' := ⟨p, hp⟩ }
  have hsuppUpper (t : ℝ) (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
      supportValue L (t : Real.Angle) = polygonHeightValue h t := by
    obtain ⟨q, hq, hqeq⟩ := hupper t ht
    apply le_antisymm
    · apply supportValue_le_of_subset_normalHalfPlane
      intro x hx
      exact polygonHeightCap_upper_bound h hx (Or.inr ht)
    · simpa only [hqeq] using inner_le_supportValue L hq (t : Real.Angle)
  have hsuppLower (t : ℝ) (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
      supportValue L ((t + Real.pi : ℝ) : Real.Angle) =
        -(polygonHeightValue h t - 1) := by
    obtain ⟨q, hq, hqeq⟩ := hlower t ht
    apply le_antisymm
    · apply supportValue_le_of_subset_normalHalfPlane
      intro x hx
      change inner ℝ x (normalVector ((t + Real.pi : ℝ) : Real.Angle)) ≤
        -(polygonHeightValue h t - 1)
      rw [normalVector_add_pi, inner_neg_right]
      exact neg_le_neg (polygonHeightCap_lower_bound h hx ht)
    · have hle := inner_le_supportValue L hq ((t + Real.pi : ℝ) : Real.Angle)
      rw [normalVector_add_pi, inner_neg_right, hqeq] at hle
      exact hle
  have hwidthω : supportValue L (Θ.angle : Real.Angle) +
      supportValue L ((Θ.angle + Real.pi : ℝ) : Real.Angle) = 1 := by
    rw [hsuppUpper Θ.angle (by simp), hsuppLower Θ.angle (by simp)]
    ring
  have hangle : (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) =
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    congr 1
    ring
  have hwidthT : supportValue L ((Real.pi / 2 : ℝ) : Real.Angle) +
      supportValue L ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 1 := by
    rw [← hangle, hsuppUpper (Real.pi / 2) (by simp),
      hsuppLower (Real.pi / 2) (by simp)]
    ring
  have hdomain : (angleDomain Θ).Finite := by
    unfold angleDomain
    exact (Θ.directions.finite_toSet.union
      (Θ.directions.finite_toSet.image (fun t : ℝ ↦ t + Real.pi / 2))).union
        (Set.finite_singleton (Real.pi / 2) |>.insert Θ.angle)
  have hlowerNormals : (capLowerNormals Θ.angle).Finite := by
    simp [capLowerNormals]
  have hrepr : HasHalfPlaneRepresentation (L : Set Point)
      (((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle) := by
    exact polygonHeightCap_halfPlaneRepresentation h
  obtain ⟨C, hCfinite, hCN, hLC⟩ :=
    hrepr.finite_constraints
      (hdomain.image _ |>.union hlowerNormals)
  exact (polygonCapTranslate_iff Θ L).mpr
    ⟨hwidthω, hwidthT, C, hCfinite, hCN, hLC⟩

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
# Polygon / Height / Positive Increment / Contacts
-/

@[expose] public section

noncomputable section

namespace MovingSofa

private theorem polygonHeightValue_raisedPolygonSupport {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ) (ε : ℝ) {s : ℝ}
    (hs : s ∈ angleDomain Θ) :
    polygonHeightValue (raisedPolygonSupport K t ε) s =
      supportValue K.val.val (s : Real.Angle) +
        if (⟨s, hs⟩ : angleDomain Θ) = t then ε else 0 := by
  simp [polygonHeightValue, raisedPolygonSupport, hs]

private theorem mem_polygonHeightCap_raised_of_mem_of_not_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ) {ε : ℝ} (hε : 0 ≤ ε)
    (ht : t.val ∉ ({Θ.angle, Real.pi / 2} : Set ℝ)) {p : Point}
    (hp : p ∈ (K.val.val : Set Point)) :
    p ∈ polygonHeightCap (raisedPolygonSupport K t ε) := by
  have hupper (s : ℝ) (hs : s ∈ angleDomain Θ) :
      inner ℝ p (normalVector (s : Real.Angle)) ≤
        polygonHeightValue (raisedPolygonSupport K t ε) s := by
    rw [polygonHeightValue_raisedPolygonSupport K t ε hs]
    exact (inner_le_supportValue K.val.val hp _).trans
      (le_add_of_nonneg_right (by split_ifs <;> positivity))
  unfold polygonHeightCap polygonHeightParallelogram
  simp only [Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro s hs
    constructor
    · exact hupper s (Or.inr hs)
    · change polygonHeightValue (raisedPolygonSupport K t ε) s - 1 ≤
        inner ℝ p (normalVector (s : Real.Angle))
      rw [polygonHeightValue_raisedPolygonSupport K t ε (Or.inr hs)]
      have hne : (⟨s, Or.inr hs⟩ : angleDomain Θ) ≠ t := by
        intro heq
        apply ht
        have hval : s = t.val := congrArg Subtype.val heq
        simpa [← hval] using hs
      rw [ite_eq_right hne]
      simp only [add_zero]
      rcases hs with rfl | rfl
      · have hlower := inner_le_supportValue K.val.val hp
          ((Θ.angle + Real.pi : ℝ) : Real.Angle)
        rw [K.val.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right] at hlower
        rw [K.val.property.2.2.1]
        linarith
      · have hlower := inner_le_supportValue K.val.val hp
          ((3 * Real.pi / 2 : ℝ) : Real.Angle)
        rw [K.val.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two] at hlower
        rw [K.val.property.2.2.2.1]
        simpa [normalVector, frame, PiLp.inner_apply] using hlower
  · intro s hs
    exact hupper s (Or.inl hs)

private theorem raisedPolygonSupport_endpoint_contacts_of_not_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ) {ε : ℝ} (hε : 0 ≤ ε)
    (ht : t.val ∉ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    (∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
        inner ℝ p (normalVector (s : Real.Angle)) =
          polygonHeightValue (raisedPolygonSupport K t ε) s) ∧
    (∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
        inner ℝ p (normalVector (s : Real.Angle)) =
          polygonHeightValue (raisedPolygonSupport K t ε) s - 1) := by
  have hne (s : ℝ) (hs : s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
      (⟨s, Or.inr hs⟩ : angleDomain Θ) ≠ t := by
    intro heq
    apply ht
    have hval : s = t.val := congrArg Subtype.val heq
    simpa [← hval] using hs
  have hvalue (s : ℝ) (hs : s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
      polygonHeightValue (raisedPolygonSupport K t ε) s =
        supportValue K.val.val (s : Real.Angle) := by
    rw [polygonHeightValue_raisedPolygonSupport K t ε (Or.inr hs), ite_eq_right (hne s hs),
      add_zero]
  constructor
  · intro s hs
    obtain ⟨p, hp, hpinner⟩ := exists_mem_inner_eq_supportValue K.val.val
      (s : Real.Angle)
    exact ⟨p, mem_polygonHeightCap_raised_of_mem_of_not_endpoint K t hε ht hp,
      hpinner.trans (hvalue s hs).symm⟩
  · intro s hs
    rcases hs with rfl | rfl
    · obtain ⟨p, hp, hpinner⟩ := exists_mem_inner_eq_supportValue K.val.val
        ((Θ.angle + Real.pi : ℝ) : Real.Angle)
      refine ⟨p, mem_polygonHeightCap_raised_of_mem_of_not_endpoint K t hε ht hp, ?_⟩
      rw [normalVector_add_pi, inner_neg_right,
        K.val.property.2.2.2.2.1] at hpinner
      rw [hvalue Θ.angle (by simp), K.val.property.2.2.1]
      linarith
    · obtain ⟨p, hp, hpinner⟩ := exists_mem_inner_eq_supportValue K.val.val
        ((3 * Real.pi / 2 : ℝ) : Real.Angle)
      refine ⟨p, mem_polygonHeightCap_raised_of_mem_of_not_endpoint K t hε ht hp, ?_⟩
      rw [K.val.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two] at hpinner
      rw [hvalue (Real.pi / 2) (by simp), K.val.property.2.2.2.1]
      simpa [normalVector, frame, PiLp.inner_apply] using hpinner

private theorem independentWallCap_self_sub_one_eq {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) :
    independentWallCap h (fun t ↦ h t - 1) = polygonHeightCap h := by
  ext p
  simp only [independentWallCap, polygonHeightCap, polygonHeightParallelogram,
    Set.mem_inter_iff, Set.mem_iInter]
  apply and_congr
  · apply forall_congr'
    intro t
    apply forall_congr'
    intro ht
    have htD : t ∈ angleDomain Θ := Or.inr ht
    simp only [polygonHeightValue, dite_eq_left htD]
  · rfl

private theorem polygonHeightCap_raised_bounded {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, |ε| ≤ ε₀ →
      Bornology.IsBounded (polygonHeightCap (raisedPolygonSupport K t ε)) := by
  let h : PolygonHeightSpace Θ :=
    fun s ↦ supportValue K.val.val (s.val : Real.Angle)
  obtain ⟨R, ε₀, hR, hε₀, hbound⟩ := polygonPerturbation_uniform_bounds Θ h
  refine ⟨ε₀, hε₀, fun ε hε ↦ ?_⟩
  let hε' := raisedPolygonSupport K t ε
  let lower : PolygonHeightSpace Θ := fun s ↦ hε' s - 1
  have hu (s : angleDomain Θ) : |hε' s - h s| ≤ ε₀ := by
    change |(supportValue K.val.val (s.val : Real.Angle) + if s = t then ε else 0) -
      supportValue K.val.val (s.val : Real.Angle)| ≤ ε₀
    split_ifs
    · simpa using hε
    · simp [hε₀.le]
  have hl (s : angleDomain Θ) : |lower s - (h s - 1)| ≤ ε₀ := by
    simpa only [lower, sub_sub_sub_cancel_right] using hu s
  have hsub := (hbound hε' lower hu hl).1
  rw [independentWallCap_self_sub_one_eq] at hsub
  exact Metric.isBounded_closedBall.subset hsub

/-- A sufficiently small interior height increase yields a translated polygon cap. -/
theorem polygonCap_positive_height_increment_of_not_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (ht : t.val ∉ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ K' : PolygonCapTranslateSpace Θ,
        K'.val = polygonHeightCap (raisedPolygonSupport K t ε) := by
  obtain ⟨ε₀, hε₀, hbounded⟩ := polygonHeightCap_raised_bounded K t
  refine ⟨ε₀, hε₀, fun ε hε hεlt ↦ ?_⟩
  have hcontacts := raisedPolygonSupport_endpoint_contacts_of_not_endpoint
    K t hε.le ht
  exact exists_polygonCapTranslate_eq_polygonHeightCap _
    (hbounded ε (abs_le.mpr ⟨by linarith, hεlt.le⟩)) hcontacts.1 hcontacts.2

private theorem midpoint_mem_strict_support_of_face {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {a b : Point} {t c : ℝ} (ht : t ∈ angleDomain Θ)
    (ha : a ∈ (K.val.val : Set Point)) (hb : b ∈ (K.val.val : Set Point))
    (hat : inner ℝ a (normalVector (t : Real.Angle)) = c)
    (hbt : inner ℝ b (normalVector (t : Real.Angle)) = c)
    (hab : a ≠ b) :
    let m := (2 : ℝ)⁻¹ • (a + b)
    m ∈ (K.val.val : Set Point) ∧
      inner ℝ m (normalVector (t : Real.Angle)) = c ∧
      ∀ s ∈ angleDomain Θ, s ≠ t →
        inner ℝ m (normalVector (s : Real.Angle)) <
          supportValue K.val.val (s : Real.Angle) := by
  dsimp
  have hm : (2 : ℝ)⁻¹ • (a + b) ∈ (K.val.val : Set Point) := by
    rw [smul_add]
    exact K.val.val.convex ha hb (by norm_num) (by norm_num) (by norm_num)
  have hmt : inner ℝ ((2 : ℝ)⁻¹ • (a + b)) (normalVector (t : Real.Angle)) =
      c := by
    rw [inner_smul_left, inner_add_left]
    simp only [RCLike.conj_to_real, hat, hbt]
    ring
  refine ⟨hm, hmt, ?_⟩
  intro s hs hst
  have hle := inner_le_supportValue K.val.val hm (s : Real.Angle)
  apply lt_of_le_of_ne hle
  intro heq
  have hae := inner_le_supportValue K.val.val ha (s : Real.Angle)
  have hbe := inner_le_supportValue K.val.val hb (s : Real.Angle)
  have hmavg : inner ℝ ((2 : ℝ)⁻¹ • (a + b)) (normalVector (s : Real.Angle)) =
      (2 : ℝ)⁻¹ * (inner ℝ a (normalVector (s : Real.Angle)) +
        inner ℝ b (normalVector (s : Real.Angle))) := by
    rw [inner_smul_left, inner_add_left]
    simp only [RCLike.conj_to_real]
  have haeq : inner ℝ a (normalVector (s : Real.Angle)) =
      supportValue K.val.val (s : Real.Angle) := by
    rw [hmavg] at heq
    nlinarith
  have hbeq : inner ℝ b (normalVector (s : Real.Angle)) =
      supportValue K.val.val (s : Real.Angle) := by
    rw [hmavg] at heq
    nlinarith
  have hortht : inner ℝ (b - a) (normalVector (t : Real.Angle)) = 0 := by
    rw [inner_sub_left, hbt, hat, sub_self]
  have horths : inner ℝ (b - a) (normalVector (s : Real.Angle)) = 0 := by
    rw [inner_sub_left, hbeq, haeq, sub_self]
  exact hst (eq_of_inner_sub_normalVector_eq_zero_of_ne
    (angleDomain_subset_Ioo Θ hs) (angleDomain_subset_Ioo Θ ht) hab horths hortht)

private theorem exists_pos_uniform_strict_support_gap {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (m : Point) (t : angleDomain Θ)
    (hstrict : ∀ s ∈ angleDomain Θ, s ≠ t.val →
      inner ℝ m (normalVector (s : Real.Angle)) <
        supportValue K.val.val (s : Real.Angle)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ angleDomain Θ, s ≠ t.val →
      δ ≤ supportValue K.val.val (s : Real.Angle) -
        inner ℝ m (normalVector (s : Real.Angle)) := by
  let gap : ℝ → ℝ := fun s ↦ if s = t.val then 1 else
    supportValue K.val.val (s : Real.Angle) - inner ℝ m (normalVector (s : Real.Angle))
  have hdomain : (angleDomain Θ).Finite := by
    unfold angleDomain
    exact (Θ.directions.finite_toSet.union
      (Θ.directions.finite_toSet.image (fun s : ℝ ↦ s + Real.pi / 2))).union
        (Set.finite_singleton (Real.pi / 2) |>.insert Θ.angle)
  have hnonempty : (angleDomain Θ).Nonempty := ⟨Θ.angle, by simp [angleDomain]⟩
  obtain ⟨δ, hδ, hδle⟩ := hdomain.isCompact.exists_pos_forall_le hnonempty
    (hdomain.continuousOn gap) (fun s hs ↦ by
      dsimp only [gap]
      split_ifs with heq
      · positivity
      · linarith [hstrict s hs heq])
  refine ⟨δ, hδ, ?_⟩
  intro s hs hne
  simpa [gap, hne] using hδle s hs

private theorem cos_sub_nonneg_of_mem_endpoints {Θ : AngleSet} {s t : ℝ}
    (hs : s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) : 0 ≤ Real.cos (s - t) := by
  apply Real.cos_nonneg_of_mem_Icc
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  all_goals constructor <;> linarith [Θ.angle_pos, Θ.angle_le, Real.pi_pos]

private theorem add_smul_normal_mem_raisedPolygonSupport {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (htendpoint : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (m : Point) (hm : m ∈ (K.val.val : Set Point))
    (hmLower : supportValue K.val.val (t.val : Real.Angle) - 1 ≤
      inner ℝ m (normalVector (t.val : Real.Angle)))
    (hmUpper : inner ℝ m (normalVector (t.val : Real.Angle)) ≤
      supportValue K.val.val (t.val : Real.Angle))
    {δ ε : ℝ} (hδ : ∀ s ∈ angleDomain Θ, s ≠ t.val →
      δ ≤ supportValue K.val.val (s : Real.Angle) -
        inner ℝ m (normalVector (s : Real.Angle)))
    (hε : 0 < ε) (hεδ : ε < δ) :
    m + ε • normalVector (t.val : Real.Angle) ∈
      polygonHeightCap (raisedPolygonSupport K t ε) := by
  unfold polygonHeightCap polygonHeightParallelogram
  simp only [Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro r hr
    have hrD : r ∈ angleDomain Θ := Or.inr hr
    have hval := polygonHeightValue_raisedPolygonSupport K t ε hrD
    constructor
    · change inner ℝ (m + ε • normalVector (t.val : Real.Angle))
          (normalVector (r : Real.Angle)) ≤
        polygonHeightValue (raisedPolygonSupport K t ε) r
      rw [hval, inner_add_left, inner_smul_left]
      simp only [RCLike.conj_to_real]
      by_cases hrt : r = t.val
      · have hsub : (⟨r, hrD⟩ : angleDomain Θ) = t := Subtype.ext hrt
        rw [ite_eq_left hsub, hrt, inner_normalVector_self]
        linarith
      · have hsub : (⟨r, hrD⟩ : angleDomain Θ) ≠ t := by
          intro heq
          exact hrt (congrArg Subtype.val heq)
        rw [ite_eq_right hsub]
        have hcos := Real.cos_le_one (t.val - r)
        rw [inner_normalVector_normalVector]
        have hgap := hδ r hrD hrt
        nlinarith
    · change polygonHeightValue (raisedPolygonSupport K t ε) r - 1 ≤
        inner ℝ (m + ε • normalVector (t.val : Real.Angle))
          (normalVector (r : Real.Angle))
      rw [hval, inner_add_left, inner_smul_left]
      simp only [RCLike.conj_to_real]
      by_cases hrt : r = t.val
      · have hsub : (⟨r, hrD⟩ : angleDomain Θ) = t := Subtype.ext hrt
        rw [ite_eq_left hsub, hrt, inner_normalVector_self]
        nlinarith
      · have hsub : (⟨r, hrD⟩ : angleDomain Θ) ≠ t := by
          intro heq
          exact hrt (congrArg Subtype.val heq)
        rw [ite_eq_right hsub, add_zero]
        have hbase : supportValue K.val.val (r : Real.Angle) - 1 ≤
            inner ℝ m (normalVector (r : Real.Angle)) := by
          rcases hr with rfl | rfl
          · have hl := inner_le_supportValue K.val.val hm
              ((Θ.angle + Real.pi : ℝ) : Real.Angle)
            rw [K.val.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right] at hl
            rw [K.val.property.2.2.1]
            linarith
          · have hl := inner_le_supportValue K.val.val hm
              ((3 * Real.pi / 2 : ℝ) : Real.Angle)
            rw [K.val.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two] at hl
            rw [K.val.property.2.2.2.1]
            simpa [normalVector, frame, PiLp.inner_apply] using hl
        have hcos := cos_sub_nonneg_of_mem_endpoints htendpoint hr
        rw [inner_normalVector_normalVector]
        exact hbase.trans (le_add_of_nonneg_right (mul_nonneg hε.le hcos))
  · intro r hr
    have hrD : r ∈ angleDomain Θ := Or.inl hr
    have hval := polygonHeightValue_raisedPolygonSupport K t ε hrD
    change inner ℝ (m + ε • normalVector (t.val : Real.Angle))
        (normalVector (r : Real.Angle)) ≤
      polygonHeightValue (raisedPolygonSupport K t ε) r
    rw [hval, inner_add_left, inner_smul_left]
    simp only [RCLike.conj_to_real]
    by_cases hrt : r = t.val
    · have hsub : (⟨r, hrD⟩ : angleDomain Θ) = t := Subtype.ext hrt
      rw [ite_eq_left hsub, hrt, inner_normalVector_self]
      linarith
    · have hsub : (⟨r, hrD⟩ : angleDomain Θ) ≠ t := by
        intro heq
        exact hrt (congrArg Subtype.val heq)
      rw [ite_eq_right hsub]
      have hcos := Real.cos_le_one (t.val - r)
      rw [inner_normalVector_normalVector]
      have hgap := hδ r hrD hrt
      nlinarith

private theorem mem_raisedPolygonSupport_of_endpoint_of_le_inner {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) {p : Point}
    (hp : p ∈ (K.val.val : Set Point)) {ε : ℝ} (hε : 0 ≤ ε)
    (hinner : ε ≤ inner ℝ p (normalVector (t.val : Real.Angle))) :
    p ∈ polygonHeightCap (raisedPolygonSupport K t ε) := by
  unfold polygonHeightCap polygonHeightParallelogram
  simp only [Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro r hr
    have hrD : r ∈ angleDomain Θ := Or.inr hr
    have hvalue := polygonHeightValue_raisedPolygonSupport K t ε hrD
    constructor
    · change inner ℝ p (normalVector (r : Real.Angle)) ≤
          polygonHeightValue (raisedPolygonSupport K t ε) r
      rw [hvalue]
      exact (inner_le_supportValue K.val.val hp _).trans
        (le_add_of_nonneg_right (by split_ifs <;> positivity))
    · change polygonHeightValue (raisedPolygonSupport K t ε) r - 1 ≤
          inner ℝ p (normalVector (r : Real.Angle))
      rw [hvalue]
      by_cases hrt : r = t.val
      · have hsub : (⟨r, hrD⟩ : angleDomain Θ) = t := Subtype.ext hrt
        rw [ite_eq_left hsub, hrt]
        have hsupport : supportValue K.val.val (t.val : Real.Angle) = 1 := by
          rcases ht with ht | ht
          · simpa [ht] using K.val.property.2.2.1
          · have ht' : t.val = Real.pi / 2 := by simpa using ht
            simpa [ht'] using K.val.property.2.2.2.1
        rw [hsupport]
        simpa using hinner
      · have hsub : (⟨r, hrD⟩ : angleDomain Θ) ≠ t := by
          intro heq
          exact hrt (congrArg Subtype.val heq)
        rw [ite_eq_right hsub, add_zero]
        rcases hr with rfl | rfl
        · have hlower := inner_le_supportValue K.val.val hp
              ((Θ.angle + Real.pi : ℝ) : Real.Angle)
          rw [K.val.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right] at hlower
          rw [K.val.property.2.2.1]
          linarith
        · have hlower := inner_le_supportValue K.val.val hp
              ((3 * Real.pi / 2 : ℝ) : Real.Angle)
          rw [K.val.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two] at hlower
          rw [K.val.property.2.2.2.1]
          simpa [normalVector, frame, PiLp.inner_apply] using hlower
  · intro r hr
    have hrD : r ∈ angleDomain Θ := Or.inl hr
    rw [polygonHeightValue_raisedPolygonSupport K t ε hrD]
    exact (inner_le_supportValue K.val.val hp _).trans
      (le_add_of_nonneg_right (by split_ifs <;> positivity))

private theorem moved_upper_lower_contacts {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ) (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (u l : Point) (hu : u ∈ (K.val.val : Set Point))
    (huval : inner ℝ u (normalVector (t.val : Real.Angle)) =
      supportValue K.val.val (t.val : Real.Angle))
    (hl : l ∈ (K.val.val : Set Point))
    (hlval : inner ℝ l (normalVector (t.val : Real.Angle)) =
      supportValue K.val.val (t.val : Real.Angle) - 1)
    {δu δl ε : ℝ}
    (hδu : ∀ s ∈ angleDomain Θ, s ≠ t.val →
      δu ≤ supportValue K.val.val (s : Real.Angle) -
        inner ℝ u (normalVector (s : Real.Angle)))
    (hδl : ∀ s ∈ angleDomain Θ, s ≠ t.val →
      δl ≤ supportValue K.val.val (s : Real.Angle) -
        inner ℝ l (normalVector (s : Real.Angle)))
    (hε : 0 < ε) (hεu : ε < δu) (hεl : ε < δl) :
    (∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
      inner ℝ p (normalVector (t.val : Real.Angle)) =
        polygonHeightValue (raisedPolygonSupport K t ε) t.val) ∧
    (∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
      inner ℝ p (normalVector (t.val : Real.Angle)) =
        polygonHeightValue (raisedPolygonSupport K t ε) t.val - 1) := by
  have huLower : supportValue K.val.val (t.val : Real.Angle) - 1 ≤
      inner ℝ u (normalVector (t.val : Real.Angle)) := by linarith
  have hlUpper : inner ℝ l (normalVector (t.val : Real.Angle)) ≤
      supportValue K.val.val (t.val : Real.Angle) := by linarith
  have hu' := add_smul_normal_mem_raisedPolygonSupport K t ht u hu huLower huval.le
    hδu hε hεu
  have hl' := add_smul_normal_mem_raisedPolygonSupport K t ht l hl hlval.ge hlUpper
    hδl hε hεl
  have hvalue : polygonHeightValue (raisedPolygonSupport K t ε) t.val =
      supportValue K.val.val (t.val : Real.Angle) + ε := by
    rw [polygonHeightValue_raisedPolygonSupport K t ε t.property]
    simp
  constructor
  · refine ⟨u + ε • normalVector (t.val : Real.Angle), hu', ?_⟩
    rw [inner_add_left, inner_smul_left, huval, inner_normalVector_self, hvalue]
    simp
  · refine ⟨l + ε • normalVector (t.val : Real.Angle), hl', ?_⟩
    rw [inner_add_left, inner_smul_left, hlval, inner_normalVector_self, hvalue]
    simp
    ring

private theorem exists_upperFace_midpoint_strict {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ)
    (ht : 0 < surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}) :
    ∃ m : Point,
      m ∈ (K.val.val : Set Point) ∧
      inner ℝ m (normalVector (t.val : Real.Angle)) =
        supportValue K.val.val (t.val : Real.Angle) ∧
      ∀ s ∈ angleDomain Θ, s ≠ t.val →
        inner ℝ m (normalVector (s : Real.Angle)) <
          supportValue K.val.val (s : Real.Angle) := by
  let a := (edgeVertices K.val.val (t.val : Real.Angle)).1
  let b := (edgeVertices K.val.val (t.val : Real.Angle)).2
  have haedge := edgeVertices_fst_mem K.val.val (t.val : Real.Angle)
  have hbedge := edgeVertices_snd_mem K.val.val (t.val : Real.Angle)
  have hab : a ≠ b := by
    have hdist : 0 < dist a b := by
      rw [(surfaceAreaMeasure_atom_length K.val.val (t.val : Real.Angle)).2.1] at ht
      exact ENNReal.ofReal_pos.mp ht
    exact dist_ne_zero.mp hdist.ne'
  let m := (2 : ℝ)⁻¹ • (a + b)
  have hm := midpoint_mem_strict_support_of_face K t.property
    haedge.1 hbedge.1 haedge.2 hbedge.2 hab
  exact ⟨m, hm⟩

private theorem stripParallelogram_top_inner_angle (Θ : AngleSet)
    (hΘ : Θ.angle < Real.pi / 2) :
    inner ℝ (stripParallelogram Θ.angle).2.2 (normalVector (Θ.angle : Real.Angle)) = 1 := by
  have hc : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Θ.angle_pos, Real.pi_pos], hΘ⟩
  have hgap : Real.tan (Real.pi / 4 - Θ.angle / 2) =
      (Real.cos Θ.angle)⁻¹ - Real.tan Θ.angle := by
    simpa [show Real.pi / 4 - Θ.angle / 2 =
        (Real.pi / 2 - Θ.angle) / 2 by ring]
      using Real.tan_pi_div_two_sub_div_two Θ.angle ⟨Θ.angle_pos.le, hΘ⟩
  have htan := Real.tan_eq_sin_div_cos Θ.angle
  simp [stripParallelogram, normalVector, frame, PiLp.inner_apply, hgap, htan]
  field_simp [hc.ne']
  ring

private theorem stripParallelogram_top_sub_vertical_mem_of_angle_lt {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hΘ : Θ.angle < Real.pi / 2) :
    (stripParallelogram Θ.angle).2.2 - tangentVector 0 ∈ (K.val.val : Set Point) := by
  let o := (stripParallelogram Θ.angle).2.2
  let a := o - tangentVector 0
  have ho := stripParallelogram_top_mem_of_angle_lt Θ hΘ K
  have haFan : a ∈ capFan Θ.angle := by
    constructor
    · change 0 ≤ inner ℝ a (normalVector (Θ.angle : Real.Angle))
      dsimp [a]
      have hoω : inner ℝ o (normalVector (Θ.angle : Real.Angle)) = 1 :=
        stripParallelogram_top_inner_angle Θ hΘ
      rw [inner_sub_left, hoω]
      simp [tangentVector, normalVector, frame, PiLp.inner_apply]
      exact Real.sin_le_one Θ.angle
    · change 0 ≤ inner ℝ a (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      simp [a, o, stripParallelogram, tangentVector, normalVector, frame,
        PiLp.inner_apply]
  apply K.val.mem_of_mem_capFan_of_le_supportValue haFan
  intro s hs
  have ho_le := inner_le_supportValue K.val.val ho (s : Real.Angle)
  have hale : inner ℝ a (normalVector (s : Real.Angle)) ≤
      inner ℝ o (normalVector (s : Real.Angle)) := by
    rw [show a = o - tangentVector 0 by rfl, inner_sub_left]
    apply sub_le_self
    have hsI : s ∈ Set.Icc 0 Real.pi := by
      rcases hs with hs | hs
      · exact ⟨hs.1, hs.2.trans (Θ.angle_le.trans (by linarith [Real.pi_pos]))⟩
      · exact ⟨(by positivity : 0 ≤ Real.pi / 2).trans hs.1,
          hs.2.trans (by linarith [Θ.angle_le, Real.pi_pos])⟩
    simpa [tangentVector, normalVector, frame, PiLp.inner_apply] using
      Real.sin_nonneg_of_mem_Icc hsI
  exact hale.trans ho_le

private theorem stripParallelogram_top_sub_normal_mem_of_angle_lt {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hΘ : Θ.angle < Real.pi / 2) :
    (stripParallelogram Θ.angle).2.2 - normalVector (Θ.angle : Real.Angle) ∈
      (K.val.val : Set Point) := by
  let o := (stripParallelogram Θ.angle).2.2
  let b := o - normalVector (Θ.angle : Real.Angle)
  have ho := stripParallelogram_top_mem_of_angle_lt Θ hΘ K
  have hbFan : b ∈ capFan Θ.angle := by
    constructor
    · change 0 ≤ inner ℝ b (normalVector (Θ.angle : Real.Angle))
      dsimp [b]
      have hoω : inner ℝ o (normalVector (Θ.angle : Real.Angle)) = 1 :=
        stripParallelogram_top_inner_angle Θ hΘ
      rw [inner_sub_left, hoω, inner_normalVector_self, sub_self]
    · change 0 ≤ inner ℝ b (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      dsimp [b]
      have hoT : inner ℝ o (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
        simp [o, stripParallelogram, normalVector, frame, PiLp.inner_apply]
      rw [inner_sub_left, hoT]
      simp [normalVector, frame, PiLp.inner_apply]
      exact Real.sin_le_one Θ.angle
  apply K.val.mem_of_mem_capFan_of_le_supportValue hbFan
  intro s hs
  have ho_le := inner_le_supportValue K.val.val ho (s : Real.Angle)
  have hble : inner ℝ b (normalVector (s : Real.Angle)) ≤
      inner ℝ o (normalVector (s : Real.Angle)) := by
    rw [show b = o - normalVector (Θ.angle : Real.Angle) by rfl, inner_sub_left]
    apply sub_le_self
    rw [inner_normalVector_normalVector]
    apply Real.cos_nonneg_of_mem_Icc
    rcases hs with hs | hs
    · constructor <;> linarith [hs.1, hs.2, Θ.angle_pos, Θ.angle_le, Real.pi_pos]
    · constructor <;> linarith [hs.1, hs.2, Θ.angle_pos, Θ.angle_le, Real.pi_pos]
  exact hble.trans ho_le

private theorem exists_lowerFace_midpoint_strict_of_angle_lt {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hΘ : Θ.angle < Real.pi / 2)
    (t : angleDomain Θ) (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    ∃ m : Point,
      m ∈ (K.val.val : Set Point) ∧
      inner ℝ m (normalVector (t.val : Real.Angle)) =
        supportValue K.val.val (t.val : Real.Angle) - 1 ∧
      ∀ s ∈ angleDomain Θ, s ≠ t.val →
        inner ℝ m (normalVector (s : Real.Angle)) <
          supportValue K.val.val (s : Real.Angle) := by
  have hzero := zero_mem_cap_of_lt K.val hΘ
  rcases ht with ht | ht
  · have htval : t.val = Θ.angle := ht
    let b := (stripParallelogram Θ.angle).2.2 - normalVector (Θ.angle : Real.Angle)
    have hb := stripParallelogram_top_sub_normal_mem_of_angle_lt K hΘ
    have hbnormal : inner ℝ b (normalVector (Θ.angle : Real.Angle)) = 0 := by
      dsimp [b]
      rw [inner_sub_left, stripParallelogram_top_inner_angle Θ hΘ,
        inner_normalVector_self, sub_self]
    have hbne : (0 : Point) ≠ b := by
      intro heq
      have hgap := (parallelogram_gap Θ.angle ⟨Θ.angle_pos.le, hΘ⟩).2.1
      rw [← show b = (stripParallelogram Θ.angle).2.2 -
        normalVector (Θ.angle : Real.Angle) by rfl, ← heq] at hgap
      have hgappos : 0 < Real.tan ((Real.pi / 2 - Θ.angle) / 2) :=
        Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith)
          (by linarith [Θ.angle_pos, Real.pi_pos])
      have hcoord := congrArg (fun p : Point ↦ p 1) hgap
      have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Θ.angle_pos, Real.pi_pos], hΘ⟩
      simp [tangentVector, frame] at hcoord
      rcases hcoord with hgapzero | hcoszero
      · exact hgappos.ne' hgapzero
      · exact hcos.ne' hcoszero
    have hm := midpoint_mem_strict_support_of_face (c := 0) K t.property hzero hb
      (by simp) (by simpa [htval, K.val.property.2.2.1] using hbnormal) hbne
    refine ⟨(2 : ℝ)⁻¹ • ((0 : Point) + b), hm.1, ?_, ?_⟩
    · rw [hm.2.1, htval, K.val.property.2.2.1]
      ring
    · simpa [htval] using hm.2.2
  · have htval : t.val = Real.pi / 2 := ht
    let a := (stripParallelogram Θ.angle).2.2 - tangentVector 0
    have ha := stripParallelogram_top_sub_vertical_mem_of_angle_lt K hΘ
    have hanormal : inner ℝ a (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
      simp [a, stripParallelogram, tangentVector, normalVector, frame, PiLp.inner_apply]
    have hane : (0 : Point) ≠ a := by
      intro heq
      have hgap := (parallelogram_gap Θ.angle ⟨Θ.angle_pos.le, hΘ⟩).1
      rw [← show a = (stripParallelogram Θ.angle).2.2 - tangentVector 0 by rfl,
        ← heq] at hgap
      have hgappos : 0 < Real.tan ((Real.pi / 2 - Θ.angle) / 2) :=
        Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith)
          (by linarith [Θ.angle_pos, Real.pi_pos])
      have hcoord := congrArg (fun p : Point ↦ p 0) hgap
      simp [normalVector, frame] at hcoord
      linarith
    have hm := midpoint_mem_strict_support_of_face (c := 0) K t.property hzero ha
      (by simp) (by simpa [htval, K.val.property.2.2.2.1] using hanormal) hane
    refine ⟨(2 : ℝ)⁻¹ • ((0 : Point) + a), hm.1, ?_, ?_⟩
    · rw [hm.2.1, htval, K.val.property.2.2.2.1]
      ring
    · simpa [htval] using hm.2.2

private theorem sub_normalVector_pi_div_two_mem_of_mem_of_angle_eq {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hΘ : Θ.angle = Real.pi / 2) {p : Point}
    (hp : p ∈ (K.val.val : Set Point))
    (hpT : inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1) :
    p - normalVector ((Real.pi / 2 : ℝ) : Real.Angle) ∈ (K.val.val : Set Point) := by
  apply K.val.mem_of_mem_capFan_of_le_supportValue
  · constructor
    · change 0 ≤ inner ℝ (p - normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
          (normalVector (Θ.angle : Real.Angle))
      rw [hΘ, inner_sub_left, hpT, inner_normalVector_self, sub_self]
    · change 0 ≤ inner ℝ (p - normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
          (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      rw [inner_sub_left, hpT, inner_normalVector_self, sub_self]
  · intro s hs
    have hsI : s ∈ Set.Icc 0 Real.pi := by
      rcases hs with hs | hs
      · exact ⟨hs.1, by rw [hΘ] at hs; linarith [hs.2, Real.pi_pos]⟩
      · exact ⟨by linarith [hs.1, Real.pi_pos], by rw [hΘ] at hs; linarith [hs.2]⟩
    have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_mem_Icc hsI
    have hle : inner ℝ (p - normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
        (normalVector (s : Real.Angle)) ≤ inner ℝ p (normalVector (s : Real.Angle)) := by
      rw [inner_sub_left]
      apply sub_le_self
      rw [inner_normalVector_normalVector]
      simpa [Real.cos_pi_div_two_sub] using hsin
    exact hle.trans (inner_le_supportValue K.val.val hp (s : Real.Angle))

private theorem exists_lowerFace_midpoint_strict_of_angle_eq {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hΘ : Θ.angle = Real.pi / 2)
    (t : angleDomain Θ) (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (hmass : 0 < surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}) :
    ∃ m : Point,
      m ∈ (K.val.val : Set Point) ∧
      inner ℝ m (normalVector (t.val : Real.Angle)) =
        supportValue K.val.val (t.val : Real.Angle) - 1 ∧
      ∀ s ∈ angleDomain Θ, s ≠ t.val →
        inner ℝ m (normalVector (s : Real.Angle)) <
          supportValue K.val.val (s : Real.Angle) := by
  have htval : t.val = Real.pi / 2 := by
    rcases ht with ht | ht
    · simpa [hΘ] using ht
    · exact ht
  let a := (edgeVertices K.val.val (t.val : Real.Angle)).1
  let b := (edgeVertices K.val.val (t.val : Real.Angle)).2
  let a' := a - normalVector ((Real.pi / 2 : ℝ) : Real.Angle)
  let b' := b - normalVector ((Real.pi / 2 : ℝ) : Real.Angle)
  have haedge := edgeVertices_fst_mem K.val.val (t.val : Real.Angle)
  have hbedge := edgeVertices_snd_mem K.val.val (t.val : Real.Angle)
  have hab : a ≠ b := by
    have hdist : 0 < dist a b := by
      rw [(surfaceAreaMeasure_atom_length K.val.val (t.val : Real.Angle)).2.1] at hmass
      exact ENNReal.ofReal_pos.mp hmass
    exact dist_ne_zero.mp hdist.ne'
  have haT : inner ℝ a (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
    have haSupport : inner ℝ a (normalVector (t.val : Real.Angle)) =
        supportValue K.val.val (t.val : Real.Angle) := haedge.2
    simpa [htval, K.val.property.2.2.2.1] using haSupport
  have hbT : inner ℝ b (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
    have hbSupport : inner ℝ b (normalVector (t.val : Real.Angle)) =
        supportValue K.val.val (t.val : Real.Angle) := hbedge.2
    simpa [htval, K.val.property.2.2.2.1] using hbSupport
  have ha' : a' ∈ (K.val.val : Set Point) :=
    sub_normalVector_pi_div_two_mem_of_mem_of_angle_eq K hΘ haedge.1 haT
  have hb' : b' ∈ (K.val.val : Set Point) :=
    sub_normalVector_pi_div_two_mem_of_mem_of_angle_eq K hΘ hbedge.1 hbT
  have ha'normal : inner ℝ a' (normalVector (t.val : Real.Angle)) = 0 := by
    rw [htval]
    dsimp [a']
    rw [inner_sub_left, haT, inner_normalVector_self, sub_self]
  have hb'normal : inner ℝ b' (normalVector (t.val : Real.Angle)) = 0 := by
    rw [htval]
    dsimp [b']
    rw [inner_sub_left, hbT, inner_normalVector_self, sub_self]
  have hab' : a' ≠ b' := by
    intro heq
    apply hab
    dsimp [a', b'] at heq
    exact sub_left_injective heq
  have hm := midpoint_mem_strict_support_of_face (c := 0) K t.property ha' hb'
    ha'normal hb'normal hab'
  refine ⟨(2 : ℝ)⁻¹ • (a' + b'), hm.1, ?_, hm.2.2⟩
  rw [hm.2.1, htval, K.val.property.2.2.2.1]
  ring

private theorem raisedPolygonSupport_endpoint_contacts_of_angle_lt {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hΘ : Θ.angle < Real.pi / 2)
    (t : angleDomain Θ) (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (hmass : 0 < surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ((∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
          inner ℝ p (normalVector (s : Real.Angle)) =
            polygonHeightValue (raisedPolygonSupport K t ε) s) ∧
      (∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
          inner ℝ p (normalVector (s : Real.Angle)) =
            polygonHeightValue (raisedPolygonSupport K t ε) s - 1)) := by
  obtain ⟨u, hu, huval, hustrict⟩ := exists_upperFace_midpoint_strict K t hmass
  obtain ⟨l, hl, hlval, hlstrict⟩ :=
    exists_lowerFace_midpoint_strict_of_angle_lt K hΘ t ht
  obtain ⟨δu, hδupos, hδu⟩ := exists_pos_uniform_strict_support_gap K u t hustrict
  obtain ⟨δl, hδlpos, hδl⟩ := exists_pos_uniform_strict_support_gap K l t hlstrict
  let o := (stripParallelogram Θ.angle).2.2
  let a := o - tangentVector 0
  let b := o - normalVector (Θ.angle : Real.Angle)
  have ho : o ∈ (K.val.val : Set Point) :=
    stripParallelogram_top_mem_of_angle_lt Θ hΘ K
  have ha : a ∈ (K.val.val : Set Point) :=
    stripParallelogram_top_sub_vertical_mem_of_angle_lt K hΘ
  have hb : b ∈ (K.val.val : Set Point) :=
    stripParallelogram_top_sub_normal_mem_of_angle_lt K hΘ
  have hoω : inner ℝ o (normalVector (Θ.angle : Real.Angle)) = 1 :=
    stripParallelogram_top_inner_angle Θ hΘ
  have hoT : inner ℝ o (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
    simp [o, stripParallelogram, normalVector, frame, PiLp.inner_apply]
  have haT : inner ℝ a (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    simp [a, o, stripParallelogram, tangentVector, normalVector, frame,
      PiLp.inner_apply]
  have hbω : inner ℝ b (normalVector (Θ.angle : Real.Angle)) = 0 := by
    dsimp [b]
    rw [inner_sub_left, hoω, inner_normalVector_self, sub_self]
  let gap := 1 - Real.sin Θ.angle
  have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Θ.angle_pos, Real.pi_pos], hΘ⟩
  have hgappos : 0 < gap := by
    have hcosSq : 0 < Real.cos Θ.angle ^ 2 := sq_pos_of_pos hcos
    have htrig := Real.sin_sq_add_cos_sq Θ.angle
    have hsinle := Real.sin_le_one Θ.angle
    dsimp [gap]
    nlinarith
  have haω : inner ℝ a (normalVector (Θ.angle : Real.Angle)) = gap := by
    dsimp [a, gap]
    rw [inner_sub_left, hoω]
    simp [tangentVector, normalVector, frame, PiLp.inner_apply]
  have hbT : inner ℝ b (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = gap := by
    dsimp [b, gap]
    rw [inner_sub_left, hoT]
    simp [normalVector, frame, PiLp.inner_apply]
  refine ⟨min δu (min δl (min 1 gap)), by positivity, ?_⟩
  intro ε hε hεlt
  have hεu : ε < δu := hεlt.trans_le (min_le_left _ _)
  have hεl : ε < δl := hεlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hε1 : ε < 1 :=
    hεlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεgap : ε < gap :=
    hεlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hmoved := moved_upper_lower_contacts K t ht u l hu huval hl hlval
    hδu hδl hε hεu hεl
  rcases ht with ht | ht
  · have htval : t.val = Θ.angle := ht
    have hoMem : o ∈ polygonHeightCap (raisedPolygonSupport K t ε) := by
      apply mem_raisedPolygonSupport_of_endpoint_of_le_inner K t (Or.inl htval) ho hε.le
      rw [htval, hoω]
      exact hε1.le
    have haMem : a ∈ polygonHeightCap (raisedPolygonSupport K t ε) := by
      apply mem_raisedPolygonSupport_of_endpoint_of_le_inner K t (Or.inl htval) ha hε.le
      rw [htval, haω]
      exact hεgap.le
    have hother : polygonHeightValue (raisedPolygonSupport K t ε) (Real.pi / 2) = 1 := by
      rw [polygonHeightValue_raisedPolygonSupport K t ε (Or.inr (by simp))]
      have hne : (⟨Real.pi / 2, Or.inr (by simp)⟩ : angleDomain Θ) ≠ t := by
        intro heq
        have := congrArg Subtype.val heq
        linarith [hΘ]
      rw [ite_eq_right hne, add_zero, K.val.property.2.2.2.1]
    constructor
    · intro s hs
      rcases hs with hs | hs
      · have hsval : s = Θ.angle := hs
        subst s
        simpa [htval] using hmoved.1
      · have hsval : s = Real.pi / 2 := by simpa using hs
        subst s
        exact ⟨o, hoMem, hoT.trans hother.symm⟩
    · intro s hs
      rcases hs with hs | hs
      · have hsval : s = Θ.angle := hs
        subst s
        simpa [htval] using hmoved.2
      · have hsval : s = Real.pi / 2 := by simpa using hs
        subst s
        refine ⟨a, haMem, ?_⟩
        rw [haT, hother]
        ring
  · have htval : t.val = Real.pi / 2 := by simpa using ht
    have hoMem : o ∈ polygonHeightCap (raisedPolygonSupport K t ε) := by
      apply mem_raisedPolygonSupport_of_endpoint_of_le_inner K t (Or.inr ht) ho hε.le
      rw [htval, hoT]
      exact hε1.le
    have hbMem : b ∈ polygonHeightCap (raisedPolygonSupport K t ε) := by
      apply mem_raisedPolygonSupport_of_endpoint_of_le_inner K t (Or.inr ht) hb hε.le
      rw [htval, hbT]
      exact hεgap.le
    have hother : polygonHeightValue (raisedPolygonSupport K t ε) Θ.angle = 1 := by
      rw [polygonHeightValue_raisedPolygonSupport K t ε (Or.inr (by simp))]
      have hne : (⟨Θ.angle, Or.inr (by simp)⟩ : angleDomain Θ) ≠ t := by
        intro heq
        have := congrArg Subtype.val heq
        linarith [hΘ]
      rw [ite_eq_right hne, add_zero, K.val.property.2.2.1]
    constructor
    · intro s hs
      rcases hs with hs | hs
      · have hsval : s = Θ.angle := hs
        subst s
        exact ⟨o, hoMem, hoω.trans hother.symm⟩
      · have hsval : s = Real.pi / 2 := by simpa using hs
        subst s
        simpa [htval] using hmoved.1
    · intro s hs
      rcases hs with hs | hs
      · have hsval : s = Θ.angle := hs
        subst s
        refine ⟨b, hbMem, ?_⟩
        rw [hbω, hother]
        ring
      · have hsval : s = Real.pi / 2 := by simpa using hs
        subst s
        simpa [htval] using hmoved.2

private theorem raisedPolygonSupport_endpoint_contacts_of_angle_eq {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hΘ : Θ.angle = Real.pi / 2)
    (t : angleDomain Θ) (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (hmass : 0 < surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ((∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
          inner ℝ p (normalVector (s : Real.Angle)) =
            polygonHeightValue (raisedPolygonSupport K t ε) s) ∧
      (∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
          inner ℝ p (normalVector (s : Real.Angle)) =
            polygonHeightValue (raisedPolygonSupport K t ε) s - 1)) := by
  obtain ⟨u, hu, huval, hustrict⟩ := exists_upperFace_midpoint_strict K t hmass
  obtain ⟨l, hl, hlval, hlstrict⟩ :=
    exists_lowerFace_midpoint_strict_of_angle_eq K hΘ t ht hmass
  obtain ⟨δu, hδupos, hδu⟩ := exists_pos_uniform_strict_support_gap K u t hustrict
  obtain ⟨δl, hδlpos, hδl⟩ := exists_pos_uniform_strict_support_gap K l t hlstrict
  have htval : t.val = Real.pi / 2 := by
    rcases ht with ht | ht
    · simpa [hΘ] using ht
    · simpa using ht
  refine ⟨min δu δl, by positivity, ?_⟩
  intro ε hε hεlt
  have hmoved := moved_upper_lower_contacts K t ht u l hu huval hl hlval
    hδu hδl hε (hεlt.trans_le (min_le_left _ _))
      (hεlt.trans_le (min_le_right _ _))
  constructor
  · intro s hs
    have hsval : s = Real.pi / 2 := by
      rcases hs with hs | hs
      · simpa [hΘ] using hs
      · simpa using hs
    subst s
    simpa [htval] using hmoved.1
  · intro s hs
    have hsval : s = Real.pi / 2 := by
      rcases hs with hs | hs
      · simpa [hΘ] using hs
      · simpa using hs
    subst s
    simpa [htval] using hmoved.2

/-- A sufficiently small endpoint height increase preserves both unit widths. -/
theorem polygonCap_positive_height_increment_of_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (hmass : 0 < surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ K' : PolygonCapTranslateSpace Θ,
        K'.val = polygonHeightCap (raisedPolygonSupport K t ε) := by
  obtain ⟨εb, hεb, hbounded⟩ := polygonHeightCap_raised_bounded K t
  obtain ⟨εc, hεc, hcontacts⟩ : ∃ εc : ℝ, 0 < εc ∧ ∀ ε : ℝ, 0 < ε → ε < εc →
      ((∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
          inner ℝ p (normalVector (s : Real.Angle)) =
            polygonHeightValue (raisedPolygonSupport K t ε) s) ∧
      (∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
          inner ℝ p (normalVector (s : Real.Angle)) =
            polygonHeightValue (raisedPolygonSupport K t ε) s - 1)) := by
    rcases lt_or_eq_of_le Θ.angle_le with hΘ | hΘ
    · exact raisedPolygonSupport_endpoint_contacts_of_angle_lt K hΘ t ht hmass
    · exact raisedPolygonSupport_endpoint_contacts_of_angle_eq K hΘ t ht hmass
  refine ⟨min εb εc, by positivity, ?_⟩
  intro ε hε hεlt
  have hb : ε < εb := hεlt.trans_le (min_le_left _ _)
  have hc : ε < εc := hεlt.trans_le (min_le_right _ _)
  have hcontact := hcontacts ε hε hc
  exact exists_polygonCapTranslate_eq_polygonHeightCap _
    (hbounded ε (abs_le.mpr ⟨by linarith, hb.le⟩)) hcontact.1 hcontact.2

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
# Polygon / Height / Positive Increment
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem polygonCap_positive_height_increment {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ)
    (ht : 0 < surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ K' : PolygonCapTranslateSpace Θ,
        K'.val = polygonHeightCap (raisedPolygonSupport K t ε) := by
  by_cases htendpoint : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)
  · exact polygonCap_positive_height_increment_of_endpoint K t htendpoint ht
  · exact polygonCap_positive_height_increment_of_not_endpoint K t htendpoint

end MovingSofa

end

end

end
