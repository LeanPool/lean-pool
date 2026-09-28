/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Cap.Foundations.Development004
public import LeanPool.MovingSofa.ForMathlib.MeasureTheory.Foundations.Development001
public import LeanPool.MovingSofa.Geometry.Foundations.Development001
/-!
# Moving sofa: related mathematical developments

* `Bounds.Niche`.
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
# Bounds / Niche
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace MovingSofa

/-- The infimum of the set’s horizontal coordinates. -/
def horizontalMin (S : Set Point) : ℝ := sInf ((fun p ↦ p 0) '' S)

/-- The supremum of the set’s horizontal coordinates. -/
def horizontalMax (S : Set Point) : ℝ := sSup ((fun p ↦ p 0) '' S)

/-- The niche is measurable, finite-area and enclosed by the specified horizontal-span
rectangle. -/
def HasNicheRectangleBounds (S N : Set Point) : Prop :=
  MeasurableSet N ∧
  N ⊆ {p | horizontalMin S < p 0 ∧ p 0 < horizontalMax S ∧
    0 ≤ p 1 ∧ p 1 < (horizontalMax S - horizontalMin S) / 2} ∧
  volume N < ⊤ ∧
  (horizontalMax S - horizontalMin S = 0 → ClassicalResults.area N = 0)

private theorem niche_coordinate_bounds {c s l r x y : ℝ}
    (hc : 0 < c) (hs : 0 < s) (hcircle : s ^ 2 + c ^ 2 = 1)
    (hlr : l ≤ r) (hy : 0 ≤ y)
    (hx : c * x + s * y < c * r + s - 1)
    (hz : -s * x + c * y < -s * l + c - 1) :
    l < x ∧ x < r ∧ y < (r - l) / 2 := by
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg s]
  have hs1 : s ≤ 1 := by nlinarith [sq_nonneg c]
  have hsc : s * c ≤ 1 / 2 := by nlinarith [sq_nonneg (s - c)]
  have hsum : 1 ≤ s + c := by nlinarith [mul_pos hs hc]
  have hxlo : l < x := by nlinarith [mul_nonneg hc.le hy]
  have hxhi : x < r := by nlinarith [mul_nonneg hs.le hy]
  have h₁ := mul_lt_mul_of_pos_left hx hs
  have h₂ := mul_lt_mul_of_pos_left hz hc
  have hcomb : y < s * c * (r - l) + 1 - s - c := by
    nlinarith [show s ^ 2 * y + c ^ 2 * y = y by nlinarith [hcircle]]
  refine ⟨hxlo, hxhi, hcomb.trans_le ?_⟩
  have := mul_le_mul_of_nonneg_right hsc (sub_nonneg.mpr hlr)
  linarith

theorem horizontalMin_le (K : ConvexBody Point) {p : Point} (hp : p ∈ K) :
    horizontalMin K ≤ p 0 := by
  apply csInf_le ((K.isCompact.image (by fun_prop : Continuous (fun p : Point ↦ p 0))).bddBelow)
  exact ⟨p, hp, rfl⟩

theorem le_horizontalMax (K : ConvexBody Point) {p : Point} (hp : p ∈ K) :
    p 0 ≤ horizontalMax K := by
  apply le_csSup ((K.isCompact.image (by fun_prop : Continuous (fun p : Point ↦ p 0))).bddAbove)
  exact ⟨p, hp, rfl⟩

theorem horizontalMin_le_horizontalMax (K : ConvexBody Point) :
    horizontalMin K ≤ horizontalMax K := by
  obtain ⟨p, hp⟩ := K.nonempty
  exact (horizontalMin_le K hp).trans (le_horizontalMax K hp)

/-- The support value at the horizontal normal is the horizontal maximum. -/
theorem supportValue_zero_eq_horizontalMax (S : Set Point) :
    supportValue S ((0 : ℝ) : Real.Angle) = horizontalMax S := by
  rw [supportValue, horizontalMax]
  congr 1
  refine Set.image_congr fun p _ ↦ ?_
  rw [inner_normalVector_real, Real.cos_zero, Real.sin_zero, mul_one, mul_zero, add_zero]

/-- The support value at the straight angle negates the horizontal minimum. -/
theorem supportValue_pi_eq_neg_horizontalMin (S : Set Point) :
    supportValue S ((Real.pi : ℝ) : Real.Angle) = -horizontalMin S := by
  have himage : (fun p : Point ↦ -p 0) '' S = -((fun p : Point ↦ p 0) '' S) := by
    ext x
    simp [neg_eq_iff_eq_neg]
  rw [supportValue, horizontalMin, ← Real.sSup_neg, ← himage]
  congr 1
  refine Set.image_congr fun p _ ↦ ?_
  rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi, mul_neg_one, mul_zero, add_zero]

/-- Both horizontal extrema of a compact convex body are attained. -/
theorem exists_horizontal_extrema (K : ConvexBody Point) :
    ∃ l r : Point, l ∈ (K : Set Point) ∧ r ∈ (K : Set Point) ∧
      l 0 = horizontalMin K ∧ r 0 = horizontalMax K := by
  obtain ⟨l, hlK, hl⟩ := K.isCompact.exists_isMinOn K.nonempty
    (by fun_prop : Continuous (fun p : Point ↦ p 0)).continuousOn
  obtain ⟨r, hrK, hr⟩ := K.isCompact.exists_isMaxOn K.nonempty
    (by fun_prop : Continuous (fun p : Point ↦ p 0)).continuousOn
  refine ⟨l, r, hlK, hrK, ?_, ?_⟩
  · apply le_antisymm
    · apply le_csInf (K.nonempty.image _)
      rintro _ ⟨p, hp, rfl⟩
      exact hl hp
    · exact horizontalMin_le K hlK
  · apply le_antisymm
    · exact le_horizontalMax K hrK
    · apply csSup_le (K.nonempty.image _)
      rintro _ ⟨p, hp, rfl⟩
      exact hr hp

theorem CapSpace.mem_horizontalStrip {ω : ℝ} (K : CapSpace ω)
    {p : Point} (hp : p ∈ K.val) : 0 ≤ p 1 ∧ p 1 ≤ 1 := by
  have hupper := inner_le_supportValue K.val hp ((Real.pi / 2 : ℝ) : Real.Angle)
  have hlower := inner_le_supportValue K.val hp ((3 * Real.pi / 2 : ℝ) : Real.Angle)
  rw [K.property.2.2.2.1] at hupper
  rw [K.property.2.2.2.2.2.1] at hlower
  rw [show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring] at hlower
  simp [normalVector, frame, PiLp.inner_apply, Real.sin_add, Real.cos_add,
    -Real.Angle.coe_add] at hupper hlower
  exact ⟨by linarith, hupper⟩

/-- A cap has area at most its horizontal width. -/
theorem CapSpace.area_le_horizontalWidth {ω : ℝ} (K : CapSpace ω) :
    ClassicalResults.area (K.val : Set Point) ≤ horizontalMax K.val - horizontalMin K.val := by
  let R : Set Point := {p | p 0 ∈ Set.Icc (horizontalMin K.val) (horizontalMax K.val) ∧
    p 1 ∈ Set.Icc 0 1}
  have hsub : (K.val : Set Point) ⊆ R := fun p hp ↦
    ⟨⟨horizontalMin_le K.val hp, le_horizontalMax K.val hp⟩, K.mem_horizontalStrip hp⟩
  have hvol : volume R = ENNReal.ofReal (horizontalMax K.val - horizontalMin K.val) := by
    rw [EuclideanSpace.volume_setOf_apply_mem_Icc]
    simp
  have hfinite : volume R ≠ ⊤ := by rw [hvol]; exact ENNReal.ofReal_ne_top
  calc
    ClassicalResults.area (K.val : Set Point) ≤ ClassicalResults.area R :=
      ENNReal.toReal_mono hfinite (measure_mono hsub)
    _ = horizontalMax K.val - horizontalMin K.val := by
      change (volume R).toReal = _
      rw [hvol, ENNReal.toReal_ofReal (sub_nonneg.mpr (horizontalMin_le_horizontalMax K.val))]

/-- Upper support bounds from the horizontal extrema and the unit-height strip. -/
theorem CapSpace.supportValue_horizontal_bounds {ω t : ℝ} (K : CapSpace ω)
    (ht : t ∈ Set.Ioo 0 ω) :
    supportValue K.val (t : Real.Angle) ≤
      Real.cos t * horizontalMax K.val + Real.sin t ∧
    supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) ≤
      -Real.sin t * horizontalMin K.val + Real.cos t := by
  have hc : 0 ≤ Real.cos t := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_le K.property.2.1⟩).le
  have hs : 0 ≤ Real.sin t := (Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [ht.2, K.property.2.1, Real.pi_pos])).le
  constructor
  · apply csSup_le (K.val.nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    have hx := mul_le_mul_of_nonneg_left (le_horizontalMax K.val hp) hc
    have hy := mul_le_mul_of_nonneg_left (K.mem_horizontalStrip hp).2 hs
    simp [normalVector, frame, PiLp.inner_apply]
    nlinarith
  · apply csSup_le (K.val.nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    have hx := mul_le_mul_of_nonneg_left (horizontalMin_le K.val hp) hs
    have hy := mul_le_mul_of_nonneg_left (K.mem_horizontalStrip hp).2 hc
    simp [normalVector, frame, PiLp.inner_apply, Real.cos_add, Real.sin_add,
      -Real.Angle.coe_add]
    nlinarith

/-- Lower support bounds from the horizontal extrema and the nonnegative heights of a cap. -/
theorem CapSpace.horizontal_le_supportValue {ω t : ℝ} (K : CapSpace ω)
    (hs : 0 ≤ Real.sin t) (hc : 0 ≤ Real.cos t) :
    Real.cos t * horizontalMax K.val ≤ supportValue K.val (t : Real.Angle) ∧
    -Real.sin t * horizontalMin K.val ≤
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
  have hcompact := K.val.isCompact.image (by fun_prop : Continuous (fun p : Point ↦ p 0))
  have hne := K.val.nonempty.image (fun p : Point ↦ p 0)
  constructor
  · obtain ⟨p, hp, hpmax⟩ := hcompact.sSup_mem hne
    have hinner := inner_le_supportValue K.val hp (t : Real.Angle)
    have hy := (K.mem_horizontalStrip hp).1
    simp [normalVector, frame, PiLp.inner_apply] at hinner
    change p 0 = horizontalMax K.val at hpmax
    rw [← hpmax]
    nlinarith [mul_nonneg hs hy]
  · obtain ⟨p, hp, hpmin⟩ := hcompact.sInf_mem hne
    have hinner := inner_le_supportValue K.val hp ((t + Real.pi / 2 : ℝ) : Real.Angle)
    have hy := (K.mem_horizontalStrip hp).1
    simp [normalVector, frame, PiLp.inner_apply, Real.cos_add, Real.sin_add,
      -Real.Angle.coe_add] at hinner
    change p 0 = horizontalMin K.val at hpmin
    rw [← hpmin]
    nlinarith [mul_nonneg hc hy]

private theorem mem_niche_rectangle {ω t : ℝ} (K : CapSpace ω)
    (ht : t ∈ Set.Ioo 0 ω) {p : Point}
    (hf : p ∈ capFan ω) (hq : p ∈ innerQuadrant K.val t) :
    horizontalMin K.val < p 0 ∧ p 0 < horizontalMax K.val ∧
      0 ≤ p 1 ∧ p 1 < (horizontalMax K.val - horizontalMin K.val) / 2 := by
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_le K.property.2.1⟩
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [ht.2, K.property.2.1, Real.pi_pos])
  have hy : 0 ≤ p 1 := by
    have := hf.2
    simpa [normalHalfPlane, normalVector, frame, PiLp.inner_apply] using this
  obtain ⟨h₁, h₂⟩ := hq
  change inner ℝ p (normalVector (t : Real.Angle)) < supportValue K.val _ - 1 at h₁
  change inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
    supportValue K.val _ - 1 at h₂
  have hbounds := K.supportValue_horizontal_bounds ht
  have hx : Real.cos t * p 0 + Real.sin t * p 1 <
      Real.cos t * horizontalMax K.val + Real.sin t - 1 := by
    have := h₁.trans_le (sub_le_sub_right hbounds.1 1)
    simpa [normalVector, frame, PiLp.inner_apply, mul_comm] using this
  have hz : -Real.sin t * p 0 + Real.cos t * p 1 <
      -Real.sin t * horizontalMin K.val + Real.cos t - 1 := by
    have := h₂.trans_le (sub_le_sub_right hbounds.2 1)
    simpa [normalVector, frame, PiLp.inner_apply, Real.cos_add, Real.sin_add,
      -Real.Angle.coe_add, mul_comm] using this
  obtain ⟨hl, hr, hh⟩ := niche_coordinate_bounds hc hs (Real.sin_sq_add_cos_sq t)
    (horizontalMin_le_horizontalMax K.val) hy hx hz
  exact ⟨hl, hr, hy, hh⟩

theorem capNiche_subset_rectangle {ω : ℝ} (K : CapSpace ω) :
    capNiche K ⊆ {p | horizontalMin K.val < p 0 ∧ p 0 < horizontalMax K.val ∧
      0 ≤ p 1 ∧ p 1 < (horizontalMax K.val - horizontalMin K.val) / 2} := by
  rintro p ⟨hf, hq⟩
  obtain ⟨t, ht, hq⟩ := Set.mem_iUnion₂.mp hq
  exact mem_niche_rectangle K ht hf hq

theorem polygonNiche_subset_capNiche (Θ : AngleSet) (K : CapSpace Θ.angle) :
    polygonNiche Θ K ⊆ capNiche K := by
  rintro p ⟨hf, hq⟩
  obtain ⟨t, ht, hq⟩ := Set.mem_iUnion₂.mp hq
  exact ⟨hf, Set.mem_iUnion₂.mpr ⟨t, Θ.interior t ht, hq⟩⟩

private theorem isBounded_coordinate_rectangle (l r h : ℝ) :
    Bornology.IsBounded {p : Point | l < p 0 ∧ p 0 < r ∧ 0 ≤ p 1 ∧ p 1 < h} := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨|l| + |r| + |h|, ?_⟩
  rintro p ⟨hl, hr, hy, hh⟩
  have hx : |p 0| ≤ |l| + |r| := abs_le.mpr ⟨by
    have := neg_abs_le l
    linarith [abs_nonneg r], by linarith [le_abs_self r, abs_nonneg l]⟩
  have hy' : |p 1| ≤ |h| := by rw [abs_of_nonneg hy]; exact hh.le.trans (le_abs_self h)
  have hx2 := sq_le_sq₀ (abs_nonneg (p 0)) (by positivity : 0 ≤ |l| + |r|) |>.mpr hx
  have hy2 := sq_le_sq₀ (abs_nonneg (p 1)) (abs_nonneg h) |>.mpr hy'
  have hn := EuclideanSpace.norm_sq_eq p
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hn hx2 hy2
  nlinarith [mul_nonneg (by positivity : 0 ≤ |l| + |r|) (abs_nonneg h), norm_nonneg p,
    abs_nonneg l, abs_nonneg r, abs_nonneg h, sq_abs h]

private theorem isClosed_capFan (ω : ℝ) : IsClosed (capFan ω) := by
  apply IsClosed.inter
  · exact isClosed_le continuous_const (by fun_prop)
  · exact isClosed_le continuous_const (by fun_prop)

private theorem isOpen_innerQuadrant (S : Set Point) (t : ℝ) :
    IsOpen (innerQuadrant S t) := by
  apply IsOpen.inter
  · exact isOpen_lt (by fun_prop) continuous_const
  · exact isOpen_lt (by fun_prop) continuous_const

theorem measurableSet_capNiche {ω : ℝ} (K : CapSpace ω) : MeasurableSet (capNiche K) :=
  (isClosed_capFan ω).measurableSet.inter
    (isOpen_iUnion fun t ↦ isOpen_iUnion fun _ ↦ isOpen_innerQuadrant K.val t).measurableSet

theorem measurableSet_polygonNiche (Θ : AngleSet) (K : CapSpace Θ.angle) :
    MeasurableSet (polygonNiche Θ K) :=
  (isClosed_capFan Θ.angle).measurableSet.inter
    (isOpen_iUnion fun t ↦ isOpen_iUnion fun _ ↦ isOpen_innerQuadrant K.val t).measurableSet

private theorem hasNicheRectangleBounds_of_subset {ω : ℝ} (K : CapSpace ω)
    {N : Set Point} (hm : MeasurableSet N) (hN : N ⊆ capNiche K) :
    HasNicheRectangleBounds K.val N := by
  have hb := hN.trans (capNiche_subset_rectangle K)
  refine ⟨hm, hb, (isBounded_coordinate_rectangle _ _ _).subset hb |>.measure_lt_top, ?_⟩
  intro hd
  have he : N = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have := hb hp
    linarith [this.1, this.2.1]
  simp [he, ClassicalResults.area]

private theorem niche_subset_uniform_rectangle {ω R : ℝ} (K : CapSpace ω)
    (hR : ∀ p ∈ (K.val : Set Point), |p 0| ≤ R) :
    capNiche K ⊆ {p | |p 0| ≤ R ∧ 0 ≤ p 1 ∧ p 1 ≤ R} := by
  have hlo : -R ≤ horizontalMin K.val := by
    apply le_csInf (K.val.nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    exact (abs_le.mp (hR p hp)).1
  have hhi : horizontalMax K.val ≤ R := by
    apply csSup_le (K.val.nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    exact (abs_le.mp (hR p hp)).2
  intro p hp
  obtain ⟨hl, hr, hy, hh⟩ := capNiche_subset_rectangle K hp
  exact ⟨abs_le.mpr ⟨hlo.trans hl.le, hr.le.trans hhi⟩, hy, by linarith⟩

theorem niche_uniform_bounds :
    (∀ (ω : ℝ) (K : CapSpace ω),
      HasNicheRectangleBounds (K.val : Set Point) (capNiche K)) ∧
    (∀ (Θ : AngleSet) (K : CapSpace Θ.angle),
      HasNicheRectangleBounds (K.val : Set Point) (polygonNiche Θ K)) ∧
    (∀ (ω : ℕ → ℝ) (K : ∀ i, CapSpace (ω i)) (L : ConvexBody Point),
      Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point) (L : Set Point))
        atTop (𝓝 0) →
      ∃ R : ℝ, 0 ≤ R ∧
        (∀ i, capNiche (K i) ⊆ {p | |p 0| ≤ R ∧ 0 ≤ p 1 ∧ p 1 ≤ R}) ∧
        (∀ i (Θ : AngleSet) (P : CapSpace Θ.angle),
          (P.val : Set Point) = ((K i).val : Set Point) →
          polygonNiche Θ P ⊆ {p | |p 0| ≤ R ∧ 0 ≤ p 1 ∧ p 1 ≤ R})) := by
  refine ⟨fun _ K ↦ hasNicheRectangleBounds_of_subset K (measurableSet_capNiche K) Set.Subset.rfl,
    fun Θ K ↦ hasNicheRectangleBounds_of_subset K (measurableSet_polygonNiche Θ K)
      (polygonNiche_subset_capNiche Θ K), ?_⟩
  intro ω K L hlim
  obtain ⟨A, hA⟩ := (Metric.isBounded_range_of_tendsto _ hlim).exists_norm_le
  obtain ⟨B, hB⟩ := L.isCompact.isBounded.exists_norm_le
  let R := |A| + |B| + 1
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hcarriers : ∀ i p, p ∈ ((K i).val : Set Point) → |p 0| ≤ R := by
    intro i p hp
    have hdist : Metric.hausdorffDist ((K i).val : Set Point) (L : Set Point) < |A| + 1 := by
      have := hA _ (Set.mem_range_self i)
      rw [Real.norm_eq_abs] at this
      exact lt_of_le_of_lt ((le_abs_self _).trans (this.trans (le_abs_self A))) (by linarith)
    obtain ⟨q, hq, hpq⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hp hdist
      (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (K i).val.nonempty L.nonempty (K i).val.isCompact.isBounded L.isCompact.isBounded)
    have hnorm : ‖p‖ ≤ R := by
      have ht := norm_add_le (p - q) q
      rw [sub_add_cancel] at ht
      rw [dist_eq_norm] at hpq
      have hb := (hB q hq).trans (le_abs_self B)
      dsimp [R]
      linarith
    have hc : |p 0| ≤ ‖p‖ := by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le p 0)
    exact hc.trans hnorm
  refine ⟨R, hR0, fun i ↦ niche_subset_uniform_rectangle (K i) (hcarriers i), ?_⟩
  intro i Θ P hP
  apply (polygonNiche_subset_capNiche Θ P).trans
  apply niche_subset_uniform_rectangle P
  intro p hp
  exact hcarriers i p (hP ▸ hp)

end MovingSofa

end

end

end
