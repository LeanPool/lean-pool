/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Analysis.Foundations.Development005
public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development002
public import LeanPool.MovingSofa.Cap.Applications.Development001
public import LeanPool.MovingSofa.Cap.Foundations.Development002
public import LeanPool.MovingSofa.Geometry.Foundations.Development003
public import LeanPool.MovingSofa.Polygon.Foundations.Development002

/-!
# Moving sofa: related mathematical developments

* `Polygon.BalancedContainment`.
* `Polygon.Polyline.Length.Basic`.
* `Polygon.Polyline.Length.Boundary`.
* `Polygon.Polyline.Length`.
* `Polygon.Balancing.Coefficients`.
* `Polygon.Balancing.Estimate`.
* `Polygon.Balancing`.
* `Polygon.EdgeNormals`.
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
# Polygon / Balanced Containment
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Balance bounds the polyline projections by the surface-area atoms. -/
theorem polygonCapPolyline_inner_le_of_balanced {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hK : IsBalancedPolygonCap K)
    (D : Finset ℝ) (hD : (D : Set ℝ) = angleDomain Θ) (s : ℝ)
    {q : Point} (hq : q ∈ (polygonCapPolyline K).carrier) :
    inner ℝ q (normalVector (s : Real.Angle)) ≤
      inner ℝ ((capVertices K.val 0).1.2) (normalVector (s : Real.Angle)) +
      ∑ u ∈ D, (surfaceAreaMeasure K.val.val {(u : Real.Angle)}).toReal *
        max (Real.sin (s - u)) 0 := by
  classical
  have hp : IsCapPolyline K (polygonCapPolyline K) := (polygonCap_polyline K).choose_spec
  have hmem (u : ℝ) (hu : u ∈ D) : u ∈ angleDomain Θ := by
    rw [← hD]
    exact hu
  have hb := (polygonCapPolyline K).inner_le_endpoint_add_sum_normal_lengths D
    (fun u hu ↦ angleDomain_subset_Ioo Θ (hmem u hu))
    (fun i ↦ by
      obtain ⟨t, ht⟩ := hp.2.2.2.1 i
      refine ⟨t.val, ?_, ht⟩
      have := t.property
      simpa only [← hD, Finset.mem_coe] using this) s hq
  rw [hp.2.2.1] at hb
  convert hb using 2
  apply Finset.sum_congr rfl
  intro u hu
  have heq := hK ⟨u, hmem u hu⟩
  rw [heq, ENNReal.toReal_ofReal]
  · rfl
  · unfold polygonCapPolylineLength
    positivity

/-- A balanced polygon cap bounds every upper-normal projection of its polyline. -/
theorem polygonCapPolyline_inner_le_support_of_balanced {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hK : IsBalancedPolygonCap K)
    (D : Finset ℝ) (hD : (D : Set ℝ) = angleDomain Θ)
    {s : ℝ} (hs : s ∈ Set.Ioo 0 Real.pi)
    {q : Point} (hq : q ∈ (polygonCapPolyline K).carrier) :
    inner ℝ q (normalVector (s : Real.Angle)) ≤ supportValue K.val.val (s : Real.Angle) := by
  have hpoly := polygonCapPolyline_inner_le_of_balanced K hK D hD s hq
  have hsum := sum_surfaceAreaMeasure_mul_pos_sin_le K.val.val D
    (fun t ht ↦ angleDomain_subset_Ioo Θ (by rw [← hD]; exact ht)) hs
  have hstart := inner_negativeVertex_zero_le_positiveVertex K.val.val ⟨hs.1.le, hs.2.le⟩
  change inner ℝ q (normalVector (s : Real.Angle)) ≤
    inner ℝ (edgeVertices K.val.val 0).2 (normalVector (s : Real.Angle)) + _ at hpoly
  rw [real_inner_comm (normalVector (s : Real.Angle)) (edgeVertices K.val.val 0).2] at hpoly
  linarith

/-- The polyline of a balanced polygon cap lies inside the cap. -/
theorem polygonCapPolyline_subset_of_balanced {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hK : IsBalancedPolygonCap K) :
    (polygonCapPolyline K).carrier ⊆ (K.val.val : Set Point) := by
  classical
  let D := Θ.directions ∪ Θ.directions.image (fun t ↦ t + Real.pi / 2) ∪
    {Θ.angle, Real.pi / 2}
  have hD : (D : Set ℝ) = angleDomain Θ := by
    simp [D, angleDomain]
  intro q hq
  have hp : IsCapPolyline K (polygonCapPolyline K) := (polygonCap_polyline K).choose_spec
  have hfront : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
    rw [hp.2.2.2.2.2.1]
    exact Or.inl (Or.inr hq)
  have hfan : q ∈ capFan Θ.angle := by
    have hmem := frontier_subset_closure hfront
    rw [hp.2.2.2.2.1.closure_eq] at hmem
    exact hmem.1
  rw [K.property.eq_iInter_supportValue]
  simp only [Set.mem_iInter]
  intro a ha
  rcases ha with ⟨t, ht, rfl⟩ | ha
  · exact polygonCapPolyline_inner_le_support_of_balanced K hK D hD
      (angleDomain_subset_Ioo Θ ht) hq
  rcases ha with rfl | rfl
  · change inner ℝ q (normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle)) ≤
      supportValue K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right]
    exact neg_nonpos.mpr hfan.1
  · have hang : ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
        (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) := by
      congr 1
      ring
    change inner ℝ q (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤
      supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.2.1, hang, normalVector_add_pi, inner_neg_right]
    exact neg_nonpos.mpr hfan.2

/-- A polygon niche lies in its cap whenever its upper boundary polyline does. -/
theorem polygonNiche_subset_of_polyline_subset {Θ : AngleSet}
    (K : PolygonCapSpace Θ)
    (hpoly : (polygonCapPolyline K).carrier ⊆ (K.val.val : Set Point)) :
    polygonNiche Θ K.val ⊆ (K.val.val : Set Point) := by
  intro q hq
  have hfan : q ∈ capFan Θ.angle := hq.1
  have hheight : q 1 < capBoundaryHeight K (q 0) := by
    by_contra hn
    have hmem : q ∈ capFan Θ.angle \ polygonNiche Θ K.val := by
      rw [capFan_sdiff_polygonNiche_eq_epigraph K]
      exact le_of_not_gt hn
    exact hmem.2 hq
  let r := pointOnGraph (capBoundaryHeight K) (q 0)
  have hrx : r 0 = q 0 := by simp [r, pointOnGraph]
  have hry : q 1 < r 1 := by simpa [r, pointOnGraph] using hheight
  have hrfront : r ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
    rw [(capFan_sdiff_polygonNiche_closed_frontier K).2]
    exact ⟨q 0, rfl⟩
  have hp : IsCapPolyline K (polygonCapPolyline K) := (polygonCap_polyline K).choose_spec
  rw [hp.2.2.2.2.2.1] at hrfront
  have hrpoly : r ∈ (polygonCapPolyline K).carrier := by
    rcases hrfront with (hrleft | hrpoly) | hrright
    · obtain ⟨c, hc, hr⟩ := hrleft
      have hrzero : inner ℝ r (normalVector (Θ.angle : Real.Angle)) = 0 := by
        rw [hr, capVertices_angle_fst_eq K, inner_add_left,
          real_inner_smul_left, real_inner_smul_left]
        have hz : inner ℝ (tangentVector (Θ.angle : Real.Angle))
            (normalVector (Θ.angle : Real.Angle)) = 0 := by
          rw [real_inner_comm (normalVector (Θ.angle : Real.Angle))]
          exact inner_normalVector_tangentVector Θ.angle
        rw [hz]
        ring
      have hqnonneg := hfan.1
      change 0 ≤ inner ℝ q (normalVector (Θ.angle : Real.Angle)) at hqnonneg
      have hs : 0 < Real.sin Θ.angle := Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
        (by linarith [Θ.angle_le, Real.pi_pos])
      simp [normalVector, frame, PiLp.inner_apply, hrx] at hrzero hqnonneg
      exfalso
      nlinarith
    · exact hrpoly
    · obtain ⟨c, hc, hr⟩ := hrright
      have hrzero : r 1 = 0 := by
        rw [hr, capVertices_zero_snd_eq K]
        simp [normalVector, frame]
      have hqnonneg := hfan.2
      change 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hqnonneg
      simp [normalVector, frame, PiLp.inner_apply] at hqnonneg
      exfalso
      linarith
  exact K.val.mem_of_fst_eq_of_snd_le (hpoly hrpoly) hfan hrx.symm hry.le

/-- Every balanced polygon cap contains its polygon niche. -/
theorem polygonNiche_subset_of_balanced {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hK : IsBalancedPolygonCap K) :
    polygonNiche Θ K.val ⊆ (K.val.val : Set Point) :=
  polygonNiche_subset_of_polyline_subset K (polygonCapPolyline_subset_of_balanced K hK)

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
# Polygon / Polyline / Length / Basic
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Extend the directional polyline-length function by zero outside the angle domain. -/
def polygonPolylineLengthAt {Θ : AngleSet} (K : PolygonCapSpace Θ) (t : ℝ) : ℝ := by
  classical
  exact if ht : t ∈ angleDomain Θ then polygonCapPolylineLength K ⟨t, ht⟩ else 0

/-- The one-dimensional Hausdorff measure of the niche frontier inside a specified set. -/
def nicheBoundaryLength {Θ : AngleSet} (K : PolygonCapSpace Θ) (S : Set Point) : ℝ :=
  (MeasureTheory.Measure.hausdorffMeasure 1 (frontier (polygonNiche Θ K.val) ∩ S)).toReal

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
# Polygon / Polyline / Length / Boundary
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

private lemma fst_mem_Icc_of_mem_segment_mc4d199c {a b q : Point}
    (hab : a 0 ≤ b 0) (hq : q ∈ segment ℝ a b) : q 0 ∈ Set.Icc (a 0) (b 0) := by
  rw [segment_eq_image'] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  change a 0 + r * (b 0 - a 0) ∈ Set.Icc (a 0) (b 0)
  constructor <;> nlinarith [hr.1, hr.2]

private theorem frontier_inter_open_eq_frontier_sdiff_open_on_interior
    {F X : Set Point} :
    frontier (F ∩ X) ∩ interior F = frontier (F \ X) ∩ interior F := by
  have hInt : IsOpen (interior F) := isOpen_interior
  calc
    frontier (F ∩ X) ∩ interior F =
        frontier ((F ∩ X) ∩ interior F) ∩ interior F :=
      (frontier_inter_open_inter hInt).symm
    _ = frontier (X ∩ interior F) ∩ interior F := by
      congr 2
      ext p
      simp only [Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨-, hpX⟩, hpF⟩
        exact ⟨hpX, hpF⟩
      · rintro ⟨hpX, hpF⟩
        exact ⟨⟨interior_subset hpF, hpX⟩, hpF⟩
    _ = frontier X ∩ interior F := frontier_inter_open_inter hInt
    _ = frontier Xᶜ ∩ interior F := by rw [frontier_compl]
    _ = frontier (Xᶜ ∩ interior F) ∩ interior F :=
      (frontier_inter_open_inter hInt).symm
    _ = frontier ((F \ X) ∩ interior F) ∩ interior F := by
      congr 2
      ext p
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
      constructor
      · rintro ⟨hpX, hpF⟩
        exact ⟨⟨interior_subset hpF, hpX⟩, hpF⟩
      · rintro ⟨⟨-, hpX⟩, hpF⟩
        exact ⟨hpX, hpF⟩
    _ = frontier (F \ X) ∩ interior F := frontier_inter_open_inter hInt

private theorem frontier_inter_open_symmDiff_subset_frontier
    {F X : Set Point} (hF : IsClosed F) :
    (frontier (F ∩ X) \ frontier (F \ X)) ∪
        (frontier (F \ X) \ frontier (F ∩ X)) ⊆ frontier F := by
  have heq := frontier_inter_open_eq_frontier_sdiff_open_on_interior (F := F) (X := X)
  intro p hp
  by_contra hpF
  have hmemF_of_left (hpN : p ∈ frontier (F ∩ X)) : p ∈ F := by
    have hpcl : p ∈ closure (F ∩ X) := frontier_subset_closure hpN
    exact hF.closure_eq ▸ closure_mono Set.inter_subset_left hpcl
  have hmemF_of_right (hpC : p ∈ frontier (F \ X)) : p ∈ F := by
    have hpcl : p ∈ closure (F \ X) := frontier_subset_closure hpC
    exact hF.closure_eq ▸ closure_mono Set.sdiff_subset hpcl
  rcases hp with hp | hp
  · have hpInt : p ∈ interior F := by
      simpa using (mem_frontier_iff_notMem_interior (hmemF_of_left hp.1)).not.mp hpF
    have : p ∈ frontier (F \ X) ∩ interior F := heq ▸ ⟨hp.1, hpInt⟩
    exact hp.2 this.1
  · have hpInt : p ∈ interior F := by
      simpa using (mem_frontier_iff_notMem_interior (hmemF_of_right hp.1)).not.mp hpF
    have : p ∈ frontier (F ∩ X) ∩ interior F := heq.symm ▸ ⟨hp.1, hpInt⟩
    exact hp.2 this.1

private theorem measure_eq_of_symmDiff_subset_null
    (μ : Measure Point) {A B E : Set Point}
    (hsub : (A \ B) ∪ (B \ A) ⊆ E) (hE : μ E = 0) : μ A = μ B := by
  apply measure_congr
  rw [ae_eq_set]
  constructor
  · exact measure_mono_null (fun _ hp ↦ hsub (Or.inl hp)) hE
  · exact measure_mono_null (fun _ hp ↦ hsub (Or.inr hp)) hE

/-- The fan clipping the niche is closed. -/
theorem isClosed_capFan (ω : ℝ) : IsClosed (capFan ω) := by
  unfold capFan normalHalfPlane
  exact (isClosed_le continuous_const (by fun_prop)).inter
    (isClosed_le continuous_const (by fun_prop))

/-- The inward quadrant of a supporting hallway is open. -/
theorem isOpen_innerQuadrant (S : Set Point) (t : ℝ) :
    IsOpen (innerQuadrant S t) := by
  unfold innerQuadrant normalHalfPlane
  exact (isOpen_lt (by fun_prop) continuous_const).inter
    (isOpen_lt (by fun_prop) continuous_const)

private theorem frontier_normalHalfPlane_lower_strict_subset_normalLine
    (t : Real.Angle) (h : ℝ) :
    frontier (normalHalfPlane t h false true) ⊆ normalLine t h := by
  change frontier {p : Point | inner ℝ p (normalVector t) < h} ⊆
    {p | inner ℝ p (normalVector t) = h}
  exact frontier_lt_subset_eq (by fun_prop) continuous_const

private theorem frontier_normalHalfPlane_upper_closed_subset_normalLine
    (t : Real.Angle) (h : ℝ) :
    frontier (normalHalfPlane t h true false) ⊆ normalLine t h := by
  change frontier {p : Point | h ≤ inner ℝ p (normalVector t)} ⊆
    {p | inner ℝ p (normalVector t) = h}
  exact frontier_ge_subset_eq continuous_const (by fun_prop)

private def polygonCapBoundaryLines {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    Finset (Real.Angle × ℝ) := by
  classical
  exact {(((Θ.angle : ℝ) : Real.Angle), 0),
      (((Real.pi / 2 : ℝ) : Real.Angle), 0)} ∪
    Θ.directions.biUnion fun t ↦
      {(((t : ℝ) : Real.Angle), supportValue K.val.val (t : Real.Angle) - 1),
        (((t + Real.pi / 2 : ℝ) : Real.Angle),
          supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)}

private theorem frontier_capFan_subset_boundaryLines {Θ : AngleSet}
    (K : PolygonCapSpace Θ) :
    frontier (capFan Θ.angle) ⊆
      ⋃ l ∈ polygonCapBoundaryLines K, normalLine l.1 l.2 := by
  intro p hp
  have hp' := frontier_inter_subset
    (normalHalfPlane (Θ.angle : Real.Angle) 0 true false)
    (normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false) hp
  rcases hp' with hp' | hp'
  · have hline := frontier_normalHalfPlane_upper_closed_subset_normalLine
      (Θ.angle : Real.Angle) 0 hp'.1
    apply Set.mem_iUnion₂.mpr
    exact ⟨(((Θ.angle : ℝ) : Real.Angle), 0), by simp [polygonCapBoundaryLines], hline⟩
  · have hline := frontier_normalHalfPlane_upper_closed_subset_normalLine
      ((Real.pi / 2 : ℝ) : Real.Angle) 0 hp'.2
    apply Set.mem_iUnion₂.mpr
    exact ⟨(((Real.pi / 2 : ℝ) : Real.Angle), 0),
      by simp [polygonCapBoundaryLines], hline⟩

private theorem frontier_innerQuadrant_subset_boundaryLines {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    frontier (innerQuadrant K.val.val t) ⊆
      ⋃ l ∈ polygonCapBoundaryLines K, normalLine l.1 l.2 := by
  classical
  intro p hp
  have hp' := frontier_inter_subset
    (normalHalfPlane (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1)
      false true)
    (normalHalfPlane ((t + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) false true) hp
  rcases hp' with hp' | hp'
  · have hline := frontier_normalHalfPlane_lower_strict_subset_normalLine
      (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1) hp'.1
    apply Set.mem_iUnion₂.mpr
    refine ⟨(((t : ℝ) : Real.Angle), supportValue K.val.val (t : Real.Angle) - 1),
      ?_, hline⟩
    simp only [polygonCapBoundaryLines, Finset.mem_union]
    right
    exact Finset.mem_biUnion.mpr ⟨t, ht, by simp⟩
  · have hline := frontier_normalHalfPlane_lower_strict_subset_normalLine
      ((t + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) hp'.2
    apply Set.mem_iUnion₂.mpr
    refine ⟨(((t + Real.pi / 2 : ℝ) : Real.Angle),
      supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1), ?_, hline⟩
    simp only [polygonCapBoundaryLines, Finset.mem_union]
    right
    exact Finset.mem_biUnion.mpr ⟨t, ht, by simp⟩

private theorem frontier_polygonComplement_subset_boundaryLines {Θ : AngleSet}
    (K : PolygonCapSpace Θ) :
    frontier (capFan Θ.angle \ polygonNiche Θ K.val) ⊆
      ⋃ l ∈ polygonCapBoundaryLines K, normalLine l.1 l.2 := by
  let X : Set Point := ⋃ t ∈ Θ.directions, innerQuadrant K.val.val t
  have hset : capFan Θ.angle \ polygonNiche Θ K.val = capFan Θ.angle \ X := by
    simp [polygonNiche, X]
  rw [hset, Set.sdiff_eq]
  intro p hp
  have hp' := frontier_inter_subset (capFan Θ.angle) Xᶜ hp
  rcases hp' with hp | hp
  · exact frontier_capFan_subset_boundaryLines K hp.1
  · have hpX : p ∈ frontier X := by simpa [frontier_compl] using hp.2
    have hmem := Finset.frontier_biUnion_subset Θ.directions
      (fun t ↦ innerQuadrant K.val.val t) hpX
    obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hmem
    exact frontier_innerQuadrant_subset_boundaryLines K ht hpt

private theorem real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
    {v : Point} (hv : v ≠ 0) {s t : ℝ}
    (hs : s ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi)
    (hvs : inner ℝ v (normalVector (s : Real.Angle)) = 0)
    (hvt : inner ℝ v (normalVector (t : Real.Angle)) = 0) : s = t := by
  apply eq_of_inner_sub_normalVector_eq_zero_of_ne (a := 0) (b := v) hs ht hv.symm
  · simpa using hvs
  · simpa using hvt

private theorem normalLine_inter_normalLine_subsingleton {s t c d : ℝ}
    (hs : s ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi) (hst : s ≠ t) :
    (normalLine (s : Real.Angle) c ∩ normalLine (t : Real.Angle) d).Subsingleton := by
  intro p hp q hq
  by_contra hpq
  have hv : p - q ≠ 0 := sub_ne_zero.mpr hpq
  have hsorth : inner ℝ (p - q) (normalVector (s : Real.Angle)) = 0 := by
    have hps : inner ℝ p (normalVector (s : Real.Angle)) = c := hp.1
    have hqs : inner ℝ q (normalVector (s : Real.Angle)) = c := hq.1
    rw [inner_sub_left, hps, hqs, sub_self]
  have htorth : inner ℝ (p - q) (normalVector (t : Real.Angle)) = 0 := by
    have hpt : inner ℝ p (normalVector (t : Real.Angle)) = d := hp.2
    have hqt : inner ℝ q (normalVector (t : Real.Angle)) = d := hq.2
    rw [inner_sub_left, hpt, hqt, sub_self]
  exact hst (real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi hv hs ht hsorth htorth)

private theorem hausdorffMeasure_normalLine_inter_normalLine_eq_zero {s t c d : ℝ}
    (hs : s ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi) (hst : s ≠ t) :
    Measure.hausdorffMeasure 1
      (normalLine (s : Real.Angle) c ∩ normalLine (t : Real.Angle) d) = 0 := by
  have := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  exact (normalLine_inter_normalLine_subsingleton hs ht hst).countable.measure_zero _

private theorem openRay_inter_hyperplane_subsingleton {p v n : Point} {c : ℝ}
    (hvn : inner ℝ v n ≠ 0) :
    (openRay p v ∩ {q | inner ℝ q n = c}).Subsingleton := by
  rintro x ⟨⟨r, hr, rfl⟩, hxr⟩ y ⟨⟨s, hs, rfl⟩, hyr⟩
  have hrs : r * inner ℝ v n = s * inner ℝ v n := by
    simp only [Set.mem_ofPred_eq, inner_add_left, real_inner_smul_left] at hxr hyr
    linarith
  rw [mul_right_cancel₀ hvn hrs]

private theorem hausdorffMeasure_openRay_inter_hyperplane_eq_zero {p v n : Point} {c : ℝ}
    (hvn : inner ℝ v n ≠ 0) :
    Measure.hausdorffMeasure 1 (openRay p v ∩ {q | inner ℝ q n = c}) = 0 := by
  have := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  exact (openRay_inter_hyperplane_subsingleton hvn).countable.measure_zero _

private theorem hausdorffMeasure_frontier_capFan_inter_normalLine_eq_zero
    {ω t c : ℝ} (hω : ω ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi)
    (htω : t ≠ ω) (htT : t ≠ Real.pi / 2) :
    Measure.hausdorffMeasure 1
      (frontier (capFan ω) ∩ normalLine (t : Real.Angle) c) = 0 := by
  apply measure_mono_null (t :=
    (normalLine (ω : Real.Angle) 0 ∩ normalLine (t : Real.Angle) c) ∪
      (normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ∩
        normalLine (t : Real.Angle) c))
  · rintro p ⟨hp, hpt⟩
    have hp' := frontier_inter_subset
      (normalHalfPlane (ω : Real.Angle) 0 true false)
      (normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false) hp
    rcases hp' with hp' | hp'
    · exact Or.inl ⟨frontier_normalHalfPlane_upper_closed_subset_normalLine _ _ hp'.1, hpt⟩
    · exact Or.inr ⟨frontier_normalHalfPlane_upper_closed_subset_normalLine _ _ hp'.2, hpt⟩
  · rw [measure_union_null]
    · exact hausdorffMeasure_normalLine_inter_normalLine_eq_zero hω ht htω.symm
    · exact hausdorffMeasure_normalLine_inter_normalLine_eq_zero
        ⟨by positivity, by linarith [Real.pi_pos]⟩ ht htT.symm

private theorem frontier_capFan_inter_normalLine_countable
    {ω t c : ℝ} (hω : ω ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi)
    (htω : t ≠ ω) (htT : t ≠ Real.pi / 2) :
    (frontier (capFan ω) ∩ normalLine (t : Real.Angle) c).Countable := by
  refine ((normalLine_inter_normalLine_subsingleton hω ht htω.symm
      (c := 0) (d := c)).countable.union
    (normalLine_inter_normalLine_subsingleton
      (s := Real.pi / 2) (t := t) (c := 0) (d := c)
      ⟨by positivity, by linarith [Real.pi_pos]⟩ ht htT.symm).countable).mono ?_
  rintro p ⟨hp, hpt⟩
  have hp' := frontier_inter_subset
    (normalHalfPlane (ω : Real.Angle) 0 true false)
    (normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false) hp
  rcases hp' with hp' | hp'
  · exact Or.inl ⟨frontier_normalHalfPlane_upper_closed_subset_normalLine _ _ hp'.1, hpt⟩
  · exact Or.inr ⟨frontier_normalHalfPlane_upper_closed_subset_normalLine _ _ hp'.2, hpt⟩

private theorem hausdorffMeasure_frontier_polygonNiche_inter_normalLine_eq_complement
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {t c : ℝ}
    (ht : t ∈ Set.Ioo 0 Real.pi) (htω : t ≠ Θ.angle)
    (htT : t ≠ Real.pi / 2) :
    Measure.hausdorffMeasure 1
        (frontier (polygonNiche Θ K.val) ∩ normalLine (t : Real.Angle) c) =
      Measure.hausdorffMeasure 1
        (frontier (capFan Θ.angle \ polygonNiche Θ K.val) ∩
          normalLine (t : Real.Angle) c) := by
  let X : Set Point := ⋃ s ∈ Θ.directions, innerQuadrant K.val.val s
  have hN : polygonNiche Θ K.val = capFan Θ.angle ∩ X := by simp [polygonNiche, X]
  have hC : capFan Θ.angle \ polygonNiche Θ K.val = capFan Θ.angle \ X := by
    simp [polygonNiche, X]
  rw [hC, hN]
  apply measure_eq_of_symmDiff_subset_null (E :=
    frontier (capFan Θ.angle) ∩ normalLine (t : Real.Angle) c)
  · intro p hp
    rcases hp with hp | hp
    · refine ⟨frontier_inter_open_symmDiff_subset_frontier
          (isClosed_capFan Θ.angle) (Or.inl ⟨hp.1.1, ?_⟩), hp.1.2⟩
      intro hpC
      exact hp.2 ⟨hpC, hp.1.2⟩
    · refine ⟨frontier_inter_open_symmDiff_subset_frontier
          (isClosed_capFan Θ.angle) (Or.inr ⟨hp.1.1, ?_⟩), hp.1.2⟩
      intro hpN
      exact hp.2 ⟨hpN, hp.1.2⟩
  · exact hausdorffMeasure_frontier_capFan_inter_normalLine_eq_zero
      ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩ ht htω htT

private theorem hausdorffMeasure_frontier_polygonComplement_inter_normalLine_eq_carrier
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {t c : ℝ}
    (hleft : inner ℝ (tangentVector (Θ.angle : Real.Angle))
      (normalVector (t : Real.Angle)) ≠ 0)
    (hright : inner ℝ (normalVector 0) (normalVector (t : Real.Angle)) ≠ 0) :
    Measure.hausdorffMeasure 1
        (frontier (capFan Θ.angle \ polygonNiche Θ K.val) ∩
          normalLine (t : Real.Angle) c) =
      Measure.hausdorffMeasure 1
        ((polygonCapPolyline K).carrier ∩ normalLine (t : Real.Angle) c) := by
  let p := polygonCapPolyline K
  have hp : IsCapPolyline K p := (polygonCap_polyline K).choose_spec
  let L := openRay ((capVertices K.val Θ.angle).2.1)
    (tangentVector (Θ.angle : Real.Angle))
  let R := openRay ((capVertices K.val 0).1.2) (normalVector 0)
  have hnullL : Measure.hausdorffMeasure 1
      (L ∩ normalLine (t : Real.Angle) c) = 0 := by
    exact hausdorffMeasure_openRay_inter_hyperplane_eq_zero hleft
  have hnullR : Measure.hausdorffMeasure 1
      (R ∩ normalLine (t : Real.Angle) c) = 0 := by
    exact hausdorffMeasure_openRay_inter_hyperplane_eq_zero hright
  apply measure_eq_of_symmDiff_subset_null
    (E := (L ∩ normalLine (t : Real.Angle) c) ∪
      (R ∩ normalLine (t : Real.Angle) c))
  · intro q hq
    rcases hq with hq | hq
    · rw [hp.2.2.2.2.2.1] at hq
      rcases hq.1.1 with hL | hR
      · rcases hL with hL | hcarrier
        · exact Or.inl ⟨hL, hq.1.2⟩
        · exact False.elim (hq.2 ⟨hcarrier, hq.1.2⟩)
      · exact Or.inr ⟨hR, hq.1.2⟩
    · exact False.elim (hq.2 ⟨by
        rw [hp.2.2.2.2.2.1]
        exact Or.inl (Or.inr hq.1.1), hq.1.2⟩)
  · rw [measure_union_null hnullL hnullR]

private theorem edge_direction_ne_zero (p : XMonotonePolylineData)
    (i : Fin p.edges) : p.vertices i.succ - p.vertices i.castSucc ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have hcoord := congrArg (fun q : Point ↦ q 0) h
  exact (ne_of_gt (p.increasing i.castSucc_lt_succ)) hcoord

private theorem IsCapPolyline.edge_subset_boundaryLine {Θ : AngleSet}
    {K : PolygonCapSpace Θ} {p : XMonotonePolylineData}
    (hp : IsCapPolyline K p) (i : Fin p.edges) :
    ∃ l ∈ polygonCapBoundaryLines K,
      segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ⊆
        normalLine l.1 l.2 := by
  classical
  simpa only [normalLine] using EuclideanGeometry.exists_segment_subset_hyperplane_of_finite_cover
    (I := polygonCapBoundaryLines K) (n := fun l ↦ normalVector l.1) (c := Prod.snd)
    (a := p.vertices i.castSucc) (b := p.vertices i.succ)
    (sub_ne_zero.mp (edge_direction_ne_zero p i)).symm (by
      intro q hq
      have hcarrier : q ∈ p.carrier := by
        rw [XMonotonePolylineData.carrier]
        exact Set.mem_iUnion.mpr ⟨i, hq⟩
      have hfrontier : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
        rw [hp.2.2.2.2.2.1]
        exact Or.inl (Or.inr hcarrier)
      exact frontier_polygonComplement_subset_boundaryLines K hfrontier)

private theorem IsCapPolyline.edge_subset_bLine_of_orthogonal {Θ : AngleSet}
    {K : PolygonCapSpace Θ} {p : XMonotonePolylineData}
    (hp : IsCapPolyline K p) {t : ℝ} (ht : t ∈ Θ.directions)
    (i : Fin p.edges)
    (hi : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector (t : Real.Angle)) = 0) :
    segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ⊆
      normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1) := by
  classical
  obtain ⟨l, hl, hline⟩ := hp.edge_subset_boundaryLine i
  have hleft := hline (left_mem_segment ℝ _ _)
  have hright := hline (right_mem_segment ℝ _ _)
  have hlorth : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector l.1) = 0 := by
    change inner ℝ (p.vertices i.castSucc) (normalVector l.1) = l.2 at hleft
    change inner ℝ (p.vertices i.succ) (normalVector l.1) = l.2 at hright
    rw [inner_sub_left, hright, hleft, sub_self]
  have htI : t ∈ Set.Ioo 0 Real.pi :=
    ⟨(Θ.interior t ht).1,
      ((Θ.interior t ht).2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos])⟩
  simp only [polygonCapBoundaryLines, Finset.mem_union] at hl
  rcases hl with hl | hl
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i)
        ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩ htI hlorth hi
      linarith [(Θ.interior t ht).2]
    · have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i)
        ⟨by positivity, by linarith [Real.pi_pos]⟩ htI hlorth hi
      linarith [(Θ.interior t ht).2, Θ.angle_le]
  · obtain ⟨s, hs, hsl⟩ := Finset.mem_biUnion.mp hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsl
    rcases hsl with rfl | rfl
    · have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i)
        ⟨(Θ.interior s hs).1,
          ((Θ.interior s hs).2.trans_le Θ.angle_le).trans
            (by linarith [Real.pi_pos])⟩ htI hlorth hi
      simpa [heq] using hline
    · have hsI : s + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
        constructor
        · linarith [(Θ.interior s hs).1, Real.pi_pos]
        · linarith [(Θ.interior s hs).2, Θ.angle_le]
      have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i) hsI htI hlorth hi
      linarith [(Θ.interior t ht).2, Θ.angle_le, (Θ.interior s hs).1, Real.pi_pos]

private theorem IsCapPolyline.edge_subset_dLine_of_orthogonal {Θ : AngleSet}
    {K : PolygonCapSpace Θ} {p : XMonotonePolylineData}
    (hp : IsCapPolyline K p) {t : ℝ} (ht : t ∈ Θ.directions)
    (i : Fin p.edges)
    (hi : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) = 0) :
    segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ⊆
      normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
        (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) := by
  classical
  obtain ⟨l, hl, hline⟩ := hp.edge_subset_boundaryLine i
  have hleft := hline (left_mem_segment ℝ _ _)
  have hright := hline (right_mem_segment ℝ _ _)
  have hlorth : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector l.1) = 0 := by
    change inner ℝ (p.vertices i.castSucc) (normalVector l.1) = l.2 at hleft
    change inner ℝ (p.vertices i.succ) (normalVector l.1) = l.2 at hright
    rw [inner_sub_left, hright, hleft, sub_self]
  have htI : t + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [(Θ.interior t ht).1, Real.pi_pos]
    · linarith [(Θ.interior t ht).2, Θ.angle_le]
  simp only [polygonCapBoundaryLines, Finset.mem_union] at hl
  rcases hl with hl | hl
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i)
        ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩ htI hlorth hi
      linarith [(Θ.interior t ht).1, Θ.angle_le, Real.pi_pos]
    · have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i)
        ⟨by positivity, by linarith [Real.pi_pos]⟩ htI hlorth hi
      linarith [(Θ.interior t ht).1]
  · obtain ⟨s, hs, hsl⟩ := Finset.mem_biUnion.mp hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsl
    rcases hsl with rfl | rfl
    · have hsI : s ∈ Set.Ioo 0 Real.pi :=
        ⟨(Θ.interior s hs).1,
          ((Θ.interior s hs).2.trans_le Θ.angle_le).trans
            (by linarith [Real.pi_pos])⟩
      have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i) hsI htI hlorth hi
      linarith [(Θ.interior s hs).2, (Θ.interior t ht).1, Θ.angle_le]
    · have hsI : s + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
        constructor
        · linarith [(Θ.interior s hs).1, Real.pi_pos]
        · linarith [(Θ.interior s hs).2, Θ.angle_le]
      have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i) hsI htI hlorth hi
      have hst : s = t := by linarith
      simpa [hst] using hline

private theorem polygonCapPolyline_spec {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    IsCapPolyline K (polygonCapPolyline K) := by
  exact (polygonCap_polyline K).choose_spec

private theorem polygonCapPolyline_bLine_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    (Measure.hausdorffMeasure 1
      ((polygonCapPolyline K).carrier ∩
        normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1))).toReal =
      polygonPolylineLengthAt K t := by
  let p := polygonCapPolyline K
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hmeasure := p.toReal_hausdorffMeasure_carrier_inter_hyperplane
    (normalVector (t : Real.Angle)) (supportValue K.val.val (t : Real.Angle) - 1)
    (fun i hi ↦ hp.edge_subset_bLine_of_orthogonal ht i hi)
  have htDomain : t ∈ angleDomain Θ := by
    exact Or.inl (Or.inl ht)
  rw [show normalLine (t : Real.Angle)
      (supportValue K.val.val (t : Real.Angle) - 1) =
        {q | inner ℝ q (normalVector (t : Real.Angle)) =
          supportValue K.val.val (t : Real.Angle) - 1} by rfl,
    hmeasure]
  simp [polygonPolylineLengthAt, htDomain, polygonCapPolylineLength, p]

private theorem polygonCapPolyline_dLine_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    (Measure.hausdorffMeasure 1
      ((polygonCapPolyline K).carrier ∩
        normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
          (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1))).toReal =
      polygonPolylineLengthAt K (t + Real.pi / 2) := by
  let p := polygonCapPolyline K
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hmeasure := p.toReal_hausdorffMeasure_carrier_inter_hyperplane
    (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle))
    (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)
    (fun i hi ↦ hp.edge_subset_dLine_of_orthogonal ht i hi)
  have htDomain : t + Real.pi / 2 ∈ angleDomain Θ := by
    exact Or.inl (Or.inr ⟨t, ht, rfl⟩)
  rw [show normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) =
        {q | inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
          supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1} by rfl,
    hmeasure]
  simp [polygonPolylineLengthAt, htDomain, polygonCapPolylineLength, p]

private theorem tangentVector_angle_inner_normalVector_direction_ne_zero
    {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.directions) :
    inner ℝ (tangentVector (Θ.angle : Real.Angle))
      (normalVector (t : Real.Angle)) ≠ 0 := by
  have hsin : 0 < Real.sin (Θ.angle - t) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [(Θ.interior t ht).2])
    (by linarith [(Θ.interior t ht).1, Θ.angle_le, Real.pi_pos])
  have h := sin_sub_eq_neg_inner_normalVector_tangentVector
    (t : Real.Angle) (Θ.angle : Real.Angle)
  change Real.sin (Θ.angle - t) =
    -inner ℝ (normalVector (t : Real.Angle))
      (tangentVector (Θ.angle : Real.Angle)) at h
  rw [real_inner_comm]
  linarith

private theorem tangentVector_angle_inner_normalVector_direction_add_ne_zero
    {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.directions) :
    inner ℝ (tangentVector (Θ.angle : Real.Angle))
      (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≠ 0 := by
  have hneg : -Real.pi < Θ.angle - (t + Real.pi / 2) := by
    linarith [(Θ.interior t ht).2, Real.pi_pos]
  have hzero : Θ.angle - (t + Real.pi / 2) < 0 := by
    linarith [(Θ.interior t ht).1, Θ.angle_le]
  have hsin : Real.sin (Θ.angle - (t + Real.pi / 2)) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt hzero hneg
  have h := sin_sub_eq_neg_inner_normalVector_tangentVector
    ((t + Real.pi / 2 : ℝ) : Real.Angle) (Θ.angle : Real.Angle)
  change Real.sin (Θ.angle - (t + Real.pi / 2)) =
    -inner ℝ (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle))
      (tangentVector (Θ.angle : Real.Angle)) at h
  rw [real_inner_comm]
  linarith

private theorem normalVector_zero_inner_normalVector_direction_ne_zero
    {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.directions) :
    inner ℝ (normalVector 0) (normalVector (t : Real.Angle)) ≠ 0 := by
  rw [show (0 : Real.Angle) = ((0 : ℝ) : Real.Angle) by rfl,
    inner_normalVector_normalVector]
  have hcos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, (Θ.interior t ht).1],
      (Θ.interior t ht).2.trans_le Θ.angle_le⟩
  simpa [Real.cos_neg] using hcos.ne'

private theorem normalVector_zero_inner_normalVector_direction_add_ne_zero
    {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.directions) :
    inner ℝ (normalVector 0)
      (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≠ 0 := by
  rw [show (0 : Real.Angle) = ((0 : ℝ) : Real.Angle) by rfl,
    inner_normalVector_normalVector]
  have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi
    (Θ.interior t ht).1
    (by linarith [(Θ.interior t ht).2, Θ.angle_le, Real.pi_pos])
  rw [show 0 - (t + Real.pi / 2) = -(t + Real.pi / 2) by ring,
    Real.cos_neg, Real.cos_add_pi_div_two]
  exact neg_ne_zero.mpr hsin.ne'

private theorem polygonNiche_bLine_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    (Measure.hausdorffMeasure 1
      (frontier (polygonNiche Θ K.val) ∩
        normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1))).toReal =
      polygonPolylineLengthAt K t := by
  have htI : t ∈ Set.Ioo 0 Real.pi :=
    ⟨(Θ.interior t ht).1,
      ((Θ.interior t ht).2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos])⟩
  rw [hausdorffMeasure_frontier_polygonNiche_inter_normalLine_eq_complement K htI
      (ne_of_lt (Θ.interior t ht).2) (ne_of_lt
        ((Θ.interior t ht).2.trans_le Θ.angle_le)),
    hausdorffMeasure_frontier_polygonComplement_inter_normalLine_eq_carrier K
      (tangentVector_angle_inner_normalVector_direction_ne_zero ht)
      (normalVector_zero_inner_normalVector_direction_ne_zero ht)]
  exact polygonCapPolyline_bLine_length K ht

private theorem polygonNiche_dLine_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    (Measure.hausdorffMeasure 1
      (frontier (polygonNiche Θ K.val) ∩
        normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
          (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1))).toReal =
      polygonPolylineLengthAt K (t + Real.pi / 2) := by
  have htI : t + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [(Θ.interior t ht).1, Real.pi_pos]
    · linarith [(Θ.interior t ht).2, Θ.angle_le]
  rw [hausdorffMeasure_frontier_polygonNiche_inter_normalLine_eq_complement K htI
      (by linarith [(Θ.interior t ht).1, Θ.angle_le, Real.pi_pos])
      (by linarith [(Θ.interior t ht).1]),
    hausdorffMeasure_frontier_polygonComplement_inter_normalLine_eq_carrier K
      (tangentVector_angle_inner_normalVector_direction_add_ne_zero ht)
      (normalVector_zero_inner_normalVector_direction_add_ne_zero ht)]
  exact polygonCapPolyline_dLine_length K ht

private theorem frontier_innerQuadrant_inter_bLine_subset_bRay
    (s : Set Point) (t : ℝ) :
    frontier (innerQuadrant s t) ∩
        normalLine (t : Real.Angle) (supportValue s (t : Real.Angle) - 1) ⊆
      (rotatingHallwayParts s (t : Real.Angle)).bRay := by
  intro p hp
  rw [mem_rotatingHallwayParts_bRay_iff]
  refine ⟨hp.2, ?_⟩
  apply closure_minimal (t := {q | inner ℝ q (tangentVector (t : Real.Angle)) ≤
      supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1})
      (fun q hq ↦ ?_) (isClosed_le (by fun_prop) continuous_const)
      (frontier_subset_closure hp.1)
  change q ∈ innerQuadrant s t at hq
  have h := hq.2
  change inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
    supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 at h
  rw [show ((t + Real.pi / 2 : ℝ) : Real.Angle) =
    (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
    normalVector_add_pi_div_two] at h
  exact h.le

private theorem frontier_innerQuadrant_inter_dLine_subset_dRay
    (s : Set Point) (t : ℝ) :
    frontier (innerQuadrant s t) ∩
        normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
          (supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) ⊆
      (rotatingHallwayParts s (t : Real.Angle)).dRay := by
  intro p hp
  rw [mem_rotatingHallwayParts_dRay_iff]
  refine ⟨?_, ?_⟩
  · apply closure_minimal (t := {q | inner ℝ q (normalVector (t : Real.Angle)) ≤
        supportValue s (t : Real.Angle) - 1})
        (fun q hq ↦ ?_) (isClosed_le (by fun_prop) continuous_const)
        (frontier_subset_closure hp.1)
    change q ∈ innerQuadrant s t at hq
    have h := hq.1
    change inner ℝ q (normalVector (t : Real.Angle)) <
      supportValue s (t : Real.Angle) - 1 at h
    exact h.le
  · have hline := hp.2
    change inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 at hline
    rw [show ((t + Real.pi / 2 : ℝ) : Real.Angle) =
      (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
      normalVector_add_pi_div_two] at hline
    exact hline

private theorem frontier_innerQuadrant_inter_bLine_countable_of_ne
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {s t : ℝ}
    (hs : s ∈ Θ.directions) (ht : t ∈ Θ.directions) (hst : s ≠ t) :
    (frontier (innerQuadrant K.val.val s) ∩
      normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1)).Countable := by
  have hsI : s ∈ Set.Ioo 0 Real.pi :=
    ⟨(Θ.interior s hs).1,
      ((Θ.interior s hs).2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos])⟩
  have htI : t ∈ Set.Ioo 0 Real.pi :=
    ⟨(Θ.interior t ht).1,
      ((Θ.interior t ht).2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos])⟩
  have hsTI : s + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [(Θ.interior s hs).1, Real.pi_pos]
    · linarith [(Θ.interior s hs).2, Θ.angle_le]
  have hfirst := normalLine_inter_normalLine_subsingleton hsI htI hst
    (c := supportValue K.val.val (s : Real.Angle) - 1)
    (d := supportValue K.val.val (t : Real.Angle) - 1)
  have hsecond := normalLine_inter_normalLine_subsingleton hsTI htI
    (by linarith [(Θ.interior s hs).1, (Θ.interior t ht).2, Θ.angle_le])
    (c := supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1)
    (d := supportValue K.val.val (t : Real.Angle) - 1)
  refine (hfirst.countable.union hsecond.countable).mono ?_
  rintro p ⟨hp, hpt⟩
  have hp' := frontier_inter_subset
    (normalHalfPlane (s : Real.Angle) (supportValue K.val.val (s : Real.Angle) - 1)
      false true)
    (normalHalfPlane ((s + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1) false true) hp
  rcases hp' with hp' | hp'
  · exact Or.inl
      ⟨frontier_normalHalfPlane_lower_strict_subset_normalLine _ _ hp'.1, hpt⟩
  · exact Or.inr
      ⟨frontier_normalHalfPlane_lower_strict_subset_normalLine _ _ hp'.2, hpt⟩

private theorem frontier_innerQuadrant_inter_dLine_countable_of_ne
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {s t : ℝ}
    (hs : s ∈ Θ.directions) (ht : t ∈ Θ.directions) (hst : s ≠ t) :
    (frontier (innerQuadrant K.val.val s) ∩
      normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
        (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)).Countable := by
  have hsI : s ∈ Set.Ioo 0 Real.pi :=
    ⟨(Θ.interior s hs).1,
      ((Θ.interior s hs).2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos])⟩
  have hsTI : s + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [(Θ.interior s hs).1, Real.pi_pos]
    · linarith [(Θ.interior s hs).2, Θ.angle_le]
  have htTI : t + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [(Θ.interior t ht).1, Real.pi_pos]
    · linarith [(Θ.interior t ht).2, Θ.angle_le]
  have hfirst := normalLine_inter_normalLine_subsingleton hsI htTI
    (by linarith [(Θ.interior s hs).2, (Θ.interior t ht).1, Θ.angle_le])
    (c := supportValue K.val.val (s : Real.Angle) - 1)
    (d := supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)
  have hsecond := normalLine_inter_normalLine_subsingleton hsTI htTI
    (by
      intro h
      apply hst
      linarith)
    (c := supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1)
    (d := supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)
  refine (hfirst.countable.union hsecond.countable).mono ?_
  rintro p ⟨hp, hpt⟩
  have hp' := frontier_inter_subset
    (normalHalfPlane (s : Real.Angle) (supportValue K.val.val (s : Real.Angle) - 1)
      false true)
    (normalHalfPlane ((s + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1) false true) hp
  rcases hp' with hp' | hp'
  · exact Or.inl
      ⟨frontier_normalHalfPlane_lower_strict_subset_normalLine _ _ hp'.1, hpt⟩
  · exact Or.inr
      ⟨frontier_normalHalfPlane_lower_strict_subset_normalLine _ _ hp'.2, hpt⟩

private theorem frontier_polygonNiche_bLine_sdiff_bRay_countable
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    ((frontier (polygonNiche Θ K.val) ∩
        normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1)) \
      (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay).Countable := by
  let L := normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1)
  let R := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay
  let X : Set Point := ⋃ s ∈ Θ.directions, innerQuadrant K.val.val s
  let E : Θ.directions → Set Point := fun s ↦
    (frontier (innerQuadrant K.val.val s) ∩ L) \ R
  have htI : t ∈ Set.Ioo 0 Real.pi :=
    ⟨(Θ.interior t ht).1,
      ((Θ.interior t ht).2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos])⟩
  have hfan : (frontier (capFan Θ.angle) ∩ L).Countable :=
    frontier_capFan_inter_normalLine_countable
      ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩ htI
      (ne_of_lt (Θ.interior t ht).2)
      (ne_of_lt ((Θ.interior t ht).2.trans_le Θ.angle_le))
  have hE (s : Θ.directions) : (E s).Countable := by
    by_cases hst : (s : ℝ) = t
    · apply Set.countable_empty.mono
      intro p hp
      exfalso
      apply hp.2
      apply frontier_innerQuadrant_inter_bLine_subset_bRay
        (s := (K.val.val : Set Point)) (t := t)
      simpa [E, L, R, hst] using hp.1
    · exact (frontier_innerQuadrant_inter_bLine_countable_of_ne K s.property ht hst).mono
        (by intro p hp; exact hp.1)
  refine (hfan.union (Set.countable_iUnion hE)).mono ?_
  intro p hp
  have hp' : p ∈ frontier (capFan Θ.angle ∩ X) := by
    simpa [polygonNiche, X] using hp.1.1
  rcases frontier_inter_subset (capFan Θ.angle) X hp' with hpF | hpX
  · exact Or.inl ⟨hpF.1, hp.1.2⟩
  · right
    have hmem := Finset.frontier_biUnion_subset Θ.directions
      (fun s ↦ innerQuadrant K.val.val s) hpX.2
    obtain ⟨s, hs, hps⟩ := Set.mem_iUnion₂.mp hmem
    exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ⟨⟨hps, hp.1.2⟩, hp.2⟩⟩

private theorem frontier_polygonNiche_dLine_sdiff_dRay_countable
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    ((frontier (polygonNiche Θ K.val) ∩
        normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
          (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)) \
      (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).dRay).Countable := by
  let L := normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
    (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)
  let R := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).dRay
  let X : Set Point := ⋃ s ∈ Θ.directions, innerQuadrant K.val.val s
  let E : Θ.directions → Set Point := fun s ↦
    (frontier (innerQuadrant K.val.val s) ∩ L) \ R
  have htI : t + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [(Θ.interior t ht).1, Real.pi_pos]
    · linarith [(Θ.interior t ht).2, Θ.angle_le]
  have hfan : (frontier (capFan Θ.angle) ∩ L).Countable :=
    frontier_capFan_inter_normalLine_countable
      ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩ htI
      (by linarith [(Θ.interior t ht).1, Θ.angle_le, Real.pi_pos])
      (by linarith [(Θ.interior t ht).1])
  have hE (s : Θ.directions) : (E s).Countable := by
    by_cases hst : (s : ℝ) = t
    · apply Set.countable_empty.mono
      intro p hp
      exfalso
      apply hp.2
      apply frontier_innerQuadrant_inter_dLine_subset_dRay
        (s := (K.val.val : Set Point)) (t := t)
      simpa [E, L, R, hst] using hp.1
    · exact (frontier_innerQuadrant_inter_dLine_countable_of_ne K s.property ht hst).mono
        (by intro p hp; exact hp.1)
  refine (hfan.union (Set.countable_iUnion hE)).mono ?_
  intro p hp
  have hp' : p ∈ frontier (capFan Θ.angle ∩ X) := by
    simpa [polygonNiche, X] using hp.1.1
  rcases frontier_inter_subset (capFan Θ.angle) X hp' with hpF | hpX
  · exact Or.inl ⟨hpF.1, hp.1.2⟩
  · right
    have hmem := Finset.frontier_biUnion_subset Θ.directions
      (fun s ↦ innerQuadrant K.val.val s) hpX.2
    obtain ⟨s, hs, hps⟩ := Set.mem_iUnion₂.mp hmem
    exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ⟨⟨hps, hp.1.2⟩, hp.2⟩⟩

private theorem rotatingHallwayParts_bRay_subset_bLine
    (s : Set Point) (t : ℝ) :
    (rotatingHallwayParts s (t : Real.Angle)).bRay ⊆
      normalLine (t : Real.Angle) (supportValue s (t : Real.Angle) - 1) := by
  intro p hp
  exact (mem_rotatingHallwayParts_bRay_iff s (t : Real.Angle) p).mp hp |>.1

private theorem rotatingHallwayParts_dRay_subset_dLine
    (s : Set Point) (t : ℝ) :
    (rotatingHallwayParts s (t : Real.Angle)).dRay ⊆
      normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
        (supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) := by
  intro p hp
  have h := (mem_rotatingHallwayParts_dRay_iff s (t : Real.Angle) p).mp hp |>.2
  change inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
    supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1
  rw [show ((t + Real.pi / 2 : ℝ) : Real.Angle) =
    (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
    normalVector_add_pi_div_two]
  exact h

private theorem polygonNiche_bRay_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    (Measure.hausdorffMeasure 1
      (frontier (polygonNiche Θ K.val) ∩
        (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay)).toReal =
      polygonPolylineLengthAt K t := by
  let L := normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1)
  let R := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay
  have hRL : R ⊆ L := rotatingHallwayParts_bRay_subset_bLine K.val.val t
  have hmeasure : Measure.hausdorffMeasure 1
      (frontier (polygonNiche Θ K.val) ∩ L) =
      Measure.hausdorffMeasure 1 (frontier (polygonNiche Θ K.val) ∩ R) := by
    apply measure_eq_of_symmDiff_subset_null (E :=
      (frontier (polygonNiche Θ K.val) ∩ L) \ R)
    · intro p hp
      rcases hp with hp | hp
      · exact ⟨hp.1, fun hpR ↦ hp.2 ⟨hp.1.1, hpR⟩⟩
      · exfalso
        exact hp.2 ⟨hp.1.1, hRL hp.1.2⟩
    · have := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
      exact (frontier_polygonNiche_bLine_sdiff_bRay_countable K ht).measure_zero _
  rw [← hmeasure]
  exact polygonNiche_bLine_length K ht

private theorem polygonNiche_dRay_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    (Measure.hausdorffMeasure 1
      (frontier (polygonNiche Θ K.val) ∩
        (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).dRay)).toReal =
      polygonPolylineLengthAt K (t + Real.pi / 2) := by
  let L := normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
    (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)
  let R := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).dRay
  have hRL : R ⊆ L := rotatingHallwayParts_dRay_subset_dLine K.val.val t
  have hmeasure : Measure.hausdorffMeasure 1
      (frontier (polygonNiche Θ K.val) ∩ L) =
      Measure.hausdorffMeasure 1 (frontier (polygonNiche Θ K.val) ∩ R) := by
    apply measure_eq_of_symmDiff_subset_null (E :=
      (frontier (polygonNiche Θ K.val) ∩ L) \ R)
    · intro p hp
      rcases hp with hp | hp
      · exact ⟨hp.1, fun hpR ↦ hp.2 ⟨hp.1.1, hpR⟩⟩
      · exfalso
        exact hp.2 ⟨hp.1.1, hRL hp.1.2⟩
    · have := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
      exact (frontier_polygonNiche_dLine_sdiff_dRay_countable K ht).measure_zero _
  rw [← hmeasure]
  exact polygonNiche_dLine_length K ht

private theorem exposedEdge_bottom_eq_segment_zero_right {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
      segment ℝ 0 (capVertices K.val 0).1.2 := by
  let A := (capVertices K.val 0).1.2
  have hAeq := capVertices_zero_snd_eq K
  change A = supportValue K.val.val (0 : Real.Angle) •
    normalVector (0 : Real.Angle) at hAeq
  have htangent : tangentVector ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
      normalVector (0 : Real.Angle) := by
    ext i
    fin_cases i <;>
      simp [tangentVector, normalVector, frame,
        show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring,
        Real.sin_add, Real.cos_add, -Real.Angle.coe_add]
  have hAK : A ∈ (K.val.val : Set Point) := by
    rw [hAeq]
    exact supportValue_zero_smul_normalVector_mem K.val
  have hAedge : A ∈ exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    refine ⟨hAK, ?_⟩
    change inner ℝ A (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.2.1, hAeq, inner_normalVector_three_pi_div_two]
    simp [normalVector, frame]
  have h0edge : (0 : Point) ∈
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    refine ⟨zero_mem_cap_of_lt K.val hω, ?_⟩
    change inner ℝ (0 : Point) (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.2.1]
    simp
  have hfst : (edgeVertices K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 = A := by
    apply edgeVertices_fst_eq_of_tangent_isGreatest K.val.val _ hAedge
    intro q hq
    have hqx := inner_le_supportValue K.val.val hq.1 (0 : Real.Angle)
    have hA := (edgeVertices_snd_mem K.val.val (0 : Real.Angle)).2
    change inner ℝ A (normalVector (0 : Real.Angle)) =
      supportValue K.val.val (0 : Real.Angle) at hA
    rw [htangent]
    exact hqx.trans_eq hA.symm
  have hsnd : (edgeVertices K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2 = 0 := by
    apply edgeVertices_snd_eq_of_tangent_isLeast K.val.val _ h0edge
    intro q hq
    have hfan := K.val.subset_capFan hq.1
    have hqy : q 1 = 0 := by
      have h := hq.2
      change inner ℝ q (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) at h
      rw [K.val.property.2.2.2.2.2.1] at h
      simpa only [inner_normalVector_three_pi_div_two, neg_eq_zero] using h
    have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
    have hqx : 0 ≤ q 0 := by
      have h := hfan.1
      change 0 ≤ inner ℝ q (normalVector (Θ.angle : Real.Angle)) at h
      simp [normalVector, frame, PiLp.inner_apply, hqy] at h
      exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using h) hcos
    rw [htangent]
    simpa [normalVector, frame, PiLp.inner_apply] using hqx
  rw [exposedEdge_eq_segment_edgeVertices, hfst, hsnd]

private theorem exposedEdge_left_eq_segment_zero_left {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    exposedEdge K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle) =
      segment ℝ 0 (capVertices K.val Θ.angle).2.1 := by
  let C := (capVertices K.val Θ.angle).2.1
  let L := supportValue K.val.val ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)
  have hCeq := capVertices_angle_fst_eq K
  change C = L • tangentVector (Θ.angle : Real.Angle) at hCeq
  have hnormal : normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle) =
      -normalVector (Θ.angle : Real.Angle) := normalVector_add_pi Θ.angle
  have htangent : tangentVector ((Θ.angle + Real.pi : ℝ) : Real.Angle) =
      -tangentVector (Θ.angle : Real.Angle) := by
    ext i
    fin_cases i <;>
      simp [tangentVector, frame, Real.sin_add, Real.cos_add, -Real.Angle.coe_add]
  have hCK : C ∈ (K.val.val : Set Point) := by
    rw [hCeq]
    exact supportValue_add_pi_div_two_smul_tangentVector_mem_of_lt K.val hω
  have hCedge : C ∈ exposedEdge K.val.val
      ((Θ.angle + Real.pi : ℝ) : Real.Angle) := by
    refine ⟨hCK, ?_⟩
    change inner ℝ C (normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle)) =
      supportValue K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.1, hnormal, hCeq, inner_neg_right,
      real_inner_smul_left, real_inner_comm, inner_normalVector_tangentVector]
    simp
  have h0edge : (0 : Point) ∈
      exposedEdge K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle) := by
    refine ⟨zero_mem_cap_of_lt K.val hω, ?_⟩
    change inner ℝ (0 : Point) (normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle)) =
      supportValue K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.1]
    simp
  have hfst : (edgeVertices K.val.val
      ((Θ.angle + Real.pi : ℝ) : Real.Angle)).1 = 0 := by
    apply edgeVertices_fst_eq_of_tangent_isGreatest K.val.val _ h0edge
    intro q hq
    have hfan := K.val.subset_capFan hq.1
    have hqn : inner ℝ q (normalVector (Θ.angle : Real.Angle)) = 0 := by
      have h := hq.2
      change inner ℝ q (normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle)) =
        supportValue K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle) at h
      rw [K.val.property.2.2.2.2.1, hnormal, inner_neg_right] at h
      linarith
    let μ := inner ℝ q (tangentVector (Θ.angle : Real.Angle))
    have hqeq : μ • tangentVector (Θ.angle : Real.Angle) = q := by
      have hframe := inner_normalVector_smul_add_inner_tangentVector_smul
        q (Θ.angle : Real.Angle)
      rw [hqn, zero_smul, zero_add] at hframe
      exact hframe
    have hμ : 0 ≤ μ := by
      have hqy := hfan.2
      change 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hqy
      have hcoord := congrArg (fun p : Point ↦ p 1) hqeq
      change μ * Real.cos Θ.angle = q 1 at hcoord
      have hqy' : 0 ≤ q 1 := by
        simpa [normalVector, frame, PiLp.inner_apply] using hqy
      rw [← hcoord] at hqy'
      exact nonneg_of_mul_nonneg_left hqy' (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩)
    rw [htangent, inner_neg_right]
    simpa using neg_nonpos.mpr hμ
  have hsnd : (edgeVertices K.val.val
      ((Θ.angle + Real.pi : ℝ) : Real.Angle)).2 = C := by
    apply edgeVertices_snd_eq_of_tangent_isLeast K.val.val _ hCedge
    intro q hq
    have hqL := inner_le_supportValue K.val.val hq.1
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)
    rw [show ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) =
      (Θ.angle : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
      normalVector_add_pi_div_two] at hqL
    change inner ℝ q (tangentVector (Θ.angle : Real.Angle)) ≤ L at hqL
    rw [htangent, hCeq, inner_neg_right, inner_neg_right, real_inner_smul_left,
      inner_tangentVector_self]
    linarith
  rw [exposedEdge_eq_segment_edgeVertices, hfst, hsnd, segment_symm]

private theorem exposedEdge_bottom_eq_segment_left_right {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle = Real.pi / 2) :
    exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
      segment ℝ (capVertices K.val Θ.angle).2.1 (capVertices K.val 0).1.2 := by
  let A := (capVertices K.val 0).1.2
  let C := (capVertices K.val Θ.angle).2.1
  have hAeq := capVertices_zero_snd_eq K
  change A = supportValue K.val.val (0 : Real.Angle) •
    normalVector (0 : Real.Angle) at hAeq
  have hCeq := capVertices_angle_fst_eq K
  change C = supportValue K.val.val ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) •
    tangentVector (Θ.angle : Real.Angle) at hCeq
  have htangent : tangentVector ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
      normalVector (0 : Real.Angle) := by
    ext i
    fin_cases i <;>
      simp [tangentVector, normalVector, frame,
        show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring,
        Real.sin_add, Real.cos_add, -Real.Angle.coe_add]
  have hAK : A ∈ (K.val.val : Set Point) := by
    rw [hAeq]
    exact supportValue_zero_smul_normalVector_mem K.val
  have hCK : C ∈ (K.val.val : Set Point) := by
    exact (edgeVertices_fst_mem K.val.val
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)).1
  have hAedge : A ∈ exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    refine ⟨hAK, ?_⟩
    change inner ℝ A (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.2.1, hAeq, inner_normalVector_three_pi_div_two]
    simp [normalVector, frame]
  have hCedge : C ∈ exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    refine ⟨hCK, ?_⟩
    change inner ℝ C (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.2.1, hCeq, inner_normalVector_three_pi_div_two]
    simp [hω, tangentVector, frame]
  have hfst : (edgeVertices K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 = A := by
    apply edgeVertices_fst_eq_of_tangent_isGreatest K.val.val _ hAedge
    intro q hq
    have hqx := inner_le_supportValue K.val.val hq.1 (0 : Real.Angle)
    have hA := (edgeVertices_snd_mem K.val.val (0 : Real.Angle)).2
    change inner ℝ A (normalVector (0 : Real.Angle)) =
      supportValue K.val.val (0 : Real.Angle) at hA
    rw [htangent]
    exact hqx.trans_eq hA.symm
  have hsnd : (edgeVertices K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2 = C := by
    apply edgeVertices_snd_eq_of_tangent_isLeast K.val.val _ hCedge
    intro q hq
    have hqx := inner_le_supportValue K.val.val hq.1 (Real.pi : Real.Angle)
    have hC := (edgeVertices_fst_mem K.val.val
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)).2
    change inner ℝ C
      (normalVector ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue K.val.val ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) at hC
    have hang : ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) =
        (Real.pi : Real.Angle) := by
      congr 1
      rw [hω]
      ring
    rw [hang] at hC
    rw [htangent]
    simpa [normalVector, frame, PiLp.inner_apply] using hqx.trans_eq hC.symm
  rw [exposedEdge_eq_segment_edgeVertices, hfst, hsnd]

private theorem XMonotonePolylineData.carrier_fst_mem_Icc
    (p : XMonotonePolylineData) {q : Point} (hq : q ∈ p.carrier) :
    q 0 ∈ Set.Icc ((p.vertices 0) 0) ((p.vertices (Fin.last p.edges)) 0) := by
  rw [XMonotonePolylineData.carrier] at hq
  obtain ⟨i, hqi⟩ := Set.mem_iUnion.mp hq
  have hi := fst_mem_Icc_of_mem_segment_mc4d199c (p.increasing i.castSucc_lt_succ).le hqi
  exact ⟨(p.increasing.monotone (Fin.zero_le i.castSucc)).trans hi.1,
    hi.2.trans (p.increasing.monotone (Fin.le_last i.succ))⟩

private theorem mem_segment_of_fst_mem_Icc_of_mem_normalLine
    {a b q : Point} {t c : ℝ} (hab : a 0 < b 0)
    (ht : t ∈ Set.Ioo 0 Real.pi)
    (ha : a ∈ normalLine (t : Real.Angle) c)
    (hb : b ∈ normalLine (t : Real.Angle) c)
    (hq : q ∈ normalLine (t : Real.Angle) c)
    (hx : q 0 ∈ Set.Icc (a 0) (b 0)) : q ∈ segment ℝ a b := by
  let r := (q 0 - a 0) / (b 0 - a 0)
  have hden : 0 < b 0 - a 0 := sub_pos.mpr hab
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hden.le
    · exact (div_le_one hden).2 (by linarith [hx.2])
  rw [segment_eq_image']
  refine ⟨r, hr, ?_⟩
  change a + r • (b - a) = q
  have hxcoord : (a + r • (b - a)) 0 = q 0 := by
    dsimp [r]
    field_simp
    ring
  have hline : a + r • (b - a) ∈ normalLine (t : Real.Angle) c := by
    change inner ℝ (a + r • (b - a)) (normalVector (t : Real.Angle)) = c
    change inner ℝ a (normalVector (t : Real.Angle)) = c at ha
    change inner ℝ b (normalVector (t : Real.Angle)) = c at hb
    rw [inner_add_left, real_inner_smul_left, inner_sub_left, ha, hb, sub_self,
      mul_zero, add_zero]
  ext i
  fin_cases i
  · exact hxcoord
  · change (a + r • (b - a)) 1 = q 1
    change inner ℝ (a + r • (b - a)) (normalVector (t : Real.Angle)) = c at hline
    change inner ℝ q (normalVector (t : Real.Angle)) = c at hq
    simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] at hline hq
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hxcoord ⊢
    apply mul_left_cancel₀ (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
    linear_combination hline - hq - Real.cos t * hxcoord

private theorem eq_of_fst_eq_of_mem_normalLine {p q : Point} {t c : ℝ}
    (ht : t ∈ Set.Ioo 0 Real.pi)
    (hp : p ∈ normalLine (t : Real.Angle) c)
    (hq : q ∈ normalLine (t : Real.Angle) c) (hx : p 0 = q 0) : p = q := by
  ext i
  fin_cases i
  · exact hx
  · change p 1 = q 1
    change inner ℝ p (normalVector (t : Real.Angle)) = c at hp
    change inner ℝ q (normalVector (t : Real.Angle)) = c at hq
    simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] at hp hq
    apply mul_left_cancel₀ (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
    linear_combination hp - hq - Real.cos t * hx

private theorem polygonCapPolyline_carrier_inter_bottom_subset_exposedEdge_of_lt
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    (polygonCapPolyline K).carrier ∩
        normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
  let p := polygonCapPolyline K
  let A := (capVertices K.val 0).1.2
  let C := (capVertices K.val Θ.angle).2.1
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hAeq := capVertices_zero_snd_eq K
  change A = supportValue K.val.val (0 : Real.Angle) •
    normalVector (0 : Real.Angle) at hAeq
  have hCeq := capVertices_angle_fst_eq K
  change C = supportValue K.val.val ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) •
    tangentVector (Θ.angle : Real.Angle) at hCeq
  have hL : 0 ≤ supportValue K.val.val
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) :=
    supportValue_nonneg_of_mem_capUpperAngles K.val hω
      (Or.inr ⟨by linarith [Θ.angle_pos, Real.pi_pos], le_rfl⟩)
  have hC0 : C 0 ≤ 0 := by
    rw [hCeq]
    simp [tangentVector, frame]
    simpa only [Real.Angle.coe_add] using mul_nonneg hL
      (Real.sin_nonneg_of_nonneg_of_le_pi Θ.angle_pos.le
        (Θ.angle_le.trans (by linarith [Real.pi_pos])))
  have hA0support : 0 < supportValue K.val.val (0 : Real.Angle) := by
    obtain ⟨u, huK, hu⟩ := exists_mem_inner_eq_supportValue K.val.val
      (Θ.angle : Real.Angle)
    have huy : u 1 ≤ 1 := by
      have huy' := inner_le_supportValue K.val.val huK
        ((Real.pi / 2 : ℝ) : Real.Angle)
      rw [K.val.property.2.2.2.1] at huy'
      simpa [normalVector, frame, PiLp.inner_apply] using huy'
    rw [K.val.property.2.2.1] at hu
    have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
    have hsin_lt : Real.sin Θ.angle < 1 := by
      nlinarith only [Real.sin_sq_add_cos_sq Θ.angle, sq_pos_of_pos hcos]
    have hux : 0 < u 0 := by
      simp [normalVector, frame, PiLp.inner_apply] at hu
      have hsin : 0 ≤ Real.sin Θ.angle :=
        (Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
          (Θ.angle_le.trans_lt (by linarith [Real.pi_pos]))).le
      have hmul := mul_le_mul_of_nonneg_left huy hsin
      nlinarith
    exact hux.trans_le (by
      have := inner_le_supportValue K.val.val huK (0 : Real.Angle)
      simpa [normalVector, frame, PiLp.inner_apply] using this)
  have hA0 : 0 < A 0 := by
    rw [hAeq]
    simpa [normalVector, frame] using hA0support
  intro q hq
  rw [exposedEdge_bottom_eq_segment_zero_right K hω]
  apply mem_segment_of_fst_mem_Icc_of_mem_normalLine hA0
    (t := Real.pi / 2) (c := 0)
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  · simp [normalLine, normalVector, frame, PiLp.inner_apply]
  · change inner ℝ (capVertices K.val 0).1.2
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0
    rw [capVertices_zero_snd_eq K]
    simp [normalVector, frame, PiLp.inner_apply]
  · exact hq.2
  · have hxbounds := p.carrier_fst_mem_Icc hq.1
    rw [hp.2.1, hp.2.2.1] at hxbounds
    refine ⟨?_, hxbounds.2⟩
    have hfront : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
      rw [hp.2.2.2.2.2.1]
      exact Or.inl (Or.inr hq.1)
    have hclosed : IsClosed (capFan Θ.angle \ polygonNiche Θ K.val) := hp.2.2.2.2.1
    have hfan : q ∈ capFan Θ.angle :=
      (hclosed.closure_eq ▸ frontier_subset_closure hfront).1
    have hqy : q 1 = 0 := by
      have h := hq.2
      change inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 at h
      simpa [normalVector, frame, PiLp.inner_apply] using h
    have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
    have h := hfan.1
    change 0 ≤ inner ℝ q (normalVector (Θ.angle : Real.Angle)) at h
    simp [normalVector, frame, PiLp.inner_apply, hqy] at h
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using h) hcos

private theorem polygonCapPolyline_carrier_inter_left_subset_exposedEdge_of_lt
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    (polygonCapPolyline K).carrier ∩ normalLine (Θ.angle : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle) := by
  let p := polygonCapPolyline K
  let C := (capVertices K.val Θ.angle).2.1
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hCeq := capVertices_angle_fst_eq K
  change C = supportValue K.val.val ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) •
    tangentVector (Θ.angle : Real.Angle) at hCeq
  have hL : 0 ≤ supportValue K.val.val
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) :=
    supportValue_nonneg_of_mem_capUpperAngles K.val hω
      (Or.inr ⟨by linarith [Θ.angle_pos, Real.pi_pos], le_rfl⟩)
  have hC0 : C 0 ≤ 0 := by
    rw [hCeq]
    simp [tangentVector, frame]
    simpa only [Real.Angle.coe_add] using mul_nonneg hL
      (Real.sin_nonneg_of_nonneg_of_le_pi Θ.angle_pos.le
        (Θ.angle_le.trans (by linarith [Real.pi_pos])))
  intro q hq
  rw [exposedEdge_left_eq_segment_zero_left K hω, segment_symm]
  have hfront : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
    rw [hp.2.2.2.2.2.1]
    exact Or.inl (Or.inr hq.1)
  have hclosed : IsClosed (capFan Θ.angle \ polygonNiche Θ K.val) := hp.2.2.2.2.1
  have hfan : q ∈ capFan Θ.angle :=
    (hclosed.closure_eq ▸ frontier_subset_closure hfront).1
  have hxbounds := p.carrier_fst_mem_Icc hq.1
  rw [hp.2.1, hp.2.2.1] at hxbounds
  have hq0 : q 0 ≤ 0 := by
    have hline := hq.2
    change inner ℝ q (normalVector (Θ.angle : Real.Angle)) = 0 at hline
    have hqy := hfan.2
    change 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hqy
    have hqy' : 0 ≤ q 1 := by
      simpa [normalVector, frame, PiLp.inner_apply] using hqy
    simp [normalVector, frame, PiLp.inner_apply] at hline
    have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
    have hsin : 0 < Real.sin Θ.angle := Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
      (by linarith [Θ.angle_le, Real.pi_pos])
    nlinarith
  have hCline : C ∈ normalLine (Θ.angle : Real.Angle) 0 := by
    change inner ℝ C (normalVector (Θ.angle : Real.Angle)) = 0
    rw [hCeq, real_inner_smul_left, real_inner_comm, inner_normalVector_tangentVector]
    simp
  have h0line : (0 : Point) ∈ normalLine (Θ.angle : Real.Angle) 0 := by
    simp [normalLine]
  by_cases hCstrict : C 0 < 0
  · exact mem_segment_of_fst_mem_Icc_of_mem_normalLine hCstrict
      ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩
      hCline h0line hq.2 ⟨hxbounds.1, hq0⟩
  · have hCzero : C 0 = 0 := le_antisymm hC0 (le_of_not_gt hCstrict)
    have hqzero : q 0 = C 0 := by linarith [hxbounds.1, hq0]
    have hqC := eq_of_fst_eq_of_mem_normalLine
      ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩
      hq.2 hCline hqzero
    rw [hqC]
    exact left_mem_segment ℝ C 0

private theorem polygonCapPolyline_carrier_inter_bottom_subset_exposedEdge_of_eq
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle = Real.pi / 2) :
    (polygonCapPolyline K).carrier ∩
        normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
  let p := polygonCapPolyline K
  let A := (capVertices K.val 0).1.2
  let C := (capVertices K.val Θ.angle).2.1
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hAeq := capVertices_zero_snd_eq K
  change A = supportValue K.val.val (0 : Real.Angle) •
    normalVector (0 : Real.Angle) at hAeq
  have hCeq := capVertices_angle_fst_eq K
  change C = supportValue K.val.val ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) •
    tangentVector (Θ.angle : Real.Angle) at hCeq
  intro q hq
  rw [exposedEdge_bottom_eq_segment_left_right K hω]
  apply mem_segment_of_fst_mem_Icc_of_mem_normalLine (polygonCap_left_x_lt_right_x K)
    (t := Real.pi / 2) (c := 0)
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  · change inner ℝ C (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0
    rw [hCeq]
    simp [hω, tangentVector, normalVector, frame, PiLp.inner_apply]
  · change inner ℝ A (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0
    rw [hAeq]
    simp [normalVector, frame, PiLp.inner_apply]
  · exact hq.2
  · have hxbounds := p.carrier_fst_mem_Icc hq.1
    simpa [hp.2.1, hp.2.2.1] using hxbounds

private theorem IsCapPolyline.edge_subset_fanLine_of_orthogonal
    {Θ : AngleSet} {K : PolygonCapSpace Θ} {p : XMonotonePolylineData}
    (hp : IsCapPolyline K p) {t : ℝ} (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (i : Fin p.edges)
    (hi : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector (t : Real.Angle)) = 0) :
    segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ⊆
      normalLine (t : Real.Angle) 0 := by
  classical
  obtain ⟨l, hl, hline⟩ := hp.edge_subset_boundaryLine i
  have hleft := hline (left_mem_segment ℝ _ _)
  have hright := hline (right_mem_segment ℝ _ _)
  have hlorth : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector l.1) = 0 := by
    change inner ℝ (p.vertices i.castSucc) (normalVector l.1) = l.2 at hleft
    change inner ℝ (p.vertices i.succ) (normalVector l.1) = l.2 at hright
    rw [inner_sub_left, hright, hleft, sub_self]
  have hωI : Θ.angle ∈ Set.Ioo 0 Real.pi :=
    ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩
  have hTI : Real.pi / 2 ∈ Set.Ioo 0 Real.pi :=
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  rcases Set.mem_insert_iff.mp ht with rfl | ht
  · simp only [polygonCapBoundaryLines, Finset.mem_union] at hl
    rcases hl with hl | hl
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · exact hline
      · have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
          (edge_direction_ne_zero p i) hTI hωI hlorth hi
        simpa [heq] using hline
    · obtain ⟨s, hs, hsl⟩ := Finset.mem_biUnion.mp hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsl
      rcases hsl with rfl | rfl
      · have hsI : s ∈ Set.Ioo 0 Real.pi :=
          ⟨(Θ.interior s hs).1,
            ((Θ.interior s hs).2.trans_le Θ.angle_le).trans
              (by linarith [Real.pi_pos])⟩
        have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
          (edge_direction_ne_zero p i) hsI hωI hlorth hi
        linarith [(Θ.interior s hs).2]
      · have hsI : s + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
          constructor
          · linarith [(Θ.interior s hs).1, Real.pi_pos]
          · linarith [(Θ.interior s hs).2, Θ.angle_le]
        have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
          (edge_direction_ne_zero p i) hsI hωI hlorth hi
        linarith [(Θ.interior s hs).1, Θ.angle_le, Real.pi_pos]
  · have ht : t = Real.pi / 2 := Set.mem_singleton_iff.mp ht
    subst t
    simp only [polygonCapBoundaryLines, Finset.mem_union] at hl
    rcases hl with hl | hl
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
          (edge_direction_ne_zero p i) hωI hTI hlorth hi
        simpa [heq] using hline
      · exact hline
    · obtain ⟨s, hs, hsl⟩ := Finset.mem_biUnion.mp hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsl
      rcases hsl with rfl | rfl
      · have hsI : s ∈ Set.Ioo 0 Real.pi :=
          ⟨(Θ.interior s hs).1,
            ((Θ.interior s hs).2.trans_le Θ.angle_le).trans
              (by linarith [Real.pi_pos])⟩
        have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
          (edge_direction_ne_zero p i) hsI hTI hlorth hi
        linarith [(Θ.interior s hs).2, Θ.angle_le]
      · have hsI : s + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
          constructor
          · linarith [(Θ.interior s hs).1, Real.pi_pos]
          · linarith [(Θ.interior s hs).2, Θ.angle_le]
        have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
          (edge_direction_ne_zero p i) hsI hTI hlorth hi
        linarith [(Θ.interior s hs).1]

private theorem polygonCapPolyline_fanLine_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    (Measure.hausdorffMeasure 1
      ((polygonCapPolyline K).carrier ∩ normalLine (t : Real.Angle) 0)).toReal =
      polygonPolylineLengthAt K t := by
  let p := polygonCapPolyline K
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hmeasure := p.toReal_hausdorffMeasure_carrier_inter_hyperplane
    (normalVector (t : Real.Angle)) 0
    (fun i hi ↦ hp.edge_subset_fanLine_of_orthogonal ht i hi)
  have htDomain : t ∈ angleDomain Θ := Or.inr ht
  rw [show normalLine (t : Real.Angle) 0 =
      {q | inner ℝ q (normalVector (t : Real.Angle)) = 0} by rfl,
    hmeasure]
  simp [polygonPolylineLengthAt, htDomain, polygonCapPolylineLength, p]

private theorem polygonNiche_inter_bottom_subset_exposedEdge_of_lt
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    polygonNiche Θ K.val ∩ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
  intro q hq
  rw [exposedEdge_bottom_eq_segment_zero_right K hω]
  rcases Set.mem_iUnion.mp hq.1.2 with ⟨t, ht⟩
  rcases Set.mem_iUnion.mp ht with ⟨htΘ, hqt⟩
  have htt := Θ.interior t htΘ
  have hcost : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [htt.1, Real.pi_pos], htt.2.trans_le Θ.angle_le⟩
  have hgapBounds := wedgeGaps_positive_lower_bound K.val t htt
  have hgap : 0 < (wedgeGaps K.val t).1 := hgapBounds.2.1.trans_le hgapBounds.1
  have hqy : q 1 = 0 := by
    have hline := hq.2
    change inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 at hline
    simpa [normalVector, frame, PiLp.inner_apply] using hline
  have hqx_endpoint : q 0 < (wedgeEndpoints K.val t).1 0 := by
    have hb := hqt.1
    change inner ℝ q (normalVector (t : Real.Angle)) <
      supportValue K.val.val (t : Real.Angle) - 1 at hb
    simp [normalVector, frame, PiLp.inner_apply, hqy] at hb
    simp only [wedgeEndpoints]
    simp [normalVector, frame]
    exact (lt_div_iff₀ hcost).2 (by simpa [mul_comm] using hb)
  have hendpoint_A : (wedgeEndpoints K.val t).1 0 < (capVertices K.val 0).1.2 0 := by
    simpa [wedgeGaps, inner_sub_left, normalVector, frame, PiLp.inner_apply] using hgap
  have hqx_nonneg : 0 ≤ q 0 := by
    have hfan := hq.1.1.1
    change 0 ≤ inner ℝ q (normalVector (Θ.angle : Real.Angle)) at hfan
    simp [normalVector, frame, PiLp.inner_apply, hqy] at hfan
    have hcosω : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hfan) hcosω
  have hApos : 0 < (capVertices K.val 0).1.2 0 :=
    hqx_nonneg.trans_lt (hqx_endpoint.trans hendpoint_A)
  apply mem_segment_of_fst_mem_Icc_of_mem_normalLine hApos
    (t := Real.pi / 2) (c := 0)
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  · simp [normalLine, normalVector, frame, PiLp.inner_apply]
  · rw [capVertices_zero_snd_eq K]
    simp [normalLine, normalVector, frame, PiLp.inner_apply]
  · exact hq.2
  · exact ⟨hqx_nonneg, (hqx_endpoint.trans hendpoint_A).le⟩

private theorem mem_segment_of_inner_tangent_mem_Icc_of_mem_normalLine
    {a b q : Point} {t : Real.Angle} {c : ℝ}
    (hab : inner ℝ a (tangentVector t) < inner ℝ b (tangentVector t))
    (ha : a ∈ normalLine t c) (hb : b ∈ normalLine t c)
    (hq : q ∈ normalLine t c)
    (hx : inner ℝ q (tangentVector t) ∈
      Set.Icc (inner ℝ a (tangentVector t)) (inner ℝ b (tangentVector t))) :
    q ∈ segment ℝ a b := by
  let r := (inner ℝ q (tangentVector t) - inner ℝ a (tangentVector t)) /
    (inner ℝ b (tangentVector t) - inner ℝ a (tangentVector t))
  have hden : 0 < inner ℝ b (tangentVector t) - inner ℝ a (tangentVector t) :=
    sub_pos.mpr hab
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hden.le
    · exact (div_le_one hden).2 (by linarith [hx.2])
  rw [segment_eq_image']
  refine ⟨r, hr, ?_⟩
  change a + r • (b - a) = q
  have hn : inner ℝ (a + r • (b - a)) (normalVector t) =
      inner ℝ q (normalVector t)
      := by
    change inner ℝ a (normalVector t) = c at ha
    change inner ℝ b (normalVector t) = c at hb
    change inner ℝ q (normalVector t) = c at hq
    rw [inner_add_left, real_inner_smul_left, inner_sub_left, ha, hb, sub_self,
      mul_zero, add_zero, hq]
  have htangent : inner ℝ (a + r • (b - a)) (tangentVector t) =
      inner ℝ q (tangentVector t)
      := by
    rw [inner_add_left, real_inner_smul_left, inner_sub_left]
    dsimp [r]
    field_simp
    ring
  rw [← inner_normalVector_smul_add_inner_tangentVector_smul
      (a + r • (b - a)) t,
    ← inner_normalVector_smul_add_inner_tangentVector_smul q t, hn, htangent]

private theorem polygonNiche_inter_left_subset_exposedEdge_of_lt
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    polygonNiche Θ K.val ∩ normalLine (Θ.angle : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle) := by
  intro q hq
  rw [exposedEdge_left_eq_segment_zero_left K hω]
  rcases Set.mem_iUnion.mp hq.1.2 with ⟨t, ht⟩
  rcases Set.mem_iUnion.mp ht with ⟨htΘ, hqt⟩
  have htt := Θ.interior t htΘ
  have hcosδ : 0 < Real.cos (Θ.angle - t) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [htt.2, Real.pi_pos], by linarith [htt.1, Θ.angle_le]⟩
  have hgapBounds := wedgeGaps_positive_lower_bound K.val t htt
  have hgap : 0 < (wedgeGaps K.val t).2 :=
    hgapBounds.2.2.2.trans_le hgapBounds.2.2.1
  have hqcoord_endpoint : inner ℝ q (tangentVector (Θ.angle : Real.Angle)) <
      inner ℝ (wedgeEndpoints K.val t).2
        (tangentVector (Θ.angle : Real.Angle)) := by
    have hd := hqt.2
    change inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
      supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 at hd
    have hqdecomp := inner_normalVector_smul_add_inner_tangentVector_smul
      q (Θ.angle : Real.Angle)
    have hqnormal := hq.2
    change inner ℝ q (normalVector (Θ.angle : Real.Angle)) = 0 at hqnormal
    rw [hqnormal, zero_smul, zero_add] at hqdecomp
    rw [← hqdecomp, real_inner_smul_left] at hd
    have hinner : inner ℝ (tangentVector (Θ.angle : Real.Angle))
        (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
        Real.cos (Θ.angle - t) := by
      rw [Real.Angle.coe_add, normalVector_add_pi_div_two]
      simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
        Real.cos_sub]
      ring_nf
    rw [hinner] at hd
    have hendpoint : inner ℝ (wedgeEndpoints K.val t).2
        (tangentVector (Θ.angle : Real.Angle)) =
        (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos (Θ.angle - t) := by
      simp only [wedgeEndpoints, real_inner_smul_left]
      rw [show inner ℝ (tangentVector (Θ.angle : Real.Angle))
        (tangentVector (Θ.angle : Real.Angle)) = 1 by
          exact inner_tangentVector_self Θ.angle, mul_one]
    rw [hendpoint]
    exact (lt_div_iff₀ hcosδ).2 (by linarith [hd])
  have hendpoint_C : inner ℝ (wedgeEndpoints K.val t).2
      (tangentVector (Θ.angle : Real.Angle)) <
      inner ℝ (capVertices K.val Θ.angle).2.1
        (tangentVector (Θ.angle : Real.Angle)) := by
    simpa [wedgeGaps, inner_sub_left] using hgap
  have hqcoord_nonneg : 0 ≤ inner ℝ q (tangentVector (Θ.angle : Real.Angle)) := by
    have hfan := hq.1.1.2
    change 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hfan
    have hqdecomp := inner_normalVector_smul_add_inner_tangentVector_smul
      q (Θ.angle : Real.Angle)
    have hqnormal := hq.2
    change inner ℝ q (normalVector (Θ.angle : Real.Angle)) = 0 at hqnormal
    rw [hqnormal, zero_smul, zero_add] at hqdecomp
    rw [← hqdecomp, real_inner_smul_left] at hfan
    have hcosω : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
    have hinner : inner ℝ (tangentVector (Θ.angle : Real.Angle))
        (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = Real.cos Θ.angle := by
      simp [tangentVector, normalVector, frame, PiLp.inner_apply,
        Fin.sum_univ_two]
    rw [hinner] at hfan
    exact nonneg_of_mul_nonneg_left hfan hcosω
  have hCpos : 0 < inner ℝ (capVertices K.val Θ.angle).2.1
      (tangentVector (Θ.angle : Real.Angle)) :=
    hqcoord_nonneg.trans_lt (hqcoord_endpoint.trans hendpoint_C)
  apply mem_segment_of_inner_tangent_mem_Icc_of_mem_normalLine
    (t := (Θ.angle : Real.Angle)) (c := 0) (by simpa using hCpos)
  · simp [normalLine]
  · have hCeq := capVertices_angle_fst_eq K
    change inner ℝ (capVertices K.val Θ.angle).2.1
      (normalVector (Θ.angle : Real.Angle)) = 0
    rw [hCeq, real_inner_smul_left, real_inner_comm,
      inner_normalVector_tangentVector, mul_zero]
  · exact hq.2
  · exact ⟨by simpa using hqcoord_nonneg, (hqcoord_endpoint.trans hendpoint_C).le⟩

private theorem polygonNiche_inter_bottom_subset_exposedEdge_of_eq
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle = Real.pi / 2) :
    polygonNiche Θ K.val ∩ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
  intro q hq
  rw [exposedEdge_bottom_eq_segment_left_right K hω]
  rcases Set.mem_iUnion.mp hq.1.2 with ⟨t, ht⟩
  rcases Set.mem_iUnion.mp ht with ⟨htΘ, hqt⟩
  have htt := Θ.interior t htΘ
  have hcost : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [htt.1, Real.pi_pos], htt.2.trans_le Θ.angle_le⟩
  have hcosδ : 0 < Real.cos (Θ.angle - t) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [htt.2, Real.pi_pos], by linarith [htt.1, Θ.angle_le]⟩
  have hgapBounds := wedgeGaps_positive_lower_bound K.val t htt
  have hgapA : 0 < (wedgeGaps K.val t).1 := hgapBounds.2.1.trans_le hgapBounds.1
  have hgapC : 0 < (wedgeGaps K.val t).2 :=
    hgapBounds.2.2.2.trans_le hgapBounds.2.2.1
  have hqy : q 1 = 0 := by
    have hline := hq.2
    change inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 at hline
    simpa [normalVector, frame, PiLp.inner_apply] using hline
  have hqx_endpoint : q 0 < (wedgeEndpoints K.val t).1 0 := by
    have hb := hqt.1
    change inner ℝ q (normalVector (t : Real.Angle)) <
      supportValue K.val.val (t : Real.Angle) - 1 at hb
    simp [normalVector, frame, PiLp.inner_apply, hqy] at hb
    simp only [wedgeEndpoints]
    simp [normalVector, frame]
    exact (lt_div_iff₀ hcost).2 (by simpa [mul_comm] using hb)
  have hendpoint_A : (wedgeEndpoints K.val t).1 0 < (capVertices K.val 0).1.2 0 := by
    simpa [wedgeGaps, inner_sub_left, normalVector, frame, PiLp.inner_apply] using hgapA
  have hqcoord_endpoint : inner ℝ q
      (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) <
      inner ℝ (wedgeEndpoints K.val t).2
        (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) := by
    have hd := hqt.2
    change inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
      supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 at hd
    have hqdecomp := inner_normalVector_smul_add_inner_tangentVector_smul
      q ((Real.pi / 2 : ℝ) : Real.Angle)
    have hqnormal := hq.2
    change inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 at hqnormal
    rw [hqnormal, zero_smul, zero_add] at hqdecomp
    rw [← hqdecomp, real_inner_smul_left] at hd
    have hinner : inner ℝ (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle))
        (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
        Real.cos (Real.pi / 2 - t) := by
      rw [Real.Angle.coe_add, normalVector_add_pi_div_two]
      simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
        Real.cos_sub]
    rw [hinner] at hd
    have hcosEq : Real.cos (Θ.angle - t) = Real.cos (Real.pi / 2 - t) := by
      rw [hω]
    have hendpoint : inner ℝ (wedgeEndpoints K.val t).2
        (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
        (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos (Real.pi / 2 - t) := by
      calc
        _ = (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
            Real.cos (Θ.angle - t) := by
          rw [show tangentVector ((Real.pi / 2 : ℝ) : Real.Angle) =
              tangentVector (Θ.angle : Real.Angle) by rw [hω]]
          simp only [wedgeEndpoints, real_inner_smul_left]
          rw [show inner ℝ (tangentVector (Θ.angle : Real.Angle))
            (tangentVector (Θ.angle : Real.Angle)) = 1 by
              exact inner_tangentVector_self Θ.angle, mul_one]
        _ = _ := by rw [hcosEq]
    rw [hendpoint]
    have hcosT : 0 < Real.cos (Real.pi / 2 - t) := by simpa [hω] using hcosδ
    exact (lt_div_iff₀ hcosT).2 (by linarith [hd])
  have hendpoint_C : inner ℝ (wedgeEndpoints K.val t).2
      (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) <
      inner ℝ (capVertices K.val Θ.angle).2.1
        (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) := by
    rw [← hω]
    simpa [wedgeGaps, inner_sub_left] using hgapC
  have hCx_lt_qx : (capVertices K.val Θ.angle).2.1 0 < q 0 := by
    have h := hqcoord_endpoint.trans hendpoint_C
    simp [tangentVector, frame, PiLp.inner_apply, hω] at h
    simpa [hω] using h
  have hqx_lt_Ax : q 0 < (capVertices K.val 0).1.2 0 :=
    hqx_endpoint.trans hendpoint_A
  apply mem_segment_of_fst_mem_Icc_of_mem_normalLine (polygonCap_left_x_lt_right_x K)
    (t := Real.pi / 2) (c := 0)
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  · rw [capVertices_angle_fst_eq K]
    simp [normalLine, normalVector, tangentVector, frame, PiLp.inner_apply, hω]
  · rw [capVertices_zero_snd_eq K]
    simp [normalLine, normalVector, frame, PiLp.inner_apply]
  · exact hq.2
  · exact ⟨hCx_lt_qx.le, hqx_lt_Ax.le⟩

private theorem mem_frontier_normalHalfPlane_upper_closed_of_mem_normalLine
    (t : ℝ) (c : ℝ) {q : Point} (hq : q ∈ normalLine (t : Real.Angle) c) :
    q ∈ frontier (normalHalfPlane (t : Real.Angle) c true false) := by
  have hqH : q ∈ normalHalfPlane (t : Real.Angle) c true false := by
    change c ≤ inner ℝ q (normalVector (t : Real.Angle))
    exact hq.ge
  apply (mem_frontier_iff_notMem_interior hqH).mpr
  intro hqInt
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior q hqInt
  let e := ε / 2
  let z := q - e • normalVector (t : Real.Angle)
  have he : 0 < e := half_pos hε
  have hzball : z ∈ Metric.ball q ε := by
    change dist z q < ε
    simp [z, norm_smul, norm_normalVector_real, abs_of_pos he]
    dsimp [e]
    linarith
  have hz := interior_subset (hball hzball)
  change c ≤ inner ℝ z (normalVector (t : Real.Angle)) at hz
  change inner ℝ q (normalVector (t : Real.Angle)) = c at hq
  dsimp [z] at hz
  rw [inner_sub_left, real_inner_smul_left, inner_normalVector_self, mul_one, hq] at hz
  linarith

private theorem capFan_inter_fanLine_subset_frontier {Θ : AngleSet} {t : ℝ}
    (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    capFan Θ.angle ∩ normalLine (t : Real.Angle) 0 ⊆ frontier (capFan Θ.angle) := by
  intro q hq
  apply (mem_frontier_iff_notMem_interior hq.1).mpr
  intro hqInt
  rcases Set.mem_insert_iff.mp ht with rfl | ht
  · have hInt := interior_mono Set.inter_subset_left hqInt
    have hfront := mem_frontier_normalHalfPlane_upper_closed_of_mem_normalLine
      Θ.angle 0 hq.2
    exact (mem_frontier_iff_notMem_interior hq.1.1).mp hfront hInt
  · have ht : t = Real.pi / 2 := Set.mem_singleton_iff.mp ht
    subst t
    have hInt := interior_mono Set.inter_subset_right hqInt
    have hfront := mem_frontier_normalHalfPlane_upper_closed_of_mem_normalLine
      (Real.pi / 2) 0 hq.2
    exact (mem_frontier_iff_notMem_interior hq.1.2).mp hfront hInt

private theorem frontier_innerQuadrant_inter_fanLine_countable
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {s t : ℝ}
    (hs : s ∈ Θ.directions) (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    (frontier (innerQuadrant K.val.val s) ∩ normalLine (t : Real.Angle) 0).Countable := by
  have hsI : s ∈ Set.Ioo 0 Real.pi :=
    ⟨(Θ.interior s hs).1,
      ((Θ.interior s hs).2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos])⟩
  have hsTI : s + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [(Θ.interior s hs).1, Real.pi_pos]
    · linarith [(Θ.interior s hs).2, Θ.angle_le]
  have htI : t ∈ Set.Ioo 0 Real.pi := by
    rcases Set.mem_insert_iff.mp ht with rfl | ht
    · exact ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩
    · rw [Set.mem_singleton_iff.mp ht]
      exact ⟨by positivity, by linarith [Real.pi_pos]⟩
  have hst : s ≠ t := by
    rcases Set.mem_insert_iff.mp ht with rfl | ht
    · exact ne_of_lt (Θ.interior s hs).2
    · rw [Set.mem_singleton_iff.mp ht]
      exact ne_of_lt ((Θ.interior s hs).2.trans_le Θ.angle_le)
  have hsTt : s + Real.pi / 2 ≠ t := by
    rcases Set.mem_insert_iff.mp ht with rfl | ht
    · intro heq
      linarith [(Θ.interior s hs).1, Θ.angle_le]
    · rw [Set.mem_singleton_iff.mp ht]
      exact ne_of_gt (by linarith [(Θ.interior s hs).1])
  refine ((normalLine_inter_normalLine_subsingleton hsI htI hst
      (c := supportValue K.val.val (s : Real.Angle) - 1) (d := 0)).countable.union
    (normalLine_inter_normalLine_subsingleton hsTI htI hsTt
      (c := supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1)
      (d := 0)).countable).mono ?_
  rintro q ⟨hqfront, hqline⟩
  have hfront := frontier_inter_subset
    (normalHalfPlane (s : Real.Angle) (supportValue K.val.val (s : Real.Angle) - 1)
      false true)
    (normalHalfPlane ((s + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1)
      false true) hqfront
  rcases hfront with hfront | hfront
  · exact Or.inl ⟨frontier_normalHalfPlane_lower_strict_subset_normalLine _ _ hfront.1,
      hqline⟩
  · exact Or.inr ⟨frontier_normalHalfPlane_lower_strict_subset_normalLine _ _ hfront.2,
      hqline⟩

private theorem frontier_polygonNiche_inter_fanLine_eq_niche_inter
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {t : ℝ}
    (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    Measure.hausdorffMeasure 1
        (frontier (polygonNiche Θ K.val) ∩ normalLine (t : Real.Angle) 0) =
      Measure.hausdorffMeasure 1
        (polygonNiche Θ K.val ∩ normalLine (t : Real.Angle) 0) := by
  let X : Set Point := ⋃ s ∈ Θ.directions, innerQuadrant K.val.val s
  have hN : polygonNiche Θ K.val = capFan Θ.angle ∩ X := by simp [polygonNiche, X]
  rw [hN]
  apply measure_eq_of_symmDiff_subset_null (E := frontier X ∩ normalLine (t : Real.Angle) 0)
  · intro q hq
    rcases hq with hq | hq
    · refine ⟨?_, hq.1.2⟩
      rw [← closure_sdiff_interior]
      refine ⟨closure_mono Set.inter_subset_right (frontier_subset_closure hq.1.1), ?_⟩
      intro hqInt
      have hqX : q ∈ X := interior_subset hqInt
      have hqF : q ∈ capFan Θ.angle := by
        have hqcl := frontier_subset_closure hq.1.1
        exact (isClosed_capFan Θ.angle).closure_eq ▸
          closure_mono Set.inter_subset_left hqcl
      exact hq.2 ⟨⟨hqF, hqX⟩, hq.1.2⟩
    · have hqFront : q ∈ frontier (capFan Θ.angle ∩ X) := by
        apply (mem_frontier_iff_notMem_interior hq.1.1).mpr
        intro hqInt
        have hqFInt := interior_mono Set.inter_subset_left hqInt
        exact (mem_frontier_iff_notMem_interior hq.1.1.1).mp
          (capFan_inter_fanLine_subset_frontier ht ⟨hq.1.1.1, hq.1.2⟩) hqFInt
      exact (hq.2 ⟨hqFront, hq.1.2⟩).elim
  · have hcount : (frontier X ∩ normalLine (t : Real.Angle) 0).Countable := by
      refine (Set.Countable.biUnion Θ.directions.countable_toSet fun s hs ↦
        frontier_innerQuadrant_inter_fanLine_countable K hs ht).mono ?_
      rintro q ⟨hqX, hqline⟩
      have hqUnion := Finset.frontier_biUnion_subset Θ.directions
        (fun s ↦ innerQuadrant K.val.val s) hqX
      obtain ⟨s, hs, hqs⟩ := Set.mem_iUnion₂.mp hqUnion
      exact Set.mem_iUnion₂.mpr ⟨s, hs, ⟨hqs, hqline⟩⟩
    have := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
    exact hcount.measure_zero (Measure.hausdorffMeasure 1)

private theorem capVertices_zero_fst_pos_of_lt {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    0 < (capVertices K.val 0).1.2 0 := by
  obtain ⟨u, huK, hu⟩ := exists_mem_inner_eq_supportValue K.val.val
    (Θ.angle : Real.Angle)
  have huy : u 1 ≤ 1 := by
    have huy' := inner_le_supportValue K.val.val huK
      ((Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.1] at huy'
    simpa [normalVector, frame, PiLp.inner_apply] using huy'
  have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
  have hsin_lt : Real.sin Θ.angle < 1 := by
    nlinarith only [Real.sin_sq_add_cos_sq Θ.angle, sq_pos_of_pos hcos]
  have hux : 0 < u 0 := by
    rw [K.val.property.2.2.1] at hu
    simp [normalVector, frame, PiLp.inner_apply] at hu
    have hsin : 0 ≤ Real.sin Θ.angle :=
      (Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
        (Θ.angle_le.trans_lt (by linarith [Real.pi_pos]))).le
    have hmul := mul_le_mul_of_nonneg_left huy hsin
    nlinarith
  have hsupport : 0 < supportValue K.val.val (0 : Real.Angle) :=
    hux.trans_le (by
      have := inner_le_supportValue K.val.val huK (0 : Real.Angle)
      simpa [normalVector, frame, PiLp.inner_apply] using this)
  rw [capVertices_zero_snd_eq K]
  simpa [normalVector, frame] using hsupport

private theorem hausdorffMeasure_bottom_exposedEdge_sdiff_niche_eq_carrier_of_lt
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    Measure.hausdorffMeasure 1
        ((exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) \
          polygonNiche Θ K.val) ∩ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0) =
      Measure.hausdorffMeasure 1
        ((polygonCapPolyline K).carrier ∩
          normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0) := by
  let p := polygonCapPolyline K
  let A := (capVertices K.val 0).1.2
  let C := (capVertices K.val Θ.angle).2.1
  let L := openRay C (tangentVector (Θ.angle : Real.Angle))
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hclosed : IsClosed (capFan Θ.angle \ polygonNiche Θ K.val) := hp.2.2.2.2.1
  apply measure_eq_of_symmDiff_subset_null (E :=
    L ∩ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0)
  · intro q hq
    rcases hq with hq | hq
    · have hqF : q ∈ capFan Θ.angle := K.val.subset_capFan hq.1.1.1.1
      have hqFrontF := capFan_inter_fanLine_subset_frontier
        (Θ := Θ) (t := Real.pi / 2) (by simp) ⟨hqF, hq.1.2⟩
      have hqC : q ∈ capFan Θ.angle \ polygonNiche Θ K.val := ⟨hqF, hq.1.1.2⟩
      have hqFrontC : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
        apply (mem_frontier_iff_notMem_interior hqC).mpr
        intro hqInt
        exact (mem_frontier_iff_notMem_interior hqF).mp hqFrontF
          (interior_mono Set.sdiff_subset hqInt)
      rw [hp.2.2.2.2.2.1] at hqFrontC
      rcases hqFrontC with hqL | hqR
      · rcases hqL with hqL | hqcarrier
        · exact ⟨hqL, hq.1.2⟩
        · exact (hq.2 ⟨hqcarrier, hq.1.2⟩).elim
      · rcases hqR with ⟨r, hr, hqr⟩
        have hD := hq.1.1.1
        rw [exposedEdge_bottom_eq_segment_zero_right K hω] at hD
        have hApos : 0 < A 0 := capVertices_zero_fst_pos_of_lt K hω
        have hqx := (fst_mem_Icc_of_mem_segment_mc4d199c hApos.le hD).2
        have hqx' : A 0 < q 0 := by
          rw [hqr]
          simp [A, normalVector, frame]
          linarith
        linarith
    · have hD := polygonCapPolyline_carrier_inter_bottom_subset_exposedEdge_of_lt
        K hω hq.1
      have hqFrontC : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
        rw [hp.2.2.2.2.2.1]
        exact Or.inl (Or.inr hq.1.1)
      have hqC : q ∈ capFan Θ.angle \ polygonNiche Θ K.val :=
        hclosed.closure_eq ▸ frontier_subset_closure hqFrontC
      exact (hq.2 ⟨⟨hD, hqC.2⟩, hq.1.2⟩).elim
  · have hinner : inner ℝ (tangentVector (Θ.angle : Real.Angle))
        (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≠ 0 := by
      have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
      simpa [tangentVector, normalVector, frame, PiLp.inner_apply,
        Fin.sum_univ_two] using hcos.ne'
    exact hausdorffMeasure_openRay_inter_hyperplane_eq_zero hinner

private theorem hausdorffMeasure_left_exposedEdge_sdiff_niche_eq_carrier_of_lt
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    Measure.hausdorffMeasure 1
        ((exposedEdge K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle) \
          polygonNiche Θ K.val) ∩ normalLine (Θ.angle : Real.Angle) 0) =
      Measure.hausdorffMeasure 1
        ((polygonCapPolyline K).carrier ∩ normalLine (Θ.angle : Real.Angle) 0) := by
  let p := polygonCapPolyline K
  let A := (capVertices K.val 0).1.2
  let C := (capVertices K.val Θ.angle).2.1
  let R := openRay A (normalVector 0)
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hclosed : IsClosed (capFan Θ.angle \ polygonNiche Θ K.val) := hp.2.2.2.2.1
  have hCeq := capVertices_angle_fst_eq K
  change C = supportValue K.val.val
    ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) •
      tangentVector (Θ.angle : Real.Angle) at hCeq
  have hL : 0 ≤ supportValue K.val.val
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) :=
    supportValue_nonneg_of_mem_capUpperAngles K.val hω
      (Or.inr ⟨by linarith [Θ.angle_pos, Real.pi_pos], le_rfl⟩)
  have hCcoord : 0 ≤ inner ℝ C (tangentVector (Θ.angle : Real.Angle)) := by
    rw [hCeq, real_inner_smul_left]
    rw [show inner ℝ (tangentVector (Θ.angle : Real.Angle))
      (tangentVector (Θ.angle : Real.Angle)) = 1 by
        exact inner_tangentVector_self Θ.angle, mul_one]
    exact hL
  apply measure_eq_of_symmDiff_subset_null (E :=
    R ∩ normalLine (Θ.angle : Real.Angle) 0)
  · intro q hq
    rcases hq with hq | hq
    · have hqF : q ∈ capFan Θ.angle := K.val.subset_capFan hq.1.1.1.1
      have hqFrontF := capFan_inter_fanLine_subset_frontier
        (Θ := Θ) (t := Θ.angle) (by simp) ⟨hqF, hq.1.2⟩
      have hqC : q ∈ capFan Θ.angle \ polygonNiche Θ K.val := ⟨hqF, hq.1.1.2⟩
      have hqFrontC : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
        apply (mem_frontier_iff_notMem_interior hqC).mpr
        intro hqInt
        exact (mem_frontier_iff_notMem_interior hqF).mp hqFrontF
          (interior_mono Set.sdiff_subset hqInt)
      rw [hp.2.2.2.2.2.1] at hqFrontC
      rcases hqFrontC with hqL | hqR
      · rcases hqL with hqL | hqcarrier
        · rcases hqL with ⟨r, hr, hqr⟩
          have hD := hq.1.1.1
          rw [exposedEdge_left_eq_segment_zero_left K hω] at hD
          rcases hD with ⟨u, v, hu, hv, huv, hqseg⟩
          have hvle : v ≤ 1 := by linarith
          have hqcoord_le : inner ℝ q (tangentVector (Θ.angle : Real.Angle)) ≤
              inner ℝ C (tangentVector (Θ.angle : Real.Angle)) := by
            rw [← hqseg, inner_add_left, real_inner_smul_left,
              real_inner_smul_left, inner_zero_left, mul_zero, zero_add]
            exact mul_le_of_le_one_left hCcoord hvle
          have hqcoord_gt : inner ℝ C (tangentVector (Θ.angle : Real.Angle)) <
              inner ℝ q (tangentVector (Θ.angle : Real.Angle)) := by
            change inner ℝ (capVertices K.val Θ.angle).2.1
                (tangentVector (Θ.angle : Real.Angle)) <
              inner ℝ q (tangentVector (Θ.angle : Real.Angle))
            rw [hqr, inner_add_left, real_inner_smul_left]
            rw [show inner ℝ (tangentVector (Θ.angle : Real.Angle))
              (tangentVector (Θ.angle : Real.Angle)) = 1 by
                exact inner_tangentVector_self Θ.angle]
            simp
            exact hr
          exact (not_lt_of_ge hqcoord_le hqcoord_gt).elim
        · exact (hq.2 ⟨hqcarrier, hq.1.2⟩).elim
      · exact ⟨hqR, hq.1.2⟩
    · have hD := polygonCapPolyline_carrier_inter_left_subset_exposedEdge_of_lt
        K hω hq.1
      have hqFrontC : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
        rw [hp.2.2.2.2.2.1]
        exact Or.inl (Or.inr hq.1.1)
      have hqC : q ∈ capFan Θ.angle \ polygonNiche Θ K.val :=
        hclosed.closure_eq ▸ frontier_subset_closure hqFrontC
      exact (hq.2 ⟨⟨hD, hqC.2⟩, hq.1.2⟩).elim
  · have hinner : inner ℝ (normalVector 0)
        (normalVector (Θ.angle : Real.Angle)) ≠ 0 := by
      have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
      rw [show (0 : Real.Angle) = ((0 : ℝ) : Real.Angle) by rfl,
        inner_normalVector_normalVector, zero_sub, Real.cos_neg]
      exact hcos.ne'
    exact hausdorffMeasure_openRay_inter_hyperplane_eq_zero hinner

private theorem bottom_exposedEdge_sdiff_niche_inter_eq_carrier_of_eq
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle = Real.pi / 2) :
    (exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) \
        polygonNiche Θ K.val) ∩ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 =
      (polygonCapPolyline K).carrier ∩
        normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 := by
  let p := polygonCapPolyline K
  let A := (capVertices K.val 0).1.2
  let C := (capVertices K.val Θ.angle).2.1
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hclosed : IsClosed (capFan Θ.angle \ polygonNiche Θ K.val) := hp.2.2.2.2.1
  ext q
  constructor
  · intro hq
    have hqF : q ∈ capFan Θ.angle := K.val.subset_capFan hq.1.1.1
    have hqFrontF := capFan_inter_fanLine_subset_frontier
      (Θ := Θ) (t := Real.pi / 2) (by simp) ⟨hqF, hq.2⟩
    have hqC : q ∈ capFan Θ.angle \ polygonNiche Θ K.val := ⟨hqF, hq.1.2⟩
    have hqFrontC : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
      apply (mem_frontier_iff_notMem_interior hqC).mpr
      intro hqInt
      exact (mem_frontier_iff_notMem_interior hqF).mp hqFrontF
        (interior_mono Set.sdiff_subset hqInt)
    rw [hp.2.2.2.2.2.1] at hqFrontC
    rcases hqFrontC with hqL | hqR
    · rcases hqL with hqL | hqcarrier
      · rcases hqL with ⟨r, hr, hqr⟩
        have hD := hq.1.1
        rw [exposedEdge_bottom_eq_segment_left_right K hω] at hD
        have hqx := fst_mem_Icc_of_mem_segment_mc4d199c
          (polygonCap_left_x_lt_right_x K).le hD
        have hqx' : q 0 < C 0 := by
          rw [hqr]
          simp [C, tangentVector, frame, hω]
          exact hr
        exact (not_lt_of_ge (by simpa [C] using hqx.1) hqx').elim
      · exact ⟨hqcarrier, hq.2⟩
    · rcases hqR with ⟨r, hr, hqr⟩
      have hD := hq.1.1
      rw [exposedEdge_bottom_eq_segment_left_right K hω] at hD
      have hqx := fst_mem_Icc_of_mem_segment_mc4d199c
        (polygonCap_left_x_lt_right_x K).le hD
      have hqx' : A 0 < q 0 := by
        rw [hqr]
        simp [A, normalVector, frame]
        exact hr
      exact (not_lt_of_ge (by simpa [A] using hqx.2) hqx').elim
  · intro hq
    have hD := polygonCapPolyline_carrier_inter_bottom_subset_exposedEdge_of_eq
      K hω hq
    have hqFrontC : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
      rw [hp.2.2.2.2.2.1]
      exact Or.inl (Or.inr hq.1)
    have hqC : q ∈ capFan Θ.angle \ polygonNiche Θ K.val :=
      hclosed.closure_eq ▸ frontier_subset_closure hqFrontC
    exact ⟨⟨hD, hqC.2⟩, hq.2⟩

private theorem segment_subset_normalLine {a b : Point} {t : Real.Angle} {c : ℝ}
    (ha : a ∈ normalLine t c) (hb : b ∈ normalLine t c) :
    segment ℝ a b ⊆ normalLine t c := by
  rintro q ⟨u, v, hu, hv, huv, rfl⟩
  change inner ℝ (u • a + v • b) (normalVector t) = c
  change inner ℝ a (normalVector t) = c at ha
  change inner ℝ b (normalVector t) = c at hb
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, ha, hb]
  linear_combination c * huv

private theorem hausdorffMeasure_niche_inter_eq_exposedEdge_sub_carrier
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {t : ℝ}
    (hDline : exposedEdge K.val.val ((t + Real.pi : ℝ) : Real.Angle) ⊆
      normalLine (t : Real.Angle) 0)
    (hNsub : polygonNiche Θ K.val ∩ normalLine (t : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((t + Real.pi : ℝ) : Real.Angle))
    (hcomp : Measure.hausdorffMeasure 1
        ((exposedEdge K.val.val ((t + Real.pi : ℝ) : Real.Angle) \
          polygonNiche Θ K.val) ∩ normalLine (t : Real.Angle) 0) =
      Measure.hausdorffMeasure 1
        ((polygonCapPolyline K).carrier ∩ normalLine (t : Real.Angle) 0)) :
    (Measure.hausdorffMeasure 1
      (polygonNiche Θ K.val ∩ normalLine (t : Real.Angle) 0)).toReal =
      (Measure.hausdorffMeasure 1
        (exposedEdge K.val.val ((t + Real.pi : ℝ) : Real.Angle))).toReal -
      (Measure.hausdorffMeasure 1
        ((polygonCapPolyline K).carrier ∩ normalLine (t : Real.Angle) 0)).toReal := by
  let μ : Measure Point := Measure.hausdorffMeasure 1
  let D := exposedEdge K.val.val ((t + Real.pi : ℝ) : Real.Angle)
  let M := polygonNiche Θ K.val ∩ normalLine (t : Real.Angle) 0
  have hdiff : D \ M =
      (D \ polygonNiche Θ K.val) ∩ normalLine (t : Real.Angle) 0 := by
    ext q
    constructor
    · intro hq
      exact ⟨⟨hq.1, fun hqN ↦ hq.2 ⟨hqN, hDline hq.1⟩⟩, hDline hq.1⟩
    · intro hq
      exact ⟨hq.1.1, fun hqM ↦ hq.1.2 hqM.1⟩
  have hNMeas : MeasurableSet (polygonNiche Θ K.val) := by
    exact (isClosed_capFan Θ.angle).measurableSet.inter
      (isOpen_iUnion fun s ↦ isOpen_iUnion fun _ ↦
        isOpen_innerQuadrant K.val.val s).measurableSet
  have hMMeas : MeasurableSet M :=
    hNMeas.inter (isClosed_eq (by fun_prop) continuous_const).measurableSet
  have hDfinite : μ D ≠ ⊤ := by
    dsimp [μ, D]
    rw [exposedEdge_eq_segment_edgeVertices, MeasureTheory.hausdorffMeasure_segment,
      edist_dist]
    simp
  have hreal := MeasureTheory.measureReal_sdiff (μ := μ) hNsub hMMeas hDfinite
  change (μ (D \ M)).toReal = (μ D).toReal - (μ M).toReal at hreal
  rw [hdiff] at hreal
  have hcompReal := congrArg ENNReal.toReal hcomp
  dsimp [μ, D, M] at hreal hcompReal ⊢
  rw [hcompReal] at hreal
  linarith

private theorem bottom_exposedEdge_subset_fanLine_of_lt {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) ⊆
      normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 := by
  rw [exposedEdge_bottom_eq_segment_zero_right K hω]
  apply segment_subset_normalLine
  · simp [normalLine]
  · rw [capVertices_zero_snd_eq K]
    simp [normalLine, normalVector, frame, PiLp.inner_apply]

private theorem left_exposedEdge_subset_fanLine_of_lt {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    exposedEdge K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle) ⊆
      normalLine (Θ.angle : Real.Angle) 0 := by
  rw [exposedEdge_left_eq_segment_zero_left K hω]
  apply segment_subset_normalLine
  · simp [normalLine]
  · change inner ℝ (capVertices K.val Θ.angle).2.1
      (normalVector (Θ.angle : Real.Angle)) = 0
    rw [capVertices_angle_fst_eq K, real_inner_smul_left,
      show inner ℝ (tangentVector (Θ.angle : Real.Angle))
        (normalVector (Θ.angle : Real.Angle)) = 0 by
          rw [real_inner_comm, inner_normalVector_tangentVector], mul_zero]

private theorem bottom_exposedEdge_subset_fanLine_of_eq {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle = Real.pi / 2) :
    exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) ⊆
      normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 := by
  rw [exposedEdge_bottom_eq_segment_left_right K hω]
  apply segment_subset_normalLine
  · rw [capVertices_angle_fst_eq K]
    simp [normalLine, normalVector, tangentVector, frame, PiLp.inner_apply, hω]
  · rw [capVertices_zero_snd_eq K]
    simp [normalLine, normalVector, frame, PiLp.inner_apply]

private theorem polygonNiche_fanLine_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    (Measure.hausdorffMeasure 1
      (polygonNiche Θ K.val ∩ normalLine (t : Real.Angle) 0)).toReal =
      (Measure.hausdorffMeasure 1
        (exposedEdge K.val.val ((t + Real.pi : ℝ) : Real.Angle))).toReal -
      polygonPolylineLengthAt K t := by
  by_cases hω : Θ.angle < Real.pi / 2
  · rcases Set.mem_insert_iff.mp ht with rfl | ht
    · rw [← polygonCapPolyline_fanLine_length K (by simp)]
      exact hausdorffMeasure_niche_inter_eq_exposedEdge_sub_carrier K
        (left_exposedEdge_subset_fanLine_of_lt K hω)
        (polygonNiche_inter_left_subset_exposedEdge_of_lt K hω)
        (hausdorffMeasure_left_exposedEdge_sdiff_niche_eq_carrier_of_lt K hω)
    · have ht : t = Real.pi / 2 := Set.mem_singleton_iff.mp ht
      subst t
      rw [← polygonCapPolyline_fanLine_length K (by simp)]
      apply hausdorffMeasure_niche_inter_eq_exposedEdge_sub_carrier K
      · convert bottom_exposedEdge_subset_fanLine_of_lt K hω using 1; ring_nf
      · convert polygonNiche_inter_bottom_subset_exposedEdge_of_lt K hω using 1; ring_nf
      · convert hausdorffMeasure_bottom_exposedEdge_sdiff_niche_eq_carrier_of_lt
          K hω using 1; ring_nf
  · have hωeq : Θ.angle = Real.pi / 2 := le_antisymm Θ.angle_le (le_of_not_gt hω)
    have htT : t = Real.pi / 2 := by
      rcases Set.mem_insert_iff.mp ht with ht | ht
      · exact ht.trans hωeq
      · exact Set.mem_singleton_iff.mp ht
    subst t
    rw [← polygonCapPolyline_fanLine_length K (by simp)]
    apply hausdorffMeasure_niche_inter_eq_exposedEdge_sub_carrier K
    · convert bottom_exposedEdge_subset_fanLine_of_eq K hωeq using 1; ring_nf
    · convert polygonNiche_inter_bottom_subset_exposedEdge_of_eq K hωeq using 1; ring_nf
    · convert congrArg (Measure.hausdorffMeasure 1)
        (bottom_exposedEdge_sdiff_niche_inter_eq_carrier_of_eq K hωeq) using 1;
        ring_nf

/-- The niche trace on a fan line is the lower face length minus polyline length. -/
theorem polygonNiche_fanLine_lengths {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    nicheBoundaryLength K (normalLine t 0) =
        (surfaceAreaMeasure K.val.val {((t + Real.pi : ℝ) : Real.Angle)}).toReal -
          polygonPolylineLengthAt K t ∧
      (Measure.hausdorffMeasure 1
        (polygonNiche Θ K.val ∩ normalLine t 0)).toReal =
        (surfaceAreaMeasure K.val.val {((t + Real.pi : ℝ) : Real.Angle)}).toReal -
          polygonPolylineLengthAt K t := by
  have hN := polygonNiche_fanLine_length K ht
  have hatom := congrArg ENNReal.toReal
    (surfaceAreaMeasure_atom_length K.val.val
      ((t + Real.pi : ℝ) : Real.Angle)).1
  rw [← hatom] at hN
  refine ⟨?_, hN⟩
  unfold nicheBoundaryLength
  rw [frontier_polygonNiche_inter_fanLine_eq_niche_inter K ht]
  exact hN

/-- Inner-wall and inner-ray niche lengths agree with the corresponding polyline lengths. -/
theorem polygonNiche_wall_lengths {Θ : AngleSet} (K : PolygonCapSpace Θ)
    {t : ℝ} (ht : t ∈ Θ.directions) :
    nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).b =
      polygonPolylineLengthAt K t ∧
    nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).bRay =
      polygonPolylineLengthAt K t ∧
    nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).d =
      polygonPolylineLengthAt K (t + Real.pi / 2) ∧
    nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).dRay =
      polygonPolylineLengthAt K (t + Real.pi / 2) := by
  have hf := rotatingHallwayParts_formulas
    (K.val.val : Set Point) (t : Real.Angle)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold nicheBoundaryLength
    rw [hf.2.2.2.2.1]
    exact polygonNiche_bLine_length K ht
  · unfold nicheBoundaryLength
    exact polygonNiche_bRay_length K ht
  · unfold nicheBoundaryLength
    rw [hf.2.2.2.2.2.2.1]
    exact polygonNiche_dLine_length K ht
  · unfold nicheBoundaryLength
    exact polygonNiche_dRay_length K ht

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
# Polygon / Polyline / Length
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem polygonCap_polyline_lengths {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    (∀ t ∈ Θ.directions,
      nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).b =
        polygonPolylineLengthAt K t ∧
      nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).bRay =
        polygonPolylineLengthAt K t ∧
      nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).d =
        polygonPolylineLengthAt K (t + Real.pi / 2) ∧
      nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).dRay =
        polygonPolylineLengthAt K (t + Real.pi / 2)) ∧
    (∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      nicheBoundaryLength K (normalLine t 0) =
        (surfaceAreaMeasure K.val.val {((t + Real.pi : ℝ) : Real.Angle)}).toReal -
          polygonPolylineLengthAt K t ∧
      (MeasureTheory.Measure.hausdorffMeasure 1
        (polygonNiche Θ K.val ∩ normalLine t 0)).toReal =
        (surfaceAreaMeasure K.val.val {((t + Real.pi : ℝ) : Real.Angle)}).toReal -
          polygonPolylineLengthAt K t) := by
  exact ⟨fun _ ht ↦ polygonNiche_wall_lengths K ht,
    fun _ ht ↦ polygonNiche_fanLine_lengths K ht⟩

private lemma polygonCapPolyline_sum_length_mul_sin {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (D : Finset ℝ) (hD : (D : Set ℝ) = angleDomain Θ) :
    ∑ t ∈ D, polygonPolylineLengthAt K t * Real.sin t =
      ((capVertices K.val 0).1.2) 0 - ((capVertices K.val Θ.angle).2.1) 0 := by
  classical
  let p := polygonCapPolyline K
  have hp : IsCapPolyline K p := (polygonCap_polyline K).choose_spec
  have hmem (t : ℝ) : t ∈ D ↔ t ∈ angleDomain Θ := by
    change t ∈ (D : Set ℝ) ↔ _
    rw [hD]
  have h := p.sum_normal_lengths_mul_sin D
    (fun t ht ↦ angleDomain_subset_Ioo Θ ((hmem t).mp ht)) (by
      intro i
      obtain ⟨t, ht⟩ := hp.2.2.2.1 i
      exact ⟨t.val, (hmem t.val).mpr t.property, ht⟩)
  have heq : ∑ t ∈ D, polygonPolylineLengthAt K t * Real.sin t =
      ∑ t ∈ D, (∑ i : Fin p.edges,
        if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (t : Real.Angle)) = 0 then
          dist (p.vertices i.castSucc) (p.vertices i.succ) else 0) * Real.sin t := by
    apply Finset.sum_congr rfl
    intro t ht
    simp only [polygonPolylineLengthAt, dite_eq_left ((hmem t).mp ht), polygonCapPolylineLength]
    rfl
  rw [heq, h, hp.2.1, hp.2.2.1]

theorem polygonCap_not_balanced_positive {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (h : ¬ IsBalancedPolygonCap K) :
    ∃ t : angleDomain Θ,
      ENNReal.ofReal (polygonCapPolylineLength K t) <
        surfaceAreaMeasure K.val.val {(t.val : Real.Angle)} := by
  classical
  by_contra hnot
  push Not at hnot
  have hfinite : (angleDomain Θ).Finite := by
    unfold angleDomain
    exact (Θ.directions.finite_toSet.union
      (Θ.directions.finite_toSet.image (fun t ↦ t + Real.pi / 2))).union (Set.toFinite _)
  let D := hfinite.toFinset
  have hD : (D : Set ℝ) = angleDomain Θ := hfinite.coe_toFinset
  have hne : D.Nonempty := by
    refine ⟨Θ.angle, ?_⟩
    change Θ.angle ∈ hfinite.toFinset
    simp [angleDomain]
  have hmem (t : ℝ) : t ∈ D ↔ t ∈ angleDomain Θ := by
    change t ∈ (D : Set ℝ) ↔ _
    rw [hD]
  have hpoly (t : angleDomain Θ) : 0 ≤ polygonCapPolylineLength K t := by
    unfold polygonCapPolylineLength
    exact Finset.sum_nonneg (fun _ _ ↦ by split_ifs <;> positivity)
  have htop (t : ℝ) : surfaceAreaMeasure K.val.val {(t : Real.Angle)} ≠ ⊤ := by
    rw [(surfaceAreaMeasure_atom_length K.val.val (t : Real.Angle)).2.1]
    exact ENNReal.ofReal_ne_top
  have hle (t : ℝ) (ht : t ∈ D) :
      (surfaceAreaMeasure K.val.val {(t : Real.Angle)}).toReal ≤ polygonPolylineLengthAt K t := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hnot ⟨t, (hmem t).mp ht⟩)
    simpa [polygonPolylineLengthAt, (hmem t).mp ht, ENNReal.toReal_ofReal
      (hpoly ⟨t, (hmem t).mp ht⟩)] using hh
  have hsum : ∑ t ∈ D,
      (polygonPolylineLengthAt K t -
        (surfaceAreaMeasure K.val.val {(t : Real.Angle)}).toReal) * Real.sin t = 0 := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, polygonCapPolyline_sum_length_mul_sin K D hD]
    have hh := K.sum_hausdorffMeasure_exposedEdge_mul_sin D hne hD
    have heq : ∑ t ∈ D,
        (surfaceAreaMeasure K.val.val {(t : Real.Angle)}).toReal * Real.sin t =
        ((capVertices K.val 0).1.2) 0 - ((capVertices K.val Θ.angle).2.1) 0 := by
      simpa only [(surfaceAreaMeasure_atom_length K.val.val _).1] using hh
    rw [heq, sub_self]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun t ht ↦
    mul_nonneg (sub_nonneg.mpr (hle t ht))
      (Real.sin_pos_of_pos_of_lt_pi (angleDomain_subset_Ioo Θ ((hmem t).mp ht)).1
        (angleDomain_subset_Ioo Θ ((hmem t).mp ht)).2).le)).mp hsum
  apply h
  intro t
  have ht := (hmem t.val).mpr t.property
  have hz := hzero t.val ht
  have hs := Real.sin_pos_of_pos_of_lt_pi (angleDomain_subset_Ioo Θ t.property).1
    (angleDomain_subset_Ioo Θ t.property).2
  have heq := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hs.ne')
  apply (ENNReal.toReal_eq_toReal_iff' (htop t.val) ENNReal.ofReal_ne_top).mp
  simpa [polygonPolylineLengthAt, t.property, ENNReal.toReal_ofReal (hpoly t)] using heq.symm

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
# Polygon / Balancing / Coefficients
-/

@[expose] public section

noncomputable section
namespace MovingSofa

/-- A convex body's frontier on a supporting line is its exposed edge. -/
theorem frontier_inter_supportingLine_eq_exposedEdge (K : ConvexBody Point)
    (t : Real.Angle) :
    frontier (K : Set Point) ∩ normalLine t (supportValue K t) = exposedEdge K t := by
  ext p
  constructor
  · rintro ⟨hp, hline⟩
    exact ⟨K.isCompact.isClosed.closure_subset (frontier_subset_closure hp), hline⟩
  · intro hp
    refine ⟨mem_frontier_of_mem_of_isExteriorNormal K (a := t) hp.1 ?_, hp.2⟩
    intro q hq
    change inner ℝ (q - p) (normalVector t) ≤ 0
    rw [inner_sub_left, show inner ℝ p (normalVector t) = supportValue K t from hp.2]
    exact sub_nonpos.mpr (inner_le_supportValue K hq t)

/-- The surface-area atom is the length of the frontier on its supporting line. -/
theorem hausdorffMeasure_frontier_inter_supportingLine (K : ConvexBody Point)
    (t : Real.Angle) :
    MeasureTheory.Measure.hausdorffMeasure 1
      (frontier (K : Set Point) ∩ normalLine t (supportValue K t)) =
      surfaceAreaMeasure K {t} := by
  rw [frontier_inter_supportingLine_eq_exposedEdge]
  exact (surfaceAreaMeasure_atom_length K t).1.symm

/-- An endpoint cap's lower wall has the surface-area atom of the opposite normal. -/
theorem hausdorffMeasure_frontier_inter_lowerLine_of_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ}
    (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    MeasureTheory.Measure.hausdorffMeasure 1
      (frontier (K.val.val : Set Point) ∩
        normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1)) =
      surfaceAreaMeasure K.val.val {((t + Real.pi : ℝ) : Real.Angle)} := by
  have htSupport : supportValue K.val.val (t : Real.Angle) = 1 := by
    rcases Set.mem_insert_iff.mp ht with ht | ht
    · subst t
      exact K.val.property.2.2.1
    · have ht' := Set.mem_singleton_iff.mp ht
      subst t
      exact K.val.property.2.2.2.1
  have htOpposite :
      supportValue K.val.val ((t + Real.pi : ℝ) : Real.Angle) = 0 := by
    rcases Set.mem_insert_iff.mp ht with ht | ht
    · subst t
      exact K.val.property.2.2.2.2.1
    · have ht' := Set.mem_singleton_iff.mp ht
      subst t
      convert K.val.property.2.2.2.2.2.1 using 1
      ring_nf
  rw [htSupport, sub_self, show normalLine (t : Real.Angle) 0 =
      normalLine ((t + Real.pi : ℝ) : Real.Angle) 0 by
    ext p
    change inner ℝ p (normalVector (t : Real.Angle)) = 0 ↔
      inner ℝ p (normalVector ((t : Real.Angle) + Real.pi)) = 0
    rw [normalVector_add_pi_angle]
    simp]
  rw [← htOpposite]
  exact hausdorffMeasure_frontier_inter_supportingLine K.val.val _

/-- Away from endpoint normals, the niche boundary on the lower wall has polyline length. -/
theorem nicheBoundaryLength_lowerLine_of_not_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (ht : t.val ∉ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    nicheBoundaryLength K
        (normalLine (t.val : Real.Angle)
          (supportValue K.val.val (t.val : Real.Angle) - 1)) =
      polygonCapPolylineLength K t := by
  rw [show polygonCapPolylineLength K t = polygonPolylineLengthAt K t.val by
    simp [polygonPolylineLengthAt, t.property]]
  rcases t.property with htInner | htEndpoint
  · rcases htInner with htDirection | ⟨s, hs, hst⟩
    · have hline := (rotatingHallwayParts_formulas
        (K.val.val : Set Point) (t.val : Real.Angle)).2.2.2.2.1
      rw [← hline]
      exact ((polygonCap_polyline_lengths K).1 t.val htDirection).1
    · have hline := (rotatingHallwayParts_formulas
        (K.val.val : Set Point) (s : Real.Angle)).2.2.2.2.2.2.1
      rw [← hst]
      change nicheBoundaryLength K
          (normalLine ((s + Real.pi / 2 : ℝ) : Real.Angle)
            (supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1)) =
        polygonPolylineLengthAt K (s + Real.pi / 2)
      have hline' :
          (rotatingHallwayParts (K.val.val : Set Point) (s : Real.Angle)).d =
            normalLine ((s + Real.pi / 2 : ℝ) : Real.Angle)
              (supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1) := by
        simpa only [Real.Angle.coe_add] using hline
      rw [← hline']
      exact ((polygonCap_polyline_lengths K).1 s hs).2.2.1
  · exact False.elim (ht htEndpoint)

/-- At an endpoint normal, the lower-wall niche length is the opposite-face length
minus the polyline length. -/
theorem nicheBoundaryLength_lowerLine_of_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    nicheBoundaryLength K
        (normalLine (t.val : Real.Angle)
          (supportValue K.val.val (t.val : Real.Angle) - 1)) =
      (surfaceAreaMeasure K.val.val
        {((t.val + Real.pi : ℝ) : Real.Angle)}).toReal -
        polygonCapPolylineLength K t := by
  have htSupport : supportValue K.val.val (t.val : Real.Angle) = 1 := by
    rcases Set.mem_insert_iff.mp ht with ht | ht
    · rw [ht]
      exact K.val.property.2.2.1
    · rw [Set.mem_singleton_iff.mp ht]
      exact K.val.property.2.2.2.1
  rw [htSupport, sub_self]
  simpa [polygonPolylineLengthAt, t.property] using
    (polygonCap_polyline_lengths K).2 t.val ht |>.1

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
# Polygon / Balancing / Estimate
-/

@[expose] public section

noncomputable section

namespace MovingSofa

private def polygonCapSupportHeight {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    PolygonHeightSpace Θ :=
  fun s ↦ supportValue K.val.val (s.val : Real.Angle)

private theorem raisedPolygonSupport_eq_update {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ) (varepsilon : ℝ) :
    raisedPolygonSupport K t varepsilon =
      Function.update (polygonCapSupportHeight K) t
        (polygonCapSupportHeight K t + varepsilon) := by
  classical
  unfold raisedPolygonSupport polygonCapSupportHeight PolygonHeightSpace
  funext s
  by_cases hst : s = t
  · subst s
    simp
  · simp [Function.update, hst]

private theorem raisedPolygonSupport_zero {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ) : raisedPolygonSupport K t 0 = polygonCapSupportHeight K := by
  unfold raisedPolygonSupport polygonCapSupportHeight PolygonHeightSpace
  funext s
  simp

private theorem update_sub_one {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (t : angleDomain Θ) (varepsilon : ℝ) :
    Function.update (fun s ↦ h s - 1) t (h t - 1 + varepsilon) =
      fun s ↦ Function.update h t (h t + varepsilon) s - 1 := by
  classical
  change angleDomain Θ → ℝ at h
  funext s
  by_cases hst : s = t
  · subst s
    simp
    ring
  · simp [Function.update, hst]

private theorem polygonHeightCap_supportHeight {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    polygonHeightCap (polygonCapSupportHeight K) = K.val.val := by
  let K' : PolygonCapTranslateSpace Θ :=
    ⟨K.val.val, ⟨K, 0, by simp⟩⟩
  change polygonHeightCap
    (fun s ↦ supportValue K.val.val (s.val : Real.Angle)) = K.val.val
  exact polygonHeightCap_of_translate K'

private theorem polygonHeightNiche_supportHeight {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    polygonHeightNiche (polygonCapSupportHeight K) = polygonNiche Θ K.val := by
  change polygonHeightNiche
    (fun s ↦ supportValue K.val.val (s.val : Real.Angle)) = polygonNiche Θ K.val
  exact (polygonHeightNiche_of_cap K).1

private theorem independentWallCap_update_eq_of_not_endpoint {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (t : angleDomain Θ) (varepsilon : ℝ)
    (ht : t.val ∉ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    independentWallCap (Function.update h t (h t + varepsilon)) (fun s ↦ h s - 1) =
      polygonHeightCap (Function.update h t (h t + varepsilon)) := by
  classical
  calc
    independentWallCap (Function.update h t (h t + varepsilon)) (fun s ↦ h s - 1) =
        independentWallCap (Function.update h t (h t + varepsilon))
          (fun s ↦ Function.update h t (h t + varepsilon) s - 1) := by
      ext p
      simp only [independentWallCap, Set.mem_inter_iff, Set.mem_iInter]
      apply and_congr
      · apply forall_congr'
        intro s
        apply forall_congr'
        intro hs
        have hst : (⟨s, Or.inr hs⟩ : angleDomain Θ) ≠ t := by
          intro hst
          apply ht
          have hval : s = t.val := congrArg Subtype.val hst
          rwa [hval] at hs
        simp [polygonHeightValue, Function.update, hst]
      · rfl
    _ = polygonHeightCap (Function.update h t (h t + varepsilon)) :=
      independentWallCap_sub_one (Θ := Θ) _

private theorem independentWallCap_update_both_eq {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (t : angleDomain Θ) (varepsilon : ℝ) :
    independentWallCap (Function.update h t (h t + varepsilon))
        (Function.update (fun s ↦ h s - 1) t (h t - 1 + varepsilon)) =
      polygonHeightCap (Function.update h t (h t + varepsilon)) := by
  rw [update_sub_one]
  exact independentWallCap_sub_one (Θ := Θ) _

private theorem independentWallNiche_update_eq {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (t : angleDomain Θ) (varepsilon : ℝ) :
    independentWallNiche
        (Function.update (fun s ↦ h s - 1) t (h t - 1 + varepsilon)) =
      polygonHeightNiche (Function.update h t (h t + varepsilon)) := by
  rw [update_sub_one]
  exact independentWallNiche_sub_one (Θ := Θ) _

/-- The balancing area estimate when the perturbed normal is not an endpoint. -/
theorem polygonCap_balancing_estimate_of_not_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (ht : t.val ∉ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    ∃ C eta : ℝ, 0 ≤ C ∧ 0 < eta ∧ ∀ varepsilon : ℝ,
      0 ≤ varepsilon → varepsilon ≤ eta →
      |polygonHeightArea (raisedPolygonSupport K t varepsilon) -
        polygonHeightArea (raisedPolygonSupport K t 0) -
        ((surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal -
          polygonCapPolylineLength K t) * varepsilon| ≤ C * varepsilon ^ 2 := by
  classical
  let h := polygonCapSupportHeight K
  obtain ⟨⟨nc, Hc, hHc, hSc⟩, ⟨nn, Hn, hHn, hSn⟩⟩ := polygonCap_niche_simpleNef Θ h
  have htInner : t.val ∈ (Θ.directions : Set ℝ) ∪
      ((fun s : ℝ ↦ s + Real.pi / 2) '' Θ.directions) := by
    rcases t.property with htInner | htEndpoint
    · exact htInner
    · exact False.elim (ht htEndpoint)
  have hcMem :
      (⟨(t.val : Real.Angle), h t, false, false⟩ : PlanarHalfPlaneData) ∈
        Set.range Hc := by
    rw [hHc]
    exact Or.inl ⟨t.val, t.property, by simp [polygonHeightValue]⟩
  obtain ⟨ic, hic⟩ := hcMem
  have hnMem :
      (⟨(t.val : Real.Angle), h t - 1, false, true⟩ : PlanarHalfPlaneData) ∈
        Set.range Hn := by
    rw [hHn]
    exact Or.inl ⟨t.val, htInner, by simp [polygonHeightValue, t.property]⟩
  obtain ⟨in_, hin⟩ := hnMem
  obtain ⟨Cc, etac, hCc, hetac, hcap⟩ :=
    polygonCap_upper_wall_area_variation h Hc hHc hSc.1 ic t hic
  obtain ⟨tn, Cn, etan, htnAngle, hCn, hetan, hniche⟩ :=
    polygonNiche_wall_area_variation h Hn hHn hSn.1 in_
  have hinAngle : (Hn in_).angle = (t.val : Real.Angle) := by rw [hin]
  have htn : tn = t := angleDomain_coe_injective Θ (htnAngle.symm.trans hinAngle)
  subst tn
  have hcapCoeff :
      (MeasureTheory.Measure.hausdorffMeasure 1
        (frontier (polygonHeightCap h) ∩ (Hc ic).boundaryLine)).toReal =
        (surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal := by
    rw [polygonHeightCap_supportHeight K, hic]
    simpa [PlanarHalfPlaneData.boundaryLine, h, polygonCapSupportHeight] using
      congrArg ENNReal.toReal
        (hausdorffMeasure_frontier_inter_supportingLine K.val.val
          (t.val : Real.Angle))
  have hnicheCoeff :
      (MeasureTheory.Measure.hausdorffMeasure 1
        (frontier (polygonHeightNiche h) ∩ (Hn in_).boundaryLine)).toReal =
        polygonCapPolylineLength K t := by
    rw [polygonHeightNiche_supportHeight K, hin]
    simpa [nicheBoundaryLength, PlanarHalfPlaneData.boundaryLine, h,
      polygonCapSupportHeight] using nicheBoundaryLength_lowerLine_of_not_endpoint K t ht
  refine ⟨Cc + Cn, min etac etan, add_nonneg hCc hCn, lt_min hetac hetan, ?_⟩
  intro varepsilon hvarepsilon hvarepsilonEta
  have hvarepsilonC : |varepsilon| ≤ etac := by
    rw [abs_of_nonneg hvarepsilon]
    exact hvarepsilonEta.trans (min_le_left _ _)
  have hvarepsilonN : |varepsilon| ≤ etan := by
    rw [abs_of_nonneg hvarepsilon]
    exact hvarepsilonEta.trans (min_le_right _ _)
  have hc := hcap varepsilon hvarepsilonC
  have hn := hniche varepsilon hvarepsilonN
  rw [hcapCoeff, independentWallCap_update_eq_of_not_endpoint h t varepsilon ht] at hc
  rw [hnicheCoeff, independentWallNiche_update_eq h t varepsilon] at hn
  simp only [hin, Bool.false_eq_true, ite_false, one_mul] at hn
  rw [raisedPolygonSupport_eq_update K t varepsilon, raisedPolygonSupport_zero K t,
    polygonHeightArea]
  change
    |(ClassicalResults.area (polygonHeightCap (Function.update h t (h t + varepsilon))) -
        ClassicalResults.area (polygonHeightNiche (Function.update h t (h t + varepsilon)))) -
      (ClassicalResults.area (polygonHeightCap h) -
        ClassicalResults.area (polygonHeightNiche h)) -
      ((surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal -
        polygonCapPolylineLength K t) * varepsilon| ≤
      (Cc + Cn) * varepsilon ^ 2
  calc
    _ = |(ClassicalResults.area
          (polygonHeightCap (Function.update h t (h t + varepsilon))) -
        ClassicalResults.area (polygonHeightCap h) -
        (surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal * varepsilon) -
      (ClassicalResults.area
          (polygonHeightNiche (Function.update h t (h t + varepsilon))) -
        ClassicalResults.area (polygonHeightNiche h) -
        polygonCapPolylineLength K t * varepsilon)| := by ring_nf
    _ ≤ |ClassicalResults.area
          (polygonHeightCap (Function.update h t (h t + varepsilon))) -
        ClassicalResults.area (polygonHeightCap h) -
        (surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal * varepsilon| +
      |ClassicalResults.area
          (polygonHeightNiche (Function.update h t (h t + varepsilon))) -
        ClassicalResults.area (polygonHeightNiche h) -
        polygonCapPolylineLength K t * varepsilon| := abs_sub _ _
    _ ≤ Cc * varepsilon ^ 2 + Cn * varepsilon ^ 2 := add_le_add hc hn
    _ = (Cc + Cn) * varepsilon ^ 2 := by ring

/-- The balancing area estimate for a simultaneous endpoint-wall displacement. -/
theorem polygonCap_balancing_estimate_of_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    ∃ C eta : ℝ, 0 ≤ C ∧ 0 < eta ∧ ∀ varepsilon : ℝ,
      0 ≤ varepsilon → varepsilon ≤ eta →
      |polygonHeightArea (raisedPolygonSupport K t varepsilon) -
        polygonHeightArea (raisedPolygonSupport K t 0) -
        ((surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal -
          polygonCapPolylineLength K t) * varepsilon| ≤ C * varepsilon ^ 2 := by
  classical
  let h := polygonCapSupportHeight K
  obtain ⟨⟨nc, Hc, hHc, hSc⟩, ⟨nn, Hn, hHn, hSn⟩⟩ := polygonCap_niche_simpleNef Θ h
  have hcuMem :
      (⟨(t.val : Real.Angle), h t, false, false⟩ : PlanarHalfPlaneData) ∈
        Set.range Hc := by
    rw [hHc]
    exact Or.inl ⟨t.val, t.property, by simp [polygonHeightValue]⟩
  obtain ⟨icu, hicu⟩ := hcuMem
  have hclMem :
      (⟨(t.val : Real.Angle), h t - 1, true, false⟩ : PlanarHalfPlaneData) ∈
        Set.range Hc := by
    rw [hHc]
    exact Or.inr ⟨t.val, ht, by simp [polygonHeightValue, t.property]⟩
  obtain ⟨icl, hicl⟩ := hclMem
  have hnMem :
      (⟨(t.val : Real.Angle), h t - 1, true, false⟩ : PlanarHalfPlaneData) ∈
        Set.range Hn := by
    rw [hHn]
    exact Or.inr ⟨t.val, ht, by simp [polygonHeightValue, t.property]⟩
  obtain ⟨in_, hin⟩ := hnMem
  obtain ⟨Cu, etau, hCu, hetau, hcapUpper⟩ :=
    polygonCap_upper_wall_area_variation h Hc hHc hSc.1 icu t hicu
  obtain ⟨Cl, etal, hCl, hetal, hcapLower⟩ :=
    polygonCap_lower_wall_area_variation h Hc hHc hSc.1 icl t hicl
  obtain ⟨tn, Cn, etan, htnAngle, hCn, hetan, hniche⟩ :=
    polygonNiche_wall_area_variation h Hn hHn hSn.1 in_
  have hinAngle : (Hn in_).angle = (t.val : Real.Angle) := by rw [hin]
  have htn : tn = t := angleDomain_coe_injective Θ (htnAngle.symm.trans hinAngle)
  subst tn
  obtain ⟨R, epsilonZero, hR, hepsilonZero, huniform⟩ :=
    polygonPerturbation_uniform_bounds Θ h
  have hupperCoeff :
      (MeasureTheory.Measure.hausdorffMeasure 1
        (frontier (polygonHeightCap h) ∩ (Hc icu).boundaryLine)).toReal =
        (surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal := by
    rw [polygonHeightCap_supportHeight K, hicu]
    simpa [PlanarHalfPlaneData.boundaryLine, h, polygonCapSupportHeight] using
      congrArg ENNReal.toReal
        (hausdorffMeasure_frontier_inter_supportingLine K.val.val
          (t.val : Real.Angle))
  have hlowerCoeff :
      (MeasureTheory.Measure.hausdorffMeasure 1
        (frontier (polygonHeightCap h) ∩ (Hc icl).boundaryLine)).toReal =
        (surfaceAreaMeasure K.val.val
          {((t.val + Real.pi : ℝ) : Real.Angle)}).toReal := by
    rw [polygonHeightCap_supportHeight K, hicl]
    simpa [PlanarHalfPlaneData.boundaryLine, h, polygonCapSupportHeight] using
      congrArg ENNReal.toReal
        (hausdorffMeasure_frontier_inter_lowerLine_of_endpoint K ht)
  have hnicheCoeff :
      (MeasureTheory.Measure.hausdorffMeasure 1
        (frontier (polygonHeightNiche h) ∩ (Hn in_).boundaryLine)).toReal =
        (surfaceAreaMeasure K.val.val
          {((t.val + Real.pi : ℝ) : Real.Angle)}).toReal -
          polygonCapPolylineLength K t := by
    rw [polygonHeightNiche_supportHeight K, hin]
    simpa [nicheBoundaryLength, PlanarHalfPlaneData.boundaryLine, h,
      polygonCapSupportHeight] using nicheBoundaryLength_lowerLine_of_endpoint K t ht
  let eta := min etau (min etal (min etan (min epsilonZero 1)))
  refine ⟨Cu + Cl + Cn, eta, add_nonneg (add_nonneg hCu hCl) hCn,
    lt_min hetau (lt_min hetal (lt_min hetan (lt_min hepsilonZero zero_lt_one))), ?_⟩
  intro varepsilon hvarepsilon hvarepsilonEta
  have hvarepsilonU : |varepsilon| ≤ etau := by
    rw [abs_of_nonneg hvarepsilon]
    exact hvarepsilonEta.trans (by simp [eta])
  have hvarepsilonL : |varepsilon| ≤ etal := by
    rw [abs_of_nonneg hvarepsilon]
    exact hvarepsilonEta.trans (by simp [eta])
  have hvarepsilonN : |varepsilon| ≤ etan := by
    rw [abs_of_nonneg hvarepsilon]
    exact hvarepsilonEta.trans (by simp [eta])
  have hvarepsilonZero : varepsilon ≤ epsilonZero :=
    hvarepsilonEta.trans (by simp [eta])
  have hvarepsilonOne : varepsilon ≤ 1 :=
    hvarepsilonEta.trans (by simp [eta])
  have hu := hcapUpper varepsilon hvarepsilonU
  have hl := hcapLower varepsilon hvarepsilonL
  have hn := hniche varepsilon hvarepsilonN
  rw [hupperCoeff] at hu
  rw [hlowerCoeff] at hl
  rw [hnicheCoeff, independentWallNiche_update_eq h t varepsilon] at hn
  simp [hin] at hn
  have hchangeUpper (s : angleDomain Θ) :
      |Function.update h t (h t + varepsilon) s - h s| ≤ epsilonZero := by
    by_cases hst : s = t
    · subst s
      have hself : Function.update h t (h t + varepsilon) t = h t + varepsilon :=
        Function.update_self t (h t + varepsilon) h
      rw [hself]
      simpa [abs_of_nonneg hvarepsilon] using hvarepsilonZero
    · simp [Function.update, hst, le_of_lt hepsilonZero]
  have hchangeLower (s : angleDomain Θ) :
      |Function.update (fun r ↦ h r - 1) t (h t - 1 + varepsilon) s -
        (h s - 1)| ≤ epsilonZero := by
    by_cases hst : s = t
    · subst s
      have hself :
          Function.update (fun r ↦ h r - 1) t (h t - 1 + varepsilon) t =
            h t - 1 + varepsilon :=
        Function.update_self t (h t - 1 + varepsilon) (fun r ↦ h r - 1)
      rw [hself]
      simpa [abs_of_nonneg hvarepsilon] using hvarepsilonZero
    · simp [Function.update, hst, le_of_lt hepsilonZero]
  have hbound (upper lower : PolygonHeightSpace Θ)
      (hupper : upper = h ∨ upper = Function.update h t (h t + varepsilon))
      (hlower : lower = (fun s ↦ h s - 1) ∨
        lower = Function.update (fun s ↦ h s - 1) t (h t - 1 + varepsilon)) :
      independentWallCap upper lower ⊆ Metric.closedBall 0 R := by
    apply (huniform upper lower ?_ ?_).1
    · rcases hupper with rfl | rfl
      · intro s
        simp [le_of_lt hepsilonZero]
      · exact hchangeUpper
    · rcases hlower with rfl | rfl
      · intro s
        simp [le_of_lt hepsilonZero]
      · exact hchangeLower
  have hadd := independentWallCap_area_update_add h t varepsilon R
    hvarepsilon hvarepsilonOne hbound
  rw [independentWallCap_update_both_eq h t varepsilon,
    independentWallCap_sub_one (Θ := Θ)] at hadd
  rw [raisedPolygonSupport_eq_update K t varepsilon, raisedPolygonSupport_zero K t,
    polygonHeightArea]
  change
    |(ClassicalResults.area (polygonHeightCap (Function.update h t (h t + varepsilon))) -
        ClassicalResults.area (polygonHeightNiche (Function.update h t (h t + varepsilon)))) -
      (ClassicalResults.area (polygonHeightCap h) -
        ClassicalResults.area (polygonHeightNiche h)) -
      ((surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal -
        polygonCapPolylineLength K t) * varepsilon| ≤
      (Cu + Cl + Cn) * varepsilon ^ 2
  let upperResidual :=
    ClassicalResults.area
        (independentWallCap (Function.update h t (h t + varepsilon)) (fun s ↦ h s - 1)) -
      ClassicalResults.area (polygonHeightCap h) -
      (surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal * varepsilon
  let lowerResidual :=
    ClassicalResults.area
        (independentWallCap h
          (Function.update (fun s ↦ h s - 1) t (h t - 1 + varepsilon))) -
      ClassicalResults.area (polygonHeightCap h) +
      (surfaceAreaMeasure K.val.val
        {((t.val + Real.pi : ℝ) : Real.Angle)}).toReal * varepsilon
  let nicheResidual :=
    ClassicalResults.area (polygonHeightNiche (Function.update h t (h t + varepsilon))) -
      ClassicalResults.area (polygonHeightNiche h) +
      ((surfaceAreaMeasure K.val.val
        {((t.val + Real.pi : ℝ) : Real.Angle)}).toReal -
        polygonCapPolylineLength K t) * varepsilon
  have hn' : |nicheResidual| ≤ Cn * varepsilon ^ 2 := by
    dsimp [nicheResidual]
    convert hn using 1
    ring_nf
  have hresidual :
      (ClassicalResults.area (polygonHeightCap (Function.update h t (h t + varepsilon))) -
          ClassicalResults.area
            (polygonHeightNiche (Function.update h t (h t + varepsilon)))) -
        (ClassicalResults.area (polygonHeightCap h) -
          ClassicalResults.area (polygonHeightNiche h)) -
        ((surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal -
          polygonCapPolylineLength K t) * varepsilon =
      upperResidual + lowerResidual - nicheResidual := by
    dsimp [upperResidual, lowerResidual, nicheResidual]
    linarith [hadd]
  rw [hresidual]
  calc
    |upperResidual + lowerResidual - nicheResidual| ≤
        |upperResidual + lowerResidual| + |nicheResidual| := abs_sub _ _
    _ ≤ (|upperResidual| + |lowerResidual|) + |nicheResidual| :=
      add_le_add (abs_add_le _ _) (le_refl _)
    _ ≤ (Cu * varepsilon ^ 2 + Cl * varepsilon ^ 2) + Cn * varepsilon ^ 2 := by
      exact add_le_add (add_le_add hu hl) hn'
    _ = (Cu + Cl + Cn) * varepsilon ^ 2 := by ring

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
# Polygon / Balancing
-/

@[expose] public section

noncomputable section

namespace MovingSofa

private lemma exists_pos_lt_of_quadratic_error {f : ℝ → ℝ} {a C η δ : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hη : 0 < η) (hδ : 0 < δ)
    (herror : ∀ ε, 0 ≤ ε → ε ≤ η → |f ε - f 0 - a * ε| ≤ C * ε ^ 2) :
    ∃ ε, 0 < ε ∧ ε < δ ∧ f 0 < f ε := by
  let ε := min (η / 2) (min (δ / 2) (a / (2 * (C + 1))))
  have hε : 0 < ε := lt_min (half_pos hη)
    (lt_min (half_pos hδ) (div_pos ha (by positivity)))
  have hεη : ε ≤ η := (min_le_left _ _).trans (by linarith)
  have hεδ : ε < δ := (min_le_right _ _).trans_lt
    ((min_le_left _ _).trans_lt (by linarith))
  have hεa : ε ≤ a / (2 * (C + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hprod : ε * (2 * (C + 1)) ≤ a :=
    (le_div_iff₀ (by positivity : 0 < 2 * (C + 1))).mp hεa
  have hsmall : C * ε < a := by nlinarith
  have hquad : C * ε ^ 2 < a * ε := by nlinarith [mul_pos (sub_pos.mpr hsmall) hε]
  have hlower := (abs_le.mp (herror ε hε.le hεη)).1
  exact ⟨ε, hε, hεδ, by linarith⟩

/-- A support-height increment has the balancing first-order area term. -/
theorem polygonCap_balancing_estimate {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ) :
    ∃ C η : ℝ, 0 ≤ C ∧ 0 < η ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ η →
      |polygonHeightArea (raisedPolygonSupport K t ε) -
        polygonHeightArea (raisedPolygonSupport K t 0) -
        ((surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal -
          polygonCapPolylineLength K t) * ε| ≤ C * ε ^ 2 := by
  by_cases ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)
  · exact polygonCap_balancing_estimate_of_endpoint K t ht
  · exact polygonCap_balancing_estimate_of_not_endpoint K t ht

/-- A maximum polygon cap has balanced boundary coefficients. -/
theorem maximumPolygonCap_balanced {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (hK : IsMaximumPolygonCap Θ K) : IsBalancedPolygonCap K := by
  classical
  by_contra hnot
  obtain ⟨t, ht⟩ := polygonCap_not_balanced_positive K hnot
  have hnonneg : 0 ≤ polygonCapPolylineLength K t := by
    unfold polygonCapPolylineLength
    exact Finset.sum_nonneg (fun _ _ ↦ by split_ifs <;> positivity)
  have hfinite : surfaceAreaMeasure K.val.val {(t.val : Real.Angle)} ≠ ⊤ := by
    let := (surfaceAreaMeasure_face_union K.val.val).1
    exact MeasureTheory.measure_ne_top _ _
  have hpos : 0 < surfaceAreaMeasure K.val.val {(t.val : Real.Angle)} :=
    lt_of_le_of_lt zero_le ht
  have hgain : 0 < (surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal -
      polygonCapPolylineLength K t := by
    have hh := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hfinite).mpr ht
    rw [ENNReal.toReal_ofReal hnonneg] at hh
    exact sub_pos.mpr hh
  obtain ⟨C, η, hC, hη, herror⟩ := polygonCap_balancing_estimate K t
  obtain ⟨δ, hδ, hfeasible⟩ := polygonCap_positive_height_increment K t hpos
  obtain ⟨ε, hε, hεδ, harea⟩ := exists_pos_lt_of_quadratic_error hgain hC hη hδ herror
  obtain ⟨K', hK'⟩ := hfeasible ε hε hεδ
  obtain ⟨L, v, htranslate⟩ := K'.property
  have hreduce := polygonHeightArea_le_translateArea (raisedPolygonSupport K t ε) K' hK'.symm
  rw [(polygonTranslateExtensions_eq L v K' htranslate).2] at hreduce
  have hzero : raisedPolygonSupport K t 0 =
      (fun s ↦ supportValue (K.val.val : Set Point) (s.val : Real.Angle)) := by
    funext s
    simp [raisedPolygonSupport]
  rw [hzero, (polygonHeightNiche_of_cap K).2] at harea
  exact (not_lt_of_ge (hK.2 L)) (harea.trans_le hreduce)

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
# Edge normals and contact vertices of a finite half-plane intersection

A convex body presented as a finite intersection of closed half-planes has only finitely many
possible contact points and only finitely many possible proper edge normals. This file records
both facts in the form used by the discrete estimates on polygon caps:

* `exists_active_constraint_of_mem_notMem_interior`: a boundary point activates a constraint;
* `exists_active_constraint_of_forall_notMem_add_smul`: a direction that immediately leaves the
  body activates a constraint increasing along it;
* `properEdgeNormal_eq_constraint_or_add_pi`: a nondegenerate exposed edge has a constraint
  normal, up to half a turn;
* `properEdgeNormal_eq_constraint`: the same, without the antipodal alternative;
* `PolygonCapSpace.properEdgeNormal_mem_allowed_or_antipodal` and
  `PolygonCapSpace.properEdgeNormal_mem_allowed`: the polygon-cap versions;
* `finiteConstraintVertices`: the finite set of transversal constraint-line intersections, which
  contains every singleton exposed edge;
* `PolygonCapSpace.surfaceAreaMeasure_compl_properEdgeNormals_eq_zero`: the surface measure of a
  polygon cap is carried by its proper edge normals.
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- A point of a finite half-plane intersection off its interior lies on an active constraint. -/
theorem exists_active_constraint_of_mem_notMem_interior
    (C : Set (Real.Angle × ℝ)) (hC : C.Finite) (S : Set Point)
    (hS : S = ⋂ c ∈ C, normalHalfPlane c.1 c.2 false false)
    {x : Point} (hxS : x ∈ S) (hxint : x ∉ interior S) :
    ∃ c ∈ C, inner ℝ x (normalVector c.1) = c.2 := by
  by_contra h
  push Not at h
  apply hxint
  rw [hS, hC.interior_biInter]
  simp only [Set.mem_iInter]
  intro c hc
  have hxc : inner ℝ x (normalVector c.1) < c.2 := by
    rw [hS] at hxS
    have hle := Set.mem_iInter.mp (Set.mem_iInter.mp hxS c) hc
    change inner ℝ x (normalVector c.1) ≤ c.2 at hle
    exact lt_of_le_of_ne hle (h c hc)
  have hUopen : IsOpen {p : Point | inner ℝ p (normalVector c.1) < c.2} :=
    isOpen_lt (by fun_prop) continuous_const
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hUopen.mem_nhds hxc)
  intro p hp
  change inner ℝ p (normalVector c.1) < c.2 at hp
  change inner ℝ p (normalVector c.1) ≤ c.2
  exact hp.le

/-- A nondegenerate exposed edge has the normal angle of one of the constraints, up to half a
turn. -/
theorem properEdgeNormal_eq_constraint_or_add_pi
    (K : ConvexBody Point) (C : Set (Real.Angle × ℝ)) (hC : C.Finite)
    (hK : (K : Set Point) = ⋂ c ∈ C, normalHalfPlane c.1 c.2 false false)
    (t : Real.Angle) (ht : (edgeVertices K t).1 ≠ (edgeVertices K t).2) :
    ∃ c ∈ C, t = c.1 ∨ t = c.1 + (Real.pi : Real.Angle) := by
  set p := (edgeVertices K t).1 with hpdef
  set q := (edgeVertices K t).2 with hqdef
  have hp : p ∈ exposedEdge K t := edgeVertices_fst_mem K t
  have hq : q ∈ exposedEdge K t := edgeVertices_snd_mem K t
  have hxedge : midpoint ℝ p q ∈ exposedEdge K t :=
    (convex_exposedEdge K t).segment_subset hp hq (midpoint_mem_segment p q)
  have hxfront : midpoint ℝ p q ∈ frontier (K : Set Point) := by
    rw [← frontier_inter_supportingLine_eq_exposedEdge K t] at hxedge
    exact hxedge.1
  obtain ⟨c, hcC, hcx⟩ := exists_active_constraint_of_mem_notMem_interior
    C hC (K : Set Point) hK hxedge.1 hxfront.2
  refine ⟨c, hcC, ?_⟩
  have hpc : inner ℝ p (normalVector c.1) ≤ c.2 := by
    have hpK : p ∈ (K : Set Point) := hp.1
    rw [hK] at hpK
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hpK c) hcC
  have hqc : inner ℝ q (normalVector c.1) ≤ c.2 := by
    have hqK : q ∈ (K : Set Point) := hq.1
    rw [hK] at hqK
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hqK c) hcC
  rw [midpoint_eq_smul_add, inner_smul_left, inner_add_left] at hcx
  norm_num at hcx
  have hpcEq : inner ℝ p (normalVector c.1) = c.2 := by linarith
  have hqcEq : inner ℝ q (normalVector c.1) = c.2 := by linarith
  have hvt : inner ℝ (p - q) (normalVector t) = 0 := by
    rw [inner_sub_left, hp.2, hq.2, sub_self]
  have hvc : inner ℝ (p - q) (normalVector c.1) = 0 := by
    rw [inner_sub_left, hpcEq, hqcEq, sub_self]
  exact normalVector_eq_or_eq_add_pi_of_orthogonal (sub_ne_zero.mpr ht) hvt hvc

/-- If a direction immediately leaves a finite intersection of closed half-planes at a point of
it, some constraint is active there and increases along that direction. -/
theorem exists_active_constraint_of_forall_notMem_add_smul
    (C : Set (Real.Angle × ℝ)) (hC : C.Finite) (S : Set Point)
    (hS : S = ⋂ c ∈ C, normalHalfPlane c.1 c.2 false false)
    {x w : Point} (hxS : x ∈ S) (hw : ∀ r : ℝ, 0 < r → x + r • w ∉ S) :
    ∃ c ∈ C, inner ℝ x (normalVector c.1) = c.2 ∧ 0 < inner ℝ w (normalVector c.1) := by
  by_contra hcon
  push Not at hcon
  have hmem : ∀ c ∈ C, inner ℝ x (normalVector c.1) ≤ c.2 := by
    intro c hc
    rw [hS] at hxS
    have hle := Set.mem_iInter.mp (Set.mem_iInter.mp hxS c) hc
    change inner ℝ x (normalVector c.1) ≤ c.2 at hle
    exact hle
  have hall : ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0), ∀ c ∈ C,
      inner ℝ (x + r • w) (normalVector c.1) ≤ c.2 := by
    refine hC.eventually_all.mpr ?_
    intro c hc
    by_cases hact : inner ℝ x (normalVector c.1) = c.2
    · have hwc : inner ℝ w (normalVector c.1) ≤ 0 := hcon c hc hact
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [inner_add_left, real_inner_smul_left, hact]
      have hrw : r * inner ℝ w (normalVector c.1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hr) hwc
      linarith
    · have hlt : inner ℝ x (normalVector c.1) < c.2 := lt_of_le_of_ne (hmem c hc) hact
      have hcont : Continuous fun r : ℝ ↦ inner ℝ (x + r • w) (normalVector c.1) := by
        fun_prop
      have h0 : inner ℝ (x + (0 : ℝ) • w) (normalVector c.1) < c.2 := by simpa using hlt
      have hev := (hcont.tendsto 0).eventually (gt_mem_nhds h0)
      exact (hev.filter_mono nhdsWithin_le_nhds).mono fun r hr ↦ hr.le
  obtain ⟨r, hrall, hrpos⟩ := (hall.and self_mem_nhdsWithin).exists
  refine hw r hrpos ?_
  rw [hS]
  refine Set.mem_iInter.2 fun c ↦ Set.mem_iInter.2 fun hc ↦ ?_
  change inner ℝ (x + r • w) (normalVector c.1) ≤ c.2
  exact hrall c hc

/-- The normal of a nondegenerate exposed edge of a finite intersection of closed half-planes is
itself a constraint normal. -/
theorem properEdgeNormal_eq_constraint (K : ConvexBody Point)
    (C : Set (Real.Angle × ℝ)) (hC : C.Finite)
    (hK : (K : Set Point) = ⋂ c ∈ C, normalHalfPlane c.1 c.2 false false)
    (t : Real.Angle) (ht : (edgeVertices K t).1 ≠ (edgeVertices K t).2) :
    ∃ c ∈ C, t = c.1 := by
  set p := (edgeVertices K t).1 with hpdef
  set q := (edgeVertices K t).2 with hqdef
  have hp : p ∈ exposedEdge K t := edgeVertices_fst_mem K t
  have hq : q ∈ exposedEdge K t := edgeVertices_snd_mem K t
  have hx : (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q ∈ exposedEdge K t :=
    (convex_exposedEdge K t) hp hq (by norm_num) (by norm_num) (by norm_num)
  have hout : ∀ r : ℝ, 0 < r →
      (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q + r • normalVector t ∉ (K : Set Point) := by
    intro r hr hmemK
    have hle := inner_le_supportValue K hmemK t
    rw [inner_add_left, real_inner_smul_left, inner_normalVector_self_angle, mul_one,
      hx.2] at hle
    linarith
  obtain ⟨c, hcC, hact, hpos⟩ :=
    exists_active_constraint_of_forall_notMem_add_smul C hC _ hK hx.1 hout
  have hpc : inner ℝ p (normalVector c.1) ≤ c.2 := by
    have hpK : p ∈ (K : Set Point) := hp.1
    rw [hK] at hpK
    have h := Set.mem_iInter.mp (Set.mem_iInter.mp hpK c) hcC
    change inner ℝ p (normalVector c.1) ≤ c.2 at h
    exact h
  have hqc : inner ℝ q (normalVector c.1) ≤ c.2 := by
    have hqK : q ∈ (K : Set Point) := hq.1
    rw [hK] at hqK
    have h := Set.mem_iInter.mp (Set.mem_iInter.mp hqK c) hcC
    change inner ℝ q (normalVector c.1) ≤ c.2 at h
    exact h
  have hmid : inner ℝ ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q) (normalVector c.1) =
      (inner ℝ p (normalVector c.1) + inner ℝ q (normalVector c.1)) / 2 := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring
  rw [hmid] at hact
  have hpceq : inner ℝ p (normalVector c.1) = c.2 := by linarith
  have hqceq : inner ℝ q (normalVector c.1) = c.2 := by linarith
  have hvt : inner ℝ (p - q) (normalVector t) = 0 := by
    rw [inner_sub_left, hp.2, hq.2, sub_self]
  have hvc : inner ℝ (p - q) (normalVector c.1) = 0 := by
    rw [inner_sub_left, hpceq, hqceq, sub_self]
  rcases normalVector_eq_or_eq_add_pi_of_orthogonal (sub_ne_zero.mpr ht) hvt hvc with h | h
  · exact ⟨c, hcC, h⟩
  · exfalso
    rw [h, normalVector_add_pi_angle, inner_neg_left, inner_normalVector_self_angle] at hpos
    linarith

/-- The allowed normal set of a polygon cap is finite. -/
theorem finite_polygonCapNormals (Θ : AngleSet) :
    (((fun r : ℝ ↦ (r : Real.Angle)) '' angleDomain Θ) ∪
      capLowerNormals Θ.angle).Finite := by
  have hdomain : (angleDomain Θ).Finite := by
    unfold angleDomain
    exact ((Θ.directions.finite_toSet.union
      (Θ.directions.finite_toSet.image (fun t ↦ t + Real.pi / 2))).union
        ((Set.finite_singleton (Real.pi / 2)).insert Θ.angle))
  exact (hdomain.image _).union ((Set.finite_singleton _).insert _)

/-- Every nondegenerate exposed edge of a polygon cap has an allowed or antipodal normal. -/
theorem PolygonCapSpace.properEdgeNormal_mem_allowed_or_antipodal
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (t : Real.Angle)
    (ht : (edgeVertices K.val.val t).1 ≠ (edgeVertices K.val.val t).2) :
    t ∈ ((fun r : ℝ ↦ (r : Real.Angle)) '' angleDomain Θ) ∪
        capLowerNormals Θ.angle ∪
      ((fun u : Real.Angle ↦ u + (Real.pi : Real.Angle)) ''
        (((fun r : ℝ ↦ (r : Real.Angle)) '' angleDomain Θ) ∪
          capLowerNormals Θ.angle)) := by
  obtain ⟨C, hC, hCN, hKC⟩ := K.property.finite_constraints (finite_polygonCapNormals Θ)
  obtain ⟨c, hcC, htc | htc⟩ :=
    properEdgeNormal_eq_constraint_or_add_pi K.val.val C hC hKC t ht
  · exact Or.inl (htc ▸ hCN c hcC)
  · exact Or.inr ⟨c.1, hCN c hcC, htc.symm⟩

/-- Every proper edge normal of a polygon cap is an allowed normal. -/
theorem PolygonCapSpace.properEdgeNormal_mem_allowed {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : Real.Angle)
    (ht : (edgeVertices K.val.val t).1 ≠ (edgeVertices K.val.val t).2) :
    t ∈ ((fun r : ℝ ↦ (r : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle := by
  obtain ⟨C, hC, hCN, hKC⟩ := K.property.finite_constraints (finite_polygonCapNormals Θ)
  obtain ⟨c, hcC, htc⟩ := properEdgeNormal_eq_constraint K.val.val C hC hKC t ht
  exact htc ▸ hCN c hcC

/-- The finitely many transversal intersection points of a finite constraint family. -/
def finiteConstraintVertices (C : Set (Real.Angle × ℝ)) : Set Point := by
  classical
  exact ⋃ c ∈ C, ⋃ d ∈ C,
    if c.1 = d.1 ∨ c.1 = d.1 + (Real.pi : Real.Angle) then ∅
    else normalLine c.1 c.2 ∩ normalLine d.1 d.2

/-- A finite constraint family has finitely many transversal intersection points. -/
theorem finite_finiteConstraintVertices (C : Set (Real.Angle × ℝ))
    (hC : C.Finite) : (finiteConstraintVertices C).Finite := by
  classical
  unfold finiteConstraintVertices
  refine hC.biUnion fun c _ ↦ hC.biUnion fun d _ ↦ ?_
  split_ifs with hparallel
  · exact Set.finite_empty
  · apply Set.Subsingleton.finite
    intro p hp q hq
    simp only [Set.mem_inter_iff, normalLine, Set.mem_ofPred_eq] at hp hq
    by_contra hpq
    have hcorth : inner ℝ (p - q) (normalVector c.1) = 0 := by
      rw [inner_sub_left, hp.1, hq.1, sub_self]
    have hdorth : inner ℝ (p - q) (normalVector d.1) = 0 := by
      rw [inner_sub_left, hp.2, hq.2, sub_self]
    exact hparallel (normalVector_eq_or_eq_add_pi_of_orthogonal
      (sub_ne_zero.mpr hpq) hcorth hdorth)

/-- A singleton exposed edge of a finite half-plane intersection is a constraint vertex. -/
theorem singleton_exposedEdge_mem_finiteConstraintVertices
    (C : Set (Real.Angle × ℝ)) (hC : C.Finite) (K : ConvexBody Point)
    (hK : (K : Set Point) = ⋂ c ∈ C, normalHalfPlane c.1 c.2 false false)
    {t : Real.Angle} {p : Point} (hp : exposedEdge K t = {p}) :
    p ∈ finiteConstraintVertices C := by
  classical
  have hpedge : p ∈ exposedEdge K t := by rw [hp]; exact Set.mem_singleton p
  have hpfront : p ∈ frontier (K : Set Point) := by
    rw [← frontier_inter_supportingLine_eq_exposedEdge K t] at hpedge
    exact hpedge.1
  obtain ⟨c, hc, hpc⟩ := exists_active_constraint_of_mem_notMem_interior
    C hC (K : Set Point) hK hpedge.1 hpfront.2
  by_contra hnot
  have hparallel (d : Real.Angle × ℝ) (hd : d ∈ C)
      (hpd : inner ℝ p (normalVector d.1) = d.2) :
      c.1 = d.1 ∨ c.1 = d.1 + (Real.pi : Real.Angle) := by
    by_contra hnon
    apply hnot
    unfold finiteConstraintVertices
    exact Set.mem_iUnion.2 ⟨c, Set.mem_iUnion.2 ⟨hc, Set.mem_iUnion.2 ⟨d,
      Set.mem_iUnion.2 ⟨hd, by simp only [hnon, ↓reduceIte]; exact ⟨hpc, hpd⟩⟩⟩⟩⟩
  have horth : inner ℝ (tangentVector c.1) (normalVector c.1) = 0 := by
    induction c.1 using Real.Angle.induction_on with
    | _ r => rw [real_inner_comm, inner_normalVector_tangentVector]
  have hvne : tangentVector c.1 ≠ 0 := by
    have hvself : inner ℝ (tangentVector c.1) (tangentVector c.1) = 1 := by
      induction c.1 using Real.Angle.induction_on with
      | _ r => exact inner_tangentVector_self r
    intro hv
    simp [hv] at hvself
  have hevent : ∀ᶠ r : ℝ in nhds 0, p + r • tangentVector c.1 ∈ (K : Set Point) := by
    have hall : ∀ᶠ r : ℝ in nhds 0, ∀ d ∈ C,
        inner ℝ (p + r • tangentVector c.1) (normalVector d.1) ≤ d.2 := by
      apply hC.eventually_all.mpr
      intro d hd
      by_cases hpd : inner ℝ p (normalVector d.1) = d.2
      · have hvd : inner ℝ (tangentVector c.1) (normalVector d.1) = 0 := by
          rcases hparallel d hd hpd with heq | heq
          · rwa [← heq]
          · have hnn : normalVector d.1 = -normalVector c.1 := by
              rw [heq, normalVector_add_pi_angle, neg_neg]
            rw [hnn, inner_neg_right, horth, neg_zero]
        exact Filter.Eventually.of_forall fun r ↦ by
          rw [inner_add_left, real_inner_smul_left, hvd, mul_zero, add_zero, hpd]
      · have hple : inner ℝ p (normalVector d.1) ≤ d.2 := by
          have hm := hpedge.1
          rw [hK] at hm
          exact Set.mem_iInter.mp (Set.mem_iInter.mp hm d) hd
        have hlt : inner ℝ p (normalVector d.1) < d.2 := lt_of_le_of_ne hple hpd
        have hcont : Continuous
            (fun r : ℝ ↦ inner ℝ (p + r • tangentVector c.1) (normalVector d.1)) := by
          fun_prop
        have hzero : inner ℝ (p + (0 : ℝ) • tangentVector c.1) (normalVector d.1) < d.2 := by
          simpa using hlt
        filter_upwards [(hcont.tendsto 0).eventually (gt_mem_nhds hzero)] with r hr
        exact hr.le
    filter_upwards [hall] with r hr
    rw [hK]
    exact Set.mem_iInter.2 fun d ↦ Set.mem_iInter.2 fun hd ↦ hr d hd
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hevent
  have hplus : p + (ε / 2) • tangentVector c.1 ∈ (K : Set Point) := hball (by
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity : 0 < ε / 2)]
    linarith)
  have hminus : p + (-(ε / 2)) • tangentVector c.1 ∈ (K : Set Point) := hball (by
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_neg]
    rw [abs_of_pos (by positivity : 0 < ε / 2)]
    linarith)
  have hplusle := inner_le_supportValue K hplus t
  have hminusle := inner_le_supportValue K hminus t
  rw [inner_add_left, real_inner_smul_left, hpedge.2] at hplusle hminusle
  have hvt : inner ℝ (tangentVector c.1) (normalVector t) = 0 := by nlinarith
  have hplusface : p + (ε / 2) • tangentVector c.1 ∈ exposedEdge K t := by
    refine ⟨hplus, ?_⟩
    change inner ℝ (p + (ε / 2) • tangentVector c.1) (normalVector t) = supportValue K t
    rw [inner_add_left, real_inner_smul_left, hvt, mul_zero, add_zero, hpedge.2]
  rw [hp, Set.mem_singleton_iff] at hplusface
  have hzero : (ε / 2) • tangentVector c.1 = 0 :=
    add_left_cancel (show p + (ε / 2) • tangentVector c.1 = p + 0 by simpa using hplusface)
  exact hvne ((smul_eq_zero.mp hzero).resolve_left (ne_of_gt (by positivity)))

/-- The transversal constraint vertices form a one-dimensional null set. -/
theorem finiteConstraintVertices_measure_zero (C : Set (Real.Angle × ℝ))
    (hC : C.Finite) :
    MeasureTheory.Measure.hausdorffMeasure 1 (finiteConstraintVertices C) = 0 := by
  let _ := MeasureTheory.Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  exact (finite_finiteConstraintVertices C hC).measure_zero _

/-- Surface measure of a finite intersection of closed half-planes is carried by its proper
edge normals. -/
theorem surfaceAreaMeasure_compl_properEdgeNormals_eq_zero_of_finite_constraints
    (C : Set (Real.Angle × ℝ)) (hC : C.Finite) (K : ConvexBody Point)
    (hK : (K : Set Point) = ⋂ c ∈ C, normalHalfPlane c.1 c.2 false false) :
    surfaceAreaMeasure K {t | (edgeVertices K t).1 = (edgeVertices K t).2} = 0 := by
  have hN : {t | (edgeVertices K t).1 ≠ (edgeVertices K t).2}.Finite := by
    apply (hC.image Prod.fst).subset
    intro t ht
    obtain ⟨c, hc, heq⟩ := properEdgeNormal_eq_constraint K C hC hK t ht
    exact ⟨c, hc, heq.symm⟩
  apply surfaceAreaMeasure_compl_properEdgeNormals_eq_zero_of_finite_carrier
    K hN (finiteConstraintVertices C) (finiteConstraintVertices_measure_zero C hC)
  intro p hp
  obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hp
  have hsingle : exposedEdge K t = {(edgeVertices K t).1} := by
    rw [exposedEdge_eq_segment_edgeVertices, ht, segment_same]
  have hpeq : p = (edgeVertices K t).1 := by simpa [hsingle] using hp
  exact hpeq ▸ singleton_exposedEdge_mem_finiteConstraintVertices C hC K hK hsingle

/-- Surface measure of a polygon cap is carried by its proper edge normals. -/
theorem PolygonCapSpace.surfaceAreaMeasure_compl_properEdgeNormals_eq_zero
    {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    surfaceAreaMeasure K.val.val
      {t | (edgeVertices K.val.val t).1 = (edgeVertices K.val.val t).2} = 0 := by
  obtain ⟨C, hC, _, hKC⟩ := K.property.finite_constraints (finite_polygonCapNormals Θ)
  exact surfaceAreaMeasure_compl_properEdgeNormals_eq_zero_of_finite_constraints
    C hC K.val.val hKC

end MovingSofa

end

end

end
