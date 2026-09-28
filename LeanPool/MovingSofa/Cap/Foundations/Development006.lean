/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Analysis.Foundations.Development002

public import LeanPool.MovingSofa.Bounds.Foundations.Development002
public import LeanPool.MovingSofa.Bounds.Foundations.Development001
public import LeanPool.MovingSofa.Cap.Foundations.Development005
public import LeanPool.MovingSofa.Cap.Foundations.Development004
public import LeanPool.MovingSofa.Sofa.Foundations.Development001
/-!
# Moving sofa: related mathematical developments

* `Cap.Connectedness`.
* `Cap.MirrorFeatures`.
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
# Cap / Connectedness
-/

@[expose] public section

noncomputable section

namespace MovingSofa

private theorem isOpen_capNiche_subtype {ω : ℝ} (K : CapSpace ω) :
    IsOpen {p : capFan ω | (p : Point) ∈ capNiche K} := by
  let U : Set Point := ⋃ t ∈ Set.Ioo 0 ω, innerQuadrant (K.val : Set Point) t
  have hU : IsOpen U := isOpen_iUnion fun t ↦ isOpen_iUnion fun _ ↦ by
    apply IsOpen.inter
    · exact isOpen_lt (by fun_prop) continuous_const
    · exact isOpen_lt (by fun_prop) continuous_const
  have heq : {p : capFan ω | (p : Point) ∈ capNiche K} =
      Subtype.val ⁻¹' U := by
    ext p
    change ((p : Point) ∈ capNiche K) ↔ (p : Point) ∈ U
    simp only [capNiche, Set.mem_inter_iff, p.property, true_and, U]
  rw [heq]
  exact hU.preimage continuous_subtype_val

private theorem capNiche_disjoint_upperBoundary_of_subset {ω : ℝ} (K : CapSpace ω)
    (hsub : capNiche K ⊆ (K.val : Set Point)) :
    Disjoint (capNiche K) (capUpperBoundary K) := by
  rw [Set.disjoint_left]
  intro p hpN hpδ
  let z : capFan ω := ⟨p, hpN.1⟩
  have hzopen : z ∈ {q : capFan ω | (q : Point) ∈ capNiche K} := hpN
  have hzint : z ∈ interior {q : capFan ω | (q : Point) ∈ (K.val : Set Point)} := by
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (isOpen_capNiche_subtype K |>.mem_nhds hzopen)
      (fun q hq ↦ hsub hq)
  have hzfront : z ∈ frontier {q : capFan ω | (q : Point) ∈ (K.val : Set Point)} := by
    rw [capUpperBoundary_relativeBoundary] at hpδ
    obtain ⟨q, hq, hqp⟩ := hpδ
    have : q = z := Subtype.ext hqp
    simpa [this] using hq
  have hzK : z ∈ {q : capFan ω | (q : Point) ∈ (K.val : Set Point)} := hsub hpN
  exact (mem_frontier_iff_notMem_interior hzK).1 hzfront hzint

private theorem mem_interior_capFan_of_pos {ω : ℝ} {p : Point}
    (hω : 0 < inner ℝ p (normalVector (ω : Real.Angle)))
    (hπ : 0 < inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))) :
    p ∈ interior (capFan ω) := by
  let U := normalHalfPlane (ω : Real.Angle) 0 true true ∩
    normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true true
  have hU : IsOpen U := (isOpen_lt continuous_const (by fun_prop)).inter
    (isOpen_lt continuous_const (by fun_prop))
  apply mem_interior_iff_mem_nhds.mpr
  refine Filter.mem_of_superset (hU.mem_nhds ?_) ?_
  · exact ⟨hω, hπ⟩
  · rintro q ⟨hqω, hqπ⟩
    change 0 < inner ℝ q (normalVector (ω : Real.Angle)) at hqω
    change 0 < inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hqπ
    change 0 ≤ inner ℝ q (normalVector (ω : Real.Angle)) ∧
      0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
    exact ⟨hqω.le, hqπ.le⟩

private theorem innerCorner_mem_interior_capFan_of_mem_capWedge {ω t : ℝ}
    (K : CapSpace ω) (ht : t ∈ Set.Ioo 0 ω) {q : Point} (hq : q ∈ capWedge K t) :
    (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner ∈
      interior (capFan ω) := by
  let z := (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner
  rcases hq with ⟨hqFan, hqQuad⟩
  have hzu : inner ℝ z (normalVector (t : Real.Angle)) =
      supportValue K.val (t : Real.Angle) - 1 := by
    simpa [z, rotatingHallwayParts, hallwayParts] using
      inner_supportingPlacement_normalVector (K.val : Set Point) (t : Real.Angle) (0 : Point)
  have hzv : inner ℝ z (tangentVector (t : Real.Angle)) =
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    simpa [z, rotatingHallwayParts, hallwayParts] using
      inner_supportingPlacement_tangentVector (K.val : Set Point) (t : Real.Angle) (0 : Point)
  change q ∈ supportingPlacement (K.val : Set Point) (t : Real.Angle) ''
    hallwayParts.innerQuadrant at hqQuad
  obtain ⟨a, ha, hqa⟩ := hqQuad
  change a 0 < 0 ∧ a 1 < 0 at ha
  have hqQuad : inner ℝ q (normalVector (t : Real.Angle)) <
      supportValue K.val (t : Real.Angle) - 1 ∧
    inner ℝ q (tangentVector (t : Real.Angle)) <
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    constructor
    · rw [← hqa, inner_supportingPlacement_normalVector]
      linarith [ha.1]
    · rw [← hqa, inner_supportingPlacement_tangentVector]
      change a 1 + supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 < _
      linarith [ha.2]
  let d := q - z
  have hdu : inner ℝ d (normalVector (t : Real.Angle)) < 0 := by
    rw [inner_sub_left]
    linarith [hqQuad.1, hzu]
  have hdv : inner ℝ d (tangentVector (t : Real.Angle)) < 0 := by
    rw [inner_sub_left]
    linarith [hqQuad.2, hzv]
  have hdφ (φ : ℝ) : inner ℝ d (normalVector (φ : Real.Angle)) =
      inner ℝ d (normalVector (t : Real.Angle)) * Real.cos (φ - t) +
        inner ℝ d (tangentVector (t : Real.Angle)) * Real.sin (φ - t) := by
    nth_rewrite 1 [← inner_normalVector_smul_add_inner_tangentVector_smul d (t : Real.Angle)]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_normalVector_normalVector]
    have hc : Real.cos (t - φ) = Real.cos (φ - t) := by
      rw [show t - φ = -(φ - t) by ring, Real.cos_neg]
    rw [hc]
    have hs : inner ℝ (tangentVector (t : Real.Angle))
        (normalVector (φ : Real.Angle)) = Real.sin (φ - t) := by
      simp [normalVector, tangentVector, frame, PiLp.inner_apply, Real.sin_sub]
      ring
    rw [hs]
  have hsint : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [ht.2, K.property.2.1, Real.pi_pos])
  have hcost : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_le K.property.2.1⟩
  have hsinδ : 0 < Real.sin (ω - t) := Real.sin_pos_of_pos_of_lt_pi
    (sub_pos.mpr ht.2) (by linarith [ht.1, K.property.2.1, Real.pi_pos])
  have hcosδ : 0 < Real.cos (ω - t) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [sub_pos.mpr ht.2, Real.pi_pos], by linarith [ht.1, K.property.2.1]⟩
  apply mem_interior_capFan_of_pos
  · change 0 < inner ℝ z (normalVector (ω : Real.Angle))
    have hdω : inner ℝ d (normalVector (ω : Real.Angle)) < 0 := by
      rw [hdφ]
      exact add_neg (mul_neg_of_neg_of_pos hdu hcosδ)
        (mul_neg_of_neg_of_pos hdv hsinδ)
    have hqω : 0 ≤ inner ℝ q (normalVector (ω : Real.Angle)) := hqFan.1
    change inner ℝ (q - z) (normalVector (ω : Real.Angle)) < 0 at hdω
    rw [inner_sub_left] at hdω
    linarith
  · change 0 < inner ℝ z (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
    have hdπ : inner ℝ d (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) < 0 := by
      rw [hdφ, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
      exact add_neg (mul_neg_of_neg_of_pos hdu hsint)
        (mul_neg_of_neg_of_pos hdv hcost)
    have hqπ : 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) := hqFan.2
    change inner ℝ (q - z) (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) < 0 at hdπ
    rw [inner_sub_left] at hdπ
    linarith

private theorem exists_mem_capNiche_not_mem_of_innerCorner {ω t : ℝ}
    (K : CapSpace ω) (ht : t ∈ Set.Ioo 0 ω)
    (hzFan : (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner ∈
      interior (capFan ω))
    (hzK : (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner ∉
      (K.val : Set Point)) :
    ∃ q, q ∈ capNiche K ∧ q ∉ (K.val : Set Point) := by
  let z := (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner
  obtain ⟨ε, hε, hεball⟩ := Metric.isOpen_iff.mp isOpen_interior z hzFan
  obtain ⟨δ, hδ, hδball⟩ := Metric.isOpen_iff.mp K.val.isClosed.isOpen_compl z hzK
  let e := min ε δ / 2
  have he : 0 < e := half_pos (lt_min hε hδ)
  let q := z - e • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)
  have hdist : dist q z = e := by
    simp [q, norm_smul, norm_normalVector_real, abs_of_pos he]
  have hqFan : q ∈ capFan ω := interior_subset (hεball (by
    change dist q z < ε
    rw [hdist]
    dsimp [e]
    linarith [min_le_left ε δ]))
  have hqK : q ∉ (K.val : Set Point) := hδball (by
    change dist q z < δ
    rw [hdist]
    dsimp [e]
    linarith [min_le_right ε δ])
  have hzu : inner ℝ z (normalVector (t : Real.Angle)) =
      supportValue K.val (t : Real.Angle) - 1 := by
    simpa [z, rotatingHallwayParts, hallwayParts] using
      inner_supportingPlacement_normalVector (K.val : Set Point) (t : Real.Angle) (0 : Point)
  have hzv : inner ℝ z (tangentVector (t : Real.Angle)) =
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    simpa [z, rotatingHallwayParts, hallwayParts] using
      inner_supportingPlacement_tangentVector (K.val : Set Point) (t : Real.Angle) (0 : Point)
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [ht.2, K.property.2.1, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_le K.property.2.1⟩
  have hquad : q ∈ innerQuadrant (K.val : Set Point) t := by
    constructor
    · change inner ℝ q (normalVector (t : Real.Angle)) < _
      dsimp [q]
      rw [inner_sub_left, real_inner_smul_left, hzu]
      simp [normalVector, frame, PiLp.inner_apply]
      nlinarith
    · change inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) < _
      rw [show ((t + Real.pi / 2 : ℝ) : Real.Angle) =
        (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
        normalVector_add_pi_div_two]
      dsimp [q]
      rw [inner_sub_left, real_inner_smul_left, hzv]
      simp [normalVector, tangentVector, frame, PiLp.inner_apply]
      nlinarith
  exact ⟨q, ⟨hqFan, Set.mem_iUnion₂.mpr ⟨t, ht, hquad⟩⟩, hqK⟩

private theorem verticalLine_disjoint_cap_diff_niche_of_innerCorner {ω t : ℝ}
    (K : CapSpace ω) (ht : t ∈ Set.Ioo 0 ω)
    (hzFan : (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner ∈
      interior (capFan ω))
    (hzK : (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner ∉
      (K.val : Set Point)) {q : Point}
    (hq : q ∈ (K.val : Set Point) \ capNiche K) :
    q 0 ≠ (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner 0 := by
  let z := (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner
  intro hx
  change q 0 = z 0 at hx
  by_cases hy : z 1 ≤ q 1
  · have hnot : ¬ ∀ u ∈ capUpperAngles ω,
        inner ℝ z (normalVector (u : Real.Angle)) ≤ supportValue K.val (u : Real.Angle) := by
      intro hall
      exact hzK (K.mem_of_mem_capFan_of_le_supportValue (interior_subset hzFan) hall)
    push Not at hnot
    obtain ⟨u, hu, hzu⟩ := hnot
    have huI : u ∈ Set.Icc 0 (ω + Real.pi / 2) := by
      rcases hu with hu | hu
      · exact ⟨hu.1, hu.2.trans (le_add_of_nonneg_right (by positivity))⟩
      · exact ⟨(by positivity : 0 ≤ Real.pi / 2).trans hu.1, hu.2⟩
    have hsin : 0 ≤ Real.sin u := Real.sin_nonneg_of_nonneg_of_le_pi huI.1
      (huI.2.trans (by linarith [K.property.2.1, Real.pi_pos]))
    have hinner : inner ℝ z (normalVector (u : Real.Angle)) ≤
        inner ℝ q (normalVector (u : Real.Angle)) := by
      simp [normalVector, frame, PiLp.inner_apply]
      rw [hx]
      nlinarith [mul_le_mul_of_nonneg_left hy hsin]
    have hqle := inner_le_supportValue K.val hq.1 (u : Real.Angle)
    linarith
  · have hzu : inner ℝ z (normalVector (t : Real.Angle)) =
        supportValue K.val (t : Real.Angle) - 1 := by
      simpa [z, rotatingHallwayParts, hallwayParts] using
        inner_supportingPlacement_normalVector (K.val : Set Point) (t : Real.Angle) (0 : Point)
    have hzv : inner ℝ z (tangentVector (t : Real.Angle)) =
        supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
      simpa [z, rotatingHallwayParts, hallwayParts] using
        inner_supportingPlacement_tangentVector (K.val : Set Point) (t : Real.Angle) (0 : Point)
    have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
      (by linarith [ht.2, K.property.2.1, Real.pi_pos])
    have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_le K.property.2.1⟩
    apply hq.2
    refine ⟨K.subset_capFan hq.1, Set.mem_iUnion₂.mpr ⟨t, ht, ?_⟩⟩
    constructor
    · change inner ℝ q (normalVector (t : Real.Angle)) < _
      simp [normalVector, frame, PiLp.inner_apply] at hzu ⊢
      nlinarith
    · change inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) < _
      rw [show ((t + Real.pi / 2 : ℝ) : Real.Angle) =
        (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
        normalVector_add_pi_div_two]
      simp [tangentVector, frame, PiLp.inner_apply] at hzv ⊢
      nlinarith

private theorem exists_upperBoundary_segment_subset_diff {ω : ℝ} (K : CapSpace ω)
    {p : Point} (hp : p ∈ (K.val : Set Point) \ capNiche K) :
    ∃ q ∈ capUpperBoundary K, segment ℝ p q ⊆ (K.val : Set Point) \ capNiche K := by
  let F : Set Point := (K.val : Set Point) ∩ {q | q 0 = p 0}
  have hFc : IsCompact F := K.val.isCompact.inter_right
    (isClosed_eq (by fun_prop) continuous_const)
  have hpF : p ∈ F := ⟨hp.1, rfl⟩
  obtain ⟨q, hqF, hqmax⟩ := hFc.exists_isMaxOn ⟨p, hpF⟩
    (by fun_prop : Continuous (fun q : Point ↦ q 1)).continuousOn
  have hqK : q ∈ (K.val : Set Point) := hqF.1
  have hqδ : q ∈ capUpperBoundary K := by
    rw [capUpperBoundary_relativeBoundary]
    let z : capFan ω := ⟨q, K.subset_capFan hqK⟩
    have hzK : z ∈ {w : capFan ω | (w : Point) ∈ (K.val : Set Point)} := hqK
    refine ⟨z, (mem_frontier_iff_notMem_interior hzK).2 ?_, rfl⟩
    intro hzint
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hzint
    let r : Point := q + (ε / 2) • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)
    have hrFan : r ∈ capFan ω := by
      constructor
      · change 0 ≤ inner ℝ r (normalVector (ω : Real.Angle))
        dsimp [r]
        rw [inner_add_left, real_inner_smul_left, inner_normalVector_normalVector]
        have hsin : 0 ≤ Real.sin ω := Real.sin_nonneg_of_nonneg_of_le_pi K.property.1.le
          (K.property.2.1.trans (by linarith [Real.pi_pos]))
        have := (K.subset_capFan hqK).1
        change 0 ≤ inner ℝ q (normalVector (ω : Real.Angle)) at this
        rw [Real.cos_pi_div_two_sub]
        positivity
      · change 0 ≤ inner ℝ r (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
        dsimp [r]
        rw [inner_add_left, real_inner_smul_left, inner_normalVector_self]
        have := (K.subset_capFan hqK).2
        change 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at this
        linarith
    have hrball : (⟨r, hrFan⟩ : capFan ω) ∈ Metric.ball z ε := by
      change dist r q < ε
      simp [r, norm_smul, norm_normalVector_real, abs_of_pos hε]
      linarith
    have hrK := interior_subset (hball hrball)
    have hrF : r ∈ F := ⟨hrK, by simpa [r, normalVector, frame] using hqF.2⟩
    have := hqmax hrF
    simp [r, normalVector, frame] at this
    linarith
  refine ⟨q, hqδ, ?_⟩
  intro x hx
  have hxK := K.val.convex.segment_subset hp.1 hqK hx
  refine ⟨hxK, ?_⟩
  intro hxN
  have hxFan := hxN.1
  obtain ⟨u, hu, hxQuad⟩ := Set.mem_iUnion₂.mp hxN.2
  have hxp0 : x 0 = p 0 := by
    rw [segment_eq_image_lineMap] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    simp [AffineMap.lineMap_apply_module]
    rw [hqF.2]
    ring
  have hpx1 : p 1 ≤ x 1 := by
    rw [segment_eq_image_lineMap] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    have hpq := hqmax hpF
    simp [AffineMap.lineMap_apply_module]
    nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hpq)]
  apply hp.2
  refine ⟨K.subset_capFan hp.1, Set.mem_iUnion₂.mpr ⟨u, hu, ?_⟩⟩
  rcases hxQuad with ⟨hxU, hxV⟩
  constructor
  · change inner ℝ p (normalVector (u : Real.Angle)) < _
    change inner ℝ x (normalVector (u : Real.Angle)) < _ at hxU
    have hs : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu.1
      (by linarith [hu.2, K.property.2.1, Real.pi_pos])
    simp [normalVector, frame, PiLp.inner_apply] at hxU ⊢
    rw [hxp0] at hxU
    nlinarith [mul_le_mul_of_nonneg_left hpx1 hs.le]
  · change inner ℝ p (normalVector ((u + Real.pi / 2 : ℝ) : Real.Angle)) < _
    change inner ℝ x (normalVector ((u + Real.pi / 2 : ℝ) : Real.Angle)) < _ at hxV
    have hc : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, hu.1], hu.2.trans_le K.property.2.1⟩
    rw [show ((u + Real.pi / 2 : ℝ) : Real.Angle) =
      (u : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
      normalVector_add_pi_div_two] at hxV ⊢
    simp [tangentVector, frame, PiLp.inner_apply] at hxV ⊢
    rw [hxp0] at hxV
    nlinarith [mul_le_mul_of_nonneg_left hpx1 hc.le]

theorem cap_niche_connected_iff {ω : ℝ} (K : CapSpace ω) :
    (capNiche K ⊆ (K.val : Set Point) ↔
      capNiche K ⊆ (K.val : Set Point) \ capUpperBoundary K) ∧
    (capNiche K ⊆ (K.val : Set Point) \ capUpperBoundary K ↔
      ∀ t ∈ Set.Ioo 0 ω,
        (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner ∉
          interior (capFan ω) ∨
        (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner ∈
          (K.val : Set Point)) ∧
    ((∀ t ∈ Set.Ioo 0 ω,
        (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner ∉
          interior (capFan ω) ∨
        (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner ∈
          (K.val : Set Point)) ↔
      IsConnected ((K.val : Set Point) \ capNiche K)) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro hsub p hp
      refine ⟨hsub hp, ?_⟩
      exact fun hpδ ↦
        Set.disjoint_left.mp (capNiche_disjoint_upperBoundary_of_subset K hsub) hp hpδ
    · intro hsub p hp
      exact (hsub hp).1
  · constructor
    · intro hsub t ht
      by_cases hzFan : (rotatingHallwayParts (K.val : Set Point)
          (t : Real.Angle)).innerCorner ∈ interior (capFan ω)
      · right
        by_contra hzK
        obtain ⟨q, hqN, hqK⟩ :=
          exists_mem_capNiche_not_mem_of_innerCorner K ht hzFan hzK
        exact hqK (hsub hqN).1
      · exact Or.inl hzFan
    · intro hcorner p hp
      have hpFan := hp.1
      obtain ⟨t, ht, hpQuad⟩ := Set.mem_iUnion₂.mp hp.2
      have hpWedge : p ∈ capWedge K t := ⟨hpFan, by
        change p ∈ innerQuadrant (K.val : Set Point) t at hpQuad
        have hf := rotatingHallwayParts_formulas (K.val : Set Point) (t : Real.Angle)
        rw [hf.2.2.2.2.2.2.2.2]
        exact hpQuad⟩
      rcases hcorner t ht with hzout | hzK
      · exact False.elim (hzout (innerCorner_mem_interior_capFan_of_mem_capWedge K ht hpWedge))
      · have hpK := capWedge_subset_of_innerCorner_mem K t ht hzK hpWedge
        refine ⟨hpK, ?_⟩
        exact fun hpδ ↦ Set.disjoint_left.mp
          (capNiche_disjoint_upperBoundary_of_subset K fun q hq ↦ by
            have hqFan := hq.1
            obtain ⟨u, hu, hqQuad⟩ := Set.mem_iUnion₂.mp hq.2
            have hqWedge : q ∈ capWedge K u := ⟨hqFan, by
              have hf := rotatingHallwayParts_formulas (K.val : Set Point) (u : Real.Angle)
              rw [hf.2.2.2.2.2.2.2.2]
              exact hqQuad⟩
            rcases hcorner u hu with hzout | hzmem
            · exact False.elim
                (hzout (innerCorner_mem_interior_capFan_of_mem_capWedge K hu hqWedge))
            · exact capWedge_subset_of_innerCorner_mem K u hu hzmem hqWedge) hp hpδ
  · constructor
    · intro hcorner
      have hsub : capNiche K ⊆ (K.val : Set Point) := by
        intro p hp
        have hpFan := hp.1
        obtain ⟨t, ht, hpQuad⟩ := Set.mem_iUnion₂.mp hp.2
        have hpWedge : p ∈ capWedge K t := ⟨hpFan, by
          have hf := rotatingHallwayParts_formulas (K.val : Set Point) (t : Real.Angle)
          rw [hf.2.2.2.2.2.2.2.2]
          exact hpQuad⟩
        rcases hcorner t ht with hzout | hzmem
        · exact False.elim
            (hzout (innerCorner_mem_interior_capFan_of_mem_capWedge K ht hpWedge))
        · exact capWedge_subset_of_innerCorner_mem K t ht hzmem hpWedge
      have hδS : capUpperBoundary K ⊆ (K.val : Set Point) \ capNiche K := by
        intro q hq
        have hqK : q ∈ (K.val : Set Point) := by
          obtain ⟨t, ht, hqedge⟩ := Set.mem_iUnion₂.mp hq
          exact hqedge.1
        exact ⟨hqK, fun hqN ↦
          Set.disjoint_left.mp (capNiche_disjoint_upperBoundary_of_subset K hsub) hqN hq⟩
      obtain ⟨l, r, hlK, -, hl, -⟩ := exists_horizontal_extrema K.val
      have hlS : l ∈ (K.val : Set Point) \ capNiche K := ⟨hlK, fun hlN ↦ by
        have := (capNiche_subset_rectangle K hlN).1
        linarith⟩
      obtain ⟨q₀, hq₀δ, hseg₀⟩ := exists_upperBoundary_segment_subset_diff K hlS
      let S : Set Point := (K.val : Set Point) \ capNiche K
      let f : S → Point := fun p ↦ Classical.choose
        (exists_upperBoundary_segment_subset_diff K p.property)
      have hfδ (p : S) : f p ∈ capUpperBoundary K :=
        (Classical.choose_spec (exists_upperBoundary_segment_subset_diff K p.property)).1
      have hfseg (p : S) : segment ℝ (p : Point) (f p) ⊆ S :=
        (Classical.choose_spec (exists_upperBoundary_segment_subset_diff K p.property)).2
      let A : S → Set Point := fun p ↦ capUpperBoundary K ∪ segment ℝ (p : Point) (f p)
      have hA (p : S) : IsPreconnected (A p) := by
        apply IsPreconnected.union' ⟨f p, hfδ p, right_mem_segment ℝ _ _⟩
        · exact (capUpperBoundary_connected K).isPreconnected
        · exact (convex_segment (𝕜 := ℝ) (p : Point) (f p)).isPreconnected
      have hcommon : (⋂ p, A p).Nonempty := by
        refine ⟨q₀, Set.mem_iInter.mpr fun p ↦ ?_⟩
        exact Or.inl hq₀δ
      have hunion : (⋃ p, A p) = S := by
        apply Set.Subset.antisymm
        · intro x hx
          obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hx
          rcases hxp with hxδ | hxseg
          · exact hδS hxδ
          · exact hfseg p hxseg
        · intro x hx
          let p : S := ⟨x, hx⟩
          exact Set.mem_iUnion.mpr ⟨p, Or.inr (left_mem_segment ℝ _ _)⟩
      refine ⟨⟨l, hlS⟩, ?_⟩
      change IsPreconnected S
      rw [← hunion]
      exact isPreconnected_iUnion hcommon hA
    · intro hconn t ht
      by_cases hzFan : (rotatingHallwayParts (K.val : Set Point)
          (t : Real.Angle)).innerCorner ∈ interior (capFan ω)
      · right
        by_contra hzK
        let z := (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner
        obtain ⟨l, r, hlK, hrK, hl, hr⟩ := exists_horizontal_extrema K.val
        have hlS : l ∈ (K.val : Set Point) \ capNiche K := ⟨hlK, fun hlN ↦ by
          have := (capNiche_subset_rectangle K hlN).1
          linarith⟩
        have hrS : r ∈ (K.val : Set Point) \ capNiche K := ⟨hrK, fun hrN ↦ by
          have := (capNiche_subset_rectangle K hrN).2.1
          linarith⟩
        have hzy : 0 < z 1 := by
          by_contra hn
          obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hzFan
          let q := z - (ε / 2) • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)
          have hq := interior_subset (hball (by
            change dist q z < ε
            simp [q, norm_smul, norm_normalVector_real, abs_of_pos hε]
            linarith))
          have := hq.2
          change 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at this
          simp [q, normalVector, frame, PiLp.inner_apply] at this
          linarith
        have hzu : inner ℝ z (normalVector (t : Real.Angle)) =
            supportValue K.val (t : Real.Angle) - 1 := by
          simpa [z, rotatingHallwayParts, hallwayParts] using
            inner_supportingPlacement_normalVector (K.val : Set Point)
              (t : Real.Angle) (0 : Point)
        have hzv : inner ℝ z (tangentVector (t : Real.Angle)) =
            supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
          simpa [z, rotatingHallwayParts, hallwayParts] using
            inner_supportingPlacement_tangentVector (K.val : Set Point)
              (t : Real.Angle) (0 : Point)
        have hb := K.supportValue_horizontal_bounds ht
        have hb₁ := hb.1
        have hb₂ := hb.2
        change supportValue K.val ((t : Real.Angle) +
          ((Real.pi / 2 : ℝ) : Real.Angle)) ≤
            -Real.sin t * horizontalMin K.val + Real.cos t at hb₂
        have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
          (by linarith [ht.2, K.property.2.1, Real.pi_pos])
        have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
          ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_le K.property.2.1⟩
        have hs1 : Real.sin t ≤ 1 := Real.sin_le_one t
        have hc1 : Real.cos t ≤ 1 := Real.cos_le_one t
        have hzlr : l 0 < z 0 ∧ z 0 < r 0 := by
          change inner ℝ z (tangentVector (t : Real.Angle)) =
            supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 at hzv
          simp [normalVector, tangentVector, frame, PiLp.inner_apply] at hzu hzv
          rw [hl, hr]
          constructor
          · nlinarith [hb₂, mul_pos hc hzy, sub_nonneg.mpr hc1]
          · nlinarith [hb₁, mul_pos hs hzy, sub_nonneg.mpr hs1]
        obtain ⟨q, hqS, hqx⟩ := hconn.isPreconnected.intermediate_value hlS hrS
          (by fun_prop : ContinuousOn (fun p : Point ↦ p 0) _)
          ⟨hzlr.1.le, hzlr.2.le⟩
        exact verticalLine_disjoint_cap_diff_niche_of_innerCorner K ht hzFan hzK hqS hqx
      · exact Or.inl hzFan

private theorem exists_line_meeting_of_support_bounds {s : Set Point} {ω : ℝ}
    (hs : IsCompact s) (hc : IsConnected s) (hω : ω ≤ Real.pi / 2) (p : Point)
    (hp0 : inner ℝ p (normalVector (0 : Real.Angle)) ≤ supportValue s 0)
    (hpω : inner ℝ p (tangentVector (ω : Real.Angle)) ≤
      supportValue s ((ω + Real.pi / 2 : ℝ) : Real.Angle)) :
    ∃ q ∈ s, ∃ θ ∈ Set.Icc ω (Real.pi / 2),
      inner ℝ (q - p) (tangentVector (θ : Real.Angle)) = 0 := by
  obtain ⟨q₀, hq₀, he₀, _⟩ := hs.exists_sSup_image_eq_and_ge
    (f := fun q : Point ↦ inner ℝ q (normalVector (0 : Real.Angle))) hc.nonempty
    (continuous_id.inner continuous_const).continuousOn
  obtain ⟨qω, hqω, heω, _⟩ := hs.exists_sSup_image_eq_and_ge
    (f := fun q : Point ↦ inner ℝ q (tangentVector (ω : Real.Angle))) hc.nonempty
    (continuous_id.inner continuous_const).continuousOn
  have hn : normalVector ((ω + Real.pi / 2 : ℝ) : Real.Angle) =
      tangentVector (ω : Real.Angle) := by
    rw [Real.Angle.coe_add, normalVector_add_pi_div_two]
  have hzero : tangentVector ((Real.pi / 2 : ℝ) : Real.Angle) =
      -normalVector (0 : Real.Angle) := by
    simpa using tangentVector_add_pi_div_two 0
  have hpω' : inner ℝ p (tangentVector (ω : Real.Angle)) ≤
      inner ℝ qω (tangentVector (ω : Real.Angle)) := by
    simpa only [supportValue, hn, heω] using hpω
  have hp0' : inner ℝ p (normalVector (0 : Real.Angle)) ≤
      inner ℝ q₀ (normalVector (0 : Real.Angle)) := by
    simpa only [supportValue, he₀] using hp0
  let f : Point × ℝ → ℝ := fun z ↦ inner ℝ (z.1 - p) (tangentVector (z.2 : Real.Angle))
  have hv : Continuous (fun θ : ℝ ↦ tangentVector (θ : Real.Angle)) := by
    have h := continuous_normalVector_real.comp (continuous_id.add continuous_const
      : Continuous (fun θ : ℝ ↦ θ + Real.pi / 2))
    simpa only [Function.comp_def, Pi.add_apply, id_eq, Real.Angle.coe_add,
      normalVector_add_pi_div_two] using h
  have hf : Continuous f := (continuous_fst.sub continuous_const).inner
    (hv.comp continuous_snd)
  have hl : f (q₀, Real.pi / 2) ≤ 0 := by
    change inner ℝ (q₀ - p) (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤ 0
    rw [hzero, inner_neg_right, inner_sub_left]
    linarith
  have hr : 0 ≤ f (qω, ω) := by
    change 0 ≤ inner ℝ (qω - p) (tangentVector (ω : Real.Angle))
    rw [inner_sub_left]
    linarith
  obtain ⟨⟨q, θ⟩, hmem, he⟩ := (hc.isPreconnected.prod isPreconnected_Icc).intermediate_value
    (f := f) ⟨hq₀, hω, le_rfl⟩ ⟨hqω, le_rfl, hω⟩ hf.continuousOn ⟨hl, hr⟩
  exact ⟨q, hmem.1, θ, hmem.2, he⟩

private theorem mem_supportingHallway_iff_coordinates (s : Set Point) (t : Real.Angle)
    (p : Point) :
    p ∈ supportingHallway s t ↔
      inner ℝ p (normalVector t) ≤ supportValue s t ∧
      inner ℝ p (tangentVector t) ≤ supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) ∧
      (supportValue s t - 1 ≤ inner ℝ p (normalVector t) ∨
        supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1 ≤
          inner ℝ p (tangentVector t)) := by
  obtain ⟨h, _, _, _, _, _, _, ho, hi⟩ := rotatingHallwayParts_formulas s t
  rw [h, ho, hi]
  simp only [Set.mem_sdiff, Set.mem_inter_iff, normalHalfPlane, Set.mem_ofPred_eq,
    Bool.false_eq_true, ↓reduceIte, normalVector_add_pi_div_two]
  simp only [not_and_or, not_lt, and_assoc]

private theorem segment_subset_supportingHallway_of_projections_le {s : Set Point}
    {t : Real.Angle} {p q : Point} (hp : p ∈ supportingHallway s t)
    (hq : q ∈ supportingHallway s t)
    (hn : inner ℝ p (normalVector t) ≤ inner ℝ q (normalVector t))
    (hv : inner ℝ p (tangentVector t) ≤ inner ℝ q (tangentVector t)) :
    segment ℝ p q ⊆ supportingHallway s t := by
  rw [mem_supportingHallway_iff_coordinates] at hp hq
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  rw [mem_supportingHallway_iff_coordinates]
  simp only [inner_add_left, real_inner_smul_left]
  have weighted_le (x y m : ℝ) (hx : x ≤ m) (hy : y ≤ m) : a * x + b * y ≤ m := by
    calc
      a * x + b * y ≤ a * m + b * m :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
      _ = m := by rw [← add_mul, hab, one_mul]
  have le_weighted (x y m : ℝ) (hx : m ≤ x) (hy : m ≤ y) : m ≤ a * x + b * y := by
    calc
      m = a * m + b * m := by rw [← add_mul, hab, one_mul]
      _ ≤ a * x + b * y :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
  refine ⟨weighted_le _ _ _ hp.1 hq.1, weighted_le _ _ _ hp.2.1 hq.2.1, ?_⟩
  rcases hp.2.2 with hn' | hv'
  · exact Or.inl (le_weighted _ _ _ hn' (hn'.trans hn))
  · exact Or.inr (le_weighted _ _ _ hv' (hv'.trans hv))

private theorem convex_stripParallelogram (ω : ℝ) : Convex ℝ (stripParallelogram ω).1 := by
  intro p hp q hq a b ha hb hab
  rw [mem_stripParallelogram_iff] at hp hq ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, inner_add_left,
    real_inner_smul_left]
  exact ⟨convex_Icc (0 : ℝ) 1 hp.1 hq.1 ha hb hab, convex_Icc (0 : ℝ) 1 hp.2 hq.2 ha hb hab⟩

private theorem segment_subset_supportingHallway_of_tangent_eq_zero {s : Set Point}
    {t θ : ℝ} {p q : Point} (hp : p ∈ supportingHallway s (t : Real.Angle))
    (hq : q ∈ supportingHallway s (t : Real.Angle))
    (hθ : θ - t ∈ Set.Icc 0 (Real.pi / 2))
    (hline : inner ℝ (q - p) (tangentVector (θ : Real.Angle)) = 0) :
    segment ℝ p q ⊆ supportingHallway s (t : Real.Angle) := by
  let c := inner ℝ (q - p) (normalVector (θ : Real.Angle))
  have hdiff : q - p = c • normalVector (θ : Real.Angle) := by
    have h := inner_normalVector_smul_add_inner_tangentVector_smul (q - p) (θ : Real.Angle)
    simpa only [hline, zero_smul, add_zero] using h.symm
  have hcos : 0 ≤ Real.cos (θ - t) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have hsin : 0 ≤ Real.sin (θ - t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [Real.pi_pos, hθ.2])
  have hn : inner ℝ q (normalVector (t : Real.Angle)) -
      inner ℝ p (normalVector (t : Real.Angle)) = c * Real.cos (θ - t) := by
    rw [← inner_sub_left, hdiff, real_inner_smul_left, inner_normalVector_normalVector]
  have hv : inner ℝ q (tangentVector (t : Real.Angle)) -
      inner ℝ p (tangentVector (t : Real.Angle)) = c * Real.sin (θ - t) := by
    rw [← inner_sub_left, hdiff, real_inner_smul_left]
    congr 1
    simp [normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
      Real.sin_sub]
    ring
  by_cases hc : 0 ≤ c
  · apply segment_subset_supportingHallway_of_projections_le hp hq
    · linarith [mul_nonneg hc hcos]
    · linarith [mul_nonneg hc hsin]
  · rw [segment_symm]
    apply segment_subset_supportingHallway_of_projections_le hq hp
    · linarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) hcos]
    · linarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) hsin]

theorem standardPosition_monotonization_connected (s : Set Point) (ω : ℝ)
    (hs : IsStandardPosition s ω) : IsConnected (monotonization s ω) := by
  have hc : IsConnected s := by
    obtain ⟨m, hm, _⟩ := hs.2.1
    exact hm.1
  have hsub := (standardPosition_subset_cap s ω hs).1
  obtain ⟨q₀, hq₀⟩ := hc.nonempty
  refine ⟨hc.nonempty.mono hsub, isPreconnected_of_forall q₀ ?_⟩
  intro p hp
  have hpH (t : ℝ) (ht : t ∈ Set.Icc 0 ω) :
      p ∈ supportingHallway s (t : Real.Angle) :=
    Set.mem_iInter.1 (Set.mem_iInter.1 hp.2 t) ht
  have hp0 := (mem_supportingHallway_iff_coordinates s 0 p).mp
    (hpH 0 ⟨le_rfl, hs.2.2.1.le⟩)
  have hpω := (mem_supportingHallway_iff_coordinates s (ω : Real.Angle) p).mp
    (hpH ω ⟨hs.2.2.1.le, le_rfl⟩)
  obtain ⟨q, hqs, θ, hθ, hline⟩ := exists_line_meeting_of_support_bounds hs.1 hc
    hs.2.2.2.1 p hp0.1 (by simpa only [Real.Angle.coe_add] using hpω.2.1)
  have hq := hsub hqs
  have hseg : segment ℝ p q ⊆ monotonization s ω := by
    intro z hz
    refine ⟨(convex_stripParallelogram ω).segment_subset hp.1 hq.1 hz,
      Set.mem_iInter.2 fun t ↦ Set.mem_iInter.2 fun ht ↦ ?_⟩
    apply segment_subset_supportingHallway_of_tangent_eq_zero (hpH t ht)
      (Set.mem_iInter.1 (Set.mem_iInter.1 hq.2 t) ht) _ hline hz
    exact ⟨by linarith [hθ.1, ht.2], by linarith [hθ.2, ht.1]⟩
  refine ⟨s ∪ segment ℝ p q, Set.union_subset hsub hseg, Or.inl hq₀,
    Or.inr (left_mem_segment ℝ p q), ?_⟩
  exact IsPreconnected.union q hqs (right_mem_segment ℝ p q) hc.isPreconnected
    (convex_segment p q).isPreconnected

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
# Cap / Mirror Features
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

private theorem mirrorReflection_eq_capReflection_m6ef9701 (ω : ℝ)
    (hω0 : 0 < ω) (hωle : ω ≤ Real.pi / 2) :
    mirrorReflection ω = capReflection ω := by
  change stripTopReflection ω = capReflection ω
  exact stripTopReflection_eq_capReflection ω hω0 hωle

private theorem capReflection_rotationMap (ω s : ℝ) (p : Point) :
    capReflection ω (rotationMap (s : Real.Angle) p) =
      rotationMap ((ω - s : ℝ) : Real.Angle) (coordinateSwap p) := by
  have hang : (ω : Real.Angle) - (s : Real.Angle) =
      ((ω - s : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_sub]
  ext i
  fin_cases i
  · change capReflection ω (rotationMap (s : Real.Angle) p) 0 =
      rotationMap ((ω - s : ℝ) : Real.Angle) (coordinateSwap p) 0
    rw [capReflection_apply_zero]
    rw [← hang]
    simp [rotationMap, Orientation.rotation_apply, rightAngleRotation_apply,
      coordinateSwap]
    rw [hang, Real.Angle.sin_coe, Real.Angle.cos_coe, Real.sin_sub, Real.cos_sub]
    ring
  · change capReflection ω (rotationMap (s : Real.Angle) p) 1 =
      rotationMap ((ω - s : ℝ) : Real.Angle) (coordinateSwap p) 1
    rw [capReflection_apply_one]
    rw [← hang]
    simp [rotationMap, Orientation.rotation_apply, rightAngleRotation_apply,
      coordinateSwap]
    rw [hang, Real.Angle.sin_coe, Real.Angle.cos_coe, Real.sin_sub, Real.cos_sub]
    ring

private theorem capReflection_normal_at_complement (ω t : ℝ) :
    capReflection ω (normalVector ((ω - t : ℝ) : Real.Angle)) =
      tangentVector (t : Real.Angle) := by
  rw [capReflection_normalVector]
  have hang : ω + Real.pi / 2 - (ω - t) = t + Real.pi / 2 := by ring
  rw [hang]
  ext i
  fin_cases i <;> simp [normalVector, tangentVector, frame,
    Real.Angle.sin_add_pi_div_two, Real.Angle.cos_add_pi_div_two]

private theorem capReflection_tangent_at_complement (ω t : ℝ) :
    capReflection ω (tangentVector ((ω - t : ℝ) : Real.Angle)) =
      normalVector (t : Real.Angle) := by
  rw [capReflection_tangentVector]
  have hang : ω + Real.pi / 2 - (ω - t) = t + Real.pi / 2 := by ring
  rw [hang]
  ext i
  fin_cases i <;> simp [normalVector, tangentVector, frame,
    Real.Angle.sin_add_pi_div_two, Real.Angle.cos_add_pi_div_two]

private theorem supportValue_reflected_at (ω t : ℝ) (K : ConvexBody Point) :
    supportValue (reflectedBody ω K) (t : Real.Angle) =
      supportValue K ((ω - t + Real.pi / 2 : ℝ) : Real.Angle) := by
  rw [supportValue_reflectedBody, reflectedAngle_coe]
  congr 2
  ring

private theorem supportValue_reflected_at_add_pi_div_two (ω t : ℝ)
    (K : ConvexBody Point) :
    supportValue (reflectedBody ω K) ((t + Real.pi / 2 : ℝ) : Real.Angle) =
      supportValue K ((ω - t : ℝ) : Real.Angle) := by
  rw [supportValue_reflectedBody, reflectedAngle_coe]
  congr 2
  ring

private theorem supportingPlacement_reflection (ω t : ℝ)
    (K : ConvexBody Point) (q : Point) :
    supportingPlacement (reflectedBody ω K) (t : Real.Angle) (coordinateSwap q) =
      capReflection ω (supportingPlacement K ((ω - t : ℝ) : Real.Angle) q) := by
  unfold supportingPlacement
  rw [map_add, map_add, map_smul, map_smul,
    capReflection_rotationMap]
  have hrot : ω - (ω - t) = t := by ring
  have htadd : (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) =
      ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_add]
  have hsadd : ((ω - t : ℝ) : Real.Angle) +
      ((Real.pi / 2 : ℝ) : Real.Angle) =
      ((ω - t + Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_add]
  rw [hrot, supportValue_reflected_at,
    htadd, supportValue_reflected_at_add_pi_div_two, hsadd,
    capReflection_normal_at_complement,
    capReflection_tangent_at_complement]
  module

private theorem coordinateSwap_involutive (p : Point) :
    coordinateSwap (coordinateSwap p) = p := by
  ext i
  fin_cases i <;> simp [coordinateSwap]

private theorem coordinateSwap_image_hallway :
    coordinateSwap '' hallway = hallway := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with ⟨a, b, h, rfl⟩ | ⟨a, b, h, rfl⟩
    · exact Or.inr ⟨b, a, ⟨h.2.1, h.2.2, h.1⟩, by
        ext i
        fin_cases i <;> simp [coordinateSwap]⟩
    · exact Or.inl ⟨b, a, ⟨h.2.2, h.1, h.2.1⟩, by
        ext i
        fin_cases i <;> simp [coordinateSwap]⟩
  · intro hp
    refine ⟨coordinateSwap p, ?_, coordinateSwap_involutive p⟩
    rcases hp with ⟨a, b, h, rfl⟩ | ⟨a, b, h, rfl⟩
    · exact Or.inr ⟨b, a, ⟨h.2.1, h.2.2, h.1⟩, by
        ext i
        fin_cases i <;> simp [coordinateSwap]⟩
    · exact Or.inl ⟨b, a, ⟨h.2.2, h.1, h.2.1⟩, by
        ext i
        fin_cases i <;> simp [coordinateSwap]⟩

private theorem coordinateSwap_image_eq_preimage (s : Set Point) :
    coordinateSwap '' s = coordinateSwap ⁻¹' s := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change coordinateSwap (coordinateSwap q) ∈ s
    rwa [coordinateSwap_involutive]
  · intro hp
    exact ⟨coordinateSwap p, hp, coordinateSwap_involutive p⟩

private theorem coordinateSwap_image_outerQuadrant :
    coordinateSwap '' hallwayParts.outerQuadrant = hallwayParts.outerQuadrant := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap, and_comm]

private theorem coordinateSwap_image_innerQuadrant :
    coordinateSwap '' hallwayParts.innerQuadrant = hallwayParts.innerQuadrant := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap, and_comm]

private theorem coordinateSwap_image_a :
    coordinateSwap '' hallwayParts.a = hallwayParts.c := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap]

private theorem coordinateSwap_image_c :
    coordinateSwap '' hallwayParts.c = hallwayParts.a := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap]

private theorem coordinateSwap_image_b :
    coordinateSwap '' hallwayParts.b = hallwayParts.d := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap]

private theorem coordinateSwap_image_d :
    coordinateSwap '' hallwayParts.d = hallwayParts.b := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap]

private theorem coordinateSwap_image_bRay :
    coordinateSwap '' hallwayParts.bRay = hallwayParts.dRay := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap, and_comm]

private theorem coordinateSwap_image_dRay :
    coordinateSwap '' hallwayParts.dRay = hallwayParts.bRay := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap, and_comm]

private theorem supportingPlacement_image_reflection (ω t : ℝ)
    (K : ConvexBody Point) (s : Set Point) :
    supportingPlacement (reflectedBody ω K) (t : Real.Angle) ''
        (coordinateSwap '' s) =
      capReflection ω ''
        (supportingPlacement K ((ω - t : ℝ) : Real.Angle) '' s) := by
  rw [Set.image_image, Set.image_image]
  congr 1
  funext q
  exact supportingPlacement_reflection ω t K q

private theorem supportingHallway_reflection (ω t : ℝ)
    (K : ConvexBody Point) :
    supportingHallway (reflectedBody ω K) (t : Real.Angle) =
      capReflection ω '' supportingHallway K ((ω - t : ℝ) : Real.Angle) := by
  unfold supportingHallway
  nth_rewrite 1 [← coordinateSwap_image_hallway]
  exact supportingPlacement_image_reflection ω t K hallway

private theorem rotatingHallwayParts_reflection (ω t : ℝ)
    (K : ConvexBody Point) :
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).innerCorner =
        capReflection ω
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).innerCorner ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).outerCorner =
        capReflection ω
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).outerCorner ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).outerQuadrant =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).outerQuadrant ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).innerQuadrant =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).innerQuadrant ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).a =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).c ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).c =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).a ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).b =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).d ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).d =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).b ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).bRay =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).dRay ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).dRay =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).bRay := by
  have hzero : coordinateSwap (0 : Point) = 0 := by
    ext i
    fin_cases i <;> simp [coordinateSwap]
  have hone : coordinateSwap (!₂[1, 1] : Point) = !₂[1, 1] := by
    ext i
    fin_cases i <;> simp [coordinateSwap]
  unfold rotatingHallwayParts
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hallwayParts]
    rw [← hzero]
    exact supportingPlacement_reflection ω t K 0
  · simp only [hallwayParts]
    nth_rewrite 1 [← hone]
    exact supportingPlacement_reflection ω t K !₂[1, 1]
  · nth_rewrite 1 [← coordinateSwap_image_outerQuadrant]
    exact supportingPlacement_image_reflection ω t K hallwayParts.outerQuadrant
  · nth_rewrite 1 [← coordinateSwap_image_innerQuadrant]
    exact supportingPlacement_image_reflection ω t K hallwayParts.innerQuadrant
  · nth_rewrite 1 [← coordinateSwap_image_c]
    exact supportingPlacement_image_reflection ω t K hallwayParts.c
  · nth_rewrite 1 [← coordinateSwap_image_a]
    exact supportingPlacement_image_reflection ω t K hallwayParts.a
  · nth_rewrite 1 [← coordinateSwap_image_d]
    exact supportingPlacement_image_reflection ω t K hallwayParts.d
  · nth_rewrite 1 [← coordinateSwap_image_b]
    exact supportingPlacement_image_reflection ω t K hallwayParts.b
  · nth_rewrite 1 [← coordinateSwap_image_dRay]
    exact supportingPlacement_image_reflection ω t K hallwayParts.dRay
  · nth_rewrite 1 [← coordinateSwap_image_bRay]
    exact supportingPlacement_image_reflection ω t K hallwayParts.bRay

private theorem exposedEdge_reflection (ω : ℝ) (K : ConvexBody Point)
    (a : Real.Angle) :
    exposedEdge (reflectedBody ω K) a =
      capReflection ω '' exposedEdge K (reflectedAngle ω a) := by
  ext p
  constructor
  · rintro ⟨⟨q, hq, rfl⟩, hp⟩
    refine ⟨q, ⟨hq, ?_⟩, rfl⟩
    change inner ℝ (capReflection ω q) (normalVector a) =
      supportValue (reflectedBody ω K) a at hp
    change inner ℝ q (normalVector (reflectedAngle ω a)) =
      supportValue K (reflectedAngle ω a)
    rw [← inner_capReflection_normalVector ω q a,
      ← supportValue_reflectedBody ω K a]
    exact hp
  · rintro ⟨q, ⟨hq, hp⟩, rfl⟩
    refine ⟨⟨q, hq, rfl⟩, ?_⟩
    change inner ℝ (capReflection ω q) (normalVector a) =
      supportValue (reflectedBody ω K) a
    rw [inner_capReflection_normalVector, supportValue_reflectedBody]
    exact hp

private theorem exposedEdgeHeights_reflection (ω : ℝ) (K : ConvexBody Point)
    (a : Real.Angle) :
    (fun p ↦ inner ℝ p (tangentVector a)) '' exposedEdge (reflectedBody ω K) a =
      -((fun p ↦ inner ℝ p (tangentVector (reflectedAngle ω a))) ''
        exposedEdge K (reflectedAngle ω a)) := by
  rw [exposedEdge_reflection]
  ext x
  simp only [Set.mem_image, Set.mem_neg]
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨q, hq, ?_⟩
    rw [inner_capReflection_tangentVector, neg_neg]
  · rintro ⟨q, hq, hq_inner⟩
    refine ⟨capReflection ω q, ⟨q, hq, rfl⟩, ?_⟩
    rw [inner_capReflection_tangentVector, hq_inner, neg_neg]

private theorem edgeVertices_reflection (ω : ℝ) (K : ConvexBody Point)
    (a : Real.Angle) :
    edgeVertices (reflectedBody ω K) a =
      (capReflection ω (edgeVertices K (reflectedAngle ω a)).2,
        capReflection ω (edgeVertices K (reflectedAngle ω a)).1) := by
  unfold edgeVertices
  dsimp only
  rw [supportValue_reflectedBody, exposedEdgeHeights_reflection,
    Real.sSup_neg, Real.sInf_neg]
  apply Prod.ext <;> dsimp only
  · rw [map_add, map_smul, map_smul, capReflection_normalVector_angle,
      capReflection_tangentVector_angle, reflectedAngle_involutive]
    module
  · rw [map_add, map_smul, map_smul, capReflection_normalVector_angle,
      capReflection_tangentVector_angle, reflectedAngle_involutive]
    module

private theorem capVertices_reflection {ω : ℝ} (K : CapSpace ω) (t : ℝ) :
    let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
    capVertices P t =
      ((capReflection ω (capVertices K (ω - t)).2.2,
        capReflection ω (capVertices K (ω - t)).2.1),
       (capReflection ω (capVertices K (ω - t)).1.2,
        capReflection ω (capVertices K (ω - t)).1.1)) := by
  dsimp only
  unfold capVertices
  rw [edgeVertices_reflection, edgeVertices_reflection]
  dsimp only
  rw [reflectedAngle_coe, reflectedAngle_coe]
  congr 1 <;> ring_nf

private theorem capReflection_normal_zero (ω : ℝ) :
    capReflection ω (normalVector 0) = tangentVector (ω : Real.Angle) := by
  simpa using capReflection_normal_at_complement ω ω

private theorem capReflection_tangent_omega (ω : ℝ) :
    capReflection ω (tangentVector (ω : Real.Angle)) = normalVector 0 := by
  simpa using capReflection_tangent_at_complement ω 0

private theorem wedgeEndpoints_reflection {ω : ℝ} (K : CapSpace ω) (t : ℝ) :
    let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
    wedgeEndpoints P t =
      (capReflection ω (wedgeEndpoints K (ω - t)).2,
        capReflection ω (wedgeEndpoints K (ω - t)).1) := by
  dsimp only
  unfold wedgeEndpoints
  rw [supportValue_reflected_at, supportValue_reflected_at_add_pi_div_two]
  apply Prod.ext <;> dsimp only
  · rw [map_smul, capReflection_tangent_omega]
    congr 2; ring_nf
  · rw [map_smul, capReflection_normal_zero]

private theorem wedgeGaps_reflection {ω : ℝ} (K : CapSpace ω) (t : ℝ) :
    let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
    wedgeGaps P t = ((wedgeGaps K (ω - t)).2, (wedgeGaps K (ω - t)).1) := by
  dsimp only
  unfold wedgeGaps
  rw [capVertices_reflection K 0, capVertices_reflection K ω,
    wedgeEndpoints_reflection K t]
  dsimp only
  apply Prod.ext <;> dsimp only
  · rw [← map_sub, ← capReflection_tangent_omega,
      (capReflection ω).inner_map_map]
    simp
  · rw [← map_sub, ← capReflection_normal_zero,
      (capReflection ω).inner_map_map]
    simp

private theorem capWedge_reflection {ω : ℝ} (K : CapSpace ω) (t : ℝ) :
    let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
    capWedge P t = capReflection ω '' capWedge K (ω - t) := by
  dsimp only
  unfold capWedge
  rw [Set.image_inter (capReflection ω).injective,
    capReflection_image_capFan,
    (rotatingHallwayParts_reflection ω t K.val).2.2.2.1]

private theorem iUnion_innerQuadrant_reflection {ω : ℝ} (K : CapSpace ω) :
    (⋃ t ∈ Set.Ioo 0 ω, innerQuadrant (reflectedBody ω K.val) t) =
      capReflection ω '' (⋃ s ∈ Set.Ioo 0 ω, innerQuadrant K.val s) := by
  ext p
  constructor
  · intro hp
    obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hp
    rcases ht with ⟨ht0, htω⟩
    rw [innerQuadrant_reflection] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    refine ⟨q, Set.mem_iUnion₂.mpr ⟨ω - t, ⟨by linarith, by linarith⟩, hq⟩, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨s, hs, hq⟩ := Set.mem_iUnion₂.mp hq
    rcases hs with ⟨hs0, hsω⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨ω - s, ⟨by linarith, by linarith⟩, ?_⟩
    rw [innerQuadrant_reflection]
    exact ⟨q, by simpa, rfl⟩

private theorem capNiche_reflection {ω : ℝ} (K : CapSpace ω) :
    let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
    capNiche P = capReflection ω '' capNiche K := by
  dsimp only
  unfold capNiche
  rw [Set.image_inter (capReflection ω).injective,
    capReflection_image_capFan, ← iUnion_innerQuadrant_reflection]

private theorem iUnion_exposedEdge_reflection {ω : ℝ} (K : CapSpace ω) :
    (⋃ t ∈ Set.Icc 0 (ω + Real.pi / 2),
        exposedEdge (reflectedBody ω K.val) (t : Real.Angle)) =
      capReflection ω ''
        (⋃ s ∈ Set.Icc 0 (ω + Real.pi / 2),
          exposedEdge K.val (s : Real.Angle)) := by
  ext p
  constructor
  · intro hp
    obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hp
    rcases ht with ⟨ht0, htω⟩
    rw [exposedEdge_reflection] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    refine ⟨q, Set.mem_iUnion₂.mpr ⟨ω + Real.pi / 2 - t,
      ⟨by linarith, by linarith⟩, ?_⟩, rfl⟩
    simpa only [reflectedAngle_coe] using hq
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨s, hs, hq⟩ := Set.mem_iUnion₂.mp hq
    rcases hs with ⟨hs0, hsω⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨ω + Real.pi / 2 - s, ⟨by linarith, by linarith⟩, ?_⟩
    rw [exposedEdge_reflection]
    refine ⟨q, ?_, rfl⟩
    rw [reflectedAngle_coe]
    convert hq using 1; ring_nf

private theorem capUpperBoundary_reflection {ω : ℝ} (K : CapSpace ω) :
    let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
    capUpperBoundary P = capReflection ω '' capUpperBoundary K := by
  dsimp only
  unfold capUpperBoundary
  exact iUnion_exposedEdge_reflection K

private def reflectedAngleEquiv (ω : ℝ) : Real.Angle ≃ᵐ Real.Angle :=
  MeasurableEquiv.ofInvolutive (reflectedAngle ω)
    (reflectedAngle_involutive ω) (by unfold reflectedAngle; fun_prop)

private theorem reflectedAngle_add_pi (ω : ℝ) (a : Real.Angle) :
    reflectedAngle ω (a + (Real.pi : Real.Angle)) =
      reflectedAngle ω a + (Real.pi : Real.Angle) := by
  have hpi : -(Real.pi : Real.Angle) = (Real.pi : Real.Angle) :=
    neg_eq_iff_add_eq_zero.mpr Real.Angle.coe_pi_add_coe_pi
  unfold reflectedAngle
  rw [sub_eq_add_neg, neg_add_rev, hpi]
  abel

private theorem isSegmentPresentation_reflectedBody (ω : ℝ)
    (K : ConvexBody Point) (d : Point × Point × Real.Angle)
    (hd : IsSegmentPresentation K d) :
    IsSegmentPresentation (reflectedBody ω K)
      (capReflection ω d.1, capReflection ω d.2.1, reflectedAngle ω d.2.2) := by
  refine ⟨fun h ↦ hd.1 ((capReflection ω).injective h), ?_, ?_⟩
  · change capReflection ω '' (K : Set Point) =
      segment ℝ (capReflection ω d.1) (capReflection ω d.2.1)
    rw [hd.2.1]
    exact image_segment ℝ
      (capReflection ω).toLinearEquiv.toLinearMap.toAffineMap d.1 d.2.1
  · rw [← map_sub, ← capReflection_normalVector_angle,
      (capReflection ω).inner_map_map]
    exact hd.2.2

private theorem reflectedBody_reflectedBody (ω : ℝ) (K : ConvexBody Point) :
    reflectedBody ω (reflectedBody ω K) = K := by
  apply ConvexBody.ext
  ext p
  constructor
  · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
    simpa only [capReflection_involutive] using hr
  · intro hp
    exact ⟨capReflection ω p, ⟨p, hp, rfl⟩, capReflection_involutive ω p⟩

private theorem subsingleton_reflectedBody_iff (ω : ℝ) (K : ConvexBody Point) :
    ((reflectedBody ω K : ConvexBody Point) : Set Point).Subsingleton ↔
      (K : Set Point).Subsingleton := by
  constructor
  · intro hP p hp q hq
    apply (capReflection ω).injective
    exact hP ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
  · intro hK _
    rintro ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    rw [hK hp hq]

private theorem exists_segmentPresentation_reflectedBody_iff (ω : ℝ)
    (K : ConvexBody Point) :
    (∃ d, IsSegmentPresentation (reflectedBody ω K) d) ↔
      ∃ d, IsSegmentPresentation K d := by
  constructor
  · rintro ⟨d, hd⟩
    have h := isSegmentPresentation_reflectedBody ω (reflectedBody ω K) d hd
    rw [reflectedBody_reflectedBody] at h
    exact ⟨_, h⟩
  · rintro ⟨d, hd⟩
    exact ⟨_, isSegmentPresentation_reflectedBody ω K d hd⟩

private theorem surfaceAreaMeasure_reflectedBody_of_subsingleton (ω : ℝ)
    (K : ConvexBody Point) (hK : (K : Set Point).Subsingleton) :
    surfaceAreaMeasure (reflectedBody ω K) =
      Measure.map (reflectedAngleEquiv ω) (surfaceAreaMeasure K) := by
  have hP : ((reflectedBody ω K : ConvexBody Point) : Set Point).Subsingleton := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    rw [hK hp hq]
  rw [surfaceAreaMeasure_eq_zero_of_subsingleton (reflectedBody ω K) hP,
    surfaceAreaMeasure_eq_zero_of_subsingleton K hK, Measure.map_zero]

private theorem surfaceAreaMeasure_reflectedBody_of_segmentPresentation (ω : ℝ)
    (K : ConvexBody Point) (d : Point × Point × Real.Angle)
    (hd : IsSegmentPresentation K d) :
    surfaceAreaMeasure (reflectedBody ω K) =
      Measure.map (reflectedAngleEquiv ω) (surfaceAreaMeasure K) := by
  rw [surfaceAreaMeasure_eq_segmentPresentation (reflectedBody ω K)
      (capReflection ω d.1, capReflection ω d.2.1, reflectedAngle ω d.2.2)
      (isSegmentPresentation_reflectedBody ω K d hd),
    surfaceAreaMeasure_eq_segmentPresentation K d hd,
    MeasureTheory.Measure.map_smul _ (reflectedAngleEquiv ω).measurable.aemeasurable,
    MeasureTheory.Measure.map_add _ _ (reflectedAngleEquiv ω).measurable,
    MeasureTheory.Measure.map_dirac, MeasureTheory.Measure.map_dirac,
    (capReflection ω).dist_map]
  change ENNReal.ofReal (dist d.1 d.2.1) •
      (Measure.dirac (reflectedAngle ω d.2.2) +
        Measure.dirac (reflectedAngle ω d.2.2 + (Real.pi : Real.Angle))) =
    ENNReal.ofReal (dist d.1 d.2.1) •
      (Measure.dirac (reflectedAngle ω d.2.2) +
        Measure.dirac (reflectedAngle ω (d.2.2 + (Real.pi : Real.Angle))))
  rw [reflectedAngle_add_pi]

private theorem isExteriorNormal_reflectedBody_iff (ω : ℝ)
    (K : ConvexBody Point) (p : Point) (a : Real.Angle) :
    IsExteriorNormal (reflectedBody ω K) (capReflection ω p) (reflectedAngle ω a) ↔
      IsExteriorNormal K p a := by
  constructor
  · intro h q hq
    have h' := h (capReflection ω q) ⟨q, hq, rfl⟩
    rw [← map_sub, ← capReflection_normalVector_angle,
      (capReflection ω).inner_map_map] at h'
    exact h'
  · intro h _
    rintro ⟨q, hq, rfl⟩
    rw [← map_sub, ← capReflection_normalVector_angle,
      (capReflection ω).inner_map_map]
    exact h q hq

private theorem mem_regularBoundary_reflectedBody_iff (ω : ℝ)
    (K : ConvexBody Point) (p : Point) :
    capReflection ω p ∈ regularBoundary (reflectedBody ω K) ↔
      p ∈ regularBoundary K := by
  have hfront : capReflection ω p ∈ frontier ((reflectedBody ω K : ConvexBody Point) : Set Point) ↔
      p ∈ frontier (K : Set Point) := by
    change capReflection ω p ∈ frontier (capReflection ω '' (K : Set Point)) ↔ _
    have himage : capReflection ω '' frontier (K : Set Point) =
        frontier (capReflection ω '' (K : Set Point)) :=
      (capReflection ω).toHomeomorph.image_frontier (K : Set Point)
    rw [← himage]
    constructor
    · rintro ⟨q, hq, hpq⟩
      have hqp : q = p := (capReflection ω).injective hpq
      simpa only [hqp] using hq
    · exact fun hp ↦ ⟨p, hp, rfl⟩
  have hunique :
      (∃! b, IsExteriorNormal (reflectedBody ω K) (capReflection ω p) b) ↔
        ∃! a, IsExteriorNormal K p a := by
    constructor
    · rintro ⟨b, hb, hub⟩
      have hbK : IsExteriorNormal K p (reflectedAngle ω b) := by
        apply (isExteriorNormal_reflectedBody_iff ω K p (reflectedAngle ω b)).mp
        simpa only [reflectedAngle_involutive] using hb
      refine ⟨reflectedAngle ω b, hbK, ?_⟩
      intro c hc
      have hcL := (isExteriorNormal_reflectedBody_iff ω K p c).mpr hc
      have hcb : reflectedAngle ω c = b := hub _ hcL
      calc
        c = reflectedAngle ω (reflectedAngle ω c) :=
          (reflectedAngle_involutive ω c).symm
        _ = reflectedAngle ω b := congrArg (reflectedAngle ω) hcb
    · rintro ⟨a, ha, hua⟩
      refine ⟨reflectedAngle ω a,
        (isExteriorNormal_reflectedBody_iff ω K p a).mpr ha, ?_⟩
      intro b hb
      have hbK : IsExteriorNormal K p (reflectedAngle ω b) := by
        apply (isExteriorNormal_reflectedBody_iff ω K p (reflectedAngle ω b)).mp
        simpa only [reflectedAngle_involutive] using hb
      have hba : reflectedAngle ω b = a := hua _ hbK
      calc
        b = reflectedAngle ω (reflectedAngle ω b) :=
          (reflectedAngle_involutive ω b).symm
        _ = reflectedAngle ω a := congrArg (reflectedAngle ω) hba
  simp only [regularBoundary, Set.mem_ofPred_eq]
  exact and_congr hfront hunique

private theorem exteriorNormalAngle_reflectedBody (ω : ℝ)
    (K : ConvexBody Point) (p : Point) (hp : p ∈ regularBoundary K) :
    exteriorNormalAngle (reflectedBody ω K) (capReflection ω p) =
      reflectedAngle ω (exteriorNormalAngle K p) := by
  have hP := (mem_regularBoundary_reflectedBody_iff ω K p).mpr hp
  have huK : ∃! a, IsExteriorNormal K p a := hp.2
  have huP : ∃! a,
      IsExteriorNormal (reflectedBody ω K) (capReflection ω p) a := hP.2
  have hnK : IsExteriorNormal K p (exteriorNormalAngle K p) := by
    unfold exteriorNormalAngle
    rw [dite_eq_left huK]
    generalize_proofs h
    exact h.choose_spec
  have hnP : IsExteriorNormal (reflectedBody ω K) (capReflection ω p)
      (exteriorNormalAngle (reflectedBody ω K) (capReflection ω p)) := by
    unfold exteriorNormalAngle
    rw [dite_eq_left huP]
    generalize_proofs _ h
    exact h.choose_spec
  exact huP.unique hnP ((isExteriorNormal_reflectedBody_iff ω K p _).mpr hnK)

private theorem regularBoundary_reflectedBody (ω : ℝ) (K : ConvexBody Point) :
    regularBoundary (reflectedBody ω K) =
      capReflection ω '' regularBoundary K := by
  ext q
  constructor
  · intro hq
    refine ⟨capReflection ω q, ?_, capReflection_involutive ω q⟩
    apply (mem_regularBoundary_reflectedBody_iff ω K (capReflection ω q)).mp
    simpa only [capReflection_involutive] using hq
  · rintro ⟨p, hp, rfl⟩
    exact (mem_regularBoundary_reflectedBody_iff ω K p).mpr hp

private theorem map_hausdorffMeasure_restrict_regularBoundary (ω : ℝ)
    (K : ConvexBody Point) :
    Measure.map (capReflection ω)
        ((Measure.hausdorffMeasure 1).restrict (regularBoundary K)) =
      (Measure.hausdorffMeasure 1).restrict
        (regularBoundary (reflectedBody ω K)) := by
  rw [regularBoundary_reflectedBody]
  let e := (capReflection ω).toHomeomorph.toMeasurableEquiv
  have hrestrict := e.restrict_map (Measure.hausdorffMeasure 1)
    (capReflection ω '' regularBoundary K)
  change (Measure.map (capReflection ω) (Measure.hausdorffMeasure 1)).restrict
      (capReflection ω '' regularBoundary K) =
    Measure.map (capReflection ω)
      ((Measure.hausdorffMeasure 1).restrict
        (capReflection ω ⁻¹' (capReflection ω '' regularBoundary K))) at hrestrict
  have hmap : Measure.map (capReflection ω) (Measure.hausdorffMeasure 1) =
      Measure.hausdorffMeasure 1 :=
    (capReflection ω).toIsometryEquiv.map_hausdorffMeasure 1
  rw [hmap] at hrestrict
  have hpre : capReflection ω ⁻¹' (capReflection ω '' regularBoundary K) =
      regularBoundary K := by
    exact Set.preimage_image_eq _ (capReflection ω).injective
  rw [hpre] at hrestrict
  exact hrestrict.symm

private theorem reflectedAngle_preimage_eq_image (ω : ℝ)
    (E : Set Real.Angle) :
    reflectedAngle ω ⁻¹' E = reflectedAngle ω '' E := by
  ext a
  constructor
  · intro ha
    exact ⟨reflectedAngle ω a, ha, reflectedAngle_involutive ω a⟩
  · rintro ⟨b, hb, rfl⟩
    simpa only [Set.mem_preimage, reflectedAngle_involutive] using hb

private theorem surfaceAreaMeasure_reflectedBody (ω : ℝ)
    (K : ConvexBody Point) :
    surfaceAreaMeasure (reflectedBody ω K) =
      Measure.map (reflectedAngleEquiv ω) (surfaceAreaMeasure K) := by
  by_cases hsub : (K : Set Point).Subsingleton
  · exact surfaceAreaMeasure_reflectedBody_of_subsingleton ω K hsub
  by_cases hseg : ∃ d, IsSegmentPresentation K d
  · obtain ⟨d, hd⟩ := hseg
    exact surfaceAreaMeasure_reflectedBody_of_segmentPresentation ω K d hd
  have hsubP : ¬ ((reflectedBody ω K : ConvexBody Point) : Set Point).Subsingleton :=
    fun h ↦ hsub ((subsingleton_reflectedBody_iff ω K).mp h)
  have hsegP : ¬ ∃ d, IsSegmentPresentation (reflectedBody ω K) d :=
    fun h ↦ hseg ((exists_segmentPresentation_reflectedBody_iff ω K).mp h)
  let μK := (Measure.hausdorffMeasure 1).restrict (regularBoundary K)
  let μP := (Measure.hausdorffMeasure 1).restrict
    (regularBoundary (reflectedBody ω K))
  have hμ : Measure.map (capReflection ω) μK = μP :=
    map_hausdorffMeasure_restrict_regularBoundary ω K
  have haeK : AEMeasurable (exteriorNormalAngle K) μK :=
    aemeasurable_exteriorNormalAngle_restrict_regularBoundary K _
  have haeP : AEMeasurable (exteriorNormalAngle (reflectedBody ω K)) μP :=
    aemeasurable_exteriorNormalAngle_restrict_regularBoundary (reflectedBody ω K) _
  simp only [surfaceAreaMeasure, hsub, hseg, hsubP, hsegP, ↓reduceIte]
  change Measure.map (exteriorNormalAngle (reflectedBody ω K)) μP =
    Measure.map (reflectedAngleEquiv ω)
      (Measure.map (exteriorNormalAngle K) μK)
  rw [← hμ]
  have haeP' : AEMeasurable (exteriorNormalAngle (reflectedBody ω K))
      (Measure.map (capReflection ω) μK) := by
    rwa [hμ]
  rw [AEMeasurable.map_map_of_aemeasurable haeP'
      (capReflection ω).continuous.measurable.aemeasurable,
    AEMeasurable.map_map_of_aemeasurable
      (reflectedAngleEquiv ω).measurable.aemeasurable haeK]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (measurableSet_regularBoundary K)] with p hp
  exact exteriorNormalAngle_reflectedBody ω K p hp

theorem cap_mirror_features {ω : ℝ} (K : CapSpace ω) :
    ∃ P : CapSpace ω,
      (P.val : Set Point) = mirrorReflection ω '' (K.val : Set Point) ∧
      (∀ t ∈ Set.Icc 0 ω,
        supportingHallway (P.val : Set Point) (t : Real.Angle) =
        mirrorReflection ω '' supportingHallway (K.val : Set Point) ((ω - t : ℝ) : Real.Angle) ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).innerCorner = mirrorReflection
          ω (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).innerCorner ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).outerCorner = mirrorReflection
          ω (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).outerCorner ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).outerQuadrant =
          mirrorReflection ω '' (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) :
          Real.Angle)).outerQuadrant ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).innerQuadrant =
          mirrorReflection ω '' (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) :
          Real.Angle)).innerQuadrant ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).a = mirrorReflection ω ''
          (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).c ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).c = mirrorReflection ω ''
          (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).a ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).b = mirrorReflection ω ''
          (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).d ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).d = mirrorReflection ω ''
          (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).b ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).bRay = mirrorReflection ω ''
          (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).dRay ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).dRay = mirrorReflection ω ''
          (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).bRay ∧
        (capVertices P t).1.1 = mirrorReflection ω (capVertices K (ω - t)).2.2 ∧
        (capVertices P t).1.2 = mirrorReflection ω (capVertices K (ω - t)).2.1 ∧
        (capVertices P t).2.1 = mirrorReflection ω (capVertices K (ω - t)).1.2 ∧
        (capVertices P t).2.2 = mirrorReflection ω (capVertices K (ω - t)).1.1) ∧
      (∀ t ∈ Set.Ioo 0 ω,
        (wedgeEndpoints P t).1 = mirrorReflection ω (wedgeEndpoints K (ω - t)).2 ∧
        (wedgeEndpoints P t).2 = mirrorReflection ω (wedgeEndpoints K (ω - t)).1 ∧
        (wedgeGaps P t).1 = (wedgeGaps K (ω - t)).2 ∧
        (wedgeGaps P t).2 = (wedgeGaps K (ω - t)).1 ∧
        capWedge P t = mirrorReflection ω '' capWedge K (ω - t)) ∧
      capUpperBoundary P = mirrorReflection ω '' capUpperBoundary K ∧
      capNiche P = mirrorReflection ω '' capNiche K ∧
      (∀ E : Set Real.Angle, MeasurableSet E →
        surfaceAreaMeasure P.val E = surfaceAreaMeasure K.val
          ((fun a : Real.Angle ↦ ((ω + Real.pi / 2 : ℝ) : Real.Angle) - a) '' E)) := by
  let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
  have hM : mirrorReflection ω = capReflection ω :=
    mirrorReflection_eq_capReflection_m6ef9701 ω K.property.1 K.property.2.1
  refine ⟨P, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change capReflection ω '' (K.val : Set Point) =
      mirrorReflection ω '' (K.val : Set Point)
    rw [hM]
  · intro t _
    rw [hM]
    have hh := supportingHallway_reflection ω t K.val
    have hp := rotatingHallwayParts_reflection ω t K.val
    have hv := capVertices_reflection K t
    rcases hp with ⟨hinner, houter, hQouter, hQinner, ha, hc, hb, hd, hbRay, hdRay⟩
    refine ⟨hh, hinner, houter, hQouter, hQinner, ha, hc, hb, hd, hbRay, hdRay,
      ?_, ?_, ?_, ?_⟩
    · simpa only [P] using congrArg (fun v ↦ v.1.1) hv
    · simpa only [P] using congrArg (fun v ↦ v.1.2) hv
    · simpa only [P] using congrArg (fun v ↦ v.2.1) hv
    · simpa only [P] using congrArg (fun v ↦ v.2.2) hv
  · intro t _
    rw [hM]
    have he := wedgeEndpoints_reflection K t
    have hg := wedgeGaps_reflection K t
    refine ⟨?_, ?_, ?_, ?_, capWedge_reflection K t⟩
    · simpa only [P] using congrArg Prod.fst he
    · simpa only [P] using congrArg Prod.snd he
    · simpa only [P] using congrArg Prod.fst hg
    · simpa only [P] using congrArg Prod.snd hg
  · rw [hM]
    exact capUpperBoundary_reflection K
  · rw [hM]
    exact capNiche_reflection K
  · intro E hE
    change surfaceAreaMeasure (reflectedBody ω K.val) E = _
    rw [surfaceAreaMeasure_reflectedBody,
      (reflectedAngleEquiv ω).map_apply]
    change surfaceAreaMeasure K.val (reflectedAngle ω ⁻¹' E) = _
    rw [reflectedAngle_preimage_eq_image]
    rfl

end MovingSofa

end

end

end
