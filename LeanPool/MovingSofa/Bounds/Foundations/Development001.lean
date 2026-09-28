/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Cap.Foundations.Development002
public import LeanPool.MovingSofa.Infrastructure.MathlibExtensions.Foundations.Development001
public import LeanPool.MovingSofa.Motion.Foundations.Development001
/-!
# Moving sofa: related mathematical developments

* `Bounds.WedgeContainment`.
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
# Bounds / Wedge Containment
-/

@[expose] public section

noncomputable section

namespace MovingSofa

private theorem smul_mem_of_mem_of_le_of_le {K : ConvexBody Point} {v : Point}
    {l x r : ℝ} (hl : l • v ∈ (K : Set Point)) (hr : r • v ∈ (K : Set Point))
    (hlx : l ≤ x) (hxr : x ≤ r) : x • v ∈ (K : Set Point) := by
  by_cases hlr : l = r
  · have hx : x = l := by linarith
    simpa [hx] using hl
  · have hlrpos : 0 < r - l := sub_pos.mpr (lt_of_le_of_ne (hlx.trans hxr) hlr)
    have hratio : (x - l) / (r - l) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hlx) hlrpos.le
      · exact (div_le_one hlrpos).2 (by linarith)
    have hmem := K.convex.lineMap_mem hl hr hratio
    rw [AffineMap.lineMap_apply_module] at hmem
    have heq : (1 - (x - l) / (r - l)) • l • v +
        ((x - l) / (r - l)) • r • v = x • v := by
      rw [smul_smul, smul_smul, ← add_smul]
      congr 1
      field_simp
      ring
    rw [heq] at hmem
    exact hmem

private theorem inner_lineMap (x y u : Point) (s : ℝ) :
    inner ℝ (AffineMap.lineMap x y s) u =
      inner ℝ x u + s * (inner ℝ y u - inner ℝ x u) := by
  rw [AffineMap.lineMap_apply_module, inner_add_left, real_inner_smul_left,
    real_inner_smul_left]
  ring

private theorem mem_segment_lineMap_of_one_le (x y : Point) {s : ℝ} (hs : 1 ≤ s) :
    y ∈ segment ℝ x (AffineMap.lineMap x y s) := by
  have hspos : 0 < s := zero_lt_one.trans_le hs
  rw [segment_eq_image_lineMap]
  refine ⟨1 / s, ⟨by positivity, (div_le_one hspos).2 hs⟩, ?_⟩
  ext i
  simp [AffineMap.lineMap_apply_module, one_div, hspos.ne']
  field_simp
  ring

private theorem exists_lineMap_fan_boundary (x y u v : Point)
    (hyu : 0 ≤ inner ℝ y u) (hyv : 0 ≤ inner ℝ y v)
    (hdu : inner ℝ (y - x) u < 0) (hdv : inner ℝ (y - x) v < 0) :
    ∃ s : ℝ, 1 ≤ s ∧
      0 ≤ inner ℝ (AffineMap.lineMap x y s) u ∧
      0 ≤ inner ℝ (AffineMap.lineMap x y s) v ∧
      (inner ℝ (AffineMap.lineMap x y s) u = 0 ∨
        inner ℝ (AffineMap.lineMap x y s) v = 0) := by
  let du := inner ℝ x u - inner ℝ y u
  let dv := inner ℝ x v - inner ℝ y v
  have hdu' : 0 < du := by
    rw [inner_sub_left] at hdu
    dsimp [du]
    linarith
  have hdv' : 0 < dv := by
    rw [inner_sub_left] at hdv
    dsimp [dv]
    linarith
  by_cases hratio : inner ℝ x u / du ≤ inner ℝ x v / dv
  · let s := inner ℝ x u / du
    have hs : 1 ≤ s := by
      apply (le_div_iff₀ hdu').2
      dsimp [du]
      linarith
    have hsdu : s * du = inner ℝ x u := by
      dsimp [s]
      field_simp
    have hsu : inner ℝ (AffineMap.lineMap x y s) u = 0 := by
      rw [inner_lineMap]
      have hdiff : inner ℝ y u - inner ℝ x u = -du := by simp [du]
      rw [hdiff, mul_neg, hsdu]
      ring
    have hsv : 0 ≤ inner ℝ (AffineMap.lineMap x y s) v := by
      have hmul : s * dv ≤ inner ℝ x v := (le_div_iff₀ hdv').mp hratio
      rw [inner_lineMap]
      dsimp [dv] at hmul
      linarith
    exact ⟨s, hs, hsu.ge, hsv, Or.inl hsu⟩
  · let s := inner ℝ x v / dv
    have hs : 1 ≤ s := by
      apply (le_div_iff₀ hdv').2
      dsimp [dv]
      linarith
    have hsdv : s * dv = inner ℝ x v := by
      dsimp [s]
      field_simp
    have hsv : inner ℝ (AffineMap.lineMap x y s) v = 0 := by
      rw [inner_lineMap]
      have hdiff : inner ℝ y v - inner ℝ x v = -dv := by simp [dv]
      rw [hdiff, mul_neg, hsdv]
      ring
    have hsu : 0 ≤ inner ℝ (AffineMap.lineMap x y s) u := by
      have hmul : s * du ≤ inner ℝ x u := (le_div_iff₀ hdu').mp (not_le.mp hratio).le
      rw [inner_lineMap]
      dsimp [du] at hmul
      linarith
    exact ⟨s, hs, hsu, hsv.ge, Or.inr hsv⟩

private theorem cap_fan_boundary_mem {ω : ℝ} (K : CapSpace ω)
    (t : ℝ) (ht : t ∈ Set.Ioo 0 ω) (p : Point)
    (hpy : 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)))
    (hpω : 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)))
    (hpboundary : inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 ∨
    inner ℝ p (normalVector (ω : Real.Angle)) = 0)
    (hpt : inner ℝ p (normalVector (t : Real.Angle)) <
      supportValue K.val (t : Real.Angle) - 1)
    (hptv : inner ℝ p (tangentVector (t : Real.Angle)) <
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) :
    p ∈ (K.val : Set Point) := by
  have hsint : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [ht.2, K.property.2.1, Real.pi_pos])
  have hcost : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_le K.property.2.1⟩
  have hsinδ : 0 < Real.sin (ω - t) := Real.sin_pos_of_pos_of_lt_pi
    (sub_pos.mpr ht.2) (by linarith [ht.1, K.property.2.1, Real.pi_pos])
  have hcosδ : 0 < Real.cos (ω - t) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [sub_pos.mpr ht.2, Real.pi_pos],
      by linarith [ht.1, K.property.2.1]⟩
  by_cases hωeq : ω = Real.pi / 2
  · have hpy0 : p 1 = 0 := by
      rcases hpboundary with hpy0 | hpω0
      · simpa [normalVector, frame, PiLp.inner_apply] using hpy0
      · rw [hωeq] at hpω0
        simpa [normalVector, frame, PiLp.inner_apply] using hpω0
    let l := -supportValue K.val (Real.pi : Real.Angle)
    let r := supportValue K.val (0 : Real.Angle)
    have hleft : l • normalVector (0 : Real.Angle) ∈ (K.val : Set Point) := by
      have h := supportValue_pi_smul_normalVector_mem_of_eq K hωeq
      convert h using 1
      ext i
      fin_cases i <;> simp [l, normalVector, frame]
    have hright : r • normalVector (0 : Real.Angle) ∈ (K.val : Set Point) := by
      exact supportValue_zero_smul_normalVector_mem K
    have hbounds := K.supportValue_upper_bounds ht
    have hsint_lt : Real.sin t < 1 := by
      nlinarith only [Real.sin_sq_add_cos_sq t, sq_pos_of_pos hcost]
    have hcost_lt : Real.cos t < 1 := by
      nlinarith only [Real.sin_sq_add_cos_sq t, sq_pos_of_pos hsint]
    have hpr : p 0 ≤ r := by
      have hpt' := hpt
      simp [normalVector, frame, PiLp.inner_apply, hpy0] at hpt'
      dsimp [r]
      nlinarith [hbounds.1]
    have hangle : ((ω + Real.pi / 2 : ℝ) : Real.Angle) =
        (Real.pi : Real.Angle) := by
      congr 1
      rw [hωeq]
      ring
    have hbound₂ := hbounds.2
    rw [hangle] at hbound₂
    have hsinωt : Real.sin (ω - t) = Real.cos t := by
      rw [hωeq, Real.sin_pi_div_two_sub]
    have hcosωt : Real.cos (ω - t) = Real.sin t := by
      rw [hωeq, Real.cos_pi_div_two_sub]
    rw [hsinωt, hcosωt] at hbound₂
    have hlp : l ≤ p 0 := by
      have hptv' := hptv
      simp only [tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe, PiLp.inner_apply,
        RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
        neg_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one, hpy0, mul_zero, add_zero,
        Real.Angle.coe_add, neg_lt_sub_iff_lt_add] at hptv'
      dsimp [l]
      by_contra hp
      have hmul := mul_lt_mul_of_pos_left (lt_of_not_ge hp) hsint
      have hsum : Real.sin t * p 0 + supportValue K.val
          ((t + Real.pi / 2 : ℝ) : Real.Angle) < 1 := by
        calc
          _ < Real.sin t * (-supportValue K.val (Real.pi : Real.Angle)) +
              supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) :=
            by
              simpa [add_comm] using add_lt_add_right hmul
                (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle))
          _ ≤ Real.sin t * (-supportValue K.val (Real.pi : Real.Angle)) +
              (Real.cos t + Real.sin t * supportValue K.val (Real.pi : Real.Angle)) :=
            by
              simpa [add_comm] using
                add_le_add_left hbound₂
                  (Real.sin t * (-supportValue K.val (Real.pi : Real.Angle)))
          _ = Real.cos t := by ring
          _ < 1 := hcost_lt
      exact (not_lt_of_ge hsum.le) hptv'
    have hpEq : p = p 0 • normalVector (0 : Real.Angle) := by
      ext i
      fin_cases i <;> simp [normalVector, frame, hpy0]
    rw [hpEq]
    exact smul_mem_of_mem_of_le_of_le hleft hright hlp hpr
  · have hωlt : ω < Real.pi / 2 := K.property.2.1.lt_of_ne hωeq
    have hzero := zero_mem_cap_of_lt K hωlt
    have hbounds := K.supportValue_upper_bounds ht
    have hcosω : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [K.property.1, Real.pi_pos], hωlt⟩
    rcases hpboundary with hpy0 | hpω0
    · have hpy0' : p 1 = 0 := by
        simpa [normalVector, frame, PiLp.inner_apply] using hpy0
      have hpx0 : 0 ≤ p 0 := by
        have hpω' := hpω
        simp [normalVector, frame, PiLp.inner_apply, hpy0'] at hpω'
        by_contra hneg
        have := mul_neg_of_pos_of_neg hcosω (lt_of_not_ge hneg)
        linarith
      have hsint_lt : Real.sin t < 1 := by
        nlinarith [Real.sin_sq_add_cos_sq t, sq_pos_of_pos hcost]
      have hpxr : p 0 ≤ supportValue K.val (0 : Real.Angle) := by
        have hpt' := hpt
        simp [normalVector, frame, PiLp.inner_apply, hpy0'] at hpt'
        nlinarith [hbounds.1]
      have hpEq : p = p 0 • normalVector (0 : Real.Angle) := by
        ext i
        fin_cases i <;> simp [normalVector, frame, hpy0']
      rw [hpEq]
      exact K.val.convex.smul_mem_of_nonneg_of_le hzero
        (supportValue_zero_smul_normalVector_mem K) hpx0 hpxr
    · let μ := inner ℝ p (tangentVector (ω : Real.Angle))
      have hpEq : μ • tangentVector (ω : Real.Angle) = p := by
        have hframe := inner_normalVector_smul_add_inner_tangentVector_smul
          p (ω : Real.Angle)
        rw [hpω0, zero_smul, zero_add] at hframe
        exact hframe
      have hμ0 : 0 ≤ μ := by
        have hp1 := congrArg (fun x : Point ↦ x 1) hpEq
        change μ * Real.cos ω = p 1 at hp1
        have hpy' : 0 ≤ p 1 := by
          simpa [normalVector, frame, PiLp.inner_apply] using hpy
        rw [← hp1] at hpy'
        by_contra hneg
        have := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hcosω
        linarith
      have hsinδ_lt : Real.sin (ω - t) < 1 := by
        nlinarith only [Real.sin_sq_add_cos_sq (ω - t), sq_pos_of_pos hcosδ]
      have htv : inner ℝ (tangentVector (ω : Real.Angle))
          (tangentVector (t : Real.Angle)) = Real.cos (ω - t) := by
        simp [tangentVector, frame, PiLp.inner_apply, Real.cos_sub]
        ring
      have hμL : μ ≤ supportValue K.val
          ((ω + Real.pi / 2 : ℝ) : Real.Angle) := by
        have hptv' := hptv
        rw [← hpEq, real_inner_smul_left, htv] at hptv'
        nlinarith [hbounds.2]
      rw [← hpEq]
      exact K.val.convex.smul_mem_of_nonneg_of_le hzero
        (supportValue_add_pi_div_two_smul_tangentVector_mem_of_lt K hωlt) hμ0 hμL

theorem capWedge_subset_of_innerCorner_mem {ω : ℝ} (K : CapSpace ω)
    (t : ℝ) (ht : t ∈ Set.Ioo 0 ω)
    (hz : (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner ∈
      (K.val : Set Point)) :
    capWedge K t ⊆ (K.val : Set Point) := by
  intro q hq
  rcases hq with ⟨hqFan, hqQuad⟩
  let z := (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner
  change z ∈ (K.val : Set Point) at hz
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
  have hzu : inner ℝ z (normalVector (t : Real.Angle)) =
      supportValue K.val (t : Real.Angle) - 1 := by
    have h := inner_supportingPlacement_normalVector (K.val : Set Point)
      (t : Real.Angle) (0 : Point)
    simpa [z, rotatingHallwayParts, hallwayParts] using h
  have hzv : inner ℝ z (tangentVector (t : Real.Angle)) =
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    have h := inner_supportingPlacement_tangentVector (K.val : Set Point)
      (t : Real.Angle) (0 : Point)
    simpa [z, rotatingHallwayParts, hallwayParts] using h
  let d := q - z
  have hdu : inner ℝ d (normalVector (t : Real.Angle)) < 0 := by
    change inner ℝ (q - z) (normalVector (t : Real.Angle)) < 0
    rw [inner_sub_left]
    linarith [hqQuad.1, hzu]
  have hdv : inner ℝ d (tangentVector (t : Real.Angle)) < 0 := by
    change inner ℝ (q - z) (tangentVector (t : Real.Angle)) < 0
    rw [inner_sub_left]
    linarith [hqQuad.2, hzv]
  have hdφ (φ : ℝ) : inner ℝ d (normalVector (φ : Real.Angle)) =
      inner ℝ d (normalVector (t : Real.Angle)) * Real.cos (φ - t) +
        inner ℝ d (tangentVector (t : Real.Angle)) * Real.sin (φ - t) := by
    have hframe := inner_normalVector_smul_add_inner_tangentVector_smul
      d (t : Real.Angle)
    nth_rewrite 1 [← hframe]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have hcos : Real.cos (t - φ) = Real.cos (φ - t) := by
      rw [show t - φ = -(φ - t) by ring, Real.cos_neg]
    rw [inner_normalVector_normalVector, hcos]
    have hsin : inner ℝ (tangentVector (t : Real.Angle))
        (normalVector (φ : Real.Angle)) = Real.sin (φ - t) := by
      simp [normalVector, tangentVector, frame, PiLp.inner_apply, Real.sin_sub]
      ring
    rw [hsin]
  have hsint : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [ht.2, K.property.2.1, Real.pi_pos])
  have hcost : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_le K.property.2.1⟩
  have hsinδ : 0 < Real.sin (ω - t) := Real.sin_pos_of_pos_of_lt_pi
    (sub_pos.mpr ht.2) (by linarith [ht.1, K.property.2.1, Real.pi_pos])
  have hcosδ : 0 < Real.cos (ω - t) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [sub_pos.mpr ht.2, Real.pi_pos],
      by linarith [ht.1, K.property.2.1]⟩
  have hdy : inner ℝ d (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) < 0 := by
    rw [hdφ, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    exact add_neg (mul_neg_of_neg_of_pos hdu hsint) (mul_neg_of_neg_of_pos hdv hcost)
  have hdω : inner ℝ d (normalVector (ω : Real.Angle)) < 0 := by
    rw [hdφ]
    exact add_neg (mul_neg_of_neg_of_pos hdu hcosδ)
      (mul_neg_of_neg_of_pos hdv hsinδ)
  have hqy : 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) := hqFan.2
  have hqω : 0 ≤ inner ℝ q (normalVector (ω : Real.Angle)) := hqFan.1
  obtain ⟨s, hs, hpy, hpω, hpboundary⟩ := exists_lineMap_fan_boundary z q
    (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) (normalVector (ω : Real.Angle))
    hqy hqω (by simpa only [d] using hdy) (by simpa only [d] using hdω)
  let p := AffineMap.lineMap z q s
  change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hpy
  change 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)) at hpω
  change inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 ∨
    inner ℝ p (normalVector (ω : Real.Angle)) = 0 at hpboundary
  have hspos : 0 < s := zero_lt_one.trans_le hs
  have hpt : inner ℝ p (normalVector (t : Real.Angle)) <
      supportValue K.val (t : Real.Angle) - 1 := by
    rw [inner_lineMap]
    have hdiff : inner ℝ q (normalVector (t : Real.Angle)) -
        inner ℝ z (normalVector (t : Real.Angle)) =
        inner ℝ d (normalVector (t : Real.Angle)) := by
      change _ = inner ℝ (q - z) (normalVector (t : Real.Angle))
      rw [inner_sub_left]
    rw [hdiff, hzu]
    have := mul_neg_of_pos_of_neg hspos hdu
    linarith
  have hptv : inner ℝ p (tangentVector (t : Real.Angle)) <
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    have hpinner := inner_lineMap z q (tangentVector (t : Real.Angle)) s
    change inner ℝ p (tangentVector (t : Real.Angle)) = _ at hpinner
    rw [hpinner]
    have hdiff : inner ℝ q (tangentVector (t : Real.Angle)) -
        inner ℝ z (tangentVector (t : Real.Angle)) =
        inner ℝ d (tangentVector (t : Real.Angle)) := by
      change _ = inner ℝ (q - z) (tangentVector (t : Real.Angle))
      rw [inner_sub_left]
    rw [hdiff, hzv]
    have := mul_neg_of_pos_of_neg hspos hdv
    linarith
  have hpFan : p ∈ capFan ω := ⟨hpω, hpy⟩
  have hqp : q ∈ segment ℝ z p := mem_segment_lineMap_of_one_le z q hs
  have hpK := cap_fan_boundary_mem K t ht p hpy hpω hpboundary hpt hptv
  exact K.val.convex.segment_subset hz hpK hqp

end MovingSofa

end

end

end
