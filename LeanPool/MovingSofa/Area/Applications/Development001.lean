/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Infrastructure.Analysis.Foundations.Development004
public import LeanPool.MovingSofa.Bounds.Foundations.Development005
public import LeanPool.MovingSofa.Cap.Foundations.Development003
public import LeanPool.MovingSofa.Cap.Foundations.Development007
public import LeanPool.MovingSofa.Infrastructure.MathlibExtensions.Foundations.Development001
/-!
# Moving sofa: related mathematical developments

* `Area.Middle`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-! # The middle part of the niche

`capMiddle_area_lower_bound` bounds the area of the part of a special cap's niche outside both
distinguished tail half-planes from below by the three signed areas of the middle fan: the two
wedge triangles and the inner-corner arc.

The geometry is that of the paper's proof.  Writing `φ` for the right distinguished angle,
`l = π/2 - φ` for the left one and `k = tan φ`, the two distinguished tail support lines are
`X = w - k y` and `X = z + k y`, where `w` and `z` are the horizontal coordinates of the two fan
points `W` and `Z`; the inner corner runs from the first line to the second through the open cone
between them, with strictly decreasing horizontal coordinate.  Adding a base line `y = -h` strictly
below the arc turns the arc together with the two side segments into a strictly monotone
three-piece roof over that base line, and the region under the roof exceeds the base trapezoid by
the asserted three signed areas.  Every point of the open region above the trapezoid lies in the
niche, because the roof point vertically above it exhibits a time whose open inward quadrant
contains it.
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The middle area bound obtained from cap area, endpoint segments and the corner-path
integral. -/
def upperBoundMiddle (K : SpecialCapSpace) : ℝ :=
  ClassicalResults.area (K.val.val : Set Point) +
    segmentArea (distinguishedCapSides K.val).2.fanPoint
      (distinguishedCapSides K.val).2.corner -
    curveAreaFunctional (capMiddleBV K) +
    segmentArea (distinguishedCapSides K.val).1.corner
      (distinguishedCapSides K.val).1.fanPoint

/-! ### Arithmetic of a side segment of the middle cone

The two side segments of the four-piece loop run along the two tail support lines, so their
displacements `(Δ₀, Δ₁)` satisfy `Δ₀ cos = Δ₁ sin` for the relevant frame angle.  The two lemmas
below are the resulting sign computations for a point `δ` below such a segment. -/

/-- On a segment parallel to the frame tangent, the frame's normal coordinate of a point below the
segment is the vertical drop only. -/
private theorem segment_cross_eq {cs sn Δ0 Δ1 u δ : ℝ} (hΔ : Δ0 * cs = Δ1 * sn) :
    u * Δ0 * cs + (-(u * Δ1) - δ) * sn = -(δ * sn) := by linear_combination u * hΔ

/-- On a segment parallel to the frame tangent, the frame's tangent coordinate of a point below the
segment is negative. -/
private theorem segment_normal_neg {cs sn Δ0 Δ1 u δ : ℝ} (hcs : 0 < cs)
    (hpy : sn ^ 2 + cs ^ 2 = 1) (hΔ : Δ0 * cs = Δ1 * sn) (hΔ1 : 0 < Δ1)
    (hu0 : 0 ≤ u) (hδ : 0 < δ) :
    -(u * Δ0) * sn + (-(u * Δ1) - δ) * cs < 0 := by
  have key : (-(u * Δ0) * sn + (-(u * Δ1) - δ) * cs) * cs = -(u * Δ1) - δ * cs ^ 2 := by
    linear_combination (-(u * sn)) * hΔ + (-(u * Δ1)) * hpy
  have hneg : (-(u * Δ0) * sn + (-(u * Δ1) - δ) * cs) * cs < 0 * cs := by
    rw [key, zero_mul]
    have h1 : 0 ≤ u * Δ1 := mul_nonneg hu0 hΔ1.le
    have h2 : 0 < δ * cs ^ 2 := mul_pos hδ (pow_pos hcs 2)
    linarith
  exact lt_of_mul_lt_mul_right hneg hcs.le

/-! ### The cone between the two distinguished tail support lines -/

/-- Both distinguished fan points lie on the horizontal axis, at the horizontal intercepts of the
two distinguished tail support lines. -/
private theorem distinguishedCapSides_fanPoint_coordinates (K : SpecialCapSpace) :
    (distinguishedCapSides K.val).1.fanPoint 0 =
        (supportValue (K.val.val : Set Point) (paperGerverConstants.2.1 : Real.Angle) - 1) /
          Real.cos paperGerverConstants.2.1 ∧
      (distinguishedCapSides K.val).1.fanPoint 1 = 0 ∧
      (distinguishedCapSides K.val).2.fanPoint 0 =
        -((supportValue (K.val.val : Set Point)
              ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos paperGerverConstants.2.1) ∧
      (distinguishedCapSides K.val).2.fanPoint 1 = 0 := by
  obtain ⟨-, -, hsum⟩ := paperGerverConstants_snd_mem_Ioo
  have hsinl : Real.sin paperGerverConstants.2.2 = Real.cos paperGerverConstants.2.1 := by
    rw [show paperGerverConstants.2.2 = Real.pi / 2 - paperGerverConstants.2.1 by linarith,
      Real.sin_pi_div_two_sub]
  obtain ⟨hW0, hW1⟩ := wedgeEndpoints_fst_coords K.val paperGerverConstants.2.1
  obtain ⟨hZ0, hZ1⟩ := wedgeEndpoints_snd_coords K.val paperGerverConstants.2.2
  rw [hsinl] at hZ0
  rw [distinguishedCapSides_fst_fanPoint, distinguishedCapSides_snd_fanPoint]
  exact ⟨hW0, hW1, hZ0, hZ1⟩

/-- The left fan point lies strictly to the left of the right one: otherwise the right fan point
would lie in the cap and in both tail half-planes, which the separation lemma forbids. -/
private theorem distinguishedCapSides_fanPoint_fst_lt (K : SpecialCapSpace) :
    (distinguishedCapSides K.val).2.fanPoint 0 < (distinguishedCapSides K.val).1.fanPoint 0 := by
  obtain ⟨hrIoo, -, hsum⟩ := paperGerverConstants_snd_mem_Ioo
  obtain ⟨hW0, hW1, hZ0, -⟩ := distinguishedCapSides_fanPoint_coordinates K
  have hcosr : 0 < Real.cos paperGerverConstants.2.1 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hrIoo.1], hrIoo.2⟩
  have hsinl : Real.sin paperGerverConstants.2.2 = Real.cos paperGerverConstants.2.1 := by
    rw [show paperGerverConstants.2.2 = Real.pi / 2 - paperGerverConstants.2.1 by linarith,
      Real.sin_pi_div_two_sub]
  have hcosladd : Real.cos (paperGerverConstants.2.2 + Real.pi / 2) =
      -Real.cos paperGerverConstants.2.1 := by
    rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, hsinl]
    ring
  have hsr1 : supportValue (K.val.val : Set Point)
      (paperGerverConstants.2.1 : Real.Angle) - 1 =
      (distinguishedCapSides K.val).1.fanPoint 0 * Real.cos paperGerverConstants.2.1 := by
    rw [hW0]
    field_simp
  have hsl1 : supportValue (K.val.val : Set Point)
      ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1 =
      -((distinguishedCapSides K.val).2.fanPoint 0 * Real.cos paperGerverConstants.2.1) := by
    rw [hZ0]
    field_simp
  by_contra hcon
  rw [not_lt] at hcon
  have hmul := mul_le_mul_of_nonneg_right hcon hcosr.le
  have h1 : (distinguishedCapSides K.val).1.fanPoint ∈
      (distinguishedCapSides K.val).1.upperHalfPlane := by
    show _ ≤ inner ℝ _ (normalVector (paperGerverConstants.2.1 : Real.Angle))
    rw [inner_normalVector_real, hW1, hsr1]
    simp
  have h2 : (distinguishedCapSides K.val).1.fanPoint ∈
      (distinguishedCapSides K.val).2.upperHalfPlane := by
    show _ ≤ inner ℝ _
      (normalVector ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle))
    rw [inner_normalVector_real, hW1, hcosladd, hsl1]
    linarith only [hmul]
  exact Set.eq_empty_iff_forall_notMem.mp (cap_and_niche_tail_separation K).1 _
    ⟨⟨(specialCap_wedgeEndpoints_in_bottomEdge K).1.1.1, h1⟩, h2⟩

/-- The inner corner traverses the closed cone between the two distinguished tail support lines
`X = w - k y` and `X = z + k y` on the middle interval, with its two endpoints on the two lines.
Here `k = tan φ` is encoded by `hk`, and `w`, `z` by the two intercept equations. -/
private theorem capInnerCorner_mem_cone (K : SpecialCapSpace) {k w z : ℝ}
    (hk : k * Real.cos paperGerverConstants.2.1 = Real.sin paperGerverConstants.2.1)
    (hw : supportValue (K.val.val : Set Point) (paperGerverConstants.2.1 : Real.Angle) - 1 =
      w * Real.cos paperGerverConstants.2.1)
    (hz : supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1 =
      -(z * Real.cos paperGerverConstants.2.1)) :
    capInnerCorner K.val paperGerverConstants.2.1 0 +
        k * capInnerCorner K.val paperGerverConstants.2.1 1 = w ∧
      capInnerCorner K.val paperGerverConstants.2.2 0 -
        k * capInnerCorner K.val paperGerverConstants.2.2 1 = z ∧
      (∀ t ∈ Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2,
        capInnerCorner K.val t 0 + k * capInnerCorner K.val t 1 ≤ w) ∧
      (∀ t ∈ Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2,
        z ≤ capInnerCorner K.val t 0 - k * capInnerCorner K.val t 1) := by
  obtain ⟨hrIoo, hlIoo, hsum⟩ := paperGerverConstants_snd_mem_Ioo
  set r : ℝ := paperGerverConstants.2.1 with hrdef
  set l : ℝ := paperGerverConstants.2.2 with hldef
  set xc : ℝ → Point := capInnerCorner K.val with hxcdef
  have hcosr : 0 < Real.cos r :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hrIoo.1], hrIoo.2⟩
  have hsinl : Real.sin l = Real.cos r := by
    rw [show l = Real.pi / 2 - r by linarith, Real.sin_pi_div_two_sub]
  have hcosl : Real.cos l = Real.sin r := by
    rw [show l = Real.pi / 2 - r by linarith, Real.cos_pi_div_two_sub]
  have hcosladd : Real.cos (l + Real.pi / 2) = -Real.cos r := by
    rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, hsinl]
    ring
  have hsinladd : Real.sin (l + Real.pi / 2) = Real.sin r := by
    rw [Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two, hcosl]
    ring
  -- the right endpoint is on the right line, the left endpoint on the left line
  have hXR : xc r 0 + k * xc r 1 = w := by
    have h := inner_capInnerCorner_normalVector K.val r
    rw [inner_normalVector_real, hw] at h
    refine mul_right_cancel₀ (ne_of_gt hcosr) ?_
    linear_combination h + xc r 1 * hk
  have hXL : xc l 0 - k * xc l 1 = z := by
    have h := inner_capInnerCorner_tangentVector K.val l
    rw [inner_tangentVector_real, hsinl, hcosl, hz] at h
    refine mul_right_cancel₀ (ne_of_gt hcosr) ?_
    linear_combination -h - xc l 1 * hk
  -- strictly inside the cone away from the two endpoints, by the monotonicity intervals
  obtain ⟨hmonoR, hmonoL, -, -⟩ := cap_tail_monotonicity_intervals K
  have hnotR : ∀ t ∈ Set.Ioc r (Real.pi / 2), xc t 0 + k * xc t 1 < w := by
    intro t ht
    have h : ¬ (supportValue (K.val.val : Set Point) (r : Real.Angle) - 1 ≤
        inner ℝ (xc t) (normalVector (r : Real.Angle))) :=
      fun hc ↦ (hmonoR t ht).1 hc
    rw [not_le, inner_normalVector_real, hw] at h
    refine lt_of_mul_lt_mul_right ?_ hcosr.le
    have he : (xc t 0 + k * xc t 1) * Real.cos r =
        xc t 0 * Real.cos r + xc t 1 * Real.sin r := by
      linear_combination xc t 1 * hk
    rw [he]
    exact h
  have hnotL : ∀ t ∈ Set.Ico (0 : ℝ) l, z < xc t 0 - k * xc t 1 := by
    intro t ht
    have h : ¬ (supportValue (K.val.val : Set Point) ((l + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
        inner ℝ (xc t) (normalVector ((l + Real.pi / 2 : ℝ) : Real.Angle))) :=
      fun hc ↦ (hmonoL t ht).1 hc
    rw [not_le, inner_normalVector_real, hcosladd, hsinladd, hz] at h
    refine lt_of_mul_lt_mul_right ?_ hcosr.le
    have he2 : (xc t 0 - k * xc t 1) * Real.cos r =
        xc t 0 * Real.cos r - xc t 1 * Real.sin r := by
      linear_combination -(xc t 1) * hk
    rw [he2]
    linarith only [h]
  refine ⟨hXR, hXL, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · rcases eq_or_lt_of_le ht.1 with heq | hlt
    · rw [← heq, hXR]
    · exact (hnotR t ⟨hlt, le_trans ht.2 hlIoo.2.le⟩).le
  · rcases eq_or_lt_of_le ht.2 with heq | hlt
    · rw [heq, hXL]
    · exact (hnotL t ⟨le_trans hrIoo.1.le ht.1, hlt⟩).le

/-- A horizontal line strictly below the inner corner on a compact subinterval of `[0, π/2]`. -/
private theorem exists_lt_capInnerCorner_snd (K : SpecialCapSpace) {a b : ℝ} (hab : a ≤ b)
    (ha : 0 ≤ a) (hb : b ≤ Real.pi / 2) :
    ∃ h : ℝ, 0 < h ∧ ∀ t ∈ Set.Icc a b, -h < capInnerCorner K.val t 1 := by
  have hsub : Set.Icc a b ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) := fun t ht ↦
    ⟨le_trans ha ht.1, le_trans ht.2 hb⟩
  have hcont : ContinuousOn (fun t ↦ capInnerCorner K.val t 1) (Set.Icc a b) :=
    (PiLp.continuous_apply 2 _ 1).comp_continuousOn (K.property.1.2.1.continuousOn.mono hsub)
  obtain ⟨t0, -, hmin⟩ := isCompact_Icc.exists_isMinOn (⟨a, le_rfl, hab⟩ : (Set.Icc a b).Nonempty)
    hcont
  refine ⟨|capInnerCorner K.val t0 1| + 1, by positivity, fun t ht ↦ ?_⟩
  have hle : capInnerCorner K.val t0 1 ≤ capInnerCorner K.val t 1 := hmin ht
  linarith only [hle, neg_abs_le (capInnerCorner K.val t0 1)]

/-- The area of the trapezoid cut from the strip `-h ≤ y ≤ 0` by two lines of opposite slope
meeting the horizontal axis at `z` and `w`. -/
private theorem volume_slantedTrapezoid {z w k h : ℝ} (hk : 0 ≤ k) (hzw : z ≤ w) (hh : 0 ≤ h) :
    MeasureTheory.volume {p : Point | p 1 ∈ Set.Icc (-h) 0 ∧
        p 0 ∈ Set.Icc (z + k * p 1) (w - k * p 1)} =
      ENNReal.ofReal (h * (w - z) + k * h ^ 2) := by
  have hkh : 0 ≤ k * h := mul_nonneg hk hh
  rw [show {p : Point | p 1 ∈ Set.Icc (-h) 0 ∧
        p 0 ∈ Set.Icc (z + k * p 1) (w - k * p 1)} =
      {p : Point | p 1 ∈ Set.Icc (-h) 0 ∧
        p 0 ∈ Set.Icc (z + k * p 1) (w + -k * p 1)} from by
      refine Set.ext fun p ↦ ?_
      simp only [Set.mem_ofPred_eq, show w + -k * p 1 = w - k * p 1 from by ring],
    EuclideanSpace.volume_horizontalTrapezoid_band (by linarith) (by linarith) (by linarith)]
  congr 1
  ring

/-! ### The niche contains the open region above the base trapezoid -/

/-- Every point strictly below the three-piece roof made of the inner-corner arc and the two side
segments, and outside the base trapezoid, lies in the niche outside both distinguished tail
half-planes.  The roof point vertically above such a point exhibits a time of the closed middle
interval whose open inward quadrant contains it, and the strict cone bounds plus the point's
positive height put it in the fan and outside the two half-planes. -/
private theorem region_under_roof_diff_subset (K : SpecialCapSpace) {k w z h : ℝ} (hk0 : 0 < k)
    (hk : k * Real.cos paperGerverConstants.2.1 = Real.sin paperGerverConstants.2.1)
    (hw : supportValue (K.val.val : Set Point) (paperGerverConstants.2.1 : Real.Angle) - 1 =
      w * Real.cos paperGerverConstants.2.1)
    (hz : supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1 =
      -(z * Real.cos paperGerverConstants.2.1))
    (P Q : Point) (γ : ContinuousBVPaths 0 3) (hP1 : P 1 = -h) (hQ1 : Q 1 = -h)
    (hγ0 : ∀ s : Set.Icc (0 : ℝ) 3, (s : ℝ) ≤ 1 →
      γ.val s = P + (s : ℝ) • (capInnerCorner K.val paperGerverConstants.2.2 - P))
    (hγ1 : ∀ s : Set.Icc (0 : ℝ) 3, 1 ≤ (s : ℝ) → (s : ℝ) ≤ 2 →
      γ.val s = capInnerCorner K.val (paperGerverConstants.2.2 +
        ((s : ℝ) - 1) * (paperGerverConstants.2.1 - paperGerverConstants.2.2)))
    (hγ2 : ∀ s : Set.Icc (0 : ℝ) 3, 2 ≤ (s : ℝ) →
      γ.val s = capInnerCorner K.val paperGerverConstants.2.1 +
        ((s : ℝ) - 2) • (Q - capInnerCorner K.val paperGerverConstants.2.1))
    (hconeR : ∀ s : Set.Icc (0 : ℝ) 3, γ.val s 0 + k * γ.val s 1 ≤ w)
    (hconeL : ∀ s : Set.Icc (0 : ℝ) 3, z ≤ γ.val s 0 - k * γ.val s 1)
    (hPpar : (capInnerCorner K.val paperGerverConstants.2.2 0 - P 0) *
        Real.cos paperGerverConstants.2.1 =
      (capInnerCorner K.val paperGerverConstants.2.2 1 - P 1) *
        Real.sin paperGerverConstants.2.1)
    (hQpar : (Q 0 - capInnerCorner K.val paperGerverConstants.2.1 0) *
        Real.cos paperGerverConstants.2.1 =
      (capInnerCorner K.val paperGerverConstants.2.1 1 - Q 1) *
        Real.sin paperGerverConstants.2.1) :
    {p : Point | ∃ s : Set.Icc (0 : ℝ) 3, p 0 = γ.val s 0 ∧ -h < p 1 ∧ p 1 < γ.val s 1} \
        {p : Point | p 1 ∈ Set.Icc (-h) 0 ∧ p 0 ∈ Set.Icc (z + k * p 1) (w - k * p 1)} ⊆
      (capNiche K.val \ (distinguishedCapSides K.val).1.upperHalfPlane) \
        (distinguishedCapSides K.val).2.upperHalfPlane := by
  obtain ⟨hrIoo, hlIoo, hsum⟩ := paperGerverConstants_snd_mem_Ioo
  set r : ℝ := paperGerverConstants.2.1 with hrdef
  set l : ℝ := paperGerverConstants.2.2 with hldef
  set xc : ℝ → Point := capInnerCorner K.val with hxcdef
  have hrl : r < l := paperGerverConstants_snd_fst_lt_snd_snd
  have hcosr : 0 < Real.cos r :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hrIoo.1], hrIoo.2⟩
  have hsinr : 0 < Real.sin r :=
    Real.sin_pos_of_pos_of_lt_pi hrIoo.1 (by linarith [Real.pi_pos, hrIoo.2])
  have hpy : Real.sin r ^ 2 + Real.cos r ^ 2 = 1 := Real.sin_sq_add_cos_sq r
  have hsinl : Real.sin l = Real.cos r := by
    rw [show l = Real.pi / 2 - r by linarith, Real.sin_pi_div_two_sub]
  have hcosl : Real.cos l = Real.sin r := by
    rw [show l = Real.pi / 2 - r by linarith, Real.cos_pi_div_two_sub]
  have hcosladd : Real.cos (l + Real.pi / 2) = -Real.cos r := by
    rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, hsinl]
    ring
  have hsinladd : Real.sin (l + Real.pi / 2) = Real.sin r := by
    rw [Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two, hcosl]
    ring
  have hcoord : ∀ (p q : Point) (c : ℝ) (i : Fin 2),
      (p + c • (q - p)) i = p i + c * (q i - p i) := fun _ _ _ _ ↦ by simp
  rintro p ⟨hpP, hpR⟩
  obtain ⟨s, hs0, hs1, hs2⟩ := hpP
  obtain ⟨δ, hδ0, hδeq⟩ : ∃ δ : ℝ, 0 < δ ∧ p 1 = γ.val s 1 - δ :=
    ⟨γ.val s 1 - p 1, by linarith only [hs2], by ring⟩
  have hkp : k * p 1 < k * γ.val s 1 := mul_lt_mul_of_pos_left hs2 hk0
  -- the point is strictly inside the open cone
  have hstrictR : p 0 + k * p 1 < w := by
    have h := hconeR s
    rw [hs0]
    linarith only [h, hkp]
  have hstrictL : z < p 0 - k * p 1 := by
    have h := hconeL s
    rw [hs0]
    linarith only [h, hkp]
  -- being outside the trapezoid, its height is positive
  have hp1pos : 0 < p 1 := by
    by_contra hcon
    rw [not_lt] at hcon
    exact hpR ⟨⟨hs1.le, hcon⟩, ⟨by linarith only [hstrictL], by linarith only [hstrictR]⟩⟩
  have hnotHR : p ∉ (distinguishedCapSides K.val).1.upperHalfPlane := by
    intro hc
    replace hc : supportValue (K.val.val : Set Point) (r : Real.Angle) - 1 ≤
      inner ℝ p (normalVector (r : Real.Angle)) := hc
    rw [inner_normalVector_real, hw] at hc
    have hm : (p 0 + k * p 1) * Real.cos r < w * Real.cos r :=
      mul_lt_mul_of_pos_right hstrictR hcosr
    have he : (p 0 + k * p 1) * Real.cos r = p 0 * Real.cos r + p 1 * Real.sin r := by
      linear_combination p 1 * hk
    rw [he] at hm
    linarith only [hc, hm]
  have hnotHL : p ∉ (distinguishedCapSides K.val).2.upperHalfPlane := by
    intro hc
    replace hc : supportValue (K.val.val : Set Point) ((l + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
      inner ℝ p (normalVector ((l + Real.pi / 2 : ℝ) : Real.Angle)) := hc
    rw [inner_normalVector_real, hcosladd, hsinladd, hz] at hc
    have hm : z * Real.cos r < (p 0 - k * p 1) * Real.cos r :=
      mul_lt_mul_of_pos_right hstrictL hcosr
    have he : (p 0 - k * p 1) * Real.cos r = p 0 * Real.cos r - p 1 * Real.sin r := by
      linear_combination -(p 1) * hk
    rw [he] at hm
    linarith only [hc, hm]
  have hfan : p ∈ capFan (Real.pi / 2) := by
    refine ⟨?_, ?_⟩ <;>
      · show (0 : ℝ) ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
        rw [inner_normalVector_pi_div_two]
        exact hp1pos.le
  -- the roof point above `p` provides the time whose inward quadrant contains `p`
  have hquad : ∃ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      p ∈ innerQuadrant (K.val.val : Set Point) t := by
    rcases le_or_gt (s : ℝ) 1 with hc | hc
    · -- the left side segment, with witness time `l`
      have hγs1 : γ.val s 1 = P 1 + (s : ℝ) * (xc l 1 - P 1) := by
        rw [hγ0 s hc, hcoord]
      have hΔ1 : 0 < xc l 1 - P 1 := by
        nlinarith only [hγs1, hs1, hs2, hP1, s.property.1]
      have hΔ : (xc l 0 - P 0) * Real.sin l = (xc l 1 - P 1) * Real.cos l := by
        rw [hsinl, hcosl]
        exact hPpar
      have e0 : p 0 - xc l 0 = -((1 - (s : ℝ)) * (xc l 0 - P 0)) := by
        rw [hs0, hγ0 s hc, hcoord]
        ring
      have e1 : p 1 - xc l 1 = -((1 - (s : ℝ)) * (xc l 1 - P 1)) - δ := by
        rw [hδeq, hγ0 s hc, hcoord]
        ring
      refine ⟨l, ⟨hlIoo.1, hlIoo.2⟩, mem_innerQuadrant_of_frame_coordinates_neg K.val l p ?_ ?_⟩
      · rw [e0, e1]
        have hnn := segment_normal_neg (cs := Real.sin l) (sn := Real.cos l)
          (u := 1 - (s : ℝ)) (δ := δ) (by rw [hsinl]; exact hcosr)
          (by rw [hsinl, hcosl]; linarith only [hpy]) hΔ hΔ1 (by linarith only [hc]) hδ0
        linarith only [hnn]
      · rw [e0, e1]
        have hcr := segment_cross_eq (cs := Real.sin l) (sn := Real.cos l)
          (u := 1 - (s : ℝ)) (δ := δ) hΔ
        have hps : 0 < δ * Real.cos l := by
          rw [hcosl]
          exact mul_pos hδ0 hsinr
        linarith only [hcr, hps]
    · rcases le_or_gt (s : ℝ) 2 with hc2 | hc2
      · -- the middle arc, with witness time in `[r, l]`
        have htI := mem_Icc_roofArcTime hrl hc.le hc2
        set t : ℝ := l + ((s : ℝ) - 1) * (r - l) with htdef
        have hgs : γ.val s = xc t := hγ1 s hc.le hc2
        have e0 : p 0 - xc t 0 = 0 := by rw [hs0, hgs]; ring
        have e1 : p 1 - xc t 1 = -δ := by rw [hδeq, hgs]; ring
        have ht0 : 0 < t := lt_of_lt_of_le hrIoo.1 htI.1
        have htpi : t < Real.pi / 2 := lt_of_le_of_lt htI.2 hlIoo.2
        have hsint : 0 < Real.sin t :=
          Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith only [Real.pi_pos, htpi])
        have hcost : 0 < Real.cos t :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith only [Real.pi_pos, ht0], htpi⟩
        refine ⟨t, ⟨ht0, htpi⟩, mem_innerQuadrant_of_frame_coordinates_neg K.val t p ?_ ?_⟩
        · rw [e0, e1]
          have hps := mul_pos hδ0 hsint
          linarith only [hps]
        · rw [e0, e1]
          have hps := mul_pos hδ0 hcost
          linarith only [hps]
      · -- the right side segment, with witness time `r`
        have hγs1 : γ.val s 1 = xc r 1 + ((s : ℝ) - 2) * (Q 1 - xc r 1) := by
          rw [hγ2 s hc2.le, hcoord]
        have hΔ1 : 0 < xc r 1 - Q 1 := by
          nlinarith only [hγs1, hs1, hs2, hQ1, hc2, s.property.2]
        have e0 : p 0 - xc r 0 = ((s : ℝ) - 2) * (Q 0 - xc r 0) := by
          rw [hs0, hγ2 s hc2.le, hcoord]
          ring
        have e1 : p 1 - xc r 1 = -(((s : ℝ) - 2) * (xc r 1 - Q 1)) - δ := by
          rw [hδeq, hγ2 s hc2.le, hcoord]
          ring
        refine ⟨r, ⟨hrIoo.1, hrIoo.2⟩,
          mem_innerQuadrant_of_frame_coordinates_neg K.val r p ?_ ?_⟩
        · rw [e0, e1]
          have hcr := segment_cross_eq (cs := Real.cos r) (sn := Real.sin r)
            (u := (s : ℝ) - 2) (δ := δ) hQpar
          have hps := mul_pos hδ0 hsinr
          linarith only [hcr, hps]
        · rw [e0, e1]
          have hnn := segment_normal_neg (cs := Real.cos r) (sn := Real.sin r)
            (u := (s : ℝ) - 2) (δ := δ) hcosr hpy hQpar hΔ1 (by linarith only [hc2]) hδ0
          linarith only [hnn]
  obtain ⟨t, htmem, hq⟩ := hquad
  exact ⟨⟨⟨hfan, Set.mem_biUnion htmem hq⟩, hnotHR⟩, hnotHL⟩

/-! ### The lower estimate -/

theorem capMiddle_area_lower_bound (K : SpecialCapSpace) :
    segmentArea (distinguishedCapSides K.val).1.fanPoint
        (distinguishedCapSides K.val).1.corner +
      curveAreaFunctional (capMiddleBV K) +
      segmentArea (distinguishedCapSides K.val).2.corner
        (distinguishedCapSides K.val).2.fanPoint ≤
    ClassicalResults.area
      ((capNiche K.val \ (distinguishedCapSides K.val).1.upperHalfPlane) \
        (distinguishedCapSides K.val).2.upperHalfPlane) := by
  obtain ⟨hW0, hW1, hZ0, hZ1⟩ := distinguishedCapSides_fanPoint_coordinates K
  obtain ⟨hrIoo, hlIoo, hsum⟩ := paperGerverConstants_snd_mem_Ioo
  set r : ℝ := paperGerverConstants.2.1 with hrdef
  set l : ℝ := paperGerverConstants.2.2 with hldef
  have hrl : r < l := paperGerverConstants_snd_fst_lt_snd_snd
  have hcosr : 0 < Real.cos r :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hrIoo.1], hrIoo.2⟩
  have hsinr : 0 < Real.sin r :=
    Real.sin_pos_of_pos_of_lt_pi hrIoo.1 (by linarith [Real.pi_pos, hrIoo.2])
  -- the cone's slope `k = tan φ` and the horizontal intercepts `w`, `z` of its two lines
  set kk : ℝ := Real.sin r / Real.cos r with hkkdef
  have hkk0 : 0 < kk := div_pos hsinr hcosr
  have hkcos : kk * Real.cos r = Real.sin r := by
    rw [hkkdef]
    field_simp
  set xc : ℝ → Point := capInnerCorner K.val with hxcdef
  set W : Point := (distinguishedCapSides K.val).1.fanPoint with hWdef
  set Z : Point := (distinguishedCapSides K.val).2.fanPoint with hZdef
  have hsr1 : supportValue (K.val.val : Set Point) (r : Real.Angle) - 1 = W 0 * Real.cos r := by
    rw [hW0, div_mul_cancel₀ _ (ne_of_gt hcosr)]
  have hsl1 : supportValue (K.val.val : Set Point) ((l + Real.pi / 2 : ℝ) : Real.Angle) - 1 =
      -(Z 0 * Real.cos r) := by
    rw [hZ0, neg_mul, div_mul_cancel₀ _ (ne_of_gt hcosr), neg_neg]
  have hzw : Z 0 < W 0 := distinguishedCapSides_fanPoint_fst_lt K
  -- the arc runs through the closed cone from one boundary line to the other
  obtain ⟨hXR, hXL, harcR, harcL⟩ := capInnerCorner_mem_cone K hkcos hsr1 hsl1
  -- a base line `y = -hgt` strictly below the arc, and the two base corners on it
  obtain ⟨hgt, hgt0, hgtlow⟩ := exists_lt_capInnerCorner_snd K hrl.le hrIoo.1.le hlIoo.2.le
  have hkh : (0 : ℝ) ≤ kk * hgt := mul_nonneg hkk0.le hgt0.le
  set Bp : Point := !₂[W 0 + kk * hgt, -hgt] with hBpdef
  set Dp : Point := !₂[Z 0 - kk * hgt, -hgt] with hDpdef
  have hBp0 : Bp 0 = W 0 + kk * hgt := rfl
  have hBp1 : Bp 1 = -hgt := rfl
  have hDp0 : Dp 0 = Z 0 - kk * hgt := rfl
  have hDp1 : Dp 1 = -hgt := rfl
  -- the three-piece roof `Dp → x(l) → arc → x(r) → Bp`
  obtain ⟨γ, hγ0, hγ1, hγ2, hγmono⟩ :=
    exists_strictMono_roof_of_strictAntiOn hrl (capMiddleBV K) xc Dp Bp (fun _ _ ↦ rfl)
      (strictAntiOn_capInnerCorner_fst K hrIoo.1.le hlIoo.2.le)
      (by
        rw [hDp0]
        have h : 0 < kk * (xc l 1 + hgt) :=
          mul_pos hkk0 (by linarith only [hgtlow l ⟨hrl.le, le_rfl⟩])
        linarith only [hXL, h])
      (by
        rw [hBp0]
        have h : 0 < kk * (xc r 1 + hgt) :=
          mul_pos hkk0 (by linarith only [hgtlow r ⟨le_rfl, hrl.le⟩])
        linarith only [hXR, h])
  -- the roof stays in the closed cone above the base line
  have hγconeR : ∀ s : Set.Icc (0 : ℝ) 3, γ.val s 0 + kk * γ.val s 1 ≤ W 0 := fun s ↦ by
    have h := le_of_threePieceRoof (α := 1) (β := kk) (cc := W 0) hrl xc Dp Bp γ hγ0 hγ1 hγ2
      (by rw [hDp0, hDp1]; linarith only [hzw, hkh])
      (by rw [hBp0, hBp1]; linarith only []) (fun t ht ↦ by linarith only [harcR t ht]) s
    linarith only [h]
  have hγconeL : ∀ s : Set.Icc (0 : ℝ) 3, Z 0 ≤ γ.val s 0 - kk * γ.val s 1 := fun s ↦ by
    have h := le_of_threePieceRoof (α := -1) (β := kk) (cc := -Z 0) hrl xc Dp Bp γ hγ0 hγ1 hγ2
      (by rw [hDp0, hDp1]; linarith only [])
      (by rw [hBp0, hBp1]; linarith only [hzw, hkh])
      (fun t ht ↦ by linarith only [harcL t ht]) s
    linarith only [h]
  have hγlow : ∀ s : Set.Icc (0 : ℝ) 3, -hgt ≤ γ.val s 1 := fun s ↦ by
    have h := le_of_threePieceRoof (α := 0) (β := -1) (cc := hgt) hrl xc Dp Bp γ hγ0 hγ1 hγ2
      (by rw [hDp1]; linarith only []) (by rw [hBp1]; linarith only [])
      (fun t ht ↦ by linarith only [hgtlow t ht]) s
    linarith only [h]
  -- the closed region under the roof and the base trapezoid
  set Pu : Set Point :=
    {p : Point | ∃ s : Set.Icc (0 : ℝ) 3, p 0 = γ.val s 0 ∧ -hgt ≤ p 1 ∧ p 1 ≤ γ.val s 1}
    with hPudef
  set Rg : Set Point :=
    {p : Point | p 1 ∈ Set.Icc (-hgt) 0 ∧ p 0 ∈ Set.Icc (Z 0 + kk * p 1) (W 0 - kk * p 1)}
    with hRgdef
  have hRgarea : MeasureTheory.volume Rg =
      ENNReal.ofReal (hgt * (W 0 - Z 0) + kk * hgt ^ 2) :=
    volume_slantedTrapezoid hkk0.le hzw.le hgt0.le
  have hRgreal : ClassicalResults.area Rg = hgt * (W 0 - Z 0) + kk * hgt ^ 2 := by
    rw [ClassicalResults.area, hRgarea, ENNReal.toReal_ofReal]
    positivity
  -- the four-piece signed area of the loop bounding the region
  have hPuarea : ClassicalResults.area Pu =
      segmentArea Bp (xc r) + curveAreaFunctional (capMiddleBV K) +
        segmentArea (xc l) Dp + segmentArea Dp Bp :=
    area_region_under_strictMono_roof hrl (capMiddleBV K) xc Dp Bp γ (fun _ _ ↦ rfl) hDp1 hBp1
      hγ0 hγ1 hγ2 hγmono hγlow
  -- the strict region above the trapezoid lies in the niche outside both half-planes
  have hincl := region_under_roof_diff_subset K hkk0 hkcos hsr1 hsl1 Dp Bp γ hDp1 hBp1
    hγ0 hγ1 hγ2 hγconeR hγconeL
    (by
      rw [hDp0, hDp1]
      linear_combination Real.cos r * hXL + (xc l 1 + hgt) * hkcos)
    (by
      rw [hBp0, hBp1]
      linear_combination (-Real.cos r) * hXR + (xc r 1 + hgt) * hkcos)
  -- comparing the three areas
  have hTgtfin : MeasureTheory.volume
      ((capNiche K.val \ (distinguishedCapSides K.val).1.upperHalfPlane) \
        (distinguishedCapSides K.val).2.upperHalfPlane) ≠ ⊤ :=
    ne_top_of_le_ne_top (niche_uniform_bounds.1 _ K.val).2.2.1.ne
      (MeasureTheory.measure_mono (Set.sdiff_subset.trans Set.sdiff_subset))
  have hbase : ∀ p : Point, (∃ s : Set.Icc (0 : ℝ) 3, p 0 = γ.val s 0) → p 1 = -hgt → p ∈ Rg := by
    rintro p ⟨s, hs0⟩ hp1
    have h1 : γ.val ⟨0, le_rfl, by norm_num⟩ 0 ≤ γ.val s 0 :=
      hγmono.monotone (show (⟨0, le_rfl, by norm_num⟩ : Set.Icc (0 : ℝ) 3) ≤ s from s.property.1)
    have h2 : γ.val s 0 ≤ γ.val ⟨3, by norm_num, le_rfl⟩ 0 :=
      hγmono.monotone (show s ≤ (⟨3, by norm_num, le_rfl⟩ : Set.Icc (0 : ℝ) 3) from s.property.2)
    rw [show γ.val ⟨0, le_rfl, by norm_num⟩ = Dp from by rw [hγ0 _ (by norm_num)]; simp] at h1
    rw [show γ.val ⟨3, by norm_num, le_rfl⟩ = Bp from by rw [hγ2 _ (by norm_num)]; norm_num] at h2
    rw [hDp0] at h1
    rw [hBp0] at h2
    refine ⟨⟨le_of_eq hp1.symm, by rw [hp1]; linarith only [hgt0]⟩, ?_⟩
    rw [hp1, hs0]
    exact ⟨by linarith only [h1], by linarith only [h2]⟩
  have hreal := area_region_under_roof_le γ hγmono Rg _
    (by rw [hRgarea]; exact ENNReal.ofReal_ne_top) hTgtfin hbase hincl
  -- the signed-area cancellation along the base line
  have harith : segmentArea W (xc r) + curveAreaFunctional (capMiddleBV K) +
      segmentArea (xc l) Z = ClassicalResults.area Pu - ClassicalResults.area Rg := by
    rw [hPuarea, hRgreal]
    simp only [segmentArea, planeCrossProduct, hBp0, hBp1, hDp0, hDp1, hW1, hZ1]
    linear_combination (-(hgt / 2)) * hXR + (hgt / 2) * hXL
  rw [show (distinguishedCapSides K.val).1.corner = xc r from rfl,
    show (distinguishedCapSides K.val).2.corner = xc l from rfl]
  linarith [harith, hreal]

end MovingSofa

end

end

end
