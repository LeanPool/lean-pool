/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.Receding
public import LeanPool.CIVAxisymmetric.Zoom.Algebra

/-!
# Lipschitz-in-space bound for the receding-axis rescaled radial field

The input to the Arzelà–Ascoli extraction of Step 3: on a rectangle `[Ra, Rb] × [Za, Zb]`
contained in the unit cylinder (via `hmem`), the receding-axis rescaled radial field
`V_n` of `eq:aniso:zoom:receding:variables` is Lipschitz in the spatial variables, with a
`τ`-independent constant `2C`.

The proof follows `CIV.Zoom.OmegaLipschitz`'s `abs_zoomOmega_sub_zoomOmega_le` /
`lipschitzOnWith_zoomOmega`: on each coordinate edge of the rectangle, the
mean-value inequality (`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`) applied to the
per-point derivative bounds from `abs_dr_zoomVRec_le` and `abs_dz_zoomVRec_le` gives a
`τ`-uniform bound; the two edges are combined by the triangle inequality.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV



theorem lipschitzOnWith_zoomVRec {C h lam rc zc Ra Rb Za Zb tau : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hC : 0 ≤ C) (hh1 : h ≤ 1 / 2) (htau : tau ≤ -1)
    (hmem : ∀ y ∈ Icc Ra Rb ×ˢ Icc Za Zb, zoomPointRec lam h rc zc (y, tau) ∈ unitCylinder) :
    LipschitzOnWith (Real.toNNReal (2 * C))
      (fun y : ℝ × ℝ => zoomVRec lam h rc zc u (y, tau)) (Icc Ra Rb ×ˢ Icc Za Zb) := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hu.of_le (by norm_num)
  have hL : (0 : ℝ) ≤ 2 * C := mul_nonneg (by norm_num) hC
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro y1 hy1 y2 hy2
  rw [Real.coe_toNNReal _ hL, Real.dist_eq]
  -- simplified exponents from abs_dr_zoomVRec_le / abs_dz_zoomVRec_le
  have hexp_dr : -(1 / 2 : ℝ) - 1 / 2 - (1 / 2 - h) * (0 : ℝ) = (-1 : ℝ) := by ring
  have hexp_dz : -(1 / 2 : ℝ) - (0 : ℝ) / 2 - (1 / 2 - h) * (1 : ℝ) = (-1 + h : ℝ) := by ring
  -- helper: (-tau) ≥ 1
  have h_base : (1 : ℝ) ≤ -tau := by linarith only [htau]
  -- radial derivative bound: |dr(zoomVRec)| ≤ C on the rectangle
  have h_dr_bound (r : ℝ) (hr : r ∈ Icc Ra Rb) :
      |dr (zoomVRec lam h rc zc u) ((r, y1.2), tau)| ≤ C := by
    have hp : zoomPointRec lam h rc zc ((r, y1.2), tau) ∈ unitCylinder :=
      hmem (r, y1.2) ⟨hr, hy1.2⟩
    have hdr := abs_dr_zoomVRec_le C h lam rc zc hlam u hb hu ((r, y1.2), tau) hp
    rw [hexp_dr] at hdr
    -- hdr : |dr| ≤ C * (-((r, y1.2), tau).2) ^ (-1 : ℝ)
    have hpow : (-tau) ^ (-1 : ℝ) ≤ (1 : ℝ) := by
      calc
        (-tau) ^ (-1 : ℝ) ≤ (-tau) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h_base (by norm_num : (-1 : ℝ) ≤ (0 : ℝ))
        _ = 1 := by rw [Real.rpow_zero (-tau)]
    have hstep : C * (-tau) ^ (-1 : ℝ) ≤ C := by
      nlinarith only [hC, hpow]
    -- rewrite ((r, y1.2), tau).2 to tau in hdr
    have h_simp : (-((r, y1.2), tau).2) = (-tau) := by simp
    rw [h_simp] at hdr
    linarith only [hdr, hstep]
  -- vertical derivative bound: |dz(zoomVRec)| ≤ C on the rectangle
  have h_dz_bound (s : ℝ) (hs : s ∈ Icc Za Zb) :
      |dz (zoomVRec lam h rc zc u) ((y2.1, s), tau)| ≤ C := by
    have hp : zoomPointRec lam h rc zc ((y2.1, s), tau) ∈ unitCylinder :=
      hmem (y2.1, s) ⟨hy2.1, hs⟩
    have hdz := abs_dz_zoomVRec_le C h lam rc zc hlam u hb hu ((y2.1, s), tau) hp
    rw [hexp_dz] at hdz
    -- hdz : |dz| ≤ C * (-((y2.1, s), tau).2) ^ (-1 + h : ℝ)
    have hpow : (-tau) ^ (-1 + h) ≤ (1 : ℝ) := by
      calc
        (-tau) ^ (-1 + h) ≤ (-tau) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h_base (by linarith only [hh1])
        _ = 1 := by rw [Real.rpow_zero (-tau)]
    have hstep : C * (-tau) ^ (-1 + h) ≤ C := by
      nlinarith only [hC, hpow]
    have h_simp : (-((y2.1, s), tau).2) = (-tau) := by simp
    rw [h_simp] at hdz
    linarith only [hdz, hstep]
  -- radial edge: y varies, y1.2 and tau fixed
  have hedgeR : |zoomVRec lam h rc zc u ((y2.1, y1.2), tau)
      - zoomVRec lam h rc zc u ((y1.1, y1.2), tau)|
      ≤ C * |y2.1 - y1.1| := by
    have hderiv : ∀ r ∈ Icc Ra Rb,
        HasDerivWithinAt (fun r' : ℝ => zoomVRec lam h rc zc u ((r', y1.2), tau))
          (dr (zoomVRec lam h rc zc u) ((r, y1.2), tau)) (Icc Ra Rb) r := by
      intro r hr
      have hp : zoomPointRec lam h rc zc ((r, y1.2), tau) ∈ unitCylinder :=
        hmem (r, y1.2) ⟨hr, hy1.2⟩
      have h_hasDeriv : HasDerivAt (fun r' : ℝ => zoomVRec lam h rc zc u ((r', y1.2), tau))
          (dr (zoomVRec lam h rc zc u) ((r, y1.2), tau)) r := by
        have h_comp := (hasDerivAt_zoomRec_component_r lam h rc zc hu1 ((r, y1.2), tau) hp
          0).const_mul lam
        have h_val : lam * (lam * spatialPartial (fun w => u w 0) 0
            (zoomPointRec lam h rc zc ((r, y1.2), tau)))
            = dr (zoomVRec lam h rc zc u) ((r, y1.2), tau) := by
          rw [dr_zoomVRec lam h rc zc u hu1 ((r, y1.2), tau) hp]
          ring
        simpa [zoomVRec, h_val] using h_comp
      exact h_hasDeriv.hasDerivWithinAt
    have hbound : ∀ r ∈ Icc Ra Rb,
        ‖dr (zoomVRec lam h rc zc u) ((r, y1.2), tau)‖ ≤ C := by
      intro r hr
      rw [Real.norm_eq_abs]
      exact h_dr_bound r hr
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      (convex_Icc Ra Rb) hy1.1 hy2.1
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
    exact hmvt
  -- vertical edge: s varies, y2.1 and tau fixed
  have hedgeZ : |zoomVRec lam h rc zc u ((y2.1, y2.2), tau)
      - zoomVRec lam h rc zc u ((y2.1, y1.2), tau)|
      ≤ C * |y2.2 - y1.2| := by
    have hderiv : ∀ s ∈ Icc Za Zb,
        HasDerivWithinAt (fun s' : ℝ => zoomVRec lam h rc zc u ((y2.1, s'), tau))
          (dz (zoomVRec lam h rc zc u) ((y2.1, s), tau)) (Icc Za Zb) s := by
      intro s hs
      have hp : zoomPointRec lam h rc zc ((y2.1, s), tau) ∈ unitCylinder :=
        hmem (y2.1, s) ⟨hy2.1, hs⟩
      have h_hasDeriv : HasDerivAt (fun s' : ℝ => zoomVRec lam h rc zc u ((y2.1, s'), tau))
          (dz (zoomVRec lam h rc zc u) ((y2.1, s), tau)) s := by
        have h_comp := (hasDerivAt_zoomRec_component_z lam h rc zc hu1 ((y2.1, s), tau) hp
          0).const_mul lam
        have h_val : lam * (lam ^ (1 - 2 * h) *
            spatialPartial (fun w => u w 0) 2 (zoomPointRec lam h rc zc ((y2.1, s), tau)))
            = dz (zoomVRec lam h rc zc u) ((y2.1, s), tau) := by
          rw [dz_zoomVRec lam h rc zc u hu1 ((y2.1, s), tau) hp]
          ring
        simpa [zoomVRec, h_val] using h_comp
      exact h_hasDeriv.hasDerivWithinAt
    have hbound : ∀ s ∈ Icc Za Zb,
        ‖dz (zoomVRec lam h rc zc u) ((y2.1, s), tau)‖ ≤ C := by
      intro s hs
      rw [Real.norm_eq_abs]
      exact h_dz_bound s hs
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      (convex_Icc Za Zb) hy1.2 hy2.2
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
    exact hmvt
  -- combine the two edges via triangle inequality
  have h_tri : |zoomVRec lam h rc zc u (y1, tau) - zoomVRec lam h rc zc u (y2, tau)|
      ≤ |zoomVRec lam h rc zc u (y1, tau) - zoomVRec lam h rc zc u ((y2.1, y1.2), tau)|
        + |zoomVRec lam h rc zc u ((y2.1, y1.2), tau) - zoomVRec lam h rc zc u (y2, tau)| :=
    abs_sub_le _ _ _
  have h_sym1 : |zoomVRec lam h rc zc u (y1, tau) - zoomVRec lam h rc zc u ((y2.1, y1.2), tau)|
      = |zoomVRec lam h rc zc u ((y2.1, y1.2), tau) - zoomVRec lam h rc zc u (y1, tau)| :=
    abs_sub_comm _ _
  have h_sym2 : |zoomVRec lam h rc zc u ((y2.1, y1.2), tau) - zoomVRec lam h rc zc u (y2, tau)|
      = |zoomVRec lam h rc zc u (y2, tau) - zoomVRec lam h rc zc u ((y2.1, y1.2), tau)| :=
    abs_sub_comm _ _
  have hd1 : |y2.1 - y1.1| ≤ dist y1 y2 := by
    have hcomp : dist y1.1 y2.1 = |y2.1 - y1.1| := by rw [Real.dist_eq, abs_sub_comm]
    rw [Prod.dist_eq, ← hcomp]
    exact le_max_left _ _
  have hd2 : |y2.2 - y1.2| ≤ dist y1 y2 := by
    have hcomp : dist y1.2 y2.2 = |y2.2 - y1.2| := by rw [Real.dist_eq, abs_sub_comm]
    rw [Prod.dist_eq, ← hcomp]
    exact le_max_right _ _
  have h_et1 : ((y1.1, y1.2) : ℝ × ℝ) = y1 := rfl
  have h_et2 : ((y2.1, y2.2) : ℝ × ℝ) = y2 := rfl
  rw [h_et1] at hedgeR
  rw [h_et2] at hedgeZ
  have hstep1 : C * |y2.1 - y1.1| ≤ C * dist y1 y2 :=
    mul_le_mul_of_nonneg_left hd1 hC
  have hstep2 : C * |y2.2 - y1.2| ≤ C * dist y1 y2 :=
    mul_le_mul_of_nonneg_left hd2 hC
  have hcombine : C * dist y1 y2 + C * dist y1 y2 = 2 * C * dist y1 y2 := by ring
  linarith only [h_tri, h_sym1, h_sym2, hedgeR, hedgeZ, hstep1, hstep2, hcombine]

end CIV
