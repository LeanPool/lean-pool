/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.Receding
public import LeanPool.CIVAxisymmetric.Zoom.Algebra

/-!
# Lipschitz-in-space bound for the rescaled vertical field `W_n`

On a rectangle contained in `{R ≥ 0}` the rescaled vertical field `W_n` of
`eq:aniso:zoom:receding:variables` has first spatial derivatives bounded *uniformly in the zoom
scale* and in the rescaled time `τ ≤ -1`.  The proof drops the nonnegative `S_n` summand from
the combined anisotropic bounds (`abs_dr_zoomWRec_add_abs_dr_zoomSRec_le`,
`abs_dz_zoomWRec_add_abs_dz_zoomSRec_le`) to obtain `τ`-uniform pointwise bounds
`|∂_R W_n| ≤ C` and `|∂_Z W_n| ≤ C`, then integrates along the two coordinate edges of a
rectangle via `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`.  This is the input to the
Arzelà–Ascoli extraction of Step 3.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### The `τ`-uniform derivative bounds -/

/-- The radial derivative of `W_n` is bounded by `C` for `τ ≤ -1`. -/
private theorem abs_dr_zoomWRec_le_const {C h lam rc zc tau : ℝ} (hlam : 0 < lam)
    (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hC : 0 ≤ C) (hh0 : 0 ≤ h) (htau : tau ≤ -1)
    (hmem : ∀ y ∈ Icc (0 : ℝ) (0 : ℝ) ×ˢ Icc (0 : ℝ) (0 : ℝ), zoomPointRec lam h rc zc (y, tau)
      ∈ unitCylinder) :
    ‖dr (zoomWRec lam h rc zc u) ((0, 0), tau)‖ ≤ C := by
  have hp : zoomPointRec lam h rc zc ((0, 0), tau) ∈ unitCylinder := hmem (0, 0) (by simp)
  have hbound := abs_dr_zoomWRec_add_abs_dr_zoomSRec_le C h lam rc zc hlam u hb hu ((0, 0), tau) hp
  have hS : (0 : ℝ) ≤ |dr (zoomSRec lam h rc zc u) ((0, 0), tau)| := abs_nonneg _
  have h_exp : -(1 / 2 : ℝ) - h - 1 / 2 - (1 / 2 - h) * (0 : ℝ) = -1 - h := by ring
  rw [h_exp] at hbound
  have hW : |dr (zoomWRec lam h rc zc u) ((0, 0), tau)| ≤ C * (-tau) ^ (-1 - h) := by
    linarith only [hbound, hS]
  have hpow : (-tau) ^ (-1 - h) ≤ 1 :=
    neg_rpow_le_one_of_le_neg_one htau (by linarith only [hh0])
  have hstep : C * (-tau) ^ (-1 - h) ≤ C * 1 :=
    mul_le_mul_of_nonneg_left hpow hC
  rw [Real.norm_eq_abs]
  linarith only [hW, hstep]

/-- The vertical derivative of `W_n` is bounded by `C` for `τ ≤ -1`. -/
private theorem abs_dz_zoomWRec_le_const {C h lam rc zc tau : ℝ} (hlam : 0 < lam)
    (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hC : 0 ≤ C) (htau : tau ≤ -1)
    (hmem : ∀ y ∈ Icc (0 : ℝ) (0 : ℝ) ×ˢ Icc (0 : ℝ) (0 : ℝ), zoomPointRec lam h rc zc (y, tau)
      ∈ unitCylinder) :
    ‖dz (zoomWRec lam h rc zc u) ((0, 0), tau)‖ ≤ C := by
  have hp : zoomPointRec lam h rc zc ((0, 0), tau) ∈ unitCylinder := hmem (0, 0) (by simp)
  have hbound := abs_dz_zoomWRec_add_abs_dz_zoomSRec_le C h lam rc zc hlam u hb hu ((0, 0), tau) hp
  have hS : (0 : ℝ) ≤ |dz (zoomSRec lam h rc zc u) ((0, 0), tau)| := abs_nonneg _
  have h_exp : -(1 / 2 : ℝ) - h - (0 : ℝ) / 2 - (1 / 2 - h) * (1 : ℝ) = -1 := by ring
  rw [h_exp] at hbound
  have hW : |dz (zoomWRec lam h rc zc u) ((0, 0), tau)| ≤ C * (-tau) ^ (-1 : ℝ) := by
    linarith only [hbound, hS]
  have hpow : (-tau) ^ (-1 : ℝ) ≤ 1 :=
    neg_rpow_le_one_of_le_neg_one htau (by norm_num)
  have hstep : C * (-tau) ^ (-1 : ℝ) ≤ C * 1 :=
    mul_le_mul_of_nonneg_left hpow hC
  rw [Real.norm_eq_abs]
  linarith only [hW, hstep]

/-! ### The two-point bound on a rectangle -/

/-- The two-point bound on a rectangle `[Ra, Rb] × [Za, Zb]` at a fixed rescaled time
`τ ≤ -1`: joining the two points by the two coordinate edges through `(y₂₁, y₁₂)` and applying the
mean value inequality on each edge. -/
theorem abs_zoomWRec_sub_zoomWRec_le {C h lam rc zc Ra Rb Za Zb tau : ℝ} (hlam : 0 < lam)
    (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hC : 0 ≤ C) (hh0 : 0 ≤ h) (htau : tau ≤ -1)
    (hmem : ∀ y ∈ Icc Ra Rb ×ˢ Icc Za Zb, zoomPointRec lam h rc zc (y, tau) ∈ unitCylinder)
    {y1 y2 : ℝ × ℝ} (hy1 : y1 ∈ Icc Ra Rb ×ˢ Icc Za Zb)
    (hy2 : y2 ∈ Icc Ra Rb ×ˢ Icc Za Zb) :
    |zoomWRec lam h rc zc u (y1, tau) - zoomWRec lam h rc zc u (y2, tau)|
      ≤ (2 * C) * dist y1 y2 := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by norm_num)
  -- the radial edge, at the height of `y1`
  have hedgeR : |zoomWRec lam h rc zc u ((y2.1, y1.2), tau)
      - zoomWRec lam h rc zc u ((y1.1, y1.2), tau)|
      ≤ C * |y2.1 - y1.1| := by
    have hderiv : ∀ r ∈ Icc Ra Rb,
        HasDerivWithinAt (fun r' : ℝ => zoomWRec lam h rc zc u ((r', y1.2), tau))
          (dr (zoomWRec lam h rc zc u) ((r, y1.2), tau)) (Icc Ra Rb) r := by
      intro r hr
      have hpt : ((r, y1.2) : ℝ × ℝ) ∈ Icc Ra Rb ×ˢ Icc Za Zb := ⟨hr, hy1.2⟩
      have hcyl : zoomPointRec lam h rc zc (((r, y1.2) : ℝ × ℝ), tau) ∈ unitCylinder := hmem _ hpt
      have hval := dr_zoomWRec lam h rc zc u hu1 ((r, y1.2), tau) hcyl
      rw [hval]
      have hbase := (hasDerivAt_zoomRec_component_r lam h rc zc hu1 ((r, y1.2), tau) hcyl
        2).const_mul
        (lam * lam ^ (2 * h))
      have heq : lam * lam ^ (2 * h) *
          (lam * spatialPartial (fun w => u w 2) 0 (zoomPointRec lam h rc zc ((r, y1.2), tau)))
        = lam ^ 2 * lam ^ (2 * h) *
          spatialPartial (fun w => u w 2) 0 (zoomPointRec lam h rc zc ((r, y1.2), tau)) := by ring
      rw [heq] at hbase
      exact hbase.hasDerivWithinAt
    have hbound : ∀ r ∈ Icc Ra Rb,
        ‖dr (zoomWRec lam h rc zc u) ((r, y1.2), tau)‖ ≤ C := by
      intro r hr
      have hpt : ((r, y1.2) : ℝ × ℝ) ∈ Icc Ra Rb ×ˢ Icc Za Zb := ⟨hr, hy1.2⟩
      have hcyl : zoomPointRec lam h rc zc (((r, y1.2) : ℝ × ℝ), tau) ∈ unitCylinder := hmem _ hpt
      have hval := dr_zoomWRec lam h rc zc u hu1 ((r, y1.2), tau) hcyl
      rw [Real.norm_eq_abs, hval]
      have hbound' := abs_dr_zoomWRec_add_abs_dr_zoomSRec_le C h lam rc zc hlam u hb hu
        ((r, y1.2), tau) hcyl
      have hS : (0 : ℝ) ≤ |dr (zoomSRec lam h rc zc u) ((r, y1.2), tau)| := abs_nonneg _
      have h_exp : -(1 / 2 : ℝ) - h - 1 / 2 - (1 / 2 - h) * (0 : ℝ) = -1 - h := by ring
      have hW : |dr (zoomWRec lam h rc zc u) ((r, y1.2), tau)| ≤ C * (-tau) ^ (-1 - h) := by
        have : (-((r, y1.2), tau).2) = (-tau) := by simp
        have htemp := hbound'
        rw [h_exp, this] at htemp
        linarith only [htemp, hS]
      have hpow : (-tau) ^ (-1 - h) ≤ 1 :=
        neg_rpow_le_one_of_le_neg_one htau (by linarith only [hh0])
      have hstep : C * (-tau) ^ (-1 - h) ≤ C :=
        calc
          C * (-tau) ^ (-1 - h) ≤ C * 1 := mul_le_mul_of_nonneg_left hpow hC
          _ = C := mul_one _
      rw [← hval]
      exact le_trans hW hstep
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      (convex_Icc Ra Rb) hy1.1 hy2.1
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
    exact hmvt
  -- the vertical edge, at the radius of `y2`
  have hedgeZ : |zoomWRec lam h rc zc u ((y2.1, y2.2), tau)
      - zoomWRec lam h rc zc u ((y2.1, y1.2), tau)|
      ≤ C * |y2.2 - y1.2| := by
    have hderiv : ∀ s ∈ Icc Za Zb,
        HasDerivWithinAt (fun s' : ℝ => zoomWRec lam h rc zc u ((y2.1, s'), tau))
          (dz (zoomWRec lam h rc zc u) ((y2.1, s), tau)) (Icc Za Zb) s := by
      intro s hs
      have hpt : ((y2.1, s) : ℝ × ℝ) ∈ Icc Ra Rb ×ˢ Icc Za Zb := ⟨hy2.1, hs⟩
      have hcyl : zoomPointRec lam h rc zc (((y2.1, s) : ℝ × ℝ), tau) ∈ unitCylinder := hmem _ hpt
      have hval := dz_zoomWRec lam h rc zc u hu1 ((y2.1, s), tau) hcyl
      rw [hval]
      have hbase := (hasDerivAt_zoomRec_component_z lam h rc zc hu1 ((y2.1, s), tau) hcyl
        2).const_mul
        (lam * lam ^ (2 * h))
      have heq : lam * lam ^ (2 * h) *
          (lam ^ (1 - 2 * h) * spatialPartial (fun w => u w 2) 2
            (zoomPointRec lam h rc zc ((y2.1, s), tau)))
        = lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) *
          spatialPartial (fun w => u w 2) 2 (zoomPointRec lam h rc zc ((y2.1, s), tau)) := by ring
      rw [heq] at hbase
      exact hbase.hasDerivWithinAt
    have hbound : ∀ s ∈ Icc Za Zb,
        ‖dz (zoomWRec lam h rc zc u) ((y2.1, s), tau)‖ ≤ C := by
      intro s hs
      have hpt : ((y2.1, s) : ℝ × ℝ) ∈ Icc Ra Rb ×ˢ Icc Za Zb := ⟨hy2.1, hs⟩
      have hcyl : zoomPointRec lam h rc zc (((y2.1, s) : ℝ × ℝ), tau) ∈ unitCylinder := hmem _ hpt
      have hval := dz_zoomWRec lam h rc zc u hu1 ((y2.1, s), tau) hcyl
      rw [Real.norm_eq_abs, hval]
      have hbound' := abs_dz_zoomWRec_add_abs_dz_zoomSRec_le C h lam rc zc hlam u hb hu
        ((y2.1, s), tau) hcyl
      have hS : (0 : ℝ) ≤ |dz (zoomSRec lam h rc zc u) ((y2.1, s), tau)| := abs_nonneg _
      have h_exp : -(1 / 2 : ℝ) - h - (0 : ℝ) / 2 - (1 / 2 - h) * (1 : ℝ) = -1 := by ring
      have hW : |dz (zoomWRec lam h rc zc u) ((y2.1, s), tau)| ≤ C * (-tau) ^ (-1 : ℝ) := by
        have : (-((y2.1, s), tau).2) = (-tau) := by simp
        have htemp := hbound'
        rw [h_exp, this] at htemp
        linarith only [htemp, hS]
      have hpow : (-tau) ^ (-1 : ℝ) ≤ 1 :=
        neg_rpow_le_one_of_le_neg_one htau (by norm_num)
      have hstep : C * (-tau) ^ (-1 : ℝ) ≤ C :=
        calc
          C * (-tau) ^ (-1 : ℝ) ≤ C * 1 := mul_le_mul_of_nonneg_left hpow hC
          _ = C := mul_one _
      rw [← hval]
      exact le_trans hW hstep
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      (convex_Icc Za Zb) hy1.2 hy2.2
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
    exact hmvt
  have hd1 : |y2.1 - y1.1| ≤ dist y1 y2 := by
    have hcomp : dist y1.1 y2.1 = |y2.1 - y1.1| := by rw [Real.dist_eq, abs_sub_comm]
    rw [Prod.dist_eq, ← hcomp]
    exact le_max_left _ _
  have hd2 : |y2.2 - y1.2| ≤ dist y1 y2 := by
    have hcomp : dist y1.2 y2.2 = |y2.2 - y1.2| := by rw [Real.dist_eq, abs_sub_comm]
    rw [Prod.dist_eq, ← hcomp]
    exact le_max_right _ _
  have he1 : ((y1.1, y1.2) : ℝ × ℝ) = y1 := rfl
  have he2 : ((y2.1, y2.2) : ℝ × ℝ) = y2 := rfl
  rw [he1] at hedgeR
  rw [he2] at hedgeZ
  have htri : |zoomWRec lam h rc zc u (y1, tau) - zoomWRec lam h rc zc u (y2, tau)|
      ≤ |zoomWRec lam h rc zc u (y1, tau) - zoomWRec lam h rc zc u ((y2.1, y1.2), tau)|
        + |zoomWRec lam h rc zc u ((y2.1, y1.2), tau) - zoomWRec lam h rc zc u (y2, tau)| :=
    abs_sub_le _ _ _
  have hsym1 : |zoomWRec lam h rc zc u (y1, tau) - zoomWRec lam h rc zc u ((y2.1, y1.2), tau)|
      = |zoomWRec lam h rc zc u ((y2.1, y1.2), tau) - zoomWRec lam h rc zc u (y1, tau)| :=
    abs_sub_comm _ _
  have hstep1 : C * |y2.1 - y1.1| ≤ C * dist y1 y2 :=
    mul_le_mul_of_nonneg_left hd1 hC
  have hstep2 : C * |y2.2 - y1.2| ≤ C * dist y1 y2 :=
    mul_le_mul_of_nonneg_left hd2 hC
  have hcombine : C * dist y1 y2 + C * dist y1 y2 = (2 * C) * dist y1 y2 := by ring
  have hsym3 : |zoomWRec lam h rc zc u ((y2.1, y1.2), tau) - zoomWRec lam h rc zc u (y2, tau)|
      = |zoomWRec lam h rc zc u (y2, tau) - zoomWRec lam h rc zc u ((y2.1, y1.2), tau)| :=
    abs_sub_comm _ _
  linarith only [htri, hsym1, hsym3, hedgeR, hedgeZ, hstep1, hstep2, hcombine]

/-- The Lipschitz-in-space bound for the rescaled vertical field `W_n` on a rectangle, at every
rescaled time `τ ≤ -1`, with a constant independent of the zoom scale and of `τ`. -/
theorem lipschitzOnWith_zoomWRec {C h lam rc zc Ra Rb Za Zb tau : ℝ} (hlam : 0 < lam)
    (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hC : 0 ≤ C) (hh0 : 0 ≤ h) (htau : tau ≤ -1)
    (hmem : ∀ y ∈ Icc Ra Rb ×ˢ Icc Za Zb, zoomPointRec lam h rc zc (y, tau) ∈ unitCylinder) :
    LipschitzOnWith (Real.toNNReal (2 * C))
      (fun y : ℝ × ℝ => zoomWRec lam h rc zc u (y, tau)) (Icc Ra Rb ×ˢ Icc Za Zb) := by
  have hLnn : (0 : ℝ) ≤ 2 * C := mul_nonneg (by norm_num) hC
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro y1 hy1 y2 hy2
  rw [Real.coe_toNNReal _ hLnn, Real.dist_eq]
  exact abs_zoomWRec_sub_zoomWRec_le hlam u hb hu hC hh0 htau hmem hy1 hy2

end CIV
