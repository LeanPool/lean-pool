/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.FiniteAxisSecondDerivativeBoundsV
public import LeanPool.CIVAxisymmetric.Zoom.VLipschitz
public import LeanPool.CIVAxisymmetric.Zoom.ScalarChainRule
public import LeanPool.CIVAxisymmetric.Identities.VorticityEquation

/-!
# Lipschitz bounds for `∂_R V_n` and for `V_n / R` up to the axis

Inputs to the admissibility of the lifted drift of `eq:drift:Bn:def` in Step 2 of the proof of
`prop:aniso:small`. On a rectangle `[Ra, Rb] × [Za, Zb]` mapped into the unit cylinder at a time
`τ ≤ -1`, the radial derivative `∂_R V_n` is Lipschitz with a constant independent of `n`
(`eq:aniso:zoom:derivatives` at order two; the mixed derivative is taken in either order by the
symmetry of the Cartesian mixed partials), and the quotient `V_n / R`, continued to the axis by
`∂_R V_n` (the axis value of `div_{X,Z} B_n / 2`), is Lipschitz on `[0, Rb] × [Za, Zb]`, since
`V_n` vanishes on the axis.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- `∂_R V_n` differentiated in the radial variable along the slice through `p`. -/
theorem hasDerivAt_dr_zoomV_radial_slice (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    HasDerivAt (fun r : ℝ => dr (zoomV lam h zc u) ((r, p.1.2), p.2))
      (dr (dr (zoomV lam h zc u)) p) p.1.1 := by
  rw [drdr_zoomV lam h zc u hu p hp]
  refine HasDerivAt.congr_of_eventuallyEq ?_ (eventually_dr_on_slice_r lam h zc u hu p hp)
  have h_mul := (hasDerivAt_spatialPartial_zero_zoom_r lam h zc u 0 hu p hp).const_mul (lam ^ 2)
  simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul

/-- `∂_R V_n` differentiated in the vertical variable along the slice through `p`; the derivative
is `∂_R ∂_Z V_n` by the symmetry of the Cartesian mixed partials. -/
theorem hasDerivAt_dr_zoomV_vertical_slice (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    HasDerivAt (fun s : ℝ => dr (zoomV lam h zc u) ((p.1.1, s), p.2))
      (dr (dz (zoomV lam h zc u)) p) p.1.2 := by
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by simp)
  have hpar : ContDiffOn ℝ 1
      (fun z : Vec3 × ℝ => spatialPartial (fun w => u w 0) 0 z) unitCylinder :=
    contDiffOn_spatialPartial_of_contDiffOn (contDiffOn_component hu2 0) 0
  have hcomm : spatialPartial
      (fun w : ParabolicPoint => spatialPartial (fun v => u v 0) 0 w) 2 (zoomPoint lam h zc p)
      = meridionalPartial (fun w => u w 0) 1 1 (zoomPoint lam h zc p) :=
    spatialSecondPartial_comm (g := fun w : ParabolicPoint => u w 0)
      (contDiffOn_component hu 0) hp 0 2
  have hbase := (hasDerivAt_zoomScalar_z
      (Phi := fun w : ParabolicPoint => spatialPartial (fun v => u v 0) 0 w)
      lam h zc isOpen_unitCylinder_prod hpar p hp).const_mul (lam ^ 2)
  have hval : lam ^ 2 * (lam ^ (1 - 2 * h) *
      spatialPartial (fun w : ParabolicPoint => spatialPartial (fun v => u v 0) 0 w) 2
        (zoomPoint lam h zc p))
      = lam ^ 2 * lam ^ (1 - 2 * h) *
        meridionalPartial (fun w => u w 0) 1 1 (zoomPoint lam h zc p) := by
    rw [hcomm]; ring
  rw [hval] at hbase
  rw [drdz_zoomV lam h zc u hu2 p hp]
  exact hbase.congr_of_eventuallyEq (eventually_dr_on_slice_z lam h zc u hu2 p hp)

/-- The radial derivative `∂_R V_n` is Lipschitz on a rectangle mapped into the cylinder at a time
`τ ≤ -1`: `|∂_R V_n(y₁) - ∂_R V_n(y₂)| ≤ C (|R₁ - R₂| + |Z₁ - Z₂|)`. -/
theorem abs_dr_zoomV_sub_le {C h lam zc Ra Rb Za Zb tau : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hC : 0 ≤ C) (hh1 : h ≤ 1 / 2) (htau : tau ≤ -1)
    (hmem : ∀ y ∈ Icc Ra Rb ×ˢ Icc Za Zb, zoomPoint lam h zc (y, tau) ∈ unitCylinder)
    {y1 y2 : ℝ × ℝ} (hy1 : y1 ∈ Icc Ra Rb ×ˢ Icc Za Zb) (hy2 : y2 ∈ Icc Ra Rb ×ˢ Icc Za Zb) :
    |dr (zoomV lam h zc u) (y1, tau) - dr (zoomV lam h zc u) (y2, tau)|
      ≤ C * (|y1.1 - y2.1| + |y1.2 - y2.2|) := by
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by simp)
  have hpow : (-tau) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith only [htau]) (by norm_num)
  have hstep : C * (-tau) ^ (-(1 / 2 : ℝ)) ≤ C := mul_le_of_le_one_right hC hpow
  -- radial edge at height `y1.2`
  have hedgeR : |dr (zoomV lam h zc u) ((y2.1, y1.2), tau)
      - dr (zoomV lam h zc u) ((y1.1, y1.2), tau)| ≤ C * |y2.1 - y1.1| := by
    have hderiv : ∀ r ∈ Icc Ra Rb,
        HasDerivWithinAt (fun r' : ℝ => dr (zoomV lam h zc u) ((r', y1.2), tau))
          (dr (dr (zoomV lam h zc u)) ((r, y1.2), tau)) (Icc Ra Rb) r := fun r hr =>
      (hasDerivAt_dr_zoomV_radial_slice lam h zc u hu2 ((r, y1.2), tau)
        (hmem (r, y1.2) ⟨hr, hy1.2⟩)).hasDerivWithinAt
    have hbound : ∀ r ∈ Icc Ra Rb, ‖dr (dr (zoomV lam h zc u)) ((r, y1.2), tau)‖ ≤ C := by
      intro r hr
      rw [Real.norm_eq_abs]
      have := abs_drdr_zoomV_le_rpow_neg_half hlam hb hu2 (hmem (r, y1.2) ⟨hr, hy1.2⟩) hC htau
      exact this.trans hstep
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      (convex_Icc Ra Rb) hy1.1 hy2.1
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  -- vertical edge at radius `y2.1`
  have hedgeZ : |dr (zoomV lam h zc u) ((y2.1, y2.2), tau)
      - dr (zoomV lam h zc u) ((y2.1, y1.2), tau)| ≤ C * |y2.2 - y1.2| := by
    have hderiv : ∀ s ∈ Icc Za Zb,
        HasDerivWithinAt (fun s' : ℝ => dr (zoomV lam h zc u) ((y2.1, s'), tau))
          (dr (dz (zoomV lam h zc u)) ((y2.1, s), tau)) (Icc Za Zb) s := fun s hs =>
      (hasDerivAt_dr_zoomV_vertical_slice lam h zc u hu ((y2.1, s), tau)
        (hmem (y2.1, s) ⟨hy2.1, hs⟩)).hasDerivWithinAt
    have hbound : ∀ s ∈ Icc Za Zb, ‖dr (dz (zoomV lam h zc u)) ((y2.1, s), tau)‖ ≤ C := by
      intro s hs
      rw [Real.norm_eq_abs]
      have := abs_drdz_zoomV_le_rpow_neg_half hlam hb hu2 (hmem (y2.1, s) ⟨hy2.1, hs⟩) hC hh1
        htau
      exact this.trans hstep
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      (convex_Icc Za Zb) hy1.2 hy2.2
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have e1 : ((y2.1, y2.2) : ℝ × ℝ) = y2 := rfl
  have e2 : ((y1.1, y1.2) : ℝ × ℝ) = y1 := rfl
  rw [e1] at hedgeZ; rw [e2] at hedgeR
  have hab := abs_sub_comm (y2.1) (y1.1)
  have hab2 := abs_sub_comm (y2.2) (y1.2)
  calc |dr (zoomV lam h zc u) (y1, tau) - dr (zoomV lam h zc u) (y2, tau)|
      = |(dr (zoomV lam h zc u) ((y2.1, y1.2), tau) - dr (zoomV lam h zc u) (y1, tau))
          + (dr (zoomV lam h zc u) (y2, tau) - dr (zoomV lam h zc u) ((y2.1, y1.2), tau))| := by
        rw [← abs_neg]; congr 1; ring
    _ ≤ |dr (zoomV lam h zc u) ((y2.1, y1.2), tau) - dr (zoomV lam h zc u) (y1, tau)|
        + |dr (zoomV lam h zc u) (y2, tau) - dr (zoomV lam h zc u) ((y2.1, y1.2), tau)| :=
        abs_add_le _ _
    _ ≤ C * |y2.1 - y1.1| + C * |y2.2 - y1.2| := add_le_add hedgeR hedgeZ
    _ = C * (|y1.1 - y2.1| + |y1.2 - y2.2|) := by rw [hab, hab2]; ring

/-- The quotient `V_n / R`, continued to the axis by `∂_R V_n`. -/
@[expose] def zoomVQuot (lam h zc : ℝ) (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  if p.1.1 = 0 then dr (zoomV lam h zc u) p else zoomV lam h zc u p / p.1.1

/-- The standing hypotheses of this section, for a rectangle `[0, Rb] × [Za, Zb]`. -/
theorem abs_zoomV_sub_mul_dr_le {C h lam zc Rb Za Zb tau : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hC : 0 ≤ C) (hh1 : h ≤ 1 / 2) (htau : tau ≤ -1)
    (hmem : ∀ y ∈ Icc 0 Rb ×ˢ Icc Za Zb, zoomPoint lam h zc (y, tau) ∈ unitCylinder)
    {R Z : ℝ} (hR : R ∈ Icc 0 Rb) (hZ : Z ∈ Icc Za Zb) :
    |zoomV lam h zc u ((R, Z), tau) - R * dr (zoomV lam h zc u) ((R, Z), tau)| ≤ C * R ^ 2 := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by simp)
  set k : ℝ → ℝ := fun s => zoomV lam h zc u ((s, Z), tau) - s * dr (zoomV lam h zc u) ((R, Z), tau)
    with hk
  have hderiv : ∀ s ∈ Icc 0 R, HasDerivWithinAt k
      (dr (zoomV lam h zc u) ((s, Z), tau) - dr (zoomV lam h zc u) ((R, Z), tau)) (Icc 0 R) s := by
    intro s hs
    have hsm : ((s, Z) : ℝ × ℝ) ∈ Icc 0 Rb ×ˢ Icc Za Zb := ⟨⟨hs.1, hs.2.trans hR.2⟩, hZ⟩
    have h1 := hasDerivAt_zoomV_radial lam h zc u hu1 ((s, Z), tau) (hmem _ hsm)
    have h2 := hasDerivAt_mul_const (x := s) (dr (zoomV lam h zc u) ((R, Z), tau))
    exact (h1.sub h2).hasDerivWithinAt
  have hbound : ∀ s ∈ Icc 0 R,
      ‖dr (zoomV lam h zc u) ((s, Z), tau) - dr (zoomV lam h zc u) ((R, Z), tau)‖ ≤ C * R := by
    intro s hs
    rw [Real.norm_eq_abs]
    have := abs_dr_zoomV_sub_le hlam hb hu hC hh1 htau hmem
      (y1 := (s, Z)) (y2 := (R, Z)) ⟨⟨hs.1, hs.2.trans hR.2⟩, hZ⟩ ⟨hR, hZ⟩
    simp only [sub_self, abs_zero, add_zero] at this
    have hsr : |s - R| ≤ R := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith only [hs.2])]; linarith only [hs.1]
    exact this.trans (mul_le_mul_of_nonneg_left hsr hC)
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_Icc 0 R) (left_mem_Icc.mpr hR.1) (right_mem_Icc.mpr hR.1)
  have hk0 : k 0 = 0 := by
    have hax := zoomV_axis lam h zc u haxi (hmem ((0, Z)) ⟨⟨le_rfl, hR.1.trans hR.2⟩, hZ⟩)
    simp [hk, hax]
  rw [hk0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg hR.1] at hmvt
  calc |zoomV lam h zc u ((R, Z), tau) - R * dr (zoomV lam h zc u) ((R, Z), tau)| = |k R| := rfl
    _ ≤ C * R * R := hmvt
    _ = C * R ^ 2 := by ring

/-- The quotient is Lipschitz along a radial slice through `[0, Rb]`, with constant `2C`. -/
theorem abs_zoomVQuot_sub_radial_le {C h lam zc Rb Za Zb tau : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hC : 0 ≤ C) (hh1 : h ≤ 1 / 2) (htau : tau ≤ -1)
    (hmem : ∀ y ∈ Icc 0 Rb ×ˢ Icc Za Zb, zoomPoint lam h zc (y, tau) ∈ unitCylinder)
    {R1 R2 Z : ℝ} (hR1 : R1 ∈ Icc 0 Rb) (hR2 : R2 ∈ Icc 0 Rb) (hZ : Z ∈ Icc Za Zb) :
    |zoomVQuot lam h zc u ((R1, Z), tau) - zoomVQuot lam h zc u ((R2, Z), tau)|
      ≤ 2 * C * |R1 - R2| := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by simp)
  -- the value at a point off the axis compared with the axis value
  have haxis : ∀ R ∈ Icc 0 Rb, 0 < R →
      |zoomVQuot lam h zc u ((R, Z), tau) - zoomVQuot lam h zc u ((0, Z), tau)| ≤ 2 * C * R := by
    intro R hR hRpos
    have h1 := abs_zoomV_sub_mul_dr_le hlam hb hu haxi hC hh1 htau hmem hR hZ
    have h2 := abs_dr_zoomV_sub_le hlam hb hu hC hh1 htau hmem (y1 := (R, Z)) (y2 := (0, Z))
      ⟨hR, hZ⟩ ⟨⟨le_rfl, hR.1.trans hR.2⟩, hZ⟩
    simp only [sub_self, abs_zero, add_zero, sub_zero, abs_of_pos hRpos] at h2
    have hq : zoomVQuot lam h zc u ((R, Z), tau) - dr (zoomV lam h zc u) ((R, Z), tau)
        = (zoomV lam h zc u ((R, Z), tau) - R * dr (zoomV lam h zc u) ((R, Z), tau)) / R := by
      simp only [zoomVQuot, hRpos.ne', ↓reduceIte]; field_simp
    have hq' : |zoomVQuot lam h zc u ((R, Z), tau) - dr (zoomV lam h zc u) ((R, Z), tau)|
        ≤ C * R := by
      rw [hq, abs_div, abs_of_pos hRpos, div_le_iff₀ hRpos]; nlinarith only [h1]
    have h0 : zoomVQuot lam h zc u ((0, Z), tau) = dr (zoomV lam h zc u) ((0, Z), tau) := by
      simp [zoomVQuot]
    rw [h0]
    calc |zoomVQuot lam h zc u ((R, Z), tau) - dr (zoomV lam h zc u) ((0, Z), tau)|
        ≤ |zoomVQuot lam h zc u ((R, Z), tau) - dr (zoomV lam h zc u) ((R, Z), tau)|
          + |dr (zoomV lam h zc u) ((R, Z), tau) - dr (zoomV lam h zc u) ((0, Z), tau)| :=
          abs_sub_le _ _ _
      _ ≤ C * R + C * R := add_le_add hq' h2
      _ = 2 * C * R := by ring
  -- two points off the axis: the mean value inequality for `V_n / R`
  have hoff : ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ Rb →
      |zoomVQuot lam h zc u ((b, Z), tau) - zoomVQuot lam h zc u ((a, Z), tau)| ≤ C * (b - a) := by
    intro a b ha hab hbR
    have hderiv : ∀ s ∈ Icc a b, HasDerivWithinAt
        (fun r : ℝ => zoomVQuot lam h zc u ((r, Z), tau))
        ((s * dr (zoomV lam h zc u) ((s, Z), tau) - zoomV lam h zc u ((s, Z), tau)) / s ^ 2)
        (Icc a b) s := by
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
      have hsm : ((s, Z) : ℝ × ℝ) ∈ Icc 0 Rb ×ˢ Icc Za Zb := ⟨⟨hs0.le, hs.2.trans hbR⟩, hZ⟩
      have h1 := hasDerivAt_zoomV_radial lam h zc u hu1 ((s, Z), tau) (hmem _ hsm)
      have h2 := h1.div (hasDerivAt_id s) hs0.ne'
      have hev : (fun r : ℝ => zoomVQuot lam h zc u ((r, Z), tau)) =ᶠ[𝓝 s]
          (fun r : ℝ => zoomV lam h zc u ((r, Z), tau) / id r) := by
        filter_upwards [isOpen_ne.mem_nhds hs0.ne'] with r hr
        simp [zoomVQuot, hr]
      have h3 := h2.congr_of_eventuallyEq hev
      convert h3.hasDerivWithinAt using 1
      simp only [id]; ring
    have hbound : ∀ s ∈ Icc a b,
        ‖(s * dr (zoomV lam h zc u) ((s, Z), tau) - zoomV lam h zc u ((s, Z), tau)) / s ^ 2‖
          ≤ C := by
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
      have h1 := abs_zoomV_sub_mul_dr_le hlam hb hu haxi hC hh1 htau hmem
        (R := s) (Z := Z) ⟨hs0.le, hs.2.trans hbR⟩ hZ
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < s ^ 2),
        div_le_iff₀ (by positivity), abs_sub_comm]
      exact h1
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      (convex_Icc a b) (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hmvt
  -- combine the cases
  rcases eq_or_lt_of_le hR1.1 with h1 | h1 <;> rcases eq_or_lt_of_le hR2.1 with h2 | h2
  · subst h1; subst h2; simp
  · rw [← h1, abs_sub_comm]
    have := haxis R2 hR2 h2
    rw [zero_sub, abs_neg, abs_of_pos h2]; exact this
  · rw [← h2]
    have := haxis R1 hR1 h1
    rw [sub_zero, abs_of_pos h1]; exact this
  · rcases le_total R1 R2 with hle | hle
    · have := hoff R1 R2 h1 hle hR2.2
      have habs : |R1 - R2| = R2 - R1 := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
      rw [abs_sub_comm, habs]
      nlinarith only [this, hC, sub_nonneg.mpr hle]
    · have := hoff R2 R1 h2 hle hR1.2
      rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      nlinarith only [this, hC, sub_nonneg.mpr hle]

/-- The quotient is Lipschitz along a vertical slice, with constant `C`. -/
theorem abs_zoomVQuot_sub_vertical_le {C h lam zc Rb Za Zb tau : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hC : 0 ≤ C) (hh1 : h ≤ 1 / 2) (htau : tau ≤ -1)
    (hmem : ∀ y ∈ Icc 0 Rb ×ˢ Icc Za Zb, zoomPoint lam h zc (y, tau) ∈ unitCylinder)
    {R Z1 Z2 : ℝ} (hR : R ∈ Icc 0 Rb) (hZ1 : Z1 ∈ Icc Za Zb) (hZ2 : Z2 ∈ Icc Za Zb) :
    |zoomVQuot lam h zc u ((R, Z1), tau) - zoomVQuot lam h zc u ((R, Z2), tau)|
      ≤ C * |Z1 - Z2| := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by simp)
  rcases eq_or_lt_of_le hR.1 with h0 | hpos
  · subst h0
    have := abs_dr_zoomV_sub_le hlam hb hu hC hh1 htau hmem (y1 := (0, Z1)) (y2 := (0, Z2))
      ⟨hR, hZ1⟩ ⟨hR, hZ2⟩
    simpa [zoomVQuot] using this
  · set d : ℝ → ℝ := fun s => zoomV lam h zc u ((s, Z1), tau) - zoomV lam h zc u ((s, Z2), tau)
      with hd
    have hderiv : ∀ s ∈ Icc 0 R, HasDerivWithinAt d
        (dr (zoomV lam h zc u) ((s, Z1), tau) - dr (zoomV lam h zc u) ((s, Z2), tau))
        (Icc 0 R) s := by
      intro s hs
      have hs1 : ((s, Z1) : ℝ × ℝ) ∈ Icc 0 Rb ×ˢ Icc Za Zb := ⟨⟨hs.1, hs.2.trans hR.2⟩, hZ1⟩
      have hs2 : ((s, Z2) : ℝ × ℝ) ∈ Icc 0 Rb ×ˢ Icc Za Zb := ⟨⟨hs.1, hs.2.trans hR.2⟩, hZ2⟩
      exact ((hasDerivAt_zoomV_radial lam h zc u hu1 ((s, Z1), tau) (hmem _ hs1)).sub
        (hasDerivAt_zoomV_radial lam h zc u hu1 ((s, Z2), tau) (hmem _ hs2))).hasDerivWithinAt
    have hbound : ∀ s ∈ Icc 0 R,
        ‖dr (zoomV lam h zc u) ((s, Z1), tau) - dr (zoomV lam h zc u) ((s, Z2), tau)‖
          ≤ C * |Z1 - Z2| := by
      intro s hs
      rw [Real.norm_eq_abs]
      have := abs_dr_zoomV_sub_le hlam hb hu hC hh1 htau hmem (y1 := (s, Z1)) (y2 := (s, Z2))
        ⟨⟨hs.1, hs.2.trans hR.2⟩, hZ1⟩ ⟨⟨hs.1, hs.2.trans hR.2⟩, hZ2⟩
      simpa using this
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      (convex_Icc 0 R) (left_mem_Icc.mpr hR.1) (right_mem_Icc.mpr hR.1)
    have hd0 : d 0 = 0 := by
      have h1 := zoomV_axis lam h zc u haxi (hmem ((0, Z1)) ⟨⟨le_rfl, hR.1.trans hR.2⟩, hZ1⟩)
      have h2 := zoomV_axis lam h zc u haxi (hmem ((0, Z2)) ⟨⟨le_rfl, hR.1.trans hR.2⟩, hZ2⟩)
      simp [hd, h1, h2]
    rw [hd0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_pos hpos] at hmvt
    have hq : zoomVQuot lam h zc u ((R, Z1), tau) - zoomVQuot lam h zc u ((R, Z2), tau)
        = d R / R := by
      simp only [zoomVQuot, hpos.ne', ↓reduceIte, hd]; ring
    rw [hq, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    linarith only [hmvt]

/-- The quotient is Lipschitz on the rectangle `[0, Rb] × [Za, Zb]`, with constant `2C` for the sum
of the coordinate increments. -/
theorem abs_zoomVQuot_sub_le {C h lam zc Rb Za Zb tau : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hC : 0 ≤ C) (hh1 : h ≤ 1 / 2) (htau : tau ≤ -1)
    (hmem : ∀ y ∈ Icc 0 Rb ×ˢ Icc Za Zb, zoomPoint lam h zc (y, tau) ∈ unitCylinder)
    {y1 y2 : ℝ × ℝ} (hy1 : y1 ∈ Icc 0 Rb ×ˢ Icc Za Zb) (hy2 : y2 ∈ Icc 0 Rb ×ˢ Icc Za Zb) :
    |zoomVQuot lam h zc u (y1, tau) - zoomVQuot lam h zc u (y2, tau)|
      ≤ 2 * C * (|y1.1 - y2.1| + |y1.2 - y2.2|) := by
  have hR := abs_zoomVQuot_sub_radial_le hlam hb hu haxi hC hh1 htau hmem hy1.1 hy2.1 hy1.2
  have hZ := abs_zoomVQuot_sub_vertical_le hlam hb hu haxi hC hh1 htau hmem hy2.1 hy1.2 hy2.2
  have e1 : ((y2.1, y2.2) : ℝ × ℝ) = y2 := rfl
  have e2 : ((y1.1, y1.2) : ℝ × ℝ) = y1 := rfl
  rw [e2] at hR; rw [e1] at hZ
  calc |zoomVQuot lam h zc u (y1, tau) - zoomVQuot lam h zc u (y2, tau)|
      ≤ |zoomVQuot lam h zc u (y1, tau) - zoomVQuot lam h zc u ((y2.1, y1.2), tau)|
        + |zoomVQuot lam h zc u ((y2.1, y1.2), tau) - zoomVQuot lam h zc u (y2, tau)| :=
        abs_sub_le _ _ _
    _ ≤ 2 * C * |y1.1 - y2.1| + C * |y1.2 - y2.2| := add_le_add hR hZ
    _ ≤ 2 * C * (|y1.1 - y2.1| + |y1.2 - y2.2|) := by
        nlinarith only [hC, abs_nonneg (y1.2 - y2.2)]

end CIV
