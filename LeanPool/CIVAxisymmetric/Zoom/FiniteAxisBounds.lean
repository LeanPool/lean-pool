/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.PotentialVorticityRescaled
public import LeanPool.CIVAxisymmetric.Zoom.SwirlSource
public import LeanPool.CIVAxisymmetric.Zoom.Algebra
public import LeanPool.CIVAxisymmetric.Zoom.DivergenceIdentity
public import LeanPool.CIVAxisymmetric.Identities.PartialCalculus

/-!
# The finite-axis bounds of the zoom-in variables

Step 1 of the finite-`h` zoom-in argument. Two families of bounds are proved here.

* The potential vorticity of the rescaled fields obeys `eq:aniso:zoom:finite:bound`:
  away from the axis `Ω_n = (δ² ∂_z V_n - ∂_r W_n)/R`, and both quotients are controlled
  by the second derivatives along the radial segment from the axis, because `∂_z u_r` and
  `∂_r u_z` vanish there. On the axis the same bound holds for the continuous extension,
  which is `δ² ∂_r ∂_z V_n - ∂_r ∂_r W_n` there. Uniformly in the rescaled time `τ ≤ -1`
  this gives `|Ω_n| ≤ 2C`.
* The six drift bounds of `eq:aniso:zoom:derivatives` that the Step 2 comparison argument
  consumes: `V_n`, `W_n` and their first derivatives are all bounded by `C (-τ)^{-1/2}`
  once `τ ≤ -1`, since each of their anisotropic exponents is at most `-1/2`.

The same segment argument bounds the quotient `V_n/R` by the supremum of `∂_R V_n`, because
`V_n` vanishes on the axis, and with these bounds the lifted drift `eq:drift:Bn:def` of
Step 2, `B_n = (V_n X/R, W_n)` on `ℝ⁴ × ℝ`, is bounded by `C (-τ)^{-1/2}` as well. Its
divergence in the five lifted coordinates is computed here too: the trace of
`∇_X(V_n X/R)` is `∂_R V_n + 3 V_n/R`, and the divergence identity of
`eq:aniso:zoom:finite:identities` turns the sum into `2 V_n/R`.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### An elementary bound for a scaled difference -/

/-- `|δ A - B| ≤ δ D + E` from `|A| ≤ D`, `|B| ≤ E` and `0 ≤ δ`. -/
private theorem abs_sub_smul_le {A B D E δ : ℝ} (hδ : 0 ≤ δ) (hA : |A| ≤ D) (hB : |B| ≤ E) :
    |δ * A - B| ≤ δ * D + E := by
  have h1 : |δ * A - B| ≤ |δ * A| + |B| := by
    rw [sub_eq_add_neg]
    calc |δ * A + -B| ≤ |δ * A| + |(-B)| := abs_add_le _ _
      _ = |δ * A| + |B| := by rw [abs_neg]
  have h2 : |δ * A| = δ * |A| := by rw [abs_mul, abs_of_nonneg hδ]
  rw [h2] at h1
  have h3 : δ * |A| ≤ δ * D := mul_le_mul_of_nonneg_left hA hδ
  linarith only [h1, h3, hB]

/-! ### Differentiability of the two numerators along the radial segment -/

/-- `∂_z V_n` is differentiable in the radial variable along the slice through `p`
(the radial slice of `eq:aniso:zoom:fields`). -/
private theorem hasDerivAt_dz_zoomV_slice (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    HasDerivAt (fun r : ℝ => dz (zoomV lam h zc u) ((r, p.1.2), p.2))
      (lam ^ 2 * lam ^ (1 - 2 * h) *
        meridionalPartial (fun w => u w 0) 1 1 (zoomPoint lam h zc p)) p.1.1 := by
  have h_event := eventually_dz_on_slice_r lam h zc u hu p hp
  have h_inner := hasDerivAt_spatialPartial_two_zoom_r lam h zc u 0 hu p hp
  have h_mul := h_inner.const_mul (lam * lam ^ (1 - 2 * h))
  have h_deriv_rhs : HasDerivAt (fun r : ℝ =>
      lam * lam ^ (1 - 2 * h) *
        spatialPartial (fun w => u w 0) 2 (zoomPoint lam h zc ((r, p.1.2), p.2)))
      (lam ^ 2 * lam ^ (1 - 2 * h) *
        meridionalPartial (fun w => u w 0) 1 1 (zoomPoint lam h zc p)) p.1.1 := by
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul
  exact h_deriv_rhs.congr_of_eventuallyEq h_event

/-- `∂_r W_n` is differentiable in the radial variable along the slice through `p`
(the radial slice of `eq:aniso:zoom:fields`). -/
private theorem hasDerivAt_dr_zoomW_slice (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    HasDerivAt (fun r : ℝ => dr (zoomW lam h zc u) ((r, p.1.2), p.2))
      (lam ^ 3 * lam ^ (2 * h) *
        meridionalPartial (fun w => u w 2) 2 0 (zoomPoint lam h zc p)) p.1.1 := by
  have h_event : (fun r : ℝ => dr (zoomW lam h zc u) ((r, p.1.2), p.2))
      =ᶠ[𝓝 p.1.1]
    fun r : ℝ =>
      lam ^ 2 * lam ^ (2 * h) *
        spatialPartial (fun w => u w 2) 0 (zoomPoint lam h zc ((r, p.1.2), p.2)) := by
    have hS_open : IsOpen {r : ℝ | zoomPoint lam h zc ((r, p.1.2), p.2) ∈ unitCylinder} :=
      isOpen_slice_r lam h zc p
    have hpS : p.1.1 ∈ {r : ℝ | zoomPoint lam h zc ((r, p.1.2), p.2) ∈ unitCylinder} := hp
    filter_upwards [hS_open.mem_nhds hpS] with r hr
    rw [dr_zoomW lam h zc u (hu.of_le (by norm_num)) ((r, p.1.2), p.2) hr]
  have h_inner := hasDerivAt_spatialPartial_zero_zoom_r lam h zc u 2 hu p hp
  have h_mul := h_inner.const_mul (lam ^ 2 * lam ^ (2 * h))
  have h_deriv_rhs : HasDerivAt (fun r : ℝ =>
      lam ^ 2 * lam ^ (2 * h) *
        spatialPartial (fun w => u w 2) 0 (zoomPoint lam h zc ((r, p.1.2), p.2)))
      (lam ^ 3 * lam ^ (2 * h) *
        meridionalPartial (fun w => u w 2) 2 0 (zoomPoint lam h zc p)) p.1.1 := by
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul
  exact h_deriv_rhs.congr_of_eventuallyEq h_event

/-! ### The two numerators vanish on the axis -/

/-- `∂_z V_n` vanishes on the axis, because `∂_z u_r` does
(the paragraph after `eq:aniso:circulation:pde`). -/
private theorem dz_zoomV_axis (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {Z τ : ℝ}
    (hmem : zoomPoint lam h zc ((0, Z), τ) ∈ unitCylinder) :
    dz (zoomV lam h zc u) ((0, Z), τ) = 0 := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by norm_num)
  have hax0 : (zoomPoint lam h zc ((0, Z), τ)).1 0 = 0 := by simp [zoomPoint, meridional]
  have hax1 : (zoomPoint lam h zc ((0, Z), τ)).1 1 = 0 := by simp [zoomPoint, meridional]
  have hzero : spatialPartial (fun w => u w 0) 2 (zoomPoint lam h zc ((0, Z), τ)) = 0 :=
    spatialPartial_two_zero_axis haxi hu1 hmem hax0 hax1
  rw [dz_zoomV lam h zc u hu1 ((0, Z), τ) hmem, hzero, mul_zero]

/-- `∂_r W_n` vanishes on the axis, because `∂_r u_z` does
(the standing assumptions of Section `sec:aniso:equations`). -/
private theorem dr_zoomW_axis (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {Z τ : ℝ}
    (hmem : zoomPoint lam h zc ((0, Z), τ) ∈ unitCylinder) :
    dr (zoomW lam h zc u) ((0, Z), τ) = 0 := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by norm_num)
  have hax0 : (zoomPoint lam h zc ((0, Z), τ)).1 0 = 0 := by simp [zoomPoint, meridional]
  have hax1 : (zoomPoint lam h zc ((0, Z), τ)).1 1 = 0 := by simp [zoomPoint, meridional]
  have hzero : spatialPartial (fun w => u w 2) 0 (zoomPoint lam h zc ((0, Z), τ)) = 0 :=
    spatialPartial_zero_two_axis haxi hu1 hmem hax0 hax1
  rw [dr_zoomW lam h zc u hu1 ((0, Z), τ) hmem, hzero, mul_zero]

/-! ### The two quotients that build the rescaled potential vorticity -/

/-- `|∂_z V_n / R| ≤ C (-τ)^{-3/2 + h}`, from the segment representation of the quotient and
the bound on `∂_r ∂_z V_n` of `eq:aniso:zoom:derivatives`. -/
theorem abs_dz_zoomV_div_le {C h lam zc : ℝ} (hlam : 0 < lam) {u : ParabolicPoint → Vec3}
    (hb : AnisotropicBounds C h u) (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (hR : p.1.1 ≠ 0) :
    |dz (zoomV lam h zc u) p / p.1.1| ≤ C * (-p.2) ^ (-(3 / 2 : ℝ) + h) := by
  have hg0 : dz (zoomV lam h zc u) ((0, p.1.2), p.2) = 0 :=
    dz_zoomV_axis lam h zc u hu haxi
      (zoomPoint_slice_mem lam h zc hlam hp hR left_mem_uIcc)
  have hd : ∀ s ∈ uIcc (0 : ℝ) p.1.1,
      DifferentiableAt ℝ (fun r : ℝ => dz (zoomV lam h zc u) ((r, p.1.2), p.2)) s := by
    intro s hs
    have hmem := zoomPoint_slice_mem lam h zc hlam hp hR hs
    exact (hasDerivAt_dz_zoomV_slice lam h zc u hu ((s, p.1.2), p.2) hmem).differentiableAt
  have hM : ∀ s ∈ uIcc (0 : ℝ) p.1.1,
      |deriv (fun r : ℝ => dz (zoomV lam h zc u) ((r, p.1.2), p.2)) s|
        ≤ C * (-p.2) ^ (-(3 / 2 : ℝ) + h) := by
    intro s hs
    have hmem := zoomPoint_slice_mem lam h zc hlam hp hR hs
    have hbnd := abs_drdz_zoomV_le C h lam zc hlam u hb hu ((s, p.1.2), p.2) hmem
    have hexp : -(1 / 2 : ℝ) - 1 / 2 - (1 / 2 - h) * 1 = -(3 / 2 : ℝ) + h := by ring
    rw [hexp] at hbnd
    exact hbnd
  exact abs_div_le_of_deriv_bound
    (g := fun r : ℝ => dz (zoomV lam h zc u) ((r, p.1.2), p.2)) hg0 hd hM hR

/-- `|∂_r W_n / R| ≤ C (-τ)^{-3/2 - h}`, from the segment representation of the quotient and
the bound on `∂_r ∂_r W_n` of `eq:aniso:zoom:derivatives`. -/
theorem abs_dr_zoomW_div_le {C h lam zc : ℝ} (hlam : 0 < lam) {u : ParabolicPoint → Vec3}
    (hb : AnisotropicBounds C h u) (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (hR : p.1.1 ≠ 0) :
    |dr (zoomW lam h zc u) p / p.1.1| ≤ C * (-p.2) ^ (-(3 / 2 : ℝ) - h) := by
  have hg0 : dr (zoomW lam h zc u) ((0, p.1.2), p.2) = 0 :=
    dr_zoomW_axis lam h zc u hu haxi
      (zoomPoint_slice_mem lam h zc hlam hp hR left_mem_uIcc)
  have hd : ∀ s ∈ uIcc (0 : ℝ) p.1.1,
      DifferentiableAt ℝ (fun r : ℝ => dr (zoomW lam h zc u) ((r, p.1.2), p.2)) s := by
    intro s hs
    have hmem := zoomPoint_slice_mem lam h zc hlam hp hR hs
    exact (hasDerivAt_dr_zoomW_slice lam h zc u hu ((s, p.1.2), p.2) hmem).differentiableAt
  have hM : ∀ s ∈ uIcc (0 : ℝ) p.1.1,
      |deriv (fun r : ℝ => dr (zoomW lam h zc u) ((r, p.1.2), p.2)) s|
        ≤ C * (-p.2) ^ (-(3 / 2 : ℝ) - h) := by
    intro s hs
    have hmem := zoomPoint_slice_mem lam h zc hlam hp hR hs
    have hbnd := abs_drdr_zoomW_add_abs_drdr_zoomS_le C h lam zc hlam u hb hu
      ((s, p.1.2), p.2) hmem
    have hS : (0 : ℝ) ≤ |dr (dr (zoomS lam h zc u)) ((s, p.1.2), p.2)| := abs_nonneg _
    have hW : |dr (dr (zoomW lam h zc u)) ((s, p.1.2), p.2)|
        ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - h - 2 / 2 - (1 / 2 - h) * 0) := by
      linarith only [hbnd, hS]
    have hexp : -(1 / 2 : ℝ) - h - 2 / 2 - (1 / 2 - h) * 0 = -(3 / 2 : ℝ) - h := by ring
    rw [hexp] at hW
    exact hW
  exact abs_div_le_of_deriv_bound
    (g := fun r : ℝ => dr (zoomW lam h zc u) ((r, p.1.2), p.2)) hg0 hd hM hR

/-! ### The finite-axis bound off the axis -/

/-- The finite-axis bound `eq:aniso:zoom:finite:bound` on the rescaled potential vorticity,
away from the axis: there `Ω_n` is the quotient `(δ² ∂_z V_n - ∂_r W_n)/R` of
`eq:aniso:zoom:finite:identities`, and each of the two quotients is controlled along the radial
segment
from the axis. -/
theorem abs_zoomOmega_le {C h lam zc : ℝ} (hlam : 0 < lam) {u : ParabolicPoint → Vec3}
    (hb : AnisotropicBounds C h u) (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (hR : p.1.1 ≠ 0) :
    |zoomOmega lam h zc u p|
      ≤ C * ((lam ^ (2 * h)) ^ 2 * (-p.2) ^ (-(3 / 2 : ℝ) + h)
          + (-p.2) ^ (-(3 / 2 : ℝ) - h)) := by
  have hV := abs_dz_zoomV_div_le hlam hb hu haxi hp hR
  have hW := abs_dr_zoomW_div_le hlam hb hu haxi hp hR
  have hδ : (0 : ℝ) ≤ (lam ^ (2 * h)) ^ 2 := by positivity
  rw [zoomOmega_eq lam h zc hlam u (hu.of_le (by norm_num)) p hp hR, sub_div, mul_div_assoc]
  refine le_trans (abs_sub_smul_le hδ hV hW) (le_of_eq ?_)
  ring

/-! ### The finite-axis bound on the axis -/

/-- The radial derivative of the azimuthal vorticity is `∂_r ∂_z u_r - ∂_r ∂_r u_z`,
which is `eq:aniso:vorticity` differentiated once more in `x₁`. -/
private theorem spatialPartial_azimuthalVorticity_zero (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) :
    spatialPartial (azimuthalVorticity u) 0 z
      = meridionalPartial (fun w => u w 0) 1 1 z - meridionalPartial (fun w => u w 2) 2 0 z := by
  have hA2 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => spatialPartial (fun v => u v 0) 2 w)
      unitCylinder :=
    contDiffOn_spatialPartial_of_contDiffOn (contDiffOn_component hu 0) 2
  have hC0 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => spatialPartial (fun v => u v 2) 0 w)
      unitCylinder :=
    contDiffOn_spatialPartial_of_contDiffOn (contDiffOn_component hu 2) 0
  have hfun : azimuthalVorticity u
      = fun w => spatialPartial (fun v => u v 0) 2 w - spatialPartial (fun v => u v 2) 0 w :=
    funext (curlComp_one u)
  rw [hfun]
  exact spatialPartial_sub_of_differentiableAt (i := 0)
    (differentiableAt_spatialSlice hA2 hz) (differentiableAt_spatialSlice hC0 hz)

/-- On the axis the rescaled potential vorticity is the radial derivative
`δ² ∂_r ∂_z V_n - ∂_r ∂_r W_n`: this is the continuous extension `Ω = ∂_r ω_θ` of
`eq:aniso:zoom:finite:identities` written in the rescaled variables. -/
private theorem zoomOmega_axis_eq (lam h zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    {p : (ℝ × ℝ) × ℝ} (hp : zoomPoint lam h zc p ∈ unitCylinder) (hR : p.1.1 = 0) :
    zoomOmega lam h zc u p
      = (lam ^ (2 * h)) ^ 2 * dr (dz (zoomV lam h zc u)) p - dr (dr (zoomW lam h zc u)) p := by
  have hδμ : lam ^ (2 * h) * lam ^ (1 - 2 * h) = lam := by
    calc
      lam ^ (2 * h) * lam ^ (1 - 2 * h) = lam ^ ((2 * h) + (1 - 2 * h)) := by
        rw [Real.rpow_add hlam]
      _ = lam ^ (1 : ℝ) := by
        congr 1
        ring
      _ = lam := by simp
  have hkey : lam ^ 3 * lam ^ (2 * h)
      = (lam ^ (2 * h)) ^ 2 * (lam ^ 2 * lam ^ (1 - 2 * h)) := by
    calc
      lam ^ 3 * lam ^ (2 * h) = lam ^ (2 * h) * lam ^ 2 * lam := by ring
      _ = lam ^ (2 * h) * lam ^ 2 * (lam ^ (2 * h) * lam ^ (1 - 2 * h)) := by rw [hδμ]
      _ = (lam ^ (2 * h)) ^ 2 * (lam ^ 2 * lam ^ (1 - 2 * h)) := by ring
  have hz0 : (zoomPoint lam h zc p).1 0 = 0 := by
    simp [zoomPoint, meridional, hR]
  have hpv : potentialVorticity u (zoomPoint lam h zc p)
      = spatialPartial (azimuthalVorticity u) 0 (zoomPoint lam h zc p) := by
    unfold potentialVorticity
    split_ifs with hcase
    · rfl
    · exact absurd hz0 hcase
  have hsplit := spatialPartial_azimuthalVorticity_zero u hu hp
  rw [drdz_zoomV lam h zc u hu p hp, drdr_zoomW lam h zc u hu p hp]
  unfold zoomOmega
  rw [hpv, hsplit]
  calc
    lam ^ 3 * lam ^ (2 * h) *
        (meridionalPartial (fun w => u w 0) 1 1 (zoomPoint lam h zc p)
          - meridionalPartial (fun w => u w 2) 2 0 (zoomPoint lam h zc p))
        = lam ^ 3 * lam ^ (2 * h) *
            meridionalPartial (fun w => u w 0) 1 1 (zoomPoint lam h zc p)
          - lam ^ 3 * lam ^ (2 * h) *
            meridionalPartial (fun w => u w 2) 2 0 (zoomPoint lam h zc p) := by ring
    _ = (lam ^ (2 * h)) ^ 2 * (lam ^ 2 * lam ^ (1 - 2 * h)) *
            meridionalPartial (fun w => u w 0) 1 1 (zoomPoint lam h zc p)
          - (lam ^ (2 * h)) ^ 2 * (lam ^ 2 * lam ^ (1 - 2 * h)) *
            meridionalPartial (fun w => u w 2) 2 0 (zoomPoint lam h zc p) := by rw [hkey]
    _ = (lam ^ (2 * h)) ^ 2 * (lam ^ 2 * lam ^ (1 - 2 * h) *
            meridionalPartial (fun w => u w 0) 1 1 (zoomPoint lam h zc p))
          - lam ^ 3 * lam ^ (2 * h) *
            meridionalPartial (fun w => u w 2) 2 0 (zoomPoint lam h zc p) := by
        rw [hkey]
        ring

/-- The finite-axis bound `eq:aniso:zoom:finite:bound` on the axis itself, where the
continuous extension of `Ω_n` is `δ² ∂_r ∂_z V_n - ∂_r ∂_r W_n`. -/
theorem abs_zoomOmega_axis_le {C h lam zc : ℝ} (hlam : 0 < lam) {u : ParabolicPoint → Vec3}
    (hb : AnisotropicBounds C h u) (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    {p : (ℝ × ℝ) × ℝ} (hp : zoomPoint lam h zc p ∈ unitCylinder) (hR : p.1.1 = 0) :
    |zoomOmega lam h zc u p|
      ≤ C * ((lam ^ (2 * h)) ^ 2 * (-p.2) ^ (-(3 / 2 : ℝ) + h)
          + (-p.2) ^ (-(3 / 2 : ℝ) - h)) := by
  have hδ : (0 : ℝ) ≤ (lam ^ (2 * h)) ^ 2 := by positivity
  have hV : |dr (dz (zoomV lam h zc u)) p| ≤ C * (-p.2) ^ (-(3 / 2 : ℝ) + h) := by
    have hbnd := abs_drdz_zoomV_le C h lam zc hlam u hb hu p hp
    have hexp : -(1 / 2 : ℝ) - 1 / 2 - (1 / 2 - h) * 1 = -(3 / 2 : ℝ) + h := by ring
    rw [hexp] at hbnd
    exact hbnd
  have hW : |dr (dr (zoomW lam h zc u)) p| ≤ C * (-p.2) ^ (-(3 / 2 : ℝ) - h) := by
    have hbnd := abs_drdr_zoomW_add_abs_drdr_zoomS_le C h lam zc hlam u hb hu p hp
    have hS : (0 : ℝ) ≤ |dr (dr (zoomS lam h zc u)) p| := abs_nonneg _
    have hWbnd : |dr (dr (zoomW lam h zc u)) p|
        ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - h - 2 / 2 - (1 / 2 - h) * 0) := by
      linarith only [hbnd, hS]
    have hexp : -(1 / 2 : ℝ) - h - 2 / 2 - (1 / 2 - h) * 0 = -(3 / 2 : ℝ) - h := by ring
    rw [hexp] at hWbnd
    exact hWbnd
  rw [zoomOmega_axis_eq lam h zc hlam u hu hp hR]
  refine le_trans (abs_sub_smul_le hδ hV hW) (le_of_eq ?_)
  ring

/-- The finite-axis bound `eq:aniso:zoom:finite:bound` at every point of the rescaled
cylinder, on and off the axis. -/
theorem abs_zoomOmega_le_of_mem {C h lam zc : ℝ} (hlam : 0 < lam) {u : ParabolicPoint → Vec3}
    (hb : AnisotropicBounds C h u) (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    |zoomOmega lam h zc u p|
      ≤ C * ((lam ^ (2 * h)) ^ 2 * (-p.2) ^ (-(3 / 2 : ℝ) + h)
          + (-p.2) ^ (-(3 / 2 : ℝ) - h)) := by
  rcases eq_or_ne p.1.1 0 with hR | hR
  · exact abs_zoomOmega_axis_le hlam hb hu hp hR
  · exact abs_zoomOmega_le hlam hb hu haxi hp hR

/-- The uniform-in-`n` form of `eq:aniso:zoom:finite:bound` used by the comparison argument:
once the rescaled time satisfies `τ ≤ -1` and the anisotropic ratio `δ = λ^{2h}` is at most
`1`, both powers of `-τ` are at most `1` and the finite-axis bound collapses to `2C`. -/
theorem abs_zoomOmega_le_two_mul_const {C h lam zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (hC : 0 ≤ C)
    (hδ : lam ^ (2 * h) ≤ 1) (hh0 : 0 < h) (hh1 : h < 1 / 2) (hτ : p.2 ≤ -1) :
    |zoomOmega lam h zc u p| ≤ 2 * C := by
  refine le_trans (abs_zoomOmega_le_of_mem hlam hb hu haxi hp) ?_
  exact finite_axis_bound_le hC (Real.rpow_nonneg hlam.le _) hδ hτ ⟨hh0, hh1⟩

/-! ### The Step 2 drift bounds -/

/-- For `τ ≤ -1` a nonpositive shift of the exponent only decreases the power of `-τ`. -/
private theorem mul_rpow_le_mul_rpow_neg_half {C τ e : ℝ} (hC : 0 ≤ C) (hτ : τ ≤ -1)
    (he : e ≤ -(1 / 2 : ℝ)) : C * (-τ) ^ e ≤ C * (-τ) ^ (-(1 / 2 : ℝ)) :=
  mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith only [hτ]) he) hC

/-- Drift bound for `V_n` (`eq:aniso:zoom:derivatives`, exponent `-1/2`). -/
theorem abs_zoomV_le_rpow_neg_half {C h lam zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (hC : 0 ≤ C) (hτ : p.2 ≤ -1) :
    |zoomV lam h zc u p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  refine le_trans (abs_zoomV_le C h lam zc hlam u hb p hp) ?_
  exact mul_rpow_le_mul_rpow_neg_half hC hτ (by norm_num)

/-- Drift bound for `∂_r V_n` (`eq:aniso:zoom:derivatives`, exponent `-1`). -/
theorem abs_dr_zoomV_le_rpow_neg_half {C h lam zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (hC : 0 ≤ C) (hτ : p.2 ≤ -1) :
    |dr (zoomV lam h zc u) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  refine le_trans (abs_dr_zoomV_le C h lam zc hlam u hb hu p hp) ?_
  exact mul_rpow_le_mul_rpow_neg_half hC hτ (by norm_num)

/-- Drift bound for `∂_z V_n` (`eq:aniso:zoom:derivatives`, exponent `-1 + h`). -/
theorem abs_dz_zoomV_le_rpow_neg_half {C h lam zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (hC : 0 ≤ C) (hh1 : h ≤ 1 / 2)
    (hτ : p.2 ≤ -1) :
    |dz (zoomV lam h zc u) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  refine le_trans (abs_dz_zoomV_le C h lam zc hlam u hb hu p hp) ?_
  exact mul_rpow_le_mul_rpow_neg_half hC hτ (by linarith only [hh1])

/-- Drift bound for `W_n` (`eq:aniso:zoom:derivatives`, exponent `-1/2 - h`). -/
theorem abs_zoomW_le_rpow_neg_half {C h lam zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hτ : p.2 ≤ -1) :
    |zoomW lam h zc u p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  have hdrop : |zoomW lam h zc u p|
      ≤ |zoomW lam h zc u p| + |zoomS lam h zc u p| :=
    le_add_of_nonneg_right (abs_nonneg _)
  refine le_trans (le_trans hdrop (abs_zoomW_add_abs_zoomS_le C h lam zc hlam u hb p hp)) ?_
  exact mul_rpow_le_mul_rpow_neg_half hC hτ (by linarith only [hh0])

/-- Drift bound for `∂_r W_n` (`eq:aniso:zoom:derivatives`, exponent `-1 - h`). -/
theorem abs_dr_zoomW_le_rpow_neg_half {C h lam zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hτ : p.2 ≤ -1) :
    |dr (zoomW lam h zc u) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  have hdrop : |dr (zoomW lam h zc u) p|
      ≤ |dr (zoomW lam h zc u) p| + |dr (zoomS lam h zc u) p| :=
    le_add_of_nonneg_right (abs_nonneg _)
  refine le_trans
    (le_trans hdrop (abs_dr_zoomW_add_abs_dr_zoomS_le C h lam zc hlam u hb hu p hp)) ?_
  exact mul_rpow_le_mul_rpow_neg_half hC hτ (by linarith only [hh0])

/-- Drift bound for `∂_z W_n` (`eq:aniso:zoom:derivatives`, exponent `-1`). -/
theorem abs_dz_zoomW_le_rpow_neg_half {C h lam zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (hC : 0 ≤ C) (hτ : p.2 ≤ -1) :
    |dz (zoomW lam h zc u) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  have hdrop : |dz (zoomW lam h zc u) p|
      ≤ |dz (zoomW lam h zc u) p| + |dz (zoomS lam h zc u) p| :=
    le_add_of_nonneg_right (abs_nonneg _)
  refine le_trans
    (le_trans hdrop (abs_dz_zoomW_add_abs_dz_zoomS_le C h lam zc hlam u hb hu p hp)) ?_
  exact mul_rpow_le_mul_rpow_neg_half hC hτ (by norm_num)


/-! ### The quotient of the radial velocity by the radius -/

/-- The radial velocity of an axisymmetric field vanishes on the axis of the zoom-in map
(the standing assumptions of Section `sec:aniso:equations`). At `p.1.1 = 0` the zoom point
lies on the rotation axis, so `apply_axis_zero` forces `u_r = 0` and hence `zoomV = 0`. -/
theorem zoomV_axis (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (haxi : IsAxisymmetricOn u unitCylinder) {Z τ : ℝ}
    (hp : zoomPoint lam h zc ((0, Z), τ) ∈ unitCylinder) :
    zoomV lam h zc u ((0, Z), τ) = 0 := by
  have h0 : (zoomPoint lam h zc ((0, Z), τ)).1 0 = 0 := by
    simp [zoomPoint, meridional]
  have h1 : (zoomPoint lam h zc ((0, Z), τ)).1 1 = 0 := by
    simp [zoomPoint, meridional]
  have hu : u (zoomPoint lam h zc ((0, Z), τ)) 0 = 0 :=
    apply_axis_zero haxi hp h0 h1
  unfold zoomV
  rw [hu]
  simp

/-- `|V_n/R| ≤ sup |∂_R V_n|` along the radial segment to the axis, the estimate recorded
before `eq:drift:Bn:def`: `V_n` vanishes at `R = 0`, the segment stays in the preimage of the
unit cylinder, and `eq:aniso:zoom:derivatives` bounds `∂_R V_n` there by `C (-τ)^{-1/2}` once
`τ ≤ -1`. -/
theorem abs_zoomV_div_le {C h lam zc : ℝ} (hlam : 0 < lam) {u : ParabolicPoint → Vec3}
    (hb : AnisotropicBounds C h u) (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (hR : p.1.1 ≠ 0) (hC : 0 ≤ C) (hτ : p.2 ≤ -1) :
    |zoomV lam h zc u p / p.1.1| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  set g := fun r : ℝ => zoomV lam h zc u ((r, p.1.2), p.2) with hg
  have hg0 : g 0 = 0 := by
    rw [hg]
    have hmem : zoomPoint lam h zc ((0, p.1.2), p.2) ∈ unitCylinder :=
      zoomPoint_slice_mem lam h zc hlam hp hR left_mem_uIcc
    have hzero : zoomV lam h zc u ((0, p.1.2), p.2) = 0 :=
      zoomV_axis lam h zc u haxi hmem
    simp [hzero]
  have h_diff : ∀ s ∈ uIcc (0 : ℝ) p.1.1, DifferentiableAt ℝ g s := by
    intro s hs
    rw [hg]
    have hmem : zoomPoint lam h zc ((s, p.1.2), p.2) ∈ unitCylinder :=
      zoomPoint_slice_mem lam h zc hlam hp hR hs
    have h_deriv : HasDerivAt (fun r : ℝ => u (zoomPoint lam h zc ((r, p.1.2), p.2)) 0)
        (lam * spatialPartial (fun w => u w 0) 0 (zoomPoint lam h zc ((s, p.1.2), p.2)))
        s :=
      hasDerivAt_comp_spatialSlice (hu.of_le (by norm_num)) hmem
        (hasDerivAt_meridional_fst lam (zc + lam ^ (1 - 2 * h) * p.1.2) s) rfl 0
    have h_zoomV : HasDerivAt (fun r : ℝ => zoomV lam h zc u ((r, p.1.2), p.2))
        (lam * (lam * spatialPartial (fun w => u w 0) 0
          (zoomPoint lam h zc ((s, p.1.2), p.2)))) s := by
      simpa [zoomV, mul_assoc] using h_deriv.const_mul lam
    exact h_zoomV.differentiableAt
  have h_bound : ∀ s ∈ uIcc (0 : ℝ) p.1.1, |deriv g s| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
    intro s hs
    have hmem : zoomPoint lam h zc ((s, p.1.2), p.2) ∈ unitCylinder :=
      zoomPoint_slice_mem lam h zc hlam hp hR hs
    have hgoal : |dr (zoomV lam h zc u) ((s, p.1.2), p.2)| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) :=
      abs_dr_zoomV_le_rpow_neg_half hlam hb hu hmem hC hτ
    simpa [hg, dr] using hgoal
  exact abs_div_le_of_deriv_bound hg0 h_diff h_bound hR

/-! ### The lifted drift of Step 2 -/

/-- The radius `R = |X|` of the four-dimensional part of the lifted spatial variable
`(X, Z) ∈ ℝ⁴ × ℝ`, in which the radial operator `∂_RR + 3R⁻¹∂_R` of
`eq:aniso:zoom:finite:equation` is the Laplacian of `ℝ⁴` acting on radial functions. -/
@[expose] def zoomLiftRadius (X : Vec 5) : ℝ :=
  Real.sqrt (X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2)

/-- The meridional point `(R, Z, τ) = (|X|, Z, τ)` underlying the lifted point `(X, Z, τ)`. -/
@[expose] def zoomLiftPoint (q : Vec 5 × ℝ) : (ℝ × ℝ) × ℝ :=
  ((zoomLiftRadius q.1, q.1 4), q.2)

/-- The lifted radius is nonnegative. -/
theorem zoomLiftRadius_nonneg (X : Vec 5) : 0 ≤ zoomLiftRadius X := Real.sqrt_nonneg _

/-- Each of the four radial coordinates is bounded by the lifted radius. -/
theorem abs_le_zoomLiftRadius (X : Vec 5) {i : Fin 5} (hi : i ≠ 4) :
    |X i| ≤ zoomLiftRadius X := by
  have key : ∀ a b : ℝ, 0 ≤ b → |a| ≤ Real.sqrt (a ^ 2 + b) := by
    intro a b hb
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith only [hb])
  rw [zoomLiftRadius]
  fin_cases i
  · exact le_of_le_of_eq (key (X 0) (X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2) (by positivity))
      (by congr 1; ring)
  · exact le_of_le_of_eq (key (X 1) (X 0 ^ 2 + X 2 ^ 2 + X 3 ^ 2) (by positivity))
      (by congr 1; ring)
  · exact le_of_le_of_eq (key (X 2) (X 0 ^ 2 + X 1 ^ 2 + X 3 ^ 2) (by positivity))
      (by congr 1; ring)
  · exact le_of_le_of_eq (key (X 3) (X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2) (by positivity))
      (by congr 1; ring)
  · exact absurd rfl hi

/-- The direction field `X/|X|` is bounded by one, including at the axis, where the junk value
of the division is `0`. -/
theorem abs_div_zoomLiftRadius_le_one (X : Vec 5) {i : Fin 5} (hi : i ≠ 4) :
    |X i / zoomLiftRadius X| ≤ 1 := by
  rcases eq_or_lt_of_le (zoomLiftRadius_nonneg X) with hR | hR
  · rw [← hR, div_zero, abs_zero]
    norm_num
  · rw [abs_div, abs_of_pos hR, div_le_one hR]
    exact abs_le_zoomLiftRadius X hi

/-- The Step 2 drift `eq:drift:Bn:def`, `B_n(X, Z, τ) = (V_n(|X|, Z, τ) X/|X|, W_n(|X|, Z, τ))`
on `ℝ⁴ × ℝ`. The four radial components take the value `0` on the axis `X = 0`, which is both
the junk value of the division and, since `V_n` vanishes there by `zoomV_axis`, the continuous
extension. -/
@[expose] def zoomDrift (lam h zc : ℝ) (u : ParabolicPoint → Vec3) (q : Vec 5 × ℝ) : Vec 5 :=
  fun i =>
  if i = 4 then zoomW lam h zc u (zoomLiftPoint q)
  else zoomV lam h zc u (zoomLiftPoint q) * (q.1 i / zoomLiftRadius q.1)

/-- The four radial components of the lifted drift vanish on the axis. -/
theorem zoomDrift_apply_axis (lam h zc : ℝ) (u : ParabolicPoint → Vec3) {q : Vec 5 × ℝ}
    (hR : zoomLiftRadius q.1 = 0) {i : Fin 5} (hi : i ≠ 4) : zoomDrift lam h zc u q i = 0 := by
  rw [zoomDrift]
  split_ifs with hcase
  · exact absurd hcase hi
  · rw [hR, div_zero, mul_zero]

/-- The uniform bound `|B_n| ≤ C |τ|^{-1/2}` for `τ ≤ -1` on the lifted drift of
`eq:drift:Bn:def`: the four radial components are `V_n` times a direction vector of length at
most one, and the vertical component is `W_n`, so the two drift bounds of
`eq:aniso:zoom:derivatives` bound every component. -/
theorem norm_zoomDrift_le {C h lam zc : ℝ} (hlam : 0 < lam) {u : ParabolicPoint → Vec3}
    (hb : AnisotropicBounds C h u) {q : Vec 5 × ℝ}
    (hp : zoomPoint lam h zc (zoomLiftPoint q) ∈ unitCylinder) (hC : 0 ≤ C) (hh0 : 0 ≤ h)
    (hτ : q.2 ≤ -1) :
    ‖zoomDrift lam h zc u q‖ ≤ C * (-q.2) ^ (-(1 / 2 : ℝ)) := by
  have hbound : (0 : ℝ) ≤ C * (-q.2) ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hC (Real.rpow_nonneg (by linarith only [hτ]) _)
  rw [pi_norm_le_iff_of_nonneg hbound]
  intro i
  rw [Real.norm_eq_abs, zoomDrift]
  split_ifs with hi
  · exact abs_zoomW_le_rpow_neg_half hlam hb hp hC hh0 hτ
  · rw [abs_mul]
    have hV := abs_zoomV_le_rpow_neg_half hlam hb hp hC hτ
    have hX := abs_div_zoomLiftRadius_le_one q.1 hi
    calc |zoomV lam h zc u (zoomLiftPoint q)| * |q.1 i / zoomLiftRadius q.1|
        ≤ |zoomV lam h zc u (zoomLiftPoint q)| * 1 :=
          mul_le_mul_of_nonneg_left hX (abs_nonneg _)
      _ = |zoomV lam h zc u (zoomLiftPoint q)| := mul_one _
      _ ≤ C * (-q.2) ^ (-(1 / 2 : ℝ)) := hV


/-! ### The divergence of the lifted drift -/

/-- Freezing all but one of the four radial coordinates leaves the lifted radius a function
`s ↦ √(s² + rest)` of the remaining one, with `rest` the sum of the other three squares. -/
theorem exists_zoomLiftRadius_update (X : Vec 5) {i : Fin 5} (hi : i ≠ 4) :
    ∃ rest : ℝ, 0 ≤ rest ∧
      ∀ s : ℝ, zoomLiftRadius (Function.update X i s) = Real.sqrt (s ^ 2 + rest) := by
  fin_cases i
  · refine ⟨X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2, by positivity, fun s => ?_⟩
    simp only [zoomLiftRadius, Function.update_apply]
    norm_num
    ring_nf
  · refine ⟨X 0 ^ 2 + X 2 ^ 2 + X 3 ^ 2, by positivity, fun s => ?_⟩
    simp only [zoomLiftRadius, Function.update_apply]
    norm_num
    ring_nf
  · refine ⟨X 0 ^ 2 + X 1 ^ 2 + X 3 ^ 2, by positivity, fun s => ?_⟩
    simp only [zoomLiftRadius, Function.update_apply]
    norm_num
    ring_nf
  · refine ⟨X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2, by positivity, fun s => ?_⟩
    simp only [zoomLiftRadius, Function.update_apply]
    norm_num
    ring_nf
  · exact absurd rfl hi

/-- The lifted radius does not depend on the vertical coordinate. -/
theorem zoomLiftRadius_update_four (X : Vec 5) (s : ℝ) :
    zoomLiftRadius (Function.update X 4 s) = zoomLiftRadius X := by
  simp only [zoomLiftRadius, Function.update_apply]
  norm_num

/-- `∂_s √(s² + rest) = s/√(s² + rest)` away from the origin. -/
theorem hasDerivAt_sqrt_sq_add {rest a : ℝ} (hpos : 0 < a ^ 2 + rest) :
    HasDerivAt (fun s : ℝ => Real.sqrt (s ^ 2 + rest)) (a / Real.sqrt (a ^ 2 + rest)) a := by
  have hinner : HasDerivAt (fun s : ℝ => s ^ 2 + rest) (2 * a) a := by
    simpa using (hasDerivAt_pow 2 a).add_const rest
  have hcomp : HasDerivAt (fun s : ℝ => Real.sqrt (s ^ 2 + rest))
      (1 / (2 * Real.sqrt (a ^ 2 + rest)) * (2 * a)) a :=
    (Real.hasDerivAt_sqrt hpos.ne').comp a hinner
  have hRne : Real.sqrt (a ^ 2 + rest) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  convert hcomp using 1
  field_simp

/-- `∂_s (s/√(s² + rest)) = rest/(s² + rest)^{3/2}` away from the origin: this is the
`1/R - X_i²/R³` entry of the matrix `∇_X(V_n X/R)`. -/
private theorem hasDerivAt_div_sqrt_sq_add {rest a : ℝ} (hpos : 0 < a ^ 2 + rest) :
    HasDerivAt (fun s : ℝ => s / Real.sqrt (s ^ 2 + rest))
      (rest / Real.sqrt (a ^ 2 + rest) ^ 3) a := by
  have hRne : Real.sqrt (a ^ 2 + rest) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hR2 : Real.sqrt (a ^ 2 + rest) ^ 2 = a ^ 2 + rest := Real.sq_sqrt hpos.le
  have hquot : HasDerivAt (fun s : ℝ => s / Real.sqrt (s ^ 2 + rest))
      ((1 * Real.sqrt (a ^ 2 + rest) - a * (a / Real.sqrt (a ^ 2 + rest)))
        / Real.sqrt (a ^ 2 + rest) ^ 2) a :=
    (hasDerivAt_id a).div (hasDerivAt_sqrt_sq_add hpos) hRne
  convert hquot using 1
  have step : (1 * Real.sqrt (a ^ 2 + rest) - a * (a / Real.sqrt (a ^ 2 + rest)))
      / Real.sqrt (a ^ 2 + rest) ^ 2
      = (Real.sqrt (a ^ 2 + rest) ^ 2 - a ^ 2) / Real.sqrt (a ^ 2 + rest) ^ 3 := by
    field_simp
  rw [step, hR2]
  ring_nf

/-- `V_n` restricted to a radial slice has derivative `∂_R V_n`. -/
theorem hasDerivAt_zoomV_radial (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    HasDerivAt (fun r : ℝ => zoomV lam h zc u ((r, p.1.2), p.2))
      (dr (zoomV lam h zc u) p) p.1.1 := by
  have hbase := (hasDerivAt_zoom_component_r lam h zc hu p hp 0).const_mul lam
  have heq : lam * (lam * spatialPartial (fun w => u w 0) 0 (zoomPoint lam h zc p))
      = lam ^ 2 * spatialPartial (fun w => u w 0) 0 (zoomPoint lam h zc p) := by ring
  rw [heq] at hbase
  rw [dr_zoomV lam h zc u hu p hp]
  exact hbase

/-- `W_n` restricted to a radial slice has derivative `∂_R W_n`. -/
theorem hasDerivAt_zoomW_radial (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    HasDerivAt (fun r : ℝ => zoomW lam h zc u ((r, p.1.2), p.2))
      (dr (zoomW lam h zc u) p) p.1.1 := by
  have hbase := (hasDerivAt_zoom_component_r lam h zc hu p hp 2).const_mul (lam * lam ^ (2 * h))
  have heq : lam * lam ^ (2 * h) *
        (lam * spatialPartial (fun w => u w 2) 0 (zoomPoint lam h zc p))
      = lam ^ 2 * lam ^ (2 * h) *
        spatialPartial (fun w => u w 2) 0 (zoomPoint lam h zc p) := by ring
  rw [heq] at hbase
  rw [dr_zoomW lam h zc u hu p hp]
  exact hbase

/-- `V_n` restricted to a vertical slice has derivative `∂_Z V_n`. -/
theorem hasDerivAt_zoomV_vertical (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    HasDerivAt (fun s : ℝ => zoomV lam h zc u ((p.1.1, s), p.2))
      (dz (zoomV lam h zc u) p) p.1.2 := by
  have hbase := (hasDerivAt_zoom_component_z lam h zc hu p hp 0).const_mul lam
  have heq : lam * (lam ^ (1 - 2 * h) *
        spatialPartial (fun w => u w 0) 2 (zoomPoint lam h zc p))
      = lam * lam ^ (1 - 2 * h) *
        spatialPartial (fun w => u w 0) 2 (zoomPoint lam h zc p) := by ring
  rw [heq] at hbase
  rw [dz_zoomV lam h zc u hu p hp]
  exact hbase

/-- `W_n` restricted to a vertical slice has derivative `∂_Z W_n`. -/
theorem hasDerivAt_zoomW_vertical (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    HasDerivAt (fun s : ℝ => zoomW lam h zc u ((p.1.1, s), p.2))
      (dz (zoomW lam h zc u) p) p.1.2 := by
  have hbase := (hasDerivAt_zoom_component_z lam h zc hu p hp 2).const_mul (lam * lam ^ (2 * h))
  have heq : lam * lam ^ (2 * h) * (lam ^ (1 - 2 * h) *
        spatialPartial (fun w => u w 2) 2 (zoomPoint lam h zc p))
      = lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) *
        spatialPartial (fun w => u w 2) 2 (zoomPoint lam h zc p) := by ring
  rw [heq] at hbase
  rw [dz_zoomW lam h zc u hu p hp]
  exact hbase

/-- The `i`-th diagonal entry of `∇_X(V_n X/R)` for one of the four radial coordinates:
`∂_{X_i}(V_n X_i/R) = ∂_R V_n · X_i²/R² + V_n (R² - X_i²)/R³`, away from the axis. -/
theorem deriv_zoomDrift_coord (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    {q : Vec 5 × ℝ} (hp : zoomPoint lam h zc (zoomLiftPoint q) ∈ unitCylinder)
    (hR : 0 < zoomLiftRadius q.1) {i : Fin 5} (hi : i ≠ 4) :
    deriv (fun s : ℝ => zoomDrift lam h zc u (Function.update q.1 i s, q.2) i) (q.1 i)
      = dr (zoomV lam h zc u) (zoomLiftPoint q) * (q.1 i ^ 2 / zoomLiftRadius q.1 ^ 2)
        + zoomV lam h zc u (zoomLiftPoint q)
            * ((zoomLiftRadius q.1 ^ 2 - q.1 i ^ 2) / zoomLiftRadius q.1 ^ 3) := by
  obtain ⟨rest, hrest0, hrest⟩ := exists_zoomLiftRadius_update q.1 hi
  have hReq : zoomLiftRadius q.1 = Real.sqrt (q.1 i ^ 2 + rest) := by
    have hval := hrest (q.1 i)
    rwa [Function.update_eq_self] at hval
  have hpos : 0 < q.1 i ^ 2 + rest := by
    rw [hReq] at hR
    exact Real.sqrt_pos.mp hR
  have hRne : zoomLiftRadius q.1 ≠ 0 := ne_of_gt hR
  have hR2 : zoomLiftRadius q.1 ^ 2 = q.1 i ^ 2 + rest := by
    rw [hReq]
    exact Real.sq_sqrt hpos.le
  have hfun : (fun s : ℝ => zoomDrift lam h zc u (Function.update q.1 i s, q.2) i)
      = fun s : ℝ => zoomV lam h zc u ((Real.sqrt (s ^ 2 + rest), q.1 4), q.2)
          * (s / Real.sqrt (s ^ 2 + rest)) := by
    funext s
    rw [zoomDrift]
    split_ifs with hcase
    · exact absurd hcase hi
    · simp only [zoomLiftPoint, hrest s, Function.update_self,
        Function.update_of_ne (Ne.symm hi)]
  have hV : HasDerivAt (fun r : ℝ => zoomV lam h zc u ((r, q.1 4), q.2))
      (dr (zoomV lam h zc u) (zoomLiftPoint q)) (Real.sqrt (q.1 i ^ 2 + rest)) := by
    rw [← hReq]
    exact hasDerivAt_zoomV_radial lam h zc u hu (zoomLiftPoint q) hp
  have hA := hV.comp (q.1 i) (hasDerivAt_sqrt_sq_add hpos)
  have hB := hasDerivAt_div_sqrt_sq_add hpos
  have hmul : HasDerivAt
      (fun s : ℝ => zoomV lam h zc u ((Real.sqrt (s ^ 2 + rest), q.1 4), q.2)
        * (s / Real.sqrt (s ^ 2 + rest)))
      (dr (zoomV lam h zc u) (zoomLiftPoint q) * (q.1 i / Real.sqrt (q.1 i ^ 2 + rest))
          * (q.1 i / Real.sqrt (q.1 i ^ 2 + rest))
        + zoomV lam h zc u ((Real.sqrt (q.1 i ^ 2 + rest), q.1 4), q.2)
            * (rest / Real.sqrt (q.1 i ^ 2 + rest) ^ 3)) (q.1 i) := hA.mul hB
  have hrest_eq : rest = zoomLiftRadius q.1 ^ 2 - q.1 i ^ 2 := by
    rw [hR2]
    ring
  rw [hfun, hmul.deriv, ← hReq, hrest_eq]
  simp only [zoomLiftPoint]
  field_simp

/-- The vertical entry of `∇B_n`: the fifth component of the lifted drift depends on the
fifth coordinate through `W_n` alone, so its derivative is `∂_Z W_n`. -/
theorem deriv_zoomDrift_vertical (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    {q : Vec 5 × ℝ} (hp : zoomPoint lam h zc (zoomLiftPoint q) ∈ unitCylinder) :
    deriv (fun s : ℝ => zoomDrift lam h zc u (Function.update q.1 4 s, q.2) 4) (q.1 4)
      = dz (zoomW lam h zc u) (zoomLiftPoint q) := by
  have hfun : (fun s : ℝ => zoomDrift lam h zc u (Function.update q.1 4 s, q.2) 4)
      = fun s : ℝ => zoomW lam h zc u ((zoomLiftRadius q.1, s), q.2) := by
    funext s
    rw [zoomDrift]
    split_ifs with hcase
    · simp only [zoomLiftPoint, zoomLiftRadius_update_four, Function.update_self]
    · exact absurd rfl hcase
  rw [hfun]
  exact (hasDerivAt_zoomW_vertical lam h zc u hu (zoomLiftPoint q) hp).deriv

/-- The vertical entry of a radial row of `∇B_n`: a radial component `j` of the lifted drift,
differentiated in the vertical direction, depends on the fifth coordinate through `V_n` alone,
scaled by the fixed direction cosine `X_j/R`. No positivity of the radius is needed, since the
factor `X_j/R` is unchanged by the differentiation. -/
theorem deriv_zoomDrift_coord_dz (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    {q : Vec 5 × ℝ} (hp : zoomPoint lam h zc (zoomLiftPoint q) ∈ unitCylinder)
    {j : Fin 5} (hj : j ≠ 4) :
    deriv (fun s : ℝ => zoomDrift lam h zc u (Function.update q.1 4 s, q.2) j) (q.1 4)
      = dz (zoomV lam h zc u) (zoomLiftPoint q) * (q.1 j / zoomLiftRadius q.1) := by
  have hfun : (fun s : ℝ => zoomDrift lam h zc u (Function.update q.1 4 s, q.2) j)
      = fun s : ℝ =>
          zoomV lam h zc u ((zoomLiftRadius q.1, s), q.2) * (q.1 j / zoomLiftRadius q.1) := by
    funext s
    rw [zoomDrift]
    split_ifs with hcase
    · exact absurd hcase hj
    · simp only [zoomLiftPoint, zoomLiftRadius_update_four, Function.update_self,
        Function.update_of_ne hj]
  rw [hfun]
  exact ((hasDerivAt_zoomV_vertical lam h zc u hu (zoomLiftPoint q) hp).mul_const
    (q.1 j / zoomLiftRadius q.1)).deriv

/-- The radial entry of the vertical row of `∇B_n`: the vertical component of the lifted
drift, differentiated in a radial direction `i`, is `∂_R W_n` at the underlying meridional
point, scaled by the direction cosine `X_i/R`, exactly as in `hasDerivAt_zoomV_radial`'s
composition with the lifted radius but for `W_n` in place of `V_n`. -/
theorem deriv_zoomDrift_vertical_dr (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    {q : Vec 5 × ℝ} (hp : zoomPoint lam h zc (zoomLiftPoint q) ∈ unitCylinder)
    (hR : 0 < zoomLiftRadius q.1) {i : Fin 5} (hi : i ≠ 4) :
    deriv (fun s : ℝ => zoomDrift lam h zc u (Function.update q.1 i s, q.2) 4) (q.1 i)
      = dr (zoomW lam h zc u) (zoomLiftPoint q) * (q.1 i / zoomLiftRadius q.1) := by
  obtain ⟨rest, hrest0, hrest⟩ := exists_zoomLiftRadius_update q.1 hi
  have hReq : zoomLiftRadius q.1 = Real.sqrt (q.1 i ^ 2 + rest) := by
    have hval := hrest (q.1 i)
    rwa [Function.update_eq_self] at hval
  have hpos : 0 < q.1 i ^ 2 + rest := by
    rw [hReq] at hR
    exact Real.sqrt_pos.mp hR
  have hfun : (fun s : ℝ => zoomDrift lam h zc u (Function.update q.1 i s, q.2) 4)
      = fun s : ℝ => zoomW lam h zc u ((Real.sqrt (s ^ 2 + rest), q.1 4), q.2) := by
    funext s
    rw [zoomDrift]
    split_ifs with hcase
    · simp only [zoomLiftPoint, hrest s, Function.update_of_ne (Ne.symm hi)]
    · exact absurd rfl hcase
  rw [hfun]
  have hW : HasDerivAt (fun r : ℝ => zoomW lam h zc u ((r, q.1 4), q.2))
      (dr (zoomW lam h zc u) (zoomLiftPoint q)) (Real.sqrt (q.1 i ^ 2 + rest)) := by
    rw [← hReq]
    exact hasDerivAt_zoomW_radial lam h zc u hu (zoomLiftPoint q) hp
  have hA := hW.comp (q.1 i) (hasDerivAt_sqrt_sq_add hpos)
  rw [← hReq] at hA
  exact hA.deriv

/-- Away from the axis, the `j`-th radial component of the lifted drift, differentiated in a
*different* radial coordinate `i`, depends on `i` only through the common factor `V_n/R`:
`X_j` is held fixed by the update, so the product rule leaves only the derivative of the
quotient `V_n(R(s), Z)/R(s)`, computed exactly as in `deriv_zoomDrift_coord` but without the
extra `s/R(s)` factor that appears there when `i = j`. -/
theorem deriv_zoomDrift_offdiag (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    {q : Vec 5 × ℝ} (hp : zoomPoint lam h zc (zoomLiftPoint q) ∈ unitCylinder)
    (hR : 0 < zoomLiftRadius q.1) {i j : Fin 5} (hi : i ≠ 4) (hj : j ≠ 4) (hij : i ≠ j) :
    deriv (fun s : ℝ => zoomDrift lam h zc u (Function.update q.1 i s, q.2) j) (q.1 i)
      = dr (zoomV lam h zc u) (zoomLiftPoint q) * (q.1 i * q.1 j / zoomLiftRadius q.1 ^ 2)
        - zoomV lam h zc u (zoomLiftPoint q) * (q.1 i * q.1 j / zoomLiftRadius q.1 ^ 3) := by
  obtain ⟨rest, hrest0, hrest⟩ := exists_zoomLiftRadius_update q.1 hi
  have hReq : zoomLiftRadius q.1 = Real.sqrt (q.1 i ^ 2 + rest) := by
    have hval := hrest (q.1 i)
    rwa [Function.update_eq_self] at hval
  have hpos : 0 < q.1 i ^ 2 + rest := by
    rw [hReq] at hR
    exact Real.sqrt_pos.mp hR
  have hRne : zoomLiftRadius q.1 ≠ 0 := ne_of_gt hR
  have hji : j ≠ i := Ne.symm hij
  have hfun : (fun s : ℝ => zoomDrift lam h zc u (Function.update q.1 i s, q.2) j)
      = fun s : ℝ => zoomV lam h zc u ((Real.sqrt (s ^ 2 + rest), q.1 4), q.2)
          * (q.1 j / Real.sqrt (s ^ 2 + rest)) := by
    funext s
    rw [zoomDrift]
    split_ifs with hcase
    · exact absurd hcase hj
    · simp only [zoomLiftPoint, hrest s, Function.update_of_ne hji,
        Function.update_of_ne (Ne.symm hi)]
  have hV : HasDerivAt (fun r : ℝ => zoomV lam h zc u ((r, q.1 4), q.2))
      (dr (zoomV lam h zc u) (zoomLiftPoint q)) (Real.sqrt (q.1 i ^ 2 + rest)) := by
    rw [← hReq]
    exact hasDerivAt_zoomV_radial lam h zc u hu (zoomLiftPoint q) hp
  have hA := hV.comp (q.1 i) (hasDerivAt_sqrt_sq_add hpos)
  have hRsqrt_ne : Real.sqrt (q.1 i ^ 2 + rest) ≠ 0 := by rw [← hReq]; exact hRne
  have hjq : HasDerivAt (fun s : ℝ => q.1 j / Real.sqrt (s ^ 2 + rest))
      ((0 * Real.sqrt (q.1 i ^ 2 + rest) - q.1 j * (q.1 i / Real.sqrt (q.1 i ^ 2 + rest)))
        / Real.sqrt (q.1 i ^ 2 + rest) ^ 2) (q.1 i) :=
    (hasDerivAt_const (q.1 i) (q.1 j)).div (hasDerivAt_sqrt_sq_add hpos) hRsqrt_ne
  have hmul : HasDerivAt
      (fun s : ℝ => zoomV lam h zc u ((Real.sqrt (s ^ 2 + rest), q.1 4), q.2)
        * (q.1 j / Real.sqrt (s ^ 2 + rest)))
      (dr (zoomV lam h zc u) (zoomLiftPoint q) * (q.1 i / Real.sqrt (q.1 i ^ 2 + rest))
          * (q.1 j / Real.sqrt (q.1 i ^ 2 + rest))
        + zoomV lam h zc u ((Real.sqrt (q.1 i ^ 2 + rest), q.1 4), q.2)
            * ((0 * Real.sqrt (q.1 i ^ 2 + rest) - q.1 j * (q.1 i / Real.sqrt (q.1 i ^ 2 + rest)))
                / Real.sqrt (q.1 i ^ 2 + rest) ^ 2)) (q.1 i) := hA.mul hjq
  rw [hfun, hmul.deriv, ← hReq]
  simp only [zoomLiftPoint]
  field_simp
  ring

/-! ### Bounds on the entries of `∇B_n` -/

/-- The vertical entry of the vertical row of `∇B_n` is bounded by the `∂_Z W_n` drift bound
of `eq:aniso:zoom:derivatives`. -/
theorem abs_deriv_zoomDrift_vertical_le {C h lam zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    {q : Vec 5 × ℝ} (hp : zoomPoint lam h zc (zoomLiftPoint q) ∈ unitCylinder)
    (hC : 0 ≤ C) (hτ : q.2 ≤ -1) :
    |deriv (fun s : ℝ => zoomDrift lam h zc u (Function.update q.1 4 s, q.2) 4) (q.1 4)|
      ≤ C * (-q.2) ^ (-(1 / 2 : ℝ)) := by
  rw [deriv_zoomDrift_vertical lam h zc u (hu.of_le (by norm_num)) hp]
  exact abs_dz_zoomW_le_rpow_neg_half hlam hb hu hp hC hτ

/-- The vertical entry of a radial row of `∇B_n` is bounded by the `∂_Z V_n` drift bound
times a direction cosine of absolute value at most one. -/
theorem abs_deriv_zoomDrift_coord_dz_le {C h lam zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    {q : Vec 5 × ℝ} (hp : zoomPoint lam h zc (zoomLiftPoint q) ∈ unitCylinder)
    (hC : 0 ≤ C) (hh1 : h ≤ 1 / 2) (hτ : q.2 ≤ -1) {j : Fin 5} (hj : j ≠ 4) :
    |deriv (fun s : ℝ => zoomDrift lam h zc u (Function.update q.1 4 s, q.2) j) (q.1 4)|
      ≤ C * (-q.2) ^ (-(1 / 2 : ℝ)) := by
  rw [deriv_zoomDrift_coord_dz lam h zc u (hu.of_le (by norm_num)) hp hj, abs_mul]
  have hdz := abs_dz_zoomV_le_rpow_neg_half hlam hb hu hp hC hh1 hτ
  have hdir := abs_div_zoomLiftRadius_le_one q.1 hj
  calc |dz (zoomV lam h zc u) (zoomLiftPoint q)| * |q.1 j / zoomLiftRadius q.1|
      ≤ C * (-q.2) ^ (-(1 / 2 : ℝ)) * 1 :=
        mul_le_mul hdz hdir (abs_nonneg _)
          (mul_nonneg hC (Real.rpow_nonneg (by linarith only [hτ]) _))
    _ = C * (-q.2) ^ (-(1 / 2 : ℝ)) := by ring

/-- The radial entry of the vertical row of `∇B_n` is bounded by the `∂_R W_n` drift bound
times a direction cosine of absolute value at most one. -/
theorem abs_deriv_zoomDrift_vertical_dr_le {C h lam zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    {q : Vec 5 × ℝ} (hp : zoomPoint lam h zc (zoomLiftPoint q) ∈ unitCylinder)
    (hR : 0 < zoomLiftRadius q.1) (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hτ : q.2 ≤ -1) {i : Fin 5}
    (hi : i ≠ 4) :
    |deriv (fun s : ℝ => zoomDrift lam h zc u (Function.update q.1 i s, q.2) 4) (q.1 i)|
      ≤ C * (-q.2) ^ (-(1 / 2 : ℝ)) := by
  rw [deriv_zoomDrift_vertical_dr lam h zc u (hu.of_le (by norm_num)) hp hR hi, abs_mul]
  have hdr := abs_dr_zoomW_le_rpow_neg_half hlam hb hu hp hC hh0 hτ
  have hdir := abs_div_zoomLiftRadius_le_one q.1 hi
  calc |dr (zoomW lam h zc u) (zoomLiftPoint q)| * |q.1 i / zoomLiftRadius q.1|
      ≤ C * (-q.2) ^ (-(1 / 2 : ℝ)) * 1 :=
        mul_le_mul hdr hdir (abs_nonneg _)
          (mul_nonneg hC (Real.rpow_nonneg (by linarith only [hτ]) _))
    _ = C * (-q.2) ^ (-(1 / 2 : ℝ)) := by ring

/-- `|X + Y| ≤ 2 C V` from two individual bounds `|X|, |Y| ≤ C V`. -/
private theorem abs_add_le_two_mul (X Y C V : ℝ) (hX : |X| ≤ C * V) (hY : |Y| ≤ C * V) :
    |X + Y| ≤ 2 * C * V := by
  calc |X + Y| ≤ |X| + |Y| := abs_add_le X Y
    _ ≤ C * V + C * V := by linarith only [hX, hY]
    _ = 2 * C * V := by ring

/-- `|X - Y| ≤ 2 C V` from two individual bounds `|X|, |Y| ≤ C V`. -/
private theorem abs_sub_le_two_mul (X Y C V : ℝ) (hX : |X| ≤ C * V) (hY : |Y| ≤ C * V) :
    |X - Y| ≤ 2 * C * V := by
  have h1 : |X - Y| ≤ |X| + |Y| := by
    have h2 := abs_add_le X (-Y)
    simpa [sub_eq_add_neg] using h2
  calc |X - Y| ≤ |X| + |Y| := h1
    _ ≤ C * V + C * V := by linarith only [hX, hY]
    _ = 2 * C * V := by ring

/-- The product of two of the four radial coordinates, divided by the squared lifted radius,
is bounded by one in absolute value away from the axis, since each direction cosine is. -/
private theorem abs_mul_div_zoomLiftRadius_sq_le_one (X : Vec 5) {i j : Fin 5}
    (hi : i ≠ 4) (hj : j ≠ 4) :
    |X i * X j / zoomLiftRadius X ^ 2| ≤ 1 := by
  have hi' := abs_div_zoomLiftRadius_le_one X hi
  have hj' := abs_div_zoomLiftRadius_le_one X hj
  have heq : (X i / zoomLiftRadius X) * (X j / zoomLiftRadius X)
      = X i * X j / zoomLiftRadius X ^ 2 := by
    rw [div_mul_div_comm, sq]
  rw [← heq, abs_mul]
  calc |X i / zoomLiftRadius X| * |X j / zoomLiftRadius X| ≤ 1 * 1 :=
        mul_le_mul hi' hj' (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- The diagonal entry of a radial row of `∇B_n` is bounded by twice the `V_n`/`∂_R V_n`
drift bounds of `eq:aniso:zoom:derivatives`, using that `V_n` vanishes on the axis. -/
theorem abs_deriv_zoomDrift_coord_le {C h lam zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {q : Vec 5 × ℝ}
    (hp : zoomPoint lam h zc (zoomLiftPoint q) ∈ unitCylinder) (hR : 0 < zoomLiftRadius q.1)
    (hC : 0 ≤ C) (hτ : q.2 ≤ -1) {i : Fin 5} (hi : i ≠ 4) :
    |deriv (fun s : ℝ => zoomDrift lam h zc u (Function.update q.1 i s, q.2) i) (q.1 i)|
      ≤ 2 * C * (-q.2) ^ (-(1 / 2 : ℝ)) := by
  rw [deriv_zoomDrift_coord lam h zc u (hu.of_le (by norm_num)) hp hR hi]
  apply abs_add_le_two_mul _ _ C ((-q.2) ^ (-(1 / 2 : ℝ)))
  · rw [abs_mul]
    have hdr := abs_dr_zoomV_le_rpow_neg_half hlam hb hu hp hC hτ
    have hsq : |q.1 i ^ 2 / zoomLiftRadius q.1 ^ 2| ≤ 1 := by
      have hle := abs_le_zoomLiftRadius q.1 hi
      have hsqle : q.1 i ^ 2 ≤ zoomLiftRadius q.1 ^ 2 := by
        calc q.1 i ^ 2 = |q.1 i| ^ 2 := (sq_abs (q.1 i)).symm
          _ ≤ zoomLiftRadius q.1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hle 2
      rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]
      exact hsqle
    calc |dr (zoomV lam h zc u) (zoomLiftPoint q)| * |q.1 i ^ 2 / zoomLiftRadius q.1 ^ 2|
        ≤ C * (-q.2) ^ (-(1 / 2 : ℝ)) * 1 :=
          mul_le_mul hdr hsq (abs_nonneg _)
            (mul_nonneg hC (Real.rpow_nonneg (by linarith only [hτ]) _))
      _ = C * (-q.2) ^ (-(1 / 2 : ℝ)) := by ring
  · have hVdiv := abs_zoomV_div_le hlam hb hu haxi hp hR.ne' hC hτ
    have hle := abs_le_zoomLiftRadius q.1 hi
    have hsqle : q.1 i ^ 2 ≤ zoomLiftRadius q.1 ^ 2 := by
      calc q.1 i ^ 2 = |q.1 i| ^ 2 := (sq_abs (q.1 i)).symm
        _ ≤ zoomLiftRadius q.1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hle 2
    have hquot_nonneg : (0 : ℝ) ≤
        (zoomLiftRadius q.1 ^ 2 - q.1 i ^ 2) / zoomLiftRadius q.1 ^ 3 :=
      div_nonneg (by linarith only [hsqle]) (by positivity)
    have hquot_le : (zoomLiftRadius q.1 ^ 2 - q.1 i ^ 2) / zoomLiftRadius q.1 ^ 3
        ≤ 1 / zoomLiftRadius q.1 := by
      have heq : 1 / zoomLiftRadius q.1
          - (zoomLiftRadius q.1 ^ 2 - q.1 i ^ 2) / zoomLiftRadius q.1 ^ 3
          = q.1 i ^ 2 / zoomLiftRadius q.1 ^ 3 := by
        field_simp
        ring
      have hnn : (0 : ℝ) ≤ q.1 i ^ 2 / zoomLiftRadius q.1 ^ 3 := by positivity
      linarith only [heq, hnn]
    rw [abs_mul, abs_of_nonneg hquot_nonneg]
    calc |zoomV lam h zc u (zoomLiftPoint q)|
          * ((zoomLiftRadius q.1 ^ 2 - q.1 i ^ 2) / zoomLiftRadius q.1 ^ 3)
        ≤ |zoomV lam h zc u (zoomLiftPoint q)| * (1 / zoomLiftRadius q.1) :=
          mul_le_mul_of_nonneg_left hquot_le (abs_nonneg _)
      _ = |zoomV lam h zc u (zoomLiftPoint q) / zoomLiftRadius q.1| := by
          rw [abs_div, abs_of_pos hR]; ring
      _ ≤ C * (-q.2) ^ (-(1 / 2 : ℝ)) := hVdiv

/-- The off-diagonal entry of a radial row of `∇B_n` is bounded by twice the `V_n`/`∂_R V_n`
drift bounds, exactly as the diagonal entry: `X_i X_j/R²` and `X_i X_j/R³` are each bounded
by one direction cosine times another, and the second is absorbed into `V_n/R`. -/
theorem abs_deriv_zoomDrift_offdiag_le {C h lam zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {q : Vec 5 × ℝ}
    (hp : zoomPoint lam h zc (zoomLiftPoint q) ∈ unitCylinder) (hR : 0 < zoomLiftRadius q.1)
    (hC : 0 ≤ C) (hτ : q.2 ≤ -1) {i j : Fin 5} (hi : i ≠ 4) (hj : j ≠ 4) (hij : i ≠ j) :
    |deriv (fun s : ℝ => zoomDrift lam h zc u (Function.update q.1 i s, q.2) j) (q.1 i)|
      ≤ 2 * C * (-q.2) ^ (-(1 / 2 : ℝ)) := by
  rw [deriv_zoomDrift_offdiag lam h zc u (hu.of_le (by norm_num)) hp hR hi hj hij]
  apply abs_sub_le_two_mul _ _ C ((-q.2) ^ (-(1 / 2 : ℝ)))
  · rw [abs_mul]
    have hdr := abs_dr_zoomV_le_rpow_neg_half hlam hb hu hp hC hτ
    have hsq := abs_mul_div_zoomLiftRadius_sq_le_one q.1 hi hj
    calc |dr (zoomV lam h zc u) (zoomLiftPoint q)| * |q.1 i * q.1 j / zoomLiftRadius q.1 ^ 2|
        ≤ C * (-q.2) ^ (-(1 / 2 : ℝ)) * 1 :=
          mul_le_mul hdr hsq (abs_nonneg _)
            (mul_nonneg hC (Real.rpow_nonneg (by linarith only [hτ]) _))
      _ = C * (-q.2) ^ (-(1 / 2 : ℝ)) := by ring
  · have hVdiv := abs_zoomV_div_le hlam hb hu haxi hp hR.ne' hC hτ
    have hsq := abs_mul_div_zoomLiftRadius_sq_le_one q.1 hi hj
    have hcube_eq : q.1 i * q.1 j / zoomLiftRadius q.1 ^ 3
        = (q.1 i * q.1 j / zoomLiftRadius q.1 ^ 2) * (1 / zoomLiftRadius q.1) := by
      field_simp
    rw [abs_mul, hcube_eq, abs_mul]
    have h3 : |(1 : ℝ) / zoomLiftRadius q.1| = 1 / zoomLiftRadius q.1 := by
      rw [abs_of_pos (by positivity)]
    rw [h3]
    calc |zoomV lam h zc u (zoomLiftPoint q)|
          * (|q.1 i * q.1 j / zoomLiftRadius q.1 ^ 2| * (1 / zoomLiftRadius q.1))
        ≤ |zoomV lam h zc u (zoomLiftPoint q)| * (1 * (1 / zoomLiftRadius q.1)) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = |zoomV lam h zc u (zoomLiftPoint q) / zoomLiftRadius q.1| := by
          rw [abs_div, abs_of_pos hR]; ring
      _ ≤ C * (-q.2) ^ (-(1 / 2 : ℝ)) := hVdiv

/-- The uniform bound `|∇B_n| ≤ 2 C |τ|^{-1/2}` on every entry of the Jacobian of the lifted
drift `eq:drift:Bn:def` away from the axis, for `τ ≤ -1`: differentiating any one of the five
lifted components `B_n` in any one of the five lifted directions gives a value bounded by
`2 C (-τ)^{-1/2}`, from the drift bounds of `eq:aniso:zoom:derivatives` together with the
direction cosines `|X_i/R| ≤ 1`. Combined with `norm_zoomDrift_le`, this is the footnote's
`|B_n| + |∇B_n| ≤ C|τ|^{-1/2}`. -/
theorem abs_deriv_zoomDrift_le {C h lam zc : ℝ} (hlam : 0 < lam) {u : ParabolicPoint → Vec3}
    (hb : AnisotropicBounds C h u) (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {q : Vec 5 × ℝ}
    (hp : zoomPoint lam h zc (zoomLiftPoint q) ∈ unitCylinder) (hR : 0 < zoomLiftRadius q.1)
    (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2) (hτ : q.2 ≤ -1) {i j : Fin 5} :
    |deriv (fun s : ℝ => zoomDrift lam h zc u (Function.update q.1 i s, q.2) j) (q.1 i)|
      ≤ 2 * C * (-q.2) ^ (-(1 / 2 : ℝ)) := by
  have hnn : (0 : ℝ) ≤ C * (-q.2) ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hC (Real.rpow_nonneg (by linarith only [hτ]) _)
  rcases eq_or_ne i 4 with hi4 | hi4
  · rcases eq_or_ne j 4 with hj4 | hj4
    · subst hi4; subst hj4
      have := abs_deriv_zoomDrift_vertical_le hlam hb hu hp hC hτ
      linarith only [this, hnn]
    · subst hi4
      have := abs_deriv_zoomDrift_coord_dz_le hlam hb hu hp hC hh1 hτ hj4
      linarith only [this, hnn]
  · rcases eq_or_ne j 4 with hj4 | hj4
    · subst hj4
      have := abs_deriv_zoomDrift_vertical_dr_le hlam hb hu hp hR hC hh0 hτ hi4
      linarith only [this, hnn]
    · rcases eq_or_ne i j with hij | hij
      · subst hij
        exact abs_deriv_zoomDrift_coord_le hlam hb hu haxi hp hR hC hτ hi4
      · exact abs_deriv_zoomDrift_offdiag_le hlam hb hu haxi hp hR hC hτ hi4 hj4 hij

/-- The Jacobian `∇B_n` of the lifted drift `eq:drift:Bn:def` in the five lifted spatial
coordinates: entry `(i, j)` is the `j`-th component of `B_n` differentiated in the `i`-th
direction. -/
@[expose] def zoomDriftJacobian (lam h zc : ℝ) (u : ParabolicPoint → Vec3) (q : Vec 5 × ℝ) :
    Fin 5 → Fin 5 → ℝ :=
  fun i j => deriv (fun s : ℝ => zoomDrift lam h zc u (Function.update q.1 i s, q.2) j) (q.1 i)

/-- The footnote's `|∇B_n| ≤ C |τ|^{-1/2}` for `τ ≤ -1`, away from the axis, as a genuine
norm bound on `zoomDriftJacobian`: combined with `norm_zoomDrift_le`, this is the pair of
bounds `|B_n| + |∇B_n| ≤ C|τ|^{-1/2}` (up to the harmless factor of two carried by every
entry of `∇B_n`) recorded before `eq:drift:Bn:def`. -/
theorem norm_zoomDriftJacobian_le {C h lam zc : ℝ} (hlam : 0 < lam) {u : ParabolicPoint → Vec3}
    (hb : AnisotropicBounds C h u) (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {q : Vec 5 × ℝ}
    (hp : zoomPoint lam h zc (zoomLiftPoint q) ∈ unitCylinder) (hR : 0 < zoomLiftRadius q.1)
    (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2) (hτ : q.2 ≤ -1) :
    ‖zoomDriftJacobian lam h zc u q‖ ≤ 2 * C * (-q.2) ^ (-(1 / 2 : ℝ)) := by
  have hbound : (0 : ℝ) ≤ 2 * C * (-q.2) ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (mul_nonneg (by norm_num) hC) (Real.rpow_nonneg (by linarith only [hτ]) _)
  rw [pi_norm_le_iff_of_nonneg hbound]
  intro i
  rw [pi_norm_le_iff_of_nonneg hbound]
  intro j
  rw [Real.norm_eq_abs, zoomDriftJacobian]
  exact abs_deriv_zoomDrift_le hlam hb hu haxi hp hR hC hh0 hh1 hτ

/-- The pointwise divergence of the lifted drift in the five lifted spatial coordinates. -/
@[expose] def zoomDriftDivergence (lam h zc : ℝ) (u : ParabolicPoint → Vec3) (q : Vec 5 × ℝ) : ℝ :=
  ∑ i : Fin 5, deriv (fun s : ℝ => zoomDrift lam h zc u (Function.update q.1 i s, q.2) i) (q.1 i)

/-- `div_{X,Z} B_n = 2 V_n/R` away from the axis. The four radial entries sum to the trace
`∂_R V_n + 3 V_n/R` of `∇_X(V_n X/R)`, because `Σ X_i² = R²`; adding `∂_Z W_n` and using the
divergence identity `∂_R V_n + V_n/R + ∂_Z W_n = 0` of `eq:aniso:zoom:finite:identities`
leaves `2 V_n/R`. -/
theorem zoomDriftDivergence_eq (lam h zc : ℝ) (hlam : 0 < lam)
    (u : ParabolicPoint → Vec3) (pr : ParabolicPoint → ℝ) (fo : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u pr fo unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {q : Vec 5 × ℝ}
    (hp : zoomPoint lam h zc (zoomLiftPoint q) ∈ unitCylinder)
    (hR : 0 < zoomLiftRadius q.1) :
    zoomDriftDivergence lam h zc u q
      = 2 * (zoomV lam h zc u (zoomLiftPoint q) / zoomLiftRadius q.1) := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hsol.1.of_le (by exact_mod_cast le_top)
  have hRne : zoomLiftRadius q.1 ≠ 0 := ne_of_gt hR
  have hsq : zoomLiftRadius q.1 ^ 2 = q.1 0 ^ 2 + q.1 1 ^ 2 + q.1 2 ^ 2 + q.1 3 ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hdiv := zoom_divergence_identity lam h zc hlam u pr fo hsol haxi
    (zoomLiftPoint q) hp hRne
  simp only [zoomLiftPoint] at hdiv
  rw [zoomDriftDivergence, Fin.sum_univ_five,
    deriv_zoomDrift_coord lam h zc u hu1 hp hR (i := 0) (by decide),
    deriv_zoomDrift_coord lam h zc u hu1 hp hR (i := 1) (by decide),
    deriv_zoomDrift_coord lam h zc u hu1 hp hR (i := 2) (by decide),
    deriv_zoomDrift_coord lam h zc u hu1 hp hR (i := 3) (by decide),
    deriv_zoomDrift_vertical lam h zc u hu1 hp]
  simp only [zoomLiftPoint]
  have hfour : dr (zoomV lam h zc u) ((zoomLiftRadius q.1, q.1 4), q.2)
        * (q.1 0 ^ 2 / zoomLiftRadius q.1 ^ 2)
      + zoomV lam h zc u ((zoomLiftRadius q.1, q.1 4), q.2)
        * ((zoomLiftRadius q.1 ^ 2 - q.1 0 ^ 2) / zoomLiftRadius q.1 ^ 3)
      + (dr (zoomV lam h zc u) ((zoomLiftRadius q.1, q.1 4), q.2)
        * (q.1 1 ^ 2 / zoomLiftRadius q.1 ^ 2)
      + zoomV lam h zc u ((zoomLiftRadius q.1, q.1 4), q.2)
        * ((zoomLiftRadius q.1 ^ 2 - q.1 1 ^ 2) / zoomLiftRadius q.1 ^ 3))
      + (dr (zoomV lam h zc u) ((zoomLiftRadius q.1, q.1 4), q.2)
        * (q.1 2 ^ 2 / zoomLiftRadius q.1 ^ 2)
      + zoomV lam h zc u ((zoomLiftRadius q.1, q.1 4), q.2)
        * ((zoomLiftRadius q.1 ^ 2 - q.1 2 ^ 2) / zoomLiftRadius q.1 ^ 3))
      + (dr (zoomV lam h zc u) ((zoomLiftRadius q.1, q.1 4), q.2)
        * (q.1 3 ^ 2 / zoomLiftRadius q.1 ^ 2)
      + zoomV lam h zc u ((zoomLiftRadius q.1, q.1 4), q.2)
        * ((zoomLiftRadius q.1 ^ 2 - q.1 3 ^ 2) / zoomLiftRadius q.1 ^ 3))
      = dr (zoomV lam h zc u) ((zoomLiftRadius q.1, q.1 4), q.2)
        + 3 * (zoomV lam h zc u ((zoomLiftRadius q.1, q.1 4), q.2) / zoomLiftRadius q.1) := by
    field_simp
    linear_combination (zoomV lam h zc u ((zoomLiftRadius q.1, q.1 4), q.2)
      - dr (zoomV lam h zc u) ((zoomLiftRadius q.1, q.1 4), q.2)
        * zoomLiftRadius q.1) * hsq
  rw [hfour]
  linarith only [hdiv]

end CIV
