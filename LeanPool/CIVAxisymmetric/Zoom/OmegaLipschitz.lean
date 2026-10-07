/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.FiniteAxisBounds
public import LeanPool.CIVAxisymmetric.Zoom.ScalarChainRule
public import LeanPool.CIVAxisymmetric.Identities.VorticityEquation

/-!
# First-derivative and Lipschitz bounds for the rescaled potential vorticity

Step 2 of the finite-`h` zoom-in argument, away from the axis. On a rectangle contained in
`{R ≥ ε}` the rescaled potential vorticity `Ω_n` of `eq:aniso:zoom:fields` has first spatial
derivatives bounded *uniformly in the zoom scale*.

Off the axis `Ω_n = (δ² ∂_Z V_n − ∂_R W_n)/R` (`eq:aniso:zoom:finite:identities`), so the
quotient rule
expresses `∂_R Ω_n` and `∂_Z Ω_n` through the first and second derivatives of `V_n` and `W_n`,
each of which obeys one of the twelve rescaled bounds of `eq:aniso:zoom:derivatives`. Every
exponent appearing there is at most `-1/2` when `0 ≤ h ≤ 1/2`, so for `τ ≤ -1` all six inputs
are bounded by `C (-τ)^{-1/2}`, and `R ≥ ε` turns the two denominators into the constants
`ε^{-1}` and `ε^{-2}`:

    |∂_R Ω_n| ≤ 2C(ε⁻¹ + ε⁻²)(-τ)^{-1/2},   |∂_Z Ω_n| ≤ 2Cε⁻¹(-τ)^{-1/2}.

The vertical derivative needs the mixed second derivative `∂_Z ∂_R W_n`, which the second-order
chain rules produce in the opposite order `∂_R ∂_Z W_n`; the two agree by the symmetry of the
Cartesian mixed spatial partials of the velocity, which is why the smoothness hypothesis here is
`C^∞` rather than `C²` (a classical solution supplies exactly this).

Integrating these two bounds along the two coordinate edges of a rectangle gives the
Lipschitz-in-space bound with the `τ`-independent constant `2C(2ε⁻¹ + ε⁻²)`, which is the input
of the equicontinuity argument.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### Elementary inequalities -/

/-- Shrinking a positive denominator increases a nonnegative quotient. -/
private theorem div_le_div_of_denom_ge {A B D : ℝ} (hA : 0 ≤ A) (hD : 0 < D) (hDB : D ≤ B) :
    A / B ≤ A / D := by
  have hB : 0 < B := lt_of_lt_of_le hD hDB
  rw [div_le_div_iff₀ hB hD]
  exact mul_le_mul_of_nonneg_left hDB hA

/-- For `τ ≤ -1` a nonpositive shift of the exponent below `-1/2` only decreases the power. -/
private theorem const_mul_rpow_le_neg_half {C t e : ℝ} (hC : 0 ≤ C) (ht : t ≤ -1)
    (he : e ≤ -(1 / 2 : ℝ)) : C * (-t) ^ e ≤ C * (-t) ^ (-(1 / 2 : ℝ)) :=
  mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith only [ht]) he) hC

/-- `|δ² A - B| ≤ 2D` from `|A| ≤ D`, `|B| ≤ D` and `0 ≤ δ ≤ 1`. -/
private theorem abs_sq_smul_sub_le {A B D delta : ℝ} (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1)
    (hA : |A| ≤ D) (hB : |B| ≤ D) : |delta ^ 2 * A - B| ≤ 2 * D := by
  have h1 : |delta ^ 2 * A - B| ≤ |delta ^ 2 * A| + |B| := by
    rw [sub_eq_add_neg]
    calc |delta ^ 2 * A + -B| ≤ |delta ^ 2 * A| + |(-B)| := abs_add_le _ _
      _ = |delta ^ 2 * A| + |B| := by rw [abs_neg]
  have h2 : |delta ^ 2 * A| = delta ^ 2 * |A| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ delta ^ 2)]
  have h3 : delta ^ 2 ≤ 1 := by nlinarith only [hd0, hd1]
  have h4 : delta ^ 2 * |A| ≤ 1 * |A| := mul_le_mul_of_nonneg_right h3 (abs_nonneg A)
  linarith only [h1, h2, h4, hA, hB]

/-- The quotient-rule estimate for the radial derivative on `{R ≥ ε}`. -/
private theorem abs_quot_deriv_le {Nr N R eps M : ℝ} (heps : 0 < eps) (hR : eps ≤ R)
    (hM : 0 ≤ M) (hNr : |Nr| ≤ 2 * M) (hN : |N| ≤ 2 * M) :
    |(Nr * R - N) / R ^ 2| ≤ 2 * M * (1 / eps + 1 / eps ^ 2) := by
  have hRpos : 0 < R := lt_of_lt_of_le heps hR
  have hRne : R ≠ 0 := ne_of_gt hRpos
  have hR2 : 0 < R ^ 2 := by positivity
  have hnum : |Nr * R - N| ≤ 2 * M * R + 2 * M := by
    have h1 : |Nr * R - N| ≤ |Nr * R| + |N| := by
      rw [sub_eq_add_neg]
      calc |Nr * R + -N| ≤ |Nr * R| + |(-N)| := abs_add_le _ _
        _ = |Nr * R| + |N| := by rw [abs_neg]
    have h2 : |Nr * R| = |Nr| * R := by rw [abs_mul, abs_of_pos hRpos]
    have h3 : |Nr| * R ≤ 2 * M * R := mul_le_mul_of_nonneg_right hNr hRpos.le
    linarith only [h1, h2, h3, hN]
  have heps2 : eps ^ 2 ≤ R ^ 2 := by nlinarith only [heps, hR]
  have h2M : (0 : ℝ) ≤ 2 * M := by linarith only [hM]
  rw [abs_div, abs_of_pos hR2]
  calc |Nr * R - N| / R ^ 2 ≤ (2 * M * R + 2 * M) / R ^ 2 := by gcongr
    _ = 2 * M / R + 2 * M / R ^ 2 := by field_simp
    _ ≤ 2 * M / eps + 2 * M / eps ^ 2 :=
        add_le_add (div_le_div_of_denom_ge h2M heps hR)
          (div_le_div_of_denom_ge h2M (by positivity) heps2)
    _ = 2 * M * (1 / eps + 1 / eps ^ 2) := by ring

/-- The quotient-rule estimate for the vertical derivative on `{R ≥ ε}`. -/
private theorem abs_quot_deriv_le' {Nz R eps M : ℝ} (heps : 0 < eps) (hR : eps ≤ R)
    (hM : 0 ≤ M) (hNz : |Nz| ≤ 2 * M) : |Nz / R| ≤ 2 * M * (1 / eps) := by
  have hRpos : 0 < R := lt_of_lt_of_le heps hR
  have h2M : (0 : ℝ) ≤ 2 * M := by linarith only [hM]
  rw [abs_div, abs_of_pos hRpos]
  calc |Nz| / R ≤ 2 * M / R := by gcongr
    _ ≤ 2 * M / eps := div_le_div_of_denom_ge h2M heps hR
    _ = 2 * M * (1 / eps) := by ring

/-! ### The two pieces of the numerator, differentiated along a coordinate slice -/

/-- `∂_Z V_n` differentiated in the radial variable along the slice through `p`. -/
private theorem hasDerivAt_dz_zoomV_radial (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    HasDerivAt (fun r : ℝ => dz (zoomV lam h zc u) ((r, p.1.2), p.2))
      (dr (dz (zoomV lam h zc u)) p) p.1.1 := by
  rw [drdz_zoomV lam h zc u hu p hp]
  refine HasDerivAt.congr_of_eventuallyEq ?_ (eventually_dz_on_slice_r lam h zc u hu p hp)
  have h_mul := (hasDerivAt_spatialPartial_two_zoom_r lam h zc u 0 hu p hp).const_mul
    (lam * lam ^ (1 - 2 * h))
  simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul

/-- `∂_R W_n` differentiated in the radial variable along the slice through `p`. -/
private theorem hasDerivAt_dr_zoomW_radial (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    HasDerivAt (fun r : ℝ => dr (zoomW lam h zc u) ((r, p.1.2), p.2))
      (dr (dr (zoomW lam h zc u)) p) p.1.1 := by
  have hev : (fun r : ℝ => dr (zoomW lam h zc u) ((r, p.1.2), p.2))
      =ᶠ[𝓝 p.1.1]
    fun r : ℝ => lam ^ 2 * lam ^ (2 * h) *
      spatialPartial (fun w => u w 2) 0 (zoomPoint lam h zc ((r, p.1.2), p.2)) := by
    have hpS : p.1.1 ∈ {r : ℝ | zoomPoint lam h zc ((r, p.1.2), p.2) ∈ unitCylinder} := hp
    filter_upwards [(isOpen_slice_r lam h zc p).mem_nhds hpS] with r hr
    exact dr_zoomW lam h zc u (hu.of_le (by norm_num)) ((r, p.1.2), p.2) hr
  rw [drdr_zoomW lam h zc u hu p hp]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have h_mul := (hasDerivAt_spatialPartial_zero_zoom_r lam h zc u 2 hu p hp).const_mul
    (lam ^ 2 * lam ^ (2 * h))
  simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul

/-- `∂_Z V_n` differentiated in the vertical variable along the slice through `p`. -/
private theorem hasDerivAt_dz_zoomV_vertical (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    HasDerivAt (fun s : ℝ => dz (zoomV lam h zc u) ((p.1.1, s), p.2))
      (dz (dz (zoomV lam h zc u)) p) p.1.2 := by
  rw [dzdz_zoomV lam h zc u hu p hp]
  refine HasDerivAt.congr_of_eventuallyEq ?_ (eventually_dz_on_slice_z lam h zc u hu p hp)
  have h_mul := (hasDerivAt_spatialPartial_two_zoom_z lam h zc u 0 hu p hp).const_mul
    (lam * lam ^ (1 - 2 * h))
  simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul

/-- `∂_R W_n` differentiated in the *vertical* variable along the slice through `p`. This is the
only place where the two orders of the mixed second derivative meet: the chain rule produces
`∂₃∂₁u₃` at the zoomed point, whereas `eq:aniso:zoom:derivatives` is stated for `∂₁∂₃u₃`, and the
two agree by the symmetry of the Cartesian mixed spatial partials. -/
private theorem hasDerivAt_dr_zoomW_vertical (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    HasDerivAt (fun s : ℝ => dr (zoomW lam h zc u) ((p.1.1, s), p.2))
      (dr (dz (zoomW lam h zc u)) p) p.1.2 := by
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by simp)
  have hpar : ContDiffOn ℝ 1
      (fun z : Vec3 × ℝ => spatialPartial (fun w => u w 2) 0 z) unitCylinder :=
    contDiffOn_spatialPartial_of_contDiffOn (contDiffOn_component hu2 2) 0
  have hev : (fun s : ℝ => dr (zoomW lam h zc u) ((p.1.1, s), p.2))
      =ᶠ[𝓝 p.1.2]
    fun s : ℝ => lam ^ 2 * lam ^ (2 * h) *
      spatialPartial (fun w => u w 2) 0 (zoomPoint lam h zc ((p.1.1, s), p.2)) := by
    have hpS : p.1.2 ∈ {s : ℝ | zoomPoint lam h zc ((p.1.1, s), p.2) ∈ unitCylinder} := hp
    filter_upwards [(isOpen_slice_z lam h zc p).mem_nhds hpS] with s hs
    exact dr_zoomW lam h zc u (hu2.of_le (by norm_num)) ((p.1.1, s), p.2) hs
  have hcomm : spatialPartial
      (fun w : ParabolicPoint => spatialPartial (fun v => u v 2) 0 w) 2 (zoomPoint lam h zc p)
      = meridionalPartial (fun w => u w 2) 1 1 (zoomPoint lam h zc p) :=
    spatialSecondPartial_comm (g := fun w : ParabolicPoint => u w 2)
      (contDiffOn_component hu 2) hp 0 2
  have hbase := (hasDerivAt_zoomScalar_z
      (Phi := fun w : ParabolicPoint => spatialPartial (fun v => u v 2) 0 w)
      lam h zc isOpen_unitCylinder_prod hpar p hp).const_mul (lam ^ 2 * lam ^ (2 * h))
  have hval : lam ^ 2 * lam ^ (2 * h) * (lam ^ (1 - 2 * h) *
      spatialPartial (fun w : ParabolicPoint => spatialPartial (fun v => u v 2) 0 w) 2
        (zoomPoint lam h zc p))
      = lam ^ 2 * lam ^ (2 * h) * lam ^ (1 - 2 * h) *
        meridionalPartial (fun w => u w 2) 1 1 (zoomPoint lam h zc p) := by
    rw [hcomm]; ring
  rw [hval] at hbase
  rw [drdz_zoomW lam h zc u hu2 p hp]
  exact hbase.congr_of_eventuallyEq hev

/-! ### The rescaled potential vorticity differentiated along a coordinate slice -/

/-- Off the axis, `Ω_n` restricted to a radial slice is differentiable, with the derivative the
quotient rule applied to `eq:aniso:zoom:finite:identities`. -/
theorem hasDerivAt_zoomOmega_radial (lam h zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) (hR : 0 < p.1.1) :
    HasDerivAt (fun r : ℝ => zoomOmega lam h zc u ((r, p.1.2), p.2))
      ((((lam ^ (2 * h)) ^ 2 * dr (dz (zoomV lam h zc u)) p
            - dr (dr (zoomW lam h zc u)) p) * p.1.1
          - ((lam ^ (2 * h)) ^ 2 * dz (zoomV lam h zc u) p - dr (zoomW lam h zc u) p))
        / p.1.1 ^ 2) p.1.1 := by
  have hev : (fun r : ℝ => zoomOmega lam h zc u ((r, p.1.2), p.2))
      =ᶠ[𝓝 p.1.1]
    fun r : ℝ => ((lam ^ (2 * h)) ^ 2 * dz (zoomV lam h zc u) ((r, p.1.2), p.2)
      - dr (zoomW lam h zc u) ((r, p.1.2), p.2)) / r := by
    have hpS : p.1.1 ∈ {r : ℝ | zoomPoint lam h zc ((r, p.1.2), p.2) ∈ unitCylinder} := hp
    filter_upwards [(isOpen_slice_r lam h zc p).mem_nhds hpS, Ioi_mem_nhds hR] with r hr hr0
    exact zoomOmega_eq lam h zc hlam u (hu.of_le (by norm_num)) ((r, p.1.2), p.2) hr
      (ne_of_gt hr0)
  have hnum : HasDerivAt
      (fun r : ℝ => (lam ^ (2 * h)) ^ 2 * dz (zoomV lam h zc u) ((r, p.1.2), p.2)
        - dr (zoomW lam h zc u) ((r, p.1.2), p.2))
      ((lam ^ (2 * h)) ^ 2 * dr (dz (zoomV lam h zc u)) p
        - dr (dr (zoomW lam h zc u)) p) p.1.1 :=
    ((hasDerivAt_dz_zoomV_radial lam h zc u hu p hp).const_mul ((lam ^ (2 * h)) ^ 2)).sub
      (hasDerivAt_dr_zoomW_radial lam h zc u hu p hp)
  have hden : HasDerivAt (fun r : ℝ => r) 1 p.1.1 := hasDerivAt_id' p.1.1
  have hq : HasDerivAt
      (fun r : ℝ => ((lam ^ (2 * h)) ^ 2 * dz (zoomV lam h zc u) ((r, p.1.2), p.2)
        - dr (zoomW lam h zc u) ((r, p.1.2), p.2)) / r)
      ((((lam ^ (2 * h)) ^ 2 * dr (dz (zoomV lam h zc u)) p - dr (dr (zoomW lam h zc u)) p)
          * p.1.1
        - ((lam ^ (2 * h)) ^ 2 * dz (zoomV lam h zc u) p - dr (zoomW lam h zc u) p) * 1)
        / p.1.1 ^ 2) p.1.1 :=
    hnum.div hden (ne_of_gt hR)
  have heqv : (((lam ^ (2 * h)) ^ 2 * dr (dz (zoomV lam h zc u)) p
          - dr (dr (zoomW lam h zc u)) p) * p.1.1
        - ((lam ^ (2 * h)) ^ 2 * dz (zoomV lam h zc u) p - dr (zoomW lam h zc u) p) * 1)
        / p.1.1 ^ 2
      = (((lam ^ (2 * h)) ^ 2 * dr (dz (zoomV lam h zc u)) p
          - dr (dr (zoomW lam h zc u)) p) * p.1.1
        - ((lam ^ (2 * h)) ^ 2 * dz (zoomV lam h zc u) p - dr (zoomW lam h zc u) p))
        / p.1.1 ^ 2 := by ring
  rw [heqv] at hq
  exact hq.congr_of_eventuallyEq hev

/-- Off the axis, `Ω_n` restricted to a vertical slice is differentiable. -/
theorem hasDerivAt_zoomOmega_vertical (lam h zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) (hR : 0 < p.1.1) :
    HasDerivAt (fun s : ℝ => zoomOmega lam h zc u ((p.1.1, s), p.2))
      (((lam ^ (2 * h)) ^ 2 * dz (dz (zoomV lam h zc u)) p
        - dr (dz (zoomW lam h zc u)) p) / p.1.1) p.1.2 := by
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by simp)
  have hev : (fun s : ℝ => zoomOmega lam h zc u ((p.1.1, s), p.2))
      =ᶠ[𝓝 p.1.2]
    fun s : ℝ => ((lam ^ (2 * h)) ^ 2 * dz (zoomV lam h zc u) ((p.1.1, s), p.2)
      - dr (zoomW lam h zc u) ((p.1.1, s), p.2)) / p.1.1 := by
    have hpS : p.1.2 ∈ {s : ℝ | zoomPoint lam h zc ((p.1.1, s), p.2) ∈ unitCylinder} := hp
    filter_upwards [(isOpen_slice_z lam h zc p).mem_nhds hpS] with s hs
    exact zoomOmega_eq lam h zc hlam u (hu2.of_le (by norm_num)) ((p.1.1, s), p.2) hs
      (ne_of_gt hR)
  have hnum : HasDerivAt
      (fun s : ℝ => (lam ^ (2 * h)) ^ 2 * dz (zoomV lam h zc u) ((p.1.1, s), p.2)
        - dr (zoomW lam h zc u) ((p.1.1, s), p.2))
      ((lam ^ (2 * h)) ^ 2 * dz (dz (zoomV lam h zc u)) p
        - dr (dz (zoomW lam h zc u)) p) p.1.2 :=
    ((hasDerivAt_dz_zoomV_vertical lam h zc u hu2 p hp).const_mul ((lam ^ (2 * h)) ^ 2)).sub
      (hasDerivAt_dr_zoomW_vertical lam h zc u hu p hp)
  exact (hnum.div_const p.1.1).congr_of_eventuallyEq hev

/-- The quotient rule for `∂_R Ω_n` off the axis. -/
theorem dr_zoomOmega_eq (lam h zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) (hR : 0 < p.1.1) :
    dr (zoomOmega lam h zc u) p
      = (((lam ^ (2 * h)) ^ 2 * dr (dz (zoomV lam h zc u)) p
            - dr (dr (zoomW lam h zc u)) p) * p.1.1
          - ((lam ^ (2 * h)) ^ 2 * dz (zoomV lam h zc u) p - dr (zoomW lam h zc u) p))
        / p.1.1 ^ 2 := by
  rw [dr]
  exact (hasDerivAt_zoomOmega_radial lam h zc hlam u hu p hp hR).deriv

/-- The quotient rule for `∂_Z Ω_n` off the axis. -/
theorem dz_zoomOmega_eq (lam h zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) (hR : 0 < p.1.1) :
    dz (zoomOmega lam h zc u) p
      = ((lam ^ (2 * h)) ^ 2 * dz (dz (zoomV lam h zc u)) p
        - dr (dz (zoomW lam h zc u)) p) / p.1.1 := by
  rw [dz]
  exact (hasDerivAt_zoomOmega_vertical lam h zc hlam u hu p hp hR).deriv

/-! ### The uniform first-derivative bounds -/

/-- The radial derivative of `Ω_n` on `{R ≥ ε}`, uniformly in the zoom scale, with the
exponent `-1/2` of `eq:aniso:zoom:derivatives`. -/
theorem abs_dr_zoomOmega_le {C h lam zc eps : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2) (hdelta : lam ^ (2 * h) ≤ 1)
    (heps : 0 < eps) {p : (ℝ × ℝ) × ℝ} (hR : eps ≤ p.1.1)
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (htau : p.2 ≤ -1) :
    |dr (zoomOmega lam h zc u) p|
      ≤ 2 * C * (1 / eps + 1 / eps ^ 2) * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by simp)
  have hRpos : 0 < p.1.1 := lt_of_lt_of_le heps hR
  have hMnn : (0 : ℝ) ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hC (Real.rpow_nonneg (by linarith only [htau]) _)
  have hd0 : (0 : ℝ) ≤ lam ^ (2 * h) := Real.rpow_nonneg hlam.le _
  have b1 : |dr (dz (zoomV lam h zc u)) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) :=
    le_trans (abs_drdz_zoomV_le C h lam zc hlam u hb hu2 p hp)
      (const_mul_rpow_le_neg_half hC htau (by linarith only [hh1]))
  have b2 : |dr (dr (zoomW lam h zc u)) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
    have hbnd := abs_drdr_zoomW_add_abs_drdr_zoomS_le C h lam zc hlam u hb hu2 p hp
    have hS : (0 : ℝ) ≤ |dr (dr (zoomS lam h zc u)) p| := abs_nonneg _
    have hW : |dr (dr (zoomW lam h zc u)) p|
        ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - h - 2 / 2 - (1 / 2 - h) * 0) := by
      linarith only [hbnd, hS]
    exact le_trans hW (const_mul_rpow_le_neg_half hC htau (by linarith only [hh0]))
  have b3 : |dz (zoomV lam h zc u) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) :=
    abs_dz_zoomV_le_rpow_neg_half hlam hb hu2 hp hC hh1 htau
  have b4 : |dr (zoomW lam h zc u) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) :=
    abs_dr_zoomW_le_rpow_neg_half hlam hb hu2 hp hC hh0 htau
  rw [dr_zoomOmega_eq lam h zc hlam u hu2 p hp hRpos]
  refine le_trans (abs_quot_deriv_le heps hR hMnn (abs_sq_smul_sub_le hd0 hdelta b1 b2)
    (abs_sq_smul_sub_le hd0 hdelta b3 b4)) (le_of_eq ?_)
  ring

/-- The vertical derivative of `Ω_n` on `{R ≥ ε}`, uniformly in the zoom scale, with the
exponent `-1/2` of `eq:aniso:zoom:derivatives`. -/
theorem abs_dz_zoomOmega_le {C h lam zc eps : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hC : 0 ≤ C) (hh1 : h ≤ 1 / 2) (hdelta : lam ^ (2 * h) ≤ 1)
    (heps : 0 < eps) {p : (ℝ × ℝ) × ℝ} (hR : eps ≤ p.1.1)
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (htau : p.2 ≤ -1) :
    |dz (zoomOmega lam h zc u) p|
      ≤ 2 * C * (1 / eps) * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by simp)
  have hRpos : 0 < p.1.1 := lt_of_lt_of_le heps hR
  have hMnn : (0 : ℝ) ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hC (Real.rpow_nonneg (by linarith only [htau]) _)
  have hd0 : (0 : ℝ) ≤ lam ^ (2 * h) := Real.rpow_nonneg hlam.le _
  have b5 : |dz (dz (zoomV lam h zc u)) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) :=
    le_trans (abs_dzdz_zoomV_le C h lam zc hlam u hb hu2 p hp)
      (const_mul_rpow_le_neg_half hC htau (by linarith only [hh1]))
  have b6 : |dr (dz (zoomW lam h zc u)) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
    have hbnd := abs_drdz_zoomW_add_abs_drdz_zoomS_le C h lam zc hlam u hb hu2 p hp
    have hS : (0 : ℝ) ≤ |dr (dz (zoomS lam h zc u)) p| := abs_nonneg _
    have hexp : -(1 / 2 : ℝ) - h - 1 / 2 - (1 / 2 - h) * 1 = -(3 / 2 : ℝ) := by ring
    rw [hexp] at hbnd
    have hW : |dr (dz (zoomW lam h zc u)) p| ≤ C * (-p.2) ^ (-(3 / 2 : ℝ)) := by
      linarith only [hbnd, hS]
    exact le_trans hW (const_mul_rpow_le_neg_half hC htau (by norm_num))
  rw [dz_zoomOmega_eq lam h zc hlam u hu p hp hRpos]
  refine le_trans (abs_quot_deriv_le' heps hR hMnn (abs_sq_smul_sub_le hd0 hdelta b5 b6))
    (le_of_eq ?_)
  ring

/-- The first-derivative bound of `Ω_n` on `{R ≥ ε}`: the sum of the two spatial derivatives is
bounded by `2C(2ε⁻¹ + ε⁻²)(-τ)^{-1/2}`, uniformly in the zoom scale. -/
theorem abs_dr_zoomOmega_add_abs_dz_zoomOmega_le {C h lam zc eps : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2) (hdelta : lam ^ (2 * h) ≤ 1)
    (heps : 0 < eps) {p : (ℝ × ℝ) × ℝ} (hR : eps ≤ p.1.1)
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (htau : p.2 ≤ -1) :
    |dr (zoomOmega lam h zc u) p| + |dz (zoomOmega lam h zc u) p|
      ≤ 2 * C * (2 / eps + 1 / eps ^ 2) * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  have h1 := abs_dr_zoomOmega_le hlam hb hu hC hh0 hh1 hdelta heps hR hp htau
  have h2 := abs_dz_zoomOmega_le hlam hb hu hC hh1 hdelta heps hR hp htau
  have hsum : 2 * C * (1 / eps + 1 / eps ^ 2) * (-p.2) ^ (-(1 / 2 : ℝ))
      + 2 * C * (1 / eps) * (-p.2) ^ (-(1 / 2 : ℝ))
      = 2 * C * (2 / eps + 1 / eps ^ 2) * (-p.2) ^ (-(1 / 2 : ℝ)) := by ring
  linarith only [h1, h2, hsum]

/-! ### The Lipschitz bound on a rectangle -/

/-- The `τ`-uniform form of the radial bound: for `τ ≤ -1` the power `(-τ)^{-1/2}` is at most
`1`, so the radial derivative is bounded by the constant `2C(ε⁻¹ + ε⁻²)`. -/
private theorem abs_dr_zoomOmega_le_const {C h lam zc eps : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2) (hdelta : lam ^ (2 * h) ≤ 1)
    (heps : 0 < eps) {p : (ℝ × ℝ) × ℝ} (hR : eps ≤ p.1.1)
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (htau : p.2 ≤ -1) :
    |dr (zoomOmega lam h zc u) p| ≤ 2 * C * (1 / eps + 1 / eps ^ 2) := by
  have hbnd := abs_dr_zoomOmega_le hlam hb hu hC hh0 hh1 hdelta heps hR hp htau
  have hpow : (-p.2) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    neg_rpow_le_one_of_le_neg_one htau (by norm_num)
  have hcoef : (0 : ℝ) ≤ 2 * C * (1 / eps + 1 / eps ^ 2) :=
    mul_nonneg (by linarith only [hC]) (by positivity)
  have hstep : 2 * C * (1 / eps + 1 / eps ^ 2) * (-p.2) ^ (-(1 / 2 : ℝ))
      ≤ 2 * C * (1 / eps + 1 / eps ^ 2) * 1 :=
    mul_le_mul_of_nonneg_left hpow hcoef
  linarith only [hbnd, hstep]

/-- The `τ`-uniform form of the vertical bound. -/
private theorem abs_dz_zoomOmega_le_const {C h lam zc eps : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hC : 0 ≤ C) (hh1 : h ≤ 1 / 2) (hdelta : lam ^ (2 * h) ≤ 1)
    (heps : 0 < eps) {p : (ℝ × ℝ) × ℝ} (hR : eps ≤ p.1.1)
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (htau : p.2 ≤ -1) :
    |dz (zoomOmega lam h zc u) p| ≤ 2 * C * (1 / eps) := by
  have hbnd := abs_dz_zoomOmega_le hlam hb hu hC hh1 hdelta heps hR hp htau
  have hpow : (-p.2) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    neg_rpow_le_one_of_le_neg_one htau (by norm_num)
  have hcoef : (0 : ℝ) ≤ 2 * C * (1 / eps) :=
    mul_nonneg (by linarith only [hC]) (by positivity)
  have hstep : 2 * C * (1 / eps) * (-p.2) ^ (-(1 / 2 : ℝ)) ≤ 2 * C * (1 / eps) * 1 :=
    mul_le_mul_of_nonneg_left hpow hcoef
  linarith only [hbnd, hstep]

/-- The two-point bound on a rectangle `[Ra, Rb] × [Za, Zb] ⊆ {R ≥ ε}` at a fixed rescaled time
`τ ≤ -1`: joining the two points by the two coordinate edges through `(y₂₁, y₁₂)` and applying the
mean value inequality on each edge. -/
theorem abs_zoomOmega_sub_zoomOmega_le {C h lam zc eps Ra Rb Za Zb tau : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2) (hdelta : lam ^ (2 * h) ≤ 1)
    (heps : 0 < eps) (hepsRa : eps ≤ Ra) (htau : tau ≤ -1)
    (hmem : ∀ y ∈ Icc Ra Rb ×ˢ Icc Za Zb, zoomPoint lam h zc (y, tau) ∈ unitCylinder)
    {y1 y2 : ℝ × ℝ} (hy1 : y1 ∈ Icc Ra Rb ×ˢ Icc Za Zb)
    (hy2 : y2 ∈ Icc Ra Rb ×ˢ Icc Za Zb) :
    |zoomOmega lam h zc u (y1, tau) - zoomOmega lam h zc u (y2, tau)|
      ≤ 2 * C * (2 / eps + 1 / eps ^ 2) * dist y1 y2 := by
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by simp)
  have hMr : (0 : ℝ) ≤ 2 * C * (1 / eps + 1 / eps ^ 2) :=
    mul_nonneg (by linarith only [hC]) (by positivity)
  have hMz : (0 : ℝ) ≤ 2 * C * (1 / eps) :=
    mul_nonneg (by linarith only [hC]) (by positivity)
  -- the radial edge, at the height of `y1`
  have hedgeR : |zoomOmega lam h zc u ((y2.1, y1.2), tau)
      - zoomOmega lam h zc u ((y1.1, y1.2), tau)|
      ≤ 2 * C * (1 / eps + 1 / eps ^ 2) * |y2.1 - y1.1| := by
    have hderiv : ∀ r ∈ Icc Ra Rb,
        HasDerivWithinAt (fun r' : ℝ => zoomOmega lam h zc u ((r', y1.2), tau))
          (dr (zoomOmega lam h zc u) ((r, y1.2), tau)) (Icc Ra Rb) r := by
      intro r hr
      have hpt : ((r, y1.2) : ℝ × ℝ) ∈ Icc Ra Rb ×ˢ Icc Za Zb := ⟨hr, hy1.2⟩
      have hcyl : zoomPoint lam h zc (((r, y1.2) : ℝ × ℝ), tau) ∈ unitCylinder := hmem _ hpt
      have hRpos : 0 < r := lt_of_lt_of_le (lt_of_lt_of_le heps hepsRa) hr.1
      have hval : dr (zoomOmega lam h zc u) ((r, y1.2), tau)
          = (((lam ^ (2 * h)) ^ 2 * dr (dz (zoomV lam h zc u)) ((r, y1.2), tau)
                - dr (dr (zoomW lam h zc u)) ((r, y1.2), tau)) * r
              - ((lam ^ (2 * h)) ^ 2 * dz (zoomV lam h zc u) ((r, y1.2), tau)
                - dr (zoomW lam h zc u) ((r, y1.2), tau))) / r ^ 2 :=
        dr_zoomOmega_eq lam h zc hlam u hu2 ((r, y1.2), tau) hcyl hRpos
      rw [hval]
      exact (hasDerivAt_zoomOmega_radial lam h zc hlam u hu2 ((r, y1.2), tau) hcyl
        hRpos).hasDerivWithinAt
    have hbound : ∀ r ∈ Icc Ra Rb,
        ‖dr (zoomOmega lam h zc u) ((r, y1.2), tau)‖ ≤ 2 * C * (1 / eps + 1 / eps ^ 2) := by
      intro r hr
      have hpt : ((r, y1.2) : ℝ × ℝ) ∈ Icc Ra Rb ×ˢ Icc Za Zb := ⟨hr, hy1.2⟩
      have hcyl : zoomPoint lam h zc (((r, y1.2) : ℝ × ℝ), tau) ∈ unitCylinder := hmem _ hpt
      have hRe : eps ≤ r := le_trans hepsRa hr.1
      rw [Real.norm_eq_abs]
      exact abs_dr_zoomOmega_le_const hlam hb hu hC hh0 hh1 hdelta heps hRe hcyl htau
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      (convex_Icc Ra Rb) hy1.1 hy2.1
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
    exact hmvt
  -- the vertical edge, at the radius of `y2`
  have hedgeZ : |zoomOmega lam h zc u ((y2.1, y2.2), tau)
      - zoomOmega lam h zc u ((y2.1, y1.2), tau)|
      ≤ 2 * C * (1 / eps) * |y2.2 - y1.2| := by
    have hderiv : ∀ s ∈ Icc Za Zb,
        HasDerivWithinAt (fun s' : ℝ => zoomOmega lam h zc u ((y2.1, s'), tau))
          (dz (zoomOmega lam h zc u) ((y2.1, s), tau)) (Icc Za Zb) s := by
      intro s hs
      have hpt : ((y2.1, s) : ℝ × ℝ) ∈ Icc Ra Rb ×ˢ Icc Za Zb := ⟨hy2.1, hs⟩
      have hcyl : zoomPoint lam h zc (((y2.1, s) : ℝ × ℝ), tau) ∈ unitCylinder := hmem _ hpt
      have hRpos : 0 < y2.1 := lt_of_lt_of_le (lt_of_lt_of_le heps hepsRa) hy2.1.1
      have hval : dz (zoomOmega lam h zc u) ((y2.1, s), tau)
          = ((lam ^ (2 * h)) ^ 2 * dz (dz (zoomV lam h zc u)) ((y2.1, s), tau)
            - dr (dz (zoomW lam h zc u)) ((y2.1, s), tau)) / y2.1 :=
        dz_zoomOmega_eq lam h zc hlam u hu ((y2.1, s), tau) hcyl hRpos
      rw [hval]
      exact (hasDerivAt_zoomOmega_vertical lam h zc hlam u hu ((y2.1, s), tau) hcyl
        hRpos).hasDerivWithinAt
    have hbound : ∀ s ∈ Icc Za Zb,
        ‖dz (zoomOmega lam h zc u) ((y2.1, s), tau)‖ ≤ 2 * C * (1 / eps) := by
      intro s hs
      have hpt : ((y2.1, s) : ℝ × ℝ) ∈ Icc Ra Rb ×ˢ Icc Za Zb := ⟨hy2.1, hs⟩
      have hcyl : zoomPoint lam h zc (((y2.1, s) : ℝ × ℝ), tau) ∈ unitCylinder := hmem _ hpt
      have hRe : eps ≤ y2.1 := le_trans hepsRa hy2.1.1
      rw [Real.norm_eq_abs]
      exact abs_dz_zoomOmega_le_const hlam hb hu hC hh1 hdelta heps hRe hcyl htau
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
  have htri : |zoomOmega lam h zc u (y1, tau) - zoomOmega lam h zc u (y2, tau)|
      ≤ |zoomOmega lam h zc u (y1, tau) - zoomOmega lam h zc u ((y2.1, y1.2), tau)|
        + |zoomOmega lam h zc u ((y2.1, y1.2), tau) - zoomOmega lam h zc u (y2, tau)| :=
    abs_sub_le _ _ _
  have hsym1 : |zoomOmega lam h zc u (y1, tau) - zoomOmega lam h zc u ((y2.1, y1.2), tau)|
      = |zoomOmega lam h zc u ((y2.1, y1.2), tau) - zoomOmega lam h zc u (y1, tau)| :=
    abs_sub_comm _ _
  have hstep1 : 2 * C * (1 / eps + 1 / eps ^ 2) * |y2.1 - y1.1|
      ≤ 2 * C * (1 / eps + 1 / eps ^ 2) * dist y1 y2 :=
    mul_le_mul_of_nonneg_left hd1 hMr
  have hstep2 : 2 * C * (1 / eps) * |y2.2 - y1.2|
      ≤ 2 * C * (1 / eps) * dist y1 y2 := mul_le_mul_of_nonneg_left hd2 hMz
  have hcombine : 2 * C * (1 / eps + 1 / eps ^ 2) * dist y1 y2 + 2 * C * (1 / eps) * dist y1 y2
      = 2 * C * (2 / eps + 1 / eps ^ 2) * dist y1 y2 := by ring
  have hsym3 : |zoomOmega lam h zc u ((y2.1, y1.2), tau) - zoomOmega lam h zc u (y2, tau)|
      = |zoomOmega lam h zc u (y2, tau) - zoomOmega lam h zc u ((y2.1, y1.2), tau)| :=
    abs_sub_comm _ _
  linarith only [htri, hsym1, hsym3, hedgeR, hedgeZ, hstep1, hstep2, hcombine]

/-- The Lipschitz-in-space bound on a rectangle `[Ra, Rb] × [Za, Zb] ⊆ {R ≥ ε}`, at every
rescaled time `τ ≤ -1`, with a constant independent of the zoom scale and of `τ`. -/
theorem lipschitzOnWith_zoomOmega {C h lam zc eps Ra Rb Za Zb tau : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2) (hdelta : lam ^ (2 * h) ≤ 1)
    (heps : 0 < eps) (hepsRa : eps ≤ Ra) (htau : tau ≤ -1)
    (hmem : ∀ y ∈ Icc Ra Rb ×ˢ Icc Za Zb, zoomPoint lam h zc (y, tau) ∈ unitCylinder) :
    LipschitzOnWith (Real.toNNReal (2 * C * (2 / eps + 1 / eps ^ 2)))
      (fun y : ℝ × ℝ => zoomOmega lam h zc u (y, tau)) (Icc Ra Rb ×ˢ Icc Za Zb) := by
  have hLnn : (0 : ℝ) ≤ 2 * C * (2 / eps + 1 / eps ^ 2) :=
    mul_nonneg (by linarith only [hC]) (by positivity)
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro y1 hy1 y2 hy2
  rw [Real.coe_toNNReal _ hLnn, Real.dist_eq]
  exact abs_zoomOmega_sub_zoomOmega_le hlam hb hu hC hh0 hh1 hdelta heps hepsRa htau hmem hy1 hy2

end CIV
