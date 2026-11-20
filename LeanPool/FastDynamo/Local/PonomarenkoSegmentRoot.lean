/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.PonomarenkoFreeOmegaInterface
public import LeanPool.FastDynamo.Local.PonomarenkoSegmentDispersion

/-!
# The intermediate-value choice of the radial parameter and of `Ω`

This module carries out the choice of `κ` and `Ω` in the proof of `lem:jump-horizontal-mode`
(Lemma 2.1), by the same intermediate value argument as the paper.

The algebraic limit of `ϱ³𝒟(ϱ(1+it))` is `(1+it)⁻³`, whose real part `(1-3t²)/(1+t²)³` is
positive at `t = 1/2` and negative at `t = 3/4`, and whose imaginary part `(t³-3t)/(1+t²)³` is
at most `-1/3` throughout `[1/2, 3/4]`.  The quantitative expansion of
`PonomarenkoSegmentDispersion` transfers all three sign statements to `ϱ³𝒟(ϱ(1+it))` once
`ϱ ≥ 32`, and the intermediate value theorem then produces `t_ϱ ∈ (1/2, 3/4)` with
`Re 𝒟(ϱ(1+it_ϱ)) = 0`.  Setting

`κ = ϱ(1+it_ϱ)`,  `Ω = -2/Im 𝒟(κ) > 0`,  `U = -Ω/N`,  `λ_* = κ² - N²`

gives the dispersion relation `Ω 𝒟(κ) = -2i` exactly, the growth bound
`Re λ_* = ϱ²(1-t_ϱ²) - N² ≥ (7/16)ϱ² - N²`, and — through the sectorised product estimate and
the cross-Wronskian identities — the six modified-Bessel nonvanishing facts.  Everything is
packaged as a `CertifiedInterfaceData N Ω κ`.

The concrete instance uses the axial wavenumber `N = 2π` of the paper and the
explicit radial scale `ϱ = 32`, the smallest power of two above every threshold derived here.
The explicit numeral is a choice of the formalisation: the paper takes `ϱ` sufficiently large
and proves `Re λ_* ≥ (7/16)ϱ² - 4π² > 0`, which at `ϱ = 32` reads `Re λ_* ≥ 448 - 4π²`.

## Contents

* The algebraic limit `(1+it)⁻³`: its real and imaginary parts and their sign pattern.
* Transfer of the sign pattern to `ϱ³𝒟(ϱ(1+it))` for `ϱ ≥ 32`.
* The intermediate value theorem and the radial parameter `κ = ϱ(1+it_ϱ)`.
* The six modified-Bessel nonvanishing facts on the segment.
* The named local eigenvalue `λ_* = κ² - N²` and its real part on the segment.
* The certified free-`Ω` interface data, and its instance at `N = 2π`, `ϱ = 32`.

Besides the interface record itself, both existence statements expose the sector data of the
chosen `κ`: `Re κ = ϱ`, `Im κ ∈ (ϱ/2, 3ϱ/4)` and `‖κ‖ ≤ (5/4)ϱ ≤ 2 Re κ`.  The later local
steps need that sector bound for the exponential decay rate of `K_ν(κr)` and for the
resolvent estimates in `{Re z > 0}`; it is proved here anyway, on the way to the six
nonvanishing facts.
-/

@[expose] public section

noncomputable section

namespace FastDynamo

open Complex Set

/-! ## The algebraic limit `(1+it)⁻³` -/

/-- The cube of the segment point: `(1+it)³ = (1-3t²) + i(3t-t³)`. -/
theorem ponomarenkoSegmentPoint_cube (t : ℝ) :
    ponomarenkoSegmentPoint t ^ 3 =
      ((1 - 3 * t ^ 2 : ℝ) : ℂ) + ((3 * t - t ^ 3 : ℝ) : ℂ) * I := by
  rw [ponomarenkoSegmentPoint]
  push_cast
  linear_combination (3 * (t : ℂ) ^ 2 + (t : ℂ) ^ 3 * I) * Complex.I_sq

theorem ponomarenkoSegmentPoint_cube_re (t : ℝ) :
    (ponomarenkoSegmentPoint t ^ 3).re = 1 - 3 * t ^ 2 := by
  rw [ponomarenkoSegmentPoint_cube, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

theorem ponomarenkoSegmentPoint_cube_im (t : ℝ) :
    (ponomarenkoSegmentPoint t ^ 3).im = 3 * t - t ^ 3 := by
  rw [ponomarenkoSegmentPoint_cube, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

theorem normSq_ponomarenkoSegmentPoint_cube (t : ℝ) :
    Complex.normSq (ponomarenkoSegmentPoint t ^ 3) = (1 + t ^ 2) ^ 3 := by
  rw [map_pow, normSq_ponomarenkoSegmentPoint]

/-- `Re (1+it)⁻³ = (1-3t²)/(1+t²)³`, as displayed in the proof of `lem:jump-horizontal-mode`. -/
theorem re_inv_ponomarenkoSegmentPoint_cube (t : ℝ) :
    ((ponomarenkoSegmentPoint t ^ 3)⁻¹).re = (1 - 3 * t ^ 2) / (1 + t ^ 2) ^ 3 := by
  rw [Complex.inv_re, normSq_ponomarenkoSegmentPoint_cube,
    ponomarenkoSegmentPoint_cube_re]

/-- `Im (1+it)⁻³ = (t³-3t)/(1+t²)³`, as displayed in the proof of `lem:jump-horizontal-mode`. -/
theorem im_inv_ponomarenkoSegmentPoint_cube (t : ℝ) :
    ((ponomarenkoSegmentPoint t ^ 3)⁻¹).im = (t ^ 3 - 3 * t) / (1 + t ^ 2) ^ 3 := by
  rw [Complex.inv_im, normSq_ponomarenkoSegmentPoint_cube,
    ponomarenkoSegmentPoint_cube_im]
  ring

/-- At `t = 1/2` the real part of the algebraic limit is `16/125 > 0`. -/
theorem re_inv_ponomarenkoSegmentPoint_cube_half :
    ((ponomarenkoSegmentPoint (1 / 2 : ℝ) ^ 3)⁻¹).re = 16 / 125 := by
  rw [re_inv_ponomarenkoSegmentPoint_cube]
  norm_num

/-- At `t = 3/4` the real part of the algebraic limit is `-2816/15625 < 0`. -/
theorem re_inv_ponomarenkoSegmentPoint_cube_three_quarters :
    ((ponomarenkoSegmentPoint (3 / 4 : ℝ) ^ 3)⁻¹).re = -2816 / 15625 := by
  rw [re_inv_ponomarenkoSegmentPoint_cube]
  norm_num

/-- The imaginary part of the algebraic limit is at most `-1/3` throughout `[1/2, 3/4]`. -/
theorem im_inv_ponomarenkoSegmentPoint_cube_le {t : ℝ}
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) (3 / 4)) :
    ((ponomarenkoSegmentPoint t ^ 3)⁻¹).im ≤ -1 / 3 := by
  obtain ⟨h1, h2⟩ := ht
  rw [im_inv_ponomarenkoSegmentPoint_cube]
  have hden : (0 : ℝ) < (1 + t ^ 2) ^ 3 := by positivity
  rw [div_le_iff₀ hden]
  have hb : t ^ 2 + t / 2 - 11 / 4 ≤ 0 := by nlinarith
  have ha : (0 : ℝ) ≤ t - 1 / 2 := by linarith
  have hfac : (t - 1 / 2) * (t ^ 2 + t / 2 - 11 / 4) ≤ 0 := by nlinarith
  have hnum : t ^ 3 - 3 * t ≤ -11 / 8 := by nlinarith
  have ht2 : t ^ 2 ≤ 9 / 16 := by nlinarith
  have hle : 1 + t ^ 2 ≤ 25 / 16 := by linarith
  have h0 : (0 : ℝ) ≤ 1 + t ^ 2 := by positivity
  have hsq : (1 + t ^ 2) * (1 + t ^ 2) ≤ (25 / 16 : ℝ) * (25 / 16) :=
    mul_le_mul hle hle h0 (by norm_num)
  have hcube : (1 + t ^ 2) ^ 3 ≤ 15625 / 4096 := by nlinarith
  linarith

/-! ## Transfer of the sign pattern to the Bessel dispersion -/

/-- For `ϱ ≥ 32` the expansion error is at most `1/16`, which is smaller than each of the
three margins of the algebraic limit on the segment. -/
theorem ponomarenko_segment_error_le_one_div_sixteen {ϱ : ℝ} (hϱ : 32 ≤ ϱ) :
    225 / (4 * ϱ ^ 2) ≤ 1 / 16 := by
  have hϱ2 : (1024 : ℝ) ≤ ϱ ^ 2 := by nlinarith
  rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 4 * ϱ ^ 2) (by norm_num : (0 : ℝ) < 16)]
  linarith

/-- The real part of the Bessel dispersion differs from that of the algebraic limit by at
most the expansion error. -/
theorem abs_re_ponomarenkoSegmentDispersion_sub_le {ϱ : ℝ} (hϱ : 2 ≤ ϱ) {t : ℝ}
    (ht : |t| ≤ 3 / 4) :
    |(ponomarenkoSegmentDispersion ϱ t).re -
      ((ponomarenkoSegmentPoint t ^ 3)⁻¹).re| ≤ 225 / (4 * ϱ ^ 2) := by
  calc
    |(ponomarenkoSegmentDispersion ϱ t).re -
        ((ponomarenkoSegmentPoint t ^ 3)⁻¹).re| =
        |(ponomarenkoSegmentDispersion ϱ t -
          (ponomarenkoSegmentPoint t ^ 3)⁻¹).re| := by
      rw [Complex.sub_re]
    _ ≤ ‖ponomarenkoSegmentDispersion ϱ t -
        (ponomarenkoSegmentPoint t ^ 3)⁻¹‖ := Complex.abs_re_le_norm _
    _ ≤ 225 / (4 * ϱ ^ 2) :=
      norm_ponomarenkoSegmentDispersion_sub_inv_cube_le hϱ ht

/-- The imaginary part of the Bessel dispersion differs from that of the algebraic limit by at
most the expansion error. -/
theorem abs_im_ponomarenkoSegmentDispersion_sub_le {ϱ : ℝ} (hϱ : 2 ≤ ϱ) {t : ℝ}
    (ht : |t| ≤ 3 / 4) :
    |(ponomarenkoSegmentDispersion ϱ t).im -
      ((ponomarenkoSegmentPoint t ^ 3)⁻¹).im| ≤ 225 / (4 * ϱ ^ 2) := by
  calc
    |(ponomarenkoSegmentDispersion ϱ t).im -
        ((ponomarenkoSegmentPoint t ^ 3)⁻¹).im| =
        |(ponomarenkoSegmentDispersion ϱ t -
          (ponomarenkoSegmentPoint t ^ 3)⁻¹).im| := by
      rw [Complex.sub_im]
    _ ≤ ‖ponomarenkoSegmentDispersion ϱ t -
        (ponomarenkoSegmentPoint t ^ 3)⁻¹‖ := Complex.abs_im_le_norm _
    _ ≤ 225 / (4 * ϱ ^ 2) :=
      norm_ponomarenkoSegmentDispersion_sub_inv_cube_le hϱ ht

/-- The real part of `ϱ³𝒟(ϱ(1+it))`, as a real function of `t`. -/
def ponomarenkoSegmentDispersionRe (ϱ t : ℝ) : ℝ :=
  (ponomarenkoSegmentDispersion ϱ t).re

/-- At `t = 1/2` the real part of the Bessel dispersion is positive, for `ϱ ≥ 32`. -/
theorem ponomarenkoSegmentDispersionRe_pos_at_half {ϱ : ℝ} (hϱ : 32 ≤ ϱ) :
    0 < ponomarenkoSegmentDispersionRe ϱ (1 / 2 : ℝ) := by
  have hϱ2 : (2 : ℝ) ≤ ϱ := by linarith
  have hab : |(1 / 2 : ℝ)| ≤ 3 / 4 := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    norm_num
  have hdiff := abs_re_ponomarenkoSegmentDispersion_sub_le hϱ2 hab
  have herr := ponomarenko_segment_error_le_one_div_sixteen hϱ
  have hlimit := re_inv_ponomarenkoSegmentPoint_cube_half
  have hlow := neg_le_of_abs_le hdiff
  rw [hlimit] at hlow
  change 0 < (ponomarenkoSegmentDispersion ϱ (1 / 2 : ℝ)).re
  linarith

/-- At `t = 3/4` the real part of the Bessel dispersion is negative, for `ϱ ≥ 32`. -/
theorem ponomarenkoSegmentDispersionRe_neg_at_three_quarters {ϱ : ℝ} (hϱ : 32 ≤ ϱ) :
    ponomarenkoSegmentDispersionRe ϱ (3 / 4 : ℝ) < 0 := by
  have hϱ2 : (2 : ℝ) ≤ ϱ := by linarith
  have hab : |(3 / 4 : ℝ)| ≤ 3 / 4 := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
  have hdiff := abs_re_ponomarenkoSegmentDispersion_sub_le hϱ2 hab
  have herr := ponomarenko_segment_error_le_one_div_sixteen hϱ
  have hlimit := re_inv_ponomarenkoSegmentPoint_cube_three_quarters
  have hup := le_of_abs_le hdiff
  rw [hlimit] at hup
  change (ponomarenkoSegmentDispersion ϱ (3 / 4 : ℝ)).re < 0
  linarith

/-- The imaginary part of the Bessel dispersion is negative throughout `[1/2, 3/4]`, for
`ϱ ≥ 32`. -/
theorem im_ponomarenkoSegmentDispersion_neg {ϱ : ℝ} (hϱ : 32 ≤ ϱ) {t : ℝ}
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) (3 / 4)) :
    (ponomarenkoSegmentDispersion ϱ t).im < 0 := by
  have hϱ2 : (2 : ℝ) ≤ ϱ := by linarith
  have hab : |t| ≤ 3 / 4 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hdiff := abs_im_ponomarenkoSegmentDispersion_sub_le hϱ2 hab
  have herr := ponomarenko_segment_error_le_one_div_sixteen hϱ
  have hlimit := im_inv_ponomarenkoSegmentPoint_cube_le ht
  have hup := le_of_abs_le hdiff
  linarith

/-! ## The intermediate value theorem -/

/-- The intermediate value step of the proof of `lem:jump-horizontal-mode`:
for `ϱ ≥ 32` there is `t_ϱ ∈ (1/2, 3/4)` with `Re 𝒟(ϱ(1+it_ϱ)) = 0`. -/
theorem exists_ponomarenkoSegmentDispersionRe_eq_zero {ϱ : ℝ} (hϱ : 32 ≤ ϱ) :
    ∃ t : ℝ, t ∈ Set.Ioo (1 / 2 : ℝ) (3 / 4) ∧
      ponomarenkoSegmentDispersionRe ϱ t = 0 := by
  have hϱpos : (0 : ℝ) < ϱ := by linarith
  have hcont : ContinuousOn (ponomarenkoSegmentDispersionRe ϱ)
      (Set.Icc (1 / 2 : ℝ) (3 / 4)) :=
    (Complex.continuous_re.comp
      (continuous_ponomarenkoSegmentDispersion hϱpos)).continuousOn
  have hhalf := ponomarenkoSegmentDispersionRe_pos_at_half hϱ
  have hthree := ponomarenkoSegmentDispersionRe_neg_at_three_quarters hϱ
  have hmem : (0 : ℝ) ∈ Set.Icc (ponomarenkoSegmentDispersionRe ϱ (3 / 4 : ℝ))
      (ponomarenkoSegmentDispersionRe ϱ (1 / 2 : ℝ)) :=
    ⟨hthree.le, hhalf.le⟩
  obtain ⟨t, htmem, hft⟩ :=
    intermediate_value_Icc' (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4) hcont hmem
  refine ⟨t, ⟨lt_of_le_of_ne htmem.1 ?_, lt_of_le_of_ne htmem.2 ?_⟩, hft⟩
  · intro heq
    rw [← heq] at hft
    linarith
  · intro heq
    rw [heq] at hft
    linarith

/-! ## The radial parameter -/

/-- The radial parameter `κ = ϱ(1+it)` of the proof of `lem:jump-horizontal-mode`. -/
def ponomarenkoSegmentArgument (ϱ t : ℝ) : ℂ :=
  (ϱ : ℂ) * ponomarenkoSegmentPoint t

theorem ponomarenkoSegmentArgument_apply (ϱ t : ℝ) :
    ponomarenkoSegmentArgument ϱ t = (ϱ : ℂ) * ponomarenkoSegmentPoint t :=
  rfl

@[simp] theorem ponomarenkoSegmentArgument_re (ϱ t : ℝ) :
    (ponomarenkoSegmentArgument ϱ t).re = ϱ :=
  ponomarenkoScaledSegmentPoint_re ϱ t

@[simp] theorem ponomarenkoSegmentArgument_im (ϱ t : ℝ) :
    (ponomarenkoSegmentArgument ϱ t).im = ϱ * t :=
  ponomarenkoScaledSegmentPoint_im ϱ t

/-- Splitting the scaled dispersion into its real part times `ϱ³`. -/
theorem re_ponomarenkoSegmentDispersion (ϱ t : ℝ) :
    (ponomarenkoSegmentDispersion ϱ t).re =
      ϱ ^ 3 * (ponomarenkoDispersion (ponomarenkoSegmentArgument ϱ t)).re := by
  rw [ponomarenkoSegmentDispersion_apply, ← ponomarenkoSegmentArgument_apply,
    show ((ϱ : ℂ)) ^ 3 = ((ϱ ^ 3 : ℝ) : ℂ) by push_cast; ring,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Splitting the scaled dispersion into its imaginary part times `ϱ³`. -/
theorem im_ponomarenkoSegmentDispersion (ϱ t : ℝ) :
    (ponomarenkoSegmentDispersion ϱ t).im =
      ϱ ^ 3 * (ponomarenkoDispersion (ponomarenkoSegmentArgument ϱ t)).im := by
  rw [ponomarenkoSegmentDispersion_apply, ← ponomarenkoSegmentArgument_apply,
    show ((ϱ : ℂ)) ^ 3 = ((ϱ ^ 3 : ℝ) : ℂ) by push_cast; ring,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-! ## Bessel denominators at a point with small product and dispersion -/

/-- A hypothetical zero `K₀(z) = 0` collapses `z³𝒟(z)` to `4 z I₁(z)K₁(z) - 2z`. -/
private theorem cube_mul_dispersion_of_K0_eq_zero {z : ℂ} (hz : 0 < z.re)
    (hK0 : ModifiedBessel.K0 z = 0) :
    z ^ 3 * ponomarenkoDispersion z =
      4 * (z * ponomarenkoOrderOneProduct z) - 2 * z := by
  have hz0 : z ≠ 0 := by
    intro hzero
    rw [hzero] at hz
    simp at hz
  have hcross := ModifiedBessel.besselCross_eq_two_div_sq hz
  rw [hK0, mul_zero, sub_zero] at hcross
  have hcross' : z ^ 2 * (ModifiedBessel.I0 z * ModifiedBessel.K2 z) = 2 := by
    calc
      z ^ 2 * (ModifiedBessel.I0 z * ModifiedBessel.K2 z) =
          (ModifiedBessel.I0 z * ModifiedBessel.K2 z) * z ^ 2 := by ring
      _ = 2 := (eq_div_iff (pow_ne_zero 2 hz0)).mp hcross
  have hI1 := ModifiedBessel.I1_eq_half_mul_I0_sub_I2 z
  have hK1 := ModifiedBessel.K1_eq_z_div_two_mul_K2_sub_K0 hz
  rw [hK0, sub_zero] at hK1
  rw [ponomarenkoDispersion_apply, hK0, mul_zero, zero_sub,
    ponomarenkoOrderOneProduct, hI1, hK1]
  linear_combination -z * hcross'

/-- A hypothetical zero `K₂(z) = 0` collapses `z³𝒟(z)` to `-4 z I₁(z)K₁(z) - 2z`. -/
private theorem cube_mul_dispersion_of_K2_eq_zero {z : ℂ} (hz : 0 < z.re)
    (hK2 : ModifiedBessel.K2 z = 0) :
    z ^ 3 * ponomarenkoDispersion z =
      -4 * (z * ponomarenkoOrderOneProduct z) - 2 * z := by
  have hz0 : z ≠ 0 := by
    intro hzero
    rw [hzero] at hz
    simp at hz
  have hcross := ModifiedBessel.besselCross_eq_two_div_sq hz
  rw [hK2, mul_zero, zero_sub] at hcross
  have hcross' : z ^ 2 *
      (-(ModifiedBessel.I2 z * ModifiedBessel.K0 z)) = 2 := by
    calc
      z ^ 2 * (-(ModifiedBessel.I2 z * ModifiedBessel.K0 z)) =
          (-(ModifiedBessel.I2 z * ModifiedBessel.K0 z)) * z ^ 2 := by ring
      _ = 2 := (eq_div_iff (pow_ne_zero 2 hz0)).mp hcross
  have hI1 := ModifiedBessel.I1_eq_half_mul_I0_sub_I2 z
  have hK1 := ModifiedBessel.K1_eq_z_div_two_mul_K2_sub_K0 hz
  rw [hK2, zero_sub] at hK1
  rw [ponomarenkoDispersion_apply, hK2, mul_zero, sub_zero,
    ponomarenkoOrderOneProduct, hI1, hK1]
  linear_combination -z * hcross'

/-- A hypothetical zero `I₀(z) = 0` collapses `z³𝒟(z)` to `2z + 4 z I₁(z)K₁(z)`. -/
private theorem cube_mul_dispersion_of_I0_eq_zero {z : ℂ} (hz : 0 < z.re)
    (hI0 : ModifiedBessel.I0 z = 0) :
    z ^ 3 * ponomarenkoDispersion z =
      2 * z + 4 * (z * ponomarenkoOrderOneProduct z) := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp at hz
  have hcross := ModifiedBessel.besselCross_eq_two_div_sq hz
  have hcross' : z ^ 2 *
      (ModifiedBessel.I0 z * ModifiedBessel.K2 z -
        ModifiedBessel.I2 z * ModifiedBessel.K0 z) = 2 := by
    calc
      z ^ 2 *
          (ModifiedBessel.I0 z * ModifiedBessel.K2 z -
            ModifiedBessel.I2 z * ModifiedBessel.K0 z) =
          (ModifiedBessel.I0 z * ModifiedBessel.K2 z -
            ModifiedBessel.I2 z * ModifiedBessel.K0 z) * z ^ 2 := by ring
      _ = 2 := (eq_div_iff (pow_ne_zero 2 hz0)).mp hcross
  have hpoly : z ^ 2 * (ModifiedBessel.I2 z * ModifiedBessel.K0 z) = -2 := by
    calc
      z ^ 2 * (ModifiedBessel.I2 z * ModifiedBessel.K0 z) =
          -(z ^ 2 *
            (ModifiedBessel.I0 z * ModifiedBessel.K2 z -
              ModifiedBessel.I2 z * ModifiedBessel.K0 z)) := by
        rw [hI0]
        ring
      _ = -2 := by rw [hcross']
  rw [ponomarenkoDispersion_apply, ponomarenkoOrderOneProduct,
    ModifiedBessel.I1_eq_half_mul_I0_sub_I2,
    ModifiedBessel.K1_eq_z_div_two_mul_K2_sub_K0 hz, hI0]
  linear_combination -z * hpoly

/-- A hypothetical zero `I₂(z) = 0` collapses `z³𝒟(z)` to `2z - 4 z I₁(z)K₁(z)`. -/
private theorem cube_mul_dispersion_of_I2_eq_zero {z : ℂ} (hz : 0 < z.re)
    (hI2 : ModifiedBessel.I2 z = 0) :
    z ^ 3 * ponomarenkoDispersion z =
      2 * z - 4 * (z * ponomarenkoOrderOneProduct z) := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp at hz
  have hcross := ModifiedBessel.besselCross_eq_two_div_sq hz
  have hcross' : z ^ 2 *
      (ModifiedBessel.I0 z * ModifiedBessel.K2 z -
        ModifiedBessel.I2 z * ModifiedBessel.K0 z) = 2 := by
    calc
      z ^ 2 *
          (ModifiedBessel.I0 z * ModifiedBessel.K2 z -
            ModifiedBessel.I2 z * ModifiedBessel.K0 z) =
          (ModifiedBessel.I0 z * ModifiedBessel.K2 z -
            ModifiedBessel.I2 z * ModifiedBessel.K0 z) * z ^ 2 := by ring
      _ = 2 := (eq_div_iff (pow_ne_zero 2 hz0)).mp hcross
  have hpoly : z ^ 2 * (ModifiedBessel.I0 z * ModifiedBessel.K2 z) = 2 := by
    calc
      z ^ 2 * (ModifiedBessel.I0 z * ModifiedBessel.K2 z) =
          z ^ 2 *
            (ModifiedBessel.I0 z * ModifiedBessel.K2 z -
              ModifiedBessel.I2 z * ModifiedBessel.K0 z) := by
        rw [hI2]
        ring
      _ = 2 := hcross'
  rw [ponomarenkoDispersion_apply, ponomarenkoOrderOneProduct,
    ModifiedBessel.I1_eq_half_mul_I0_sub_I2,
    ModifiedBessel.K1_eq_z_div_two_mul_K2_sub_K0 hz, hI2]
  linear_combination z * hpoly

/-- All six modified-Bessel denominators used by the radial formulas
(`eq:bessel-solutions`) are nonzero at a
right-half-plane point where the order-one product is strictly within `1/2` of `1/2`,
the cubed dispersion has norm at most `2`, and `‖κ‖ > 3`. -/
theorem modifiedBessel_denominators_ne_zero_of_bounds {κ : ℂ} (hκ : 0 < κ.re)
    (hnorm : 3 < ‖κ‖)
    (hhalf : ‖κ * ponomarenkoOrderOneProduct κ - (1 / 2 : ℂ)‖ < 1 / 2)
    (hdisp : ‖κ ^ 3 * ponomarenkoDispersion κ‖ ≤ 2) :
    ModifiedBessel.I0 κ ≠ 0 ∧ ModifiedBessel.I1 κ ≠ 0 ∧
      ModifiedBessel.I2 κ ≠ 0 ∧ ModifiedBessel.K0 κ ≠ 0 ∧
      ModifiedBessel.K1 κ ≠ 0 ∧ ModifiedBessel.K2 κ ≠ 0 := by
  have hhalfNorm : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  have hQ : ‖κ * ponomarenkoOrderOneProduct κ‖ ≤ 1 := by
    have h1 : ‖κ * ponomarenkoOrderOneProduct κ‖ - ‖(1 / 2 : ℂ)‖ ≤
        ‖κ * ponomarenkoOrderOneProduct κ - (1 / 2 : ℂ)‖ :=
      norm_sub_norm_le _ _
    rw [hhalfNorm] at h1
    linarith
  have hQne : κ * ponomarenkoOrderOneProduct κ ≠ 0 := by
    intro h
    rw [h, zero_sub, norm_neg, hhalfNorm] at hhalf
    linarith
  have hI1 : ModifiedBessel.I1 κ ≠ 0 := by
    intro h
    apply hQne
    simp [ponomarenkoOrderOneProduct, h]
  have hK1 : ModifiedBessel.K1 κ ≠ 0 := by
    intro h
    apply hQne
    simp [ponomarenkoOrderOneProduct, h]
  have hfour : ‖4 * (κ * ponomarenkoOrderOneProduct κ)‖ ≤ 4 := by
    simpa [norm_mul] using
      mul_le_mul_of_nonneg_left hQ (by norm_num : (0 : ℝ) ≤ 4)
  refine ⟨?_, hI1, ?_, ?_, hK1, ?_⟩
  · intro hI0
    have heq := cube_mul_dispersion_of_I0_eq_zero hκ hI0
    have hbound : 2 * ‖κ‖ ≤ 6 := by
      calc
        2 * ‖κ‖ = ‖2 * κ‖ := by simp
        _ = ‖(2 * κ + 4 * (κ * ponomarenkoOrderOneProduct κ)) -
              4 * (κ * ponomarenkoOrderOneProduct κ)‖ := by
          congr 1
          ring
        _ ≤ ‖2 * κ + 4 * (κ * ponomarenkoOrderOneProduct κ)‖ +
              ‖4 * (κ * ponomarenkoOrderOneProduct κ)‖ := norm_sub_le _ _
        _ ≤ 2 + 4 := by
          rw [← heq]
          exact add_le_add hdisp hfour
        _ = 6 := by norm_num
    linarith
  · intro hI2
    have heq := cube_mul_dispersion_of_I2_eq_zero hκ hI2
    have hbound : 2 * ‖κ‖ ≤ 6 := by
      calc
        2 * ‖κ‖ = ‖2 * κ‖ := by simp
        _ = ‖(2 * κ - 4 * (κ * ponomarenkoOrderOneProduct κ)) +
              4 * (κ * ponomarenkoOrderOneProduct κ)‖ := by
          congr 1
          ring
        _ ≤ ‖2 * κ - 4 * (κ * ponomarenkoOrderOneProduct κ)‖ +
              ‖4 * (κ * ponomarenkoOrderOneProduct κ)‖ := norm_add_le _ _
        _ ≤ 2 + 4 := by
          rw [← heq]
          exact add_le_add hdisp hfour
        _ = 6 := by norm_num
    linarith
  · intro hK0
    have heq := cube_mul_dispersion_of_K0_eq_zero hκ hK0
    have hbound : 2 * ‖κ‖ ≤ 6 := by
      calc
        2 * ‖κ‖ = ‖2 * κ‖ := by simp
        _ = ‖4 * (κ * ponomarenkoOrderOneProduct κ) -
              (4 * (κ * ponomarenkoOrderOneProduct κ) - 2 * κ)‖ := by
          congr 1
          ring
        _ ≤ ‖4 * (κ * ponomarenkoOrderOneProduct κ)‖ +
              ‖4 * (κ * ponomarenkoOrderOneProduct κ) - 2 * κ‖ := norm_sub_le _ _
        _ ≤ 4 + 2 := by
          rw [← heq]
          exact add_le_add hfour hdisp
        _ = 6 := by norm_num
    linarith
  · intro hK2
    have heq := cube_mul_dispersion_of_K2_eq_zero hκ hK2
    have hneg : ‖-4 * (κ * ponomarenkoOrderOneProduct κ)‖ ≤ 4 := by
      simpa [norm_mul] using
        mul_le_mul_of_nonneg_left hQ (by norm_num : (0 : ℝ) ≤ 4)
    have hbound : 2 * ‖κ‖ ≤ 6 := by
      calc
        2 * ‖κ‖ = ‖2 * κ‖ := by simp
        _ = ‖-4 * (κ * ponomarenkoOrderOneProduct κ) -
              (-4 * (κ * ponomarenkoOrderOneProduct κ) - 2 * κ)‖ := by
          congr 1
          ring
        _ ≤ ‖-4 * (κ * ponomarenkoOrderOneProduct κ)‖ +
              ‖-4 * (κ * ponomarenkoOrderOneProduct κ) - 2 * κ‖ := norm_sub_le _ _
        _ ≤ 4 + 2 := by
          rw [← heq]
          exact add_le_add hneg hdisp
        _ = 6 := by norm_num
    linarith

/-! ## The two bounds on the segment -/

/-- On the segment and for `ϱ ≥ 32`, the order-one product is strictly within `1/2` of `1/2`. -/
theorem norm_orderOneProduct_sub_half_lt_half_on_segment {ϱ : ℝ} (hϱ : 32 ≤ ϱ) {t : ℝ}
    (ht : |t| ≤ 3 / 4) :
    ‖ponomarenkoSegmentArgument ϱ t *
        ponomarenkoOrderOneProduct (ponomarenkoSegmentArgument ϱ t) -
      (1 / 2 : ℂ)‖ < 1 / 2 := by
  have hϱpos : (0 : ℝ) < ϱ := by linarith
  have hone : 1 ≤ (ponomarenkoSegmentArgument ϱ t).re := by
    rw [ponomarenkoSegmentArgument_re]
    linarith
  have hnormEq : ‖ponomarenkoSegmentArgument ϱ t‖ =
      ϱ * ‖ponomarenkoSegmentPoint t‖ := by
    rw [ponomarenkoSegmentArgument_apply, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hϱpos]
  have hsector : ‖ponomarenkoSegmentArgument ϱ t‖ ≤
      2 * (ponomarenkoSegmentArgument ϱ t).re := by
    rw [hnormEq, ponomarenkoSegmentArgument_re]
    nlinarith [norm_ponomarenkoSegmentPoint_le ht, hϱpos]
  have hbound :=
    norm_ponomarenkoOrderOneProduct_mul_sub_half_le_three_div_re_sq hone hsector
  rw [ponomarenkoSegmentArgument_re] at hbound
  have hϱ2 : (1024 : ℝ) ≤ ϱ ^ 2 := by nlinarith
  have hsmall : (3 : ℝ) / ϱ ^ 2 < 1 / 2 := by
    rw [div_lt_div_iff₀ (by linarith : (0 : ℝ) < ϱ ^ 2) (by norm_num : (0 : ℝ) < 2)]
    linarith
  linarith

/-- The exact identity `κ³𝒟(κ) = 1 + w³(ϱ³𝒟(ϱw) - w⁻³)` for `κ = ϱw`, `w = 1 + it`. -/
theorem cube_mul_dispersion_eq_one_add_on_segment (ϱ t : ℝ) :
    ponomarenkoSegmentArgument ϱ t ^ 3 *
        ponomarenkoDispersion (ponomarenkoSegmentArgument ϱ t) =
      1 + ponomarenkoSegmentPoint t ^ 3 *
        (ponomarenkoSegmentDispersion ϱ t -
          (ponomarenkoSegmentPoint t ^ 3)⁻¹) := by
  have hcube : ponomarenkoSegmentPoint t ^ 3 *
      (ponomarenkoSegmentPoint t ^ 3)⁻¹ = 1 :=
    mul_inv_cancel₀ (pow_ne_zero 3 (ponomarenkoSegmentPoint_ne_zero t))
  rw [ponomarenkoSegmentArgument_apply, ponomarenkoSegmentDispersion_apply]
  linear_combination hcube

/-- On the segment and for `ϱ ≥ 32`, the cubed dispersion has norm at most `2`. -/
theorem norm_cube_mul_dispersion_le_two_on_segment {ϱ : ℝ} (hϱ : 32 ≤ ϱ) {t : ℝ}
    (ht : |t| ≤ 3 / 4) :
    ‖ponomarenkoSegmentArgument ϱ t ^ 3 *
      ponomarenkoDispersion (ponomarenkoSegmentArgument ϱ t)‖ ≤ 2 := by
  have hϱ2 : (2 : ℝ) ≤ ϱ := by linarith
  have hE := norm_ponomarenkoSegmentDispersion_sub_inv_cube_le hϱ2 ht
  have herr := ponomarenko_segment_error_le_one_div_sixteen hϱ
  have hw := norm_ponomarenkoSegmentPoint_le ht
  have hx0 : (0 : ℝ) ≤ ‖ponomarenkoSegmentPoint t‖ := norm_nonneg _
  have hsq : ‖ponomarenkoSegmentPoint t‖ * ‖ponomarenkoSegmentPoint t‖ ≤
      (5 / 4 : ℝ) * (5 / 4) :=
    mul_le_mul hw hw hx0 (by norm_num)
  have hpow : ‖ponomarenkoSegmentPoint t‖ ^ 3 ≤ (5 / 4 : ℝ) ^ 3 := by
    nlinarith [hx0, hw, hsq]
  have h2 : ‖ponomarenkoSegmentDispersion ϱ t -
      (ponomarenkoSegmentPoint t ^ 3)⁻¹‖ ≤ 1 / 16 := le_trans hE herr
  have hmul := mul_le_mul hpow h2 (norm_nonneg _)
    (by norm_num : (0 : ℝ) ≤ (5 / 4 : ℝ) ^ 3)
  rw [cube_mul_dispersion_eq_one_add_on_segment]
  calc
    ‖(1 : ℂ) + ponomarenkoSegmentPoint t ^ 3 *
        (ponomarenkoSegmentDispersion ϱ t -
          (ponomarenkoSegmentPoint t ^ 3)⁻¹)‖ ≤
        ‖(1 : ℂ)‖ + ‖ponomarenkoSegmentPoint t ^ 3 *
          (ponomarenkoSegmentDispersion ϱ t -
            (ponomarenkoSegmentPoint t ^ 3)⁻¹)‖ := norm_add_le _ _
    _ = 1 + ‖ponomarenkoSegmentPoint t‖ ^ 3 *
        ‖ponomarenkoSegmentDispersion ϱ t -
          (ponomarenkoSegmentPoint t ^ 3)⁻¹‖ := by
      rw [norm_mul, norm_pow, norm_one]
    _ ≤ 1 + (5 / 4 : ℝ) ^ 3 * (1 / 16 : ℝ) := by linarith
    _ ≤ 2 := by norm_num

/-- The six modified-Bessel nonvanishing facts on the segment, for `ϱ ≥ 32` (the paper
derives the nonvanishing of the denominators of `eq:bessel-solutions` from
`eq:bessel-product-expansion` for `ϱ` sufficiently large). -/
theorem modifiedBessel_denominators_ne_zero_on_segment {ϱ : ℝ} (hϱ : 32 ≤ ϱ) {t : ℝ}
    (ht : |t| ≤ 3 / 4) :
    ModifiedBessel.I0 (ponomarenkoSegmentArgument ϱ t) ≠ 0 ∧
      ModifiedBessel.I1 (ponomarenkoSegmentArgument ϱ t) ≠ 0 ∧
      ModifiedBessel.I2 (ponomarenkoSegmentArgument ϱ t) ≠ 0 ∧
      ModifiedBessel.K0 (ponomarenkoSegmentArgument ϱ t) ≠ 0 ∧
      ModifiedBessel.K1 (ponomarenkoSegmentArgument ϱ t) ≠ 0 ∧
      ModifiedBessel.K2 (ponomarenkoSegmentArgument ϱ t) ≠ 0 := by
  have hre : 0 < (ponomarenkoSegmentArgument ϱ t).re := by
    rw [ponomarenkoSegmentArgument_re]
    linarith
  have hnorm : 3 < ‖ponomarenkoSegmentArgument ϱ t‖ := by
    have h := Complex.re_le_norm (ponomarenkoSegmentArgument ϱ t)
    rw [ponomarenkoSegmentArgument_re] at h
    linarith
  exact modifiedBessel_denominators_ne_zero_of_bounds hre hnorm
    (norm_orderOneProduct_sub_half_lt_half_on_segment hϱ ht)
    (norm_cube_mul_dispersion_le_two_on_segment hϱ ht)

/-! ## The local eigenvalue `λ_*` -/

/-- The local eigenvalue `λ_* = κ² - N²` of `eq:local-eigenvalue` (where `N = 2π`).  Naming it
gives the later local steps a stable handle on the quantity whose positive real part drives
the whole construction. -/
def ponomarenkoLocalEigenvalue (N : ℝ) (κ : ℂ) : ℂ :=
  κ ^ 2 - (N : ℂ) ^ 2

/-- The defining formula of `λ_*`. -/
theorem ponomarenkoLocalEigenvalue_apply (N : ℝ) (κ : ℂ) :
    ponomarenkoLocalEigenvalue N κ = κ ^ 2 - (N : ℂ) ^ 2 :=
  rfl

/-- `Re λ_* = ϱ²(1 - t²) - N²` on the segment `κ = ϱ(1+it)`, the exact identity of
`eq:local-eigenvalue`. -/
theorem re_ponomarenkoLocalEigenvalue_segment (ϱ t N : ℝ) :
    (ponomarenkoLocalEigenvalue N (ponomarenkoSegmentArgument ϱ t)).re =
      ϱ ^ 2 * (1 - t ^ 2) - N ^ 2 := by
  rw [ponomarenkoLocalEigenvalue, Complex.sub_re,
    pow_two (ponomarenkoSegmentArgument ϱ t), pow_two ((N : ℂ)),
    Complex.mul_re, Complex.mul_re, ponomarenkoSegmentArgument_re,
    ponomarenkoSegmentArgument_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-! ## The certified free-`Ω` interface data -/

/-- The scalar half of `lem:jump-horizontal-mode`.

For every radial scale `ϱ ≥ 32` and every axial wavenumber `N > 0` with `N² < (7/16)ϱ²`, the
intermediate value theorem produces `t_ϱ ∈ (1/2, 3/4)` with `Re 𝒟(ϱ(1+it_ϱ)) = 0`; setting
`κ = ϱ(1+it_ϱ)` and `Ω = -2/Im 𝒟(κ) > 0` gives the exact dispersion relation `Ω 𝒟(κ) = -2i`,
the six Bessel nonvanishing facts, the four transverse transmission laws, and the growth
bound `Re λ_* = Re(κ² - N²) ≥ (7/16)ϱ² - N² > 0` of `eq:local-eigenvalue`.

The conclusion also exposes the sector data of the chosen `κ`, all of which is produced by
the proof anyway: `Re κ = ϱ`, `Im κ ∈ (ϱ/2, 3ϱ/4)` (from `t_ϱ ∈ (1/2, 3/4)`) and
`‖κ‖ ≤ (5/4)ϱ`, hence `‖κ‖ ≤ 2 Re κ`.  Since `κ` is existentially bound, a consumer cannot
recover `t_ϱ` and so cannot re-derive these. -/
theorem exists_certifiedInterfaceData_of_segment {ϱ : ℝ} (hϱ : 32 ≤ ϱ)
    {N : ℝ} (hN : 0 < N) (hNϱ : N ^ 2 < (7 / 16 : ℝ) * ϱ ^ 2) :
    ∃ (Ω : ℝ) (κ : ℂ),
      PonomarenkoFreeOmegaInterface.CertifiedInterfaceData N Ω κ ∧
        κ.re = ϱ ∧ ϱ / 2 < κ.im ∧ κ.im < 3 * ϱ / 4 ∧
          ‖κ‖ ≤ (5 / 4 : ℝ) * ϱ ∧
          (7 / 16 : ℝ) * ϱ ^ 2 - N ^ 2 ≤ (ponomarenkoLocalEigenvalue N κ).re := by
  have hϱpos : (0 : ℝ) < ϱ := by linarith
  have hϱcube : (0 : ℝ) < ϱ ^ 3 := by positivity
  obtain ⟨t, ht, hzero⟩ := exists_ponomarenkoSegmentDispersionRe_eq_zero hϱ
  have htIcc : t ∈ Set.Icc (1 / 2 : ℝ) (3 / 4) := ⟨ht.1.le, ht.2.le⟩
  have htabs : |t| ≤ 3 / 4 := abs_le.mpr ⟨by linarith [ht.1], ht.2.le⟩
  have hDre : (ponomarenkoDispersion (ponomarenkoSegmentArgument ϱ t)).re = 0 := by
    have h : (ponomarenkoSegmentDispersion ϱ t).re = 0 := hzero
    rw [re_ponomarenkoSegmentDispersion] at h
    rcases mul_eq_zero.mp h with hcase | hcase
    · exact absurd hcase (ne_of_gt hϱcube)
    · exact hcase
  have hDim : (ponomarenkoDispersion (ponomarenkoSegmentArgument ϱ t)).im < 0 := by
    have h := im_ponomarenkoSegmentDispersion_neg hϱ htIcc
    rw [im_ponomarenkoSegmentDispersion] at h
    by_contra hcon
    have hnn : (0 : ℝ) ≤
        (ponomarenkoDispersion (ponomarenkoSegmentArgument ϱ t)).im := not_lt.mp hcon
    nlinarith [mul_nonneg hϱcube.le hnn]
  have hDne : (ponomarenkoDispersion (ponomarenkoSegmentArgument ϱ t)).im ≠ 0 :=
    ne_of_lt hDim
  have ht2 : t ^ 2 ≤ 9 / 16 := by nlinarith [ht.1, ht.2]
  have himlow : ϱ / 2 < (ponomarenkoSegmentArgument ϱ t).im := by
    rw [ponomarenkoSegmentArgument_im]
    nlinarith [ht.1, hϱpos]
  have himhigh : (ponomarenkoSegmentArgument ϱ t).im < 3 * ϱ / 4 := by
    rw [ponomarenkoSegmentArgument_im]
    nlinarith [ht.2, hϱpos]
  have hnormκ : ‖ponomarenkoSegmentArgument ϱ t‖ ≤ (5 / 4 : ℝ) * ϱ := by
    rw [ponomarenkoSegmentArgument_apply, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hϱpos]
    nlinarith [norm_ponomarenkoSegmentPoint_le htabs, hϱpos]
  have hgrowthNum : (7 / 16 : ℝ) * ϱ ^ 2 - N ^ 2 ≤
      (ponomarenkoLocalEigenvalue N (ponomarenkoSegmentArgument ϱ t)).re := by
    rw [re_ponomarenkoLocalEigenvalue_segment]
    nlinarith [ht2, hϱpos,
      mul_nonneg (sq_nonneg ϱ) (by linarith : (0 : ℝ) ≤ 9 / 16 - t ^ 2)]
  refine ⟨-2 / (ponomarenkoDispersion (ponomarenkoSegmentArgument ϱ t)).im,
    ponomarenkoSegmentArgument ϱ t, ?_, ponomarenkoSegmentArgument_re ϱ t,
    himlow, himhigh, hnormκ, hgrowthNum⟩
  · have hΩim : (-2 / (ponomarenkoDispersion (ponomarenkoSegmentArgument ϱ t)).im) *
        (ponomarenkoDispersion (ponomarenkoSegmentArgument ϱ t)).im = -2 := by
      rw [div_mul_eq_mul_div, mul_div_assoc, div_self hDne, mul_one]
    have hΩpos : (0 : ℝ) <
        -2 / (ponomarenkoDispersion (ponomarenkoSegmentArgument ϱ t)).im := by
      nlinarith [hΩim, hDim]
    have hΩdisp : ((-2 /
        (ponomarenkoDispersion (ponomarenkoSegmentArgument ϱ t)).im : ℝ) : ℂ) *
          ponomarenkoDispersion (ponomarenkoSegmentArgument ϱ t) = -2 * I := by
      apply Complex.ext
      · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hDre]
        simp
      · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hΩim]
        simp
    have hκre : 0 < (ponomarenkoSegmentArgument ϱ t).re := by
      rw [ponomarenkoSegmentArgument_re]
      linarith
    obtain ⟨hI0, hI1, hI2, hK0, hK1, hK2⟩ :=
      modifiedBessel_denominators_ne_zero_on_segment hϱ htabs
    have hgrowth : 0 < ((ponomarenkoSegmentArgument ϱ t ^ 2 - (N : ℂ) ^ 2).re) := by
      have hEq : ((ponomarenkoSegmentArgument ϱ t ^ 2 - (N : ℂ) ^ 2).re) =
          (ponomarenkoLocalEigenvalue N (ponomarenkoSegmentArgument ϱ t)).re :=
        rfl
      rw [hEq]
      linarith [hgrowthNum, hNϱ]
    exact
      { scale_pos := hN
        omega_pos := hΩpos
        dispersion := hΩdisp
        kappa_re_pos := hκre
        spectral_growth := hgrowth
        I0_ne_zero := hI0
        I1_ne_zero := hI1
        I2_ne_zero := hI2
        K0_ne_zero := hK0
        K1_ne_zero := hK1
        K2_ne_zero := hK2
        radial_boundary_ne_zero :=
          PonomarenkoFreeOmegaInterface.radialInside_one_ne_zero_of_dispersion hΩdisp
        interface_laws :=
          PonomarenkoFreeOmegaInterface.transverseInterfaceLaws_of_dispersion hκre
            hΩdisp }

/-- The concrete scalar seed: the paper's axial wavenumber `N = 2π` and the
explicit radial scale `ϱ = 32` (a choice of the formalisation; the paper only takes `ϱ`
sufficiently large), the smallest power of two above every threshold used above.
The growth bound reads `Re λ_* ≥ 448 - 4π² > 0`, and the sector data of `κ` reads
`Re κ = 32`, `Im κ ∈ (16, 24)`, `‖κ‖ ≤ 40 = 2 Re κ · (5/8)`. -/
theorem exists_certifiedInterfaceData_two_pi :
    ∃ (Ω : ℝ) (κ : ℂ),
      PonomarenkoFreeOmegaInterface.CertifiedInterfaceData (2 * Real.pi) Ω κ ∧
        κ.re = 32 ∧ 16 < κ.im ∧ κ.im < 24 ∧ ‖κ‖ ≤ 40 ∧
          (448 : ℝ) - (2 * Real.pi) ^ 2 ≤
            (ponomarenkoLocalEigenvalue (2 * Real.pi) κ).re := by
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hpipos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hN : (0 : ℝ) < 2 * Real.pi := by linarith
  have hNϱ : (2 * Real.pi) ^ 2 < (7 / 16 : ℝ) * (32 : ℝ) ^ 2 := by nlinarith
  obtain ⟨Ω, κ, hdata, hre, himlow, himhigh, hnormκ, hgrowth⟩ :=
    exists_certifiedInterfaceData_of_segment (ϱ := (32 : ℝ)) (by norm_num) hN hNϱ
  refine ⟨Ω, κ, hdata, hre, by linarith, by linarith, by linarith, ?_⟩
  have hnum : (7 / 16 : ℝ) * (32 : ℝ) ^ 2 = 448 := by norm_num
  rw [hnum] at hgrowth
  exact hgrowth

end FastDynamo
