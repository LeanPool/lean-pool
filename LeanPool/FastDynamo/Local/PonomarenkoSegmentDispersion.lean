/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.PonomarenkoSectorOrderOneProduct

/-!
# The dispersion function on the paper's segment

The proof of `lem:jump-horizontal-mode` restricts the radial parameter to `κ = ϱ(1+it)` with
`t ∈ [1/2, 3/4]` and `ϱ` sufficiently large, and derives from the product expansion
`eq:bessel-product-expansion` the quantitative form

`ϱ³ 𝒟(ϱ(1+it)) = (1+it)⁻³ + O(ϱ⁻²)`, uniformly in `t`

(the display after `eq:dispersion`).  This module proves that expansion with an
explicit constant: the error is at most `225/(4ϱ²)`, for `ϱ ≥ 2` and `|t| ≤ 3/4`.

The route differs from the paper's, which quotes the expansions of `I₀K₀` and `I₂K₂` from
DLMF: it is the exact identity `ϱ³𝒟(ϱw) = 2Q_ϱ(w)/w³ - 2Q_ϱ'(w)/w²` for the order-one product
`Q_ϱ(w) = ϱ w I₁(ϱw)K₁(ϱw)`, the sectorised product estimate of
`PonomarenkoSectorOrderOneProduct`, and one Cauchy estimate on the radius-`1/5` disk about the
segment point.

## Contents

* The segment point `w = 1 + it`, its real and imaginary parts and its norm.
* Geometry of the radius-`1/5` disk about a segment point, and of its `ϱ`-dilate.
* The uniform order-one product bound and the Cauchy derivative bound on the segment.
* The explicit expansion `‖ϱ³𝒟(ϱ(1+it)) - (1+it)⁻³‖ ≤ 225/(4ϱ²)`.
-/

@[expose] public section

noncomputable section

namespace FastDynamo

open Complex Set

/-! ## The segment point -/

/-- The segment parameter `w = 1 + i t` of the proof of `lem:jump-horizontal-mode`
(`κ = ϱ w`). -/
def ponomarenkoSegmentPoint (t : ℝ) : ℂ :=
  1 + (t : ℂ) * I

@[simp] theorem ponomarenkoSegmentPoint_re (t : ℝ) :
    (ponomarenkoSegmentPoint t).re = 1 := by
  simp [ponomarenkoSegmentPoint]

@[simp] theorem ponomarenkoSegmentPoint_im (t : ℝ) :
    (ponomarenkoSegmentPoint t).im = t := by
  simp [ponomarenkoSegmentPoint]

theorem ponomarenkoScaledSegmentPoint_re (ϱ t : ℝ) :
    (((ϱ : ℂ) * ponomarenkoSegmentPoint t).re) = ϱ := by
  simp [Complex.mul_re]

theorem ponomarenkoScaledSegmentPoint_im (ϱ t : ℝ) :
    (((ϱ : ℂ) * ponomarenkoSegmentPoint t).im) = ϱ * t := by
  simp [Complex.mul_im]

/-- The segment point is never zero: its real part is one. -/
theorem ponomarenkoSegmentPoint_ne_zero (t : ℝ) :
    ponomarenkoSegmentPoint t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  rw [ponomarenkoSegmentPoint_re] at hre
  norm_num at hre

theorem normSq_ponomarenkoSegmentPoint (t : ℝ) :
    Complex.normSq (ponomarenkoSegmentPoint t) = 1 + t ^ 2 := by
  rw [Complex.normSq_apply, ponomarenkoSegmentPoint_re, ponomarenkoSegmentPoint_im]
  ring

theorem one_le_norm_ponomarenkoSegmentPoint (t : ℝ) :
    1 ≤ ‖ponomarenkoSegmentPoint t‖ := by
  have h := Complex.re_le_norm (ponomarenkoSegmentPoint t)
  rwa [ponomarenkoSegmentPoint_re] at h

/-- On the paper's segment the point has norm at most `5/4`. -/
theorem norm_ponomarenkoSegmentPoint_le {t : ℝ} (ht : |t| ≤ 3 / 4) :
    ‖ponomarenkoSegmentPoint t‖ ≤ 5 / 4 := by
  have hsq : ‖ponomarenkoSegmentPoint t‖ ^ 2 = 1 + t ^ 2 := by
    rw [Complex.sq_norm]
    exact normSq_ponomarenkoSegmentPoint t
  have habs := abs_le.mp ht
  have htsq : t ^ 2 ≤ 9 / 16 := by nlinarith [habs.1, habs.2]
  nlinarith [norm_nonneg (ponomarenkoSegmentPoint t), hsq, htsq]

theorem continuous_ponomarenkoSegmentPoint :
    Continuous ponomarenkoSegmentPoint := by
  unfold ponomarenkoSegmentPoint
  exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

/-! ## Geometry of the radius-`1/5` disk about a segment point -/

/-- Every point of the radius-`1/5` disk about a segment point has real part at least `4/5`
and norm at most `29/20`. -/
theorem ponomarenkoSegmentDisk_geometry {t : ℝ} (ht : |t| ≤ 3 / 4) {u : ℂ}
    (hu : u ∈ Metric.closedBall (ponomarenkoSegmentPoint t) (1 / 5 : ℝ)) :
    (4 / 5 : ℝ) ≤ u.re ∧ ‖u‖ ≤ (29 / 20 : ℝ) := by
  have hdist : ‖u - ponomarenkoSegmentPoint t‖ ≤ (1 / 5 : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu
  constructor
  · have hre : |u.re - 1| ≤ (1 / 5 : ℝ) := by
      calc
        |u.re - 1| = |(u - ponomarenkoSegmentPoint t).re| := by
          rw [Complex.sub_re, ponomarenkoSegmentPoint_re]
        _ ≤ ‖u - ponomarenkoSegmentPoint t‖ := Complex.abs_re_le_norm _
        _ ≤ (1 / 5 : ℝ) := hdist
    have := neg_le_of_abs_le hre
    linarith
  · calc
      ‖u‖ = ‖(u - ponomarenkoSegmentPoint t) + ponomarenkoSegmentPoint t‖ := by
        congr 1
        ring
      _ ≤ ‖u - ponomarenkoSegmentPoint t‖ + ‖ponomarenkoSegmentPoint t‖ :=
        norm_add_le _ _
      _ ≤ (1 / 5 : ℝ) + 5 / 4 := add_le_add hdist (norm_ponomarenkoSegmentPoint_le ht)
      _ = (29 / 20 : ℝ) := by norm_num

/-- The `ϱ`-dilate of the radius-`1/5` disk about a segment point lies in the aperture-two
sector `‖z‖ ≤ 2 Re z` and has real part at least `(4/5)ϱ ≥ 1`. -/
theorem ponomarenkoSegmentDisk_scaled_geometry {ϱ : ℝ} (hϱ : 2 ≤ ϱ) {t : ℝ}
    (ht : |t| ≤ 3 / 4) {u : ℂ}
    (hu : u ∈ Metric.closedBall (ponomarenkoSegmentPoint t) (1 / 5 : ℝ)) :
    (4 / 5 : ℝ) * ϱ ≤ (((ϱ : ℂ) * u).re) ∧ 1 ≤ (((ϱ : ℂ) * u).re) ∧
      ‖(ϱ : ℂ) * u‖ ≤ 2 * (((ϱ : ℂ) * u).re) := by
  obtain ⟨hre, hnorm⟩ := ponomarenkoSegmentDisk_geometry ht hu
  have hϱpos : 0 < ϱ := by linarith
  have hreEq : (((ϱ : ℂ) * u).re) = ϱ * u.re := by
    simp [Complex.mul_re]
  have hnormEq : ‖(ϱ : ℂ) * u‖ = ϱ * ‖u‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hϱpos]
  refine ⟨?_, ?_, ?_⟩
  · rw [hreEq]
    nlinarith
  · rw [hreEq]
    nlinarith
  · rw [hreEq, hnormEq]
    have hsector : ‖u‖ ≤ 2 * u.re := by linarith
    nlinarith

/-! ## The order-one product on the segment disk -/

/-- Uniform order-one product estimate on the radius-`1/5` disk about a segment point. -/
theorem norm_ponomarenkoScaledOrderOneProduct_sub_half_le_on_segment_disk
    {ϱ : ℝ} (hϱ : 2 ≤ ϱ) {t : ℝ} (ht : |t| ≤ 3 / 4) {u : ℂ}
    (hu : u ∈ Metric.closedBall (ponomarenkoSegmentPoint t) (1 / 5 : ℝ)) :
    ‖ponomarenkoScaledOrderOneProduct ϱ u - (1 / 2 : ℂ)‖ ≤ 75 / (16 * ϱ ^ 2) := by
  obtain ⟨hlow, hone, hsector⟩ := ponomarenkoSegmentDisk_scaled_geometry hϱ ht hu
  have hϱpos : 0 < ϱ := by linarith
  have hbound :=
    norm_ponomarenkoOrderOneProduct_mul_sub_half_le_three_div_re_sq hone hsector
  have heq : ponomarenkoScaledOrderOneProduct ϱ u =
      (ϱ : ℂ) * u * ponomarenkoOrderOneProduct ((ϱ : ℂ) * u) := rfl
  rw [heq]
  refine hbound.trans ?_
  have hposRe : 0 < (((ϱ : ℂ) * u).re) := by linarith
  have hsq : ((4 / 5 : ℝ) * ϱ) ^ 2 ≤ (((ϱ : ℂ) * u).re) ^ 2 := by
    nlinarith [hlow, hϱpos]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hsq]

/-- The scaled order-one product is differentiable on the radius-`1/5` disk about a segment
point. -/
theorem differentiableOn_ponomarenkoScaledOrderOneProduct_segment_disk
    {ϱ : ℝ} (hϱ : 2 ≤ ϱ) {t : ℝ} (ht : |t| ≤ 3 / 4) :
    DifferentiableOn ℂ (ponomarenkoScaledOrderOneProduct ϱ)
      (Metric.closedBall (ponomarenkoSegmentPoint t) (1 / 5 : ℝ)) := by
  intro u hu
  obtain ⟨hre, _⟩ := ponomarenkoSegmentDisk_geometry ht hu
  have hϱpos : 0 < ϱ := by linarith
  have hmem : u ∈ {v : ℂ | 0 < v.re} := by
    change (0 : ℝ) < u.re
    linarith
  exact (ponomarenkoScaledOrderOneProduct_analyticOnNhd hϱpos u
    hmem).differentiableAt.differentiableWithinAt

/-- Cauchy estimate at the centre of the segment disk: the derivative of the scaled order-one
product at a segment point is at most five times the uniform disk bound. -/
theorem norm_deriv_ponomarenkoScaledOrderOneProduct_le_on_segment
    {ϱ : ℝ} (hϱ : 2 ≤ ϱ) {t : ℝ} (ht : |t| ≤ 3 / 4) :
    ‖deriv (ponomarenkoScaledOrderOneProduct ϱ) (ponomarenkoSegmentPoint t)‖ ≤
      375 / (16 * ϱ ^ 2) := by
  have hcauchy :=
    norm_deriv_le_div_radius_gap_of_norm_sub_const_le
      (ponomarenkoScaledOrderOneProduct ϱ) (1 / 2 : ℂ)
      (ponomarenkoSegmentPoint t) (R := (1 / 5 : ℝ)) (r := 0)
      (by norm_num)
      (differentiableOn_ponomarenkoScaledOrderOneProduct_segment_disk hϱ ht)
      (fun u hu ↦
        norm_ponomarenkoScaledOrderOneProduct_sub_half_le_on_segment_disk hϱ ht hu)
      (Metric.mem_closedBall_self le_rfl)
  calc
    ‖deriv (ponomarenkoScaledOrderOneProduct ϱ) (ponomarenkoSegmentPoint t)‖ ≤
        75 / (16 * ϱ ^ 2) / ((1 / 5 : ℝ) - 0) := hcauchy
    _ = 375 / (16 * ϱ ^ 2) := by
      norm_num
      ring

/-! ## The expansion on the segment -/

/-- The scaled dispersion along the paper's segment, `ϱ³𝒟(ϱ(1+it))`. -/
def ponomarenkoSegmentDispersion (ϱ t : ℝ) : ℂ :=
  (ϱ : ℂ) ^ 3 * ponomarenkoDispersion ((ϱ : ℂ) * ponomarenkoSegmentPoint t)

/-- Unfolding lemma for the scaled dispersion along the segment. -/
theorem ponomarenkoSegmentDispersion_apply (ϱ t : ℝ) :
    ponomarenkoSegmentDispersion ϱ t =
      (ϱ : ℂ) ^ 3 *
        ponomarenkoDispersion ((ϱ : ℂ) * ponomarenkoSegmentPoint t) :=
  rfl

/-- The scaled dispersion along the segment is a continuous function of `t`. -/
theorem continuous_ponomarenkoSegmentDispersion {ϱ : ℝ} (hϱ : 0 < ϱ) :
    Continuous (ponomarenkoSegmentDispersion ϱ) := by
  rw [continuous_iff_continuousAt]
  intro t
  change ContinuousAt
    (fun s : ℝ ↦ (ϱ : ℂ) ^ 3 *
      ponomarenkoDispersion ((ϱ : ℂ) * ponomarenkoSegmentPoint s)) t
  have hre : 0 < (((ϱ : ℂ) * ponomarenkoSegmentPoint t).re) := by
    rw [ponomarenkoScaledSegmentPoint_re]
    exact hϱ
  have h1 : ContinuousAt (fun s : ℝ ↦ (ϱ : ℂ) * ponomarenkoSegmentPoint s) t :=
    (continuous_const.mul continuous_ponomarenkoSegmentPoint).continuousAt
  have hD : ContinuousAt ponomarenkoDispersion
      ((ϱ : ℂ) * ponomarenkoSegmentPoint t) :=
    (ponomarenkoDispersion_analyticOnNhd _ hre).continuousAt
  have hcomp : ContinuousAt
      (ponomarenkoDispersion ∘
        fun s : ℝ ↦ (ϱ : ℂ) * ponomarenkoSegmentPoint s) t := by
    refine ContinuousAt.comp ?_ h1
    exact hD
  exact continuousAt_const.mul hcomp

/-- The exact error identity behind the expansion: with `Q_ϱ` the scaled order-one product,
`ϱ³𝒟(ϱw) - w⁻³ = 2(Q_ϱ(w) - 1/2)/w³ - 2Q_ϱ'(w)/w²`. -/
theorem ponomarenko_cube_dispersion_sub_inv_cube_eq
    {ϱ : ℝ} (hϱ : 0 < ϱ) {w : ℂ} (hw : 0 < w.re) :
    (ϱ : ℂ) ^ 3 * ponomarenkoDispersion ((ϱ : ℂ) * w) - (w ^ 3)⁻¹ =
      2 * (ponomarenkoScaledOrderOneProduct ϱ w - (1 / 2 : ℂ)) / w ^ 3 -
        2 * deriv (ponomarenkoScaledOrderOneProduct ϱ) w / w ^ 2 := by
  rw [ponomarenko_scaledDispersion_besselPart_eq_orderOneProduct hϱ hw]
  ring

/-- The quantitative product expansion of the proof of `lem:jump-horizontal-mode`, with an
explicit constant: on the segment `κ = ϱ(1+it)` with `|t| ≤ 3/4`,

`‖ϱ³𝒟(ϱ(1+it)) - (1+it)⁻³‖ ≤ 225/(4ϱ²)`. -/
theorem norm_ponomarenkoSegmentDispersion_sub_inv_cube_le
    {ϱ : ℝ} (hϱ : 2 ≤ ϱ) {t : ℝ} (ht : |t| ≤ 3 / 4) :
    ‖ponomarenkoSegmentDispersion ϱ t - (ponomarenkoSegmentPoint t ^ 3)⁻¹‖ ≤
      225 / (4 * ϱ ^ 2) := by
  have hϱpos : 0 < ϱ := by linarith
  have hwRe : 0 < (ponomarenkoSegmentPoint t).re := by
    rw [ponomarenkoSegmentPoint_re]
    norm_num
  have hδ : (0 : ℝ) ≤ 75 / (16 * ϱ ^ 2) := by positivity
  have hη : (0 : ℝ) ≤ 375 / (16 * ϱ ^ 2) := by positivity
  have hid := ponomarenko_cube_dispersion_sub_inv_cube_eq hϱpos hwRe
  have hmain :=
    norm_error_le_two_mul_add_of_order_one_product_identity
      (ponomarenkoScaledOrderOneProduct ϱ)
      (fun v : ℂ ↦ (ϱ : ℂ) ^ 3 * ponomarenkoDispersion ((ϱ : ℂ) * v) - (v ^ 3)⁻¹)
      hδ hη (one_le_norm_ponomarenkoSegmentPoint t)
      (norm_ponomarenkoScaledOrderOneProduct_sub_half_le_on_segment_disk hϱ ht
        (Metric.mem_closedBall_self (by norm_num)))
      (norm_deriv_ponomarenkoScaledOrderOneProduct_le_on_segment hϱ ht)
      hid
  calc
    ‖ponomarenkoSegmentDispersion ϱ t - (ponomarenkoSegmentPoint t ^ 3)⁻¹‖ ≤
        2 * (75 / (16 * ϱ ^ 2)) + 2 * (375 / (16 * ϱ ^ 2)) := hmain
    _ = 225 / (4 * ϱ ^ 2) := by ring

end FastDynamo
