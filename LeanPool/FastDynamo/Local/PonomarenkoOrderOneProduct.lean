/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import Mathlib.Analysis.Complex.Liouville
public import LeanPool.FastDynamo.Local.ModifiedBesselWronskian

/-!
# The order-one Bessel product and the Cauchy bounds for the dispersion function

The proof of Lemma 2.1 (`lem:jump-horizontal-mode`) needs the dispersion function `𝒟` of
`eq:dispersion` on the segment `κ = ϱ(1+it)` in the quantitative form
`ϱ³𝒟(ϱ(1+it)) = (1+it)⁻³ + O(ϱ⁻²)` (the display after `eq:dispersion`), which
`PonomarenkoSegmentDispersion` proves.  This module supplies the exact identity and the two
estimates that proof rests on.

Everything is rewritten in terms of the order-one product `Q_N(w) = N w I₁(Nw) K₁(Nw)`, so
that the error is controlled by one leading estimate instead of separate asymptotic
expansions of `I₀K₀` and `I₂K₂`: the exact identity is
`N³𝒟(Nw) = 2Q_N(w)/w³ - 2Q_N'(w)/w²`.  A concentric-disk Cauchy estimate converts a uniform
bound for `Q_N - c` on a disk into a derivative bound on a smaller disk, and a pointwise
estimate bounds an error of the shape `2(Q - 1/2)/w³ - 2Q'/w²` for `1 ≤ ‖w‖`.

## Contents

* Scaled order-one Bessel product: `ponomarenkoOrderOneProduct` and its scaling
  `ponomarenkoScaledOrderOneProduct`, their analyticity and derivative, and the identity
  `ponomarenko_scaledDispersion_besselPart_eq_orderOneProduct`.
* Cauchy bounds: `norm_deriv_le_div_radius_gap_of_norm_sub_const_le` and
  `norm_error_le_two_mul_add_of_order_one_product_identity`.
-/

@[expose] public section

/-!
## Scaled order-one Bessel product

The scaled Ponomarenko dispersion is rewritten here in terms of the single
order-one product

`Q_N(w) = N w I₁(Nw) K₁(Nw)`.

Consequently, the remaining large-`N` analytic input can be stated as a leading estimate
for `Q_N` and its derivative, rather than as separate asymptotic expansions for four
modified-Bessel factors.
-/

noncomputable section

namespace FastDynamo

open Complex Set

/-- The central order-one modified-Bessel product. -/
def ponomarenkoOrderOneProduct (z : ℂ) : ℂ :=
  ModifiedBessel.I1 z * ModifiedBessel.K1 z

/-- The scaled order-one product `Q_N(w) = Nw I₁(Nw) K₁(Nw)`. -/
def ponomarenkoScaledOrderOneProduct (N : ℝ) (w : ℂ) : ℂ :=
  (N : ℂ) * w * ponomarenkoOrderOneProduct ((N : ℂ) * w)

/-- The order-one product is analytic on the open right half-plane. -/
theorem ponomarenkoOrderOneProduct_analyticOnNhd :
    AnalyticOnNhd ℂ ponomarenkoOrderOneProduct {z : ℂ | 0 < z.re} := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} :=
    continuous_re.isOpen_preimage _ isOpen_Ioi
  rw [analyticOnNhd_iff_differentiableOn hopen]
  intro z hz
  exact (ModifiedBessel.hasDerivAt_I1_mul_K1 hz).differentiableAt.differentiableWithinAt

/-- For positive scale, the scaled order-one product is analytic on the open
right half-plane in `w`. -/
theorem ponomarenkoScaledOrderOneProduct_analyticOnNhd {N : ℝ} (hN : 0 < N) :
    AnalyticOnNhd ℂ (ponomarenkoScaledOrderOneProduct N) {w : ℂ | 0 < w.re} := by
  intro w hw
  have hNw : 0 < (((N : ℂ) * w).re) := by
    simpa using mul_pos hN hw
  have hinner : AnalyticAt ℂ (fun u : ℂ ↦ (N : ℂ) * u) w :=
    analyticAt_const.mul analyticAt_id
  have hprod : AnalyticAt ℂ
      (fun u : ℂ ↦ ponomarenkoOrderOneProduct ((N : ℂ) * u)) w :=
    (ponomarenkoOrderOneProduct_analyticOnNhd ((N : ℂ) * w) hNw).comp hinner
  exact (analyticAt_const.mul analyticAt_id).mul hprod

/-- Exact derivative of the scaled order-one product in terms of the concrete
dispersion. -/
theorem hasDerivAt_ponomarenkoScaledOrderOneProduct
    {N : ℝ} {w : ℂ} (hN : 0 < N) (hw : 0 < w.re) :
    HasDerivAt (ponomarenkoScaledOrderOneProduct N)
      ((N : ℂ) * ponomarenkoOrderOneProduct ((N : ℂ) * w) -
        (N : ℂ) ^ 3 * w ^ 2 / 2 *
          ponomarenkoDispersion ((N : ℂ) * w)) w := by
  have hNw : 0 < (((N : ℂ) * w).re) := by
    simpa using mul_pos hN hw
  have hinner : HasDerivAt (fun u : ℂ ↦ (N : ℂ) * u) (N : ℂ) w :=
    by simpa using (hasDerivAt_id w).const_mul (N : ℂ)
  have hproduct := (ModifiedBessel.hasDerivAt_I1_mul_K1 hNw).comp w hinner
  have hscaled := (((hasDerivAt_const w (N : ℂ)).mul (hasDerivAt_id w)).mul hproduct)
  apply hscaled.congr_deriv
  simp only [Function.comp_apply, Pi.mul_apply, id_eq, ponomarenkoOrderOneProduct]
  ring

/-- Exact scaled identity
`N³ 𝒟(Nw) = 2 Q_N(w)/w³ - 2 Q_N'(w)/w²`. -/
theorem ponomarenko_scaledDispersion_besselPart_eq_orderOneProduct
    {N : ℝ} (hN : 0 < N) {w : ℂ} (hw : 0 < w.re) :
    (N : ℂ) ^ 3 * ponomarenkoDispersion ((N : ℂ) * w) =
      2 * ponomarenkoScaledOrderOneProduct N w / w ^ 3 -
        2 * deriv (ponomarenkoScaledOrderOneProduct N) w / w ^ 2 := by
  have hw0 : w ≠ 0 := by
    intro h
    subst w
    simp at hw
  rw [(hasDerivAt_ponomarenkoScaledOrderOneProduct hN hw).deriv]
  simp only [ponomarenkoScaledOrderOneProduct]
  field_simp [hw0]
  ring

end FastDynamo

/-!
## Cauchy bounds from the scaled order-one product

A uniform leading estimate for `Q_N` on a disk supplies derivative estimates on smaller
concentric disks, and with them value estimates for the error of the dispersion function.
-/

noncomputable section

namespace FastDynamo

open Complex Set

/-- A concentric-disk Cauchy estimate centered at an arbitrary constant. -/
theorem norm_deriv_le_div_radius_gap_of_norm_sub_const_le
    (Q : ℂ → ℂ) (c center : ℂ) {R r δ : ℝ}
    (hgap : 0 < R - r)
    (hQdiff : DifferentiableOn ℂ Q (Metric.closedBall center R))
    (hbound : ∀ z ∈ Metric.closedBall center R, ‖Q z - c‖ ≤ δ)
    {w : ℂ} (hw : w ∈ Metric.closedBall center r) :
    ‖deriv Q w‖ ≤ δ / (R - r) := by
  have hwDist : dist w center ≤ r := by
    simpa [Metric.mem_closedBall] using hw
  have houter : Metric.closedBall w (R - r) ⊆ Metric.closedBall center R := by
    intro z hz
    rw [Metric.mem_closedBall] at hz ⊢
    calc
      dist z center ≤ dist z w + dist w center := dist_triangle _ _ _
      _ ≤ (R - r) + r := add_le_add hz hwDist
      _ = R := by ring
  let F : ℂ → ℂ := fun z ↦ Q z - c
  have hdiffClosed : DifferentiableOn ℂ F (Metric.closedBall w (R - r)) := by
    intro z hz
    exact ((hQdiff z (houter hz)).mono houter).sub
      (differentiableWithinAt_const (c := c))
  have hdc : DiffContOnCl ℂ F (Metric.ball w (R - r)) :=
    DiffContOnCl.mk_ball
      (hdiffClosed.mono Metric.ball_subset_closedBall)
      hdiffClosed.continuousOn
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    hgap hdc
    (fun z hz ↦ hbound z (houter (Metric.sphere_subset_closedBall hz)))
  have hderiv : deriv F w = deriv Q w := by
    dsimp [F]
    rw [deriv_sub_const]
  simpa [hderiv] using hcauchy

/-- Pointwise norm estimate supplied by the exact order-one-product error
identity when `1 ≤ ‖w‖`. -/
theorem norm_error_le_two_mul_add_of_order_one_product_identity
    (Q E : ℂ → ℂ) {δ η : ℝ} {w : ℂ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hwNorm : 1 ≤ ‖w‖)
    (hQval : ‖Q w - (1 / 2 : ℂ)‖ ≤ δ)
    (hQderiv : ‖deriv Q w‖ ≤ η)
    (hidentity : E w =
      2 * (Q w - (1 / 2 : ℂ)) / w ^ 3 - 2 * deriv Q w / w ^ 2) :
    ‖E w‖ ≤ 2 * δ + 2 * η := by
  rw [hidentity]
  calc
    ‖2 * (Q w - (1 / 2 : ℂ)) / w ^ 3 - 2 * deriv Q w / w ^ 2‖
        ≤ ‖2 * (Q w - (1 / 2 : ℂ)) / w ^ 3‖ +
          ‖2 * deriv Q w / w ^ 2‖ := norm_sub_le _ _
    _ = 2 * ‖Q w - (1 / 2 : ℂ)‖ / ‖w‖ ^ 3 +
          2 * ‖deriv Q w‖ / ‖w‖ ^ 2 := by
      simp only [norm_div, norm_mul, norm_ofNat, norm_pow]
    _ ≤ 2 * δ / ‖w‖ ^ 3 + 2 * η / ‖w‖ ^ 2 := by
      gcongr
    _ ≤ 2 * δ + 2 * η := by
      exact add_le_add
        (div_le_self (mul_nonneg (by norm_num) hδ) (one_le_pow₀ hwNorm))
        (div_le_self (mul_nonneg (by norm_num) hη) (one_le_pow₀ hwNorm))

end FastDynamo
