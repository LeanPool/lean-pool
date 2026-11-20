/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.ModifiedBesselKGaussian
public import LeanPool.FastDynamo.Local.ModifiedBesselIGaussian
public import LeanPool.FastDynamo.Local.ModifiedBesselGaussianMoments
public import LeanPool.FastDynamo.Local.PonomarenkoOrderOneProduct

/-!
# Gaussian factors of the order-one Bessel product

The order-one product `Q(z) = z I₁(z) K₁(z)` of `PonomarenkoOrderOneProduct` is written
through the exponentially normalized integral factors `ponomarenkoI1Factor` and
`ponomarenkoK1Factor`, whose common leading term is the half-line Gaussian
`ponomarenkoHalfGaussian z`.  This module defines these factors and the real Gaussian majorant,
computes the squares of the half-line Gaussian and of its majorant and the modulus of the
former, and bounds the half-line Gaussian by its majorant.  These are the inputs of the
sectorised product estimate of `PonomarenkoSectorOrderOneProduct` and of
`PonomarenkoSecondOrderProduct`.  (Lemma 2.1 of the paper quotes the product expansion
`eq:bessel-product-expansion` from DLMF; the formalisation derives its estimates from such
Gaussian bounds instead.)
-/

@[expose] public section

noncomputable section

namespace FastDynamo

open Complex MeasureTheory Set Real

/-- The common half-Gaussian leading factor for the normalized `I₁` and `K₁`
integrals. -/
def ponomarenkoHalfGaussian (z : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 0, Complex.exp (-z * (x : ℂ) ^ 2 / 2)

/-- The real Gaussian majorant obtained by replacing `z` with `re z`. -/
def ponomarenkoHalfGaussianMajorant (z : ℂ) : ℝ :=
  Real.sqrt (Real.pi / (z.re / 2)) / 2

/-- The exponentially normalized integral factor for `I₁`. -/
def ponomarenkoI1Factor (z : ℂ) : ℂ :=
  (Real.pi : ℂ) * Complex.exp (-z) * ModifiedBessel.I1 z

/-- The exponentially normalized integral factor for `K₁`. -/
def ponomarenkoK1Factor (z : ℂ) : ℂ :=
  Complex.exp z * ModifiedBessel.K1 z

/-- The square of the half-line Gaussian integral is `π/(2z)`, obtained from the full-line Gaussian
by evenness of the integrand. -/
lemma ponomarenkoHalfGaussian_sq {z : ℂ} (hz : 0 < z.re) :
    ponomarenkoHalfGaussian z ^ 2 = (Real.pi : ℂ) / (2 * z) := by
  let f : ℝ → ℂ := fun x ↦ Complex.exp (-(z / 2) * (x : ℂ) ^ 2)
  have hb : 0 < (z / 2).re := by simpa using half_pos hz
  have hG : ponomarenkoHalfGaussian z = ∫ x : ℝ in Ioi 0, f x := by
    rw [ponomarenkoHalfGaussian]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp [f]
    congr 1
    ring
  have heven : (∫ x : ℝ in Iic 0, f x) = ∫ x : ℝ in Ioi 0, f x := by
    calc
      (∫ x : ℝ in Iic 0, f x) = ∫ x : ℝ in Ioi 0, f (-x) := by
        simpa [f] using (integral_comp_neg_Ioi 0 f).symm
      _ = ∫ x : ℝ in Ioi 0, f x := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x _
        simp [f]
  have hint : Integrable f := by
    simpa [f] using integrable_cexp_neg_mul_sq hb
  have hwhole : (∫ x : ℝ, f x) = 2 * ∫ x : ℝ in Ioi 0, f x := by
    rw [← integral_add_compl (s := Ioi 0) measurableSet_Ioi hint, compl_Ioi, heven]
    ring
  have hfull := integral_gaussian_sq_complex (b := z / 2) hb
  change (∫ x : ℝ, f x) ^ 2 = (Real.pi : ℂ) / (z / 2) at hfull
  rw [hwhole] at hfull
  rw [hG]
  calc
    (∫ x : ℝ in Ioi 0, f x) ^ 2 =
        (2 * ∫ x : ℝ in Ioi 0, f x) ^ 2 / 4 := by ring
    _ = ((Real.pi : ℂ) / (z / 2)) / 4 := by rw [hfull]
    _ = (Real.pi : ℂ) / (2 * z) := by
      have hz0 : z ≠ 0 := by
        intro hz0
        rw [hz0] at hz
        simp at hz
      field_simp [hz0]
      norm_num

/-- The real Gaussian majorant squares to `π/(2 Re z)`. -/
lemma ponomarenkoHalfGaussianMajorant_sq {z : ℂ} (hz : 0 < z.re) :
    ponomarenkoHalfGaussianMajorant z ^ 2 = Real.pi / (2 * z.re) := by
  rw [ponomarenkoHalfGaussianMajorant, div_pow, Real.sq_sqrt]
  · ring
  · positivity

/-- The real half-line Gaussian at `Re z` is exactly the majorant used here. -/
lemma realGaussianHalfLine_eq_ponomarenkoMajorant {z : ℂ} (hz : 0 < z.re) :
    ModifiedBessel.realGaussianHalfLine z.re =
      ponomarenkoHalfGaussianMajorant z := by
  rw [ModifiedBessel.realGaussianHalfLine_eq_sqrt hz]
  rfl

/-- The squared modulus of the half-line Gaussian integral is `π/(2‖z‖)`. -/
lemma norm_ponomarenkoHalfGaussian_sq {z : ℂ} (hz : 0 < z.re) :
    ‖ponomarenkoHalfGaussian z‖ ^ 2 = Real.pi / (2 * ‖z‖) := by
  calc
    ‖ponomarenkoHalfGaussian z‖ ^ 2 = ‖ponomarenkoHalfGaussian z ^ 2‖ := by
      rw [norm_pow]
    _ = ‖(Real.pi : ℂ) / (2 * z)‖ := by rw [ponomarenkoHalfGaussian_sq hz]
    _ = Real.pi / (2 * ‖z‖) := by
      simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        norm_mul]
      norm_num

/-- The half-line Gaussian integral is dominated in modulus by its real majorant at `Re z`, since
`Re z ≤ ‖z‖`. -/
lemma norm_ponomarenkoHalfGaussian_le_majorant {z : ℂ} (hz : 0 < z.re) :
    ‖ponomarenkoHalfGaussian z‖ ≤ ponomarenkoHalfGaussianMajorant z := by
  have hzNorm : 0 < ‖z‖ := by
    apply norm_pos_iff.mpr
    intro hz0
    subst z
    simp at hz
  have hleft0 : 0 ≤ ‖ponomarenkoHalfGaussian z‖ := norm_nonneg _
  have hright0 : 0 ≤ ponomarenkoHalfGaussianMajorant z := by
    rw [ponomarenkoHalfGaussianMajorant]
    positivity
  rw [← (sq_le_sq₀ hleft0 hright0)]
  rw [norm_ponomarenkoHalfGaussian_sq hz,
    ponomarenkoHalfGaussianMajorant_sq hz]
  rw [div_le_div_iff₀ (show 0 < 2 * ‖z‖ by positivity)
    (show 0 < 2 * z.re by positivity)]
  have hre := Complex.re_le_norm z
  nlinarith [Real.pi_pos]

end FastDynamo
