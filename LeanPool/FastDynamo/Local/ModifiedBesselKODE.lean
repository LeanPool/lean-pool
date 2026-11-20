/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.ModifiedBessel
public import LeanPool.FastDynamo.Local.ModifiedBesselKRecurrence

/-!
# Differential equations for the integral modified-Bessel K functions

This file derives the second derivatives and the polynomial modified-Bessel equations for
`K0`, `K1`, and `K2` on the open right half-plane.  The proofs use only the first-derivative
recurrences established for the integral definitions.  Writing the equations in
polynomial form avoids introducing any extra denominator into the public ODE statements.
-/

@[expose] public section

noncomputable section

namespace FastDynamo.ModifiedBessel

open Complex Set Filter

/-- The open right half-plane `{z : Re z > 0}`, the natural domain of the integral second-kind
functions, is open. -/
private lemma isOpen_rightHalfPlane : IsOpen {z : ℂ | 0 < z.re} :=
  continuous_re.isOpen_preimage _ isOpen_Ioi

/-- The usual order-two first-derivative recurrence, expressed using `K1`. -/
theorem hasDerivAt_K2_eq_neg_K1_sub_two_div {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt K2 (-K1 z - 2 / z * K2 z) z := by
  apply (hasDerivAt_K2_eq_K0_sub_K2 hz).congr_deriv
  rw [K1_eq_z_div_two_mul_K2_sub_K0 hz]
  ring

/-- The second derivative of `K0` on the open right half-plane. -/
theorem hasDerivAt_deriv_K0 {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (deriv K0) ((K0 z + K2 z) / 2) z := by
  have h := (hasDerivAt_K1_eq_neg_K0_add_K2 hz).neg
  apply (h.congr_deriv (by ring)).congr_of_eventuallyEq
  filter_upwards [isOpen_rightHalfPlane.mem_nhds hz] with w hw
  exact (hasDerivAt_K0_eq_neg_K1 hw).deriv

/-- The second derivative of `K2` on the open right half-plane. -/
theorem hasDerivAt_deriv_K2 {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (deriv K2) (K2 z + K1 z / z + 6 * K2 z / z ^ 2) z := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp at hz
  have hcoef : HasDerivAt (fun w : ℂ ↦ 2 / w) (-2 / z ^ 2) z := by
    apply ((hasDerivAt_const z (2 : ℂ)).div (hasDerivAt_id z) hz0).congr_deriv
    simp only [id_eq]
    field_simp [hz0]
    ring
  have h := (hasDerivAt_K1_eq_neg_K0_add_K2 hz).neg.sub
    (hcoef.mul (hasDerivAt_K2_eq_neg_K1_sub_two_div hz))
  have hderiv :
      -(-(K0 z + K2 z) / 2) -
          ((-2 / z ^ 2) * K2 z + (2 / z) * (-K1 z - 2 / z * K2 z)) =
        K2 z + K1 z / z + 6 * K2 z / z ^ 2 := by
    rw [K1_eq_z_div_two_mul_K2_sub_K0 hz]
    field_simp [hz0]
    ring
  apply (h.congr_deriv hderiv).congr_of_eventuallyEq
  filter_upwards [isOpen_rightHalfPlane.mem_nhds hz] with w hw
  exact (hasDerivAt_K2_eq_neg_K1_sub_two_div hw).deriv

/-- The order-zero modified-Bessel differential equation on the open right half-plane. -/
theorem K0_differential_equation {z : ℂ} (hz : 0 < z.re) :
    z ^ 2 * deriv (deriv K0) z + z * deriv K0 z - z ^ 2 * K0 z = 0 := by
  rw [(hasDerivAt_deriv_K0 hz).deriv, (hasDerivAt_K0_eq_neg_K1 hz).deriv,
    K1_eq_z_div_two_mul_K2_sub_K0 hz]
  ring

/-- The order-two modified-Bessel differential equation on the open right half-plane. -/
theorem K2_differential_equation {z : ℂ} (hz : 0 < z.re) :
    z ^ 2 * deriv (deriv K2) z + z * deriv K2 z - (z ^ 2 + 4) * K2 z = 0 := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp at hz
  rw [(hasDerivAt_deriv_K2 hz).deriv,
    (hasDerivAt_K2_eq_neg_K1_sub_two_div hz).deriv]
  field_simp [hz0]
  ring

/-! ## Composition with a radial scaling -/

/-- If the scaled argument `κ r` lies in the open right half-plane, so does `κ s` for all `s`
near `r`; this is what lets the second-kind recurrences be differentiated once more along the
radial variable. -/
private theorem eventually_K_radial_mem_rightHalfPlane {kappa r : ℂ}
    (hkr : 0 < (kappa * r).re) :
    ∀ᶠ s in nhds r, 0 < (kappa * s).re := by
  have hscale : Continuous (fun s : ℂ ↦ kappa * s) :=
    continuous_const.mul continuous_id
  have hopen : IsOpen {s : ℂ | 0 < (kappa * s).re} :=
    (continuous_re.comp hscale).isOpen_preimage _ isOpen_Ioi
  exact hopen.mem_nhds hkr

/-- Chain rule for the scaled order-zero exterior branch. -/
theorem K0_radial_hasDerivAt (kappa r : ℂ) (hkr : 0 < (kappa * r).re) :
    HasDerivAt (fun s : ℂ ↦ K0 (kappa * s))
      (kappa * (-K1 (kappa * r))) r := by
  have h := (hasDerivAt_K0_eq_neg_K1 hkr).comp_of_eq r
    (mul_variable_hasDerivAt kappa r) rfl
  exact h.congr_deriv (by ring)

/-- Value form of the radial chain rule for the order-zero exterior branch:
`d/dr K₀(κ r) = κ (-K₁(κ r))`. -/
theorem deriv_K0_radial (kappa r : ℂ) (hkr : 0 < (kappa * r).re) :
    deriv (fun s : ℂ ↦ K0 (kappa * s)) r =
      kappa * (-K1 (kappa * r)) :=
  (K0_radial_hasDerivAt kappa r hkr).deriv

/-- Chain rule for the scaled order-one exterior branch. -/
theorem K1_radial_hasDerivAt (kappa r : ℂ) (hkr : 0 < (kappa * r).re) :
    HasDerivAt (fun s : ℂ ↦ K1 (kappa * s))
      (kappa * (-(K0 (kappa * r) + K2 (kappa * r)) / 2)) r := by
  have h := (hasDerivAt_K1_eq_neg_K0_add_K2 hkr).comp_of_eq r
    (mul_variable_hasDerivAt kappa r) rfl
  exact h.congr_deriv (by ring)

/-- Chain rule for the scaled order-two exterior branch. -/
theorem K2_radial_hasDerivAt (kappa r : ℂ) (hkr : 0 < (kappa * r).re) :
    HasDerivAt (fun s : ℂ ↦ K2 (kappa * s))
      (kappa * (-K1 (kappa * r) - 2 / (kappa * r) * K2 (kappa * r))) r := by
  have h := (hasDerivAt_K2_eq_neg_K1_sub_two_div hkr).comp_of_eq r
    (mul_variable_hasDerivAt kappa r) rfl
  exact h.congr_deriv (by ring)

/-- Value form of the radial chain rule for the order-two exterior branch:
`d/dr K₂(κ r) = κ (-K₁(κ r) - (2/(κ r)) K₂(κ r))`. -/
theorem deriv_K2_radial (kappa r : ℂ) (hkr : 0 < (kappa * r).re) :
    deriv (fun s : ℂ ↦ K2 (kappa * s)) r =
      kappa * (-K1 (kappa * r) - 2 / (kappa * r) * K2 (kappa * r)) :=
  (K2_radial_hasDerivAt kappa r hkr).deriv

/-- The second radial derivative of the scaled order-zero exterior branch. -/
theorem deriv_deriv_K0_radial (kappa r : ℂ) (hkr : 0 < (kappa * r).re) :
    deriv (deriv (fun s : ℂ ↦ K0 (kappa * s))) r =
      kappa ^ 2 * ((K0 (kappa * r) + K2 (kappa * r)) / 2) := by
  have hsecond := (hasDerivAt_deriv_K0 hkr).comp_of_eq r
    (mul_variable_hasDerivAt kappa r) rfl
  have hscaled := hsecond.const_mul kappa
  have heq :
      deriv (fun s : ℂ ↦ K0 (kappa * s)) =ᶠ[nhds r]
        fun s : ℂ ↦ kappa * (deriv K0 ∘ fun t : ℂ ↦ kappa * t) s := by
    filter_upwards [eventually_K_radial_mem_rightHalfPlane hkr] with s hs
    change deriv (fun t : ℂ ↦ K0 (kappa * t)) s = kappa * deriv K0 (kappa * s)
    rw [deriv_K0_radial kappa s hs, (hasDerivAt_K0_eq_neg_K1 hs).deriv]
  exact (hscaled.congr_of_eventuallyEq heq).deriv.trans (by ring)

/-- The second radial derivative of the scaled order-two exterior branch. -/
theorem deriv_deriv_K2_radial (kappa r : ℂ) (hkr : 0 < (kappa * r).re) :
    deriv (deriv (fun s : ℂ ↦ K2 (kappa * s))) r =
      kappa ^ 2 *
        (K2 (kappa * r) + K1 (kappa * r) / (kappa * r) +
          6 * K2 (kappa * r) / (kappa * r) ^ 2) := by
  have hsecond := (hasDerivAt_deriv_K2 hkr).comp_of_eq r
    (mul_variable_hasDerivAt kappa r) rfl
  have hscaled := hsecond.const_mul kappa
  have heq :
      deriv (fun s : ℂ ↦ K2 (kappa * s)) =ᶠ[nhds r]
        fun s : ℂ ↦ kappa * (deriv K2 ∘ fun t : ℂ ↦ kappa * t) s := by
    filter_upwards [eventually_K_radial_mem_rightHalfPlane hkr] with s hs
    change deriv (fun t : ℂ ↦ K2 (kappa * t)) s = kappa * deriv K2 (kappa * s)
    rw [deriv_K2_radial kappa s hs,
      (hasDerivAt_K2_eq_neg_K1_sub_two_div hs).deriv]
  exact (hscaled.congr_of_eventuallyEq heq).deriv.trans (by ring)

/-! ## Radial modified-Bessel equations -/

/-- The scaled order-zero exterior branch satisfies the radial modified-Bessel equation. -/
theorem K0_radial_ode (kappa r : ℂ) (hkr : 0 < (kappa * r).re) :
    r ^ 2 * deriv (deriv (fun s : ℂ ↦ K0 (kappa * s))) r +
        r * deriv (fun s : ℂ ↦ K0 (kappa * s)) r -
      (kappa ^ 2 * r ^ 2) * K0 (kappa * r) = 0 := by
  calc
    r ^ 2 * deriv (deriv (fun s : ℂ ↦ K0 (kappa * s))) r +
          r * deriv (fun s : ℂ ↦ K0 (kappa * s)) r -
        (kappa ^ 2 * r ^ 2) * K0 (kappa * r) =
        (kappa * r) ^ 2 * deriv (deriv K0) (kappa * r) +
          (kappa * r) * deriv K0 (kappa * r) -
          (kappa * r) ^ 2 * K0 (kappa * r) := by
      rw [deriv_deriv_K0_radial kappa r hkr, deriv_K0_radial kappa r hkr,
        (hasDerivAt_deriv_K0 hkr).deriv, (hasDerivAt_K0_eq_neg_K1 hkr).deriv]
      ring
    _ = 0 := K0_differential_equation hkr

/-- The scaled order-two exterior branch satisfies the radial modified-Bessel equation. -/
theorem K2_radial_ode (kappa r : ℂ) (hkr : 0 < (kappa * r).re) :
    r ^ 2 * deriv (deriv (fun s : ℂ ↦ K2 (kappa * s))) r +
        r * deriv (fun s : ℂ ↦ K2 (kappa * s)) r -
      (kappa ^ 2 * r ^ 2 + 4) * K2 (kappa * r) = 0 := by
  calc
    r ^ 2 * deriv (deriv (fun s : ℂ ↦ K2 (kappa * s))) r +
          r * deriv (fun s : ℂ ↦ K2 (kappa * s)) r -
        (kappa ^ 2 * r ^ 2 + 4) * K2 (kappa * r) =
        (kappa * r) ^ 2 * deriv (deriv K2) (kappa * r) +
          (kappa * r) * deriv K2 (kappa * r) -
          ((kappa * r) ^ 2 + 4) * K2 (kappa * r) := by
      rw [deriv_deriv_K2_radial kappa r hkr, deriv_K2_radial kappa r hkr,
        (hasDerivAt_deriv_K2 hkr).deriv,
        (hasDerivAt_K2_eq_neg_K1_sub_two_div hkr).deriv]
      ring
    _ = 0 := K2_differential_equation hkr

end FastDynamo.ModifiedBessel
