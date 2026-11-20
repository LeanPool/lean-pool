/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.ModifiedBesselWronskian

/-!
# Cross-normalized Ponomarenko boundary branches

This file records the denominator-free part of the radial Ponomarenko calculation.  The
order-two and order-zero solutions are cross-normalized at `r = 1`.  Their values therefore
match there without any nonvanishing assumption on an individual Bessel factor, while the
normalized derivative Wronskians give jumps `-1` and `+1`.

Only the two transverse scalar combinations and their boundary algebra are treated here.  In
particular, this module does not construct an axial component or assert Sobolev membership or a
full eigenmode.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace PonomarenkoCrossNormalizedJump

open Complex

/-! ## Cross-normalized scalar branches -/

/-- The regular order-two branch, normalized by the exterior boundary factor. -/
def plusInside (κ r : ℂ) : ℂ :=
  ModifiedBessel.K2 κ * ModifiedBessel.I2 (κ * r)

/-- The decaying order-two branch, normalized by the interior boundary factor. -/
def plusOutside (κ r : ℂ) : ℂ :=
  ModifiedBessel.I2 κ * ModifiedBessel.K2 (κ * r)

/-- The regular order-zero branch, with the sign used by the dispersion relation. -/
def minusInside (κ r : ℂ) : ℂ :=
  -ModifiedBessel.K0 κ * ModifiedBessel.I0 (κ * r)

/-- The decaying order-zero branch, with the sign used by the dispersion relation. -/
def minusOutside (κ r : ℂ) : ℂ :=
  -ModifiedBessel.I0 κ * ModifiedBessel.K0 (κ * r)

/-- Boundary value jump, with the paper convention `out - in`. -/
def boundaryValueJump (inside outside : ℂ → ℂ) : ℂ :=
  outside 1 - inside 1

/-- Boundary radial-derivative jump, with the paper convention `out - in`. -/
def boundaryDerivativeJump (inside outside : ℂ → ℂ) : ℂ :=
  deriv outside 1 - deriv inside 1

/-- The cross-normalized order-two branches have a common value at `r = 1`. -/
@[simp] theorem plus_boundaryValueJump (κ : ℂ) :
    boundaryValueJump (plusInside κ) (plusOutside κ) = 0 := by
  simp only [boundaryValueJump, plusInside, plusOutside, mul_one]
  ring

/-- The cross-normalized signed order-zero branches have a common value at `r = 1`. -/
@[simp] theorem minus_boundaryValueJump (κ : ℂ) :
    boundaryValueJump (minusInside κ) (minusOutside κ) = 0 := by
  simp only [boundaryValueJump, minusInside, minusOutside, mul_one]
  ring

/-- Multiplication by a constant has that constant as its derivative at `1`. -/
theorem κ_mul_hasDerivAt (κ : ℂ) :
    HasDerivAt (fun r : ℂ ↦ κ * r) κ 1 := by
  simpa using (hasDerivAt_id (x := (1 : ℂ))).const_mul κ

/-- A complex number with strictly positive real part is nonzero. -/
theorem κ_ne_zero {κ : ℂ} (hκ : 0 < κ.re) : κ ≠ 0 := by
  intro hzero
  subst κ
  simp at hκ

/-- Chain rule at the interface radius for the regular order-two branch `r ↦ K₂(κ) I₂(κr)`: its
derivative at `r = 1` is `K₂(κ) · I₂'(κ) · κ`. -/
private theorem hasDerivAt_plusInside_one {κ : ℂ} (hκ : 0 < κ.re) :
    HasDerivAt (plusInside κ)
      (ModifiedBessel.K2 κ * (deriv ModifiedBessel.I2 κ * κ)) 1 := by
  have hI2 : HasDerivAt ModifiedBessel.I2 (deriv ModifiedBessel.I2 κ) κ :=
    (ModifiedBessel.I2_hasDerivAt_recurrence κ (κ_ne_zero hκ)).differentiableAt.hasDerivAt
  have h := (hI2.comp_of_eq (1 : ℂ) (κ_mul_hasDerivAt κ) (by simp)).const_mul
    (ModifiedBessel.K2 κ)
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun r ↦ by
    simp only [plusInside, Function.comp_apply]

/-- Chain rule at the interface radius for the decaying order-two branch `r ↦ I₂(κ) K₂(κr)`: its
derivative at `r = 1` is `I₂(κ) · K₂'(κ) · κ`. -/
private theorem hasDerivAt_plusOutside_one {κ : ℂ} (hκ : 0 < κ.re) :
    HasDerivAt (plusOutside κ)
      (ModifiedBessel.I2 κ * (deriv ModifiedBessel.K2 κ * κ)) 1 := by
  have hK2 : HasDerivAt ModifiedBessel.K2 (deriv ModifiedBessel.K2 κ) κ :=
    (ModifiedBessel.hasDerivAt_K2 hκ).differentiableAt.hasDerivAt
  have h := (hK2.comp_of_eq (1 : ℂ) (κ_mul_hasDerivAt κ) (by simp)).const_mul
    (ModifiedBessel.I2 κ)
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun r ↦ by
    simp only [plusOutside, Function.comp_apply]

/-- Chain rule at the interface radius for the signed regular order-zero branch
`r ↦ -K₀(κ) I₀(κr)`: its derivative at `r = 1` is `-K₀(κ) · I₀'(κ) · κ`. -/
private theorem hasDerivAt_minusInside_one (κ : ℂ) :
    HasDerivAt (minusInside κ)
      (-ModifiedBessel.K0 κ * (deriv ModifiedBessel.I0 κ * κ)) 1 := by
  have hI0 : HasDerivAt ModifiedBessel.I0 (deriv ModifiedBessel.I0 κ) κ :=
    (ModifiedBessel.I0_hasDerivAt_recurrence κ).differentiableAt.hasDerivAt
  have h := (hI0.comp_of_eq (1 : ℂ) (κ_mul_hasDerivAt κ) (by simp)).const_mul
    (-ModifiedBessel.K0 κ)
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun r ↦ by
    simp only [minusInside, Function.comp_apply]

/-- Chain rule at the interface radius for the signed decaying order-zero branch
`r ↦ -I₀(κ) K₀(κr)`: its derivative at `r = 1` is `-I₀(κ) · K₀'(κ) · κ`. -/
private theorem hasDerivAt_minusOutside_one {κ : ℂ} (hκ : 0 < κ.re) :
    HasDerivAt (minusOutside κ)
      (-ModifiedBessel.I0 κ * (deriv ModifiedBessel.K0 κ * κ)) 1 := by
  have hK0 : HasDerivAt ModifiedBessel.K0 (deriv ModifiedBessel.K0 κ) κ :=
    (ModifiedBessel.hasDerivAt_K0 hκ).differentiableAt.hasDerivAt
  have h := (hK0.comp_of_eq (1 : ℂ) (κ_mul_hasDerivAt κ) (by simp)).const_mul
    (-ModifiedBessel.I0 κ)
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun r ↦ by
    simp only [minusOutside, Function.comp_apply]

/-- The order-two derivative jump is `-1`.  This is the normalized order-two Wronskian,
with no division by `I₂ κ` or `K₂ κ`. -/
theorem plus_boundaryDerivativeJump {κ : ℂ} (hκ : 0 < κ.re) :
    boundaryDerivativeJump (plusInside κ) (plusOutside κ) = -1 := by
  rw [boundaryDerivativeJump, (hasDerivAt_plusOutside_one hκ).deriv,
    (hasDerivAt_plusInside_one hκ).deriv]
  calc
    ModifiedBessel.I2 κ * (deriv ModifiedBessel.K2 κ * κ) -
          ModifiedBessel.K2 κ * (deriv ModifiedBessel.I2 κ * κ) =
        -κ * (deriv ModifiedBessel.I2 κ * ModifiedBessel.K2 κ -
          ModifiedBessel.I2 κ * deriv ModifiedBessel.K2 κ) := by ring
    _ = -κ * (1 / κ) := by
      rw [ModifiedBessel.deriv_I2_mul_K2_sub_I2_mul_deriv_K2_eq_one_div hκ]
    _ = -1 := by field_simp [κ_ne_zero hκ]

/-- The signed order-zero derivative jump is `+1`.  This is the normalized order-zero
Wronskian, again without a Bessel denominator. -/
theorem minus_boundaryDerivativeJump {κ : ℂ} (hκ : 0 < κ.re) :
    boundaryDerivativeJump (minusInside κ) (minusOutside κ) = 1 := by
  rw [boundaryDerivativeJump, (hasDerivAt_minusOutside_one hκ).deriv,
    (hasDerivAt_minusInside_one κ).deriv]
  calc
    -ModifiedBessel.I0 κ * (deriv ModifiedBessel.K0 κ * κ) -
          -ModifiedBessel.K0 κ * (deriv ModifiedBessel.I0 κ * κ) =
        κ * (deriv ModifiedBessel.I0 κ * ModifiedBessel.K0 κ -
          ModifiedBessel.I0 κ * deriv ModifiedBessel.K0 κ) := by ring
    _ = κ * (1 / κ) := by
      rw [ModifiedBessel.deriv_I0_mul_K0_sub_I0_mul_deriv_K0_eq_one_div hκ]
    _ = 1 := by field_simp [κ_ne_zero hκ]

/-! ## Radial and angular combinations -/

/-- `B_r = (B_+ + B_-)/2` on the interior branch. -/
def radialInside (κ r : ℂ) : ℂ :=
  (plusInside κ r + minusInside κ r) / 2

/-- `B_r = (B_+ + B_-)/2` on the exterior branch. -/
def radialOutside (κ r : ℂ) : ℂ :=
  (plusOutside κ r + minusOutside κ r) / 2

/-- `B_θ = (B_+ - B_-)/(2i)` on the interior branch. -/
def angularInside (κ r : ℂ) : ℂ :=
  (plusInside κ r - minusInside κ r) / (2 * I)

/-- `B_θ = (B_+ - B_-)/(2i)` on the exterior branch. -/
def angularOutside (κ r : ℂ) : ℂ :=
  (plusOutside κ r - minusOutside κ r) / (2 * I)

/-- The recombined radial branch is continuous at `r = 1`. -/
@[simp] theorem radial_boundaryValueJump (κ : ℂ) :
    boundaryValueJump (radialInside κ) (radialOutside κ) = 0 := by
  simp only [boundaryValueJump, radialInside, radialOutside, plusInside, plusOutside,
    minusInside, minusOutside, mul_one]
  ring

/-- The recombined angular branch is continuous at `r = 1`. -/
@[simp] theorem angular_boundaryValueJump (κ : ℂ) :
    boundaryValueJump (angularInside κ) (angularOutside κ) = 0 := by
  simp only [boundaryValueJump, angularInside, angularOutside, plusInside, plusOutside,
    minusInside, minusOutside, mul_one]
  ring

/-- Derivative of the interior radial profile at the interface radius `1`. -/
theorem hasDerivAt_radialInside_one {κ : ℂ} (hκ : 0 < κ.re) :
    HasDerivAt (radialInside κ)
      ((ModifiedBessel.K2 κ * (deriv ModifiedBessel.I2 κ * κ) +
        -ModifiedBessel.K0 κ * (deriv ModifiedBessel.I0 κ * κ)) / 2) 1 := by
  have h :=
    ((hasDerivAt_plusInside_one hκ).add (hasDerivAt_minusInside_one κ)).div_const 2
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun r ↦ by
    simp only [radialInside, Pi.add_apply]

/-- Derivative of the exterior radial profile at the interface radius `1`. -/
theorem hasDerivAt_radialOutside_one {κ : ℂ} (hκ : 0 < κ.re) :
    HasDerivAt (radialOutside κ)
      ((ModifiedBessel.I2 κ * (deriv ModifiedBessel.K2 κ * κ) +
        -ModifiedBessel.I0 κ * (deriv ModifiedBessel.K0 κ * κ)) / 2) 1 := by
  have h :=
    ((hasDerivAt_plusOutside_one hκ).add (hasDerivAt_minusOutside_one hκ)).div_const 2
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun r ↦ by
    simp only [radialOutside, Pi.add_apply]

/-- Derivative at the interface radius of the interior angular profile `B_θ = (B₊ - B₋)/(2i)`,
obtained from the two order-two and order-zero interior branch derivatives. -/
private theorem hasDerivAt_angularInside_one {κ : ℂ} (hκ : 0 < κ.re) :
    HasDerivAt (angularInside κ)
      ((ModifiedBessel.K2 κ * (deriv ModifiedBessel.I2 κ * κ) -
        -ModifiedBessel.K0 κ * (deriv ModifiedBessel.I0 κ * κ)) / (2 * I)) 1 := by
  have h :=
    ((hasDerivAt_plusInside_one hκ).sub (hasDerivAt_minusInside_one κ)).div_const (2 * I)
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun r ↦ by
    simp only [angularInside, Pi.sub_apply]

/-- Derivative at the interface radius of the exterior angular profile `B_θ = (B₊ - B₋)/(2i)`,
obtained from the two order-two and order-zero exterior branch derivatives. -/
private theorem hasDerivAt_angularOutside_one {κ : ℂ} (hκ : 0 < κ.re) :
    HasDerivAt (angularOutside κ)
      ((ModifiedBessel.I2 κ * (deriv ModifiedBessel.K2 κ * κ) -
        -ModifiedBessel.I0 κ * (deriv ModifiedBessel.K0 κ * κ)) / (2 * I)) 1 := by
  have h :=
    ((hasDerivAt_plusOutside_one hκ).sub (hasDerivAt_minusOutside_one hκ)).div_const
      (2 * I)
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun r ↦ by
    simp only [angularOutside, Pi.sub_apply]

/-- The radial derivative is continuous: `[B_r'] = 0`. -/
theorem radial_boundaryDerivativeJump {κ : ℂ} (hκ : 0 < κ.re) :
    boundaryDerivativeJump (radialInside κ) (radialOutside κ) = 0 := by
  have hplus := plus_boundaryDerivativeJump hκ
  have hminus := minus_boundaryDerivativeJump hκ
  rw [boundaryDerivativeJump, (hasDerivAt_radialOutside_one hκ).deriv,
    (hasDerivAt_radialInside_one hκ).deriv]
  rw [boundaryDerivativeJump, (hasDerivAt_plusOutside_one hκ).deriv,
    (hasDerivAt_plusInside_one hκ).deriv] at hplus
  rw [boundaryDerivativeJump, (hasDerivAt_minusOutside_one hκ).deriv,
    (hasDerivAt_minusInside_one κ).deriv] at hminus
  calc
    (ModifiedBessel.I2 κ * (deriv ModifiedBessel.K2 κ * κ) +
            -ModifiedBessel.I0 κ * (deriv ModifiedBessel.K0 κ * κ)) / 2 -
          (ModifiedBessel.K2 κ * (deriv ModifiedBessel.I2 κ * κ) +
            -ModifiedBessel.K0 κ * (deriv ModifiedBessel.I0 κ * κ)) / 2 =
        ((ModifiedBessel.I2 κ * (deriv ModifiedBessel.K2 κ * κ) -
            ModifiedBessel.K2 κ * (deriv ModifiedBessel.I2 κ * κ)) +
          (-ModifiedBessel.I0 κ * (deriv ModifiedBessel.K0 κ * κ) -
            -ModifiedBessel.K0 κ * (deriv ModifiedBessel.I0 κ * κ))) / 2 := by ring
    _ = ((-1 : ℂ) + 1) / 2 := by rw [hplus, hminus]
    _ = 0 := by norm_num

/-- The angular derivative has the normalized jump `[B_θ'] = i`. -/
theorem angular_boundaryDerivativeJump {κ : ℂ} (hκ : 0 < κ.re) :
    boundaryDerivativeJump (angularInside κ) (angularOutside κ) = I := by
  have hplus := plus_boundaryDerivativeJump hκ
  have hminus := minus_boundaryDerivativeJump hκ
  rw [boundaryDerivativeJump, (hasDerivAt_angularOutside_one hκ).deriv,
    (hasDerivAt_angularInside_one hκ).deriv]
  rw [boundaryDerivativeJump, (hasDerivAt_plusOutside_one hκ).deriv,
    (hasDerivAt_plusInside_one hκ).deriv] at hplus
  rw [boundaryDerivativeJump, (hasDerivAt_minusOutside_one hκ).deriv,
    (hasDerivAt_minusInside_one κ).deriv] at hminus
  calc
    (ModifiedBessel.I2 κ * (deriv ModifiedBessel.K2 κ * κ) -
            -ModifiedBessel.I0 κ * (deriv ModifiedBessel.K0 κ * κ)) / (2 * I) -
          (ModifiedBessel.K2 κ * (deriv ModifiedBessel.I2 κ * κ) -
            -ModifiedBessel.K0 κ * (deriv ModifiedBessel.I0 κ * κ)) / (2 * I) =
        ((ModifiedBessel.I2 κ * (deriv ModifiedBessel.K2 κ * κ) -
            ModifiedBessel.K2 κ * (deriv ModifiedBessel.I2 κ * κ)) -
          (-ModifiedBessel.I0 κ * (deriv ModifiedBessel.K0 κ * κ) -
            -ModifiedBessel.K0 κ * (deriv ModifiedBessel.I0 κ * κ))) / (2 * I) := by ring
    _ = ((-1 : ℂ) - 1) / (2 * I) := by rw [hplus, hminus]
    _ = I := by
      apply (div_eq_iff (by norm_num : (2 * I : ℂ) ≠ 0)).2
      rw [show I * (2 * I) = 2 * (I * I) by ring, Complex.I_mul_I]
      ring

/-! ## The radial trace and the dispersion function -/

/-- At the interface, the radial cross-normalization is minus one half of the concrete
dispersion function. -/
theorem radialInside_one_eq_neg_half_dispersion (κ : ℂ) :
    radialInside κ 1 = -ponomarenkoDispersion κ / 2 := by
  simp only [radialInside, plusInside, minusInside, mul_one,
    ponomarenkoDispersion_apply]
  ring

end PonomarenkoCrossNormalizedJump
end FastDynamo
