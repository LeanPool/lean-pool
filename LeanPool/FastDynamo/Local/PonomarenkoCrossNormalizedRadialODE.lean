/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.PonomarenkoCrossNormalizedAxial
public import LeanPool.FastDynamo.Local.PonomarenkoGaussianFactors
public import LeanPool.FastDynamo.Local.ModifiedBesselKODE

/-!
# Radial modified-Bessel equations of the transverse Ponomarenko branches

Lemma 2.1 (`lem:jump-horizontal-mode`) solves the transverse induction equation for the
`m = 1` Ponomarenko mode by reducing its two circular components to modified-Bessel
equations in the radius.  This module proves the radial equations satisfied by the four
denominator-free cross-normalized transverse branches, in a polynomial form.

The scalar layer derives the modified-Bessel equations of orders zero and two for the
first-kind functions from the exact recurrences, first at the order's own argument and then
composed with a radial scaling, the order-two statements being taken away from the removable
singularity at zero.  Combined with the second-kind equations of
`Local/ModifiedBesselKODE.lean`, this gives a vanishing polynomial residual
`radialResidual orderSq κ f r = r² f'' + r f' - (κ² r² + orderSq) f` for each of the four
transverse branches `plusInside`, `plusOutside` (order two) and `minusInside`, `minusOutside`
(order zero).  These residual identities are what
`Local/HorizontalModeSecondDerivatives.lean` uses to compute the second derivatives of the
horizontal mode.

## Contents

* Differential equations for the concrete modified-Bessel `I` functions: the second
  derivative of `I2`, its differential equation, composition with a radial scaling, and the
  resulting radial equations `I0_radial_ode`, `I2_radial_ode`.
* The polynomial radial residual `radialResidual` and its vanishing on the four transverse
  scalar branches (`plusInside_radialResidual` and its three companions).
-/

@[expose] public section

/-!
## Differential equations for the concrete modified-Bessel `I` functions

The modified-Bessel equations for the orders used by the
Ponomarenko seed.  The proofs use only the exact derivative and recurrence API
from `ModifiedBesselIRecurrence`.  The order-two statements are
made away from the removable singularity at zero, which is the natural domain
of the quotient recurrences used in their proofs.
-/

namespace FastDynamo.ModifiedBessel

open Complex

/-! ## Second derivatives -/

/-- The second derivative of `I2`, away from zero. -/
theorem deriv_I2_hasDerivAt (z : ℂ) (hz : z ≠ 0) :
    HasDerivAt (deriv I2)
      ((I0 z + I2 z) / 2 - 2 * I1 z / z + 6 * I2 z / z ^ 2) z := by
  have hquot := (I2_hasDerivAt_recurrence z hz).div (hasDerivAt_id z) hz
  have hrec := (I1_hasDerivAt z).sub (hquot.const_mul 2)
  have htarget :
      HasDerivAt (fun w : ℂ ↦ I1 w - 2 * (I2 w / w))
        ((I0 z + I2 z) / 2 - 2 * I1 z / z + 6 * I2 z / z ^ 2) z := by
    have hfun :
        (I1 - fun w : ℂ ↦ 2 * (I2 / (id : ℂ → ℂ)) w) =
          fun w : ℂ ↦ I1 w - 2 * (I2 w / w) := by
      funext w
      rfl
    rw [hfun] at hrec
    simp only [id_eq, mul_one] at hrec
    apply hrec.congr_deriv
    field_simp [hz]
    ring
  apply htarget.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hz] with w hw
  simpa [div_eq_mul_inv, mul_assoc] using deriv_I2 w hw

/-- Value form of the second derivative of `I₂` away from the origin:
`I₂'' z = (I₀ z + I₂ z)/2 - 2 I₁ z / z + 6 I₂ z / z²`. -/
theorem deriv_deriv_I2 (z : ℂ) (hz : z ≠ 0) :
    deriv (deriv I2) z =
      (I0 z + I2 z) / 2 - 2 * I1 z / z + 6 * I2 z / z ^ 2 :=
  (deriv_I2_hasDerivAt z hz).deriv

/-! ## Modified-Bessel differential equations -/

/-- The order-two modified-Bessel equation, away from zero. -/
theorem I2_ode (z : ℂ) (hz : z ≠ 0) :
    z ^ 2 * deriv (deriv I2) z + z * deriv I2 z -
      (z ^ 2 + 4) * I2 z = 0 := by
  rw [deriv_deriv_I2 z hz, deriv_I2 z hz, I1_eq_half_mul_I0_sub_I2]
  field_simp [hz]
  ring

/-! ## Composition with a radial scaling -/

/-- Chain rule for the scaled order-zero regular branch. -/
theorem I0_radial_hasDerivAt (kappa r : ℂ) :
    HasDerivAt (fun s : ℂ ↦ I0 (kappa * s))
      (kappa * I1 (kappa * r)) r := by
  have h := (I0_hasDerivAt_I1 (kappa * r)).comp_of_eq r
    (mul_variable_hasDerivAt kappa r) rfl
  exact h.congr_deriv (by ring)

/-- Value form of the radial chain rule for the order-zero branch:
`d/dr I₀(κ r) = κ I₁(κ r)`. -/
theorem deriv_I0_radial (kappa r : ℂ) :
    deriv (fun s : ℂ ↦ I0 (kappa * s)) r =
      kappa * I1 (kappa * r) :=
  (I0_radial_hasDerivAt kappa r).deriv

/-- Chain rule for the scaled order-one regular branch. -/
theorem I1_radial_hasDerivAt (kappa r : ℂ) :
    HasDerivAt (fun s : ℂ ↦ I1 (kappa * s))
      (kappa * ((I0 (kappa * r) + I2 (kappa * r)) / 2)) r := by
  have h := (I1_hasDerivAt (kappa * r)).comp_of_eq r
    (mul_variable_hasDerivAt kappa r) rfl
  exact h.congr_deriv (by ring)

/-- Chain rule for the scaled order-two regular branch, away from the
removable singularity in the recurrence formula. -/
theorem I2_radial_hasDerivAt (kappa r : ℂ) (hkr : kappa * r ≠ 0) :
    HasDerivAt (fun s : ℂ ↦ I2 (kappa * s))
      (kappa * (I1 (kappa * r) - 2 * I2 (kappa * r) / (kappa * r))) r := by
  have h := (I2_hasDerivAt_recurrence (kappa * r) hkr).comp_of_eq r
    (mul_variable_hasDerivAt kappa r) rfl
  exact h.congr_deriv (by ring)

/-- Value form of the radial chain rule for the order-two branch away from the origin:
`d/dr I₂(κ r) = κ (I₁(κ r) - 2 I₂(κ r) / (κ r))`. -/
theorem deriv_I2_radial (kappa r : ℂ) (hkr : kappa * r ≠ 0) :
    deriv (fun s : ℂ ↦ I2 (kappa * s)) r =
      kappa * (I1 (kappa * r) - 2 * I2 (kappa * r) / (kappa * r)) :=
  (I2_radial_hasDerivAt kappa r hkr).deriv

/-- The second radial derivative of the scaled order-zero branch. -/
theorem deriv_deriv_I0_radial (kappa r : ℂ) :
    deriv (deriv (fun s : ℂ ↦ I0 (kappa * s))) r =
      kappa ^ 2 * ((I0 (kappa * r) + I2 (kappa * r)) / 2) := by
  have hfun :
      deriv (fun s : ℂ ↦ I0 (kappa * s)) =
        fun s : ℂ ↦ kappa * I1 (kappa * s) :=
    funext fun s ↦ deriv_I0_radial kappa s
  rw [hfun]
  have h := (I1_radial_hasDerivAt kappa r).const_mul kappa
  exact h.deriv.trans (by ring)

/-- The second radial derivative of the scaled order-two branch. -/
theorem deriv_deriv_I2_radial (kappa r : ℂ) (hkr : kappa * r ≠ 0) :
    deriv (deriv (fun s : ℂ ↦ I2 (kappa * s))) r =
      kappa ^ 2 *
        ((I0 (kappa * r) + I2 (kappa * r)) / 2 -
          2 * I1 (kappa * r) / (kappa * r) +
          6 * I2 (kappa * r) / (kappa * r) ^ 2) := by
  have hkappa : kappa ≠ 0 := by
    intro hkappa
    apply hkr
    simp [hkappa]
  have hr : r ≠ 0 := by
    intro hr
    apply hkr
    simp [hr]
  have hsecond := (deriv_I2_hasDerivAt (kappa * r) hkr).comp_of_eq r
    (mul_variable_hasDerivAt kappa r) rfl
  have hscaled := hsecond.const_mul kappa
  calc
    deriv (deriv (fun s : ℂ ↦ I2 (kappa * s))) r =
        deriv (fun s : ℂ ↦ kappa * (deriv I2 ∘ fun t : ℂ ↦ kappa * t) s) r := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [eventually_ne_nhds hr] with s hs
      have hks : kappa * s ≠ 0 := mul_ne_zero hkappa hs
      rw [deriv_I2_radial kappa s hks]
      simp only [Function.comp_apply, deriv_I2 (kappa * s) hks]
    _ = kappa *
        (((I0 (kappa * r) + I2 (kappa * r)) / 2 -
          2 * I1 (kappa * r) / (kappa * r) +
          6 * I2 (kappa * r) / (kappa * r) ^ 2) * kappa) := hscaled.deriv
    _ = _ := by ring

/-! ## Radial modified-Bessel equations -/

/-- The scaled order-zero branch satisfies the radial modified-Bessel equation. -/
theorem I0_radial_ode (kappa r : ℂ) :
    r ^ 2 * deriv (deriv (fun s : ℂ ↦ I0 (kappa * s))) r +
        r * deriv (fun s : ℂ ↦ I0 (kappa * s)) r -
      (kappa ^ 2 * r ^ 2) * I0 (kappa * r) = 0 := by
  rw [deriv_deriv_I0_radial, deriv_I0_radial,
    I1_eq_half_mul_I0_sub_I2]
  ring

/-- The scaled order-two branch satisfies the radial modified-Bessel equation. -/
theorem I2_radial_ode (kappa r : ℂ) (hkr : kappa * r ≠ 0) :
    r ^ 2 * deriv (deriv (fun s : ℂ ↦ I2 (kappa * s))) r +
        r * deriv (fun s : ℂ ↦ I2 (kappa * s)) r -
      (kappa ^ 2 * r ^ 2 + 4) * I2 (kappa * r) = 0 := by
  rw [deriv_deriv_I2_radial kappa r hkr, deriv_I2_radial kappa r hkr]
  have h := I2_ode (kappa * r) hkr
  rw [deriv_deriv_I2 (kappa * r) hkr, deriv_I2 (kappa * r) hkr] at h
  convert h using 1
  ring

end FastDynamo.ModifiedBessel

/-!
## Radial equations for the cross-normalized Ponomarenko branches

The bulk radial equations for the four denominator-free transverse branches are verified
here.

All derivatives are complex derivatives of the displayed radial functions.  The claims remain
local algebraic statements: no Sobolev membership, polar-axis regularity, decay, or global
eigenmode is asserted.
-/

noncomputable section

namespace FastDynamo
namespace PonomarenkoCrossNormalizedRadialODE

open Complex
open PonomarenkoCrossNormalizedJump
open PonomarenkoCrossNormalizedAxial

/-! ## A polynomial radial residual -/

/-- The denominator-free radial modified-Bessel residual.

The parameter `orderSq` is the square of the Bessel order, so the three cases used below are
`0`, `1`, and `4`. -/
def radialResidual (orderSq kappa : ℂ) (f : ℂ → ℂ) (r : ℂ) : ℂ :=
  r ^ 2 * deriv (deriv f) r + r * deriv f r -
    (kappa ^ 2 * r ^ 2 + orderSq) * f r

/-- A constant scalar multiple of a radial branch has the correspondingly scaled residual. -/
theorem radialResidual_const_mul (orderSq kappa c : ℂ) (f : ℂ → ℂ) (r : ℂ) :
    radialResidual orderSq kappa (fun s ↦ c * f s) r =
      c * radialResidual orderSq kappa f r := by
  simp only [radialResidual, deriv_const_mul_field, deriv_const_mul_field']
  ring

/-! ## Transverse scalar branches -/

/-- The regular cross-normalized `B_+` branch solves the order-two equation. -/
theorem plusInside_radialResidual
    {kappa r : ℂ} (hkr : kappa * r ≠ 0) :
    radialResidual 4 kappa (plusInside kappa) r = 0 := by
  change radialResidual 4 kappa
    (fun s : ℂ ↦ ModifiedBessel.K2 kappa * ModifiedBessel.I2 (kappa * s)) r = 0
  rw [radialResidual_const_mul]
  have hbase : radialResidual 4 kappa
      (fun s : ℂ ↦ ModifiedBessel.I2 (kappa * s)) r = 0 := by
    simpa only [radialResidual] using ModifiedBessel.I2_radial_ode kappa r hkr
  rw [hbase, mul_zero]

/-- The decaying cross-normalized `B_+` branch solves the order-two equation. -/
theorem plusOutside_radialResidual
    {kappa r : ℂ} (hkr : 0 < (kappa * r).re) :
    radialResidual 4 kappa (plusOutside kappa) r = 0 := by
  change radialResidual 4 kappa
    (fun s : ℂ ↦ ModifiedBessel.I2 kappa * ModifiedBessel.K2 (kappa * s)) r = 0
  rw [radialResidual_const_mul]
  have hbase : radialResidual 4 kappa
      (fun s : ℂ ↦ ModifiedBessel.K2 (kappa * s)) r = 0 := by
    simpa only [radialResidual] using ModifiedBessel.K2_radial_ode kappa r hkr
  rw [hbase, mul_zero]

/-- The regular signed `B_-` branch solves the order-zero equation. -/
theorem minusInside_radialResidual (kappa r : ℂ) :
    radialResidual 0 kappa (minusInside kappa) r = 0 := by
  change radialResidual 0 kappa
    (fun s : ℂ ↦ -ModifiedBessel.K0 kappa * ModifiedBessel.I0 (kappa * s)) r = 0
  rw [radialResidual_const_mul]
  have hbase : radialResidual 0 kappa
      (fun s : ℂ ↦ ModifiedBessel.I0 (kappa * s)) r = 0 := by
    simpa only [radialResidual, add_zero] using ModifiedBessel.I0_radial_ode kappa r
  rw [hbase, mul_zero]

/-- The decaying signed `B_-` branch solves the order-zero equation. -/
theorem minusOutside_radialResidual
    {kappa r : ℂ} (hkr : 0 < (kappa * r).re) :
    radialResidual 0 kappa (minusOutside kappa) r = 0 := by
  change radialResidual 0 kappa
    (fun s : ℂ ↦ -ModifiedBessel.I0 kappa * ModifiedBessel.K0 (kappa * s)) r = 0
  rw [radialResidual_const_mul]
  have hbase : radialResidual 0 kappa
      (fun s : ℂ ↦ ModifiedBessel.K0 (kappa * s)) r = 0 := by
    simpa only [radialResidual, add_zero] using ModifiedBessel.K0_radial_ode kappa r hkr
  rw [hbase, mul_zero]

end PonomarenkoCrossNormalizedRadialODE
end FastDynamo
