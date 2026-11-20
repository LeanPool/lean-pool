/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.PonomarenkoCrossNormalizedAxial
public import LeanPool.FastDynamo.Local.PonomarenkoGaussianFactors

/-!
# Free-`Ω` interface data

In the paper the angular speed `Ω` of the Ponomarenko jump flow
`V⁰ = 1_{r<1}(Ω r e_θ + U e₃)` (`eq:jump-flow`), `U = -Ω/(2π)`, is an *output* of the
construction: in the proof of `lem:jump-horizontal-mode` the radial parameter `κ` is chosen
first so that `Re 𝒟(κ) = 0`, and then `Ω := -2/Im 𝒟(κ)`.

This module keeps `Ω` a free parameter, with axial wavenumber `N` (the paper's case is
`N = 2π`).  It records

* the transverse transmission conditions `[B_r] = [B_θ] = [B_r'] = 0`, `[B_θ'] = Ω B_r(1)` of
  `eq:transmission-horizontal` at a free `Ω`;
* the equivalence of the dispersion relation `Ω 𝒟(κ) = -2i` (`eq:dispersion`) with the
  denominator-free boundary identity `Ω B_r(1) = i`;
* the certificate `CertifiedInterfaceData N Ω κ` of a root of the dispersion relation at a
  free `Ω`;
* the axial speed `U = -Ω/N` and its helical cancellation `Ω + N U = 0`.

No differential equation, Sobolev membership or eigenmode is asserted here: only scalar trace
and derivative data at `r = 1`.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace PonomarenkoFreeOmegaInterface

open Complex
open PonomarenkoCrossNormalizedJump

/-! ## The transverse transmission conditions at a free angular speed -/

/-- The transverse transmission conditions at `r = 1` with a free angular speed `Ω`:
`[B_r] = 0`, `[B_θ] = 0`, `[B_r'] = 0` and `[B_θ'] = Ω B_r(1)`, in the paper's convention
`[f] = f_out - f_in` (`eq:transmission-horizontal`).

There is no axial branch: the horizontal operator `A_w` of `eq:horizontal-induction` acts on
two-component fields. -/
structure TransverseInterfaceLaws (Ω κ : ℂ) : Prop where
  radial_value_jump :
    boundaryValueJump (radialInside κ) (radialOutside κ) = 0
  angular_value_jump :
    boundaryValueJump (angularInside κ) (angularOutside κ) = 0
  radial_derivative_jump :
    boundaryDerivativeJump (radialInside κ) (radialOutside κ) = 0
  angular_derivative_jump :
    boundaryDerivativeJump (angularInside κ) (angularOutside κ) =
      Ω * radialInside κ 1

/-- The dispersion relation `Ω 𝒟(κ) = -2i` (`eq:dispersion`) is exactly the denominator-free
boundary identity `Ω B_r(1) = i`, because the cross-normalized radial trace is
`B_r(1) = -𝒟(κ)/2`. -/
theorem mul_radialInside_one_eq_I_iff_dispersion (Ω κ : ℂ) :
    Ω * radialInside κ 1 = I ↔ Ω * ponomarenkoDispersion κ = -2 * I := by
  rw [radialInside_one_eq_neg_half_dispersion]
  constructor
  · intro h
    linear_combination (-2 : ℂ) * h
  · intro h
    linear_combination (-1 / 2 : ℂ) * h

/-- A solution of the dispersion relation has a nonzero cross-normalized radial boundary
trace, so the transmission source does not degenerate. -/
theorem radialInside_one_ne_zero_of_dispersion {Ω κ : ℂ}
    (hdisp : Ω * ponomarenkoDispersion κ = -2 * I) :
    radialInside κ 1 ≠ 0 := by
  intro hzero
  have h := (mul_radialInside_one_eq_I_iff_dispersion Ω κ).2 hdisp
  rw [hzero, mul_zero] at h
  exact Complex.I_ne_zero h.symm

/-- At every right-half-plane `κ` satisfying the dispersion relation `Ω 𝒟(κ) = -2i`, the four
free-`Ω` transverse transmission conditions hold. -/
theorem transverseInterfaceLaws_of_dispersion {Ω κ : ℂ} (hκ : 0 < κ.re)
    (hdisp : Ω * ponomarenkoDispersion κ = -2 * I) :
    TransverseInterfaceLaws Ω κ := by
  refine ⟨radial_boundaryValueJump κ, angular_boundaryValueJump κ,
    radial_boundaryDerivativeJump hκ, ?_⟩
  rw [angular_boundaryDerivativeJump hκ]
  exact ((mul_radialInside_one_eq_I_iff_dispersion Ω κ).2 hdisp).symm

/-! ## The axial speed -/

/-- The axial speed `U = -Ω/N` of the jump flow (`eq:jump-flow`, where `N = 2π`). -/
def jumpAxialSpeed (N Ω : ℝ) : ℝ :=
  -Ω / N

/-- The cancellation `N U = -Ω` that makes the transport-stretching term `-i(jΩ + N U)b`
vanish at the angular index `j = 1` (proof of `lem:jump-horizontal-mode`, where `N = 2π`). -/
theorem scale_mul_jumpAxialSpeed {N Ω : ℝ} (hN : N ≠ 0) :
    N * jumpAxialSpeed N Ω = -Ω := by
  have hrewrite : N * (-Ω / N) = (N / N) * (-Ω) := by
    ring
  rw [jumpAxialSpeed, hrewrite, div_self hN, one_mul]

/-! ## The free-`Ω` certificate -/

/-- All scalar data carried by a certified free-`Ω` interface root of
`lem:jump-horizontal-mode`.

The parameters are the axial wavenumber `N`, the angular speed `Ω` of the jump flow
`V⁰ = 1_{r<1}(Ω r e_θ + U e₃)` with `U = -Ω/N`, and the radial parameter `κ`, related to the
eigenvalue by `κ² = N² + λ_*`.  The angular speed is free and `κ` is not tied to `N`. -/
structure CertifiedInterfaceData (N Ω : ℝ) (κ : ℂ) : Prop where
  scale_pos :
    0 < N
  omega_pos :
    0 < Ω
  dispersion :
    (Ω : ℂ) * ponomarenkoDispersion κ = -2 * I
  kappa_re_pos :
    0 < κ.re
  spectral_growth :
    0 < ((κ ^ 2 - (N : ℂ) ^ 2).re)
  I0_ne_zero :
    ModifiedBessel.I0 κ ≠ 0
  I1_ne_zero :
    ModifiedBessel.I1 κ ≠ 0
  I2_ne_zero :
    ModifiedBessel.I2 κ ≠ 0
  K0_ne_zero :
    ModifiedBessel.K0 κ ≠ 0
  K1_ne_zero :
    ModifiedBessel.K1 κ ≠ 0
  K2_ne_zero :
    ModifiedBessel.K2 κ ≠ 0
  radial_boundary_ne_zero :
    radialInside κ 1 ≠ 0
  interface_laws :
    TransverseInterfaceLaws (Ω : ℂ) κ

end PonomarenkoFreeOmegaInterface
end FastDynamo
