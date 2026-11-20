/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.GlobalParameterChoiceConcrete

/-!
# Explicit witnesses of Theorem 1.2 at the parameter chain

This module names the velocity, the diffusivity threshold and the growth floor of Theorem 1.2
at the parameter chain of `Global/GlobalParameterChoiceConcrete.lean`.
`Global/MainTheoremWitnesses.lean` takes them over verbatim as `mainVelocity`, `mainEps0` and
`mainGrowthFloor`, so these are *the* witnesses of the theorem:

* `chainVelocity` — the global velocity `u = sum_n (u_n^loc + u_n^ax)` of `eq:global-u`
  at the chosen `(q, tau, K_0)`;
* `chainEps0` — the diffusivity threshold `eps_0 = delta_+/K_0²` of §3.2;
* `chainGrowthFloor` — the growth floor `g_* = min_{cG} Re zeta = Re(centre) - radius` of the
  two-component seed contour (`eq:spectral-gap`).

The seed runs at `k_* = 1` (so `N = 2 pi`) and `rho = 32`, whence `Re lambda_* ≥ 448 - 4 pi²`
and `g_* ≥ (3/4)(448 - 4 pi²) ≈ 306`.  The value `rho = 32`, the factor `3/4` and these
numerical bounds are choices of the formalisation: the paper proves
`Re lambda_* ≥ (7/16) rho² - 4 pi² > 0` for `rho` sufficiently large (proof of
`lem:jump-horizontal-mode`) and gives no numerical value of `g_*`.

`Global/GlobalSpectralTransferConcrete.lean` turns these witnesses into
`prop:global-spectral-transfer` at every matching cell — it is also where
`lem:global-contour-resolvent` is named at the witnesses — and
`Global/MainTheoremWitnesses.lean` assembles the clauses of Theorem 1.2 from it.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open GlobalSeedInterface
open HorizontalMode

/-! ## The three witnesses -/

/-- **The velocity of Theorem 1.2 at the parameter chain**: the single global velocity of
`eq:global-u`, fixed before the diffusivity. -/
def chainVelocity : TransverseRealW1Inf :=
  mainParameterChoice.velocity

/-- **The diffusivity threshold `eps_0` of Theorem 1.2 at the parameter chain** (§3.2). -/
def chainEps0 : ℝ :=
  mainParameterChoice.eps0

/-- **The growth floor `gamma_0` of Theorem 1.2 at the parameter chain**: the growth floor
`g_* = min_{cG} Re zeta` of the two-component seed contour (`eq:spectral-gap`).  It depends on
neither the diffusivity, nor the velocity, nor the sector, nor the axial shift, nor the
placement: it is a closed term of the seed alone. -/
def chainGrowthFloor : ℝ :=
  globalSeedInterface.growthFloor

/-! ## The velocity -/

/-- The velocity of Theorem 1.2 is transversally divergence-free (`lem:global-velocity`). -/
theorem chainVelocity_isTransverseDivergenceFree :
    IsTransverseDivergenceFree chainVelocity :=
  mainParameterChoice.velocity_isTransverseDivergenceFree

/-- The velocity of Theorem 1.2 is nonzero. -/
theorem chainVelocity_ne_zero : chainVelocity ≠ 0 :=
  mainParameterChoice.velocity_ne_zero

/-! ## The diffusivity threshold -/

/-- The diffusivity threshold is strictly positive. -/
theorem chainEps0_pos : 0 < chainEps0 :=
  mainParameterChoice.eps0_pos

/-- **The paper's formula for `eps_0`** (§3.2): `eps_0 = delta_+ / K_0²`, the seed's
upper rescaled-diffusivity endpoint divided by the square of the base Fourier index.  The
seed has `k_* = 1`, so the factor `k_*²` of the general formula is one. -/
theorem chainEps0_eq :
    chainEps0 =
      globalSeedInterface.parameters.deltaPlus / (mainParameterChoice.baseIndex : ℝ) ^ 2 :=
  mainParameterChoice_eps0_formula

/-- The seed's fixed integer wavenumber is `k_* = 1`, so its axial wavenumber is
`N = 2 pi`. -/
theorem globalSeedInterface_kStar : globalSeedInterface.parameters.kStar = 1 :=
  localSeedC2_kStar

/-- The seed's axial wavenumber is `N = 2 pi`, the wavenumber of the axial mode
`e^{2 pi i x_3}` of §2.1. -/
theorem globalSeedInterface_wavenumber : globalSeedInterface.parameters.wavenumber =
    2 * Real.pi :=
  localSeedC2_wavenumber

/-! ## The growth floor -/

/-- The growth floor is strictly positive (`eq:spectral-gap`). -/
theorem chainGrowthFloor_pos : 0 < chainGrowthFloor :=
  globalSeedInterface.growthFloor_pos

/-- **The growth floor, unfolded**: `gamma_0 = Re(centre of Gamma) - radius of Gamma`, the
minimum of `Re zeta` over the closed disc `cG` bounded by the seed contour. -/
theorem chainGrowthFloor_eq :
    chainGrowthFloor =
      globalSeedInterface.contour.center.re - globalSeedInterface.contour.radius :=
  rfl

/-- **`gamma_0 ≥ (3/4) Re lambda_*`**, with the certified lower bound `448 - (2 pi)²` for the
real part of the seed eigenvalue `lambda_* = kappa² - N²` at `N = 2 pi` and `rho = 32`
(`Local/LocalSeedC2Concrete.lean`).  The isolating circle of the two-component seed is placed so
that its growth floor retains three quarters of the eigenvalue's real part.  `rho = 32` and the
factor `3/4` are choices of the formalisation; the paper takes `rho` sufficiently large. -/
theorem chainGrowthFloor_ge_three_quarters :
    3 / 4 * (448 - (2 * Real.pi) ^ 2) ≤ chainGrowthFloor :=
  seedGrowthFloorBound_le_globalSeedInterface_growthFloor

/-- A purely numeric consequence: the growth floor of the parameter chain exceeds `288`.  Only
`pi ≤ 4` is used, so the numeral is crude; the sharp value of
`(3/4)(448 - 4 pi²)` is about `306`. -/
theorem chainGrowthFloor_ge_numeric : (288 : ℝ) ≤ chainGrowthFloor := by
  have h := chainGrowthFloor_ge_three_quarters
  nlinarith [Real.pi_pos, Real.pi_le_four]

end

end FastDynamo
