/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Main
public import LeanPool.FastDynamo.Global.GlobalSpectralTransferConcrete

/-!
# Explicit witnesses for the main theorem

`FastDynamo/MainTheorem.lean` proves `MainReducedTarget` and `MainPhysicalConclusion`, both of
which hide the velocity `u`, the diffusivity threshold `ε₀` and the growth floor `γ₀` behind
existential quantifiers, even though the proof produces *closed terms* for all three.  This
module names those terms and proves the clauses of Theorem 1.2 at the named witnesses, so that
downstream statements can talk about *the* velocity of Theorem 1.2 rather than about *some*
velocity.

## The witnesses

* `mainVelocity` — the global velocity `u = Σ_n (u_n^loc + u_n^ax)` of `eq:global-u`
  at the parameter chain
  `HorizontalMode.mainParameterChoice` of `Global/GlobalParameterChoiceConcrete.lean`;
* `mainEps0` — the diffusivity threshold `ε₀ = δ₊/K₀²` (§3.2);
* `mainGrowthFloor` — the growth floor `γ₀ = g_* = min_{ζ ∈ 𝒢} Re ζ` of the two-component seed
  contour (`eq:spectral-gap`), a closed term of the seed alone.

By definition, the three are `chainVelocity`, `chainEps0` and `chainGrowthFloor` of
`Global/ParameterChainWitnesses.lean`.

## The headline statements

* `mainReducedClauses_holds : MainReducedClauses mainVelocity mainEps0 mainGrowthFloor`, proved
  through `prop:global-spectral-transfer` at the parameter chain
  (`Global/GlobalSpectralTransferConcrete.lean`);
* `mainPhysicalClauses_holds : MainPhysicalClauses mainVelocity mainEps0 mainGrowthFloor`;
* `main_theorem_explicit_witnesses`, the conjunction of the four side conditions with the
  physical clauses.

## How explicit are the three numbers?

* `mainEps0` **is** a formula: `mainEps0_eq` states `ε₀ = δ₊/K₀²`, the seed's upper
  rescaled-diffusivity endpoint divided by the square of the base Fourier index of the chosen
  chain.  The factor `k_*²` of the general formula is `1` because the seed runs at
  `k_* = 1` (`seed_kStar`), i.e. at `N = 2π`.
* `mainGrowthFloor` is the seed contour's growth floor `Re(centre Γ) − radius Γ`
  (`mainGrowthFloor_eq`), i.e. the minimum of `Re ζ` over the closed disc `𝒢` bounded by `Γ`.
  Quantitatively `mainGrowthFloor_ge_three_quarters` gives `γ₀ ≥ (3/4)(448 − 4π²)` — three
  quarters of the certified lower bound for `Re λ_*` at `N = 2π` and `ϱ = 32` — and
  `mainGrowthFloor_ge_numeric` the crude numeral `γ₀ ≥ 288`.  These numerals are choices of
  the formalisation: the paper proves `Re λ_* ≥ (7/16)ϱ² − 4π² > 0` for `ϱ` sufficiently large
  (proof of `lem:jump-horizontal-mode`), fixes no value of `ϱ`, and gives no numerical value
  of `γ₀ = g_*`; nor does it fix the factor `3/4`.
* `mainVelocity` is the global velocity of the chain; its concrete cell-by-cell description
  lives in the torus velocity modules, and `FastDynamo/MainTheoremStrengthened.lean` records
  its representatives and their regularity.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open GlobalSeedInterface
open HorizontalMode

/-! ## The three witnesses of Theorem 1.2 -/

/-- **The velocity of Theorem 1.2 of the paper**: the single global velocity of `eq:global-u`
pinned by the parameter chain, chosen before the diffusivity. -/
def mainVelocity : TransverseRealW1Inf :=
  chainVelocity

/-- **The diffusivity threshold `ε₀` of Theorem 1.2 of the paper** (§3.2). -/
def mainEps0 : ℝ :=
  chainEps0

/-- **The growth floor `γ₀` of Theorem 1.2 of the paper**: the growth floor `g_*` of the
two-component local seed's contour.  It depends on neither the diffusivity, nor the velocity,
nor the sector, nor the axial shift, nor the placement — it is a closed term of the seed
alone. -/
def mainGrowthFloor : ℝ :=
  chainGrowthFloor

/-! ## The velocity -/

/-- The velocity of Theorem 1.2 is transversally divergence-free (`lem:global-velocity`). -/
theorem mainVelocity_isTransverseDivergenceFree :
    IsTransverseDivergenceFree mainVelocity :=
  chainVelocity_isTransverseDivergenceFree

/-- The velocity of Theorem 1.2 is nonzero. -/
theorem mainVelocity_ne_zero : mainVelocity ≠ 0 :=
  chainVelocity_ne_zero

/-! ## The diffusivity threshold -/

/-- The diffusivity threshold is strictly positive. -/
theorem mainEps0_pos : 0 < mainEps0 :=
  chainEps0_pos

/-- **The paper's formula for `ε₀`** (§3.2): `ε₀ = δ₊ / K₀²`, with `δ₊` the
seed's upper rescaled-diffusivity endpoint and `K₀` the base Fourier index of the chain. -/
theorem mainEps0_eq :
    mainEps0 =
      globalSeedInterface.parameters.deltaPlus / (mainParameterChoice.baseIndex : ℝ) ^ 2 :=
  chainEps0_eq

/-- The seed's fixed integer wavenumber is `k_* = 1`; this is why the factor `k_*²`
disappears from `mainEps0_eq`. -/
theorem seed_kStar : globalSeedInterface.parameters.kStar = 1 :=
  globalSeedInterface_kStar

/-- The seed's axial wavenumber is `N = 2π`, the wavenumber of the axial mode `e^{2πix₃}`
of §2.1. -/
theorem seed_wavenumber : globalSeedInterface.parameters.wavenumber = 2 * Real.pi :=
  globalSeedInterface_wavenumber

/-! ## The growth floor -/

/-- The growth floor is strictly positive (`eq:spectral-gap`). -/
theorem mainGrowthFloor_pos : 0 < mainGrowthFloor :=
  chainGrowthFloor_pos

/-- **The growth floor, unfolded**: `γ₀ = Re(centre Γ) − radius Γ`, the minimum of `Re ζ` over
the closed disc `𝒢` bounded by the seed's isolating circle. -/
theorem mainGrowthFloor_eq :
    mainGrowthFloor =
      globalSeedInterface.contour.center.re - globalSeedInterface.contour.radius :=
  chainGrowthFloor_eq

/-- **`γ₀ ≥ (3/4) Re λ_*`** with the certified lower bound `448 − (2π)²` for the real part of
the seed eigenvalue `λ_* = κ² − N²` at `N = 2π` and `ϱ = 32`: the isolating circle is placed so
that its growth floor retains three quarters of the eigenvalue's real part.  The value `ϱ = 32`
and the factor `3/4` are choices of the formalisation; the paper takes `ϱ` sufficiently large. -/
theorem mainGrowthFloor_ge_three_quarters :
    3 / 4 * (448 - (2 * Real.pi) ^ 2) ≤ mainGrowthFloor :=
  chainGrowthFloor_ge_three_quarters

/-- A purely numeric consequence: the growth floor `γ₀` of Theorem 1.2 exceeds `288`.  Only
`π ≤ 4` is used, so the numeral is crude; the sharp value of `(3/4)(448 − 4π²)` is
about `306`. -/
theorem mainGrowthFloor_ge_numeric : (288 : ℝ) ≤ mainGrowthFloor :=
  chainGrowthFloor_ge_numeric

/-! ## The clauses of Theorem 1.2 at the witnesses -/

/-- **The reduced clauses at the explicit witnesses.**  For every `0 < ε ≤ mainEps0` the reduced
induction operator at `mainVelocity` has, in the nonzero axial sector of the cell matched to
`ε`, an eigenpair whose eigenvalue has real part at least `mainGrowthFloor`.

This is `prop:global-spectral-transfer` at the parameter chain: the contour
resolvent of `lem:global-contour-resolvent`, the nonvanishing Riesz projection of
`lem:global-riesz-nonzero` at the placed seed witness, the eigenvalue extraction, and the finish
bridge `lem:axial-recovery` that turns the two-component eigenfunction into the three-component
amplitude the theorem states. -/
theorem mainReducedClauses_holds :
    MainReducedClauses mainVelocity mainEps0 mainGrowthFloor := by
  intro epsilon hpos hle
  obtain ⟨lambda, b, hfloor, hreduced, -, -, -⟩ :=
    exists_growing_reducedInduction_eigenpair_matchingCell hpos
      (mainParameterChoice.matchingCell hpos hle)
  exact ⟨mainParameterChoice.fourierIndex (mainParameterChoice.matchingCell hpos hle),
    lambda, b,
    mainParameterChoice.fourierIndex_ne_zero (mainParameterChoice.matchingCell hpos hle),
    hfloor, hreduced⟩

/-- **The physical clauses of Theorem 1.2 of the paper at the explicit witnesses.**  Every clause
of `MainPhysicalClauses` — the auxiliary and curl-form eigenmodes, the divergence-free property,
the nonvanishing real datum, the exact norm law and the uniform growth bound, and the
strong-solution property of the explicit real curve — holds at `mainVelocity`, `mainEps0` and
`mainGrowthFloor`. -/
theorem mainPhysicalClauses_holds :
    MainPhysicalClauses mainVelocity mainEps0 mainGrowthFloor :=
  mainPhysicalClauses_of_mainReducedClauses mainVelocity_isTransverseDivergenceFree
    mainGrowthFloor_pos mainReducedClauses_holds

/-- **The spectral half of Theorem 1.2 with all three witnesses exposed.**  The same content as
`mainPhysicalConclusion_holds` of `FastDynamo/MainTheorem.lean`, but with the existential
quantifiers replaced by the closed terms `mainVelocity`, `mainEps0` and `mainGrowthFloor`. -/
theorem main_theorem_explicit_witnesses :
    IsTransverseDivergenceFree mainVelocity ∧ mainVelocity ≠ 0 ∧
      0 < mainEps0 ∧ 0 < mainGrowthFloor ∧
        MainPhysicalClauses mainVelocity mainEps0 mainGrowthFloor :=
  ⟨mainVelocity_isTransverseDivergenceFree, mainVelocity_ne_zero, mainEps0_pos,
    mainGrowthFloor_pos, mainPhysicalClauses_holds⟩

end

end FastDynamo
