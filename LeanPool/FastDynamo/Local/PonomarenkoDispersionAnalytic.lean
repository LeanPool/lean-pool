/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.ModifiedBesselKAnalytic
public import Mathlib.Topology.MetricSpace.Contracting
public import LeanPool.FastDynamo.Local.ModifiedBessel

/-!
# The Ponomarenko dispersion function and its analyticity

Lemma 2.1 (`lem:jump-horizontal-mode`) obtains the growing local eigenvalue from a zero of
the Ponomarenko dispersion relation `eq:dispersion`, which the paper finds on the segment
`κ = ϱ(1+it)`, `t ∈ [1/2, 3/4]`, by the intermediate value theorem (formalised in
`PonomarenkoSegmentRoot`).  This module defines the dispersion function
`𝒟(κ) = I₀(κ)K₀(κ) - I₂(κ)K₂(κ)` (`ponomarenkoDispersion`) from the integral second-kind
modified-Bessel functions and proves that it is analytic on the open right half-plane
(`ponomarenkoDispersion_analyticOnNhd`, used by `PonomarenkoSegmentDispersion`).

## Contents

* Typed interface for the Ponomarenko dispersion relation: `PonomarenkoSecondKind`, the
  dispersion function, and its concrete instance `ponomarenkoDispersion`.
* Analyticity of the Ponomarenko dispersion function: `ponomarenkoDispersion_analyticOnNhd`.
-/

@[expose] public section

/-!
## Typed interface for the Ponomarenko dispersion relation

The two integral second-kind modified-Bessel orders and the exact dispersion function
`eq:dispersion` on the right half-plane.
-/

noncomputable section

namespace FastDynamo

open Function Set Complex

/-- An interface for the two second-kind modified-Bessel orders used by the azimuthal mode `j = 1`.
It is instantiated below by the hyperbolic-integral definitions. -/
structure PonomarenkoSecondKind where
  /-- The order-zero second-kind function. -/
  K0 : ℂ → ℂ
  /-- The order-two second-kind function. -/
  K2 : ℂ → ℂ

/-- The second-kind pair supplied by the hyperbolic-integral definitions in
`ModifiedBesselK`. These represent the classical functions when the argument
has positive real part. -/
def ponomarenkoIntegralSecondKind : PonomarenkoSecondKind where
  K0 := ModifiedBessel.K0
  K2 := ModifiedBessel.K2

namespace PonomarenkoSecondKind

/-- The exact scalar Bessel combination
`I₀(κ) K₀(κ) - I₂(κ) K₂(κ)` from the dispersion relation `eq:dispersion`. -/
def dispersion (K : PonomarenkoSecondKind) (κ : ℂ) : ℂ :=
  ModifiedBessel.I0 κ * K.K0 κ - ModifiedBessel.I2 κ * K.K2 κ

end PonomarenkoSecondKind

/-- The concrete dispersion function `𝒟` of `eq:dispersion`, using the totalized integral
definitions of `K₀` and `K₂`. It has the classical interpretation when
`0 < κ.re`. -/
def ponomarenkoDispersion (κ : ℂ) : ℂ :=
  ponomarenkoIntegralSecondKind.dispersion κ

/-- Unfolding of the concrete dispersion function to the combination
`𝒟(κ) = I₀(κ)K₀(κ) - I₂(κ)K₂(κ)` (Paper equation `eq:dispersion`, Lemma 2.1). -/
@[simp] theorem ponomarenkoDispersion_apply (κ : ℂ) :
    ponomarenkoDispersion κ =
      ModifiedBessel.I0 κ * ModifiedBessel.K0 κ -
        ModifiedBessel.I2 κ * ModifiedBessel.K2 κ :=
  rfl

end FastDynamo

/-!
## Analyticity of the Ponomarenko dispersion functions

The right-half-plane analyticity of the integral modified-Bessel
functions is transferred here to the concrete dispersion function.
-/

noncomputable section

namespace FastDynamo

open Complex Set

/-- The concrete integral Ponomarenko dispersion is analytic on the open right half-plane. -/
theorem ponomarenkoDispersion_analyticOnNhd :
    AnalyticOnNhd ℂ ponomarenkoDispersion {k : ℂ | 0 < k.re} := by
  intro k hk
  exact ((ModifiedBessel.I0_analyticAt k).mul
    (ModifiedBessel.analyticOnNhd_K0 k hk)).sub
      ((ModifiedBessel.I2_analyticAt k).mul
        (ModifiedBessel.analyticOnNhd_K2 k hk))

end FastDynamo
