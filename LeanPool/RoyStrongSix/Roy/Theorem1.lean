/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.Common
public import LeanPool.RoyStrongSix.Defs

/-!
# Waldschmidt's transcendence theorem on `G_a^{d₀} × G_m^{d₁}` (Roy's Theorem 1)

This file only *states* the theorem, as a `Prop`; it is proved unconditionally as
`StrongSix.M2.waldschmidtTheorem1` (`StrongSix/M2/Final.lean`). The implication

  `WaldschmidtTheorem1 → StrongSixExponentials`

is proved in `StrongSix/Roy/Final.lean` (`StrongSix.Roy.strongSix_of_theorem1`), following
D. Roy, *Matrices whose coefficients are linear forms in logarithms*, J. Number Theory 41 (1992)
22–47, §§1–4. The statement below transcribes Roy's Theorem 1 (p. 25) with `K = ℂ`:

> Let `d₀, d₁ ≥ 0`.
> * `Y` is a finite-dimensional `ℚ`-subspace of `K^{d₀} × K^{d₁}` contained in `Qbar^{d₀} × L^{d₁}`.
> * `W` is a `K`-subspace of `K^{d₀} × K^{d₁}` that is rational over `Qbar`.
> * `V` is a `K`-subspace containing `Y` and `W`.
>
> If `V ≠ K^{d₀} × K^{d₁}`, there is a surjective `K`-linear map
> `s : K^{d₀} × K^{d₁} → K^{d₀'} × K^{d₁'}` with `s(Qbar^{d₀} × 0) ⊂ Qbar^{d₀'} × 0` and
> `s(0 × ℚ^{d₁}) ⊂ 0 × ℚ^{d₁'}` such that, writing `Y' = s(Y)`, `W' = s(W)`, `V' = s(V)`,
> `Ω = 0 × ωℚ^{d₁}` and `Ω' = 0 × ωℚ^{d₁'}` (`ω = 2πi`), we have `W' ≠ K^{d₀'} × K^{d₁'}` and
>
>   `(d₁' − dim_ℚ(Y' ∩ Ω') + dim_ℚ Y') / (d₀' + d₁' − dim_K W') ≤ (d₁ − dim_ℚ(Y ∩ Ω)) / (d₀ + d₁ −
dim_K V)`.

Here `L` is the set of logarithms of nonzero algebraic numbers, i.e. `StrongSix.logAlg`.
-/

@[expose] public section

namespace LeanPool

open Complex Module Real

namespace StrongSix.Roy

/-- The ambient space `ℂ^{d₀} × ℂ^{d₁}`: the Lie algebra of `G_a^{d₀} × G_m^{d₁}`. -/
abbrev E (d0 d1 : ℕ) := (Fin d0 → ℂ) × (Fin d1 → ℂ)

/-- A vector with algebraic coordinates (a point of `Qbar^n`). -/
def AlgVec {n : ℕ} (u : Fin n → ℂ) : Prop := ∀ i, IsAlgebraic ℚ (u i)

/-- A vector with rational coordinates (a point of `ℚ^n`). -/
def RatVec {n : ℕ} (v : Fin n → ℂ) : Prop := ∀ i, ∃ q : ℚ, v i = q

/-- A `ℂ`-subspace of `ℂ^{d₀} × ℂ^{d₁}` is *rational over `Qbar`* if it is spanned over `ℂ` by
vectors with algebraic coordinates. -/
def RationalOverQbar {d0 d1 : ℕ} (W : Submodule ℂ (E d0 d1)) : Prop :=
  W = Submodule.span ℂ {w | w ∈ W ∧ AlgVec w.1 ∧ AlgVec w.2}

/-- `Ω = 0 × ωℚ^{d₁}` with `ω = 2πi`, as a `ℚ`-subspace. -/
noncomputable def Omega (d0 d1 : ℕ) : Submodule ℚ (E d0 d1) :=
  Submodule.span ℚ (Set.range fun j : Fin d1 => ((0 : Fin d0 → ℂ), Pi.single j (2 * π * I)))

/-- **Waldschmidt's theorem** (Roy 1992, Theorem 1; Waldschmidt 1988, Theorem 4.1, applied to
`G_a^{d₀} × G_m^{d₁}`), with `K = ℂ`. -/
def WaldschmidtTheorem1 : Prop :=
  ∀ (d0 d1 : ℕ) (Y : Submodule ℚ (E d0 d1)) (W V : Submodule ℂ (E d0 d1)),
    FiniteDimensional ℚ Y →
    (∀ p ∈ Y, AlgVec p.1 ∧ ∀ j, p.2 j ∈ logAlg) →
    RationalOverQbar W →
    (∀ p ∈ Y, p ∈ V) → W ≤ V → V ≠ ⊤ →
    ∃ (d0' d1' : ℕ) (s : E d0 d1 →ₗ[ℂ] E d0' d1'),
      Function.Surjective s ∧
      (∀ u : Fin d0 → ℂ, AlgVec u → ∃ u', AlgVec u' ∧ s (u, 0) = (u', 0)) ∧
      (∀ v : Fin d1 → ℂ, RatVec v → ∃ v', RatVec v' ∧ s (0, v) = (0, v')) ∧
      W.map s ≠ ⊤ ∧
      ((d1' : ℚ) - finrank ℚ ↥(Y.map (s.restrictScalars ℚ) ⊓ Omega d0' d1') +
          finrank ℚ ↥(Y.map (s.restrictScalars ℚ))) /
        ((d0' + d1' : ℚ) - finrank ℂ ↥(W.map s)) ≤
      ((d1 : ℚ) - finrank ℚ ↥(Y ⊓ Omega d0 d1)) / ((d0 + d1 : ℚ) - finrank ℂ ↥V)

end StrongSix.Roy

end LeanPool
