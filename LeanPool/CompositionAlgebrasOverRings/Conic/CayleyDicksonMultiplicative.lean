/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Conic.CayleyDickson
public import LeanPool.CompositionAlgebrasOverRings.Conic.Multiplicative

/-!
# The double of an associative multiplicative conic algebra is multiplicative (`GPR Exc. 18.18`)

`Cay(B, μ)` has a multiplicative norm **if and only if** `B` is associative with a multiplicative
norm (`GPR Exc. 18.18`). This file proves the direction that builds algebras: it is what carries
`n(xy) = n(x)n(y)` up the tower `k → k[√·] → ℍ → 𝕆`, and — since `𝕆` is *not* associative — it is
also where the tower stops, which is the content of the sedenion non-example (`GPR 19.23`,
Layer 8).

## The computation

Write `x = u₁ + v₁ j`, `y = u₂ + v₂ j`. Expanding

  `n(xy) = n_B(u₁u₂ + μ (conj v₂)v₁) - μ n_B(v₂u₁ + v₁(conj u₂))`

with `n_B` multiplicative and `n_B(conj z) = n_B(z)` leaves exactly the terms of
`n(x)n(y) = (n_B(u₁) - μ n_B(v₁))(n_B(u₂) - μ n_B(v₂))`, plus

  `μ · [ n_B(u₁u₂, (conj v₂)v₁) - n_B(v₂u₁, v₁(conj u₂)) ]`.

So everything reduces to the vanishing of that bracket, `polar_shuffle` below. That is where
associativity of `B` is spent, and it is spent exactly once: the two polar terms are moved onto a
common form by the two halves of norm-associativity
(`ConicAlgebra.IsMultiplicative.polar_mul_left` and `.polar_mul_right`), and what stands between
them is `v₂(u₁u₂) = (v₂u₁)u₂`.

⚠ No hypothesis is needed on the conjugation of `B` — unlike `ConicAlgebra.isAlternative_cay`,
which needs it to be an involution. Only `conj (conj z) = z` is used, and that holds in every
conic algebra (`ConicAlgebra.conj_conj`). Nor is anything needed on `μ`, on `2`, or on the module
underlying `B`.

## Main results

* `ConicAlgebra.isMultiplicative_cay` : **`GPR Exc. 18.18`**, the direction `⇐`.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 18.13, Exc. 18.18.
-/

@[expose] public section

universe u v

namespace ConicAlgebra

variable {k : Type u} {B : Type v} [CommRing k] [Ring B] [Algebra k B] {C : ConicAlgebra k B}

/-- The one place associativity of `B` enters `GPR Exc. 18.18`: for a multiplicative norm on an
associative `B`,

  `n(u₁u₂, (conj v₂)v₁) = n(v₂u₁, v₁(conj u₂))`.

Both sides equal `n(v₁, (v₂u₁)u₂)`: the left by norm-associativity on the left
(`ConicAlgebra.IsMultiplicative.polar_mul_left`) followed by `v₂(u₁u₂) = (v₂u₁)u₂`, the right by
norm-associativity on the right (`ConicAlgebra.IsMultiplicative.polar_mul_right`). -/
private theorem polar_shuffle (h : C.IsMultiplicative) (u₁ u₂ v₁ v₂ : B) :
    QuadraticMap.polar C.norm (u₁ * u₂) (C.conj v₂ * v₁)
      = QuadraticMap.polar C.norm (v₂ * u₁) (v₁ * C.conj u₂) :=
  calc QuadraticMap.polar C.norm (u₁ * u₂) (C.conj v₂ * v₁)
      = QuadraticMap.polar C.norm (C.conj v₂ * v₁) (u₁ * u₂) := QuadraticMap.polar_comm ..
    _ = QuadraticMap.polar C.norm v₁ (C.conj (C.conj v₂) * (u₁ * u₂)) := h.polar_mul_left ..
    _ = QuadraticMap.polar C.norm v₁ (v₂ * u₁ * C.conj (C.conj u₂)) := by
        rw [conj_conj, conj_conj, mul_assoc]
    _ = QuadraticMap.polar C.norm (v₁ * C.conj u₂) (v₂ * u₁) := (h.polar_mul_right ..).symm
    _ = QuadraticMap.polar C.norm (v₂ * u₁) (v₁ * C.conj u₂) := QuadraticMap.polar_comm ..

/-- **`GPR Exc. 18.18`, `⇐`.** If `B` is associative and its norm is multiplicative, then the
norm of
`Cay(B, μ)` is multiplicative, for every scalar `μ`.

This is the step that makes `ℍ` a composition algebra out of `ℂ`, and `𝕆` out of `ℍ`; it fails to
apply one rung further because `𝕆` is not associative, which is why the sedenions
`Cay(𝕆, μ)` are conic but not composition (`GPR 19.23`). -/
theorem isMultiplicative_cay (C : ConicAlgebra k B) (μ : k) (h : C.IsMultiplicative) :
    (C.cay μ).IsMultiplicative := by
  intro x y
  simp only [cay_norm_apply, Cay.fst_mul, Cay.snd_mul, C.norm_add, QuadraticMap.map_smul,
    QuadraticMap.polar_smul_right, h.norm_mul, norm_conj, smul_eq_mul,
    polar_shuffle h x.1 y.1 x.2 y.2]
  ring

end ConicAlgebra
