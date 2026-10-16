/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Conic.Multiplicative
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Regularity

/-!
# Kirmse's identities, and alternativity of a multiplicative conic algebra

**Kirmse's identities** for a multiplicative conic algebra are

  `(conj x)(xy) = n(x) y`,   `(yx)(conj x) = n(x) y`.

They are the mechanism behind `GPR 19.3`: substituting `conj x = t(x)·1 - x` and using the
degree-two identity `x² = t(x)·x - n(x)·1` turns them into precisely the two alternative laws, so a
multiplicative conic algebra satisfying them is alternative.

## The Kirmse element lies in the radical

Write `w = (conj x)(xy) - n(x)·y` for the defect of the first identity. **In every multiplicative
conic algebra, with no hypothesis whatsoever, `w` lies in the radical of the norm** — that is, both

  `n(w, z) = 0` for every `z`   and   `n(w) = 0`.

The first is two applications of norm-associativity (`Conic/Multiplicative.lean`); the second is
the computation

  `n(w) = n(x)²n(y) + n(x)²n(y) - n(x)² · n(y, y) = 2n(x)²n(y) - 2n(x)²n(y) = 0`,

using `n(y, y) = 2n(y)`. Both are `ConicAlgebra.IsMultiplicative.mem_radical_conj_mul_mul` below,
and similarly for the second identity.

Consequently the hypothesis that lets `w` be cancelled is exactly **`GPR`'s non-degeneracy**,
`QuadraticForm.IsGPRNondegenerate` — the vanishing of `QuadraticMap.radical` — which is the
hypothesis `GPR 19.3` puts on the norm. `GPR 19.3` itself starts from a unital algebra with such a
form and *derives* the conic structure, and also shows that the polar radical is a central ideal
annihilated by `2` and by every `n(x, y)`; those parts are `Conic/Recognition.lean`
(`ConicAlgebra.ofMultiplicative` and the results after it). Here the conic structure is the input.
Nothing here needs the polar form to be injective, so nothing here is
troubled by characteristic 2, where the polar form of a non-singular form of odd rank has a kernel.

⚠ **Non-degeneracy is not implied by non-singularity over a ring**, so this is not yet `GPR 19.3`
for composition algebras over an arbitrary base: `QuadraticForm.rankOne 1` over `𝔽₂[t]/(t²)` is
non-singular (`QuadraticForm.isGPRNonsingular_rankOne`) but has `t` in its radical. Over a *field*
non-singularity does imply a vanishing radical
(`QuadraticForm.radical_eq_bot_of_radical_baseChangeOfProjective_eq_bot`), which is what
`Composition/Basic.lean` uses. Over a ring, alternativity of composition algebras is proved by a
different route in `Composition/Alternative.lean`
(`ConicAlgebra.IsComposition.isAlternative_general`: regularity, the rank-one case, and the rank
decomposition); see below for why residue-field descent is not that route.

## Main results

* `ConicAlgebra.IsMultiplicative.mem_radical_conj_mul_mul`,
  `.mem_radical_mul_mul_conj` : the Kirmse defects lie in the radical of the norm,
  unconditionally.
* `ConicAlgebra.IsMultiplicative.conj_mul_mul`, `.mul_mul_conj` : **Kirmse's identities**, for a
  norm with vanishing radical.
* `ConicAlgebra.IsMultiplicative.isAlternative` : such an algebra is alternative. This is
  `GPR 19.3`'s alternativity statement, with `GPR`'s own hypothesis and no assumption on `2`, on
  the rank, or on the module.

## Why not residue-field descent

Alternativity of a composition algebra over an arbitrary commutative ring, whose norm is only
*non-singular*, is proved in `Composition/Alternative.lean`. A route once recorded here does not
work, and is written out so that it is not attempted again.

That route was: the alternative laws are multilinear, and a map of finitely generated modules
vanishes as soon as it vanishes after base change to every residue field; over each residue field
the base-changed algebra is again a multiplicative conic algebra with vanishing radical
(`ConicAlgebra.IsComposition.baseChangeOfProjective`, `Composition/BaseChange.lean`), so the theorem
below applies there.

⚠ The second ingredient — residue-field detection — is **false**. Over `R = 𝔽₂[t]/(t²)`, the map
`R → R`, `x ↦ t x`, is nonzero, yet `R` has the single maximal ideal `(t)` and the map vanishes
after base change to `R ⧸ (t) = 𝔽₂`. Base changing to every *field* over `R`, rather than every
residue field, does not help: `t` is nilpotent, so it dies in every field over `R`. Nothing about
finite generation or projectivity repairs this — residue fields simply cannot see a nilpotent, and
this is the same phenomenon as the ⚠ above, where `t` sits in the radical of a non-singular form
over exactly that ring. The proof in `Composition/Alternative.lean` therefore works over the base:
regularity where the rank exceeds one, and commutativity and associativity outright in rank one.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 19.3 (composition
  algebras are alternative), 16.5 (norm-associativity).
-/

@[expose] public section

universe u v

namespace ConicAlgebra

namespace IsMultiplicative

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] {C : ConicAlgebra k A}

omit [SMulCommClass k A A] in
/-- **Kirmse's left identity, in polar form**: `n((conj x)(xy), z) = n(x) n(y, z)`, in every
multiplicative conic algebra and with no regularity hypothesis.

Norm-associativity moves `conj x` across the polar form as `x` (`conj (conj x) = x`), turning the
left side into `n(xy, xz)`, which is the linearization of multiplicativity in the right variable. -/
theorem polar_conj_mul_mul (h : C.IsMultiplicative) (x y z : A) :
    QuadraticMap.polar C.norm (C.conj x * (x * y)) z
      = C.norm x * QuadraticMap.polar C.norm y z := by
  rw [h.polar_mul_left, conj_conj, h.polar_mul_mul_left]

omit [IsScalarTower k A A] in
/-- **Kirmse's right identity, in polar form**: `n((yx)(conj x), z) = n(x) n(y, z)`, in every
multiplicative conic algebra and with no regularity hypothesis. -/
theorem polar_mul_mul_conj (h : C.IsMultiplicative) (x y z : A) :
    QuadraticMap.polar C.norm ((y * x) * C.conj x) z
      = C.norm x * QuadraticMap.polar C.norm y z := by
  rw [h.polar_mul_right, conj_conj, h.polar_mul_mul_right, mul_comm]

omit [SMulCommClass k A A] in
/-- The norm of the left Kirmse defect vanishes: `n((conj x)(xy) - n(x)·y) = 0`.

Multiplicativity evaluates the two square terms as `n(x)²n(y)` each, and the polar term as
`n(x)² · n(y, y) = 2n(x)²n(y)` by `ConicAlgebra.IsMultiplicative.polar_conj_mul_mul` at `z = y`.
They cancel. No regularity, and nothing on `2`: the `2` here comes from `n(y, y) = 2n(y)` and is
cancelled against itself, never divided by. -/
theorem norm_conj_mul_mul_sub (h : C.IsMultiplicative) (x y : A) :
    C.norm (C.conj x * (x * y) - C.norm x • y) = 0 := by
  simp only [C.norm_sub, h.norm_mul, norm_conj, QuadraticMap.map_smul,
    QuadraticMap.polar_smul_right, h.polar_conj_mul_mul, QuadraticMap.polar_self, smul_eq_mul,
    nsmul_eq_mul]
  push_cast
  ring

omit [IsScalarTower k A A] in
/-- The norm of the right Kirmse defect vanishes: `n((yx)(conj x) - n(x)·y) = 0`. -/
theorem norm_mul_mul_conj_sub (h : C.IsMultiplicative) (x y : A) :
    C.norm ((y * x) * C.conj x - C.norm x • y) = 0 := by
  simp only [C.norm_sub, h.norm_mul, norm_conj, QuadraticMap.map_smul,
    QuadraticMap.polar_smul_right, h.polar_mul_mul_conj, QuadraticMap.polar_self, smul_eq_mul,
    nsmul_eq_mul]
  push_cast
  ring

omit [SMulCommClass k A A] in
/-- **The left Kirmse defect lies in the radical of the norm**, in every multiplicative conic
algebra and with no hypothesis at all. This is the sharp unconditional statement behind
`GPR 19.3`; the identity `(conj x)(xy) = n(x)·y` is exactly its image under `radical = ⊥`. -/
theorem mem_radical_conj_mul_mul (h : C.IsMultiplicative) (x y : A) :
    C.conj x * (x * y) - C.norm x • y ∈ QuadraticMap.radical C.norm :=
  ⟨h.norm_conj_mul_mul_sub x y, LinearMap.ext fun z ↦ by
    rw [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply, QuadraticMap.polar_sub_left,
      h.polar_conj_mul_mul, QuadraticMap.polar_smul_left, smul_eq_mul, sub_self]⟩

omit [IsScalarTower k A A] in
/-- **The right Kirmse defect lies in the radical of the norm**, unconditionally. -/
theorem mem_radical_mul_mul_conj (h : C.IsMultiplicative) (x y : A) :
    (y * x) * C.conj x - C.norm x • y ∈ QuadraticMap.radical C.norm :=
  ⟨h.norm_mul_mul_conj_sub x y, LinearMap.ext fun z ↦ by
    rw [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply, QuadraticMap.polar_sub_left,
      h.polar_mul_mul_conj, QuadraticMap.polar_smul_left, smul_eq_mul, sub_self]⟩

variable (hrad : C.norm.IsGPRNondegenerate)
include hrad

omit [SMulCommClass k A A] in
/-- **Kirmse's left identity**: `(conj x)(xy) = n(x) y`.

The hypothesis is `GPR`'s non-degeneracy, `QuadraticMap.radical C.norm = ⊥` — exactly what
`GPR 19.3` assumes, and exactly what is needed to cancel the radical element of
`ConicAlgebra.IsMultiplicative.mem_radical_conj_mul_mul`. -/
theorem conj_mul_mul (h : C.IsMultiplicative) (x y : A) :
    C.conj x * (x * y) = C.norm x • y := by
  have hmem := h.mem_radical_conj_mul_mul x y
  rw [show C.norm.radical = ⊥ from hrad, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hmem

omit [IsScalarTower k A A] in
/-- **Kirmse's right identity**: `(yx)(conj x) = n(x) y`. -/
theorem mul_mul_conj (h : C.IsMultiplicative) (x y : A) :
    (y * x) * C.conj x = C.norm x • y := by
  have hmem := h.mem_radical_mul_mul_conj x y
  rw [show C.norm.radical = ⊥ from hrad, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hmem

/-- **`GPR 19.3`, the alternativity statement: a multiplicative conic algebra with non-degenerate
norm is alternative.**

Each alternative law is one of Kirmse's identities rewritten with `conj x = t(x)·1 - x` and the
degree-two identity `x² = t(x)·x - n(x)·1`.

The hypotheses on the norm are `GPR`'s: multiplicative, with zero radical. Nothing is assumed
about `2`, about the rank, or about the module — in particular no projectivity, which `GPR 19.3`
carries for its other conclusions. The conic structure (the degree-two identity) is an input
here; `GPR 19.3` derives it from the form, which is `ConicAlgebra.ofMultiplicative` in
`Conic/Recognition.lean`. -/
theorem isAlternative (h : C.IsMultiplicative) : IsAlternative A where
  left_alt x y := by
    have hk := h.conj_mul_mul hrad x y
    rw [conj_apply, sub_mul, smul_mul_assoc, one_mul] at hk
    simp only [C.mul_self_eq x, sub_mul, smul_mul_assoc, one_mul]
    linear_combination (norm := module) -hk
  right_alt x y := by
    have hk := h.mul_mul_conj hrad x y
    rw [conj_apply, mul_sub, mul_smul_comm, mul_one] at hk
    simp only [C.mul_self_eq x, mul_sub, mul_smul_comm, mul_one]
    linear_combination (norm := module) -hk

end IsMultiplicative

end ConicAlgebra
