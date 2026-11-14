/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Defs
public import LeanPool.CompositionAlgebrasOverRings.Conic.Kirmse
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.NonsingularOverFields

/-!
# Composition algebras are alternative (`GPR 19.3`)

`GPR 19.3` says that a composition algebra is alternative, and that its norm is the unique conic
norm on it. This file proves the alternativity statement in the two cases where the hypothesis
`GPR 19.3` actually consumes — vanishing of the radical of the norm — is available from
non-singularity: **over a field**, unconditionally, and **over a ring in which `2` is
invertible**.

The mathematical content is entirely in `Conic/Kirmse.lean`, where the Kirmse defect
`(conj x)(xy) - n(x)·y` is shown to lie in the radical of the norm with no hypothesis at all. All
that happens here is the passage from the composition-algebra hypothesis,
`QuadraticForm.IsGPRNonsingular`, to `QuadraticForm.IsGPRNondegenerate`.

⚠ **That passage is not free over a ring.** Non-singularity does not imply that the radical
vanishes: `QuadraticForm.rankOne 1` over `𝔽₂[t]/(t²)` is non-singular but has `t` in its radical.
Over a field, non-singularity implies a vanishing radical, because it includes the trivial base
change (`QuadraticForm.radical_eq_bot_of_radical_baseChangeOfProjective_eq_bot`) — only that
direction: `x² + t y²` over `𝔽₂(t)` has zero radical but acquires a radical vector over `𝔽₂(√t)`.
Over a ring with `2` invertible, non-singular implies regular (`GN (C.8.2)`) and hence injective
polar form. The general ring case is not a descent from the residue fields (`Conic/Kirmse.lean`
explains why that fails); alternativity over an arbitrary ring is proved instead in
`Composition/Alternative.lean`.

## Main results

* `ConicAlgebra.IsComposition.isGPRNondegenerate` : over a field, the radical of the norm of a
  composition algebra vanishes.
* `ConicAlgebra.IsComposition.isAlternative` : **`GPR 19.3` over a field**, with no hypothesis on
  `2` and none on the rank — in particular it covers characteristic 2.
* `ConicAlgebra.IsComposition.isAlternative_of_invertible_two` : the same over any commutative ring
  in which `2` is a unit.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 19.3.
* [GN] Gille, Neher, *Group schemes over LG-rings…*, European J. Math. **11** (2025), art. 42,
  C.8, (C.8.2).
-/

@[expose] public section

universe u v

namespace ConicAlgebra

section CommRing

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A]
  {C : ConicAlgebra k A}

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- When `2 ∈ kˣ`, the radical of the norm of a composition algebra vanishes: non-singular implies
regular (`GN (C.8.2)`), and with `2` invertible an injective polar form is the same thing as a
vanishing radical. -/
theorem IsComposition.isGPRNondegenerate_of_invertible_two [Invertible (2 : k)]
    (h : C.IsComposition.{u, v, u}) : C.norm.IsGPRNondegenerate :=
  (QuadraticForm.radical_eq_bot_iff_injective_polarBilin C.norm).mpr h.isGPRRegular.injective

/-- **`GPR 19.3` over a commutative ring in which `2` is invertible: a composition algebra is
alternative.** -/
theorem IsComposition.isAlternative_of_invertible_two [Invertible (2 : k)]
    (h : C.IsComposition.{u, v, u}) : IsAlternative A :=
  h.isMultiplicative.isAlternative h.isGPRNondegenerate_of_invertible_two

end CommRing

section Field

variable {K : Type u} {A : Type v} [Field K] [NonAssocRing A] [Module K A]
  [SMulCommClass K A A] [IsScalarTower K A A] [Module.Finite K A] [Module.Projective K A]
  {C : ConicAlgebra K A}

omit [SMulCommClass K A A] [IsScalarTower K A A] in
/-- **Over a field, the radical of the norm of a composition algebra vanishes.**

Non-singularity quantifies over *every* field extension of the base, so it applies in particular to
the base field itself, and `QuadraticForm.radical_eq_bot_of_radical_baseChangeOfProjective_eq_bot`
brings the conclusion back down along `K → K ⊗[K] A`. No hypothesis on `2`, and none on the rank:
in characteristic 2 the polar form may well have a kernel, but the *radical* — which constrains `n`
as well as `n(·,·)` — does not. -/
theorem IsComposition.isGPRNondegenerate (h : C.IsComposition.{u, v, u}) :
    C.norm.IsGPRNondegenerate :=
  C.norm.radical_eq_bot_of_radical_baseChangeOfProjective_eq_bot (h.isGPRNonsingular K)

/-- **`GPR 19.3` over a field: every composition algebra is alternative.**

No hypothesis on `2` and none on the rank. The characteristic-2 case, where the polar form of the
norm can be degenerate, is covered: Kirmse's identities need the radical to vanish, not the polar
form to be injective (`Conic/Kirmse.lean`). -/
theorem IsComposition.isAlternative (h : C.IsComposition.{u, v, u}) : IsAlternative A :=
  h.isMultiplicative.isAlternative h.isGPRNondegenerate

end Field

end ConicAlgebra
