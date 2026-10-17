/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.CayleyDickson
public import LeanPool.CompositionAlgebrasOverRings.Conic.CayleyDicksonAlternative
public import LeanPool.CompositionAlgebrasOverRings.Conic.CayleyDicksonAssociative

/-!
# The Cayley–Dickson tower: rank 2, 4 and 8 (`GPR 19.18`)

Iterating the Cayley–Dickson process three times from the base ring produces, for scalars
`μ₁, μ₂, μ₃ ∈ k`, conic algebras of ranks `2`, `4` and `8`:

  `Cay₂ k μ₁ = Cay(k, μ₁)`,
  `Cay₄ k μ₁ μ₂ = Cay(Cay₂, μ₂)`   — a quaternion algebra,
  `Cay₈ k μ₁ μ₂ μ₃ = Cay(Cay₄, μ₃)` — an **octonion algebra**, which mathlib does
  not have.

Everything is over an arbitrary commutative ring `k`, with arbitrary scalars; the hypotheses
`2 ∈ kˣ` and `μᵢ ∈ kˣ` appear only on the theorem that the tower consists of *composition*
algebras.

## Why the tower stops at 8

Each rung is built by a theorem whose hypothesis is a property of the rung below.
`ConicAlgebra.mul_comm_cay` needs its input's conjugation to be the identity, which holds for the
base ring; `ConicAlgebra.mul_assoc_cay` needs its input commutative; and
`ConicAlgebra.isMultiplicative_cay` (`GPR Exc. 18.18`) and `ConicAlgebra.isAlternative_cay`
(`GPR 18.14(c)`) need it associative. So each property may be lost one rung after the property
that implies it, and the fourth double — the **sedenions** — is in general neither alternative
nor
multiplicative. That is the mechanism behind the rank dichotomy `1, 2, 4, 8` of `GPR 19.18`.

What is proved *positively* here is that `Cay₂` is commutative, `Cay₄` is associative, and
`Cay₈`
is alternative with multiplicative norm — each over an arbitrary base.

⚠ The *negative* half is genuinely characteristic-dependent and is therefore **not** stated in
this file. Over a base in which `2 = 0` the conjugation of `Cay₂` is again the identity, so
`ConicAlgebra.mul_comm_cay` applies once more and the tower stays commutative — the ranks still
double, but the algebras do not become non-commutative and then non-associative in the classical
way. The explicit witnesses that `ℍ` is not commutative and `𝕆` is not associative are proved
over
`ℝ` in `Composition/Examples.lean`, from the general
`ConicAlgebra.exists_mul_ne_mul_cay` and `ConicAlgebra.exists_mul_mul_ne_mul_mul_cay`.

Once such a witness is in hand for a rung, `ConicAlgebra.not_isAlternative_cay_of_mul_mul_ne` —
the converse half of `GPR 18.14(c)` — turns it into the failure of alternativity one rung up, with
no hypothesis on the scalar. That is the route to the sedenions of `GPR 19.23`.

## Main definitions

* `ConicAlgebra.Cay₂`, `ConicAlgebra.Cay₄`, `ConicAlgebra.Cay₈` : the underlying modules.
* `ConicAlgebra.cay₂`, `ConicAlgebra.cay₄`, `ConicAlgebra.cay₈` : their conic structures.
* `ConicAlgebra.Octonion`, `ConicAlgebra.octonion` : notation for the rank-8 case.

## Main results

* `ConicAlgebra.isMultiplicative_cay₈` : the octonion norm permits composition.
* `ConicAlgebra.isAlternative_cay₈` : octonion algebras are alternative (directly, from
  `GPR 18.14(c)`, without going through `GPR 19.3`).
* `ConicAlgebra.isComposition_cay₈` : for `2 ∈ kˣ` and `μᵢ` units, the octonion algebra is a
  composition algebra; likewise `isComposition_cay₂` and `isComposition_cay₄`.
* `ConicAlgebra.finrank_cay₂`, `.finrank_cay₄`, `.finrank_cay₈` : the ranks are `2`, `4`, `8`.

## Implementation notes

The `Ring`, `CommRing` and `Algebra` structures on the rungs are declared as **genuine instances**
here, unlike the `def`s they come from in `Conic/CayleyDicksonAssociative.lean`: at each rung the
side conditions are discharged by theorems (`ConicAlgebra.baseRing_conj_apply` at the bottom,
`ConicAlgebra.ConjIsInvolution.cay` above it) rather than assumed, so there is nothing for instance
search to guess. This is what makes the tower usable without `letI` at every step.

⚠ `Cay₄` is **not** mathlib's `QuaternionAlgebra`, and the two are incomparable in general —
see
overview trap 3. `QuaternionAlgebra` takes arbitrary structure constants and always produces a
*free* module; `Cay₄` produces a composition algebra exactly under the hypotheses below. Relating
them is the job of a later file.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 18.14, Exc. 18.18,
  19.18.
-/

@[expose] public section

universe u

namespace ConicAlgebra

variable (k : Type u) [CommRing k] (μ₁ μ₂ μ₃ : k)

/-! ### Rank 2 -/

/-- The **rank-2** Cayley–Dickson algebra `Cay(k, μ₁)`, as a `k`-module. -/
abbrev Cay₂ : Type u := Cay (baseRing k) μ₁

/-- The conic structure on `Cay₂`, i.e. `GPR 18.4` applied to the base ring. -/
noncomputable abbrev cay₂ : ConicAlgebra k (Cay₂ k μ₁) := (baseRing k).cay μ₁

/-- `Cay₂` is **commutative**: the conjugation of the base ring is the identity
(`ConicAlgebra.baseRing_conj_apply`), which is exactly the hypothesis of
`ConicAlgebra.mul_comm_cay`. This is the last commutative rung. -/
noncomputable instance : CommRing (Cay₂ k μ₁) :=
  Cay.commRing (baseRing k) μ₁ (baseRing_conj_apply k)

noncomputable instance : Algebra k (Cay₂ k μ₁) :=
  Cay.algebra (baseRing k) μ₁ (conjIsInvolution_of_conj_eq_id _ (baseRing_conj_apply k))

theorem conjIsInvolution_cay₂ : (cay₂ k μ₁).ConjIsInvolution :=
  ConjIsInvolution.cay (conjIsInvolution_of_conj_eq_id _ (baseRing_conj_apply k))

/-- The rank-2 norm is multiplicative: `GPR Exc. 18.18` applied to the base ring, which is
associative
with multiplicative norm. -/
theorem isMultiplicative_cay₂ : (cay₂ k μ₁).IsMultiplicative :=
  isMultiplicative_cay (baseRing k) μ₁ (isMultiplicative_baseRing k)

/-! ### Rank 4 -/

/-- The **rank-4** Cayley–Dickson algebra `Cay(Cay(k, μ₁), μ₂)` — a quaternion algebra.

⚠ Not mathlib's `QuaternionAlgebra`; see the module docstring. -/
abbrev Cay₄ : Type u := Cay (cay₂ k μ₁) μ₂

/-- The conic structure on `Cay₄`. -/
noncomputable abbrev cay₄ : ConicAlgebra k (Cay₄ k μ₁ μ₂) := (cay₂ k μ₁).cay μ₂

/-- `Cay₄` is **associative**, by `GPR 18.14(b)` applied to the commutative `Cay₂`. It is the
last
associative rung, which is why the tower produces composition algebras only up to rank 8. -/
noncomputable instance : Ring (Cay₄ k μ₁ μ₂) :=
  Cay.ring (cay₂ k μ₁) μ₂ (conjIsInvolution_cay₂ k μ₁)

noncomputable instance : Algebra k (Cay₄ k μ₁ μ₂) :=
  Cay.algebra (cay₂ k μ₁) μ₂ (conjIsInvolution_cay₂ k μ₁)

theorem conjIsInvolution_cay₄ : (cay₄ k μ₁ μ₂).ConjIsInvolution :=
  ConjIsInvolution.cay (conjIsInvolution_cay₂ k μ₁)

theorem isMultiplicative_cay₄ : (cay₄ k μ₁ μ₂).IsMultiplicative :=
  isMultiplicative_cay (cay₂ k μ₁) μ₂ (isMultiplicative_cay₂ k μ₁)

/-! ### Rank 8: octonion algebras -/

/-- The **rank-8** Cayley–Dickson algebra `Cay(Cay(Cay(k, μ₁), μ₂), μ₃)`: an
**octonion algebra**.
mathlib has no octonions, so this is the definition of record here. -/
abbrev Cay₈ : Type u := Cay (cay₄ k μ₁ μ₂) μ₃

/-- The conic structure on `Cay₈`. -/
noncomputable abbrev cay₈ : ConicAlgebra k (Cay₈ k μ₁ μ₂ μ₃) :=
  (cay₄ k μ₁ μ₂).cay μ₃

/-- The underlying module of an octonion algebra, under its usual name. -/
abbrev Octonion : Type u := Cay₈ k μ₁ μ₂ μ₃

/-- An octonion algebra, under its usual name. -/
noncomputable abbrev octonion : ConicAlgebra k (Octonion k μ₁ μ₂ μ₃) :=
  cay₈ k μ₁ μ₂ μ₃

theorem conjIsInvolution_cay₈ : (cay₈ k μ₁ μ₂ μ₃).ConjIsInvolution :=
  ConjIsInvolution.cay (conjIsInvolution_cay₄ k μ₁ μ₂)

/-- **Octonion algebras are alternative** — `GPR 18.14(c)` applied to the associative `Cay₄`.

This is a *direct* proof, independent of `GPR 19.3`: it needs no regularity of the norm, no
hypothesis on `2`, and no hypothesis on the `μᵢ`, whereas the general
`ConicAlgebra.IsComposition.isAlternative` needs the norm's radical to vanish. -/
instance isAlternative_cay₈ : IsAlternative (Cay₈ k μ₁ μ₂ μ₃) :=
  isAlternative_cay (cay₄ k μ₁ μ₂) μ₃ (conjIsInvolution_cay₄ k μ₁ μ₂)

/-- **The octonion norm permits composition**, `n(xy) = n(x)n(y)` — `GPR Exc. 18.18` applied to the
associative `Cay₄`. Again no hypothesis on `2` or on the `μᵢ`.

This is the last rung covered uniformly by the associative-input theorem used here. For a
further double, `GPR Exc. 18.18` gives the sharp criterion `μ₄[B, B, B] ⊆ Rad(Dn_B)`.
Non-associativity alone does not force failure of norm multiplicativity; the criterion is
automatic when `μ₄ = 0`. -/
theorem isMultiplicative_cay₈ : (cay₈ k μ₁ μ₂ μ₃).IsMultiplicative :=
  isMultiplicative_cay (cay₄ k μ₁ μ₂) μ₃ (isMultiplicative_cay₄ k μ₁ μ₂)

/-! ### The ranks are `2`, `4`, `8`

`ConicAlgebra.Cay.finrank_cay` doubles the rank at each step, starting from `finrank k k = 1`.
These need `k` nontrivial (otherwise `finrank` is `0` throughout) but nothing else — no unit
scalars, no hypothesis on `2`, and no composition. -/

section Rank

variable [Nontrivial k]

@[simp] theorem finrank_cay₂ : Module.finrank k (Cay₂ k μ₁) = 2 := by
  rw [Cay.finrank_cay, Module.finrank_self]

@[simp] theorem finrank_cay₄ : Module.finrank k (Cay₄ k μ₁ μ₂) = 4 := by
  rw [Cay.finrank_cay, finrank_cay₂]

/-- **An octonion algebra has rank 8.** -/
@[simp] theorem finrank_cay₈ : Module.finrank k (Cay₈ k μ₁ μ₂ μ₃) = 8 := by
  rw [Cay.finrank_cay, finrank_cay₄]

end Rank

/-! ### The tower consists of composition algebras

Here, and only here, the scalars must be units and `2` must be invertible. The hypothesis on `2`
is what turns non-singularity of each norm into the *regularity* that
`ConicAlgebra.IsComposition.cay` consumes; without it the very first rung already fails, since
`Cay(k, μ)` in characteristic 2 is inseparable and not a composition algebra. -/

section Composition

variable [Invertible (2 : k)]

theorem isComposition_cay₂ (h₁ : IsUnit μ₁) : (cay₂ k μ₁).IsComposition.{u, u, u} :=
  IsComposition.cay_of_invertible_two _ h₁ (isComposition_baseRing k)

theorem isComposition_cay₄ (h₁ : IsUnit μ₁) (h₂ : IsUnit μ₂) :
    (cay₄ k μ₁ μ₂).IsComposition.{u, u, u} :=
  IsComposition.cay_of_invertible_two _ h₂ (isComposition_cay₂ k μ₁ h₁)

/-- **An octonion algebra with unit scalars, over a base in which `2` is invertible, is a
composition algebra.** -/
theorem isComposition_cay₈ (h₁ : IsUnit μ₁) (h₂ : IsUnit μ₂) (h₃ : IsUnit μ₃) :
    (cay₈ k μ₁ μ₂ μ₃).IsComposition.{u, u, u} :=
  IsComposition.cay_of_invertible_two _ h₃ (isComposition_cay₄ k μ₁ μ₂ h₁ h₂)

end Composition

end ConicAlgebra
