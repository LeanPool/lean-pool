/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Conic.CayleyDickson

/-!
# The double is alternative exactly when the base is associative (`GPR 18.14(c)`)

`Cay(B, μ)` is alternative **if and only if** `B` is associative and the conjugation of `B` is an
involution (`GPR 18.14(c)`). Both directions are proved here, for every scalar `μ` and with no
hypothesis on `B` beyond the conic structure.

The direction `⇐` is the one that builds algebras: octonions from quaternions, quaternions from
quadratic étale algebras. The direction `⇒` is what stops the tower — it is the source of the
rank dichotomy `1, 2, 4, 8` (`GPR 19.18`), since the fourth double is alternative only if the
third is associative, which it is not.

## The hypotheses of `⇐`

Both are needed, and neither is free:

* **`B` associative**, as the explicit hypothesis `∀ a b c : B, a * b * c = a * (b * c)` rather
  than a `Ring B` instance, so that the same statement serves both directions of the equivalence:
  the converse produces associativity of a `B` that is only a `NonAssocRing`, and cannot produce
  an instance. `ConicAlgebra.isAlternative_cay` below is the `[Ring B] [Algebra k B]` form, which
  is what the Cayley–Dickson tower consumes.
* **The conjugation of `B` is an involution** (`ConicAlgebra.ConjIsInvolution`). This does *not*
  follow from associativity over an arbitrary base — `Conic/TraceDefectCounterexample.lean` is an
  associative conic algebra whose conjugation is not an anti-homomorphism — but it does hold as
  soon as `B` is finitely generated projective (`ConicAlgebra.conjIsInvolution_of_projective`) or
  the base is a field (`ConicAlgebra.conj_mul`).

`μ` remains an arbitrary scalar, in both directions. In particular the converse needs no unit
hypothesis: it reads off the two conclusions from products in which every `μ` has already
cancelled.

## The proof of `⇐`

Write `x = a + bj`, `y = c + dj`. Expanding the two alternative laws in components and using only

* associativity of `B`,
* anti-multiplicativity of the conjugation,
* `conj z = t(z) · 1 - z` (`ConicAlgebra.conj_apply`), which turns every conjugate into a scalar
  multiple of `1` minus the element, and
* `z² = t(z) · z - n(z) · 1` (`ConicAlgebra.mul_self_eq`) for `z = a` and `z = b`,

turns each of the four component identities into an identity between `k`-linear combinations of
the same products, which `module` closes. This is `GPR`'s "lengthy but straightforward
computation" of `GPR 18.13` specialized to `u₁ = u₂`, `v₁ = v₂`; here it is a single `simp only`
with a normalizing rewrite set, because eliminating the conjugation first makes all the
cancellations linear.

## The proof of `⇒`

Each conclusion is one component of one instance of one alternative law, so neither uses the
other, and neither uses `μ`.

* **Involutivity** is the `j`-component of left alternativity at `x = a + j`, `y = c`:

    `(conj c) a + conj(ac) = t(a) (conj c)`,

and `t(a) (conj c) - (conj c) a = (conj c) (conj a)`. The element `b` multiplying the conjugate in
the general computation is here specialized to `1`, which is what makes the defect visible without
any faithfulness hypothesis: `GPR 16.10(a)` only places the trace defect in `Ann(B)`, but `B` is
unital, so it vanishes.
* **Associativity** is the `j`-component of the linearized right alternative law
  (`IsAlternative.right_alt_linearized`) at `x = a`, `y = b`, `z = cj`:

    `a(bc) + (ab)(conj c) = (ac)b + (a(conj c))b`,

  in which expanding `conj c = t(c) · 1 - c` cancels both the trace terms and the two products that
  are not associated, leaving `abc = a(bc)`. Note that this is the linearization, not either
  alternative law itself: the plain laws applied to elements of these shapes give back only
  alternativity of `B` and the commutator identity, never associativity.

## Implementation notes

⚠ The elements `(a, 1)`, `(0, c)` and friends must be introduced **opaquely** — as local
constants of type `Cay C μ` whose components are fixed by hypotheses — and not as pair literals
ascribed to `Cay C μ`. A literal `((a, 1) : Cay C μ)` still elaborates with inferred type `B × B`,
so `ConicAlgebra.Cay.fst_mul` and `ConicAlgebra.Cay.snd_mul`, whose implicit `C` and `μ` are
determined only by that type, no longer unify and every rewrite silently fails.

## Main results

* `ConicAlgebra.isAlternative_cay_iff` : **`GPR 18.14(c)`**, the equivalence.
* `ConicAlgebra.isAlternative_cay_of_mul_assoc`, `ConicAlgebra.isAlternative_cay` : the
  direction `⇐`, the second in the `[Ring B]` form the tower uses.
* `ConicAlgebra.mul_assoc_of_isAlternative_cay`,
  `ConicAlgebra.conjIsInvolution_of_isAlternative_cay` : the two halves of `⇒`.
* `ConicAlgebra.not_isAlternative_cay_of_mul_mul_ne` : the contrapositive, in the form a
  non-associativity witness for `B` consumes.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 18.13, 18.14(c).
-/

@[expose] public section

universe u v

namespace ConicAlgebra

section NonAssoc

variable {k : Type u} {B : Type v} [CommRing k] [NonAssocRing B] [Module k B]
  [SMulCommClass k B B] [IsScalarTower k B B]

/-! ### The double of an associative algebra is alternative -/

omit [IsScalarTower k B B] in
/-- Reassociating `z b b` when `b² = t(b) b - n(b) 1`. This is the one place associativity of `B`
is used that the simp set cannot reach on its own: the product `(z * b) * b` has no `b * b`
subterm. -/
private theorem mul_mul_self (C : ConicAlgebra k B)
    (hassoc : ∀ a b c : B, a * b * c = a * (b * c)) (b z : B) :
    z * b * b = C.trace b • (z * b) - C.norm b • z := by
  rw [hassoc, C.mul_self_eq, mul_sub, mul_smul_comm, mul_smul_comm, mul_one]

/-- **`GPR 18.14(c)`, `⇐`.** If `B` is associative and its conjugation is an involution, then
`Cay(B, μ)` is alternative, for every scalar `μ`.

Stated with associativity as a hypothesis rather than an instance, so that it can be paired with
`ConicAlgebra.mul_assoc_of_isAlternative_cay` into the equivalence
`ConicAlgebra.isAlternative_cay_iff`. For an associative `B` use `ConicAlgebra.isAlternative_cay`,
which takes `mul_assoc` from the instance. -/
theorem isAlternative_cay_of_mul_assoc (C : ConicAlgebra k B) (μ : k)
    (hassoc : ∀ a b c : B, a * b * c = a * (b * c)) (hconj : C.ConjIsInvolution) :
    IsAlternative (Cay C μ) where
  left_alt x y := by
    refine Cay.ext ?_ ?_ <;>
      simp only [Cay.fst_mul, Cay.snd_mul, map_add, map_smul, hconj.conj_mul, conj_conj,
        C.conj_apply x.1, C.conj_apply x.2, mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc,
        mul_smul_comm, smul_add, smul_sub, mul_one, one_mul, ← hassoc,
        C.mul_self_eq x.1, C.mul_self_eq x.2, mul_mul_self C hassoc x.1,
        mul_mul_self C hassoc x.2] <;>
      module
  right_alt x y := by
    refine Cay.ext ?_ ?_ <;>
      simp only [Cay.fst_mul, Cay.snd_mul, map_add, map_sub, map_smul, hconj.conj_mul, conj_one,
        C.conj_apply x.1, C.conj_apply x.2, mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc,
        mul_smul_comm, smul_add, smul_sub, mul_one, one_mul, ← hassoc,
        C.mul_self_eq x.1, C.mul_self_eq x.2, mul_mul_self C hassoc x.1] <;>
      module

/-! ### The base of an alternative double is associative with involutive conjugation -/

/-- **`GPR 18.14(c)`, `⇒`, first half.** If `Cay(B, μ)` is alternative then the conjugation of `B`
is an involution.

The `j`-component of left alternativity at `x = a + j` and `y = c` reads
`(conj c) a + conj(ac) = t(a) (conj c)`, and `t(a) (conj c) - (conj c) a` is `(conj c) (conj a)` by
`ConicAlgebra.conj_apply`. No hypothesis on `μ`, and no associativity of `B`: taking the `j`-part of
`x` to be `1` removes every product in which `μ` or a reassociation could appear. -/
theorem conjIsInvolution_of_isAlternative_cay (C : ConicAlgebra k B) (μ : k)
    (h : IsAlternative (Cay C μ)) : C.ConjIsInvolution := by
  intro a c
  obtain ⟨x, hx1, hx2⟩ : ∃ x : Cay C μ, x.1 = a ∧ x.2 = 1 := ⟨(a, 1), rfl, rfl⟩
  obtain ⟨y, hy1, hy2⟩ : ∃ y : Cay C μ, y.1 = c ∧ y.2 = 0 := ⟨(c, 0), rfl, rfl⟩
  have key := congrArg Prod.snd (h.left_alt x y)
  simp only [Cay.fst_mul, Cay.snd_mul, hx1, hx2, hy1, hy2, map_zero, zero_mul, smul_zero,
    add_zero, zero_add, one_mul, mul_one] at key
  rw [C.add_conj a, smul_mul_assoc, one_mul] at key
  rw [C.conj_apply a, mul_sub, mul_smul_comm, mul_one]
  linear_combination (norm := module) key

/-- **`GPR 18.14(c)`, `⇒`, second half.** If `Cay(B, μ)` is alternative then `B` is associative.

The `j`-component of the linearized right alternative law at `x = a`, `y = b`, `z = cj` reads
`a(bc) + (ab)(conj c) = (ac)b + (a(conj c))b`; expanding `conj c = t(c) · 1 - c` cancels the trace
terms against the two products that are not associated. No hypothesis on `μ`: every product below
has a zero component where `μ` would enter. -/
theorem mul_assoc_of_isAlternative_cay (C : ConicAlgebra k B) (μ : k)
    (h : IsAlternative (Cay C μ)) (a b c : B) : a * b * c = a * (b * c) := by
  let := h
  obtain ⟨x, hx1, hx2⟩ : ∃ x : Cay C μ, x.1 = b ∧ x.2 = 0 := ⟨(b, 0), rfl, rfl⟩
  obtain ⟨y, hy1, hy2⟩ : ∃ y : Cay C μ, y.1 = c ∧ y.2 = 0 := ⟨(c, 0), rfl, rfl⟩
  obtain ⟨z, hz1, hz2⟩ : ∃ z : Cay C μ, z.1 = 0 ∧ z.2 = a := ⟨(0, a), rfl, rfl⟩
  have key := congrArg Prod.snd (IsAlternative.right_alt_linearized x y z)
  simp only [Cay.snd_add, Cay.fst_mul, Cay.snd_mul, hx1, hx2, hy1, hy2, hz1, hz2, map_zero,
    zero_mul, mul_zero, smul_zero, add_zero, zero_add] at key
  simp only [C.conj_apply c, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one] at key
  linear_combination (norm := module) -key

/-- **`GPR 18.14(c)`.** The Cayley–Dickson double `Cay(B, μ)` is alternative exactly when `B` is
associative and its conjugation is an involution — for every scalar `μ`. -/
theorem isAlternative_cay_iff (C : ConicAlgebra k B) (μ : k) :
    IsAlternative (Cay C μ) ↔
      (∀ a b c : B, a * b * c = a * (b * c)) ∧ C.ConjIsInvolution :=
  ⟨fun h ↦
      ⟨mul_assoc_of_isAlternative_cay C μ h, conjIsInvolution_of_isAlternative_cay C μ h⟩,
    fun h ↦ isAlternative_cay_of_mul_assoc C μ h.1 h.2⟩

/-- **The double of a non-associative algebra is not alternative.** The contrapositive of
`ConicAlgebra.mul_assoc_of_isAlternative_cay`, in the form that a single witness to the failure of
associativity in `B` consumes: this is what makes the fourth Cayley–Dickson rung — the sedenions,
`GPR 19.23` — fail to be alternative, and hence fail to be a composition algebra. -/
theorem not_isAlternative_cay_of_mul_mul_ne (C : ConicAlgebra k B) (μ : k) {a b c : B}
    (hne : a * b * c ≠ a * (b * c)) : ¬ IsAlternative (Cay C μ) :=
  fun h ↦ hne (mul_assoc_of_isAlternative_cay C μ h a b c)

end NonAssoc

/-! ### The associative case

The form the Cayley–Dickson tower consumes: `B` associative as an instance, which is what
`Conic/CayleyDicksonAssociative.lean` supplies for a double. -/

variable {k : Type u} {B : Type v} [CommRing k] [Ring B] [Algebra k B]

/-- **`GPR 18.14(c)`, `⇐`, for an associative `B`.** If the conjugation of an associative conic
algebra `B` is an involution, then `Cay(B, μ)` is alternative, for every scalar `μ`. -/
theorem isAlternative_cay (C : ConicAlgebra k B) (μ : k) (hconj : C.ConjIsInvolution) :
    IsAlternative (Cay C μ) :=
  isAlternative_cay_of_mul_assoc C μ (fun a b c ↦ mul_assoc a b c) hconj

end ConicAlgebra
