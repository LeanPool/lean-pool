/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Alternative
public import LeanPool.CompositionAlgebrasOverRings.LGRing.Examples
public import LeanPool.CompositionAlgebrasOverRings.Conic.Doubling
public import LeanPool.CompositionAlgebrasOverRings.Conic.Projective
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.OrthogonalComplement
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Representation

/-!
# A regular subalgebra of a composition algebra splits off (`GPR 19.16(a)`)

Let `C` be a composition algebra over an **LG ring** `k` and let `B ⊆ C` be a unital subalgebra
whose restricted norm is **regular**. If the orthogonal complement `Bᗮ` has full support — the
precise sense in which `B` is *properly* contained in `C` — then there is a `v ∈ Bᗮ` with `n(v)`
a unit, and

  `Cay(B, -n(v)) ↪ C`,   `u + wj ↦ u + wv`,

is an injective homomorphism. This is `GPR 19.16(a)`: the doubling process, run backwards.

## The three steps

1. **Split.** `n|_B` regular makes `B` a direct summand, `C = B ⊕ Bᗮ`, with
   `n = n|_B ⊥ n|_{Bᗮ}` (`QuadraticForm/OrthogonalComplement.lean`). In particular `Bᗮ` is again
   finitely generated projective, and `n|_{Bᗮ}` is non-singular by `GN (C.8.3)`.
2. **Represent.** Over an LG ring a non-singular form on a finitely generated projective module of
   full support represents a unit (`GPR 11.26`, `QuadraticForm/Representation.lean`). Applied to
   `n|_{Bᗮ}` this produces the element `v`.
3. **Double.** `v ⊥ B` and `n(v) ∈ kˣ` are exactly the hypotheses of `GPR 18.1`
   (`Conic/Doubling.lean`), which turns `B + Bv` into a copy of `Cay(B, -n(v))`.

## Hypotheses

**Alternativity is derived, not assumed.** Every composition algebra is alternative over an
arbitrary commutative ring; `ConicAlgebra.IsComposition.isAlternative_general` supplies the
instance used by the doubling identities.

**Full support of `Bᗮ`, not `B ≠ C`.** Over a ring the two are genuinely different: on a product
ring a subalgebra may fill up one factor and not the other, and then no single `v` can work. Full
support of the complement — `F ⊗ Bᗮ ≠ 0` for every field `F ∈ k`-alg — is what the representation
lemma consumes, and it is the honest hypothesis.

**Regularity of `n|_B`, not non-singularity.** It is used twice: to split `C` at all, and, in
`ConicAlgebra.cayToAlgebra_injective`, to know that the doubled norm has vanishing radical
(`GN (C.8.3)`). Both fail for merely non-singular forms in characteristic 2.

## Main results

* `ConicAlgebra.hasFullSupport_polarOrthogonal_of_finrank_lt` : the rank criterion for the
  full-support hypothesis.
* `ConicAlgebra.IsComposition.exists_isUnit_norm_orthogonal` : steps 1–2, the element `v`.
* `ConicAlgebra.IsComposition.exists_cayToAlgebra` : **`GPR 19.16(a)`**.
* `ConicAlgebra.IsComposition.exists_cayToAlgebra_of_field` : the same over a field, where
  alternativity is automatic.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 11.26, 18.1,
  19.16(a).
* [GN] Gille, Neher, *Group schemes over LG-rings and applications to cancellation theorems and
  Azumaya algebras*, European Journal of Mathematics **11** (2025), article 42, (C.8.3), C.13(a).
-/

@[expose] public section

universe u v

open QuadraticMap (polar)

open scoped TensorProduct

namespace ConicAlgebra

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A]
  {C : ConicAlgebra k A} {B : NonAssocSubalgebra k A}

omit [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A] in
/-- The submodule underlying a unital subalgebra, as a subset of the algebra. -/
theorem mem_toSubmodule_iff {x : A} :
    x ∈ B.toNonUnitalSubalgebra.toSubmodule ↔ x ∈ B := Iff.rfl

omit [SMulCommClass k A A] [IsScalarTower k A A] [Module.Projective k A] in
/-- **`B` is properly contained in `C` at every point.** If the rank of `B` is smaller than that
of `C` over every field in `k`-alg, the orthogonal complement has full support, which is what the
representation lemma consumes.

This is the usable form of the hypothesis: over a ring, `B ≠ C` is *not* enough — on a product ring
a subalgebra can fill up one factor — and the rank inequality is exactly the pointwise statement
that it does not. -/
theorem hasFullSupport_polarOrthogonal_of_finrank_lt
    (hreg : QuadraticForm.IsGPRRegular (C.restrict B).norm)
    (hlt : ∀ (F : Type u) [Field F] [Algebra k F],
      Module.finrank F (F ⊗[k] B.toNonUnitalSubalgebra.toSubmodule) <
        Module.finrank F (F ⊗[k] A)) :
    Module.HasFullSupport k
      (C.norm.polarOrthogonal B.toNonUnitalSubalgebra.toSubmodule) := fun F _ _ ↦
  QuadraticForm.nontrivial_baseChange_polarOrthogonal hreg F (hlt F)

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- **`GPR 19.16(a)`, steps 1–2: the element `v`.**

The complement of `B` is finitely generated projective with non-singular restricted norm, so over
an LG ring the representation lemma `GPR 11.26` finds a vector of unit norm in it as soon as it has
full support. -/
theorem IsComposition.exists_isUnit_norm_orthogonal (hLG : IsLGRing k)
    (h : C.IsComposition.{u, v, u})
    (hreg : QuadraticForm.IsGPRRegular (C.restrict B).norm)
    (hsupp : Module.HasFullSupport k
      (C.norm.polarOrthogonal B.toNonUnitalSubalgebra.toSubmodule)) :
    ∃ v : A, IsUnit (C.norm v) ∧ ∀ b ∈ B, polar C.norm b v = 0 := by
  have := QuadraticForm.finite_polarOrthogonal hreg
  have := QuadraticForm.projective_polarOrthogonal hreg
  obtain ⟨w, hw⟩ := QuadraticForm.exists_isUnit_apply_of_hasFullSupport hLG
    (QuadraticForm.IsGPRNonsingular.comp_polarOrthogonal_subtype hreg h.isGPRNonsingular) hsupp
  exact ⟨(w : A), hw, fun b hb ↦ w.2 b hb⟩

/-- **`GPR 19.16(a)`.** Over an LG ring, a unital subalgebra `B` of a composition algebra `C` whose
restricted norm is regular and whose orthogonal complement has full support is doubled inside `C`:
there is a unit `μ = -n(v)` and an injective, unital, multiplicative, isometric map
`Cay(B, μ) → C`.

The map is `ConicAlgebra.cayToAlgebra`, `u + wj ↦ u + wv`; its image is the subalgebra `B + Bv`. -/
theorem IsComposition.exists_cayToAlgebra (hLG : IsLGRing k)
    (h : C.IsComposition.{u, v, u})
    (hreg : QuadraticForm.IsGPRRegular (C.restrict B).norm)
    (hsupp : Module.HasFullSupport k
      (C.norm.polarOrthogonal B.toNonUnitalSubalgebra.toSubmodule)) :
    ∃ v : A, IsUnit (C.norm v) ∧ (∀ b ∈ B, polar C.norm b v = 0) ∧
      Function.Injective (cayToAlgebra C B v) ∧
      (∀ p q : Cay (C.restrict B) (-C.norm v),
        cayToAlgebra C B v (p * q) = cayToAlgebra C B v p * cayToAlgebra C B v q) ∧
      (∀ p : Cay (C.restrict B) (-C.norm v),
        C.norm (cayToAlgebra C B v p) = ((C.restrict B).cay (-C.norm v)).norm p) := by
  let : IsAlternative A := h.isAlternative_general
  obtain ⟨v, hu, hBv⟩ := h.exists_isUnit_norm_orthogonal hLG hreg hsupp
  refine ⟨v, hu, hBv, ?_, ?_, ?_⟩
  · exact cayToAlgebra_injective hBv hu h.isMultiplicative hreg
  · exact cayToAlgebra_mul hBv C.conjIsInvolution_of_projective hu
  · exact norm_cayToAlgebra hBv h.isMultiplicative

end ConicAlgebra

namespace ConicAlgebra

section Field

variable {K : Type u} {A : Type v} [Field K] [NonAssocRing A] [Module K A]
  [SMulCommClass K A A] [IsScalarTower K A A] [Module.Finite K A] [Module.Projective K A]
  {C : ConicAlgebra K A} {B : NonAssocSubalgebra K A}

/-- **`GPR 19.16(a)` over a field**, where alternativity of `C` is automatic (`GPR 19.3`) and the
LG hypothesis is discharged by `isLGRing_of_field`. -/
theorem IsComposition.exists_cayToAlgebra_of_field (h : C.IsComposition.{u, v, u})
    (hreg : QuadraticForm.IsGPRRegular (C.restrict B).norm)
    (hsupp : Module.HasFullSupport K
      (C.norm.polarOrthogonal B.toNonUnitalSubalgebra.toSubmodule)) :
    ∃ v : A, IsUnit (C.norm v) ∧ (∀ b ∈ B, polar C.norm b v = 0) ∧
      Function.Injective (cayToAlgebra C B v) ∧
      (∀ p q : Cay (C.restrict B) (-C.norm v),
        cayToAlgebra C B v (p * q) = cayToAlgebra C B v p * cayToAlgebra C B v q) ∧
      (∀ p : Cay (C.restrict B) (-C.norm v),
        C.norm (cayToAlgebra C B v p) = ((C.restrict B).cay (-C.norm v)).norm p) :=
  h.exists_cayToAlgebra (isLGRing_of_field K) hreg hsupp

end Field

end ConicAlgebra
