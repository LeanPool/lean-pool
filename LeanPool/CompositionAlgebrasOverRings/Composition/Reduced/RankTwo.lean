/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.RankDichotomy
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Defs

/-!
# Reduced algebras of rank two are split (`GPR 22.10`)

**`GPR 22.10`.** *The reduced composition algebras of rank `2` over `k` are precisely the split
quadratic étale `k`-algebras.*

One direction is `ConicAlgebra.hasElementaryIdempotent_splitEtale`: `k × k` has the elementary
idempotent `(1, 0)`. This file proves the other, and proves it for conic algebras, with no
regularity or multiplicativity hypothesis at all:

> if a conic algebra of constant rank `2` has an elementary idempotent `c`, then
> `(a, b) ↦ a c + b (conj c)` is an **isomorphism** `k × k → A` of conic algebras.

The map is injective in any conic algebra (`GPR 22.9`'s proof); what rank `2` adds is surjectivity,
and it adds it through the orthogonal splitting rather than through any counting of generators: the
plane `k c ⊕ k (conj c)` has regular restricted norm, so it is a direct summand whose complement has
rank `0`, hence is trivial.

## Main results

* `ConicAlgebra.IsElementaryIdempotent.bijective_elementaryIdempotentEmbedding` : **`GPR 22.10`**,
  the embedding is bijective in constant rank `2`.
* `ConicAlgebra.IsElementaryIdempotent.splitEtaleEquiv` : the resulting isomorphism `k × k ≃ₗ A`,
  with `map_one`, `map_mul` and `norm` lemmas — an isomorphism of conic algebras.
* `ConicAlgebra.IsComposition.hasSplitEtaleSubalgebra_iff_isGPRIsotropic_of_rankAtStalk_eq_two` :
  for a composition algebra of constant rank `2`, being split is equivalent to isotropy of the
  norm. This is `GPR 22.18` in rank `2`, and the regularity `GPR 22.9` consumes is supplied by
  `GPR 19.11`, since the rank is not `1`.

## Implementation notes

Constant rank is `Module.rankAtStalk`, as everywhere else in this development, not `finrank`: over
a ring with idempotents the two differ, and it is the pointwise statement on `Spec k` that the
orthogonal-complement argument needs.

The isomorphism is delivered as a `LinearEquiv` together with three properties rather than as a
bundled algebra isomorphism: `A` is not assumed associative, so mathlib's `AlgEquiv` does not
apply, and the norm has to be carried explicitly in any case (overview §2 — the norm is data).

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 19.11, 21.19,
  22.9, 22.10, 22.18.
-/

@[expose] public section

universe u v w

namespace ConicAlgebra

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A]
  {C : ConicAlgebra k A} {c : A}

namespace IsElementaryIdempotent

variable (hc : C.IsElementaryIdempotent c)
include hc

omit [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A] in
/-- The plane `k c ⊕ k (conj c)` has constant rank `2`: it is `k × k` as a module. -/
theorem rankAtStalk_planeSubmodule :
    Module.rankAtStalk (R := k)
      (QuadraticMap.IsHyperbolicPair.planeSubmodule (R := k) c (C.conj c)) = fun _ ↦ 2 := by
  rcases subsingleton_or_nontrivial k with hk | hk
  · have := hk
    exact funext fun p ↦ (IsEmpty.false p).elim
  · rw [← Module.rankAtStalk_eq_of_equiv hc.isHyperbolicPair.planeEquiv,
      Module.rankAtStalk_prod, Module.rankAtStalk_self]
    rfl

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- **`GPR 22.10`.** In a conic algebra of constant rank `2`, an elementary idempotent generates
everything: `(a, b) ↦ a c + b (conj c)` is bijective.

Injectivity is `GPR 22.9`'s and holds always; surjectivity is the orthogonal splitting, since the
plane is regular and of full rank. No hypothesis on the norm of `C` and none on `2`. -/
theorem bijective_elementaryIdempotentEmbedding
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 2) :
    Function.Bijective (C.elementaryIdempotentEmbedding c) := by
  refine ⟨hc.injective_elementaryIdempotentEmbedding, fun x ↦ ?_⟩
  have htop := QuadraticForm.eq_top_of_isGPRRegular_of_rankAtStalk_eq
    hc.isHyperbolicPair.isGPRRegular_comp_planeSubmodule_subtype hA hc.rankAtStalk_planeSubmodule
  have hx : x ∈ QuadraticMap.IsHyperbolicPair.planeSubmodule (R := k) c (C.conj c) :=
    htop ▸ Submodule.mem_top
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy⟩

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- **`GPR 22.10`, packaged**: a conic algebra of constant rank `2` with an elementary idempotent
*is* the split quadratic étale algebra `k × k`. -/
noncomputable def splitEtaleEquiv (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 2) :
    (k × k) ≃ₗ[k] A :=
  LinearEquiv.ofBijective _ (hc.bijective_elementaryIdempotentEmbedding hA)

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp] theorem splitEtaleEquiv_apply (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 2)
    (x : k × k) : hc.splitEtaleEquiv hA x = x.1 • c + x.2 • C.conj c := rfl

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- The isomorphism of `GPR 22.10` is unital. -/
theorem splitEtaleEquiv_one (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 2) :
    hc.splitEtaleEquiv hA 1 = 1 :=
  hc.elementaryIdempotentEmbedding_one

/-- The isomorphism of `GPR 22.10` is multiplicative. -/
theorem splitEtaleEquiv_mul (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 2) (x y : k × k) :
    hc.splitEtaleEquiv hA (x * y) = hc.splitEtaleEquiv hA x * hc.splitEtaleEquiv hA y :=
  hc.elementaryIdempotentEmbedding_mul x y

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- The isomorphism of `GPR 22.10` carries the split quadratic étale norm `(a, b) ↦ ab` to the
norm of `C`. -/
theorem norm_splitEtaleEquiv (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 2) (x : k × k) :
    C.norm (hc.splitEtaleEquiv hA x) = QuadraticForm.plane k x :=
  hc.norm_elementaryIdempotentEmbedding x

end IsElementaryIdempotent

/-- **`GPR 22.10`, existence form.** A conic algebra of constant rank `2` containing a split
quadratic étale subalgebra *is* one: the subalgebra is everything. -/
theorem exists_linearEquiv_of_hasSplitEtaleSubalgebra_of_rankAtStalk_eq_two
    (hred : C.HasSplitEtaleSubalgebra) (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 2) :
    ∃ e : (k × k) ≃ₗ[k] A, e 1 = 1 ∧ (∀ x y : k × k, e (x * y) = e x * e y) ∧
      ∀ x : k × k, C.norm (e x) = QuadraticForm.plane k x := by
  obtain ⟨c, hc⟩ := hasSplitEtaleSubalgebra_iff_hasElementaryIdempotent.mp hred
  exact ⟨hc.splitEtaleEquiv hA, hc.splitEtaleEquiv_one hA, hc.splitEtaleEquiv_mul hA,
    hc.norm_splitEtaleEquiv hA⟩

/-! ### Rank two composition algebras: split ↔ isotropic norm

For a composition algebra the regularity that `GPR 22.9` consumes is not a hypothesis: `GPR 19.11`
gives it as soon as the constant rank is not `1`. So in rank `2` the chain
"split ↔ reduced ↔ isotropic norm" closes with no side conditions beyond the rank. -/

variable (C)

/-- **`GPR 22.18` in rank two.** For a composition algebra of constant rank `2`, containing a split
quadratic étale subalgebra — equivalently, by `GPR 22.10`, *being* one — is equivalent to isotropy
of the norm in `GPR`'s sense.

The regularity `GPR 22.9` needs comes from `GPR 19.11`
(`IsComposition.isGPRRegular_of_rankAtStalk_ne_one`), since `2 ≠ 1`. -/
theorem IsComposition.hasSplitEtaleSubalgebra_iff_isGPRIsotropic_of_rankAtStalk_eq_two
    (h : C.IsComposition.{u, v, u}) (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 2) :
    C.HasSplitEtaleSubalgebra ↔ C.norm.IsGPRIsotropic :=
  hasSplitEtaleSubalgebra_iff_isGPRIsotropic
    (h.isGPRRegular_of_rankAtStalk_ne_one hA (by norm_num)) h.isMultiplicative

end ConicAlgebra
