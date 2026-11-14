/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.RankDichotomy
public import LeanPool.CompositionAlgebrasOverRings.Module.RankDecomposition

/-!
# Composition algebras are alternative, over an arbitrary commutative ring

`Composition/Basic.lean` derives alternativity (`GPR 19.3`) from non-singularity in the two cases
where non-singularity yields a vanishing radical: over a field, and over a ring in which `2` is
invertible. This file removes both restrictions, for **every** composition algebra: no hypothesis
on `2`, none on the rank, and none on the base ring beyond commutativity.

## Why the general case is not a descent

`GPR 19.3` itself is *not* a statement about composition algebras. Its hypothesis is that the norm
be **non-degenerate** in the sense of `GPR 11.11` — the radical vanishes — and in that form it is
already proved in full generality here (`ConicAlgebra.IsMultiplicative.isAlternative`, in
`Conic/Kirmse.lean`). What a composition algebra supplies is **non-singularity**, which over a ring
does not imply it, and `GPR 19.6` shows the two genuinely differ: the base ring `k = 𝔽₂[t]/(t²)` is
a composition algebra over itself whose norm has `t` in its radical. So no argument can derive a
vanishing radical from the definition, and the residue-field descent once proposed for this cannot
work — `t` is nilpotent and dies in every field over that ring.

`GPR 19.7(c)` says what is true instead: it is the **regular** composition algebras that are
alternative, via `GPR 19.3`. Regularity gives a vanishing radical for free and with no hypothesis
on `2`, since the radical is contained in the kernel of the polar form
(`QuadraticForm.IsGPRRegular.isGPRNondegenerate`).

## Closing the gap

That leaves only the algebras `GPR 19.11` excludes from regularity, and they are harmless. If a
composition algebra has constant rank `r`, then either its norm is regular — and alternativity
follows as above — or `r = 1`. In rank one every element is a scalar multiple of the identity
(`ConicAlgebra.eq_unitForm_smul_one_of_rankAtStalk_eq_one`), so the algebra is commutative and
associative outright, hence alternative. `𝔽₂[t]/(t²)` is exactly such an algebra: it is alternative,
just not for the reason `GPR 19.3` gives.

The two cases together prove alternativity for every constant-rank composition algebra over a
nontrivial commutative ring. The constant-rank hypothesis then comes off by the rank decomposition
`GPR Exc. 9.31`, and the base ring need not be nontrivial: over the zero ring the index set of the
decomposition is empty and the module is a subsingleton, so the argument is vacuously fine.

## Main results

* `ConicAlgebra.IsComposition.isAlternative_of_isGPRRegular` : **`GPR 19.7(c)`** — a regular
  composition algebra is alternative, over any commutative ring.
* `ConicAlgebra.mul_assoc_of_rankAtStalk_eq_one`, `ConicAlgebra.mul_comm_of_rankAtStalk_eq_one` :
  a constant-rank-one conic algebra is associative and commutative.
* `ConicAlgebra.IsComposition.isAlternative_of_rankAtStalk` : alternativity of a composition
  algebra of constant rank over a nontrivial commutative ring.
* `ConicAlgebra.IsComposition.isAlternative_general` : **alternativity of an arbitrary composition
  algebra over an arbitrary commutative ring**, the constant-rank hypothesis removed by the rank
  decomposition.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 19.3, 19.6,
  19.7(c), 19.11, Exc. 9.31.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace ConicAlgebra

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A]
  {C : ConicAlgebra k A}

/-- **`GPR 19.7(c)`.** A composition algebra whose norm is *regular* is alternative, over an
arbitrary commutative ring and with no hypothesis on `2`.

Regularity means the polar form is injective into the dual, and the radical is contained in its
kernel, so the radical vanishes — which is precisely the hypothesis of `GPR 19.3`. -/
theorem IsComposition.isAlternative_of_isGPRRegular (h : C.IsComposition.{u, v, u})
    (hreg : C.norm.IsGPRRegular) : IsAlternative A :=
  h.isMultiplicative.isAlternative hreg.isGPRNondegenerate

section RankOne

/-- A conic algebra of constant rank one is **associative**: every element is a scalar multiple of
the identity, so every product is too. -/
theorem mul_assoc_of_rankAtStalk_eq_one [Nontrivial k] (C : ConicAlgebra k A)
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 1) (x y z : A) :
    x * y * z = x * (y * z) := by
  have hx := C.eq_unitForm_smul_one_of_rankAtStalk_eq_one hA x
  have hy := C.eq_unitForm_smul_one_of_rankAtStalk_eq_one hA y
  have hz := C.eq_unitForm_smul_one_of_rankAtStalk_eq_one hA z
  rw [hx, hy, hz]
  simp only [smul_mul_smul_comm, one_mul, mul_assoc]

/-- A conic algebra of constant rank one is **commutative**, for the same reason. -/
theorem mul_comm_of_rankAtStalk_eq_one [Nontrivial k] (C : ConicAlgebra k A)
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 1) (x y : A) : x * y = y * x := by
  have hx := C.eq_unitForm_smul_one_of_rankAtStalk_eq_one hA x
  have hy := C.eq_unitForm_smul_one_of_rankAtStalk_eq_one hA y
  rw [hx, hy]
  simp only [smul_mul_smul_comm, one_mul, mul_comm]

/-- A conic algebra of constant rank one is alternative, being associative. -/
theorem isAlternative_of_rankAtStalk_eq_one [Nontrivial k] (C : ConicAlgebra k A)
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 1) : IsAlternative A where
  left_alt a b := (mul_assoc_of_rankAtStalk_eq_one C hA a a b).symm
  right_alt a b := mul_assoc_of_rankAtStalk_eq_one C hA b a a

end RankOne

/-- **Composition algebras of constant rank are alternative over an arbitrary nontrivial
commutative ring**, with no hypothesis on `2`.

`GPR 19.11` splits the problem in two: either the norm is regular, and `GPR 19.7(c)` applies, or
the rank is one, and the algebra is associative because every element is a scalar. The second case
is not vacuous — over `𝔽₂[t]/(t²)` the base ring is a composition algebra whose norm is not
regular (`GPR 19.6`) — which is why it has to be handled separately rather than by weakening the
regularity hypothesis. -/
theorem IsComposition.isAlternative_of_rankAtStalk [Nontrivial k] (h : C.IsComposition.{u, v, u})
    {r : ℕ} (hrank : Module.rankAtStalk (R := k) A = fun _ ↦ r) : IsAlternative A := by
  rcases h.isGPRRegular_or_rank_eq_one hrank with hreg | ⟨hr, -⟩
  · exact h.isAlternative_of_isGPRRegular hreg
  · subst hr
    exact isAlternative_of_rankAtStalk_eq_one C hrank

/-! ### Removing the constant-rank hypothesis

`GPR Exc. 9.31` splits `k` into the finitely many factors `kᵢ = k ⧸ (1 - εᵢ)` on which `A` has
constant rank `i`, and each `kᵢ ⊗ A` is again a composition algebra, of constant rank `i`. So each
factor is alternative by the theorem above.

Transporting *back* is where an equation is easier than a structure. `IsAlternative` is two
identities, and an element of `A` vanishes as soon as it vanishes in every factor
(`Module.eq_zero_of_forall_rankIdempotent_smul_eq_zero`,
`Module.rankIdempotent_smul_eq_zero_of_one_tmul_eq_zero`); the map `x ↦ 1 ⊗ x` carries products to
products by `Algebra.TensorProduct.tmul_mul_tmul`, so it carries each alternative law to the
corresponding one. No product decomposition of the algebra has to be built. -/

section AllRanks

variable (C)

omit [Module.Finite k A] [Module.Projective k A] in
/-- The canonical map `x ↦ 1 ⊗ x` into a base change carries products to products. -/
theorem one_tmul_mul (S : Type w) [CommRing S] [Algebra k S] (x y : A) :
    (1 : S) ⊗ₜ[k] (x * y) = ((1 : S) ⊗ₜ[k] x) * ((1 : S) ⊗ₜ[k] y) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- A base change of constant rank is alternative.

The base may be the zero ring — the rank-`i` locus is empty for all but finitely many `i` — and
then the base change is a subsingleton and there is nothing to prove. -/
theorem isAlternative_baseChange_of_rankAtStalk (h : C.IsComposition.{u, v, u})
    (S : Type u) [CommRing S] [Algebra k S] {i : ℕ}
    (hrank : Module.rankAtStalk (R := S) (S ⊗[k] A) = fun _ ↦ i) :
    IsAlternative (S ⊗[k] A) := by
  rcases subsingleton_or_nontrivial S with _ | _
  · have : Subsingleton (S ⊗[k] A) := Module.subsingleton S _
    exact ⟨fun _ _ ↦ Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _⟩
  · exact (h.baseChangeOfProjective S).isAlternative_of_rankAtStalk hrank

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- Two elements agreeing in every factor of the rank decomposition are equal. -/
theorem eq_of_forall_one_tmul_eq {x y : A}
    (h : ∀ i : ℕ, (1 : k ⧸ Ideal.span {1 - Module.rankIdempotent k A i}) ⊗ₜ[k] x =
      (1 : k ⧸ Ideal.span {1 - Module.rankIdempotent k A i}) ⊗ₜ[k] y) : x = y := by
  refine sub_eq_zero.mp (Module.eq_zero_of_forall_rankIdempotent_smul_eq_zero k A fun i ↦ ?_)
  refine Module.rankIdempotent_smul_eq_zero_of_one_tmul_eq_zero k A i ?_
  rw [TensorProduct.tmul_sub, h i, sub_self]

/-- **Every composition algebra is alternative**, over an arbitrary commutative ring, with no
hypothesis on `2` and **no constant-rank hypothesis**.

By `GPR Exc. 9.31` it suffices to check each factor of the rank decomposition, where the rank is
constant; `ConicAlgebra.one_tmul_mul` carries each alternative law into the factor, and
`ConicAlgebra.eq_of_forall_one_tmul_eq` brings the conclusion back. No product decomposition of
the algebra itself has to be built. -/
theorem IsComposition.isAlternative_general (h : C.IsComposition.{u, v, u}) : IsAlternative A := by
  refine ⟨fun a b ↦ eq_of_forall_one_tmul_eq (k := k) (A := A) fun i ↦ ?_,
    fun a b ↦ eq_of_forall_one_tmul_eq (k := k) (A := A) fun i ↦ ?_⟩ <;>
  · have := isAlternative_baseChange_of_rankAtStalk C h _
      (Module.rankAtStalk_quotientTensor_rankIdempotent k A i)
    simp only [one_tmul_mul]
    first
      | exact IsAlternative.left_alt _ _
      | exact IsAlternative.right_alt _ _

end AllRanks

end ConicAlgebra
