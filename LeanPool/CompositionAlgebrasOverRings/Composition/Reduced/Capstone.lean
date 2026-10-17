/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.RankTwoSubalgebra
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Classification

/-!
# Splitting octonion algebras from their quadratic étale subalgebras

This file formalizes the final paragraph of `GN Example 3.15`. Let `k` be an LG ring over which
every quadratic étale algebra is split. A rank-eight composition algebra contains a regular
rank-two composition subalgebra by `GPR 19.16(b)`. The hypothesis makes that subalgebra split, so
an elementary idempotent in it gives one in the ambient algebra. The reduced classification
`GPR 22.16` then makes the octonion algebra split.

The hypothesis is stated only for the regular rank-two subalgebras `k[u]` which the proof
consumes. This avoids replacing the mathematical condition by the stronger assertion that every
rank-two conic algebra, with arbitrary norm data, is split.

## Main results

* `ConicAlgebra.IsComposition.isSplitOfRank_of_forall_isSplit_adjoinElement` : every composition
  algebra of constant rank two, four, or eight over the stated LG ring is split.
* `ConicAlgebra.IsComposition.isSplitOfRank_eight_of_forall_isSplit_adjoinElement` : every
  rank-eight composition algebra over the stated LG ring is split.

## Implementation notes

The conic norm bundled by `GPR 19.16(b)` is initially existential. Its uniqueness on the finite
projective quadratic subalgebra identifies it with the ambient restricted norm (`GPR 19.8`),
which is the step that transports the elementary idempotent into the octonion algebra.

## References

* [GN] Gille, Neher, *Group schemes over LG-rings and applications to cancellation theorems and
  Azumaya algebras*, European Journal of Mathematics **11** (2025), article 42, Example 3.15.
* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 19.8, 19.16(b),
  22.9, 22.16.
-/

@[expose] public section

universe u v

namespace ConicAlgebra

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A]
  [Module.Finite k A] [Module.Projective k A]
  {C : ConicAlgebra k A}

omit [Module.Finite k A] [Module.Projective k A] in
/-- An elementary idempotent of a regular quadratic subalgebra remains elementary in the ambient
conic algebra. The substantive input is uniqueness of the conic norm on the finite projective
subalgebra (`GPR 19.8`). -/
theorem RegularRankTwoCompositionStructure.isElementaryIdempotent_ambient {u : A}
    (h : C.RegularRankTwoCompositionStructure u) {c : C.adjoinElement u}
    (hc : h.conic.IsElementaryIdempotent c) : C.IsElementaryIdempotent (c : A) := by
  have hnorm := h.conic_norm_eq_normAdjoinElement
  constructor
  · rw [← C.normAdjoinElement_apply u c, ← hnorm]
    exact hc.norm_eq_zero
  · have htrace := hc.trace_eq_one
    rw [trace_apply, hnorm] at htrace
    rw [trace_apply]
    exact htrace

/-- **Final paragraph of `GN Example 3.15`, in every constant rank greater than one.** Let `k` be
an LG ring such that every regular rank-two composition subalgebra `k[u]` is split. Then every
composition algebra over `k` of constant rank `2`, `4`, or `8` is split.

The hypothesis is precisely the "every quadratic étale algebra is split" input needed by the
proof, specialized to the subalgebras produced by `GPR 19.16(b)`. Over a field this is the class
of fields — separably closed fields among them — over which `GPR 23.12` gives a unique composition
algebra in each dimension. -/
theorem IsComposition.isSplitOfRank_of_forall_isSplit_adjoinElement {r : ℕ}
    (hcomp : C.IsComposition.{u, v, u}) (hLG : IsLGRing k)
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r) (hr : r = 2 ∨ r = 4 ∨ r = 8)
    (hsplit : ∀ (u : A) (h : C.RegularRankTwoCompositionStructure u),
      letI := C.adjoinElementCommRing u
      letI := C.adjoinElementAlgebra u
      letI : Module.Finite k (C.adjoinElement u) := C.finite_adjoinElement u
      letI : Module.Projective k (C.adjoinElement u) := h.projective
      h.conic.IsSplitOfRank 2) : C.IsSplitOfRank r := by
  rcases subsingleton_or_nontrivial k with hk | hk
  · let := hk
    rcases hr with rfl | rfl | rfl <;> exact Isomorphic.of_subsingleton
  let := hk
  obtain ⟨u, ⟨h⟩⟩ := hcomp.exists_isRegularRankTwoComposition_of_rankAtStalk hLG (by
    intro p
    simp only [hA]
    rcases hr with rfl | rfl | rfl <;> omega)
  let := C.adjoinElementCommRing u
  let := C.adjoinElementAlgebra u
  let : Module.Finite k (C.adjoinElement u) := C.finite_adjoinElement u
  let : Module.Projective k (C.adjoinElement u) := h.projective
  obtain ⟨c, hc⟩ :=
    (hsplit u h).hasElementaryIdempotent_of_two_or_four_or_eight (Or.inl rfl)
  have hcA : C.IsElementaryIdempotent (c : A) :=
    h.isElementaryIdempotent_ambient hc
  have hreg := hcomp.isGPRRegular_of_rankAtStalk_ne_one hA
    (by rcases hr with rfl | rfl | rfl <;> omega)
  let : IsAlternative A :=
    hcomp.isMultiplicative.isAlternative hreg.isGPRNondegenerate
  rcases hr with rfl | rfl | rfl
  · exact hcA.isSplitOfRank_two hA
  · exact hcA.isSplitOfRank_four_of_isLGRing hLG hcomp hA
  · exact hcA.isSplitOfRank_eight_of_isLGRing hLG hcomp hA

/-- **Final paragraph of `GN Example 3.15`.** Let `k` be an LG ring such that every regular
rank-two composition subalgebra `k[u]` is split. Then every constant-rank-eight composition
algebra over `k` is split. This is the octonion case of
`ConicAlgebra.IsComposition.isSplitOfRank_of_forall_isSplit_adjoinElement`, and it is the
statement `GN Example 3.15` makes for the ring of all algebraic integers. -/
theorem IsComposition.isSplitOfRank_eight_of_forall_isSplit_adjoinElement
    (hcomp : C.IsComposition.{u, v, u}) (hLG : IsLGRing k)
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 8)
    (hsplit : ∀ (u : A) (h : C.RegularRankTwoCompositionStructure u),
      letI := C.adjoinElementCommRing u
      letI := C.adjoinElementAlgebra u
      letI : Module.Finite k (C.adjoinElement u) := C.finite_adjoinElement u
      letI : Module.Projective k (C.adjoinElement u) := h.projective
      h.conic.IsSplitOfRank 2) : C.IsSplitOfRank 8 :=
  hcomp.isSplitOfRank_of_forall_isSplit_adjoinElement hLG hA (Or.inr (Or.inr rfl)) hsplit

end ConicAlgebra
