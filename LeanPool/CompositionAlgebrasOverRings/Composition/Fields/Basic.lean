/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Classification
public import LeanPool.CompositionAlgebrasOverRings.Conic.Division

/-!
# Composition algebras over a field: the classification mechanism (`GPR 23.12`)

Over a field the general theory of the previous layers collapses to two statements, and every
classification result in this layer is one of them applied to a field whose quadratic forms are
understood.

**Splitting is isotropy.** A composition algebra of dimension `2`, `4`, or `8` over a field is
split exactly when its norm has a nonzero null vector, equivalently exactly when it is not a
division algebra (`GPR 22.18`). Over a field the two isotropy notions of the literature agree
(`QuadraticMap.isGPRIsotropic_iff_not_anisotropic`), so no unimodularity bookkeeping survives.

**The norm is a complete invariant.** Two composition algebras over a field with isometric norm
forms are isomorphic; this is Layer 9 applied with `isLGRing_of_field`.

Together these reduce classification over a particular field to two questions about quadratic
forms over that field: which forms of dimension `2`, `4`, `8` are isotropic, and which anisotropic
ones occur as norms.

⚠ **On "division".** Each division statement below comes in two forms: one with
`ConicAlgebra.HasTwoSidedInverses` — every nonzero element has a two-sided inverse — and one with
`IsDivision`, division in the sense of `GPR 8.6`. In general the first is weaker, but composition
algebras are alternative, so the two agree once `1 ≠ 0` (`GPR 13.8`,
`ConicAlgebra.IsComposition.isDivision_iff_hasTwoSidedInverses`), proved in this file); the
`IsDivision` forms are derived from the others by that equivalence.

## Main results

* `ConicAlgebra.IsComposition.isSplitOfRank_iff_not_anisotropic` : **`GPR 22.18`** over a field,
  in dimensions.
* `ConicAlgebra.IsComposition.isSplitOfRank_of_forall_not_anisotropic` : the `u`-invariant
  mechanism — if all forms of the relevant dimension over `K` are isotropic, every composition
  algebra of that dimension is split.
* `ConicAlgebra.IsComposition.isSplitOfRank_or_isDivision`,
  `ConicAlgebra.IsComposition.isSplitOfRank_or_hasTwoSidedInverses` : the dichotomy — over a field a
  composition algebra of dimension `2`, `4`, or `8` is split or a division algebra, never both.
* `ConicAlgebra.IsComposition.isSplitOfRank_iff_not_isDivision` : **`GPR 22.18`** over a field, with
  division in the sense of `GPR 8.6`.
* `ConicAlgebra.IsComposition.isDivision_iff_hasTwoSidedInverses` : **`GPR 13.8`** for composition
  algebras over a field.
* `ConicAlgebra.mul_assoc_of_finrank_eq_two`, `ConicAlgebra.mul_comm_of_finrank_eq_two` : a
  two-dimensional conic algebra over a field is an associative commutative algebra (`GPR 16.4`).
* `ConicAlgebra.IsSplitOfRank.isomorphic` : the split algebra of a given dimension is unique.
* `ConicAlgebra.IsComposition.isomorphic_of_isometryEquiv` : composition algebras over a field
  with isometric norms are isomorphic (Layer 9 over a field).
* `ConicAlgebra.IsComposition.isomorphic_iff_nonempty_isometryEquiv` : the two previous results
  combined — isomorphism and norm isometry are the same relation over a field.

## Implementation notes

The results of Layers 9 and 10 are stated with `Module.rankAtStalk`, which over a field is
`Module.finrank` (`Module.rankAtStalk_eq_of_finrank_eq`). This file performs that translation once
so that the field-specific files can speak about dimensions throughout.

⚠ Dimension one is excluded from the splitting criterion, not overlooked: the rank-one algebra is
the base field, it is split and a division algebra at once, and its norm `x ↦ x²` is anisotropic.
`GPR 22.18` states the equivalence for dimensions greater than one for exactly this reason.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 8.6, 13.8, 16.4,
  19.3, 19.18, 22.18, 23.12.
-/

@[expose] public section

universe u v w

namespace ConicAlgebra

variable {K : Type u} {A : Type v} {B : Type w} [Field K]
  [NonAssocRing A] [Module K A] [SMulCommClass K A A] [IsScalarTower K A A]
  [Module.Finite K A] [Module.Projective K A]
  [NonAssocRing B] [Module K B] [SMulCommClass K B B] [IsScalarTower K B B]
  [Module.Finite K B] [Module.Projective K B]
  {C : ConicAlgebra K A} {D : ConicAlgebra K B} {r : ℕ}

/-! ### Splitting is isotropy -/

/-- **`GPR 22.18` over a field.** A composition algebra of dimension `2`, `4`, or `8` over a field
is split if and only if its norm has a nonzero null vector.

This is the constant-rank equivalence over an LG ring, with `Module.rankAtStalk` traded for
`Module.finrank` and GPR's unimodular isotropy traded for mathlib's failure of anisotropy — the
two agree over a field. -/
theorem IsComposition.isSplitOfRank_iff_not_anisotropic (h : C.IsComposition.{u, v, u})
    (hA : Module.finrank K A = r) (hr : r = 2 ∨ r = 4 ∨ r = 8) :
    C.IsSplitOfRank r ↔ ¬ C.norm.Anisotropic :=
  (h.isSplitOfRank_iff_isGPRIsotropic_of_isLGRing (isLGRing_of_field K)
      (Module.rankAtStalk_eq_of_finrank_eq hA) hr).trans
    QuadraticMap.isGPRIsotropic_iff_not_anisotropic

/-- **`GPR 22.18` over a field**, in the form used by every classification below: a nonzero null
vector splits a composition algebra of dimension `2`, `4`, or `8`. -/
theorem IsComposition.isSplitOfRank_of_exists_ne_zero_norm_eq_zero
    (h : C.IsComposition.{u, v, u}) (hA : Module.finrank K A = r) (hr : r = 2 ∨ r = 4 ∨ r = 8)
    {x : A} (hx : x ≠ 0) (hnx : C.norm x = 0) : C.IsSplitOfRank r :=
  (h.isSplitOfRank_iff_not_anisotropic hA hr).mpr fun hani ↦ hx (hani x hnx)

/-- **The `u`-invariant mechanism.** If every quadratic form on a `K`-space of dimension `r` is
isotropic, then every composition algebra of dimension `r ∈ {2, 4, 8}` over `K` is split.

This is how every "large enough dimension" classification in this layer is applied: over a finite
field the hypothesis holds for `r ≥ 3` (Chevalley–Warning,
`QuadraticForm.not_anisotropic_of_two_lt_finrank`), and over a local field it holds for `r ≥ 5`,
which covers the octonion case `r = 8`. -/
theorem IsComposition.isSplitOfRank_of_forall_not_anisotropic (h : C.IsComposition.{u, v, u})
    (hA : Module.finrank K A = r) (hr : r = 2 ∨ r = 4 ∨ r = 8)
    (hiso : ∀ (V : Type v) [AddCommGroup V] [Module K V], Module.finrank K V = r →
      ∀ q : QuadraticForm K V, ¬ q.Anisotropic) : C.IsSplitOfRank r :=
  (h.isSplitOfRank_iff_not_anisotropic hA hr).mpr (hiso A hA C.norm)

/-- **The dichotomy of `GPR 22.18`.** Over a field a composition algebra of dimension `2`, `4`, or
`8` is either split or a division algebra. -/
theorem IsComposition.isSplitOfRank_or_hasTwoSidedInverses (h : C.IsComposition.{u, v, u})
    (hA : Module.finrank K A = r) (hr : r = 2 ∨ r = 4 ∨ r = 8) :
    C.IsSplitOfRank r ∨ C.HasTwoSidedInverses := by
  by_cases hs : C.IsSplitOfRank r
  · exact Or.inl hs
  · exact Or.inr (h.isMultiplicative.hasTwoSidedInverses_iff_anisotropic.mpr
      (not_not.mp ((not_congr (h.isSplitOfRank_iff_not_anisotropic hA hr)).mp hs)))

/-- **The dichotomy of `GPR 22.18` is exclusive.** A split composition algebra of dimension `2`,
`4`, or `8` is not a division algebra. -/
theorem IsComposition.not_hasTwoSidedInverses_of_isSplitOfRank (h : C.IsComposition.{u, v, u})
    (hA : Module.finrank K A = r) (hr : r = 2 ∨ r = 4 ∨ r = 8) (hs : C.IsSplitOfRank r) :
    ¬ C.HasTwoSidedInverses :=
  (h.isSplitOfRank_iff_not_hasTwoSidedInverses (Module.rankAtStalk_eq_of_finrank_eq hA) hr).mp hs

/-! ### Division in the sense of `GPR 8.6`

The theorems above are stated with `ConicAlgebra.HasTwoSidedInverses`. For a composition algebra
over a field that is `GPR`'s division property: composition algebras are alternative (`GPR 19.3`),
so `GPR 13.8` applies. The statements below are the same theorems with `GPR`'s `IsDivision`. -/

/-- **`GPR 13.8` for composition algebras over a field.** A nonzero composition algebra is a
division algebra in the sense of `GPR 8.6` exactly when every nonzero element has a two-sided
inverse, since composition algebras are alternative (`ConicAlgebra.IsComposition.isAlternative`). -/
theorem IsComposition.isDivision_iff_hasTwoSidedInverses [Nontrivial A]
    (h : C.IsComposition.{u, v, u}) : IsDivision A ↔ C.HasTwoSidedInverses :=
  have := h.isAlternative
  C.isDivision_iff_hasTwoSidedInverses.trans (and_iff_right inferInstance)

/-- **The dichotomy of `GPR 22.18`, with `GPR 8.6`'s division.** Over a field a composition algebra
of dimension `2`, `4`, or `8` is either split or a division algebra. -/
theorem IsComposition.isSplitOfRank_or_isDivision (h : C.IsComposition.{u, v, u})
    (hA : Module.finrank K A = r) (hr : r = 2 ∨ r = 4 ∨ r = 8) :
    C.IsSplitOfRank r ∨ IsDivision A :=
  have : Nontrivial A := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  (h.isSplitOfRank_or_hasTwoSidedInverses hA hr).imp_right h.isDivision_iff_hasTwoSidedInverses.mpr

/-- **A split composition algebra of dimension `2`, `4`, or `8` is not a division algebra** in the
sense of `GPR 8.6`. -/
theorem IsComposition.not_isDivision_of_isSplitOfRank (h : C.IsComposition.{u, v, u})
    (hA : Module.finrank K A = r) (hr : r = 2 ∨ r = 4 ∨ r = 8) (hs : C.IsSplitOfRank r) :
    ¬ IsDivision A := fun hdiv ↦
  h.not_hasTwoSidedInverses_of_isSplitOfRank hA hr hs (C.hasTwoSidedInverses_of_isDivision hdiv)

/-- **`GPR 22.18` over a field, with `GPR 8.6`'s division**: a composition algebra of dimension
`2`, `4`, or `8` is split exactly when it is not a division algebra. -/
theorem IsComposition.isSplitOfRank_iff_not_isDivision (h : C.IsComposition.{u, v, u})
    (hA : Module.finrank K A = r) (hr : r = 2 ∨ r = 4 ∨ r = 8) :
    C.IsSplitOfRank r ↔ ¬ IsDivision A :=
  ⟨h.not_isDivision_of_isSplitOfRank hA hr, (h.isSplitOfRank_or_isDivision hA hr).resolve_right⟩

/-! ### Algebras of dimension two are commutative and associative -/

/-- **`GPR 16.4` in dimension two.** A two-dimensional conic algebra over a field is associative:
it is generated by one element (`ConicAlgebra.mul_assoc_of_isLGRing_of_rankAtStalk_eq_two`). -/
theorem mul_assoc_of_finrank_eq_two (C : ConicAlgebra K A) (hA : Module.finrank K A = 2) :
    ∀ x y z : A, x * y * z = x * (y * z) :=
  C.mul_assoc_of_isLGRing_of_rankAtStalk_eq_two (isLGRing_of_field K)
    (Module.rankAtStalk_eq_of_finrank_eq hA)

/-- **`GPR 16.4` in dimension two.** A two-dimensional conic algebra over a field is commutative:
it is generated by one element (`ConicAlgebra.mul_comm_of_isLGRing_of_rankAtStalk_eq_two`). -/
theorem mul_comm_of_finrank_eq_two (C : ConicAlgebra K A) (hA : Module.finrank K A = 2) :
    ∀ x y : A, x * y = y * x :=
  C.mul_comm_of_isLGRing_of_rankAtStalk_eq_two (isLGRing_of_field K)
    (Module.rankAtStalk_eq_of_finrank_eq hA)

/-! ### The norm is a complete invariant -/

omit [SMulCommClass K A A] [IsScalarTower K A A] [SMulCommClass K B B] [IsScalarTower K B B]
  [Module.Finite K A] [Module.Projective K A] [Module.Finite K B] [Module.Projective K B] in
/-- **Uniqueness of the split algebra.** Two conic algebras split of the same dimension are
isomorphic, because both are isomorphic to the same standard model of `GPR 21.19`. -/
theorem IsSplitOfRank.isomorphic (hC : C.IsSplitOfRank r) (hD : D.IsSplitOfRank r)
    (hr : r = 1 ∨ r = 2 ∨ r = 4 ∨ r = 8) : C.Isomorphic D := by
  rcases hr with rfl | rfl | rfl | rfl
  exacts [(isSplitOfRank_one_iff.mp hC).trans (isSplitOfRank_one_iff.mp hD).symm,
    (isSplitOfRank_two_iff.mp hC).trans (isSplitOfRank_two_iff.mp hD).symm,
    (isSplitOfRank_four_iff.mp hC).trans (isSplitOfRank_four_iff.mp hD).symm,
    (isSplitOfRank_eight_iff.mp hC).trans (isSplitOfRank_eight_iff.mp hD).symm]

/-- **Layer 9 over a field.** Composition algebras over a field whose norm forms are isometric are
isomorphic. This is the converse direction of the norm classification, specialized by passing
`isLGRing_of_field`; no dimension hypothesis is needed because the isometry transports the
dimension. -/
theorem IsComposition.isomorphic_of_isometryEquiv (hC : C.IsComposition.{u, v, u})
    (hD : D.IsComposition.{u, w, u}) (e : C.norm.IsometryEquiv D.norm) : C.Isomorphic D :=
  hC.exists_isometryEquiv_map_one_map_mul (isLGRing_of_field K) C D hD e

/-- **Layer 9 over a field, both directions.** Over a field, two composition algebras are
isomorphic exactly when their norm forms are isometric. The easy direction holds over any
commutative ring; the converse is the matched-doubling argument of Layer 9. -/
theorem IsComposition.isomorphic_iff_nonempty_isometryEquiv (hC : C.IsComposition.{u, v, u})
    (hD : D.IsComposition.{u, w, u}) :
    C.Isomorphic D ↔ Nonempty (C.norm.IsometryEquiv D.norm) :=
  ⟨fun ⟨e, _, _⟩ ↦ ⟨e⟩, fun ⟨e⟩ ↦ hC.isomorphic_of_isometryEquiv hD e⟩

/-- A composition algebra over a field whose norm is isometric to that of a split algebra of
dimension `1`, `2`, `4`, or `8` is itself split of that dimension. -/
theorem IsComposition.isSplitOfRank_of_isometryEquiv (hC : C.IsComposition.{u, v, u})
    (hD : D.IsComposition.{u, w, u}) (e : C.norm.IsometryEquiv D.norm)
    (hD' : D.IsSplitOfRank r) (hr : r = 1 ∨ r = 2 ∨ r = 4 ∨ r = 8) : C.IsSplitOfRank r := by
  have h := hC.isomorphic_of_isometryEquiv hD e
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h.trans (isSplitOfRank_one_iff.mp hD'), h.trans (isSplitOfRank_two_iff.mp hD'),
    h.trans (isSplitOfRank_four_iff.mp hD'), h.trans (isSplitOfRank_eight_iff.mp hD')]

end ConicAlgebra
