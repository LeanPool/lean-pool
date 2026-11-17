/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Fields.Basic
public import LeanPool.CompositionAlgebrasOverRings.Composition.QuadraticEtale
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.FiniteField
public import Mathlib.FieldTheory.Finite.Extension

/-!
# Composition algebras over a finite field (`GPR 23.14`)

Over a finite field every quadratic form in at least three variables is isotropic
(`QuadraticForm.not_anisotropic_of_two_lt_finrank`, from Chevalley–Warning), so no composition
algebra of dimension four or eight can be a division algebra. By `GPR 22.18` every one of them is
split, hence isomorphic to `Mat₂(K)` or to the Zorn vector matrices `Zor(K)`.

What survives is dimension two, where the norm is a binary form and can be anisotropic: the
quadratic field extension of `𝔽_q` is a composition division algebra. Thus there is exactly one
composition algebra in each of the dimensions `1`, `4`, `8`, and two — the split one and a
division algebra — in dimension `2`.

⚠ **On "division".** Each division statement below comes in two forms: one with
`ConicAlgebra.HasTwoSidedInverses` — every nonzero element has a two-sided inverse — and one with
`IsDivision`, division in the sense of `GPR 8.6`. In general the first is weaker, but composition
algebras are alternative, so the two agree once `1 ≠ 0` (`GPR 13.8`,
`ConicAlgebra.IsComposition.isDivision_iff_hasTwoSidedInverses`); the `IsDivision` forms are
derived from the others by that equivalence.

## Main results

* `ConicAlgebra.IsComposition.isSplitOfRank_of_finite` : **`GPR 23.14`**, every composition
  algebra of dimension four or eight over a finite field is split.
* `ConicAlgebra.IsComposition.not_isDivision_of_finite`,
  `ConicAlgebra.IsComposition.not_hasTwoSidedInverses_of_finite` : there are no quaternion or
  octonion division algebras over a finite field.
* `ConicAlgebra.IsComposition.isomorphic_splitQuaternion_of_finite`,
  `ConicAlgebra.IsComposition.isomorphic_zor_of_finite` : the two split models are the only ones.
* `ConicAlgebra.IsComposition.isomorphic_of_finite_of_ne_two` : uniqueness — over a finite field,
  any two composition algebras of the same dimension other than two are isomorphic.
* `ConicAlgebra.IsComposition.isomorphic_of_finite_of_isDivision_two`,
  `ConicAlgebra.IsComposition.isomorphic_of_finite_of_hasTwoSidedInverses_two` : the remaining
  uniqueness statement — any two dimension-two composition division algebras are isomorphic.
* `ConicAlgebra.exists_isComposition_isDivision_not_isSplitOfRank_two`,
  `ConicAlgebra.exists_isComposition_hasTwoSidedInverses_not_isSplitOfRank_two` : the matching
  existence statement — a quadratic field extension is one.
* `ConicAlgebra.IsComposition.isSplitOfRank_or_isDivision_two`,
  `ConicAlgebra.IsComposition.isSplitOfRank_or_hasTwoSidedInverses_two` : in dimension two the
  dichotomy is genuine, and this is the only dimension in which it is.

## Implementation notes

For the dimension-two division case, `GPR 19.8` first shows that the multiplication is associative
and commutative. Anisotropy makes this quadratic algebra a field. Mathlib's
`FiniteField.algEquivExtension` then identifies it with the unique finite extension of degree two;
this includes characteristic two and avoids duplicating Artin–Schreier theory here.

Existence is supplied separately by `Composition/QuadraticEtale.lean`, which puts a conic
structure on any quadratic algebra and shows it is a composition algebra exactly when the
discriminant is a unit. Over a finite field that discriminant is always a unit, so any quadratic
field extension is a dimension-two composition division algebra. Existence and uniqueness together
give the dimension-two half of `GPR 23.14` in full.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 8.6, 13.8, 22.18,
  23.14.
-/

@[expose] public section

universe u v w

namespace ConicAlgebra

variable {K : Type u} {A : Type v} {B : Type w} [Field K] [Finite K]
  [NonAssocRing A] [Module K A] [SMulCommClass K A A] [IsScalarTower K A A]
  [Module.Finite K A] [Module.Projective K A]
  [NonAssocRing B] [Module K B] [SMulCommClass K B B] [IsScalarTower K B B]
  [Module.Finite K B] [Module.Projective K B]
  {C : ConicAlgebra K A} {D : ConicAlgebra K B} {r : ℕ}

/-- **`GPR 23.14`.** Over a finite field every composition algebra of dimension four or eight is
split. The norm is a quadratic form in more than two variables, so Chevalley–Warning produces a
nonzero null vector, and `GPR 22.18` turns that into splitness. -/
theorem IsComposition.isSplitOfRank_of_finite (h : C.IsComposition.{u, v, u})
    (hA : Module.finrank K A = r) (hr : r = 4 ∨ r = 8) : C.IsSplitOfRank r :=
  (h.isSplitOfRank_iff_not_anisotropic hA (by tauto)).mpr
    (C.norm.not_anisotropic_of_two_lt_finrank (by rcases hr with rfl | rfl <;> omega))

/-- **No quaternion or octonion division algebras over a finite field.** -/
theorem IsComposition.not_hasTwoSidedInverses_of_finite (h : C.IsComposition.{u, v, u})
    (hA : Module.finrank K A = r) (hr : r = 4 ∨ r = 8) : ¬ C.HasTwoSidedInverses :=
  h.not_hasTwoSidedInverses_of_isSplitOfRank hA (by tauto) (h.isSplitOfRank_of_finite hA hr)

/-- **`GPR 23.14`: no quaternion or octonion division algebras over a finite field**, with division
in the sense of `GPR 8.6`. -/
theorem IsComposition.not_isDivision_of_finite (h : C.IsComposition.{u, v, u})
    (hA : Module.finrank K A = r) (hr : r = 4 ∨ r = 8) : ¬ IsDivision A := fun hdiv ↦
  h.not_hasTwoSidedInverses_of_finite hA hr (C.hasTwoSidedInverses_of_isDivision hdiv)

/-- **Every quaternion algebra over a finite field is `Mat₂(K)`.** -/
theorem IsComposition.isomorphic_splitQuaternion_of_finite (h : C.IsComposition.{u, v, u})
    (hA : Module.finrank K A = 4) : C.Isomorphic (splitQuaternion K) :=
  isSplitOfRank_four_iff.mp (h.isSplitOfRank_of_finite hA (Or.inl rfl))

/-- **Every octonion algebra over a finite field is the split one**, the algebra `Zor(K)` of Zorn
vector matrices. -/
theorem IsComposition.isomorphic_zor_of_finite (h : C.IsComposition.{u, v, u})
    (hA : Module.finrank K A = 8) : C.Isomorphic (zor K) :=
  isSplitOfRank_eight_iff.mp (h.isSplitOfRank_of_finite hA (Or.inr rfl))

/-- **Uniqueness away from dimension two.** Over a finite field any two composition algebras of
the same dimension `1`, `4`, or `8` are isomorphic.

Dimension one is the base field itself (`GPR 19.19`); dimensions four and eight are split by
`GPR 23.14`, and the split algebra of a given dimension is unique. -/
theorem IsComposition.isomorphic_of_finite_of_ne_two (hC : C.IsComposition.{u, v, u})
    (hD : D.IsComposition.{u, w, u}) (hA : Module.finrank K A = r)
    (hB : Module.finrank K B = r) (hr : r = 1 ∨ r = 4 ∨ r = 8) : C.Isomorphic D := by
  rcases hr with rfl | hr
  · exact (isSplitOfRank_one (Module.rankAtStalk_eq_of_finrank_eq hA)).isomorphic
      (isSplitOfRank_one (Module.rankAtStalk_eq_of_finrank_eq hB)) (Or.inl rfl)
  · exact (hC.isSplitOfRank_of_finite hA hr).isomorphic (hD.isSplitOfRank_of_finite hB hr)
      (by tauto)

/-- **The dimension-two division composition algebra over a finite field is unique.**

By `GPR 19.8`, each algebra is associative and commutative. Its anisotropic multiplicative norm
rules out zero divisors, so module-finiteness makes it a field extension of `K`. Mathlib's
classification of finite-field extensions then supplies a `K`-algebra equivalence between the two
degree-two fields. Uniqueness of the conic norm on a finite projective algebra turns this
equivalence into an isomorphism of composition algebras. -/
theorem IsComposition.isomorphic_of_finite_of_hasTwoSidedInverses_two
    (hC : C.IsComposition.{u, v, u}) (hD : D.IsComposition.{u, w, u})
    (hA : Module.finrank K A = 2) (hB : Module.finrank K B = 2)
    (hCdiv : C.HasTwoSidedInverses) (hDdiv : D.HasTwoSidedInverses) : C.Isomorphic D := by
  let : CommRing A :=
    { (inferInstance : NonAssocRing A) with
      mul_assoc := C.mul_assoc_of_finrank_eq_two hA
      mul_comm := C.mul_comm_of_finrank_eq_two hA }
  let : Algebra K A := Algebra.ofModule (fun r x y ↦ by exact smul_mul_assoc r x y)
    (fun r x y ↦ by exact mul_smul_comm r x y)
  let : Nontrivial A := Module.nontrivial_of_finrank_pos (by rw [hA]; omega)
  let : NoZeroDivisors A :=
    (hC.isMultiplicative.anisotropic_iff_noZeroDivisors_of_isDomain).mp
      (hC.isMultiplicative.hasTwoSidedInverses_iff_anisotropic.mp hCdiv)
  let : IsDomain A := NoZeroDivisors.to_isDomain A
  let : Field A := (IsField.of_isDomain_of_finite K A).toField
  let : CommRing B :=
    { (inferInstance : NonAssocRing B) with
      mul_assoc := D.mul_assoc_of_finrank_eq_two hB
      mul_comm := D.mul_comm_of_finrank_eq_two hB }
  let : Algebra K B := Algebra.ofModule (fun r x y ↦ by exact smul_mul_assoc r x y)
    (fun r x y ↦ by exact mul_smul_comm r x y)
  let : Nontrivial B := Module.nontrivial_of_finrank_pos (by rw [hB]; omega)
  let : NoZeroDivisors B :=
    (hD.isMultiplicative.anisotropic_iff_noZeroDivisors_of_isDomain).mp
      (hD.isMultiplicative.hasTwoSidedInverses_iff_anisotropic.mp hDdiv)
  let : IsDomain B := NoZeroDivisors.to_isDomain B
  let : Field B := (IsField.of_isDomain_of_finite K B).toField
  let ⟨p, hp⟩ := CharP.exists K
  let : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  let : CharP K p := hp
  let e : A ≃ₐ[K] B :=
    (FiniteField.algEquivExtension K p 2 A hA).trans
      (FiniteField.algEquivExtension K p 2 B hB).symm
  exact ⟨isometryEquivOfAlgEquiv C D e, e.map_one, e.map_mul⟩

/-- **Existence of the non-split composition algebra in dimension two.** A quadratic field
extension of a finite field, with the conic structure of `GPR 19.8`, is a composition division
algebra, and in particular is not split.

The discriminant of such an extension is a unit in every characteristic
(`ConicAlgebra.IsQuadraticAlgebra.isUnit_discriminant_of_finite`), which is what makes it a
composition algebra; being a field it has no zero divisors, so its norm is anisotropic. Together
with `isomorphic_of_finite_of_hasTwoSidedInverses_two` this completes `GPR 23.14` in dimension two:
the division algebra exists and is unique. -/
theorem exists_isComposition_hasTwoSidedInverses_not_isSplitOfRank_two {L : Type w} [Field L]
    [Algebra K L] (hL : Module.finrank K L = 2) :
    ∃ (_ : Module.Finite K L) (_ : Module.Projective K L) (E : ConicAlgebra K L),
      E.IsComposition.{u, w, u} ∧ E.HasTwoSidedInverses ∧ ¬ E.IsSplitOfRank 2 := by
  obtain ⟨u, t, n₀, hq⟩ := exists_isQuadraticAlgebra_of_finrank_eq_two hL
  have := hq.module_free
  have := hq.module_finite
  have : Module.Projective K L := inferInstance
  have hcomp := hq.isComposition_conic hq.isUnit_discriminant_of_finite
  have hani : hq.conic.norm.Anisotropic :=
    hcomp.isMultiplicative.anisotropic_iff_noZeroDivisors_of_isDomain.mpr inferInstance
  refine ⟨inferInstance, inferInstance, hq.conic, hcomp,
    hcomp.isMultiplicative.hasTwoSidedInverses_iff_anisotropic.mpr hani, ?_⟩
  rw [hcomp.isSplitOfRank_iff_not_anisotropic hL (Or.inl rfl)]
  exact not_not.mpr hani

omit [Finite K] in
/-- **Dimension two is where the dichotomy of `GPR 22.18` survives over a finite field.** A
two-dimensional composition algebra over a finite field is split or a division algebra; both occur,
the second being the quadratic field extension of the base. -/
theorem IsComposition.isSplitOfRank_or_hasTwoSidedInverses_two (h : C.IsComposition.{u, v, u})
    (hA : Module.finrank K A = 2) : C.IsSplitOfRank 2 ∨ C.HasTwoSidedInverses :=
  h.isSplitOfRank_or_hasTwoSidedInverses hA (Or.inl rfl)

/-! ### The same, with division in the sense of `GPR 8.6` -/

/-- **The dimension-two division composition algebra over a finite field is unique**, with
division in the sense of `GPR 8.6`. -/
theorem IsComposition.isomorphic_of_finite_of_isDivision_two
    (hC : C.IsComposition.{u, v, u}) (hD : D.IsComposition.{u, w, u})
    (hA : Module.finrank K A = 2) (hB : Module.finrank K B = 2)
    (hCdiv : IsDivision A) (hDdiv : IsDivision B) : C.Isomorphic D :=
  hC.isomorphic_of_finite_of_hasTwoSidedInverses_two hD hA hB
    (C.hasTwoSidedInverses_of_isDivision hCdiv) (D.hasTwoSidedInverses_of_isDivision hDdiv)

/-- **A dimension-two division composition algebra exists over a finite field**, with division in
the sense of `GPR 8.6`: the quadratic field extension. -/
theorem exists_isComposition_isDivision_not_isSplitOfRank_two {L : Type w} [Field L]
    [Algebra K L] (hL : Module.finrank K L = 2) :
    ∃ (_ : Module.Finite K L) (_ : Module.Projective K L) (E : ConicAlgebra K L),
      E.IsComposition.{u, w, u} ∧ IsDivision L ∧ ¬ E.IsSplitOfRank 2 := by
  obtain ⟨_, _, E, hE, hinv, hns⟩ :=
    exists_isComposition_hasTwoSidedInverses_not_isSplitOfRank_two (K := K) hL
  exact ⟨‹_›, ‹_›, E, hE, hE.isDivision_iff_hasTwoSidedInverses.mpr hinv, hns⟩

omit [Finite K] in
/-- **`GPR 23.14` in dimension two, with `GPR 8.6`'s division**: a two-dimensional composition
algebra over a finite field is split or a division algebra. -/
theorem IsComposition.isSplitOfRank_or_isDivision_two (h : C.IsComposition.{u, v, u})
    (hA : Module.finrank K A = 2) : C.IsSplitOfRank 2 ∨ IsDivision A :=
  h.isSplitOfRank_or_isDivision hA (Or.inl rfl)

end ConicAlgebra
