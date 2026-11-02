/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Examples
public import LeanPool.CompositionAlgebrasOverRings.Composition.Fields.Basic
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Real

/-!
# Composition algebras over the reals (`GPR 23.13`)

Over `ℝ` there is exactly one composition **division** algebra in each of the dimensions `1`, `2`,
`4`, `8` — the classical tower `ℝ, ℂ, ℍ, 𝕆` — and, besides these, only the split algebra in each of
the dimensions `2`, `4`, `8`. `GPR 23.13` notes that the same holds over any real closed field; only
`ℝ` is treated here.

Two inputs do all the work.

* **Sylvester's law of inertia.** A composition algebra which is not split has anisotropic norm, and
  an anisotropic real quadratic form taking a positive value is a sum of squares
  (`QuadraticForm.equivalent_sumSquares_of_anisotropic`). The norm takes the value `1` at the
  identity element, so it is positive definite and is determined by the dimension alone.
* **Layer 9.** Over a field, composition algebras with isometric norms are isomorphic. So the
  dimension already determines the division algebra.

Existence is the Cayley–Dickson tower at `μ₁ = μ₂ = μ₃ = -1` (`Composition/Examples.lean`), which
supplies a positive definite — hence anisotropic, hence division — composition algebra in each of
the four dimensions.

⚠ **On "division".** Each division statement below comes in two forms: one with
`ConicAlgebra.HasTwoSidedInverses` — every nonzero element has a two-sided inverse — and one with
`IsDivision`, division in the sense of `GPR 8.6`. In general the first is weaker, but composition
algebras are alternative, so the two agree once `1 ≠ 0` (`GPR 13.8`,
`ConicAlgebra.IsComposition.isDivision_iff_hasTwoSidedInverses`); the `IsDivision` forms are
derived from the others by that equivalence.

## Main results

* `ConicAlgebra.IsComposition.posDef_norm_of_isDivision`,
  `ConicAlgebra.IsComposition.posDef_norm_of_hasTwoSidedInverses` : a real composition division
  algebra has positive definite norm.
* `ConicAlgebra.IsComposition.isomorphic_of_anisotropic` : two real composition algebras with
  anisotropic norms and the same dimension are isomorphic.
* `ConicAlgebra.IsComposition.isomorphic_of_isDivision`,
  `ConicAlgebra.IsComposition.isomorphic_of_hasTwoSidedInverses` : the same for division algebras.
* `ConicAlgebra.IsComposition.isomorphic_realTower_of_isDivision`,
  `ConicAlgebra.IsComposition.isomorphic_realTower_of_hasTwoSidedInverses` : **`GPR 23.13`**, every
  real composition division algebra is `ℝ`, `ℂ`, `ℍ`, or `𝕆`.
* `ConicAlgebra.IsComposition.isSplitOfRank_or_isomorphic_realTower` : the complete list — a real
  composition algebra of dimension `2`, `4`, or `8` is either split or one of the three division
  algebras of that dimension.

## Implementation notes

`ℂ` and `ℍ` appear as the Cayley–Dickson doubles `Cay₂ ℝ (-1)` and `Cay₄ ℝ (-1) (-1)`, not as
mathlib's `Complex` and `Quaternion ℝ`; see `Composition/Examples.lean`. The identification of
`Cay₄ ℝ (-1) (-1)` with `ℍ[ℝ]` is in `Composition/ComplexQuaternion.lean` and is not needed here.

⚠ Positive definiteness, not mere anisotropy, is what makes the classification finite: over a
general field the anisotropic forms of a given dimension are not unique, and this is why the other
files in this layer need a separate argument for each class of field.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 8.6, 13.8, 22.18,
  23.13.
* Sylvester, *A demonstration of the theorem that every homogeneous quadratic polynomial is
  reducible by real orthogonal substitutions to the form of a sum of positive and negative
  squares*, Philosophical Magazine **4** (1852), 138–142.
-/

@[expose] public section

universe v w

namespace ConicAlgebra

variable {A : Type v} [NonAssocRing A] [Module ℝ A] [SMulCommClass ℝ A A]
  [IsScalarTower ℝ A A]
  [Module.Finite ℝ A] [Module.Projective ℝ A]
  {B : Type w} [NonAssocRing B] [Module ℝ B] [SMulCommClass ℝ B B] [IsScalarTower ℝ B B]
  [Module.Finite ℝ B] [Module.Projective ℝ B]
  {C : ConicAlgebra ℝ A} {D : ConicAlgebra ℝ B}

/-! ### Anisotropic real norms are positive definite -/

omit [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] [Module.Finite ℝ A] [Module.Projective ℝ A] in
/-- The norm of a real conic algebra is positive at the identity element, since `n(1) = 1`. -/
theorem norm_one_pos (C : ConicAlgebra ℝ A) : 0 < C.norm 1 := by
  rw [C.norm_one]
  norm_num

omit [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] [Module.Finite ℝ A] [Module.Projective ℝ A] in
/-- **An anisotropic real composition norm is positive definite.** The value at `1` is `1 > 0`, and
an anisotropic real form with a positive value is positive definite. -/
theorem posDef_norm_of_anisotropic (C : ConicAlgebra ℝ A) (hani : C.norm.Anisotropic) :
    C.norm.PosDef :=
  C.norm.posDef_of_anisotropic hani C.norm_one_pos

/-- **A real composition division algebra has positive definite norm.** -/
theorem IsComposition.posDef_norm_of_hasTwoSidedInverses (h : C.IsComposition.{0, v, 0})
    (hdiv : C.HasTwoSidedInverses) : C.norm.PosDef :=
  C.posDef_norm_of_anisotropic (h.isMultiplicative.hasTwoSidedInverses_iff_anisotropic.mp hdiv)

/-! ### Uniqueness in each dimension -/

/-- **The real division composition algebra of a given dimension is unique.** Both norms are
positive definite of the same dimension, hence isometric by Sylvester's law; Layer 9 turns the
isometry into an algebra isomorphism. -/
theorem IsComposition.isomorphic_of_anisotropic (hC : C.IsComposition.{0, v, 0})
    (hD : D.IsComposition.{0, w, 0}) (hCani : C.norm.Anisotropic) (hDani : D.norm.Anisotropic)
    (hdim : Module.finrank ℝ A = Module.finrank ℝ B) : C.Isomorphic D := by
  obtain ⟨e⟩ := QuadraticForm.equivalent_of_anisotropic_of_finrank_eq hCani hDani
    C.norm_one_pos D.norm_one_pos hdim
  exact hC.isomorphic_of_isometryEquiv hD e

/-- **The real division composition algebra of a given dimension is unique**, stated for division
algebras. -/
theorem IsComposition.isomorphic_of_hasTwoSidedInverses (hC : C.IsComposition.{0, v, 0})
    (hD : D.IsComposition.{0, w, 0}) (hCdiv : C.HasTwoSidedInverses) (hDdiv : D.HasTwoSidedInverses)
    (hdim : Module.finrank ℝ A = Module.finrank ℝ B) : C.Isomorphic D :=
  hC.isomorphic_of_anisotropic hD (hC.isMultiplicative.hasTwoSidedInverses_iff_anisotropic.mp hCdiv)
    (hD.isMultiplicative.hasTwoSidedInverses_iff_anisotropic.mp hDdiv) hdim

/-! ### The classical tower realizes every dimension -/

section Tower

/-- The conic structure on `ℂ = Cay(ℝ, -1)`. -/
noncomputable abbrev realComplex : ConicAlgebra ℝ RealComplex := cay₂ ℝ (-1)

/-- The conic structure on `ℍ = Cay(ℂ, -1)`. -/
noncomputable abbrev realQuaternion : ConicAlgebra ℝ RealQuaternion := cay₄ ℝ (-1) (-1)

theorem isComposition_realComplex : realComplex.IsComposition.{0, 0, 0} :=
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  isComposition_cay₂ ℝ (-1) (IsUnit.neg isUnit_one)

theorem isComposition_realQuaternion : realQuaternion.IsComposition.{0, 0, 0} :=
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  isComposition_cay₄ ℝ (-1) (-1) (IsUnit.neg isUnit_one) (IsUnit.neg isUnit_one)

theorem anisotropic_norm_baseRing : (baseRing ℝ).norm.Anisotropic :=
  (posDef_baseRing ℝ).anisotropic

theorem anisotropic_norm_realComplex : realComplex.norm.Anisotropic :=
  (posDef_cay₂ ℝ (by norm_num)).anisotropic

theorem anisotropic_norm_realQuaternion : realQuaternion.norm.Anisotropic :=
  (posDef_cay₄ ℝ (by norm_num) (by norm_num)).anisotropic

theorem anisotropic_norm_realOctonion : realOctonion.norm.Anisotropic :=
  posDef_realOctonion.anisotropic

end Tower

/-- **`GPR 23.13`.** Every composition division algebra over `ℝ` is isomorphic to one of `ℝ`, `ℂ`,
`ℍ`, `𝕆`. The dimension is `1`, `2`, `4`, or `8` by `GPR 19.18`, the norm is positive definite,
and in each dimension the tower supplies a positive definite composition algebra to compare with. -/
theorem IsComposition.isomorphic_realTower_of_hasTwoSidedInverses (h : C.IsComposition.{0, v, 0})
    (hdiv : C.HasTwoSidedInverses) :
    C.Isomorphic (baseRing ℝ) ∨ C.Isomorphic realComplex ∨ C.Isomorphic realQuaternion ∨
      C.Isomorphic realOctonion := by
  have hani := h.isMultiplicative.hasTwoSidedInverses_iff_anisotropic.mp hdiv
  rcases h.finrank_eq_one_or_two_or_four_or_eight with h1 | h2 | h4 | h8
  · exact Or.inl (h.isomorphic_of_anisotropic (isComposition_baseRing ℝ) hani
      anisotropic_norm_baseRing (by rw [h1, Module.finrank_self]))
  · exact Or.inr (Or.inl (h.isomorphic_of_anisotropic isComposition_realComplex hani
      anisotropic_norm_realComplex (by rw [h2, finrank_realComplex])))
  · exact Or.inr (Or.inr (Or.inl (h.isomorphic_of_anisotropic isComposition_realQuaternion hani
      anisotropic_norm_realQuaternion (by rw [h4, finrank_realQuaternion]))))
  · exact Or.inr (Or.inr (Or.inr (h.isomorphic_of_anisotropic isComposition_realOctonion hani
      anisotropic_norm_realOctonion (by rw [h8, finrank_realOctonion]))))

/-- **The complete list over `ℝ`.** A real composition algebra of dimension `2`, `4`, or `8` is
either split or the division algebra of that dimension. Together with
`ConicAlgebra.isSplitOfRank_one` in dimension one this classifies all of them. -/
theorem IsComposition.isSplitOfRank_or_isomorphic_realTower {r : ℕ}
    (h : C.IsComposition.{0, v, 0}) (hA : Module.finrank ℝ A = r)
    (hr : r = 2 ∨ r = 4 ∨ r = 8) :
    C.IsSplitOfRank r ∨ C.Isomorphic realComplex ∨ C.Isomorphic realQuaternion ∨
      C.Isomorphic realOctonion := by
  rcases h.isSplitOfRank_or_hasTwoSidedInverses hA hr with hs | hdiv
  · exact Or.inl hs
  have hani := h.isMultiplicative.hasTwoSidedInverses_iff_anisotropic.mp hdiv
  rcases hr with rfl | rfl | rfl
  · exact Or.inr (Or.inl (h.isomorphic_of_anisotropic isComposition_realComplex hani
      anisotropic_norm_realComplex (by rw [hA, finrank_realComplex])))
  · exact Or.inr (Or.inr (Or.inl (h.isomorphic_of_anisotropic isComposition_realQuaternion hani
      anisotropic_norm_realQuaternion (by rw [hA, finrank_realQuaternion]))))
  · exact Or.inr (Or.inr (Or.inr (h.isomorphic_of_anisotropic isComposition_realOctonion hani
      anisotropic_norm_realOctonion (by rw [hA, finrank_realOctonion]))))

/-! ### The same, with division in the sense of `GPR 8.6` -/

/-- **A real composition division algebra has positive definite norm**, with division in the sense
of `GPR 8.6`. -/
theorem IsComposition.posDef_norm_of_isDivision (h : C.IsComposition.{0, v, 0})
    (hdiv : IsDivision A) : C.norm.PosDef :=
  h.posDef_norm_of_hasTwoSidedInverses (C.hasTwoSidedInverses_of_isDivision hdiv)

/-- **The real division composition algebra of a given dimension is unique**, with division in the
sense of `GPR 8.6`. -/
theorem IsComposition.isomorphic_of_isDivision (hC : C.IsComposition.{0, v, 0})
    (hD : D.IsComposition.{0, w, 0}) (hCdiv : IsDivision A) (hDdiv : IsDivision B)
    (hdim : Module.finrank ℝ A = Module.finrank ℝ B) : C.Isomorphic D :=
  hC.isomorphic_of_hasTwoSidedInverses hD (C.hasTwoSidedInverses_of_isDivision hCdiv)
    (D.hasTwoSidedInverses_of_isDivision hDdiv) hdim

/-- **`GPR 23.13`, with division in the sense of `GPR 8.6`.** Every composition division algebra
over `ℝ` is isomorphic to one of `ℝ`, `ℂ`, `ℍ`, `𝕆`. -/
theorem IsComposition.isomorphic_realTower_of_isDivision (h : C.IsComposition.{0, v, 0})
    (hdiv : IsDivision A) :
    C.Isomorphic (baseRing ℝ) ∨ C.Isomorphic realComplex ∨ C.Isomorphic realQuaternion ∨
      C.Isomorphic realOctonion :=
  h.isomorphic_realTower_of_hasTwoSidedInverses (C.hasTwoSidedInverses_of_isDivision hdiv)

end ConicAlgebra
