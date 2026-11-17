/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-!
# The group completion of a commutative monoid

Mathlib defines the group completion of a commutative monoid `M` as `Localization ⊤` and gives its
universal property. This file describes pairs of its elements in terms of the canonical map
`of : M →* G(M)` and deduces that the functor between one-object categories induced by `of` is
representably flat, hence final. The additive versions come from `to_additive`.

## Main statements

* `Algebra.GrothendieckGroup.exists_of_mul_eq_and_of_mul_eq`: two elements are translates
  `of m₁ * g`, `of m₂ * g` of a common one (a common denominator).
* `Algebra.GrothendieckGroup.representablyFlat_toFunctor_of`: the functor
  `SingleObj M ⥤ SingleObj G(M)` induced by `of` is representably flat.
* `Algebra.GrothendieckGroup.final_toFunctor_of`: hence it is final.
-/

public section

open CategoryTheory

namespace Algebra.GrothendieckGroup

universe u

variable {M : Type u} [CommMonoid M]

/-- Every element of the group completion becomes an element of `M` after multiplication by an
element of `M`. -/
@[to_additive /-- Every element of the group completion becomes an element of `M` after adding
an element of `M`. -/]
private theorem exists_of_mul_eq_of (x : GrothendieckGroup M) :
    ∃ b a : M, of b * x = of a := by
  obtain ⟨⟨a, b⟩, h⟩ := (Localization.monoidOf (⊤ : Submonoid M)).surj x
  exact ⟨b, a, (mul_comm _ _).trans h⟩

/-- Any two elements of the group completion are translates of a common element by elements
of `M`. -/
@[to_additive /-- Any two elements of the group completion are translates of a common element
by elements of `M`. -/]
theorem exists_of_mul_eq_and_of_mul_eq (g₁ g₂ : GrothendieckGroup M) :
    ∃ (g : GrothendieckGroup M) (m₁ m₂ : M), of m₁ * g = g₁ ∧ of m₂ * g = g₂ := by
  obtain ⟨b₁, a₁, h₁⟩ := exists_of_mul_eq_of g₁
  obtain ⟨b₂, a₂, h₂⟩ := exists_of_mul_eq_of g₂
  refine ⟨(of (b₁ * b₂))⁻¹, b₂ * a₁, b₁ * a₂, ?_, ?_⟩ <;>
    simp only [map_mul, ← h₁, ← h₂, mul_inv_eq_iff_eq_mul] <;> ac_rfl

/-- Two elements of `M` have the same image in the group completion iff they become equal after
multiplication by an element of `M`. -/
@[to_additive /-- Two elements of `M` have the same image in the group completion iff they
become equal after adding an element of `M`. -/]
private theorem of_eq_of_iff {m₁ m₂ : M} : of m₁ = of m₂ ↔ ∃ c : M, c * m₁ = c * m₂ :=
  (Localization.monoidOf (⊤ : Submonoid M)).eq_iff_exists.trans
    ⟨fun ⟨c, hc⟩ ↦ ⟨c, hc⟩, fun ⟨c, hc⟩ ↦ ⟨⟨c, Submonoid.mem_top c⟩, hc⟩⟩

/-- **The map from a commutative monoid to its group completion is representably flat**: for
the unique object `X`, the category `X / of` of elements of `G(M)` with arrows given by `M`
acting by translation is cofiltered. -/
theorem representablyFlat_toFunctor_of : RepresentablyFlat (of (M := M)).toFunctor where
  cofiltered X :=
    { cone_objs Y₁ Y₂ := by
        obtain ⟨g, m₁, m₂, h₁, h₂⟩ := exists_of_mul_eq_and_of_mul_eq (M := M) Y₁.hom Y₂.hom
        exact ⟨StructuredArrow.mk (Y := SingleObj.star M) g, StructuredArrow.homMk m₁ h₁,
          StructuredArrow.homMk m₂ h₂, trivial⟩
      cone_maps Y Y' φ ψ := by
        have hφ := StructuredArrow.w φ
        have hψ := StructuredArrow.w ψ
        obtain ⟨c, hc⟩ := (of_eq_of_iff (M := M) (m₁ := φ.right) (m₂ := ψ.right)).1
          (mul_right_cancel (hφ.trans hψ.symm))
        refine ⟨StructuredArrow.mk (Y := SingleObj.star M) ((of c)⁻¹ * Y.hom),
          StructuredArrow.homMk c (mul_inv_cancel_left (of c) Y.hom),
          StructuredArrow.hom_ext _ _ ?_⟩
        change φ.right * c = ψ.right * c
        rw [mul_comm, hc, mul_comm]
      nonempty := ⟨StructuredArrow.mk (Y := SingleObj.star M) (1 : GrothendieckGroup M)⟩ }

/-- The functor `SingleObj M ⥤ SingleObj (GrothendieckGroup M)` induced by `of` is final
(`CategoryTheory.final_of_representablyFlat`). -/
theorem final_toFunctor_of : (of (M := M)).toFunctor.Final :=
  have := representablyFlat_toFunctor_of (M := M)
  final_of_representablyFlat _

end Algebra.GrothendieckGroup
