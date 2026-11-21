/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.LocallyPresentableCategories.Models
public import Mathlib.CategoryTheory.ObjectProperty.LimitsClosure
public import Mathlib.CategoryTheory.Limits.FullSubcategory

/-!
# Generation under `D`-limits

For a small family `D` of limit shapes, a family `i : I → R` of objects generates `R` under
`D`-limits (`Generates D i`) when the closure of its image under limits of the shapes `D a` is
all of `R`. We prove `generates_iff_essSurj` (roadmap 5.5): in a category `R` with `D`-limits, `i`
generates iff every fully faithful `D`-functor `F : B ⥤ R` from a category with `D`-limits,
whose essential image contains the `i x`, is essentially surjective.

* Forward: the essential image of such an `F` is closed under isomorphisms and `D`-limits
  (Mathlib), so it contains the closure.
* Backward: apply the hypothesis to the inclusion of the closure itself.

The comparison of roadmap 5.5 with presentations by envelopes, localisations and adjunctions of
arrows is not formalised.
-/

@[expose] public section

namespace LeanPool.LocallyPresentableCategories

open CategoryTheory Limits

universe w v u

variable {α : Type w} (D : α → Type w) [∀ a, SmallCategory (D a)]

/-- A category has `D`-limits: limits of every shape `D a`. -/
def HasDLimits (X : Type u) [Category.{v} X] : Prop :=
  ∀ a, HasLimitsOfShape (D a) X

/-- A functor `i : I → R` generates `R` under `D`-limits: the closure of its image under limits of
the shapes `D a` is all of `R` (roadmap 5.5). -/
def Generates {R : Type u} [Category.{v} R] {I : Type w} (i : I → R) : Prop :=
  (ObjectProperty.ofObj i).limitsClosure D = ⊤

/-- Roadmap 5.5. In a category with `D`-limits, `i` generates iff every fully faithful
`D`-functor through whose essential image `i` passes is essentially surjective (compare Kelly,
*Basic concepts*, §3.5). -/
theorem generates_iff_essSurj {R : Type u} [Category.{v} R] (hR : HasDLimits D R) {I : Type w}
    (i : I → R) :
    Generates D i ↔
      ∀ (B : Type u) [Category.{v} B] (F : B ⥤ R) [F.Full] [F.Faithful], HasDLimits D B →
        PreservesDLimits D F → (∀ x, ∃ b, Nonempty (F.obj b ≅ i x)) → F.EssSurj := by
  constructor
  · intro h B _ F _ _ hB hF hi
    have (a : α) : F.essImage.IsClosedUnderLimitsOfShape (D a) := by
      have := hB a
      have := hF a
      infer_instance
    have hle : (ObjectProperty.ofObj i).limitsClosure D ≤ F.essImage :=
      ObjectProperty.limitsClosure_le (by
        rintro _ ⟨x⟩
        obtain ⟨b, ⟨e⟩⟩ := hi x
        exact ⟨b, ⟨e⟩⟩)
    exact ⟨fun Y ↦ hle Y (by rw [h]; trivial)⟩
  · intro h
    let P := (ObjectProperty.ofObj i).limitsClosure D
    have (a : α) : HasLimitsOfShape (D a) R := hR a
    have := h P.FullSubcategory P.ι (fun a ↦ inferInstance) (fun a ↦ inferInstance)
      (fun x ↦ ⟨⟨i x, ObjectProperty.le_limitsClosure _ _ _ (ObjectProperty.ofObj_apply _ x)⟩,
        ⟨Iso.refl _⟩⟩)
    refine le_antisymm le_top fun Y _ ↦ ?_
    exact P.prop_of_iso (P.ι.objObjPreimageIso Y) (P.ι.objPreimage Y).property

end LeanPool.LocallyPresentableCategories
