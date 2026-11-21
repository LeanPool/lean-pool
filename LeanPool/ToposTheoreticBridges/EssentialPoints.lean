/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.Morita
public import Mathlib.CategoryTheory.Functor.KanExtension.RestrictedYoneda
public import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits

/-!
# Essential points of a presheaf topos

A *point* of a topos `E` is a geometric morphism `Set → E`; we record it by its inverse image
`p : E ⥤ Type u`, a functor with a right adjoint (the direct image) which preserves finite
limits (`isPoint`). The point is *essential* when the inverse image also has a left adjoint
(`isEssentialPoint`). The category of essential points `EssentialPoint E` is the full
subcategory of `E ⥤ Type u` on the inverse images of essential points, so a morphism of
essential points is a natural transformation between their inverse images.

For a small category `C` we prove that the essential points of the presheaf topos
`Cᵒᵖ ⥤ Type u` form a category equivalent to the opposite of the Karoubi envelope of `C`:
`essentialPointEquivKaroubiOp : EssentialPoint (Cᵒᵖ ⥤ Type u) ≌ (Karoubi C)ᵒᵖ`, or
equivalently `essentialPointEquivKaroubi : EssentialPoint (Cᵒᵖ ⥤ Type u) ≌ Karoubi Cᵒᵖ`.
On objects of `C`, the point attached to `X : C` is evaluation at `X`
(`isEssentialPoint_evaluation`), and a morphism `X ⟶ Y` in `C` induces a natural
transformation from evaluation at `Y` to evaluation at `X`: the variance is reversed, since
morphisms of points are transformations of inverse images (SGA 4 IV, §3.2).

The classification of essential points of a presheaf topos by the idempotent completion of `C`
is SGA 4 IV, Exercise 7.7 (c), (e).

## Proof

* An inverse image `p` with a left adjoint `L` is corepresented by `P := L.obj PUnit`
  (`isoCoyonedaOfAdjunction`), and `p` preserves colimits since it is a left adjoint; hence
  every morphism from `P` to the point of a small colimit cocone factors through a leg, and `P`
  is a retract of a representable presheaf by `isRetractOfRepresentable_iff` (from
  `LeanPool.ToposTheoreticBridges.Morita`).
* Conversely, if `P` is a retract of `yoneda.obj X`, then `Hom(P, -)` is a retract of
  `Hom(yoneda.obj X, -) ≅ evaluation at X` (a component of `curriedYonedaLemma`), so it
  preserves colimits (`preservesColimitsOfSize_of_retract`, from Mathlib's stability of
  `ObjectProperty.preservesColimitsOfShape` under retracts), and therefore has a right adjoint
  by the adjoint functor theorem for presheaf categories; it has the left adjoint `S ↦ ∐_S P`
  (`sigmaConstAdj`) and preserves limits.
* The functor `P ↦ Hom(P, -)` from the opposite of the full subcategory of retracts of
  representables is fully faithful (Yoneda) and, by the above, essentially surjective onto
  essential points. We conclude with `karoubiEquivRetractsOfRepresentables`.

We do not formalise geometric morphisms as such (only inverse images), nor the corresponding
statement for arbitrary points of a presheaf topos (flat functors).
-/

@[expose] public section

namespace LeanPool.ToposTheoreticBridges

open CategoryTheory Limits Opposite Idempotents

universe u u₁ v₁ u₂ v₂ w w'

/-- The inverse images of the points of a category `E`: functors `E ⥤ Type u` which have a
right adjoint and preserve finite limits. -/
def isPoint (E : Type u₁) [Category.{v₁} E] : ObjectProperty (E ⥤ Type u) :=
  fun p => p.IsLeftAdjoint ∧ PreservesFiniteLimits p

/-- The inverse images of the essential points of a category `E`: inverse images of points
which moreover have a left adjoint. -/
def isEssentialPoint (E : Type u₁) [Category.{v₁} E] : ObjectProperty (E ⥤ Type u) :=
  fun p => isPoint E p ∧ p.IsRightAdjoint

/-- The category of essential points of `E`, as the full subcategory of `E ⥤ Type u` on the
inverse images of essential points. -/
abbrev EssentialPoint (E : Type u₁) [Category.{v₁} E] :=
  (isEssentialPoint.{u} E).FullSubcategory

/-- Being the inverse image of an essential point is invariant under natural isomorphism. -/
theorem isEssentialPoint_of_iso {E : Type u₁} [Category.{v₁} E] {p q : E ⥤ Type u}
    (e : p ≅ q) (hp : isEssentialPoint.{u} E p) : isEssentialPoint.{u} E q := by
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hp
  exact ⟨⟨Functor.isLeftAdjoint_of_iso e, preservesFiniteLimits_of_natIso e⟩,
    Functor.isRightAdjoint_of_iso e⟩

section Retract

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- A retract of a functor preserving colimits preserves colimits: this is Mathlib's stability of
`ObjectProperty.preservesColimitsOfShape` under retracts, for every shape. -/
theorem preservesColimitsOfSize_of_retract {G H : A ⥤ B} (ρ : Retract G H)
    [PreservesColimitsOfSize.{w', w} H] : PreservesColimitsOfSize.{w', w} G where
  preservesColimitsOfShape {K} _ :=
    (ObjectProperty.preservesColimitsOfShape K).prop_of_retract ρ
      (inferInstanceAs (PreservesColimitsOfShape K H))

end Retract

section Presheaf

variable {C : Type u} [SmallCategory C]

/-- The functor corepresented by a representable presheaf `yoneda.obj X` is evaluation
at `X`: the component at `op X` of the curried Yoneda lemma `curriedYonedaLemma`. -/
noncomputable def coyonedaYonedaIsoEvaluation (X : C) :
    coyoneda.obj (op (yoneda.obj X)) ≅ (evaluation Cᵒᵖ (Type u)).obj (op X) :=
  curriedYonedaLemma.app (op X)

/-- The functor corepresented by a retract of a representable presheaf preserves small
colimits. -/
theorem preservesColimits_coyoneda_of_isRetractOfRepresentable {P : Cᵒᵖ ⥤ Type u}
    (hP : isRetractOfRepresentable C P) :
    PreservesColimitsOfSize.{u, u} (coyoneda.obj (op P)) := by
  obtain ⟨X, ⟨r⟩⟩ := hP
  have := preservesColimits_of_natIso (coyonedaYonedaIsoEvaluation X).symm
  exact preservesColimitsOfSize_of_retract (r.op.map coyoneda)

/-- The functor corepresented by a retract of a representable presheaf is the inverse image
of an essential point of the presheaf topos. -/
theorem isEssentialPoint_coyoneda {P : Cᵒᵖ ⥤ Type u} (hP : isRetractOfRepresentable C P) :
    isEssentialPoint.{u} (Cᵒᵖ ⥤ Type u) (coyoneda.obj (op P)) := by
  have := preservesColimits_coyoneda_of_isRetractOfRepresentable hP
  exact ⟨⟨Presheaf.isLeftAdjoint_of_preservesColimits.{u} _, inferInstance⟩,
    ⟨_, ⟨sigmaConstAdj P⟩⟩⟩

/-- Evaluation at an object `X : C` is the inverse image of an essential point of the
presheaf topos. -/
theorem isEssentialPoint_evaluation (X : C) :
    isEssentialPoint.{u} (Cᵒᵖ ⥤ Type u) ((evaluation Cᵒᵖ (Type u)).obj (op X)) :=
  isEssentialPoint_of_iso (coyonedaYonedaIsoEvaluation X)
    (isEssentialPoint_coyoneda ⟨X, ⟨Retract.refl _⟩⟩)

/-- A presheaf whose corepresented functor preserves small colimits factors through
colimits. -/
theorem factorsThroughColimits_of_preservesColimits (P : Cᵒᵖ ⥤ Type u)
    [PreservesColimitsOfSize.{u, u} (coyoneda.obj (op P))] :
    FactorsThroughColimits.{u} P := by
  intro J _ G c hc f
  obtain ⟨j, g, hg⟩ :=
    Types.jointly_surjective _ (isColimitOfPreserves (coyoneda.obj (op P)) hc) f
  exact ⟨j, g, hg.symm⟩

/-- A functor `p : (Cᵒᵖ ⥤ Type u) ⥤ Type u` with a left adjoint `L` is corepresented by
`L.obj PUnit`. -/
noncomputable def isoCoyonedaOfAdjunction {L : Type u ⥤ (Cᵒᵖ ⥤ Type u)}
    {p : (Cᵒᵖ ⥤ Type u) ⥤ Type u} (adj : L ⊣ p) : p ≅ coyoneda.obj (op (L.obj PUnit)) :=
  (p.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft p Coyoneda.punitIso.symm) ≪≫
    (adj.corepresentableBy PUnit).toIso.symm

/-- The inverse image of an essential point of a presheaf topos is corepresented by a retract
of a representable presheaf. -/
theorem exists_isRetractOfRepresentable_of_isEssentialPoint {p : (Cᵒᵖ ⥤ Type u) ⥤ Type u}
    (hp : isEssentialPoint.{u} (Cᵒᵖ ⥤ Type u) p) :
    ∃ P : Cᵒᵖ ⥤ Type u, isRetractOfRepresentable C P ∧ Nonempty (p ≅ coyoneda.obj (op P)) := by
  obtain ⟨⟨h₁, -⟩, h₃⟩ := hp
  let e := isoCoyonedaOfAdjunction (Adjunction.ofIsRightAdjoint p)
  have := (Adjunction.ofIsLeftAdjoint p).leftAdjoint_preservesColimits
  have := preservesColimits_of_natIso e
  exact ⟨_, (isRetractOfRepresentable_iff _).2
    (factorsThroughColimits_of_preservesColimits _), ⟨e⟩⟩

/-- A functor `(Cᵒᵖ ⥤ Type u) ⥤ Type u` is the inverse image of an essential point of the
presheaf topos if and only if it is corepresented by a retract of a representable presheaf. -/
theorem isEssentialPoint_iff (p : (Cᵒᵖ ⥤ Type u) ⥤ Type u) :
    isEssentialPoint.{u} (Cᵒᵖ ⥤ Type u) p ↔
      ∃ P : Cᵒᵖ ⥤ Type u, isRetractOfRepresentable C P ∧ Nonempty (p ≅ coyoneda.obj (op P)) :=
  ⟨exists_isRetractOfRepresentable_of_isEssentialPoint, fun ⟨_, hP, ⟨e⟩⟩ =>
    isEssentialPoint_of_iso e.symm (isEssentialPoint_coyoneda hP)⟩

variable (C)

/-- The functor sending a retract `P` of a representable presheaf to the essential point with
inverse image `Hom(P, -)`. -/
noncomputable def coyonedaEssentialPoint :
    (isRetractOfRepresentable C).FullSubcategoryᵒᵖ ⥤ EssentialPoint.{u} (Cᵒᵖ ⥤ Type u) :=
  (isEssentialPoint.{u} _).lift ((isRetractOfRepresentable C).ι.op ⋙ coyoneda)
    fun P => isEssentialPoint_coyoneda P.unop.2

/-- `coyonedaEssentialPoint` is full (Yoneda). -/
instance : (coyonedaEssentialPoint C).Full := by
  dsimp [coyonedaEssentialPoint]; infer_instance

/-- `coyonedaEssentialPoint` is faithful (Yoneda). -/
instance : (coyonedaEssentialPoint C).Faithful := by
  dsimp [coyonedaEssentialPoint]; infer_instance

/-- Every essential point of the presheaf topos is corepresented by a retract of a
representable presheaf. -/
instance : (coyonedaEssentialPoint C).EssSurj where
  mem_essImage p := by
    obtain ⟨P, hP, ⟨e⟩⟩ := exists_isRetractOfRepresentable_of_isEssentialPoint p.2
    exact ⟨op ⟨P, hP⟩, ⟨(isEssentialPoint.{u} _).fullyFaithfulι.preimageIso e.symm⟩⟩

/-- `coyonedaEssentialPoint` is an equivalence of categories. -/
instance : (coyonedaEssentialPoint C).IsEquivalence where

/-- The essential points of the presheaf topos on `C` form a category equivalent to the
opposite of the category of retracts of representable presheaves. -/
noncomputable def essentialPointEquivRetracts :
    EssentialPoint.{u} (Cᵒᵖ ⥤ Type u) ≌ (isRetractOfRepresentable C).FullSubcategoryᵒᵖ :=
  (coyonedaEssentialPoint C).asEquivalence.symm

/-- The essential points of the presheaf topos `Cᵒᵖ ⥤ Type u` form a category equivalent to
the opposite of the Karoubi envelope of `C`. -/
noncomputable def essentialPointEquivKaroubiOp :
    EssentialPoint.{u} (Cᵒᵖ ⥤ Type u) ≌ (Karoubi C)ᵒᵖ :=
  (essentialPointEquivRetracts C).trans (karoubiEquivRetractsOfRepresentables C).op.symm

/-- The essential points of the presheaf topos `Cᵒᵖ ⥤ Type u` form a category equivalent to
the Karoubi envelope of `Cᵒᵖ`. -/
noncomputable def essentialPointEquivKaroubi :
    EssentialPoint.{u} (Cᵒᵖ ⥤ Type u) ≌ Karoubi Cᵒᵖ :=
  (essentialPointEquivKaroubiOp C).trans (karoubiOpEquiv C).symm

end Presheaf

end LeanPool.ToposTheoreticBridges
