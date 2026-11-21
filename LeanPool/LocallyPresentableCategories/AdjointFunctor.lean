/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.LocallyPresentableCategories.Reflective
public import Mathlib.CategoryTheory.Presentable.SolutionSetCondition
public import Mathlib.CategoryTheory.Presentable.Uniformization
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-!
# Accessible and complete categories, and the adjoint functor theorem

* `isLocallyPresentable_iff_isAccessibleCategory_and_hasLimits` (roadmap 1.3; Adámek–Rosický,
  Corollary 2.47): a category is locally presentable iff it is accessible and complete. For a
  complete `κ`-accessible `C`, the nerve `C ⥤ (presentableModel C κ)ᵒᵖ ⥤ Type w` is fully
  faithful, preserves limits and is accessible, hence a right adjoint by the general adjoint
  functor theorem and Mathlib's solution-set condition for accessible functors; so `C` is
  reflective in a presheaf category, hence cocomplete.
* `isRightAdjoint_iff` (roadmap 1.4; Adámek–Rosický, Theorem 1.66): between locally presentable
  categories a functor is a right adjoint iff it preserves limits and is accessible. A right
  adjoint `G` is `κ`-accessible as soon as its left adjoint `F` preserves `κ`-presentable objects
  (Mathlib's uniformization theorem provides such `κ`): `Hom(a, G -) ≅ Hom(F a, -)` preserves
  `κ`-filtered colimits for `κ`-presentable `a`, and the nerve of `D`, being fully faithful,
  reflects colimits.
* `isLeftAdjoint_iff` (roadmap 1.4): between locally presentable categories a functor is a left
  adjoint iff it preserves colimits. Instead of the special adjoint functor theorem (which would
  need co-wellpoweredness), we apply the general adjoint functor theorem to `F.op`: for `Y : D`
  the colimit `B` of the `κ`-presentable objects `a` over `F a ⟶ Y` carries a map `F B ⟶ Y`
  through which every `F X ⟶ Y` factors, `X` being the canonical colimit of the
  `κ`-presentable objects over it.
-/

@[expose] public section

namespace LeanPool.LocallyPresentableCategories

open CategoryTheory Limits Opposite

universe w v v' u u'

/-- Roadmap 1.3. A category is locally presentable iff it is accessible and complete
(Adámek–Rosický, Corollary 2.47). -/
theorem isLocallyPresentable_iff_isAccessibleCategory_and_hasLimits (C : Type u)
    [Category.{v} C] :
    IsLocallyPresentable.{w} C ↔ IsAccessibleCategory.{w} C ∧ HasLimitsOfSize.{w, w} C := by
  constructor
  · intro
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨_, _⟩
    obtain ⟨κ, _, _⟩ := IsAccessibleCategory.exists_cardinal.{w} C
    have := isCardinalAccessible_presentableNerve C κ
    have : (presentableNerve C κ).IsAccessible.{w} :=
      Functor.isAccessible_of_isCardinalAccessible _ κ
    have : (presentableNerve C κ).IsRightAdjoint :=
      isRightAdjoint_of_preservesLimits_of_solutionSetCondition _
        (SolutionSetCondition.of_isCardinalAccessible _)
    have : Reflective (presentableNerve C κ) :=
      { L := (presentableNerve C κ).leftAdjoint
        adj := Adjunction.ofIsRightAdjoint _ }
    have : HasColimitsOfSize.{w, w} C :=
      ⟨fun J _ ↦ hasColimitsOfShape_of_reflective (presentableNerve C κ)⟩
    exact ⟨κ, inferInstance, { }⟩

section RightAdjoint

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- For an adjunction `F ⊣ G` and `a : D`, the functor `Hom(a, G -)` is `Hom(F a, -)`. -/
noncomputable def shrinkCoyonedaCompIso [LocallySmall.{w} C] [LocallySmall.{w} D]
    {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) (a : D) :
    G ⋙ shrinkCoyoneda.{w}.obj (op a) ≅ shrinkCoyoneda.{w}.obj (op (F.obj a)) :=
  NatIso.ofComponents (fun X ↦ Equiv.toIso (shrinkCoyonedaObjObjEquiv.trans
    ((adj.homEquiv _ _).symm.trans shrinkCoyonedaObjObjEquiv.symm))) (fun f ↦ by
      ext x
      obtain ⟨x, rfl⟩ := shrinkCoyonedaObjObjEquiv.symm.surjective x
      apply shrinkCoyonedaObjObjEquiv.injective
      have h₁ := shrinkYonedaObjObjEquiv_map_app (shrinkYonedaObjObjEquiv.symm x) (G.map f)
      have h₂ := shrinkYonedaObjObjEquiv_map_app
        (shrinkYonedaObjObjEquiv.symm ((adj.homEquiv _ _).symm x)) f
      simp only [Equiv.apply_symm_apply] at h₁ h₂
      simp only [shrinkCoyonedaObjObjEquiv]
      simp [h₁, h₂, Adjunction.homEquiv_naturality_right_symm])

/-- A right adjoint between accessible categories is accessible. -/
theorem isAccessible_of_isRightAdjoint [IsAccessibleCategory.{w} C] [IsAccessibleCategory.{w} D]
    (G : C ⥤ D) [G.IsRightAdjoint] : G.IsAccessible.{w} := by
  let adj := Adjunction.ofIsRightAdjoint G
  have := adj.leftAdjoint_preservesColimits
  have : G.leftAdjoint.IsAccessible.{w} := ⟨Cardinal.aleph0, Cardinal.fact_isRegular_aleph0,
    inferInstance⟩
  obtain ⟨κ, _, _, _, _, _⟩ := IsCardinalAccessibleCategory.uniformization G.leftAdjoint
  refine ⟨κ, inferInstance, ⟨fun J _ _ ↦ ?_⟩⟩
  suffices PreservesColimitsOfShape J (G ⋙ presentableNerve D κ) from
    preservesColimitsOfShape_of_reflects_of_preserves G (presentableNerve D κ)
  refine preservesColimitsOfShape_of_evaluation _ _ fun a ↦ ?_
  let b := (presentableModelι D κ).obj a.unop
  have := (isCardinalAccessible_shrinkCoyoneda_obj (G.leftAdjoint.obj b)
    κ).preservesColimitOfShape J
  exact preservesColimitsOfShape_of_natIso
    ((Functor.associator _ _ _) ≪≫ Functor.isoWhiskerLeft G
      (presentableNerveCompEvaluationIso D κ a.unop) ≪≫ shrinkCoyonedaCompIso adj b).symm

/-- Roadmap 1.4. Between locally presentable categories, a functor is a right adjoint iff it
preserves small limits and is accessible (Adámek–Rosický, Theorem 1.66). -/
theorem isRightAdjoint_iff [IsLocallyPresentable.{w} C] [IsLocallyPresentable.{w} D]
    (G : C ⥤ D) :
    G.IsRightAdjoint ↔ PreservesLimitsOfSize.{w, w} G ∧ G.IsAccessible.{w} := by
  constructor
  · intro
    exact ⟨(Adjunction.ofIsRightAdjoint G).rightAdjoint_preservesLimits,
      isAccessible_of_isRightAdjoint G⟩
  · rintro ⟨_, _⟩
    exact isRightAdjoint_of_preservesLimits_of_solutionSetCondition _
      (SolutionSetCondition.of_isCardinalAccessible _)

end RightAdjoint

section LeftAdjoint

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- A colimit-preserving functor `F` out of a locally presentable category satisfies the
solution-set condition for `F.op`: for `Y : D`, every `F X ⟶ Y` factors through
`F B ⟶ Y`, where `B` is the colimit of the `κ`-presentable `a` over the arrows `F a ⟶ Y`. -/
theorem solutionSetCondition_op [IsLocallyPresentable.{w} C] [LocallySmall.{w} D] (F : C ⥤ D)
    [PreservesColimitsOfSize.{w, w} F] : SolutionSetCondition.{w} F.op := by
  obtain ⟨κ, _, _⟩ := IsLocallyPresentable.exists_cardinal.{w} C
  intro Y
  let ι := presentableModelι C κ
  let K : CostructuredArrow (ι ⋙ F) Y.unop ⥤ C := CostructuredArrow.proj _ _ ⋙ ι
  have : HasColimitsOfShape (CostructuredArrow (ι ⋙ F) Y.unop) C :=
    hasColimitsOfShape_of_essentiallySmall.{w} _ _
  have : PreservesColimitsOfShape (CostructuredArrow (ι ⋙ F) Y.unop) F :=
    preservesColimitsOfShape_of_equiv (equivSmallModel.{w} _).symm F
  let hK := isColimitOfPreserves F (colimit.isColimit K)
  let f : F.obj (colimit K) ⟶ Y.unop := hK.desc
    { pt := Y.unop
      ι := { app e := e.hom
             naturality _ _ φ := by simpa [K] using CostructuredArrow.w φ } }
  refine ⟨PUnit, fun _ ↦ op (colimit K), fun _ ↦ f.op, fun X h ↦ ?_⟩
  let hX := ι.denseAt X.unop
  have : PreservesColimitsOfShape (CostructuredArrow ι X.unop) F :=
    preservesColimitsOfShape_of_equiv (equivSmallModel.{w} _).symm F
  let e (u : CostructuredArrow ι X.unop) : CostructuredArrow (ι ⋙ F) Y.unop :=
    CostructuredArrow.mk (Y := u.left) (F.map u.hom ≫ h.unop)
  let g : X.unop ⟶ colimit K := hX.desc
    { pt := colimit K
      ι := { app u := colimit.ι K (e u)
             naturality u u' φ := by
               have := colimit.w K (CostructuredArrow.homMk (f := e u) (f' := e u') φ.left
                 (by simp [e, ← F.map_comp_assoc, CostructuredArrow.w φ]))
               dsimp
               rw [Category.comp_id]
               exact this } }
  refine ⟨PUnit.unit, g.op, Quiver.Hom.unop_inj ?_⟩
  refine (isColimitOfPreserves F hX).hom_ext fun u ↦ ?_
  have h₁ : u.hom ≫ g = colimit.ι K (e u) := by simpa using hX.fac _ u
  have h₂ : F.map (colimit.ι K (e u)) ≫ f = (e u).hom := hK.fac _ (e u)
  simp [← F.map_comp_assoc, h₁, h₂, e]

/-- Roadmap 1.4. Between locally presentable categories, a functor is a left adjoint iff it
preserves small colimits. The proof applies the general adjoint functor theorem to `F.op`. -/
theorem isLeftAdjoint_iff [IsLocallyPresentable.{w} C] [IsLocallyPresentable.{w} D]
    (F : C ⥤ D) :
    F.IsLeftAdjoint ↔ PreservesColimitsOfSize.{w, w} F := by
  constructor
  · intro
    exact (Adjunction.ofIsLeftAdjoint F).leftAdjoint_preservesColimits
  · intro
    have := preservesLimitsOfSize_op.{w, w} F
    have : F.op.IsRightAdjoint :=
      isRightAdjoint_of_preservesLimits_of_solutionSetCondition _ (solutionSetCondition_op F)
    exact ⟨_, ⟨(Adjunction.ofIsRightAdjoint F.op).unop⟩⟩

end LeftAdjoint

end LeanPool.LocallyPresentableCategories
