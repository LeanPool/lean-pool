/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Generic

/-!
# Natural transformations out of the Horn category and homomorphisms

Let `F' G'` be functors out of the presheaf topos on the Horn category which preserve finite
limits, epimorphisms and coproducts (for instance inverse images of geometric morphisms). The
interpretation of a Horn formula `X` in the structure of `yoneda ⋙ F'` is the subobject
`F'(y X) ⟶ F'(y ⊤ₙ)` (`HornCat.interp_toFormula_yoneda_comp`). Hence a homomorphism `h` between the
structures of `yoneda ⋙ F'` and `yoneda ⋙ G'` restricts, on each `F'(y X)` seen inside the
`n`-th power of the carrier, to a morphism `F'(y X) ⟶ G'(y X)`; these form a natural
transformation, the unique one with component `h` at `⊤₁` (`HornCat.exists_natTrans_of_isHom`,
`HornCat.natTrans_ext`).
-/

@[expose] public section

universe u u₁ u₂

namespace LeanPool.ClassifyingTopoi.Syntactic

open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits LeanPool.ClassifyingTopoi
  Opposite

variable {L : Language.{u₁, u₂}}

namespace HornCat

section Ext

variable {E : Type*} [Category E] [HasFiniteProducts E] {A B : HornCat.{u} L ⥤ E}
  [∀ n : ℕ, PreservesLimit (Discrete.functor fun _ : Fin n => top.{u} (L := L) 1) B]
  [∀ X : HornCat.{u} L, Mono (B.map (ι X))]

/-- A natural transformation into a functor preserving powers and the inclusions of Horn
formulas is determined by its component at `⊤₁`. -/
theorem natTrans_ext (γ γ' : A ⟶ B) (h : γ.app (top 1) = γ'.app (top 1)) : γ = γ' := by
  ext X
  rw [← cancel_mono (B.map (ι X) ≫ (isoPow B X.n).hom)]
  ext i
  simp only [Category.assoc, isoPow_hom_π, ← B.map_comp, ← NatTrans.naturality, h]

end Ext

variable {E : Type*} [Category E] [HasFiniteLimits E] [HasImages E]
  [HasCoproducts.{max u₁ u₂ u} E] [StrongEpiCategory E]
  (F' : ((HornCat.{u} L)ᵒᵖ ⥤ Type (max u₁ u₂ u)) ⥤ E) [PreservesFiniteLimits F']
  [F'.PreservesEpimorphisms] [∀ ι : Type (max u₁ u₂ u), PreservesColimitsOfShape (Discrete ι) F']

omit [StrongEpiCategory E] [F'.PreservesEpimorphisms]
  [∀ ι : Type (max u₁ u₂ u), PreservesColimitsOfShape (Discrete ι) F'] in
/-- The structure of `yoneda ⋙ F'` and the image of the generic structure under `F'` have the
same interpretations. -/
theorem interp_hornStructure_yoneda_comp {n : ℕ}
    (φ : GeometricFormula.{max u₁ u₂ u} L n) :
    (hornStructure (yoneda ⋙ F')).interp φ = ((genericPsh L).map F').interp φ := by
  have h₁ := (isHom_comp_hornStructure (yoneda : HornCat.{u} L ⥤ _) F').interp_le φ
  have h₂ := (isHom_comp_hornStructure' (yoneda : HornCat.{u} L ⥤ _) F').interp_le φ
  simp only [Limits.Pi.map_id, Subobject.pullback_id] at h₁ h₂
  exact le_antisymm h₁ h₂

/-- The interpretation of a Horn formula in the structure of `yoneda ⋙ F'` is the subobject
`F'(y X) ⟶ F'(y ⊤ₙ)`. -/
theorem interp_toFormula_yoneda_comp (X : HornCat.{u} L) :
    (hornStructure (yoneda ⋙ F')).interp X.toFormula =
      Subobject.mk ((yoneda ⋙ F').map (ι X) ≫ (isoPow (yoneda ⋙ F') X.n).hom) := by
  rw [interp_hornStructure_yoneda_comp, CatStructure.interp_map, interp_toFormula_genericPsh,
    mapSubobject_mk]
  refine Subobject.mk_eq_mk_of_comm _ _ (Iso.refl _) ?_
  rw [Iso.refl_hom, Category.id_comp, isoPow_comp_hom, F'.map_comp, Category.assoc]
  rfl

instance (X : HornCat.{u} L) : Mono ((yoneda ⋙ F').map (ι X)) :=
  inferInstanceAs (Mono (F'.map (yoneda.map (ι X))))

variable {F'} {G' : ((HornCat.{u} L)ᵒᵖ ⥤ Type (max u₁ u₂ u)) ⥤ E} [PreservesFiniteLimits G']
  [G'.PreservesEpimorphisms] [∀ ι : Type (max u₁ u₂ u), PreservesColimitsOfShape (Discrete ι) G']

/-- A homomorphism between the structures of `yoneda ⋙ F'` and `yoneda ⋙ G'` is the component
at `⊤₁` of a natural transformation. -/
theorem exists_natTrans_of_isHom {h : (yoneda ⋙ F').obj (top 1) ⟶ (yoneda ⋙ G').obj (top 1)}
    (hh : (hornStructure (yoneda ⋙ F')).IsHom (hornStructure (yoneda ⋙ G')) h) :
    ∃ γ : yoneda ⋙ F' ⟶ yoneda ⋙ G', γ.app (top 1) = h := by
  have key : ∀ X : HornCat.{u} L, ∃ g : (yoneda ⋙ F').obj X ⟶ (yoneda ⋙ G').obj X,
      g ≫ (yoneda ⋙ G').map (ι X) ≫ (isoPow (yoneda ⋙ G') X.n).hom =
        ((yoneda ⋙ F').map (ι X) ≫ (isoPow (yoneda ⋙ F') X.n).hom) ≫
          Limits.Pi.map fun _ => h := by
    intro X
    have hle := hh.interp_le X.toFormula
    rw [interp_toFormula_yoneda_comp, interp_toFormula_yoneda_comp] at hle
    obtain ⟨a, ha⟩ := exists_comp_of_le_pullback hle
    refine ⟨(Subobject.underlyingIso _).inv ≫ a ≫ (Subobject.underlyingIso _).hom, ?_⟩
    have e₁ := Subobject.underlyingIso_hom_comp_eq_mk
      ((yoneda ⋙ G').map (ι X) ≫ (isoPow (yoneda ⋙ G') X.n).hom)
    have e₂ := Subobject.underlyingIso_arrow
      ((yoneda ⋙ F').map (ι X) ≫ (isoPow (yoneda ⋙ F') X.n).hom)
    calc _ = (Subobject.underlyingIso _).inv ≫ a ≫ ((Subobject.underlyingIso _).hom ≫
          ((yoneda ⋙ G').map (ι X) ≫ (isoPow (yoneda ⋙ G') X.n).hom)) := by
          simp only [Category.assoc]
      _ = _ := by rw [e₁, ← ha, ← Category.assoc, e₂]
  choose g hg using key
  have hmono : ∀ X : HornCat.{u} L,
      Mono ((yoneda ⋙ G').map (ι X) ≫ (isoPow (yoneda ⋙ G') X.n).hom) := fun _ => inferInstance
  refine ⟨{ app := g, naturality := fun X Y f => ?_ }, ?_⟩
  · obtain ⟨σ, hσ, rfl⟩ := exists_eq_mor f
    rw [← cancel_mono ((yoneda ⋙ G').map (ι Y) ≫ (isoPow (yoneda ⋙ G') Y.n).hom)]
    have hι : mor σ hσ ≫ ι Y = ι X ≫ toTop (top X.n) σ := by
      change toTop X _ = toTop X _
      exact toTop_eq_toTop_iff.2 fun _ _ _ _ _ => by simp
    have hlift : ∀ (A' : HornCat.{u} L ⥤ E)
        [∀ n : ℕ, PreservesLimit (Discrete.functor fun _ : Fin n => top.{u} (L := L) 1) A'],
        A'.map (mor σ hσ) ≫ A'.map (ι Y) ≫ (isoPow A' Y.n).hom =
          (A'.map (ι X) ≫ (isoPow A' X.n).hom) ≫
            Pi.lift fun i => (hornStructure A').termMap (σ i) := fun A' _ => by
      rw [piLift_termMap_hornStructure, ← A'.map_comp_assoc, hι, A'.map_comp]
      simp
    have hcomm : (Pi.lift fun i => (hornStructure (yoneda ⋙ F')).termMap (σ i)) ≫
        (Limits.Pi.map fun _ => h) = (Limits.Pi.map fun _ => h) ≫
          Pi.lift fun i => (hornStructure (yoneda ⋙ G')).termMap (σ i) := by
      ext i
      simp [hh.termMap]
    calc ((yoneda ⋙ F').map (mor σ hσ) ≫ g Y) ≫ (yoneda ⋙ G').map (ι Y) ≫
          (isoPow (yoneda ⋙ G') Y.n).hom
        = ((yoneda ⋙ F').map (mor σ hσ) ≫ (yoneda ⋙ F').map (ι Y) ≫
            (isoPow (yoneda ⋙ F') Y.n).hom) ≫ Limits.Pi.map (fun _ => h) := by
          rw [Category.assoc, hg]
          simp only [Category.assoc]
      _ = ((yoneda ⋙ F').map (ι X) ≫ (isoPow (yoneda ⋙ F') X.n).hom) ≫
            (Limits.Pi.map fun _ => h) ≫
              Pi.lift fun i => (hornStructure (yoneda ⋙ G')).termMap (σ i) := by
          rw [hlift, Category.assoc, hcomm]
      _ = (g X ≫ (yoneda ⋙ G').map (ι X) ≫ (isoPow (yoneda ⋙ G') X.n).hom) ≫
            Pi.lift fun i => (hornStructure (yoneda ⋙ G')).termMap (σ i) := by
          rw [hg]
          simp only [Category.assoc]
      _ = (g X ≫ (yoneda ⋙ G').map (mor σ hσ)) ≫ (yoneda ⋙ G').map (ι Y) ≫
            (isoPow (yoneda ⋙ G') Y.n).hom := by
          simp only [Category.assoc]
          rw [hlift]
          simp only [Category.assoc]
  · rw [← cancel_mono ((yoneda ⋙ G').map (ι (top 1)) ≫ (isoPow (yoneda ⋙ G') 1).hom)]
    change g (top 1) ≫ _ = _
    rw [hg]
    ext i
    have hp : proj 1 i = 𝟙 (top.{u} (L := L) 1) := by
      rw [Subsingleton.elim i 0]
      exact (mor_eq_mor_iff _ _).2 fun _ _ _ _ j => by rw [Subsingleton.elim j 0]
    have hι : ι (top.{u} (L := L) 1) = 𝟙 _ := rfl
    simp only [Category.assoc, Limits.Pi.map_π, isoPow_hom_π_assoc, isoPow_hom_π, hp, hι]
    simp

end HornCat

end LeanPool.ClassifyingTopoi.Syntactic
