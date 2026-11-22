/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Reflecting distinguished triangles

Let `Γ : 𝒯 ⥤ 𝒮` be a triangulated functor and `P` a class of objects of `𝒯` which is stable
under `⟦1⟧` and contains a cone of every morphism between its objects. If `Γ` is bijective on
morphisms between objects of `P`, then a triangle with vertices in `P` is distinguished as soon as
its image under `Γ` is: complete its first morphism to a distinguished triangle with third vertex
in `P`, compare the images under `Γ`, and lift the comparison isomorphism.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Pretriangulated

variable {𝒯 𝒮 : Type*} [Category 𝒯] [Category 𝒮] [Preadditive 𝒯] [Preadditive 𝒮]
  [HasZeroObject 𝒯] [HasZeroObject 𝒮] [HasShift 𝒯 ℤ] [HasShift 𝒮 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒯 n).Additive] [∀ n : ℤ, (shiftFunctor 𝒮 n).Additive]
  [Pretriangulated 𝒯] [Pretriangulated 𝒮] (Γ : 𝒯 ⥤ 𝒮) [Γ.CommShift ℤ] [Γ.IsTriangulated]

lemma reflect_distinguished (P : ObjectProperty 𝒯)
    (hcone : ∀ {X Y : 𝒯} (f : X ⟶ Y), P X → P Y → ∃ (Z : 𝒯) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang 𝒯 ∧ P Z)
    (hshift : ∀ X, P X → P (X⟦(1 : ℤ)⟧))
    (hbij : ∀ X Y, P X → P Y → Function.Bijective (Γ.map : (X ⟶ Y) → (Γ.obj X ⟶ Γ.obj Y)))
    (T : Triangle 𝒯) (h₁ : P T.obj₁) (h₂ : P T.obj₂) (h₃ : P T.obj₃)
    (hT : Γ.mapTriangle.obj T ∈ distTriang 𝒮) : T ∈ distTriang 𝒯 := by
  obtain ⟨Z, g, h, hT', hZ⟩ := hcone T.mor₁ h₁ h₂
  let e := isoTriangleOfIso₁₂ (Γ.mapTriangle.obj (Triangle.mk T.mor₁ g h)) (Γ.mapTriangle.obj T)
    (Γ.map_distinguished _ hT') hT (Iso.refl _) (Iso.refl _) (by simp)
  let e₃ := Triangle.π₃.mapIso e
  obtain ⟨φ, hφ⟩ := (hbij _ _ hZ h₃).2 e₃.hom
  obtain ⟨ψ, hψ⟩ := (hbij _ _ h₃ hZ).2 e₃.inv
  have hφψ : φ ≫ ψ = 𝟙 Z := (hbij _ _ hZ hZ).1 (by
    rw [Γ.map_comp, hφ, hψ]
    exact e₃.hom_inv_id.trans (Γ.map_id Z).symm)
  have hψφ : ψ ≫ φ = 𝟙 T.obj₃ := (hbij _ _ h₃ h₃).1 (by
    rw [Γ.map_comp, hφ, hψ]
    exact e₃.inv_hom_id.trans (Γ.map_id _).symm)
  have i₁ : e.inv.hom₁ = 𝟙 _ := rfl
  have i₂ : e.inv.hom₂ = 𝟙 _ := rfl
  have c₂ : T.mor₂ ≫ ψ = g := (hbij _ _ h₂ hZ).1 (by
    rw [Γ.map_comp, hψ]
    have := e.inv.comm₂
    rw [i₂, Category.id_comp] at this
    exact this)
  have c₃ : T.mor₃ = ψ ≫ h := (hbij _ _ h₃ (hshift _ h₁)).1 (by
    rw [Γ.map_comp, hψ, ← cancel_mono ((Γ.commShiftIso (1 : ℤ)).hom.app T.obj₁)]
    have := e.inv.comm₃
    rw [i₁, CategoryTheory.Functor.map_id, Category.comp_id] at this
    exact this.trans (Category.assoc _ _ _).symm)
  refine isomorphic_distinguished _ hT' _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ⟨ψ, φ, hψφ, hφψ⟩ (by simp) (by simpa using c₂) (by simpa using c₃))

omit [HasZeroObject 𝒮] [∀ n : ℤ, (shiftFunctor 𝒮 n).Additive] [Pretriangulated 𝒮] in
/-- Two distinguished triangles with the same end terms and the same third morphism have
isomorphic middle terms, compatibly with the first two morphisms. -/
lemma exists_iso_of_distinguished {A B B' C : 𝒯} {x : A ⟶ B} {y : B ⟶ C} {x' : A ⟶ B'}
    {y' : B' ⟶ C} {z : C ⟶ A⟦(1 : ℤ)⟧} (h : Triangle.mk x y z ∈ distTriang 𝒯)
    (h' : Triangle.mk x' y' z ∈ distTriang 𝒯) :
    ∃ e : B ≅ B', x ≫ e.hom = x' ∧ e.hom ≫ y' = y := by
  let e := isoTriangleOfIso₁₃ _ _ h h' (Iso.refl _) (Iso.refl _) (by simp)
  refine ⟨Triangle.π₂.mapIso e, ?_, ?_⟩
  · simpa [e] using e.hom.comm₁
  · simpa [e] using e.hom.comm₂.symm

end ExtriangulatedRealization
