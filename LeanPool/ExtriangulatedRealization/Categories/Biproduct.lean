/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Binary biproducts from explicit data

Inclusions `i₁, i₂` and projections `p₁, p₂` satisfying the biproduct identities identify an
object with the chosen binary biproduct.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits

/-- The isomorphism `Y ≅ X₁ ⊞ X₂` given by biproduct data on `Y`. -/
@[simps!]
noncomputable def isoBiprodOfTotal {𝒯 : Type*} [Category 𝒯] [Preadditive 𝒯]
    [HasBinaryBiproducts 𝒯] {Y X₁ X₂ : 𝒯} (i₁ : X₁ ⟶ Y) (i₂ : X₂ ⟶ Y) (p₁ : Y ⟶ X₁)
    (p₂ : Y ⟶ X₂) (h₁ : i₁ ≫ p₁ = 𝟙 _) (h₂ : i₂ ≫ p₂ = 𝟙 _) (h₁₂ : i₁ ≫ p₂ = 0)
    (h₂₁ : i₂ ≫ p₁ = 0) (h : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 Y) : Y ≅ X₁ ⊞ X₂ :=
  let bicone : BinaryBicone X₁ X₂ := ⟨Y, p₁, p₂, i₁, i₂, h₁, h₁₂, h₂₁, h₂⟩
  biprod.uniqueUpToIso _ _ (isBinaryBilimitOfTotal bicone h)

/-- An additive functor maps a bicone satisfying the totality identity to a biproduct. -/
@[simps!]
noncomputable def mapBiprodOfTotal {𝒮 𝒯 : Type*} [Category 𝒮] [Preadditive 𝒮]
    [Category 𝒯] [Preadditive 𝒯] [HasBinaryBiproducts 𝒯]
    (F : 𝒮 ⥤ 𝒯) [F.Additive] {X Y : 𝒮} (bicone : BinaryBicone X Y)
    (total : bicone.fst ≫ bicone.inl + bicone.snd ≫ bicone.inr = 𝟙 bicone.pt) :
    F.obj bicone.pt ≅ F.obj X ⊞ F.obj Y :=
  biprod.uniqueUpToIso _ _ (isBinaryBilimitOfTotal (F.mapBinaryBicone bicone) (by
    change F.map bicone.fst ≫ F.map bicone.inl + F.map bicone.snd ≫ F.map bicone.inr =
      𝟙 (F.obj bicone.pt)
    rw [← F.map_comp, ← F.map_comp, ← F.map_add, total, F.map_id]))

end ExtriangulatedRealization
