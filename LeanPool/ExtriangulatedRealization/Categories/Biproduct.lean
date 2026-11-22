/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

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
@[simps]
noncomputable def isoBiprodOfTotal {𝒯 : Type*} [Category 𝒯] [Preadditive 𝒯]
    [HasBinaryBiproducts 𝒯] {Y X₁ X₂ : 𝒯} (i₁ : X₁ ⟶ Y) (i₂ : X₂ ⟶ Y) (p₁ : Y ⟶ X₁)
    (p₂ : Y ⟶ X₂) (h₁ : i₁ ≫ p₁ = 𝟙 _) (h₂ : i₂ ≫ p₂ = 𝟙 _) (h₁₂ : i₁ ≫ p₂ = 0)
    (h₂₁ : i₂ ≫ p₁ = 0) (h : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 Y) : Y ≅ X₁ ⊞ X₂ where
  hom := biprod.lift p₁ p₂
  inv := biprod.desc i₁ i₂
  hom_inv_id := by rw [biprod.lift_desc, h]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp [h₁, h₂, h₁₂, h₂₁]

end ExtriangulatedRealization
