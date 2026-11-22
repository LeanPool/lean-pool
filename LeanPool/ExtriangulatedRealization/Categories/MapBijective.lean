/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Functors bijective on morphism groups between finite direct sums

If an additive functor is bijective on the morphisms between the summands of two finite direct
sums, it is bijective on the morphisms between the direct sums. Bijectivity on a morphism set is
invariant under isomorphisms of source and target.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits

variable {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (H : 𝒞 ⥤ 𝒟)

lemma map_bijective_of_iso {X X' Y Y' : 𝒞} (e : X ≅ X') (e' : Y ≅ Y')
    (h : Function.Bijective (H.map : (X' ⟶ Y') → (H.obj X' ⟶ H.obj Y'))) :
    Function.Bijective (H.map : (X ⟶ Y) → (H.obj X ⟶ H.obj Y)) := by
  constructor
  · intro f g hfg
    have : e.inv ≫ f ≫ e'.hom = e.inv ≫ g ≫ e'.hom := h.1 (by simp only [H.map_comp, hfg])
    simpa using congrArg (fun φ => e.hom ≫ φ ≫ e'.inv) this
  · intro φ
    obtain ⟨g, hg⟩ := h.2 (H.map e.inv ≫ φ ≫ H.map e'.hom)
    refine ⟨e.hom ≫ g ≫ e'.inv, ?_⟩
    rw [H.map_comp, H.map_comp, hg]
    simp only [Category.assoc, ← H.map_comp, e'.hom_inv_id, H.map_id, Category.comp_id]
    rw [← Category.assoc, ← H.map_comp, e.hom_inv_id, H.map_id, Category.id_comp]

variable [Preadditive 𝒞] [Preadditive 𝒟] [H.Additive]

section Biproduct

variable {ι κ : Type} [Finite ι] [Finite κ] (X : ι → 𝒞) (Y : κ → 𝒞) [HasBiproduct X]
  [HasBiproduct Y]

lemma hom_ext_map_biproduct {a b : H.obj (⨁ X) ⟶ H.obj (⨁ Y)}
    (hab : ∀ i j, H.map (biproduct.ι X i) ≫ a ≫ H.map (biproduct.π Y j) =
      H.map (biproduct.ι X i) ≫ b ≫ H.map (biproduct.π Y j)) : a = b := by
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  have eX : 𝟙 (H.obj (⨁ X)) = ∑ i, H.map (biproduct.π X i) ≫ H.map (biproduct.ι X i) := by
    rw [← H.map_id, ← biproduct.total, H.map_sum]
    simp only [H.map_comp]
  have eY : 𝟙 (H.obj (⨁ Y)) = ∑ j, H.map (biproduct.π Y j) ≫ H.map (biproduct.ι Y j) := by
    rw [← H.map_id, ← biproduct.total, H.map_sum]
    simp only [H.map_comp]
  rw [← Category.id_comp a, ← Category.comp_id a, ← Category.id_comp b, ← Category.comp_id b,
    eX, eY]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [reassoc_of% (hab i j)]

lemma map_bijective_biproduct
    (h : ∀ i j, Function.Bijective (H.map : (X i ⟶ Y j) → (H.obj (X i) ⟶ H.obj (Y j)))) :
    Function.Bijective (H.map : (⨁ X ⟶ ⨁ Y) → (H.obj (⨁ X) ⟶ H.obj (⨁ Y))) := by
  constructor
  · intro f g hfg
    apply biproduct.hom_ext
    intro j
    apply biproduct.hom_ext'
    intro i
    apply (h i j).1
    simp only [H.map_comp, hfg]
  · intro φ
    choose f hf using fun i j => (h i j).2 (H.map (biproduct.ι X i) ≫ φ ≫ H.map (biproduct.π Y j))
    refine ⟨biproduct.desc fun i => biproduct.lift fun j => f i j,
      hom_ext_map_biproduct H X Y fun i j => ?_⟩
    rw [← H.map_comp, ← H.map_comp, biproduct.ι_desc_assoc, biproduct.lift_π, hf]

end Biproduct

end ExtriangulatedRealization
