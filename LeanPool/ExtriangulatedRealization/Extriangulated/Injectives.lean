/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Statement

/-!
# Injective objects of an extriangulated category

An object `U` with `E(-, U) = 0` is injective: for a conflation `A → B → C` realizing `δ` and
`f : A ⟶ U`, the extension `f_* δ` vanishes, so condition `(∗)` applied to the split conflation
`U → U ⊞ C → C` gives a morphism `B ⟶ U ⊞ C` extending `f`.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Statement

variable {k : Type*} [CommRing k] {C : Type*} [Category C] [Preadditive C] [Linear k C]
  [HasBinaryBiproducts C] {𝔼 : ExtriangulatedData k C}

/-- An object `U` with `E(-, U) = 0` is injective. -/
lemma isInjectiveObject_of_ext_eq_zero (h𝔼 : 𝔼.IsExtriangulated) {U : C}
    (hU : ∀ (C' : C) (δ : 𝔼.Ext C' U), δ = 0) : 𝔼.IsInjectiveObject U := by
  intro A B C' δ x y hr f
  obtain ⟨b, hb, -⟩ := h𝔼.realizes_morphism hr (h𝔼.realizes_zero U C') f (𝟙 C')
    (by rw [hU _ (𝔼.push f δ), map_zero])
  exact ⟨b ≫ biprod.fst, by rw [← Category.assoc, hb, Category.assoc, biprod.inl_fst,
    Category.comp_id]⟩

end ExtriangulatedRealization
