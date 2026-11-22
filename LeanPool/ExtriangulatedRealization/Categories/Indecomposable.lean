/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Statement

/-!
# Objects whose endomorphisms are scalars

In a `k`-linear category over a field, a nonzero object all of whose endomorphisms are scalar
multiples of the identity is indecomposable and has local endomorphism ring `k`.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Statement

variable {k : Type*} [Field k] {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞]

section

variable {X : 𝒞} (h₁ : 𝟙 X ≠ 0) (h : ∀ f : X ⟶ X, ∃ c : k, f = c • 𝟙 X)
include h₁

lemma smul_id_injective : Function.Injective (fun c : k => c • 𝟙 X) :=
  smul_left_injective k h₁

include h in
lemma existsUnique_smul_id (f : X ⟶ X) : ∃! c : k, f = c • 𝟙 X := by
  obtain ⟨c, hc⟩ := h f
  exact ⟨c, hc, fun c' hc' => smul_id_injective h₁ (hc'.symm.trans hc)⟩

include h in
/-- The endomorphism ring is local. -/
lemma isLocalRing_end : IsLocalRing (End X) := by
  have : Nontrivial (End X) := ⟨⟨1, 0, fun h' => h₁ (congrArg End.asHom h')⟩⟩
  refine IsLocalRing.of_surjective' (algebraMap k (End X)) fun f => ?_
  obtain ⟨c, hc⟩ := h f.asHom
  refine ⟨c, ?_⟩
  ext
  rw [Algebra.algebraMap_eq_smul_one, End.smul_asHom, hc]
  rfl

variable [HasFiniteBiproducts 𝒞] [HasBinaryBiproducts 𝒞]

omit [HasFiniteBiproducts 𝒞] in
include h in
/-- A nonzero object with scalar endomorphisms is indecomposable. -/
lemma isIndecomposable_of_endo_scalar : Indecomposable X := by
  refine ⟨fun hX => h₁ (hX.eq_of_src _ _), fun Y Z e => ?_⟩
  let p : X ⟶ X := e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv
  have hp : p ≫ p = p := by simp [p]
  obtain ⟨c, hc⟩ := h p
  have hcc : IsIdempotentElem c := by
    apply smul_id_injective h₁
    have h2 := hp
    rw [hc, Linear.smul_comp, Linear.comp_smul, Category.comp_id, smul_smul] at h2
    exact h2
  have key : biprod.fst ≫ biprod.inl = e.inv ≫ p ≫ e.hom := by simp [p]
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hcc with rfl | rfl
  · left
    rw [IsZero.iff_id_eq_zero]
    calc 𝟙 Y = biprod.inl ≫ (biprod.fst ≫ biprod.inl) ≫ biprod.fst := by simp
      _ = 0 := by rw [key, hc, zero_smul]; simp
  · right
    rw [IsZero.iff_id_eq_zero]
    calc 𝟙 Z = biprod.inr ≫ (biprod.fst ≫ biprod.inl) ≫ biprod.snd := by
          rw [key, hc, one_smul]; simp
      _ = 0 := by simp

end

end ExtriangulatedRealization
