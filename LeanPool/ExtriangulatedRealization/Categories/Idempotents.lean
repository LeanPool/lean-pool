/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Splitting idempotents

* An idempotent on `B ⊞ Z` with vanishing component `B ⟶ Z` splits as soon as idempotents on
  `B` and on `Z` split: its diagonal blocks are idempotents, and their splittings combine with
  the off-diagonal component into a splitting.
* An idempotent square matrix over a field factors as `E * I` with `I * E = 1`, through the
  range of the corresponding linear map.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits

/-- Idempotents on an object split. -/
def IdempotentsSplit {C : Type*} [Category C] (X : C) : Prop :=
  ∀ p : X ⟶ X, p ≫ p = p → ∃ (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p

section Triangular

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

/-- A triangular idempotent on `B ⊞ Z` splits when idempotents on `B` and `Z` split. -/
lemma split_biprod_of_triangular {B Z : C} (hB : IdempotentsSplit B) (hZ : IdempotentsSplit Z)
    (p : B ⊞ Z ⟶ B ⊞ Z) (hp : p ≫ p = p) (h0 : biprod.inl ≫ p ≫ biprod.snd = 0) :
    ∃ (Y : C) (i : Y ⟶ B ⊞ Z) (e : B ⊞ Z ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p := by
  obtain ⟨a, ha⟩ : ∃ a : B ⟶ B, biprod.inl ≫ p ≫ biprod.fst = a := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : Z ⟶ Z, biprod.inr ≫ p ≫ biprod.snd = d := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Z ⟶ B, biprod.inr ≫ p ≫ biprod.fst = g := ⟨_, rfl⟩
  have hinl : biprod.inl ≫ p = a ≫ biprod.inl := by
    apply biprod.hom_ext
    · rw [Category.assoc, ha, Category.assoc, biprod.inl_fst, Category.comp_id]
    · rw [Category.assoc, h0, Category.assoc, biprod.inl_snd, comp_zero]
  have hinr : biprod.inr ≫ p = g ≫ biprod.inl + d ≫ biprod.inr := by
    apply biprod.hom_ext
    · rw [Category.assoc, hg, Preadditive.add_comp, Category.assoc, Category.assoc,
        biprod.inl_fst, biprod.inr_fst, Category.comp_id, comp_zero, add_zero]
    · rw [Category.assoc, hd, Preadditive.add_comp, Category.assoc, Category.assoc,
        biprod.inl_snd, biprod.inr_snd, Category.comp_id, comp_zero, zero_add]
  have hl : a ≫ a ≫ (biprod.inl : B ⟶ B ⊞ Z) = a ≫ biprod.inl := by
    have h := biprod.inl ≫= hp
    rw [← Category.assoc, hinl, Category.assoc, hinl] at h
    exact h
  have haa : a ≫ a = a := by simpa using hl =≫ biprod.fst
  have hr : g ≫ a ≫ (biprod.inl : B ⟶ B ⊞ Z) + d ≫ (g ≫ biprod.inl + d ≫ biprod.inr) =
      g ≫ biprod.inl + d ≫ biprod.inr := by
    have h := biprod.inr ≫= hp
    rw [← Category.assoc, hinr, Preadditive.add_comp, Category.assoc, hinl, Category.assoc,
      hinr] at h
    exact h
  have hgad : g ≫ a + d ≫ g = g := by simpa using hr =≫ biprod.fst
  have hdd : d ≫ d = d := by simpa using hr =≫ biprod.snd
  obtain ⟨B₁, iB, rB, hB₁, hB₂⟩ := hB a haa
  obtain ⟨Z₁, iZ, rZ, hZ₁, hZ₂⟩ := hZ d hdd
  have hrB : a ≫ rB = rB := by rw [← hB₂, Category.assoc, hB₁, Category.comp_id]
  have hiZ : iZ ≫ d = iZ := by rw [← hZ₂, ← Category.assoc, hZ₁, Category.id_comp]
  have hgz : iZ ≫ g ≫ rB = 0 := by
    have hdg : d ≫ g = g - g ≫ a := eq_sub_of_add_eq' hgad
    rw [← hiZ, Category.assoc, ← Category.assoc d, hdg, Preadditive.sub_comp, Category.assoc,
      hrB, sub_self, comp_zero]
  refine ⟨B₁ ⊞ Z₁, biprod.desc (iB ≫ biprod.inl) (iZ ≫ (g ≫ biprod.inl + biprod.inr)),
    biprod.lift (biprod.fst ≫ rB + biprod.snd ≫ g ≫ rB) (biprod.snd ≫ rZ), ?_, ?_⟩
  · apply biprod.hom_ext' <;> apply biprod.hom_ext
    · simp [hB₁]
    · simp
    · simp only [biprod.inr_desc_assoc, Category.assoc, biprod.lift_fst, Preadditive.add_comp,
        Preadditive.comp_add, biprod.inl_fst_assoc, biprod.inl_snd_assoc, zero_comp, add_zero,
        biprod.inr_fst_assoc, biprod.inr_snd_assoc, zero_add, Category.id_comp,
        biprod.inr_fst]
      rw [hgz, add_zero]
    · simp [hZ₁]
  · apply biprod.hom_ext'
    · rw [hinl, ← hB₂]
      simp
    · rw [hinr]
      simp only [biprod.lift_desc, Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
        biprod.inr_fst_assoc, biprod.inr_snd_assoc, zero_comp, zero_add]
      have hB₂' : rB ≫ iB ≫ (biprod.inl : B ⟶ B ⊞ Z) = a ≫ biprod.inl := by
        rw [← Category.assoc, hB₂]
      have hZ₂' : ∀ {W : C} (h : Z ⟶ W), rZ ≫ iZ ≫ h = d ≫ h := fun h => by
        rw [← Category.assoc, hZ₂]
      rw [hB₂', hZ₂', hZ₂', ← add_assoc, ← Category.assoc g, ← Category.assoc d,
        ← Preadditive.add_comp, hgad]

end Triangular

section Matrix

variable {k : Type*} [Field k]

/-- An idempotent square matrix over a field factors through its rank. -/
lemma Matrix.exists_factor_of_mul_self {ι : Type*} [Fintype ι]
    (P : Matrix ι ι k) (hP : P * P = P) :
    ∃ (r : ℕ) (E : Matrix ι (Fin r) k) (I : Matrix (Fin r) ι k), I * E = 1 ∧ E * I = P := by
  classical
  let L := Matrix.toLin' P
  have hLL : L ∘ₗ L = L := by rw [← Matrix.toLin'_mul, hP]
  let W := LinearMap.range L
  let b := Module.finBasis k W
  let φE : (Fin (Module.finrank k W) → k) →ₗ[k] (ι → k) :=
    W.subtype ∘ₗ b.equivFun.symm.toLinearMap
  let φI : (ι → k) →ₗ[k] (Fin (Module.finrank k W) → k) :=
    b.equivFun.toLinearMap ∘ₗ L.rangeRestrict
  have hfix : ∀ w ∈ W, L w = w := by
    rintro _ ⟨v, rfl⟩
    exact LinearMap.congr_fun hLL v
  have h1 : φI ∘ₗ φE = LinearMap.id := by
    apply LinearMap.ext
    intro c
    change b.equivFun (L.rangeRestrict (b.equivFun.symm c : W)) = c
    have : L.rangeRestrict (b.equivFun.symm c : W) = b.equivFun.symm c :=
      Subtype.ext (hfix _ (b.equivFun.symm c).2)
    rw [this, LinearEquiv.apply_symm_apply]
  have h2 : φE ∘ₗ φI = L := by
    apply LinearMap.ext
    intro v
    change ((b.equivFun.symm (b.equivFun (L.rangeRestrict v)) : W) : ι → k) = L v
    rw [LinearEquiv.symm_apply_apply]
    rfl
  refine ⟨Module.finrank k W, LinearMap.toMatrix' φE, LinearMap.toMatrix' φI, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, h1, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp, h2, LinearMap.toMatrix'_toLin']

end Matrix

end ExtriangulatedRealization
