/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.CD.Closure

/-!
# The extension bifunctor of `C(D)`

`E(C, A) = Ext¹(ρC, ρA)`; pushforward and pullback are composition with `ρ` of morphisms in
degree `0`, so `E` is `k`-bilinear (axiom (ET1)). Realizations are closed under isomorphisms of
the middle term.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I] (D : Iᵒᵖ ⥤ ModuleCat.{u} k)

attribute [local instance] HasExt.standard

instance rho0_linear : (rho0 D).Linear k where
  map_smul {X Y} f r := by
    rcases X with _ | a
    · exact (isZero_zero _).eq_of_src _ _
    rcases Y with _ | b
    · exact (isZero_zero _).eq_of_tgt _ _
    · rfl

instance rho_linear : (rho D).Linear k where
  map_smul {M N} f r := by
    change biproduct.matrix (fun i j => (rho0 D).map ((r • f) i j)) =
      r • biproduct.matrix (fun i j => (rho0 D).map (f i j))
    apply biproduct.hom_ext
    intro j
    apply biproduct.hom_ext'
    intro i
    rw [biproduct.matrix_π, biproduct.ι_desc, Linear.smul_comp, Linear.comp_smul,
      biproduct.matrix_π, biproduct.ι_desc]
    exact (rho0 D).map_smul r (f i j)

lemma cdData_push {C A A' : CD D} (a : A ⟶ A') (δ : (cdData D).Ext C A) :
    ((cdData D).push a δ : Abelian.Ext.{u + 1} _ _ 1) =
      (δ : Abelian.Ext.{u + 1} ((rho D).obj C) ((rho D).obj A) 1).comp
        (Abelian.Ext.mk₀ ((rho D).map a)) (add_zero 1) := rfl

lemma cdData_pull {C'' C A : CD D} (c : C'' ⟶ C) (δ : (cdData D).Ext C A) :
    ((cdData D).pull c δ : Abelian.Ext.{u + 1} _ _ 1) =
      (Abelian.Ext.mk₀ ((rho D).map c)).comp
        (δ : Abelian.Ext.{u + 1} ((rho D).obj C) ((rho D).obj A) 1) (zero_add 1) := rfl

lemma cdData_push_add {C A A' : CD D} (a a' : A ⟶ A') (δ : (cdData D).Ext C A) :
    (cdData D).push (a + a') δ = (cdData D).push a δ + (cdData D).push a' δ := by
  change (δ : Abelian.Ext.{u + 1} ((rho D).obj C) ((rho D).obj A) 1).comp
      (Abelian.Ext.mk₀ ((rho D).map (a + a'))) (add_zero 1) = _
  rw [Functor.map_add, Abelian.Ext.mk₀_add]
  exact Abelian.Ext.comp_add _ _ _ _

lemma cdData_push_smul {C A A' : CD D} (r : k) (a : A ⟶ A') (δ : (cdData D).Ext C A) :
    (cdData D).push (r • a) δ = r • (cdData D).push a δ := by
  change (δ : Abelian.Ext.{u + 1} ((rho D).obj C) ((rho D).obj A) 1).comp
      (Abelian.Ext.mk₀ ((rho D).map (r • a))) (add_zero 1) = _
  rw [Functor.map_smul, Abelian.Ext.mk₀_smul]
  exact Abelian.Ext.comp_smul _ _ _ _

lemma cdData_pull_add {C'' C A : CD D} (c c' : C'' ⟶ C) (δ : (cdData D).Ext C A) :
    (cdData D).pull (c + c') δ = (cdData D).pull c δ + (cdData D).pull c' δ := by
  change (Abelian.Ext.mk₀ ((rho D).map (c + c'))).comp
      (δ : Abelian.Ext.{u + 1} ((rho D).obj C) ((rho D).obj A) 1) (zero_add 1) = _
  rw [Functor.map_add, Abelian.Ext.mk₀_add]
  exact Abelian.Ext.add_comp _ _ _ _

lemma cdData_pull_smul {C'' C A : CD D} (r : k) (c : C'' ⟶ C) (δ : (cdData D).Ext C A) :
    (cdData D).pull (r • c) δ = r • (cdData D).pull c δ := by
  change (Abelian.Ext.mk₀ ((rho D).map (r • c))).comp
      (δ : Abelian.Ext.{u + 1} ((rho D).obj C) ((rho D).obj A) 1) (zero_add 1) = _
  rw [Functor.map_smul, Abelian.Ext.mk₀_smul]
  exact Abelian.Ext.smul_comp _ _ _ _

/-- Realizations are closed under isomorphisms of the middle term. -/
lemma cdData_realizes_iso {A B B' C : CD D} {δ : (cdData D).Ext C A} {x : A ⟶ B} {y : B ⟶ C}
    (b : B ≅ B') (h : (cdData D).Realizes δ x y) :
    (cdData D).Realizes δ (x ≫ b.hom) (b.inv ≫ y) := by
  obtain ⟨w, ⟨hS, hcls⟩, N, hN, θ, x', y', h1, h2, h3⟩ := h
  have w' : (x ≫ b.hom) ≫ (b.inv ≫ y) = 0 := by simp [w]
  let e : ShortComplex.mk ((rho D).map x) ((rho D).map y)
      (by rw [← Functor.map_comp, w, Functor.map_zero]) ≅
      ShortComplex.mk ((rho D).map (x ≫ b.hom)) ((rho D).map (b.inv ≫ y))
        (by rw [← Functor.map_comp, w', Functor.map_zero]) :=
    ShortComplex.isoMk (Iso.refl _) ((rho D).mapIso b) (Iso.refl _)
      (by simp) (by simp [← Functor.map_comp])
  have hS' := ShortComplex.shortExact_of_iso e hS
  refine ⟨w', ⟨hS', ?_⟩, N, hN, b.symm ≪≫ θ, x', y', h1, ?_, ?_⟩
  · have hnat := hS.extClass_naturality hS' e.hom
    change hS.extClass.comp (Abelian.Ext.mk₀ (𝟙 _)) (add_zero 1) =
      (Abelian.Ext.mk₀ (𝟙 _)).comp hS'.extClass (zero_add 1) at hnat
    rw [Abelian.Ext.comp_mk₀_id, Abelian.Ext.mk₀_id_comp] at hnat
    rw [← hnat, hcls]
  · simp [h2]
  · simp [h3]

lemma cdData_pull_id {C A : CD D} (δ : (cdData D).Ext C A) : (cdData D).pull (𝟙 C) δ = δ := by
  change (Abelian.Ext.mk₀ ((rho D).map (𝟙 C))).comp
      (δ : Abelian.Ext.{u + 1} ((rho D).obj C) ((rho D).obj A) 1) (zero_add 1) = δ
  rw [CategoryTheory.Functor.map_id]
  exact Abelian.Ext.mk₀_id_comp _

lemma cdData_pull_zero {C' C A : CD D} (δ : (cdData D).Ext C A) :
    (cdData D).pull (0 : C' ⟶ C) δ = 0 := by
  change (Abelian.Ext.mk₀ ((rho D).map (0 : C' ⟶ C))).comp
      (δ : Abelian.Ext.{u + 1} ((rho D).obj C) ((rho D).obj A) 1) (zero_add 1) = 0
  rw [Functor.map_zero, Abelian.Ext.mk₀_zero]
  exact Abelian.Ext.zero_comp (X := (rho D).obj C') (Y := (rho D).obj C) (n := 0)
    (δ : Abelian.Ext.{u + 1} ((rho D).obj C) ((rho D).obj A) 1) 1 (zero_add 1)

lemma cdData_pull_inl_sum {C₁ A₁ C₂ A₂ : CD D} (δ : (cdData D).Ext C₁ A₁)
    (δ' : (cdData D).Ext C₂ A₂) :
    (cdData D).pull biprod.inl ((cdData D).sum δ δ') = (cdData D).push biprod.inl δ := by
  rw [ExtriangulatedData.sum, map_add, ExtriangulatedData.pull_comp, ExtriangulatedData.pull_comp,
    biprod.inl_fst,
    biprod.inl_snd, cdData_pull_id, cdData_pull_zero, add_zero]

lemma cdData_pull_inr_sum {C₁ A₁ C₂ A₂ : CD D} (δ : (cdData D).Ext C₁ A₁)
    (δ' : (cdData D).Ext C₂ A₂) :
    (cdData D).pull biprod.inr ((cdData D).sum δ δ') = (cdData D).push biprod.inr δ' := by
  rw [ExtriangulatedData.sum, map_add, ExtriangulatedData.pull_comp, ExtriangulatedData.pull_comp,
    biprod.inr_fst,
    biprod.inr_snd, cdData_pull_id, cdData_pull_zero, zero_add]

end ExtriangulatedRealization
