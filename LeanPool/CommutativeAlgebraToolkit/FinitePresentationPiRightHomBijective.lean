/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Tensoring a finitely presented module with a product

For a finitely presented `R`-module `M` and any family of `R`-modules `P i`, the canonical map
`M ⊗[R] (Π i, P i) → Π i, M ⊗[R] P i` is bijective. The proof reduces to finite free modules
through a presentation `R^m → R^n → M → 0` and the five lemma, using that products of exact
sequences are exact.

## Main statements

* `Function.Exact.piMap`, `Function.Exact.prodMap`: products of exact pairs are exact (and their
  multiplicative versions `Function.MulExact.piMap`, `Function.MulExact.prodMap`).
* `Module.piRightHom_bijective_of_finite_free`: the case `M = κ → R` with `κ` finite.
* `Module.FinitePresentation.piRightHom_bijective`: the case of a finitely presented `M`.
-/

public section

namespace Function.MulExact

@[to_additive /-- A product of exact pairs is exact. -/]
lemma piMap {ι : Type*} {α β γ : ι → Type*} [∀ i, One (γ i)] {f : ∀ i, α i → β i}
    {g : ∀ i, β i → γ i} (h : ∀ i, MulExact (f i) (g i)) : MulExact (Pi.map f) (Pi.map g) := by
  refine fun y ↦ ⟨fun hy ↦ ?_, ?_⟩
  · choose x hx using fun i ↦ (h i (y i)).1 (congrFun hy i)
    exact ⟨x, funext hx⟩
  · rintro ⟨x, rfl⟩
    exact funext fun i ↦ (h i _).2 ⟨x i, rfl⟩

@[to_additive /-- A product of two exact pairs is exact. -/]
lemma prodMap {M₁ N₁ P₁ M₂ N₂ P₂ : Type*} [One P₁] [One P₂] {f₁ : M₁ → N₁} {g₁ : N₁ → P₁}
    {f₂ : M₂ → N₂} {g₂ : N₂ → P₂} (h₁ : MulExact f₁ g₁) (h₂ : MulExact f₂ g₂) :
    MulExact (Prod.map f₁ f₂) (Prod.map g₁ g₂) := by
  rintro ⟨y₁, y₂⟩
  simp [Set.range_prodMap, h₁ y₁, h₂ y₂]

end Function.MulExact

section Pi

open TensorProduct LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {ι : Type*} (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]

variable (R) in
/-- For `κ` finite, the canonical map `(κ → R) ⊗[R] (Π i, P i) → Π i, (κ → R) ⊗[R] P i` is
bijective. -/
lemma Module.piRightHom_bijective_of_finite_free (κ : Type*) [Finite κ] :
    Function.Bijective (piRightHom R R (κ → R) P) := by
  classical
  have := Fintype.ofFinite κ
  have key : ⇑(LinearEquiv.piCongrRight fun i ↦
        TensorProduct.comm R (κ → R) (P i) ≪≫ₗ piScalarRight R R (P i) κ) ∘
        ⇑(piRightHom R R (κ → R) P) =
      Equiv.piComm _ ∘ ⇑(TensorProduct.comm R (κ → R) (Π i, P i) ≪≫ₗ
        piScalarRight R R (Π i, P i) κ) := by
    ext x : 1
    induction x with
    | tmul a q => ext; simp [Function.swap]
    | add x y hx hy =>
      simp only [Function.comp_apply, map_add] at hx hy ⊢
      rw [hx, hy]
      rfl
  rw [← EquivLike.comp_bijective _ (LinearEquiv.piCongrRight fun i ↦
    TensorProduct.comm R (κ → R) (P i) ≪≫ₗ piScalarRight R R (P i) κ), key]
  exact (Equiv.bijective _).comp (LinearEquiv.bijective _)

variable (R M) in
/-- If `M` is a finitely presented `R`-module, then for any family of `R`-modules `P i`, the
canonical map `M ⊗[R] (Π i, P i) → Π i, M ⊗[R] P i` is bijective. -/
@[stacks 059K "(1) ⇒ (2)"]
theorem Module.FinitePresentation.piRightHom_bijective [Module.FinitePresentation R M] :
    Function.Bijective (piRightHom R R M P) := by
  obtain ⟨n, m, f, g, hf, hfg⟩ := Module.FinitePresentation.exists_fin' R M
  exact bijective_of_surjective_of_bijective_of_right_exact (g.rTensor _) (f.rTensor _)
    (piMap fun i ↦ g.rTensor (P i)) (piMap fun i ↦ f.rTensor (P i)) _ _ _
    (TensorProduct.ext' fun _ _ ↦ by ext; simp) (TensorProduct.ext' fun _ _ ↦ by ext; simp)
    (rTensor_exact _ hfg hf) (Function.Exact.piMap fun i ↦ rTensor_exact _ hfg hf)
    (piRightHom_bijective_of_finite_free R P _).2 (piRightHom_bijective_of_finite_free R P _)
    (rTensor_surjective _ hf)
    (by simpa using Function.Surjective.piMap fun i ↦ rTensor_surjective _ hf)

end Pi
