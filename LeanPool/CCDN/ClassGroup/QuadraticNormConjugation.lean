/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity

/-! Explicit quadratic conjugation formulas. These identify the
two-element Galois group, the field norm, and its fixed field; they
connect the unit-norm obstruction with the involution formulation. -/

@[expose] public section
namespace CCDN
noncomputable section

variable (F K : Type*) [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [Algebra.IsSeparable F K]

/-- In a quadratic separable extension with a nontrivial automorphism `σ`, every automorphism is
either the identity or `σ`. -/
theorem quadratic_automorphism_eq_one_or
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
    (τ : K ≃ₐ[F] K) : τ = 1 ∨ τ = σ := by
  classical
  let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
  have hc : Fintype.card (K ≃ₐ[F] K) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hd]
  by_cases hτ : τ = 1
  · exact Or.inl hτ
  · right
    have he : (Finset.univ.erase (1 : K ≃ₐ[F] K)).card ≤ 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hc]
    exact Finset.card_le_one.mp he _ (by simp [hτ]) _ (by simp [hσ])

/-- Every automorphism of a quadratic separable extension is an involution. -/
theorem quadratic_automorphism_involutive
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) :
    Function.Involutive σ := by
  let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
  have hs : σ ^ 2 = 1 := by
    simpa only [IsGalois.card_aut_eq_finrank, hd] using
      (pow_card_eq_one' (x := σ))
  intro x
  simpa only [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply] using
    congrArg (fun τ : K ≃ₐ[F] K ↦ τ x) hs

/-- In a quadratic separable extension with nontrivial automorphism `σ`, the norm of `x` is
`x * σ x`. -/
theorem quadratic_norm_eq_mul_conjugate
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1) (x : K) :
    algebraMap F K (Algebra.norm F x) = x * σ x := by
  classical
  let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
  rw [Algebra.norm_eq_prod_automorphisms]
  have hp := Fintype.prod_eq_mul (f := fun τ : K ≃ₐ[F] K ↦ τ x)
    1 σ hσ.symm (fun τ hτ ↦
      False.elim ((quadratic_automorphism_eq_one_or F K hd σ hσ τ).elim hτ.1 hτ.2))
  simpa only [AlgEquiv.one_apply] using hp

end
end CCDN
