/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Linear maps vanishing at independent vectors

For linearly independent `v : Fin r → V`, the map `A ↦ (A (v i))ᵢ` from `V →ₗ[K] W` to
`Fin r → W` is surjective. Hence the linear maps that vanish at `v 0, …, v (r - 1)` form a
proportion `1 / Nat.card W ^ r` of all linear maps. A uniformly random linear map `A` stands in for
the random subspace of Fox and Lovász: its kernel contains `r` given independent vectors with
probability `Nat.card W ^ (-r)`.

## Main statements

* `LinearMap.finite_of_finite`: there are finitely many linear maps between finite modules.
* `LinearIndependent.exists_linearMap_apply_eq`: prescribing the values of a linear map at
  linearly independent vectors.
* `LinearIndependent.surjective_pi_applyₗ`: the map `A ↦ (A (v i))ᵢ` is surjective.
* `LinearIndependent.natCard_mul_pow_eq_natCard`: the count of linear maps vanishing at `r`
  linearly independent vectors.
-/

public section

open Module

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {r : ℕ} {v : Fin r → V}

/-- There are finitely many linear maps between finite modules. -/
instance LinearMap.finite_of_finite [Finite V] [Finite W] : Finite (V →ₗ[K] W) :=
  Finite.of_injective _ DFunLike.coe_injective

/-- A linear map can take any prescribed values at linearly independent vectors. -/
private lemma LinearIndependent.exists_linearMap_apply_eq (hv : LinearIndependent K v)
    (w : Fin r → W) : ∃ A : V →ₗ[K] W, ∀ i, A (v i) = w i := by
  obtain ⟨A, hA⟩ := LinearMap.exists_extend ((Basis.span hv).constr K w)
  use A
  intro i
  simpa [Finsupp.single_apply] using congr($hA (Basis.span hv i))

/-- For linearly independent `v`, the map `A ↦ (A (v i))ᵢ` is surjective. -/
private lemma LinearIndependent.surjective_pi_applyₗ (hv : LinearIndependent K v) :
    Function.Surjective
      (LinearMap.pi fun i ↦ LinearMap.applyₗ (v i) : (V →ₗ[K] W) →ₗ[K] Fin r → W) := by
  intro w
  obtain ⟨A, hA⟩ := hv.exists_linearMap_apply_eq w
  exact ⟨A, funext hA⟩

/-- The linear maps vanishing at `r` linearly independent vectors form a proportion
`1 / Nat.card W ^ r` of all linear maps. -/
lemma LinearIndependent.natCard_mul_pow_eq_natCard (hv : LinearIndependent K v) :
    Nat.card {A : V →ₗ[K] W // ∀ i, A (v i) = 0} * Nat.card W ^ r = Nat.card (V →ₗ[K] W) := by
  convert AddSubgroup.card_ker_mul_card_of_surjective (f := (LinearMap.pi fun i ↦
    LinearMap.applyₗ (v i) : (V →ₗ[K] W) →ₗ[K] Fin r → W).toAddMonoidHom) hv.surjective_pi_applyₗ
    using 2
  · exact Nat.card_congr (Equiv.subtypeEquivRight fun A ↦ by simp [funext_iff])
  · rw [Nat.card_fun, Nat.card_fin]
