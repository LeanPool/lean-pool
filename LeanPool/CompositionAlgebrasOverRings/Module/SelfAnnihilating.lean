/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Functionals that annihilate their own argument

A linear form `φ : M → R` is **self-annihilating** if `φ x • x = 0` for every `x`. On a finitely
generated projective module this forces `φ = 0`.

Over a free module the reason is immediate: a basis vector `e` has `φ e • e = 0`, and a basis
vector is not killed by any nonzero scalar. Over a projective module it is *false* pointwise —
`φ x • x = 0` says only that `φ x` annihilates `x` — and what rescues it is that the hypothesis is
required for *every* `x`, so it survives base change and can be checked after localizing at each
maximal ideal, where the module is free.

This is the mechanism behind `GPR 16.14(b)`: an identity of the shape `c(x) • x = d(x) • 1`,
which is what flexibility gives in a conic algebra, collapses to `c = 0` as soon as the algebra is
projective — see `CompositionAlgebras/Conic/Projective.lean`.

## Main results

* `LinearMap.eq_zero_of_smul_self_eq_zero_of_free` : the free case.
* `LinearMap.eq_zero_of_smul_self_eq_zero` : the finitely generated projective case.

## Implementation notes

The projective case is proved by base change to `Localization.AtPrime 𝔪` rather than by
localizing the module: `LinearMap.baseChange` and `TensorProduct.induction_on` are enough, and the
hypothesis transfers to `S ⊗[R] M` in two steps — its linearization `φ u • v + φ v • u = 0` is
bi-additive and so reduces to pure tensors, and the hypothesis itself then follows from the
linearization by induction. This is the same two-step shape as the degree-two identity in
`CompositionAlgebras/Conic/BaseChange.lean`.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace LinearMap

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The linearization of `φ x • x = 0`. -/
theorem smul_add_smul_eq_zero_of_smul_self_eq_zero {φ : M →ₗ[R] R}
    (h : ∀ x : M, φ x • x = 0) (u v : M) : φ u • v + φ v • u = 0 := by
  have huv := h (u + v)
  rw [map_add, add_smul, smul_add, smul_add, h u, h v] at huv
  simpa using huv

/-- **A self-annihilating functional on a free module is zero.** A basis vector is killed by no
nonzero scalar. -/
theorem eq_zero_of_smul_self_eq_zero_of_free [Module.Free R M] (φ : M →ₗ[R] R)
    (h : ∀ x : M, φ x • x = 0) : φ = 0 := by
  classical
  set b := Module.Free.chooseBasis R M with hb
  refine b.ext fun i ↦ ?_
  have hi := congrArg (fun z ↦ b.repr z i) (h (b i))
  simpa using hi

section BaseChange

variable (S : Type*) [CommRing S] [Algebra R S]

variable {S}

/-- Moving a scalar of `R` out of the `S`-action on a pure tensor. -/
private theorem smul_smul_tmul (c : R) (s s' : S) (x : M) :
    (c • s) • (s' ⊗ₜ[R] x) = (s * s') ⊗ₜ[R] (c • x) := by
  rw [smul_assoc, TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.smul_tmul',
    TensorProduct.smul_tmul]

/-- The linearized hypothesis transfers to the base change: it is bi-additive, so it is enough to
check it on pure tensors. -/
theorem smul_add_smul_baseChange_eq_zero {φ : M →ₗ[R] R} (h : ∀ x : M, φ x • x = 0)
    (z w : S ⊗[R] M) :
    Module.Dual.baseChange S φ z • w + Module.Dual.baseChange S φ w • z = 0 := by
  induction z with
  | add z₁ z₂ h₁ h₂ =>
    simp only [map_add, add_smul, smul_add]
    linear_combination (norm := module) h₁ + h₂
  | tmul s x =>
    induction w with
    | add w₁ w₂ h₁ h₂ =>
      simp only [map_add, add_smul, smul_add]
      linear_combination (norm := module) h₁ + h₂
    | tmul s' x' =>
      rw [Module.Dual.baseChange_apply_tmul, Module.Dual.baseChange_apply_tmul, smul_smul_tmul,
        smul_smul_tmul, mul_comm s' s, ← TensorProduct.tmul_add,
        smul_add_smul_eq_zero_of_smul_self_eq_zero h, TensorProduct.tmul_zero]

/-- Self-annihilation transfers to the base change. -/
theorem smul_self_baseChange_eq_zero {φ : M →ₗ[R] R} (h : ∀ x : M, φ x • x = 0)
    (z : S ⊗[R] M) : Module.Dual.baseChange S φ z • z = 0 := by
  induction z with
  | tmul s x =>
    rw [Module.Dual.baseChange_apply_tmul, smul_smul_tmul, h x, TensorProduct.tmul_zero]
  | add z w hz hw =>
    have hlin := smul_add_smul_baseChange_eq_zero (S := S) h z w
    simp only [map_add, add_smul, smul_add]
    linear_combination (norm := module) hz + hw + hlin

end BaseChange

/-- **A self-annihilating functional on a finitely generated projective module is zero.**

Base change to `Localization.AtPrime 𝔪` preserves the hypothesis, and there the module is free,
so the base-changed functional vanishes; hence `φ x` dies in every localization, hence is `0`. -/
theorem eq_zero_of_smul_self_eq_zero [Module.Finite R M] [Module.Projective R M]
    (φ : M →ₗ[R] R)
    (h : ∀ x : M, φ x • x = 0) : φ = 0 := by
  ext x
  refine eq_zero_of_localization (φ x) fun J hJ ↦ ?_
  set S := Localization.AtPrime J with hS
  have : Module.Free S (S ⊗[R] M) := Module.free_of_flat_of_isLocalRing
  have hψ : Module.Dual.baseChange S φ = 0 :=
    eq_zero_of_smul_self_eq_zero_of_free _ (smul_self_baseChange_eq_zero h)
  have := congrArg (fun ψ ↦ ψ ((1 : S) ⊗ₜ[R] x)) hψ
  simpa [Algebra.smul_def] using this

end LinearMap
