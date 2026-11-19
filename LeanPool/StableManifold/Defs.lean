/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# The definitions in the statement of the stable manifold theorem

* `Function.localStableSet f p U`: the points whose forward orbit stays in `U` and tends to `p`;
* `Function.localUnstableSet f p U`: the points having a backward orbit in `U` that tends to `p`;
* `ContinuousLinearMap.stableSubspace A`: the vectors `v` with `Aⁿ v → 0`;
* `ContinuousLinearMap.unstableSubspace A`: the vectors having a backward orbit tending to `0`;
* `ContinuousLinearMap.IsHyperbolic A` (finite dimension): no complex eigenvalue of `A` has
  modulus `1`.

The upstream Palomar challenge uses these definitions in its theorem statements. See
`LeanPool.StableManifold.LocalSets` and `LeanPool.StableManifold.Linear.Subspaces` for their
properties.
-/

@[expose] public section

open Filter Topology

namespace Function

variable {X : Type*} [TopologicalSpace X]

/-- The **local stable set** of `f|_U` at `p`: the points `x` whose forward orbit `fⁿ(x)` stays in
`U` and tends to `p`. (For the iterates of `f|_U` to be defined the orbit must stay in `U`.) -/
def localStableSet (f : X → X) (p : X) (U : Set X) : Set X :=
  {x | (∀ n : ℕ, f^[n] x ∈ U) ∧ Tendsto (fun n : ℕ ↦ f^[n] x) atTop (𝓝 p)}

/-- The **local unstable set** of `f|_U` at `p`: the points `x` having a backward orbit `y`
(`y 0 = x`, `f (y (n + 1)) = y n`) in `U` that tends to `p`. For an `f` invertible on `U` it is the
local stable set of `f⁻¹|_U`. -/
def localUnstableSet (f : X → X) (p : X) (U : Set X) : Set X :=
  {x | ∃ y : ℕ → X, y 0 = x ∧ (∀ n, y n ∈ U ∧ f (y (n + 1)) = y n) ∧ Tendsto y atTop (𝓝 p)}

end Function

namespace ContinuousLinearMap

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **stable subspace** of `A`: the vectors `v` with `Aⁿ v → 0`. For a hyperbolic `A` it is
`ker pₛ(A)`, for the factor `pₛ` of the characteristic polynomial with its roots of modulus `< 1`
(`ContinuousLinearMap.exists_stableSubspace_unstableSubspace_eq_ker_aeval` in the library), that
is, the sum of the generalized eigenspaces of the eigenvalues of modulus `< 1`. -/
def stableSubspace (A : E →L[ℝ] E) : Submodule ℝ E where
  carrier := {v | Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 0)}
  add_mem' {v w} hv hw := by
    simp only [Set.mem_ofPred_eq, map_add] at hv hw ⊢
    simpa using hv.add hw
  zero_mem' := by simp
  smul_mem' c v hv := by
    simp only [Set.mem_ofPred_eq, map_smul] at hv ⊢
    simpa using hv.const_smul c

/-- The **unstable subspace** of `A`: the vectors `v` having a backward orbit tending to `0`
(`w 0 = v`, `A (w (n + 1)) = w n`, `w n → 0`). For an invertible `A` it is the stable subspace of
`A⁻¹`; for a hyperbolic `A` it is `ker pᵤ(A)`, for the factor `pᵤ` of the characteristic
polynomial with its roots of modulus `> 1`
(`ContinuousLinearMap.exists_stableSubspace_unstableSubspace_eq_ker_aeval` in the library), that
is, the sum of the generalized eigenspaces of the eigenvalues of modulus `> 1`. -/
def unstableSubspace (A : E →L[ℝ] E) : Submodule ℝ E where
  carrier := {v | ∃ w : ℕ → E, w 0 = v ∧ (∀ n, A (w (n + 1)) = w n) ∧
    Tendsto w atTop (𝓝 0)}
  add_mem' {v₁ v₂} h₁ h₂ := by
    obtain ⟨w₁, h01, hA1, ht1⟩ := h₁
    obtain ⟨w₂, h02, hA2, ht2⟩ := h₂
    refine ⟨fun n ↦ w₁ n + w₂ n, by simp [h01, h02], fun n ↦ by simp [hA1, hA2], ?_⟩
    simpa using ht1.add ht2
  zero_mem' := ⟨fun _ ↦ 0, rfl, fun _ ↦ by simp, tendsto_const_nhds⟩
  smul_mem' c v h := by
    obtain ⟨w, h0, hA, ht⟩ := h
    refine ⟨fun n ↦ c • w n, by simp [h0], fun n ↦ by simp [hA], ?_⟩
    simpa using ht.const_smul c

end General

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A linear map is **hyperbolic** if it has no eigenvalue of absolute value `1`: no complex root
of its characteristic polynomial has modulus `1`. (A real operator may have non-real eigenvalues,
so the eigenvalues are the complex roots of `LinearMap.charpoly`.) -/
def IsHyperbolic (A : E →L[ℝ] E) : Prop :=
  ∀ μ : ℂ, Polynomial.aeval μ (LinearMap.charpoly (A : E →ₗ[ℝ] E)) = 0 → ‖μ‖ ≠ 1

end FiniteDimensional

end ContinuousLinearMap
