/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-! # Stable and unstable subspaces of a continuous linear map -/

@[expose] public section

open Filter Topology

namespace ContinuousLinearMap

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

theorem mem_stableSubspace {A : E →L[ℝ] E} {v : E} :
    v ∈ A.stableSubspace ↔ Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 0) :=
  Iff.rfl

theorem mem_unstableSubspace {A : E →L[ℝ] E} {v : E} :
    v ∈ A.unstableSubspace ↔
      ∃ w : ℕ → E, w 0 = v ∧ (∀ n, A (w (n + 1)) = w n) ∧ Tendsto w atTop (𝓝 0) :=
  Iff.rfl

/-- The stable subspace is `A`-invariant.

Proof: `Aⁿ (A v) = A (Aⁿ v) → A 0 = 0`. -/
theorem map_mem_stableSubspace {A : E →L[ℝ] E} {v : E} (hv : v ∈ A.stableSubspace) :
    A v ∈ A.stableSubspace := by
  rw [mem_stableSubspace] at hv ⊢
  refine ((tendsto_add_atTop_iff_nat 1).2 hv).congr fun n ↦ ?_
  rw [pow_succ, mul_apply_eq_comp]

/-- The unstable subspace is `A`-invariant.

Proof: the backward orbit `0 ↦ A v`, `n + 1 ↦ w n`. -/
theorem map_mem_unstableSubspace {A : E →L[ℝ] E} {v : E} (hv : v ∈ A.unstableSubspace) :
    A v ∈ A.unstableSubspace := by
  obtain ⟨w, h0, hA, ht⟩ := hv
  refine ⟨fun n ↦ match n with | 0 => A v | n + 1 => w n, rfl, fun n ↦ ?_,
    (tendsto_add_atTop_iff_nat 1).1 ht⟩
  cases n with
  | zero => simp [h0]
  | succ n => exact hA n

/-- Every point of a backward orbit tending to zero lies in the unstable subspace. -/
theorem mem_unstableSubspace_of_backwardOrbit {A : E →L[ℝ] E} {w : ℕ → E}
    (hA : ∀ n, A (w (n + 1)) = w n) (ht : Tendsto w atTop (𝓝 0)) (n : ℕ) :
    w n ∈ A.unstableSubspace :=
  ⟨fun k ↦ w (k + n), by simp, fun k ↦ by simpa only [Nat.add_right_comm k 1 n] using hA (k + n),
    (tendsto_add_atTop_iff_nat n).2 ht⟩

/-- `A` maps the unstable subspace onto itself: a vector of the unstable subspace has a preimage
in it.

Proof: `w 1`, with the backward orbit `n ↦ w (n + 1)`. -/
theorem exists_mem_unstableSubspace_apply_eq {A : E →L[ℝ] E} {v : E}
    (hv : v ∈ A.unstableSubspace) : ∃ w ∈ A.unstableSubspace, A w = v := by
  obtain ⟨w, h0, hA, ht⟩ := hv
  exact ⟨w 1, mem_unstableSubspace_of_backwardOrbit hA ht 1, by rw [hA 0, h0]⟩

/-- The stable subspace of `e⁻¹` is the unstable subspace of `e`.

Proof: a backward orbit of `e` is unique, `w n = e⁻ⁿ v`, so `v` lies in the unstable subspace of
`e` if and only if `e⁻ⁿ v → 0`. -/
theorem stableSubspace_symm (e : E ≃L[ℝ] E) :
    stableSubspace (e.symm : E →L[ℝ] E) = unstableSubspace (e : E →L[ℝ] E) := by
  ext v
  rw [mem_stableSubspace, mem_unstableSubspace]
  constructor
  · intro hv
    refine ⟨fun n ↦ ((e.symm : E →L[ℝ] E) ^ n) v, by simp, fun n ↦ ?_, hv⟩
    simp [pow_succ']
  · rintro ⟨w, h0, hA, ht⟩
    have hw : ∀ n, w n = ((e.symm : E →L[ℝ] E) ^ n) v := by
      intro n
      induction n with
      | zero => simp [h0]
      | succ n ih => rw [pow_succ', mul_apply_eq_comp, ← ih, ← hA n]; simp
    exact ht.congr hw

/-- The unstable subspace of `e⁻¹` is the stable subspace of `e`. -/
theorem unstableSubspace_symm (e : E ≃L[ℝ] E) :
    unstableSubspace (e.symm : E →L[ℝ] E) = stableSubspace (e : E →L[ℝ] E) := by
  simpa using (stableSubspace_symm e.symm).symm

/-- Applying `Aⁿ` to the `n`-th point of a backward orbit returns its starting point. -/
theorem pow_apply_of_backwardOrbit {A : E →L[ℝ] E} {w : ℕ → E} {v : E}
    (h0 : w 0 = v) (hA : ∀ n, A (w (n + 1)) = w n) (n : ℕ) : (A ^ n) (w n) = v := by
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [pow_succ, mul_apply_eq_comp, hA, ih]

/-- Evaluating a power of a restriction commutes with the inclusion of the invariant subspace. -/
theorem coe_restrict_pow_apply (A : E →L[ℝ] E) {p : Submodule ℝ E} (h : ∀ x ∈ p, A x ∈ p)
    (n : ℕ) (x : p) : (((A.restrict h) ^ n) x : E) = (A ^ n) x := by
  change (↑((↑((A.restrict h) ^ n) : p →ₗ[ℝ] p) x) : E) = (↑(A ^ n) : E →ₗ[ℝ] E) x
  rw [toLinearMap_pow, toLinearMap_restrict, Module.End.pow_restrict, LinearMap.restrict_apply,
    toLinearMap_pow]

end ContinuousLinearMap
