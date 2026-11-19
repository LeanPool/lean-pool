/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import LeanPool.StableManifold.Defs
public import LeanPool.StableManifold.Linear.Spectral

/-!
# Stable and unstable subspaces of a linear map

For a continuous linear map `A` of a real normed space:

* `ContinuousLinearMap.stableSubspace A`: the vectors `v` with `Aⁿ v → 0`;
* `ContinuousLinearMap.unstableSubspace A`: the vectors having a backward orbit tending to `0`
  (`w 0 = v`, `A (w (n + 1)) = w n`, `w n → 0`);
* `ContinuousLinearMap.IsHyperbolic A` (finite dimension): no complex eigenvalue of `A` has
  modulus `1`.

The three are defined in `StableManifold.Defs`, with the other definitions in the statement of the
stable manifold theorem.

Both subspaces are `A`-invariant, and `A` maps the unstable subspace onto itself
(`map_mem_stableSubspace`, `map_mem_unstableSubspace`, `exists_mem_unstableSubspace_apply_eq`).
For a continuous linear equivalence `e`, the stable subspace of `e⁻¹` is the unstable subspace of
`e` and conversely (`stableSubspace_symm`, `unstableSubspace_symm`). In finite dimension the two
subspaces are always disjoint (`disjoint_stableSubspace_unstableSubspace`, no hyperbolicity
needed), so `A` is injective on the unstable subspace (`injOn_unstableSubspace`). That they span
the space when `A` is hyperbolic is `ContinuousLinearMap.isCompl_stableSubspace_unstableSubspace`
(`StableManifold.Linear.Splitting`).

## Proofs

* Invariance: `Aⁿ (A v) = Aⁿ⁺¹ v → 0` (`pow_succ`, `tendsto_add_atTop_iff_nat`); for the
  unstable subspace, the backward orbit of `A v` is `0 ↦ A v`, `n + 1 ↦ w n`, and the backward
  orbit of `w 1` (a preimage of `v`) is `n ↦ w (n + 1)`.
* `stableSubspace_symm`, `unstableSubspace_symm`: a backward orbit of `e` is unique,
  `w n = (e.symm ^ n) v` (induction, `pow_succ'`); conversely `n ↦ (e.symm ^ n) v` is a backward
  orbit. Symmetrically, a backward orbit of `e.symm` is the forward orbit of `e`.
* `disjoint_stableSubspace_unstableSubspace`: the restriction `T` of `A` to `Eₛ`
  (`ContinuousLinearMap.restrict`, by invariance) has `Tⁿ x → 0` for every `x`, so
  `‖Tⁿ‖ ≤ C rⁿ ≤ C` (`exists_norm_pow_le_mul_pow_of_tendsto`, finite dimension). If
  `v ∈ Eₛ ⊓ Eᵤ` with backward orbit `w`, then `Aⁿ (w n) = v`, so `Aᵐ (w n) = Aᵐ⁻ⁿ v → 0` and
  `w n ∈ Eₛ`; hence `‖v‖ = ‖Tⁿ (w n)‖ ≤ C ‖w n‖ → 0`, and `v = 0`.
* `injOn_unstableSubspace`: if `v, v' ∈ Eᵤ` and `A v = A v'`, then `v - v' ∈ Eᵤ` and
  `Aⁿ⁺¹ (v - v') = 0`, so `v - v' ∈ Eₛ ⊓ Eᵤ = 0`.
-/

@[expose] public section

open Filter Topology

namespace ContinuousLinearMap

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

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

/-- `A` maps the unstable subspace onto itself: a vector of the unstable subspace has a preimage
in it.

Proof: `w 1`, with the backward orbit `n ↦ w (n + 1)`. -/
theorem exists_mem_unstableSubspace_apply_eq {A : E →L[ℝ] E} {v : E}
    (hv : v ∈ A.unstableSubspace) : ∃ w ∈ A.unstableSubspace, A w = v := by
  obtain ⟨w, h0, hA, ht⟩ := hv
  exact ⟨w 1, ⟨fun n ↦ w (n + 1), rfl, fun n ↦ hA (n + 1), (tendsto_add_atTop_iff_nat 1).2 ht⟩,
    by rw [hA 0, h0]⟩

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

end General

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- In finite dimension the stable and unstable subspaces are **disjoint**, for every `A`.

Proof: the powers of the restriction `T` of `A` to `Eₛ` are bounded, `‖Tⁿ‖ ≤ C`
(`exists_norm_pow_le_mul_pow_of_tendsto`). A backward orbit `w` of `v ∈ Eₛ ⊓ Eᵤ` lies in `Eₛ`
and `Aⁿ (w n) = v`, so `‖v‖ ≤ C ‖w n‖ → 0`. -/
theorem disjoint_stableSubspace_unstableSubspace (A : E →L[ℝ] E) :
    Disjoint A.stableSubspace A.unstableSubspace := by
  rw [Submodule.disjoint_def]
  intro v hs hu
  -- the restriction `T` of `A` to the stable subspace has bounded powers
  let T : A.stableSubspace →L[ℝ] A.stableSubspace :=
    A.restrict fun _ hx ↦ map_mem_stableSubspace hx
  have hTn (n : ℕ) (x : A.stableSubspace) : ((T ^ n) x : E) = (A ^ n) x :=
    A.coe_restrict_pow_apply (fun _ hx ↦ map_mem_stableSubspace hx) n x
  obtain ⟨C, r, hC1, hr0, hr1, hC⟩ := T.exists_norm_pow_le_mul_pow_of_tendsto fun x ↦ by
    rw [tendsto_subtype_rng]
    simp only [hTn, Submodule.coe_zero]
    exact x.2
  -- the backward orbit `w` of `v` lies in the stable subspace, and `Aⁿ (w n) = v`
  obtain ⟨w, h0, hA, ht⟩ := hu
  have hwA := pow_apply_of_backwardOrbit h0 hA
  have hws : ∀ n, w n ∈ A.stableSubspace := by
    intro n
    rw [mem_stableSubspace, ← tendsto_add_atTop_iff_nat n]
    refine hs.congr fun m ↦ ?_
    rw [pow_add, mul_apply_eq_comp, hwA]
  -- so `‖v‖ ≤ C ‖w n‖ → 0`
  have hle : ∀ n, ‖v‖ ≤ C * ‖w n‖ := by
    intro n
    have hrn : r ^ n ≤ 1 := pow_le_one₀ hr0.le hr1.le
    calc ‖v‖ = ‖(T ^ n) ⟨w n, hws n⟩‖ := by rw [← Submodule.norm_coe, hTn, hwA]
      _ ≤ ‖T ^ n‖ * ‖w n‖ := (T ^ n).le_opNorm _
      _ ≤ C * ‖w n‖ := by
        gcongr
        exact (hC n).trans (mul_le_of_le_one_right (by linarith) hrn)
  have := ge_of_tendsto' (ht.norm.const_mul C) hle
  simpa using this

/-- `A` is injective on its unstable subspace.

Proof: if `A v = A v'` then `v - v' ∈ Eᵤ` and `Aⁿ (v - v') = 0` for `n ≥ 1`, so
`v - v' ∈ Eₛ ⊓ Eᵤ = 0` (`disjoint_stableSubspace_unstableSubspace`). -/
theorem injOn_unstableSubspace (A : E →L[ℝ] E) :
    Set.InjOn A (A.unstableSubspace : Set E) := by
  intro v hv v' hv' h
  have hs : v - v' ∈ A.stableSubspace := by
    rw [mem_stableSubspace, ← tendsto_add_atTop_iff_nat 1]
    refine tendsto_const_nhds.congr fun n ↦ ?_
    rw [pow_succ, mul_apply_eq_comp, map_sub, h, sub_self, map_zero]
  exact sub_eq_zero.1 (Submodule.disjoint_def.1 (disjoint_stableSubspace_unstableSubspace A) _ hs
    (sub_mem hv hv'))

end FiniteDimensional

end ContinuousLinearMap
