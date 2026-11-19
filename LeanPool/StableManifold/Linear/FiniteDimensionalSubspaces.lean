/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import LeanPool.StableManifold.Linear.PowerDecay
public import LeanPool.StableManifold.Linear.Subspaces

/-! # Disjoint stable and unstable subspaces in finite dimension -/

@[expose] public section

open Filter Topology

namespace ContinuousLinearMap

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- In finite dimension the stable and unstable subspaces are **disjoint**, for every `A`.

Proof: the powers of the restriction of `A` to its stable subspace tend to zero in norm.
A backward orbit `w` of `v` in the intersection stays in the stable subspace and
`Aⁿ (w n) = v`, so `‖v‖ ≤ ‖w n‖` eventually. -/
theorem disjoint_stableSubspace_unstableSubspace (A : E →L[ℝ] E) :
    Disjoint A.stableSubspace A.unstableSubspace := by
  rw [Submodule.disjoint_def]
  intro v hs hu
  -- the restriction `T` of `A` to the stable subspace has bounded powers
  let T : A.stableSubspace →L[ℝ] A.stableSubspace :=
    A.restrict fun _ hx ↦ map_mem_stableSubspace hx
  have hTn (n : ℕ) (x : A.stableSubspace) : ((T ^ n) x : E) = (A ^ n) x :=
    A.coe_restrict_pow_apply (fun _ hx ↦ map_mem_stableSubspace hx) n x
  have hnorm : Tendsto (fun n : ℕ ↦ ‖T ^ n‖) atTop (𝓝 0) :=
    T.tendsto_norm_pow_of_pointwise_tendsto fun x ↦ by
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
  have hle : ∀ᶠ n in atTop, ‖v‖ ≤ ‖w n‖ := by
    filter_upwards [hnorm.eventually (gt_mem_nhds zero_lt_one)] with n hn
    calc ‖v‖ = ‖(T ^ n) ⟨w n, hws n⟩‖ := by rw [← Submodule.norm_coe, hTn, hwA]
      _ ≤ ‖T ^ n‖ * ‖w n‖ := (T ^ n).le_opNorm _
      _ ≤ ‖w n‖ := mul_le_of_le_one_left (norm_nonneg _) hn.le
  simpa using ge_of_tendsto ht.norm hle

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
