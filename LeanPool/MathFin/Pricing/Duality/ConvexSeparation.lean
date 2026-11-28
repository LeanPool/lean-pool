/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.Duality.ConvexDuality
public import Mathlib.Analysis.RCLike.Lemmas

/-!
# Separating-functional kernel for the finite Fundamental Theorem of Asset Pricing

A finite-dimensional subspace `V ⊆ (ι → ℝ)` disjoint from the standard simplex
admits a strictly-positive dual functional that annihilates it. This is the
geometric heart of the finite-state FTAP: when the attainable-gains subspace of a
market misses the simplex (no arbitrage), the separating hyperplane *is* the
equivalent martingale measure (a strictly-positive pricing functional).

This kernel is **derived** from the cone-separation root
`exists_pos_separating_of_cone_disjoint_simplex` (`MathFin/Pricing/Duality/ConvexDuality.lean`):
a subspace is a two-sided cone, so the root's one-sided `≤ 0` bound plus neg-closure
yields the two-sided `= 0` annihilation. It is the subspace case of the convex-duality
unification.

The underlying separation is the cone root `MathFin.exists_pos_separating_of_cone_disjoint_simplex`
(`Pricing/Duality/ConvexDuality.lean`), specialised to the two-sided subspace case.

## Main results

* `MathFin.exists_pos_dual_of_disjoint_stdSimplex`
* `MathFin.exists_ne_zero_sum_mul_eq_zero` — a proper subspace of `ι → ℝ` is annihilated by a
  nonzero vector (the second FTAP's dual certificate of incompleteness).
* `MathFin.exists_pos_add_mul_pos` — strictly positive weights stay strictly positive after a
  small perturbation in any direction.

## Tags

separating hyperplane, no arbitrage, state prices, equivalent martingale measure, finite-state FTAP,
standard simplex, MSC 90C25, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin


/-- **Separating-dual kernel.** A subspace `V` of the finite-dimensional space
`ι → ℝ` that contains no probability vector (no nonnegative `v` with `∑ i, v i = 1`) admits a
strictly-positive vector `q` whose induced functional annihilates `V`. -/
theorem exists_pos_dual_of_disjoint_stdSimplex
    {ι : Type*} [Fintype ι]
    (V : Submodule ℝ (ι → ℝ)) (hV : ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → ∑ i, v i = 1 → v ∉ V) :
    ∃ q : ι → ℝ, (∀ i, 0 < q i) ∧ ∀ v ∈ V, ∑ i, q i * v i = 0 := by
  -- A subspace is a two-sided cone: apply the cone-separation root to `V`, then
  -- use neg-closure to promote the one-sided `≤ 0` to the two-sided `= 0`.
  obtain ⟨q, hpos, hle⟩ :=
    exists_pos_separating_of_cone_disjoint_simplex (V : Set (ι → ℝ)) V.convex
      V.isClosed_of_finiteDimensional (fun x hx c _ ↦ V.smul_mem c hx)
      hV
  refine ⟨q, hpos, fun v hv ↦ le_antisymm (hle v hv) ?_⟩
  have hneg := hle (-v) (V.neg_mem hv)
  simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib] at hneg
  linarith

/-- A proper subspace of `ι → ℝ` over a finite `ι` is annihilated, under the pairing
`∑ g i * η i`, by a nonzero `η`. -/
theorem exists_ne_zero_sum_mul_eq_zero {ι : Type*} [Fintype ι] {W : Submodule ℝ (ι → ℝ)}
    (hW : W < ⊤) : ∃ η : ι → ℝ, η ≠ 0 ∧ ∀ g ∈ W, ∑ i, g i * η i = 0 := by
  classical
  obtain ⟨ℓ, hℓ0, hℓ⟩ := W.exists_le_ker_of_lt_top hW
  let η : ι → ℝ := fun i ↦ ℓ fun j ↦ if i = j then 1 else 0
  have hℓη (g : ι → ℝ) : ℓ g = ∑ i, g i * η i := by
    rw [LinearMap.pi_apply_eq_sum_univ ℓ g]
    simp [η]
  exact ⟨η, fun h ↦ hℓ0 (LinearMap.ext fun g ↦ by simp [hℓη, h]),
    fun g hg ↦ (hℓη g).symm.trans (LinearMap.mem_ker.1 (hℓ hg))⟩

/-- Positive weights stay positive under a small perturbation in any direction. -/
theorem exists_pos_add_mul_pos {ι : Type*} [Finite ι] {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    (η : ι → ℝ) : ∃ ε > 0, ∀ i, 0 < p i + ε * η i := by
  have h : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i, 0 < p i + ε * η i :=
    eventually_nhdsWithin_of_eventually_nhds <| Filter.eventually_all.2 fun i ↦ by
      have : Filter.Tendsto (fun ε : ℝ ↦ p i + ε * η i) (nhds 0) (nhds (p i)) := by
        simpa using ((continuous_id.mul_const (η i)).const_add (p i)).tendsto 0
      exact this.eventually_const_lt (hp i)
  exact (h.and self_mem_nhdsWithin).exists.imp fun _ h ↦ ⟨h.2, h.1⟩

end MathFin
