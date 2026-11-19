/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # Geometric decay of powers of a continuous linear map -/

@[expose] public section

open Filter Topology

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If the norms of the powers tend to zero, some positive power has norm less than one. -/
theorem exists_norm_pow_lt_one_of_norm_tendsto (A : E →L[ℝ] E)
    (h : Tendsto (fun n : ℕ ↦ ‖A ^ n‖) atTop (𝓝 0)) : ∃ N : ℕ, 0 < N ∧ ‖A ^ N‖ < 1 := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h.eventually (gt_mem_nhds (a := (1 : ℝ)) (by simp)))
  exact ⟨N + 1, N.succ_pos, hN (N + 1) (Nat.le_succ _)⟩

variable [FiniteDimensional ℝ E]

/-- In finite dimension, if every orbit `Aⁿ v` tends to `0`, then the powers tend to zero in norm.

Proof: with a basis `b`, `Module.Basis.exists_opNorm_le` gives `‖Aⁿ‖ ≤ K ∑ᵢ ‖Aⁿ (b i)‖ → 0`. -/
theorem tendsto_norm_pow_of_pointwise_tendsto (A : E →L[ℝ] E)
    (hA : ∀ v, Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ ‖A ^ n‖) atTop (𝓝 0) := by
  let b := Module.finBasis ℝ E
  obtain ⟨C, -, hC⟩ := b.exists_opNorm_le (F := E)
  -- `‖Aⁿ‖ ≤ C ∑ᵢ ‖Aⁿ (b i)‖ → 0`
  have hs : Tendsto (fun n : ℕ ↦ ∑ i, ‖(A ^ n) (b i)‖) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ fun i _ ↦ (hA (b i)).norm
  refine squeeze_zero (fun n ↦ norm_nonneg _)
    (fun n ↦ hC (Finset.sum_nonneg fun i _ ↦ norm_nonneg _) fun i ↦
      Finset.single_le_sum (f := fun i ↦ ‖(A ^ n) (b i)‖) (fun i _ ↦ norm_nonneg _)
        (Finset.mem_univ i)) ?_
  simpa using hs.const_mul C

/-- Pointwise decay in finite dimension gives a positive power of norm less than one. -/
theorem exists_norm_pow_lt_one_of_tendsto (A : E →L[ℝ] E)
    (hA : ∀ v, Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 0)) :
    ∃ N : ℕ, 0 < N ∧ ‖A ^ N‖ < 1 :=
  A.exists_norm_pow_lt_one_of_norm_tendsto (A.tendsto_norm_pow_of_pointwise_tendsto hA)

omit [FiniteDimensional ℝ E] in
/-- **Geometric decay** from one contracting power: if `‖A ^ N‖ < 1` with `N ≥ 1`, then
`‖Aⁿ‖ ≤ C rⁿ` for all `n`, with `1 ≤ C` and `0 < r < 1`.

Proof: with `ρ = max (1/2) ‖A ^ N‖` and `r = ρ ^ (1 / N)`, write `n = N q + j`, `j < N`; then
`‖Aⁿ‖ ≤ ρ ^ q K ≤ (K / ρ) rⁿ`, where `K` bounds `‖A ^ j‖` for `j < N`. -/
theorem exists_norm_pow_le_mul_pow (A : E →L[ℝ] E) {N : ℕ} (hN : 0 < N) (hA : ‖A ^ N‖ < 1) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ r < 1 ∧ ∀ n : ℕ, ‖A ^ n‖ ≤ C * r ^ n := by
  set ρ := max (1 / 2) ‖A ^ N‖
  have hρ0 : 0 < ρ := lt_max_of_lt_left (by norm_num)
  have hρ1 : ρ < 1 := max_lt (by norm_num) hA
  set K := 1 + ∑ j ∈ Finset.range N, ‖A ^ j‖
  have hK1 : 1 ≤ K := le_add_of_nonneg_right (Finset.sum_nonneg fun j _ ↦ norm_nonneg _)
  have hKj : ∀ j < N, ‖A ^ j‖ ≤ K := fun j hj ↦
    (Finset.single_le_sum (f := fun j ↦ ‖A ^ j‖) (fun j _ ↦ norm_nonneg _)
      (Finset.mem_range.2 hj)).trans (le_add_of_nonneg_left zero_le_one)
  set r := ρ ^ (1 / (N : ℝ))
  have hr0 : 0 < r := Real.rpow_pos_of_pos hρ0 _
  have hr1 : r < 1 := Real.rpow_lt_one hρ0.le hρ1 (by positivity)
  have hrN : r ^ N = ρ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0.le, one_div_mul_cancel (by positivity),
      Real.rpow_one]
  -- along the multiples of `N`
  have hq : ∀ q j : ℕ, ‖A ^ (N * q + j)‖ ≤ ρ ^ q * ‖A ^ j‖ := by
    intro q j
    induction q with
    | zero => simp
    | succ q ih =>
      calc ‖A ^ (N * (q + 1) + j)‖ = ‖A ^ N * A ^ (N * q + j)‖ := by
            rw [← pow_add]; congr 2; ring
        _ ≤ ‖A ^ N‖ * ‖A ^ (N * q + j)‖ := norm_mul_le _ _
        _ ≤ ρ * (ρ ^ q * ‖A ^ j‖) := by gcongr; exact le_max_right _ _
        _ = ρ ^ (q + 1) * ‖A ^ j‖ := by ring
  refine ⟨K / ρ, r, (one_le_div hρ0).2 (by linarith), hr0, hr1, fun n ↦ ?_⟩
  obtain ⟨q, j, hj, rfl⟩ : ∃ q j, j < N ∧ n = N * q + j :=
    ⟨n / N, n % N, Nat.mod_lt _ hN, (Nat.div_add_mod n N).symm⟩
  calc ‖A ^ (N * q + j)‖ ≤ ρ ^ q * K := (hq q j).trans (by gcongr; exact hKj j hj)
    _ = K / ρ * (ρ ^ q * r ^ N) := by rw [hrN]; field_simp
    _ ≤ K / ρ * (ρ ^ q * r ^ j) := by
      have := pow_le_pow_of_le_one hr0.le hr1.le hj.le
      gcongr
    _ = K / ρ * r ^ (N * q + j) := by rw [pow_add, pow_mul, hrN]

/-- In finite dimension, if every orbit `Aⁿ v` tends to `0`, then `‖Aⁿ‖ ≤ C rⁿ` for all `n`, with
`1 ≤ C` and `0 < r < 1`.

Proof: `exists_norm_pow_lt_one_of_tendsto` and `exists_norm_pow_le_mul_pow`. -/
theorem exists_norm_pow_le_mul_pow_of_tendsto (A : E →L[ℝ] E)
    (hA : ∀ v, Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 0)) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ r < 1 ∧ ∀ n : ℕ, ‖A ^ n‖ ≤ C * r ^ n :=
  let ⟨_, hN, hAN⟩ := A.exists_norm_pow_lt_one_of_tendsto hA
  A.exists_norm_pow_le_mul_pow hN hAN

end ContinuousLinearMap
