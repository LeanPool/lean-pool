/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.StaticUnaryUnbiasedFlipMarginals
public import Mathlib.Tactic.FieldSimp

/-!
Uniform one-bit mutation and its exact radius moments.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-- The radius-one static unary-unbiased mutation operator: each singleton
mask receives mass `1/n`, and every other mask receives zero mass. -/
noncomputable def uniformOneBitLaw {n : ℕ} (hn : 0 < n) :
    StaticUnaryUnbiasedMutation n := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  refine
    { weight := fun mask => if mask.card = 1 then (n : ℝ)⁻¹ else 0,
      weight_nonneg := ?_,
      weight_sum := ?_,
      card_invariant := ?_ }
  · intro mask
    split_ifs
    · exact inv_nonneg.mpr (Nat.cast_nonneg n)
    · exact le_refl 0
  · have hmembership (mask : MutationMask n) :
        (mask.card = 1) ↔
          mask ∈ Finset.powersetCard 1 (Finset.univ : Finset (Fin n)) := by
        simp
    have hsum :
        (∑ mask : MutationMask n, if mask.card = 1 then (n : ℝ)⁻¹ else 0) =
          ∑ mask ∈ Finset.powersetCard 1
            (Finset.univ : Finset (Fin n)), (n : ℝ)⁻¹ := by
      simp_rw [hmembership]
      exact Finset.sum_ite_mem_eq
        (Finset.powersetCard 1 (Finset.univ : Finset (Fin n)))
        (fun _mask : MutationMask n => (n : ℝ)⁻¹)
    have hcard :
        (Finset.powersetCard 1 (Finset.univ : Finset (Fin n))).card = n := by
      simp
    calc
      (∑ mask : MutationMask n, if mask.card = 1 then (n : ℝ)⁻¹ else 0) =
          ∑ mask ∈ Finset.powersetCard 1
            (Finset.univ : Finset (Fin n)), (n : ℝ)⁻¹ := hsum
      _ = (n : ℝ) * (n : ℝ)⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
      _ = 1 := by field_simp [hn0]
  · intro mask₁ mask₂ hcard
    simp [hcard]

/-- A uniform one-bit mutation has total singleton probability exactly one. -/
theorem uniformOneBitLaw_oneBitMass {n : ℕ} (hn : 0 < n) :
    (uniformOneBitLaw hn).oneBitMass = 1 := by
  let i : Fin n := ⟨0, hn⟩
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  calc
    (uniformOneBitLaw hn).oneBitMass =
        (n : ℝ) * (uniformOneBitLaw hn).weight ({i} : MutationMask n) :=
      (uniformOneBitLaw hn).oneBitMass_eq_n_mul_singleton i
    _ = (n : ℝ) * (n : ℝ)⁻¹ := by
      simp [uniformOneBitLaw]
    _ = 1 := by field_simp [hn0]

/-- The radius distribution of the uniform one-bit operator is a point mass
at radius one. -/
theorem uniformOneBitLaw_radiusMass {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (uniformOneBitLaw hn).radiusMass k = if k = 1 then 1 else 0 := by
  classical
  by_cases hk : k = 1
  · subst k
    simpa [oneBitMass] using uniformOneBitLaw_oneBitMass hn
  · simp only [ite_eq_right hk]
    unfold radiusMass
    apply Finset.sum_eq_zero
    intro mask hmask
    have hcard : mask.card = k := (Finset.mem_powersetCard.mp hmask).2
    simp [uniformOneBitLaw, hcard, hk]

/-- The exact mean radius of the uniform one-bit law. -/
theorem uniformOneBitLaw_meanRadius {n : ℕ} (hn : 0 < n) :
    (uniformOneBitLaw hn).meanRadius = 1 := by
  unfold meanRadius
  calc
    (∑ k ∈ Finset.range (n + 1), (k : ℝ) * (uniformOneBitLaw hn).radiusMass k) =
        ∑ k ∈ Finset.range (n + 1), if k = 1 then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [uniformOneBitLaw_radiusMass hn]
      split_ifs with h
      · subst k
        norm_num
      · simp
    _ = 1 := by
      have hmem : 1 ∈ Finset.range (n + 1) :=
        Finset.mem_range.mpr (by omega)
      simp [hmem]

/-- The exact second factorial radius moment of a one-bit law is zero. -/
theorem uniformOneBitLaw_secondFactorialRadiusMoment {n : ℕ} (hn : 0 < n) :
    (uniformOneBitLaw hn).secondFactorialRadiusMoment = 0 := by
  unfold secondFactorialRadiusMoment
  apply Finset.sum_eq_zero
  intro k hk
  rw [uniformOneBitLaw_radiusMass hn]
  by_cases h : k = 1
  · subst k
    norm_num
  · simp [h]

end StaticUnaryUnbiasedMutation
end ECRuntime
