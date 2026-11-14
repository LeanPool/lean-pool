/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.PrimeRootReciprocalLowerBound

/-! # The logarithmic sieve-product bound for irreducible polynomials -/

@[expose] public section

namespace NairTenenbaum

open Finset Real Polynomial

theorem sieveProduct_le_exp_neg_primeRootSum {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q) (x : ℝ) :
    sieveProduct Q x ≤ Real.exp (-primeRootReciprocalSum Q x) := by
  unfold sieveProduct primeRootReciprocalSum
  rw [← sum_neg_distrib, Real.exp_sum]
  apply prod_le_prod₀
  · intro p hp
    have hp' := (mem_filter.mp hp).2
    apply sub_nonneg.mpr
    exact (div_le_one (by
      exact_mod_cast hp'.pos : (0 : ℝ) < p)).mpr (by exact_mod_cast (hQ p hp').le)
  · intro p _
    simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-((rootCount Q p : ℝ) / p))

theorem exists_irreducible_sieveProduct_log_bound {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) :
    ∃ x₀ C : ℝ, 1 < x₀ ∧ 0 < C ∧ ∀ x : ℝ, x₀ < x →
      sieveProduct Q x ≤ C / Real.log x := by
  obtain ⟨C, x₀, hx₀, H⟩ := exists_primeRootReciprocalSum_lower_bound hQ hirr
  refine ⟨x₀, Real.exp C, hx₀, Real.exp_pos C, fun x hx => ?_⟩
  have hl : 0 < Real.log x := Real.log_pos (hx₀.trans hx)
  calc
    _ ≤ Real.exp (-primeRootReciprocalSum Q x) := sieveProduct_le_exp_neg_primeRootSum hQ x
    _ ≤ Real.exp (C - Real.log (Real.log x)) := Real.exp_le_exp.mpr (by linarith [H x hx])
    _ = _ := by rw [Real.exp_sub, Real.exp_log hl]

end NairTenenbaum
