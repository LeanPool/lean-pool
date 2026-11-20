/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.ChebyshevWeights
public import Mathlib.LinearAlgebra.Lagrange

/-! # Normalized interpolation weights on arbitrary distinct nodes -/

@[expose] public section

namespace NoncommutativeAMGM
open Polynomial
open scoped BigOperators

/-- The normalized nodal-product weights from equation (21). -/
noncomputable def interpolationWeight (m : ℕ) (t : ℕ → ℝ) (j : ℕ) : ℝ :=
  ((2 : ℝ) ^ (m - 1))⁻¹ /
    (∏ l ∈ (Finset.range (m + 1)).erase j, (t j - t l))

/-- The weights on any distinct nodes extract the normalized top coefficient. -/
theorem interpolationWeight_extracts {m : ℕ} (t : ℕ → ℝ)
    (ht : Set.InjOn t (Finset.range (m + 1))) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ m) :
    (∑ j ∈ Finset.range (m + 1), interpolationWeight m t j * p.eval (t j)) =
      p.coeff m / (2 : ℝ) ^ (m - 1) := by
  have hdeg : p.degree < ((Finset.range (m + 1)).card : ℕ) := by
    rw [Finset.card_range]
    have hnat : p.natDegree < m + 1 := by omega
    exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hnat)
  have he := Lagrange.coeff_eq_sum ht hdeg
  simp only [Finset.card_range, Nat.add_sub_cancel] at he
  calc
    _ = ((2 : ℝ) ^ (m - 1))⁻¹ *
        ∑ j ∈ Finset.range (m + 1), p.eval (t j) /
          (∏ l ∈ (Finset.range (m + 1)).erase j, (t j - t l)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [interpolationWeight]
      ring
    _ = _ := by rw [← he]; ring

/-- At the ideal cosine nodes the general product rule is the explicit Chebyshev rule. -/
theorem interpolationWeight_chebyshev {m j : ℕ} (hm : 0 < m) (hj : j ≤ m) :
    interpolationWeight m (chebyshevNode m) j = chebyshevWeight m j := by
  exact (chebyshevWeight_eq_product hm hj).symm

/-- Exact perturbation formula before taking any absolute values or estimates. -/
theorem interpolationWeight_perturbation {m j : ℕ} (t c : ℕ → ℝ)
    (hc : ∀ l ∈ (Finset.range (m + 1)).erase j, c j - c l ≠ 0) :
    interpolationWeight m t j = interpolationWeight m c j *
      (∏ l ∈ (Finset.range (m + 1)).erase j, (t j - t l) / (c j - c l))⁻¹ := by
  classical
  have hprod : (∏ l ∈ (Finset.range (m + 1)).erase j, (c j - c l)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hc
  rw [Finset.prod_div_distrib]
  dsimp [interpolationWeight]
  field_simp

/-- Applying the rule to `Tₘ` gives the exact moment used in the total-variation estimate. -/
theorem interpolationWeight_chebyshev_moment {m : ℕ} (t : ℕ → ℝ)
    (ht : Set.InjOn t (Finset.range (m + 1))) :
    (∑ j ∈ Finset.range (m + 1), interpolationWeight m t j *
      (Chebyshev.T ℝ (m : ℤ)).eval (t j)) = 1 := by
  have hdeg : (Chebyshev.T ℝ (m : ℤ)).natDegree = m := by simp [Chebyshev.natDegree_T]
  have hc : (Chebyshev.T ℝ (m : ℤ)).coeff m = (2 : ℝ) ^ (m - 1) := by
    have h := coeff_natDegree (p := Chebyshev.T ℝ (m : ℤ))
    simpa only [hdeg, Chebyshev.leadingCoeff_T, Int.natAbs_natCast] using h
  rw [interpolationWeight_extracts t ht _ hdeg.le, hc,
    div_self (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))]

end NoncommutativeAMGM
