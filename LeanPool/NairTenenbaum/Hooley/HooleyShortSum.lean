/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.DivisorBounds
public import LeanPool.NairTenenbaum.Results.FamilyTheorems

/-! # Hooley moments reduced to their root-weighted means

This is the proved short-sum input to Corollary 4. The long weighted Hooley
mean estimate and the sharper polynomial Euler-product estimate used there
are separate analytic steps, not hypotheses hidden in the arithmetic class.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

theorem extend_hooley_rpow {t : ℝ} (ht : 0 < t) (n : ℕ) :
    extendArithmeticMap (fun v => hooleyMap v ^ t) (fun _ => n) =
      (hooleyDelta n : ℝ) ^ t := by
  by_cases hn : n = 0
  · simp [hn, extendArithmeticMap, hooleyDelta_zero, Real.zero_rpow ht.ne']
  · simp [extendArithmeticMap, Nat.pos_of_ne_zero hn, hooleyMap]

/-- The short sum of Hooley's divisor function evaluated on polynomial values. -/
noncomputable def hooleyPolynomialSum (Q : ℤ[X]) (t x y : ℝ) : ℝ :=
  ∑ n ∈ shortInterval x y, (hooleyDelta (Q.eval (n : ℤ)).natAbs : ℝ) ^ t

/-- The root-weighted sum of Hooley's divisor function. -/
noncomputable def hooleyRootSum (Q : ℤ[X]) (t x : ℝ) : ℝ :=
  ∑ n ∈ positiveUpTo x, (hooleyDelta n : ℝ) ^ t * ((rootCount Q n : ℝ) / (n : ℝ))

/-- The Hooley specialization of the proved main theorem, for every positive
interval exponent and moment order. No irreducibility is needed for this
root-weighted form. The constants may depend on the fixed polynomial. -/
theorem exists_hooleyPolynomialSum_root_bound (Q : ℤ[X])
    (hQ : NoFixedPrimeDivisor Q) (hdeg : 0 < Q.natDegree)
    {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    ∃ x₀ C : ℝ, 0 < x₀ ∧ 0 < C ∧ ∀ x y : ℝ,
      x₀ < x → x ^ α ≤ y → y ≤ x →
      hooleyPolynomialSum Q t x y ≤
        C * (y * sieveProduct Q x * hooleyRootSum Q t x) := by
  let g := Q.natDegree
  have hg : (0 : ℝ) < g := by exact_mod_cast hdeg
  let ε : ℝ := min α 1 / (16 * (g : ℝ) ^ 2)
  have hε : 0 < ε := div_pos (lt_min hα zero_lt_one) (by positivity)
  have hεsmall : ε < 1 / (8 * (g : ℝ) ^ 2) := by
    dsimp [ε]
    apply (div_lt_iff₀ (by positivity)).mpr
    have Heq : 1 / (8 * (g : ℝ) ^ 2) * (16 * (g : ℝ) ^ 2) = 2 := by
      field_simp
      ring
    rw [Heq]
    exact (min_le_right _ _).trans_lt (by norm_num)
  have hεα : 4 * (g : ℝ) ^ 2 * ε ≤ α := by
    have Heq : 4 * (g : ℝ) ^ 2 * ε = min α 1 / 4 := by
      dsimp [ε]
      field_simp
      ring
    rw [Heq]
    linarith [min_le_left α 1]
  obtain ⟨B, hB, hF⟩ := hooley_rpow_admissible (div_pos hε (by norm_num : (0 : ℝ) < 3)) ht
  obtain ⟨c, hc, C, hC, H⟩ := corollaryThree_for_families (k := 1) (g := g)
    (by norm_num) hdeg (Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) ht.le)
    hB hε hεsmall (δ := 1) zero_lt_one le_rfl
  let family : Fin 1 → ℤ[X] := fun _ => Q
  have hfamily : NoFixedPrimeDivisor (∏ j, family j) := by simpa [family] using hQ
  refine ⟨max 2 (c * (polynomialHeight Q : ℝ)), C (familyBadDiscriminant family hfamily),
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), hC _, ?_⟩
  intro x y hx hy hyx
  have hx₁ : 1 ≤ x := by have := (le_max_left _ _).trans_lt hx; linarith
  have hheight : c * (polynomialHeight (∏ j, family j) : ℝ) ^ (1 : ℝ) < x := by
    simpa [family] using (le_max_right _ _).trans_lt hx
  have Hbound := H family hfamily (by simp [family, g])
    (fun i j hij => (hij (Subsingleton.elim _ _)).elim)
    (fun _ => fun v => hooleyMap v ^ t)
    (fun _ => by simpa using hF) x y hheight
    ((Real.rpow_le_rpow_of_exponent_le hx₁ hεα).trans hy) hyx
  simp only [productShortSum, family, Fin.prod_univ_one] at Hbound
  simp_rw [extend_hooley_rpow ht] at Hbound
  simpa only [rootWeightedSum, hooleyMap, hooleyPolynomialSum, hooleyRootSum, family] using Hbound

end NairTenenbaum
