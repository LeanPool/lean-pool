/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.IdealRootEulerBound
public import LeanPool.NairTenenbaum.NumberFields.MinpolyEulerProduct

/-! # A sharp lower bound for the prime-root Dirichlet series -/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial NumberField

variable {K : Type*} [Field K] [NumberField K]

theorem summable_monic_rootPrimePower {Q : ℤ[X]} (hQ : Q.Monic) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => (rootCount Q p.1 : ℝ) * (p.1 : ℝ) ^ (-σ)) := by
  have H := ((Real.summable_nat_rpow.mpr (by
    linarith : -σ < -1)).subtype Nat.Prime).mul_left (Q.natDegree : ℝ)
  apply Summable.of_nonneg_of_le (fun p => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg
      (Nat.cast_nonneg _) _)) _ H
  intro p
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast rootCount_le_degree_of_monic hQ p.2)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem exists_minpoly_rootPrimePowerSum_lower_bound (θ : 𝓞 K)
    (hD : RingOfIntegers.exponent θ ≠ 0) :
    ∃ C b : ℝ, 1 < b ∧ ∀ σ : ℝ, 1 < σ → σ < b →
      -Real.log (σ - 1) - C ≤ rootPrimePowerSum (minpoly ℤ θ) σ := by
  obtain ⟨c, b, hc, hb, H⟩ := exists_idealNormDirichlet_pole_lower_bound K
  refine ⟨idealRootEulerError θ - Real.log c, b, hb, fun σ hσ hσb => ?_⟩
  have hδ : 0 < σ - 1 := by linarith
  have HE := idealNormDirichlet_le_root_exp θ hD hσ
    (summable_monic_rootPrimePower (minpoly.monic θ.isIntegral) hσ)
  have HL := Real.log_le_log (div_pos hc hδ) ((H σ hσ hσb).trans HE)
  rw [Real.log_div hc.ne' hδ.ne', Real.log_exp] at HL
  linarith

end NairTenenbaum
