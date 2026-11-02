/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.DivisorSums.DivisorHitFixedPrime
public import LeanPool.NairTenenbaum.NumberFields.IrreducibleRootDensity
public import LeanPool.NairTenenbaum.Results.TheoremTwoStatement

/-! # Divisor hits in the interval prescribed by Theorem 2

This interface uses the original irreducibility and degree hypotheses.
The arithmetic root-density lower bound is proved and gives an unconditional
divisor-hit estimate in the power-shaped interval.
-/

@[expose] public section

namespace NairTenenbaum

open Real Filter Polynomial
open scoped Topology

theorem eventually_power_interval_le_half {β : ℝ} (hβ : β < 1) :
    ∀ᶠ x : ℝ in atTop, x ^ β ≤ x / 2 := by
  have H : Tendsto (fun x : ℝ => x ^ (β - 1)) atTop (𝓝 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (show 0 < 1 - β by linarith)
  filter_upwards [H.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  rw [Real.rpow_sub hxpos, Real.rpow_one] at hx
  have H' := (div_lt_iff₀ hxpos).mp hx
  linarith

theorem exists_theoremTwo_divisorHit_density_bound {Q : ℤ[X]} (hQ : Irreducible Q)
    (hdeg : 0 < Q.natDegree) {k : ℕ} (hk : Q.natDegree < k) {η c : ℝ}
    (hη : Real.log 4 - 1 < η) (hc : 0 < c) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ < x →
      let y : ℝ := x ^ ((Q.natDegree : ℝ) / k)
      4 * c ≤ dyadicRootDensitySum Q y →
        c * y / (Real.log x) ^ η ≤ polynomialDivisorHitCount Q x y := by
  have hirr := (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    (hQ.isPrimitive hdeg.ne')).mp hQ
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hdeg.trans hk
  have hβ : 0 < (Q.natDegree : ℝ) / k := div_pos (by exact_mod_cast hdeg) hkpos
  have hβ₁ : (Q.natDegree : ℝ) / k < 1 := (div_lt_one hkpos).mpr (by exact_mod_cast hk)
  obtain ⟨x₁, hx₁, H₁⟩ := exists_polynomialDivisorHitCount_density_bound_unrestricted hirr hβ hη hc
  obtain ⟨x₂, H₂⟩ := eventually_atTop.mp (eventually_power_interval_le_half hβ₁)
  refine ⟨max x₁ x₂, hx₁.trans_le (le_max_left _ _), fun x hx => ?_⟩
  exact H₁ x _ ((le_max_left _ _).trans_lt hx) le_rfl (H₂ x ((le_max_right _ _).trans hx.le))

theorem exists_theoremTwo_divisorHit_bound {Q : ℤ[X]} (hQ : Irreducible Q)
    (hdeg : 0 < Q.natDegree) {k : ℕ} (hk : Q.natDegree < k) {η : ℝ}
    (hη : Real.log 4 - 1 < η) :
    ∃ c x₀ : ℝ, 0 < c ∧ 1 < x₀ ∧ ∀ x : ℝ, x₀ < x →
      let y : ℝ := x ^ ((Q.natDegree : ℝ) / k)
      c * y / (Real.log x) ^ η ≤ polynomialDivisorHitCount Q x y := by
  obtain ⟨d, hd, hroot⟩ := exists_irreducible_dyadicRootDensity_lower_bound hQ hdeg
  have hc : 0 < d / 4 := by positivity
  obtain ⟨x₁, hx₁, HH⟩ := exists_theoremTwo_divisorHit_density_bound hQ hdeg hk hη hc
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hdeg.trans hk
  have hβ : 0 < (Q.natDegree : ℝ) / k := div_pos (by exact_mod_cast hdeg) hkpos
  obtain ⟨x₂, HX⟩ := eventually_atTop.mp ((tendsto_rpow_atTop hβ).eventually hroot)
  refine ⟨d / 4, max x₁ x₂, hc, hx₁.trans_le (le_max_left _ _), fun x hx => ?_⟩
  apply HH x ((le_max_left _ _).trans_lt hx)
  simpa only [mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0)] using
    HX x ((le_max_right _ _).trans hx.le)

end NairTenenbaum
