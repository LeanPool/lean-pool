/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.ContractionState

/-!
# Extending a unit-vector occupation bound by scaling

A unit-vector Pauli bound extends to every one-particle vector, including zero. This is a
conditional scaling helper, not the unconditional Pauli occupation result.
-/

public section

open MeasureTheory

namespace LiebThirring

/-- A unit-vector Pauli bound extends to every one-particle vector, including
zero. This is a conditional scaling helper, not the unconditional Pauli occupation result. -/
theorem oneParticleContraction_pauli_of_unit_bound {N q : ℕ} (i : Fin N)
    (ψ : State N q)
    (hunit : ∀ g : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position),
      ‖g‖ = 1 → (N : ℝ) * ‖oneParticleContraction i g ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) :
    (N : ℝ) * ‖oneParticleContraction i f ψ‖ ^ 2 ≤ ‖f‖ ^ 2 * ‖ψ‖ ^ 2 := by
  by_cases hf : f = 0
  · subst f
    rw [oneParticleContraction_zero, norm_zero]
    simp
  have hn : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hf
  let g := ((‖f‖⁻¹ : ℝ) : ℂ) • f
  have hg : ‖g‖ = 1 := by
    dsimp only [g]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg f)), inv_mul_cancel₀ hn]
  have hfg : ((‖f‖ : ℝ) : ℂ) • g = f := by
    dsimp only [g]
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn, Complex.ofReal_one, one_smul]
  have hnorm : ‖oneParticleContraction i f ψ‖ =
      ‖f‖ * ‖oneParticleContraction i g ψ‖ := by
    conv_lhs => rw [← hfg, oneParticleContraction_smul]
    rw [smul_apply, norm_smul, norm_star, Complex.norm_real,
      Real.norm_eq_abs, abs_norm]
  have h := mul_le_mul_of_nonneg_left (hunit g hg) (sq_nonneg ‖f‖)
  rw [hnorm, mul_pow]
  calc
    _ = ‖f‖ ^ 2 * ((N : ℝ) * ‖oneParticleContraction i g ψ‖ ^ 2) := by ring
    _ ≤ _ := h

end LiebThirring

end
