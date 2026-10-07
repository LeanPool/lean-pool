/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLocalExistence

/-!
# Time scale for the local regularized mild solution

These constants are the lifespan parameters in `lem:reg-local-mild`.
-/

public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CKN.Leray

/-- The profile's real `L²` norm, expressed through its `Lᵖ` seminorm. -/
@[expose]
def regularizedMildProfileL2Norm (ρ : RegMollifierProfile) : ℝ :=
  ENNReal.toReal (eLpNorm ρ.rho (2 : ℝ≥0∞) volume)

/-- The Abel-kernel constant for the regularized mild contraction. -/
@[expose]
def regularizedMildAeps (ρ : RegMollifierProfile) (ε : ℝ) : ℝ :=
  regularizedMildProfileL2Norm ρ * ε ^ (-(3 / 2 : ℝ)) /
    Real.sqrt (2 * Real.exp 1)

/-- The lifespan in `lem:reg-local-mild`. -/
@[expose]
def regularizedMildLocalLifespan (ρ : RegMollifierProfile) (ε : ℝ)
    (b : RealVectorL2) : ℝ :=
  (16 * regularizedMildAeps ρ ε * (1 + ‖b‖))⁻¹ ^ 2

private theorem regularizedMildProfile_memLp (ρ : RegMollifierProfile) :
    MemLp ρ.rho (2 : ℝ≥0∞) volume :=
  ρ.smooth.continuous.memLp_of_hasCompactSupport ρ.compact

/-- The parameter in the quadratic tensor bounds is the profile norm times
the spatial scale factor. -/
theorem regularizedMildMollifierConstant_eq_profile (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) :
    regularizedMildMollifierConstant ρ ε =
      regularizedMildProfileL2Norm ρ * ε ^ (-(3 / 2 : ℝ)) := by
  have hρ := regularizedMildProfile_memLp ρ
  simp [regularizedMildMollifierConstant, regularizedMildProfileL2Norm,
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (le_of_lt (Real.rpow_pos_of_pos hε _)), mul_comm]

private theorem regularizedMildProfileL2Norm_pos (ρ : RegMollifierProfile) :
    0 < regularizedMildProfileL2Norm ρ := by
  have hρ := regularizedMildProfile_memLp ρ
  have hρfinite : eLpNorm ρ.rho 2 volume ≠ ∞ := hρ.eLpNorm_ne_top
  have hρnonzero : eLpNorm ρ.rho 2 volume ≠ 0 := by
    intro hzero
    have hzeroAE : ρ.rho =ᵐ[volume] 0 :=
      (eLpNorm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).1 hzero
    have hone : (1 : ℝ) = 0 := by
      rw [← ρ.integral_eq_one, integral_congr_ae hzeroAE]
      simp
    exact one_ne_zero hone
  exact ENNReal.toReal_pos hρnonzero hρfinite

/-- The Abel constant and local lifespan are positive for every admissible
profile and positive regularization scale. -/
theorem regularizedMildAeps_pos (ρ : RegMollifierProfile) (ε : ℝ)
    (hε : 0 < ε) : 0 < regularizedMildAeps ρ ε := by
  rw [regularizedMildAeps]
  exact div_pos (mul_pos (regularizedMildProfileL2Norm_pos ρ)
    (Real.rpow_pos_of_pos hε _)) (Real.sqrt_pos.2 (by positivity))

theorem regularizedMildLocalLifespan_pos (ρ : RegMollifierProfile) (ε : ℝ)
    (hε : 0 < ε) (b : RealVectorL2) :
    0 < regularizedMildLocalLifespan ρ ε b := by
  rw [regularizedMildLocalLifespan]
  exact sq_pos_of_pos (inv_pos.mpr (mul_pos (mul_pos
    (by norm_num : (0 : ℝ) < 16) (regularizedMildAeps_pos ρ ε hε))
    (by positivity : (0 : ℝ) < 1 + ‖b‖)))

end CKN.Leray

end
