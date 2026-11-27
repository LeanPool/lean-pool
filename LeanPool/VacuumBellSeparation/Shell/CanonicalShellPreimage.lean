/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.NormalizedTargetGeometry

/-!
# The literal reference momentum for an imaginary boost

For a negative real shell length rho and sin(theta)>0, the momentum is
(0,B,0), with omega=sqrt(t^2+rho^2)/sin(theta) and B=sqrt(omega^2-t^2).
The real and imaginary boost vectors are computed in the original
spacetime. No positive-mass assumption excludes t=0.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped InnerProductSpace Matrix

/-- Canonical shell energy given by `Real.sqrt (t ^ 2 + ρ ^ 2) / Real.sin θ`. -/
noncomputable def canonicalShellEnergy (t ρ θ : ℝ) : ℝ :=
  Real.sqrt (t ^ 2 + ρ ^ 2) / Real.sin θ

/-- Canonical shell transverse defined as `Real.sqrt (canonicalShellEnergy t ρ θ ^ 2 - t ^ 2)`. -/
noncomputable def canonicalShellTransverse (t ρ θ : ℝ) : ℝ :=
  Real.sqrt (canonicalShellEnergy t ρ θ ^ 2 - t ^ 2)

/-- Canonical shell momentum defined as `WithLp.toLp 2 ![0, canonicalShellTransverse t ρ θ, 0]`. -/
noncomputable def canonicalShellMomentum (t ρ θ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![0, canonicalShellTransverse t ρ θ, 0]

/-- Canonical shell real. -/
noncomputable def canonicalShellReal (t ρ θ : ℝ) : Spacetime :=
  (canonicalShellEnergy t ρ θ * Real.cos θ, canonicalShellMomentum t ρ θ)

/-- Canonical shell imaginary. -/
noncomputable def canonicalShellImaginary (t ρ θ : ℝ) : Spacetime :=
  (0, WithLp.toLp 2 ![canonicalShellEnergy t ρ θ * Real.sin θ, 0, 0])

theorem canonicalShellEnergy_pos {t ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 < Real.sin θ) :
    0 < canonicalShellEnergy t ρ θ :=
  div_pos (Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos (sq_nonneg t) (sq_pos_of_pos hρ))) hθ

theorem canonicalShellEnergy_sq_mul_sin_sq {t ρ θ : ℝ} (hθ : 0 < Real.sin θ) :
    canonicalShellEnergy t ρ θ ^ 2 * Real.sin θ ^ 2 = t ^ 2 + ρ ^ 2 := by
  rw [canonicalShellEnergy, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (ne_of_gt hθ))]
  exact Real.sq_sqrt (add_nonneg (sq_nonneg t) (sq_nonneg ρ))

theorem canonicalShellEnergy_sq_sub_mass_pos {t ρ θ : ℝ}
    (hρ : 0 < ρ) (hθ : 0 < Real.sin θ) :
    0 < canonicalShellEnergy t ρ θ ^ 2 - t ^ 2 := by
  have he := canonicalShellEnergy_sq_mul_sin_sq (t := t) (ρ := ρ) hθ
  have hm := mul_le_of_le_one_right (sq_nonneg (canonicalShellEnergy t ρ θ))
    (Real.sin_sq_le_one θ)
  nlinarith [sq_pos_of_pos hρ]

theorem canonicalShellTransverse_pos {t ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 < Real.sin θ) :
    0 < canonicalShellTransverse t ρ θ :=
  Real.sqrt_pos.2 (canonicalShellEnergy_sq_sub_mass_pos hρ hθ)

theorem canonicalShellTransverse_sq {t ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 < Real.sin θ) :
    canonicalShellTransverse t ρ θ ^ 2 = canonicalShellEnergy t ρ θ ^ 2 - t ^ 2 :=
  Real.sq_sqrt (canonicalShellEnergy_sq_sub_mass_pos hρ hθ).le

theorem canonicalShellMomentum_norm_sq (t ρ θ : ℝ) :
    ‖canonicalShellMomentum t ρ θ‖ ^ 2 = canonicalShellTransverse t ρ θ ^ 2 := by
  simp [canonicalShellMomentum, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

theorem canonicalShellMomentum_dispersion {t ρ θ : ℝ}
    (hρ : 0 < ρ) (hθ : 0 < Real.sin θ) :
    dispersion t (canonicalShellMomentum t ρ θ) = canonicalShellEnergy t ρ θ := by
  rw [dispersion, canonicalShellMomentum_norm_sq, canonicalShellTransverse_sq hρ hθ,
    show t ^ 2 + (canonicalShellEnergy t ρ θ ^ 2 - t ^ 2) =
      canonicalShellEnergy t ρ θ ^ 2 by ring,
    Real.sqrt_sq (canonicalShellEnergy_pos hρ hθ).le]

theorem canonicalShellReal_square {t ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 < Real.sin θ) :
    minkowskiForm (canonicalShellReal t ρ θ) (canonicalShellReal t ρ θ) = -ρ ^ 2 := by
  simp only [minkowskiForm, canonicalShellReal, real_inner_self_eq_norm_sq,
    canonicalShellMomentum_norm_sq, canonicalShellTransverse_sq hρ hθ]
  have he := canonicalShellEnergy_sq_mul_sin_sq (t := t) (ρ := ρ) hθ
  linear_combination
    canonicalShellEnergy t ρ θ ^ 2 * Real.sin_sq_add_cos_sq θ - he

theorem canonicalShellImaginary_square {t ρ θ : ℝ} (hθ : 0 < Real.sin θ) :
    minkowskiForm (canonicalShellImaginary t ρ θ) (canonicalShellImaginary t ρ θ) =
      -(t ^ 2 + ρ ^ 2) := by
  simp [minkowskiForm, canonicalShellImaginary,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
    mul_pow, canonicalShellEnergy_sq_mul_sin_sq hθ]

theorem canonicalShellPair_orthogonal (t ρ θ : ℝ) :
    minkowskiForm (canonicalShellReal t ρ θ) (canonicalShellImaginary t ρ θ) = 0 := by
  simp [minkowskiForm, canonicalShellReal, canonicalShellImaginary, canonicalShellMomentum,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]

theorem canonicalShellReal_negative {t ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 < Real.sin θ) :
    minkowskiForm (canonicalShellReal t ρ θ) (canonicalShellReal t ρ θ) < 0 := by
  rw [canonicalShellReal_square hρ hθ]
  exact neg_neg_of_pos (sq_pos_of_pos hρ)

theorem canonicalShellImaginary_negative {t ρ θ : ℝ}
    (hρ : 0 < ρ) (hθ : 0 < Real.sin θ) :
    minkowskiForm (canonicalShellImaginary t ρ θ) (canonicalShellImaginary t ρ θ) < 0 := by
  rw [canonicalShellImaginary_square hθ]
  exact neg_neg_of_pos (add_pos_of_nonneg_of_pos (sq_nonneg t) (sq_pos_of_pos hρ))

theorem canonicalShellBoost_pair {t ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 < Real.sin θ) :
    complexShellBoost t ((θ : ℂ) * Complex.I) (canonicalShellMomentum t ρ θ) =
      complexSpacetimeOfReal (canonicalShellReal t ρ θ) +
        Complex.I • complexSpacetimeOfReal (canonicalShellImaginary t ρ θ) := by
  rw [complexShellBoost, canonicalShellMomentum_dispersion hρ hθ,
    Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  apply Prod.ext
  · apply Complex.ext <;>
      simp [canonicalShellMomentum, canonicalShellReal, canonicalShellImaginary,
        complexSpacetimeOfReal, Complex.mul_re, Complex.mul_im]
  · ext i
    fin_cases i <;> apply Complex.ext <;>
      simp [canonicalShellMomentum, canonicalShellReal, canonicalShellImaginary,
        complexSpacetimeOfReal, Complex.mul_re, Complex.mul_im]

/-- Continuous linear equivalence for the canonical shell frame, of type `Spacetime ≃L[ℝ]
Spacetime`. -/
noncomputable def canonicalShellFrame {t ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 < Real.sin θ) :
    Spacetime ≃L[ℝ] Spacetime :=
  lorentzNegativePairFrame (canonicalShellReal_negative hρ hθ)
    (canonicalShellImaginary_negative hρ hθ) (canonicalShellPair_orthogonal t ρ θ)

theorem canonicalShellFrame_gamma_sq {t ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 < Real.sin θ) :
    (canonicalShellFrame (t := t) hρ hθ (1, 0)).1 ^ 2 =
      1 + (canonicalShellEnergy t ρ θ * Real.cos θ) ^ 2 / ρ ^ 2 := by
  unfold canonicalShellFrame
  rw [lorentzNegativePairFrame_gamma_sq, canonicalShellReal_square hρ hθ,
    canonicalShellImaginary_square hθ]
  simp [canonicalShellReal, canonicalShellImaginary]

theorem canonicalShellFrame_gamma_scaled_sq {t ρ θ : ℝ}
    (hρ : 0 < ρ) (hθ : 0 < Real.sin θ) :
    (canonicalShellFrame (t := t) hρ hθ (1, 0)).1 ^ 2 * Real.sin θ ^ 2 * ρ ^ 2 =
      ρ ^ 2 + t ^ 2 * Real.cos θ ^ 2 := by
  rw [canonicalShellFrame_gamma_sq hρ hθ]
  calc
    _ = Real.sin θ ^ 2 * ρ ^ 2 +
        (canonicalShellEnergy t ρ θ ^ 2 * Real.sin θ ^ 2) * Real.cos θ ^ 2 := by
      field_simp [ne_of_gt hρ]
    _ = Real.sin θ ^ 2 * ρ ^ 2 + (t ^ 2 + ρ ^ 2) * Real.cos θ ^ 2 := by
      rw [canonicalShellEnergy_sq_mul_sin_sq hθ]
    _ = _ := by linear_combination ρ ^ 2 * Real.sin_sq_add_cos_sq θ

theorem canonicalShellFrame_gamma_mul_sin_le_two {t ρ θ : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hρ : 4 ≤ ρ) (hθ : 0 < Real.sin θ) :
    (canonicalShellFrame (t := t) (by linarith : 0 < ρ) hθ (1, 0)).1 * Real.sin θ ≤ 2 := by
  have ht : t ^ 2 ≤ 1 := by nlinarith
  have hc : t ^ 2 * Real.cos θ ^ 2 ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left (Real.cos_sq_le_one θ) (sq_nonneg t)).trans
      (by simpa using ht)
  have he := canonicalShellFrame_gamma_scaled_sq (t := t) (by linarith : 0 < ρ) hθ
  have hr : 16 ≤ ρ ^ 2 := by nlinarith
  have hprod : ((canonicalShellFrame (t := t) (by linarith : 0 < ρ) hθ (1, 0)).1 *
      Real.sin θ) ^ 2 ≤ 4 := by
    apply (_root_.mul_le_mul_iff_left₀ (sq_pos_of_pos (show 0 < ρ by linarith))).mp
    nlinarith only [he, hc, hr]
  nlinarith

end VacuumBellSeparation
