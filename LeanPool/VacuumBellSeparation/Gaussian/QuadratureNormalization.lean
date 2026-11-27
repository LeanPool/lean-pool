/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalCharacteristic

/-!
# Literal real-quadrature normalization of the canonical thermal model

The real label `(x,y)` represents the actual Weyl operator at
`(x+i y)/sqrt(2)`. Consequently the Weyl phase is `exp(-i σ/2)` and the
thermal covariance is `(1+q)/(2(1-q)) I`, with vacuum covariance `I/2`.
These are statements about the constructed Weyl unitaries and states;
no unbounded position/momentum generator or arbitrary-field identification
is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open scoped ComplexConjugate

/-- Quadrature label given by `((v.1 : ℂ) + Complex.I * (v.2 : ℂ)) / (Real.sqrt 2 : ℂ)`. -/
noncomputable def quadratureLabel (v : ℝ × ℝ) : ℂ :=
  ((v.1 : ℂ) + Complex.I * (v.2 : ℂ)) / (Real.sqrt 2 : ℂ)

/-- Quadrature symplectic given by `v.1 * w.2 - v.2 * w.1`. -/
def quadratureSymplectic (v w : ℝ × ℝ) : ℝ := v.1 * w.2 - v.2 * w.1

theorem quadratureLabel_add (v w : ℝ × ℝ) :
    quadratureLabel (v + w) = quadratureLabel v + quadratureLabel w := by
  simp only [quadratureLabel, Prod.fst_add, Prod.snd_add, Complex.ofReal_add]
  ring

theorem quadratureLabel_norm_sq (v : ℝ × ℝ) :
    ‖quadratureLabel v‖ ^ 2 = (v.1 ^ 2 + v.2 ^ 2) / 2 := by
  rw [quadratureLabel, norm_div, div_pow,
    Complex.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num),
    Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem quadratureLabel_symplectic (v w : ℝ × ℝ) :
    (conj (quadratureLabel v) * quadratureLabel w).im = quadratureSymplectic v w / 2 := by
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [quadratureLabel, quadratureLabel, map_div₀, Complex.conj_ofReal,
    div_mul_div_comm, hs]
  simp [quadratureSymplectic,
    Complex.mul_re, Complex.mul_im]
  ring

/-- Quadrature Weyl obtained from `oscillatorWeyl`. -/
noncomputable def quadratureWeyl (v : ℝ × ℝ) :
    OscillatorSpace →L[ℂ] OscillatorSpace := oscillatorWeyl (quadratureLabel v)

theorem quadratureWeyl_mem_unitary (v : ℝ × ℝ) :
    quadratureWeyl v ∈ unitary (OscillatorSpace →L[ℂ] OscillatorSpace) :=
  oscillatorWeyl_mem_unitary _

theorem quadratureWeyl_mul (v w : ℝ × ℝ) :
    quadratureWeyl v * quadratureWeyl w =
      Complex.exp (-(Complex.I * ((quadratureSymplectic v w / 2 : ℝ) : ℂ))) •
        quadratureWeyl (v + w) := by
  rw [quadratureWeyl, quadratureWeyl, oscillatorWeyl_mul, weylPhase]
  simp only [id_eq, RCLike.inner_apply', quadratureLabel_symplectic,
    quadratureWeyl, quadratureLabel_add]

/-- Thermal quadrature variance given by `(1 + q) / (2 * (1 - q))`. -/
noncomputable def thermalQuadratureVariance (q : ℝ) : ℝ := (1 + q) / (2 * (1 - q))

theorem thermalState_quadratureWeyl {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (v : ℝ × ℝ) : thermalState hq₀ hq₁ (quadratureWeyl v) =
      Complex.exp (((-(thermalQuadratureVariance q / 2) * (v.1 ^ 2 + v.2 ^ 2) : ℝ) : ℂ)) := by
  rw [quadratureWeyl, thermalState_oscillatorWeyl hq₀ hq₁, quadratureLabel_norm_sq]
  congr 1
  rw [thermalQuadratureVariance]
  push_cast
  ring

theorem thermalQuadratureVariance_zero : thermalQuadratureVariance 0 = 1 / 2 := by
  norm_num [thermalQuadratureVariance]

theorem half_le_thermalQuadratureVariance {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    1 / 2 ≤ thermalQuadratureVariance q := by
  unfold thermalQuadratureVariance
  rw [le_div_iff₀ (mul_pos (by norm_num) (sub_pos.mpr hq₁))]
  nlinarith

theorem half_lt_thermalQuadratureVariance {q : ℝ} (hq₀ : 0 < q) (hq₁ : q < 1) :
    1 / 2 < thermalQuadratureVariance q := by
  unfold thermalQuadratureVariance
  rw [lt_div_iff₀ (mul_pos (by norm_num) (sub_pos.mpr hq₁))]
  nlinarith

theorem thermalQuadratureVariance_parameter {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    (2 * thermalQuadratureVariance q - 1) / (2 * thermalQuadratureVariance q + 1) = q := by
  have ha : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq₁)
  have hb : 2 * thermalQuadratureVariance q + 1 ≠ 0 := by
    have h := half_le_thermalQuadratureVariance hq₀ hq₁
    linarith
  rw [div_eq_iff hb]
  unfold thermalQuadratureVariance
  field_simp [ha]
  ring

end VacuumBellSeparation.Gaussian
