/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Defs
public import Mathlib.Analysis.Distribution.FourierMultiplier

/-!
# Massive Klein–Gordon powers on the Schwartz core

The symbols use Mathlib's normalized Fourier frequency. Their temperate growth
is proved, so `fourierMultiplierCLM` is actual multiplication, not its default
zero branch. The positive square-root symbol is the source energy evaluated at
`2πξ`.
-/

@[expose] public section

open scoped SchwartzMap FourierTransform
open MeasureTheory

namespace VacuumBellSeparation

/-- A scaled Bessel-potential symbol for the `s`th power of the massive energy.
Theorems identifying it with the energy use `m > 0`. -/
noncomputable def massiveSchwartzSymbol (m s : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  m ^ s * (1 + ‖((2 * Real.pi) / m) • ξ‖ ^ 2) ^ (s / 2)

theorem hasTemperateGrowth_massiveSchwartzSymbol (m s : ℝ) :
    Function.HasTemperateGrowth (massiveSchwartzSymbol m s) := by
  unfold massiveSchwartzSymbol
  apply Function.HasTemperateGrowth.mul (Function.HasTemperateGrowth.const _)
  exact (Function.hasTemperateGrowth_one_add_norm_sq_rpow
    (EuclideanSpace ℝ (Fin 3)) (s / 2)).comp (by fun_prop)

theorem massiveSchwartzSymbol_pos {m : ℝ} (hm : 0 < m) (s : ℝ)
    (ξ : EuclideanSpace ℝ (Fin 3)) : 0 < massiveSchwartzSymbol m s ξ := by
  unfold massiveSchwartzSymbol
  positivity

theorem massiveSchwartzSymbol_add {m : ℝ} (hm : 0 < m) (s t : ℝ)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    massiveSchwartzSymbol m (s + t) ξ =
      massiveSchwartzSymbol m s ξ * massiveSchwartzSymbol m t ξ := by
  unfold massiveSchwartzSymbol
  rw [Real.rpow_add hm, add_div, Real.rpow_add (by positivity)]
  ring

@[simp] theorem massiveSchwartzSymbol_zero (m : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    massiveSchwartzSymbol m 0 ξ = 1 := by
  simp [massiveSchwartzSymbol]

theorem massiveSchwartzSymbol_two {m : ℝ} (hm : 0 < m)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    massiveSchwartzSymbol m 2 ξ = m ^ 2 + (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 := by
  have hc : 0 ≤ 2 * Real.pi / m := by positivity
  simp only [massiveSchwartzSymbol, div_self (by norm_num : (2 : ℝ) ≠ 0),
    Real.rpow_two, Real.rpow_one,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  field_simp [hm.ne']

/-- The positive first-power symbol is exactly the relativistic energy. -/
theorem massiveSchwartzSymbol_one {m : ℝ} (hm : 0 < m)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    massiveSchwartzSymbol m 1 ξ = dispersion m ((2 * Real.pi) • ξ) := by
  have hsq : (massiveSchwartzSymbol m 1 ξ) ^ 2 =
      m ^ 2 + (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 := by
    rw [pow_two, ← massiveSchwartzSymbol_add hm, show (1 : ℝ) + 1 = 2 by norm_num,
      massiveSchwartzSymbol_two hm]
  have hd : (dispersion m ((2 * Real.pi) • ξ)) ^ 2 =
      m ^ 2 + (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 := by
    rw [dispersion, Real.sq_sqrt (by positivity), norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    ring
  have hp := massiveSchwartzSymbol_pos hm 1 ξ
  have hq : 0 ≤ dispersion m ((2 * Real.pi) • ξ) := Real.sqrt_nonneg _
  nlinarith

theorem massiveSchwartzSymbol_neg_one {m : ℝ} (hm : 0 < m)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    massiveSchwartzSymbol m (-1) ξ = (dispersion m ((2 * Real.pi) • ξ))⁻¹ := by
  have h := massiveSchwartzSymbol_add hm (-1) 1 ξ
  rw [neg_add_cancel, massiveSchwartzSymbol_zero, massiveSchwartzSymbol_one hm] at h
  exact eq_inv_of_mul_eq_one_left h.symm

/-- Powers of the position-space massive energy on the Schwartz core. -/
noncomputable def massiveSchwartzPower (m s : ℝ) :
    SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ →L[ℂ]
      SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ :=
  SchwartzMap.fourierMultiplierCLM ℂ (fun ξ => (massiveSchwartzSymbol m s ξ : ℂ))

theorem hasTemperateGrowth_complex_massiveSchwartzSymbol (m s : ℝ) :
    Function.HasTemperateGrowth (fun ξ => (massiveSchwartzSymbol m s ξ : ℂ)) :=
  Complex.ofRealCLM.hasTemperateGrowth.comp (hasTemperateGrowth_massiveSchwartzSymbol m s)

/-- Powers compose by addition of their exponents on the Schwartz core. -/
theorem massiveSchwartzPower_add {m : ℝ} (hm : 0 < m) (s t : ℝ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    massiveSchwartzPower m s (massiveSchwartzPower m t f) = massiveSchwartzPower m (s + t) f := by
  unfold massiveSchwartzPower
  rw [SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply
    (hasTemperateGrowth_complex_massiveSchwartzSymbol m s)
    (hasTemperateGrowth_complex_massiveSchwartzSymbol m t)]
  congr 2
  funext ξ
  simp only [Pi.mul_apply, massiveSchwartzSymbol_add hm, Complex.ofReal_mul]

@[simp] theorem massiveSchwartzPower_zero (m : ℝ) :
    massiveSchwartzPower m 0 = ContinuousLinearMap.id ℂ _ := by
  simp [massiveSchwartzPower, massiveSchwartzSymbol_zero]

/-- The reciprocal and square-root energy multipliers are genuine inverses on this core. -/
theorem massiveSchwartzPower_inv {m : ℝ} (hm : 0 < m) (s : ℝ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    massiveSchwartzPower m (-s) (massiveSchwartzPower m s f) = f := by
  rw [massiveSchwartzPower_add hm, neg_add_cancel, massiveSchwartzPower_zero]
  rfl

open Laplacian

/-- The second energy power is the actual massive spatial Klein–Gordon
differential operator, with the Laplacian sign fixed by Fourier normalization. -/
theorem massiveSchwartzPower_two {m : ℝ} (hm : 0 < m)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    massiveSchwartzPower m 2 f = ((m ^ 2 : ℝ) : ℂ) • f - Δ f := by
  apply (FourierTransform.fourierCLE ℂ
    (SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)).injective
  change 𝓕 (massiveSchwartzPower m 2 f) = 𝓕 (((m ^ 2 : ℝ) : ℂ) • f - Δ f)
  rw [SchwartzMap.laplacian_eq_fourierMultiplierCLM]
  simp only [massiveSchwartzPower, SchwartzMap.fourierMultiplierCLM_apply,
    sub_eq_add_neg, FourierTransform.fourier_add, FourierTransform.fourier_neg,
    FourierTransform.fourier_smul,
    FourierTransform.fourier_fourierInv_eq]
  ext ξ
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (hasTemperateGrowth_complex_massiveSchwartzSymbol m 2)]
  simp only [
    SchwartzMap.smulLeftCLM_apply_apply
      (Function.hasTemperateGrowth_norm_sq (EuclideanSpace ℝ (Fin 3))),
    smul_apply, add_apply, neg_apply, smul_eq_mul, Complex.real_smul,
    massiveSchwartzSymbol_two hm]
  push_cast
  ring

/-- The positive-energy first-power multiplier squares to `-Δ + m²` on Schwartz space. -/
theorem massiveSchwartzPower_one_sq {m : ℝ} (hm : 0 < m)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    massiveSchwartzPower m 1 (massiveSchwartzPower m 1 f) =
      ((m ^ 2 : ℝ) : ℂ) • f - Δ f := by
  rw [massiveSchwartzPower_add hm, show (1 : ℝ) + 1 = 2 by norm_num,
    massiveSchwartzPower_two hm]

end VacuumBellSeparation
