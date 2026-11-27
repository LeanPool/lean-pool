/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Interval.Taylor
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Steklov averages

The **Steklov average** of `g : ℝ → ℂ` with step `η` is the forward mean

`M_η g(x) = η^(-1) ∫_0^η g(x + τ) dτ`   (`Interval.steklov`).

For continuous `g` it is differentiable with `(M_η g)' = η^(-1) Δ_η g`
(`Interval.hasDerivAt_steklov`): averaging gains one derivative.  Steklov averages commute with
translations and differences, so the `m`-fold average `M_η^m g` of a continuous `g` lies in
`C^m` (`Interval.contDiff_steklovIter`) with

`(M_η^r g)^(r) = η^(-r) Δ_η^r g`   (`Interval.iteratedDeriv_steklovIter`).

The derivative of order `r` of a smoothed function is therefore a difference of order `r` of the
original function, which is how moduli of smoothness control the approximation of smooth
functions in Jackson's inequality.
-/

@[expose] public section

open MeasureTheory Set Polynomial
open Rd (higherDiff)
open scoped ENNReal

namespace Interval

/-- The **Steklov average** `M_η g(x) = η^(-1) ∫_0^η g(x + τ) dτ`. -/
noncomputable def steklov (η : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((η : ℂ))⁻¹ * ∫ τ in (0 : ℝ)..η, g (x + τ)

/-- `M_η g(x) = η^(-1) ∫_x^{x+η} g`. -/
theorem steklov_eq (η : ℝ) (g : ℝ → ℂ) (x : ℝ) :
    steklov η g x = ((η : ℂ))⁻¹ * ∫ t in x..x + η, g t := by
  rw [steklov, intervalIntegral.integral_comp_add_left, add_zero]

/-- **Steklov averages gain a derivative**: `(M_η g)' = η^(-1) (g(· + η) - g)` for continuous
`g`. -/
theorem hasDerivAt_steklov {g : ℝ → ℂ} (hg : Continuous g) (η x : ℝ) :
    HasDerivAt (steklov η g) (((η : ℂ))⁻¹ * (g (x + η) - g x)) x := by
  have hF : ∀ y, HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, g t) (g y) y := fun y =>
    (hg.integral_hasStrictDerivAt 0 y).hasDerivAt
  have hrepr : steklov η g = fun y => ((η : ℂ))⁻¹ *
      ((∫ t in (0 : ℝ)..y + η, g t) - ∫ t in (0 : ℝ)..y, g t) := by
    funext y
    rw [steklov_eq, intervalIntegral.integral_interval_sub_left
      (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  rw [hrepr]
  exact (((hF (x + η)).comp_add_const x η).sub (hF x)).const_mul _

/-- Steklov averages of continuous functions are differentiable. -/
theorem differentiable_steklov {g : ℝ → ℂ} (hg : Continuous g) (η : ℝ) :
    Differentiable ℝ (steklov η g) :=
  fun x => (hasDerivAt_steklov hg η x).differentiableAt

/-- The derivative of a Steklov average. -/
theorem deriv_steklov {g : ℝ → ℂ} (hg : Continuous g) (η : ℝ) :
    deriv (steklov η g) = fun x => ((η : ℂ))⁻¹ * fwdDiff η g x :=
  funext fun x => (hasDerivAt_steklov hg η x).deriv

/-- Steklov averages commute with translations. -/
theorem steklov_comp_add (η : ℝ) (g : ℝ → ℂ) (c : ℝ) :
    steklov η (fun y => g (y + c)) = fun x => steklov η g (x + c) := by
  funext x
  simp only [steklov]
  congr 1
  exact intervalIntegral.integral_congr fun τ _ => by
    show g (x + τ + c) = g (x + c + τ)
    rw [add_right_comm]

/-- Steklov averages are additive on continuous functions. -/
theorem steklov_sub {g₁ g₂ : ℝ → ℂ} (h₁ : Continuous g₁) (h₂ : Continuous g₂) (η : ℝ) :
    steklov η (fun y => g₁ y - g₂ y) = fun x => steklov η g₁ x - steklov η g₂ x := by
  funext x
  simp only [steklov]
  have c₁ : Continuous fun τ => g₁ (x + τ) := h₁.comp (continuous_const.add continuous_id)
  have c₂ : Continuous fun τ => g₂ (x + τ) := h₂.comp (continuous_const.add continuous_id)
  rw [intervalIntegral.integral_sub (c₁.intervalIntegrable _ _) (c₂.intervalIntegrable _ _),
    mul_sub]

/-- Steklov averages commute with forward differences. -/
theorem steklov_fwdDiff {g : ℝ → ℂ} (hg : Continuous g) (η h : ℝ) :
    steklov η (fwdDiff h g) = fwdDiff h (steklov η g) := by
  have : fwdDiff h g = fun y => g (y + h) - g y := rfl
  have c : Continuous fun y => g (y + h) := hg.comp (continuous_id.add continuous_const)
  rw [this, steklov_sub c hg, steklov_comp_add]
  rfl

/-- Steklov averages of continuous functions are continuous. -/
theorem continuous_steklov {g : ℝ → ℂ} (hg : Continuous g) (η : ℝ) :
    Continuous (steklov η g) :=
  (differentiable_steklov hg η).continuous

/-- Forward differences of continuous functions are continuous. -/
theorem continuous_fwdDiff {g : ℝ → ℂ} (hg : Continuous g) (h : ℝ) : Continuous (fwdDiff h g) :=
  (hg.comp (continuous_id.add continuous_const)).sub hg

/-- Forward differences keep smoothness. -/
theorem contDiff_fwdDiff {k : ℕ} {g : ℝ → ℂ} (hg : ContDiff ℝ k g) (h : ℝ) :
    ContDiff ℝ k (fwdDiff h g) :=
  (hg.comp (contDiff_id.add contDiff_const)).sub hg

/-- **Averaging gains one derivative**: `g ∈ C^k` implies `M_η g ∈ C^(k+1)`. -/
theorem contDiff_steklov {k : ℕ} {g : ℝ → ℂ} (hg : ContDiff ℝ k g) (η : ℝ) :
    ContDiff ℝ (k + 1) (steklov η g) := by
  have hc : Continuous g := hg.continuous
  have h1 : ContDiff ℝ ((k : WithTop ℕ∞) + 1) (steklov η g) := by
    refine contDiff_succ_iff_deriv.2 ⟨differentiable_steklov hc η, fun h => ?_, ?_⟩
    · exact absurd h (by simp)
    · rw [deriv_steklov hc]
      exact contDiff_const.mul (contDiff_fwdDiff hg η)
  exact_mod_cast h1

/-- The `m`-fold Steklov average `M_η^m g`. -/
noncomputable def steklovIter (m : ℕ) (η : ℝ) (g : ℝ → ℂ) : ℝ → ℂ := (steklov η)^[m] g

/-- `M_η^(m+1) = M_η ∘ M_η^m`. -/
theorem steklovIter_succ (m : ℕ) (η : ℝ) (g : ℝ → ℂ) :
    steklovIter (m + 1) η g = steklov η (steklovIter m η g) := by
  rw [steklovIter, Function.iterate_succ_apply']
  rfl

/-- **The `m`-fold Steklov average of a continuous function lies in `C^m`**. -/
theorem contDiff_steklovIter {g : ℝ → ℂ} (hg : Continuous g) (m : ℕ) (η : ℝ) :
    ContDiff ℝ m (steklovIter m η g) := by
  induction m with
  | zero => exact contDiff_zero.2 hg
  | succ m ih =>
    rw [steklovIter_succ]
    exact_mod_cast contDiff_steklov ih η

/-- Iterated Steklov averages of continuous functions are continuous. -/
theorem continuous_steklovIter {g : ℝ → ℂ} (hg : Continuous g) (m : ℕ) (η : ℝ) :
    Continuous (steklovIter m η g) :=
  (contDiff_steklovIter hg m η).continuous

/-- Iterated Steklov averages commute with forward differences. -/
theorem steklovIter_fwdDiff {g : ℝ → ℂ} (hg : Continuous g) (m : ℕ) (η h : ℝ) :
    steklovIter m η (fwdDiff h g) = fwdDiff h (steklovIter m η g) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [steklovIter_succ, steklovIter_succ, ih,
      steklov_fwdDiff (continuous_steklovIter hg m η)]

/-- **The derivative of order `k` of an iterated Steklov average**:
`(M_η^(m+k) g)^(k) = η^(-k) M_η^m (Δ_η^k g)` for continuous `g`. -/
theorem iteratedDeriv_steklovIter_add {g : ℝ → ℂ} (hg : Continuous g) (m k : ℕ) (η : ℝ) :
    iteratedDeriv k (steklovIter (m + k) η g) =
      fun x => ((η : ℂ))⁻¹ ^ k * steklovIter m η (higherDiff k η g) x := by
  induction k generalizing g with
  | zero => funext x; simp [higherDiff]
  | succ k ih =>
    rw [iteratedDeriv_succ', show m + (k + 1) = m + k + 1 by ring, steklovIter_succ,
      deriv_steklov (continuous_steklovIter hg (m + k) η),
      ← steklovIter_fwdDiff hg (m + k) η η]
    funext x
    rw [iteratedDeriv_const_mul_field, ih (continuous_fwdDiff hg η), higherDiff_succ', pow_succ]
    ring

/-- **`(M_η^r g)^(r) = η^(-r) Δ_η^r g`** for continuous `g`. -/
theorem iteratedDeriv_steklovIter {g : ℝ → ℂ} (hg : Continuous g) (r : ℕ) (η : ℝ) :
    iteratedDeriv r (steklovIter r η g) = fun x => ((η : ℂ))⁻¹ ^ r * higherDiff r η g x := by
  have h := iteratedDeriv_steklovIter_add hg 0 r η
  rw [zero_add] at h
  rw [h]
  rfl

end Interval
