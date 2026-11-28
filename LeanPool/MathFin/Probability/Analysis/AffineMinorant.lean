/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Jensen's inequality through a supporting line

If `f` lies above the line through `(m, f m)` with slope `c` at almost every value of `X`, and
`X` has mean `m`, then `f(m) ≤ 𝔼[f(X)]`: the line averages to `f(m)`. For a convex `f` with a
supporting line at the mean this is Jensen's inequality. It asks for no closed domain, unlike
Mathlib's `ConvexOn.map_integral_le`, so it applies on `(0, ∞)`, where Black–Scholes prices are
convex in the spot (`Models/BlackScholes/SpotConvexity.bsV_spot_tangent_le`).

If the line lies strictly below `f` away from `m` and `X` is not almost surely `m`, the inequality
is strict: the gap `f(X) − line(X)` is nonnegative and positive with positive probability.

## Main results

* `le_integral_of_affine_le`: `f(m) ≤ 𝔼[f(X)]` from an affine minorant through `(m, f m)`.
* `lt_integral_of_affine_lt`: `f(m) < 𝔼[f(X)]` from a strict one, unless `X = m` almost surely.
* `integral_lt_integral_of_ae_le_of_not_ae_eq`: the integral is strictly monotone; the strict
  inequality above, and the strict upper bound of a jump-diffusion call
  (`Models/Jumps/JumpImpliedVol.lean`), both go through it.

## Tags

Jensen's inequality, supporting line, convexity, strict inequality, convex price in spot, MSC 60E15,
MSC 28A25
-/

@[expose] public section

namespace MathFin

open MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- **The integral is strictly monotone**: if `f ≤ g` almost everywhere and `f` and `g` are not
almost everywhere equal, then `∫ f < ∫ g`. -/
lemma integral_lt_integral_of_ae_le_of_not_ae_eq {f g : α → ℝ} (hf : Integrable f μ)
    (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) (hne : ¬f =ᵐ[μ] g) : ∫ a, f a ∂μ < ∫ a, g a ∂μ :=
  (integral_mono_ae hf hg hfg).lt_of_ne fun h ↦ hne ((integral_eq_iff_of_ae_le hf hg hfg).1 h)

variable [IsProbabilityMeasure μ]

/-- A line through `(m, y)` averages to `y` when `X` has mean `m`. -/
lemma integral_add_mul_sub {X : α → ℝ} {m : ℝ} (hX : Integrable X μ) (hm : ∫ a, X a ∂μ = m)
    (y c : ℝ) : ∫ a, (y + c * (X a - m)) ∂μ = y := by
  have hlin : Integrable (fun a ↦ c * (X a - m)) μ := (hX.sub (integrable_const m)).const_mul c
  rw [integral_add (integrable_const _) hlin, integral_const_mul,
    integral_sub hX (integrable_const m), hm, integral_const, integral_const, probReal_univ,
    one_smul, one_smul, sub_self, mul_zero, add_zero]

/-- **Jensen's inequality through a supporting line.** If `X` has mean `m` and
`f m + c (X − m) ≤ f(X)` almost surely, then `f(m) ≤ 𝔼[f(X)]`. -/
theorem le_integral_of_affine_le {X : α → ℝ} {f : ℝ → ℝ} {m c : ℝ} (hX : Integrable X μ)
    (hm : ∫ a, X a ∂μ = m) (hf : Integrable (fun a ↦ f (X a)) μ)
    (h : ∀ᵐ a ∂μ, f m + c * (X a - m) ≤ f (X a)) : f m ≤ ∫ a, f (X a) ∂μ :=
  (integral_add_mul_sub hX hm (f m) c).symm.trans_le <|
    integral_mono_ae ((integrable_const _).add ((hX.sub (integrable_const m)).const_mul c)) hf h

/-- **Strict Jensen's inequality through a supporting line.** If `X` has mean `m`, the line
`f m + c (X − m)` lies strictly below `f(X)` wherever `X ≠ m`, and `X` is not almost surely `m`,
then `f(m) < 𝔼[f(X)]`. -/
theorem lt_integral_of_affine_lt {X : α → ℝ} {f : ℝ → ℝ} {m c : ℝ} (hX : Integrable X μ)
    (hm : ∫ a, X a ∂μ = m) (hf : Integrable (fun a ↦ f (X a)) μ)
    (h : ∀ᵐ a ∂μ, X a ≠ m → f m + c * (X a - m) < f (X a)) (hX_ne : ¬X =ᵐ[μ] fun _ ↦ m) :
    f m < ∫ a, f (X a) ∂μ := by
  have hlin : Integrable (fun a ↦ f m + c * (X a - m)) μ :=
    (integrable_const _).add ((hX.sub (integrable_const m)).const_mul c)
  have hle : (fun a ↦ f m + c * (X a - m)) ≤ᵐ[μ] fun a ↦ f (X a) := by
    filter_upwards [h] with a ha
    rcases eq_or_ne (X a) m with hXa | hXa
    · simp [hXa]
    · exact (ha hXa).le
  refine (integral_add_mul_sub hX hm (f m) c).symm.trans_lt <|
    integral_lt_integral_of_ae_le_of_not_ae_eq hlin hf hle fun h_eq ↦ hX_ne ?_
  filter_upwards [h, h_eq] with a ha hfa
  by_contra hXa
  exact (ha hXa).ne hfa

end MathFin
