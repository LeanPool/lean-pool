/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Gaussian.StandardNormal

/-!
# Derivative of the standard normal CDF: `Φ'(x) = ϕ(x)`

The standard normal CDF `Phi x = (gaussianReal 0 1 (Iic x)).toReal` has
derivative equal to the standard normal PDF at every point, by FTC.

This is a foundational identity not present in Mathlib (no `Real.erf`, no
`gaussianReal_Iic_hasDerivAt`). Proved here via Lebesgue-`Iic` decomposition
into an interval integral plus a constant, then `intervalIntegral.integral_hasDerivAt_right`.

## Main results

* `hasDerivAt_Phi` — `HasDerivAt Phi (gaussianPDFReal 0 1 x) x` for every `x : ℝ`.
* `hasDerivAt_gaussianPDFReal_zero_one` — the PDF derivative `ϕ'(z) = -z·ϕ(z)`
  (and its `.neg`-flip `hasDerivAt_neg_gaussianPDFReal_zero_one`), the
  standard-normal first derivative reused across the Greeks and the Bachelier
  truncated-mean identity.

## Tags

standard normal CDF, normal density, Black–Scholes delta, Gaussian derivative,
fundamental theorem of calculus, MSC 60E05, MSC 91G20
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-- `(−ϕ(0,1,·))' = z · ϕ(0,1,z)`. Algebraic content: `d/dz [exp(-z²/2)] = -z · exp(-z²/2)`. -/
lemma hasDerivAt_neg_gaussianPDFReal_zero_one (z : ℝ) :
    HasDerivAt (fun z' : ℝ ↦ -gaussianPDFReal 0 1 z')
      (z * gaussianPDFReal 0 1 z) z := by
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  set c := (Real.sqrt (2 * π))⁻¹
  -- d/dz [-z²/2] = -z
  have h_sq : HasDerivAt (fun z' : ℝ ↦ -(z'^2)/2) (-z) z := by
    have h_pow : HasDerivAt (fun z' : ℝ ↦ z'^2) (2 * z) z := by
      simpa using hasDerivAt_pow 2 z
    have h_div : HasDerivAt (fun z' : ℝ ↦ z'^2 / 2) z z := by
      have := h_pow.div_const 2; simpa using this
    have h_neg : HasDerivAt (fun z' : ℝ ↦ -(z'^2 / 2)) (-z) z := h_div.neg
    have h_eq : (fun z' : ℝ ↦ -(z'^2)/2) = (fun z' : ℝ ↦ -(z'^2 / 2)) := by
      funext z'; ring
    rw [h_eq]; exact h_neg
  -- d/dz [exp(-z²/2)] = exp(-z²/2) · -z
  have h_exp : HasDerivAt (fun z' : ℝ ↦ Real.exp (-(z'^2)/2))
      (Real.exp (-(z^2)/2) * -z) z := h_sq.exp
  -- d/dz [c · exp(-z²/2)] = c · exp(-z²/2) · -z
  have h_const : HasDerivAt (fun z' : ℝ ↦ c * Real.exp (-(z'^2)/2))
      (c * (Real.exp (-(z^2)/2) * -z)) z := h_exp.const_mul c
  -- neg
  have h_neg := h_const.neg
  convert h_neg using 1; ring

/-- `ϕ(0,1,·)' = -z · ϕ(0,1,z)` — the standard-normal PDF derivative (the
`.neg`-flip of `hasDerivAt_neg_gaussianPDFReal_zero_one`). The single
standard-normal first-derivative reused across the Greeks files. -/
theorem hasDerivAt_gaussianPDFReal_zero_one (z : ℝ) :
    HasDerivAt (fun z' : ℝ ↦ gaussianPDFReal 0 1 z')
      (-(z * gaussianPDFReal 0 1 z)) z := by
  have h := (hasDerivAt_neg_gaussianPDFReal_zero_one z).neg
  have h_eq : ((-fun z' : ℝ ↦ -gaussianPDFReal 0 1 z') : ℝ → ℝ)
            = fun z' : ℝ ↦ gaussianPDFReal 0 1 z' := by funext z'; simp
  rw [h_eq] at h
  exact h

/-- **Standard normal CDF derivative**: `Phi'(x) = gaussianPDFReal 0 1 x`. -/
theorem hasDerivAt_Phi (x : ℝ) :
    HasDerivAt Phi (gaussianPDFReal 0 1 x) x := by
  set a : ℝ := x - 1
  have hax : a < x := by change x - 1 < x; linarith
  have h_pdf_int : Integrable (gaussianPDFReal 0 1) volume :=
    integrable_gaussianPDFReal _ _
  have h_pdf_cont : Continuous (gaussianPDFReal 0 1) := by
    unfold gaussianPDFReal
    exact (continuous_const).mul (by fun_prop)
  have h_int_ax : IntervalIntegrable (gaussianPDFReal 0 1) volume a x :=
    h_pdf_int.intervalIntegrable
  -- FTC right endpoint
  have h_ftc : HasDerivAt (fun u ↦ ∫ z in a..u, gaussianPDFReal 0 1 z)
      (gaussianPDFReal 0 1 x) x :=
    intervalIntegral.integral_hasDerivAt_right h_int_ax
      h_pdf_cont.aestronglyMeasurable.stronglyMeasurableAtFilter
      h_pdf_cont.continuousAt
  -- Add the constant Phi a.
  have h_shifted : HasDerivAt
      (fun u ↦ Phi a + ∫ z in a..u, gaussianPDFReal 0 1 z)
      (gaussianPDFReal 0 1 x) x := by
    have := h_ftc.const_add (Phi a)
    simpa using this
  -- Phi equals this function in a neighborhood of x (for y > a).
  have h_eq_nhds : Phi =ᶠ[nhds x]
      (fun u ↦ Phi a + ∫ z in a..u, gaussianPDFReal 0 1 z) := by
    refine Filter.eventually_of_mem (Ioi_mem_nhds hax) ?_
    intro y hy
    rw [Set.mem_Ioi] at hy
    change Phi y = Phi a + ∫ z in a..y, gaussianPDFReal 0 1 z
    rw [Phi_eq_integral, Phi_eq_integral, intervalIntegral.integral_of_le hy.le]
    have h_decomp : Set.Iic y = Set.Iic a ∪ Set.Ioc a y := by
      ext z
      simp only [Set.mem_Iic, Set.mem_union, Set.mem_Ioc]
      refine ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩
      · by_cases h : z ≤ a
        · exact Or.inl h
        · exact Or.inr ⟨not_le.mp h, hz⟩
      · rcases hz with h | ⟨_, h⟩
        · linarith
        · exact h
    have h_disj : Disjoint (Set.Iic a) (Set.Ioc a y) := by
      rw [Set.disjoint_left]
      intro z hz1 hz2
      simp only [Set.mem_Iic] at hz1
      simp only [Set.mem_Ioc] at hz2
      linarith [hz2.1]
    rw [h_decomp, setIntegral_union h_disj measurableSet_Ioc
      h_pdf_int.integrableOn h_pdf_int.integrableOn]
  exact h_shifted.congr_of_eventuallyEq h_eq_nhds

end MathFin
