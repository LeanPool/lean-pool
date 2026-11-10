/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.EhrhardType.Characterization
public import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integrability for Ehrhard-type laws

A finite convex normal representative has an affine minorant. Thus all its negative
exponential moments are integrable. One positive exponential moment then gives every
polynomial moment. These are the integrability prerequisites of the Ehrhard-type moment inequalities
and FMP25 §3;
they do not assume a Gaussian convexity theorem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace EhrhardGaussian.EhrhardType

/-- A finite convex real function has a global supporting affine lower bound. -/
theorem exists_affine_minorant {h : ℝ → ℝ} (hc : ConvexOn ℝ univ h) :
    ∃ m c : ℝ, ∀ x, m * x + c ≤ h x := by
  let m := derivWithin h (Iio 0) 0
  refine ⟨m, h 0, fun x => ?_⟩
  have hi : (0 : ℝ) ∈ interior (univ : Set ℝ) := by rw [interior_univ]; trivial
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hs := hc.slope_le_leftDeriv_of_mem_interior (mem_univ x) hi hx
    rw [slope_def_field] at hs
    have hs' := (div_le_iff₀ (sub_pos.mpr hx)).mp hs
    change h 0 - h x ≤ m * (0 - x) at hs'
    linarith only [hs']
  · rw [mul_zero, zero_add]
  · have hs := (hc.leftDeriv_le_rightDeriv_of_mem_interior hi).trans
      (hc.rightDeriv_le_slope_of_mem_interior hi (mem_univ x) hx)
    rw [slope_def_field] at hs
    have hs' := (le_div_iff₀ (sub_pos.mpr hx)).mp hs
    change m * (x - 0) ≤ h x - h 0 at hs'
    linarith only [hs']

/-- Negative exponential moments of a finite convex normal functional are finite. -/
theorem integrable_exp_mul_of_convex {h : ℝ → ℝ} (hc : ConvexOn ℝ univ h)
    {q : ℝ} (hq : q ≤ 0) :
    Integrable (fun z => Real.exp (q * h z)) (gaussianReal 0 1) := by
  obtain ⟨m, c, hlower⟩ := exists_affine_minorant hc
  have hcont : Continuous h := continuousOn_univ.mp (hc.continuousOn isOpen_univ)
  have hmajor := (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (q * m)).const_mul
    (Real.exp (q * c))
  apply hmajor.mono' (hcont.measurable.const_mul q |>.exp |>.aestronglyMeasurable)
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hle := mul_le_mul_of_nonpos_left (hlower z) hq
  calc
    q * h z ≤ q * (m * z + c) := hle
    _ = _ := by ring

/-- Every Ehrhard law has all nonpositive exponential moments as ordinary integrals. -/
theorem integrable_exp_mul_of_isEhrhardType {μ : Measure ℝ} (hμ : IsEhrhardType μ)
    {q : ℝ} (hq : q ≤ 0) : Integrable (fun x => Real.exp (q * x)) μ := by
  obtain ⟨h, hh, hc, rfl⟩ := exists_monotone_convex_representative hμ
  apply (integrable_map_measure (by fun_prop) hh.measurable.aemeasurable).mpr
  exact integrable_exp_mul_of_convex hc hq

/-- A single positive exponential moment gives all polynomial moments of an Ehrhard law. -/
theorem integrable_pow_of_isEhrhardType {μ : Measure ℝ} (hμ : IsEhrhardType μ)
    (hexp : Integrable (fun x => Real.exp x) μ) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) μ := by
  have hpos : Integrable (fun x : ℝ => Real.exp (1 * x)) μ := by
    simpa only [one_mul] using hexp
  exact integrable_pow_of_integrable_exp_mul (X := id) one_ne_zero hpos
    (integrable_exp_mul_of_isEhrhardType hμ (by norm_num : (-1 : ℝ) ≤ 0)) n

/-- A finite positive exponential moment gives square integrability for an Ehrhard-type law. -/
theorem integrable_sq_of_isEhrhardType {μ : Measure ℝ} (hμ : IsEhrhardType μ)
    (hexp : Integrable (fun x => Real.exp x) μ) : Integrable (fun x : ℝ => x ^ 2) μ :=
  integrable_pow_of_isEhrhardType hμ hexp 2

/-- The expectation used at parameter zero of the normalized log MGF is an ordinary integral. -/
theorem integrable_id_of_isEhrhardType {μ : Measure ℝ} (hμ : IsEhrhardType μ)
    (hexp : Integrable (fun x => Real.exp x) μ) : Integrable id μ := by
  change Integrable (fun x : ℝ => x) μ
  exact (integrable_pow_of_isEhrhardType hμ hexp 1).congr
    (ae_of_all _ fun x => pow_one x)

/-- Exponential integrability around zero, needed for the analytic log-MGF derivative. -/
theorem zero_mem_interior_integrableExpSet_of_isEhrhardType {μ : Measure ℝ}
    (hμ : IsEhrhardType μ) (hexp : Integrable (fun x => Real.exp x) μ) :
    0 ∈ interior (integrableExpSet id μ) := by
  apply mem_interior_iff_mem_nhds.mpr
  apply mem_of_superset (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
  intro t ht
  have hneg := integrable_exp_mul_of_isEhrhardType hμ (by norm_num : (-1 : ℝ) ≤ 0)
  have hpos : Integrable (fun x : ℝ => Real.exp (1 * x)) μ := by
    simpa only [one_mul] using hexp
  exact integrable_exp_mul_of_le_of_le (X := id) hneg hpos ht.1.le ht.2.le

/-- Any one strictly positive exponential moment supplies a neighborhood of zero. -/
theorem zero_mem_interior_integrableExpSet_of_positive_moment {μ : Measure ℝ}
    (hμ : IsEhrhardType μ) {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun x => Real.exp (r * x)) μ) :
    0 ∈ interior (integrableExpSet id μ) := by
  apply mem_interior_iff_mem_nhds.mpr
  apply mem_of_superset (Ioo_mem_nhds (neg_neg_of_pos hr) hr)
  intro t ht
  have hneg := integrable_exp_mul_of_isEhrhardType hμ (neg_nonpos.mpr hr.le)
  exact integrable_exp_mul_of_le_of_le (X := id) hneg hexp ht.1.le ht.2.le

end EhrhardGaussian.EhrhardType
