/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityQuadraticProduct
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityPressureFixedMultiplier

/-!
# Stability Quadratic Integral

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

namespace CKN

/-- Quadratic velocity pairings against a bounded test converge under
strong local `L³` convergence. -/
theorem stability_tendsto_integral_quadratic_test
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (F G : ℕ → α → ℝ) (f g φ : α → ℝ)
    (hF : ∀ n, MemLp (F n) 3 μ) (hG : ∀ n, MemLp (G n) 3 μ)
    (hf : MemLp f 3 μ) (hg : MemLp g 3 μ)
    (hφ : MemLp φ ∞ μ)
    (hFconv : Tendsto (fun n => eLpNorm (F n - f) 3 μ) atTop (nhds 0))
    (hGconv : Tendsto (fun n => eLpNorm (G n - g) 3 μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, F n x * G n x * φ x ∂μ) atTop
      (nhds (∫ x, f x * g x * φ x ∂μ)) := by
  let : ENNReal.HolderTriple (3 : ℝ≥0∞) 3 (3 / 2 : ℝ≥0∞) := by
    have hreal : Real.HolderTriple 3 3 (3 / 2) := by
      exact ⟨by norm_num, by norm_num, by norm_num⟩
    simpa only [CKN.ofReal_threeHalves, ENNReal.ofReal_ofNat] using
      hreal.ennrealOfReal
  have hQn (n : ℕ) : MemLp (fun x => F n x * G n x)
      (3 / 2 : ℝ≥0∞) μ := by
    have h : MemLp (F n * G n) (3 / 2 : ℝ≥0∞) μ :=
      (hF n).mul (hG n)
    have heq : F n * G n = (fun x => F n x * G n x) := by
      funext x
      rfl
    rwa [heq] at h
  have hQconv := stability_tendsto_eLpNorm_product_three
    F G f g hF hG hf hg hFconv hGconv
  have h := stability_tendsto_integral_mul_test_of_LthreeHalves μ
    (fun n x => F n x * G n x) (fun x => f x * g x) φ
    hQn hφ hQconv
  have heqFn (n : ℕ) :
      (∫ x, φ x * (F n x * G n x) ∂μ) =
        ∫ x, F n x * G n x * φ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have heqG : (∫ x, φ x * (f x * g x) ∂μ) =
      ∫ x, f x * g x * φ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  simpa only [heqFn, heqG] using h

end CKN
