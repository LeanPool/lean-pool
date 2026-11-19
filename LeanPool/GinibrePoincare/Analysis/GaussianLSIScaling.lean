/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianLSIScaling.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GaussianLSIReal

/-!
# Gaussian LSI scaling

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gaussianReal_lsi_variance_C1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Sharp Gaussian LSI after a nondegenerate dilation. -/
theorem gaussianReal_lsi_dilation (c : ℝ) (hc : c ≠ 0)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    squareEntropy (gaussianReal 0 ⟨c ^ 2, sq_nonneg c⟩) f ≤
      (2 * c ^ 2) * ∫ x, (deriv f x) ^ 2 ∂gaussianReal 0 ⟨c ^ 2, sq_nonneg c⟩ := by
  let F : ℝ → ℝ := fun x => f (c * x)
  have hF : ContDiff ℝ 2 F := hf.comp (by fun_prop)
  have hFc : HasCompactSupport F := hfc.comp_homeomorph (Homeomorph.mulLeft₀ c hc)
  have hd (x : ℝ) : deriv F x = deriv f (c * x) * c :=
    by simpa only [F, Function.comp_def, mul_one] using ((hf.differentiable (by norm_num) (c *
         x)).hasDerivAt.comp x
      ((hasDerivAt_id x).const_mul c)).deriv
  have hmap : (gaussianReal 0 1).map (fun x => c * x) = gaussianReal 0 ⟨c ^ 2, sq_nonneg c⟩ := by
    convert! gaussianReal_map_const_mul (μ := 0) (v := 1) c using 1
    simp only [mul_zero, mul_one]
    congr 1
  have hent : squareEntropy (gaussianReal 0 ⟨c ^ 2, sq_nonneg c⟩) f =
      squareEntropy (gaussianReal 0 1) F := by
    rw [← hmap]
    exact squareEntropy_map _ _ (by fun_prop) f (hf.continuous.pow 2).aestronglyMeasurable
        (continuous_square_mul_log hf.continuous).aestronglyMeasurable
  have he : (∫ x, (deriv F x) ^ 2 ∂gaussianReal 0 1) =
      c ^ 2 * ∫ x, (deriv f x) ^ 2 ∂gaussianReal 0 ⟨c ^ 2, sq_nonneg c⟩ := by
    simp_rw [hd, mul_pow]
    rw [integral_mul_const, ← hmap, integral_map (φ := fun x : ℝ => c * x) (f := fun x => (deriv f
        x) ^ 2) (by fun_prop)
      ((hf.continuous_deriv (by norm_num)).pow 2).aestronglyMeasurable]
    ring
  rw [hent]
  have h := gaussianReal_lsi_C2 F hF hFc
  rw [he] at h
  simpa only [mul_assoc] using h

/-- Sharp Gaussian LSI for every variance, including the degenerate zero law. -/
theorem gaussianReal_lsi_variance (v : ℝ≥0) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    squareEntropy (gaussianReal 0 v) f ≤
      (2 * (v : ℝ)) * ∫ x, (deriv f x) ^ 2 ∂gaussianReal 0 v := by
  by_cases hv : v = 0
  · subst v
    simp [gaussianReal_zero_var, squareEntropy]
  · let c := Real.sqrt (v : ℝ)
    have hcp : 0 < c := Real.sqrt_pos.mpr (by exact_mod_cast (pos_iff_ne_zero.mpr hv))
    have he : (⟨c ^ 2, sq_nonneg c⟩ : ℝ≥0) = v := by
      apply Subtype.ext
      exact Real.sq_sqrt v.coe_nonneg
    have h := gaussianReal_lsi_dilation c hcp.ne' f hf hc
    rw [he] at h
    simpa only [c, Real.sq_sqrt v.coe_nonneg] using h

/-- A compact C² LSI under any probability law extends to its actual weighted
value-derivative completion. The core bound is explicit in this reusable lemma. -/
theorem weightedH1Completion_lsi_of_C2 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (c : ℝ)
    (hcore : ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      squareEntropy μ f ≤ c * ∫ x, (deriv f x) ^ 2 ∂μ) :
    ∀ p ∈ closure (compactC1SobolevPairs μ),
      Integrable (fun x => p.1 x ^ 2 * Real.log (p.1 x ^ 2)) μ ∧
        squareEntropy μ p.1 ≤ c * ‖p.2‖ ^ 2 := by
  rw [closure_compactC1SobolevPairs_eq_C2]
  apply entropy_bound_on_closure
  intro p hp
  obtain ⟨f, hf, hc, hv, hd⟩ := hp
  constructor
  · apply ((continuous_square_mul_log hf.continuous).integrable_of_hasCompactSupport
      (μ := μ) (compactSupport_square_mul_log hc)).congr
    filter_upwards [hv] with x hx
    simp [hx]
  · rw [squareEntropy_congr_ae _ hv, ← integral_square_eq_L2_norm_sq]
    have he : (∫ x, p.2 x ^ 2 ∂μ) = ∫ x, (deriv f x) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hd] with x hx
      simp [hx]
    rw [he]
    exact hcore f hf hc

/-- The sharp inequality on the weighted Gaussian H¹ completion for any variance.
The completion is in the product of the actual value and derivative L² spaces. -/
theorem gaussianReal_lsi_variance_H1Completion (v : ℝ≥0) :
    ∀ p ∈ closure (compactC1SobolevPairs (gaussianReal 0 v)),
      Integrable (fun x => p.1 x ^ 2 * Real.log (p.1 x ^ 2)) (gaussianReal 0 v) ∧
        squareEntropy (gaussianReal 0 v) p.1 ≤ (2 * (v : ℝ)) * ‖p.2‖ ^ 2 :=
  weightedH1Completion_lsi_of_C2 _ _ (gaussianReal_lsi_variance v)

/-- Finite-energy C¹ observables satisfy the sharp LSI at every variance,
without compact support and without a separate logarithmic-integrability premise. -/
theorem gaussianReal_lsi_variance_C1 (v : ℝ≥0) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (hv : MemLp f 2 (gaussianReal 0 v))
    (hd : MemLp (deriv f) 2 (gaussianReal 0 v)) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) (gaussianReal 0 v) ∧
      squareEntropy (gaussianReal 0 v) f ≤
        (2 * (v : ℝ)) * ∫ x, (deriv f x) ^ 2 ∂gaussianReal 0 v := by
  have h := gaussianReal_lsi_variance_H1Completion v (hv.toLp f, hd.toLp (deriv f))
    (C1_pair_mem_sobolev_completion _ f hf hv hd)
  constructor
  · apply h.1.congr
    filter_upwards [hv.coeFn_toLp] with x hx
    simp [hx]
  · have he := h.2
    rw [squareEntropy_congr_ae _ hv.coeFn_toLp, ← integral_square_eq_L2_norm_sq] at he
    have he' : (∫ x, (hd.toLp (deriv f)) x ^ 2 ∂gaussianReal 0 v) =
        ∫ x, (deriv f x) ^ 2 ∂gaussianReal 0 v := by
      apply integral_congr_ae
      filter_upwards [hd.coeFn_toLp] with x hx
      simp [hx]
    rw [he'] at he
    exact he

end
end GinibrePoincare
