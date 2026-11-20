/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUEPaperH1.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEOptimality
/-!
# Correspondence GUE paper H 1

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `guePaperH1Completion_poincare`, `guePaperH1Completion_square_lsi`,
`guePaper_poincare_constant_optimal`, `guePaper_lsi_constant_optimal`.
-/

@[expose] public section
open MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators
namespace GinibrePoincare
noncomputable section

/-- Paper Section 1.1's smooth compact symmetric value/ordinary-gradient core,
for the actual real GUE density of Section 1.2. -/
def guePaperSmoothPairs (n : ℕ) : Set (GUEFullSobolevPair n) :=
  {p | ∃f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    (∀σ x, f (guePermute n σ x)=f x) ∧
    (p.1 : EuclideanSpace ℝ (Fin n) → ℝ)=ᵐ[gueFullMeasure n]f ∧
    (p.2 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))=ᵐ[gueFullMeasure n]gradient f}

/-- The paper's `H¹` space for `gueFullMeasure n`: the closure of `guePaperSmoothPairs n`. -/
def guePaperH1Completion (n : ℕ) : Set (GUEFullSobolevPair n) := closure (guePaperSmoothPairs n)

theorem guePaperH1Completion_subset (n : ℕ) : guePaperH1Completion n⊆gueSymmetricH1Completion n :=
    by
  apply closure_mono
  rintro p ⟨f, hf, hc, hs, hv, hg⟩
  exact ⟨f, hf.of_le (by simp), hc, hs, hv, hg⟩

theorem guePaperH1Completion_poincare {n : ℕ} (hn : 0 < n)
    (p : GUEFullSobolevPair n) (hp : p ∈ guePaperH1Completion n) :
    (∫x, p.1 x^2 ∂gueFullMeasure n)-(∫x, p.1 x ∂gueFullMeasure n)^2≤(1/(n : ℝ))*‖p.2‖^2 :=
  gueSymmetricH1Completion_poincare hn p (guePaperH1Completion_subset n hp)

theorem guePaperH1Completion_square_lsi {n : ℕ} (hn : 0 < n)
    (p : GUEFullSobolevPair n) (hp : p ∈ guePaperH1Completion n) :
    Integrable (fun x => p.1 x^2*Real.log (p.1 x^2)) (gueFullMeasure n) ∧
      squareEntropy (gueFullMeasure n) p.1≤(2/(n : ℝ))*‖p.2‖^2 :=
  gueSymmetricH1Completion_square_lsi hn p (guePaperH1Completion_subset n hp)

theorem gueSymmetric_smooth_pair_mem_paperH1 {n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hs : ∀ σ x, f (guePermute n σ x) = f x)
    (hv : MemLp f 2 (gueFullMeasure n))
    (hg : MemLp (gradient f) 2 (gueFullMeasure n)) :
    (hv.toLp f, hg.toLp (gradient f))∈guePaperH1Completion n := by
  refine gueSymmetric_C1_pair_mem_closure hn f (hf.of_le (by simp)) hv hg
    (guePaperSmoothPairs n) ?_
  intro k hV hG
  refine ⟨gueSymmetricSpatialTruncation n k f, ?_, gueSymmetricSpatialTruncation_compact n k f,
    ?_, hV.coeFn_toLp, hG.coeFn_toLp⟩
  · unfold gueSymmetricSpatialTruncation
    exact (gueSymmetricSpatialCutoff_smooth n k).mul hf
  · intro σ x
    unfold gueSymmetricSpatialTruncation
    rw [gueSymmetricSpatialCutoff_symmetric, hs]

theorem guePaper_center_witness_mem_H1 {n : ℕ} (hn : 0 < n) :
    ((gueCenterCoordinate_memLp hn).toLp (gueCenterCoordinate n),
      (gueCenterCoordinate_gradient_memLp hn).toLp (gradient (gueCenterCoordinate
          n)))∈guePaperH1Completion n :=
  gueSymmetric_smooth_pair_mem_paperH1 hn _ (gueCenterCoordinate_contDiff n)
    (gueCenterCoordinate_symmetric n) (gueCenterCoordinate_memLp hn)
        (gueCenterCoordinate_gradient_memLp hn)

theorem guePaper_lsi_witness_mem_H1 {n : ℕ} (hn : 0 < n) :
    ((gueLSIWitness_memLp hn).toLp (gueLSIWitness n),
      (gueLSIWitness_gradient_memLp hn).toLp (gradient (gueLSIWitness n)))∈guePaperH1Completion n :=
  gueSymmetric_smooth_pair_mem_paperH1 hn _ (gueLSIWitness_contDiff n)
    (gueLSIWitness_symmetric n) (gueLSIWitness_memLp hn) (gueLSIWitness_gradient_memLp hn)

theorem guePaper_poincare_constant_optimal {n : ℕ} (hn : 0 < n) (c : ℝ)
    (hc : ∀ p ∈ guePaperH1Completion n,
      (∫ x, p.1 x ^ 2 ∂gueFullMeasure n) - (∫ x, p.1 x ∂gueFullMeasure n) ^ 2 ≤ c * ‖p.2‖ ^ 2) :
    1/(n : ℝ)≤c := by
  let := gueFullMeasure_probability hn
  let hv := gueCenterCoordinate_memLp hn
  let hg := gueCenterCoordinate_gradient_memLp hn
  have h := hc (hv.toLp (gueCenterCoordinate n), hg.toLp (gradient (gueCenterCoordinate n)))
    (guePaper_center_witness_mem_H1 hn)
  have he : ‖hg.toLp (gradient (gueCenterCoordinate n))‖^2=
      (∫x, ‖gradient (gueCenterCoordinate n) x‖^2 ∂gueFullMeasure n) := by
    rw [← integral_norm_sq_eq_L2_norm_sq]
    exact integral_congr_ae (hg.coeFn_toLp.fun_comp (fun y => ‖y‖^2))
  have hsq : (∫x, (hv.toLp (gueCenterCoordinate n)) x^2 ∂gueFullMeasure n)=
      (∫x, gueCenterCoordinate n x^2 ∂gueFullMeasure n) := by
    apply integral_congr_ae
    filter_upwards [hv.coeFn_toLp] with x hx
    rw [hx]
  rw [hsq, integral_congr_ae hv.coeFn_toLp, he, gueCenterCoordinate_poincare_equality hn] at h
  simpa only [gueCenterCoordinate_gradient, gueCenterUnit_norm hn, one_pow, integral_const,
    probReal_univ, smul_eq_mul, mul_one] using h

theorem guePaper_lsi_constant_optimal {n : ℕ} (hn : 0 < n) (c : ℝ)
    (hc : ∀ p ∈ guePaperH1Completion n, squareEntropy (gueFullMeasure n) p.1 ≤ c * ‖p.2‖ ^ 2) :
    2/(n : ℝ)≤c := by
  let hv := gueLSIWitness_memLp hn
  let hg := gueLSIWitness_gradient_memLp hn
  have h := hc (hv.toLp (gueLSIWitness n), hg.toLp (gradient (gueLSIWitness n)))
    (guePaper_lsi_witness_mem_H1 hn)
  have he : ‖hg.toLp (gradient (gueLSIWitness n))‖^2=
      (∫x, ‖gradient (gueLSIWitness n) x‖^2 ∂gueFullMeasure n) := by
    rw [← integral_norm_sq_eq_L2_norm_sq]
    exact integral_congr_ae (hg.coeFn_toLp.fun_comp (fun y => ‖y‖^2))
  rw [squareEntropy_congr_ae _ hv.coeFn_toLp, he, gueLSIWitness_lsi_equality hn,
    gueLSIWitness_gradient_energy hn] at h
  exact (mul_le_mul_iff_left₀ (by positivity : 0<(1/4 : ℝ)*Real.exp ((gueCenterVariance n :
                                    ℝ)/2))).mp h

end
end GinibrePoincare
