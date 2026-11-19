/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/PairwiseRadius.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreRadialGamma

/-!
# Pairwise radius

Part of the polynomial, radial and equilibrium sectors development of the
Ginibre Poincaré formalization.

Main results: `pairwiseRadius_permute`, `pairwiseRadius_ginibre_gamma`,
`coordinateSum_pairwiseRadius_indepFun`.
-/

@[expose] public section

open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- The paper's radial observable, expressed using unordered particle pairs. -/
def pairwiseRadius {n : ℕ} (z : Configuration n) : ℝ :=
  ∑ j : Fin n, ∑ k ∈ Finset.Ioi j, Complex.normSq (z j - z k)

/-- The squared modulus `Complex.normSq (coordinateSum z)` of the sum of the particle
positions. -/
def ginibreCenterSquared (n : ℕ) (z : Configuration n) : ℝ := Complex.normSq (coordinateSum z)

private theorem normSq_sub_symm (a b : ℂ) :
    Complex.normSq (a - b) = Complex.normSq (b - a) := by
  rw [show a - b = -(b - a) by ring, Complex.normSq_neg]

private theorem double_sum_pairwise {n : ℕ} (z : Configuration n) :
    (∑ j : Fin n, ∑ k : Fin n, Complex.normSq (z j - z k)) =
      2 * pairwiseRadius z := by
  have hio (j : Fin n) : Finset.Ioi j = Finset.univ.filter (fun k => j < k) := by
    ext k; simp
  have hii (j : Fin n) : Finset.Iio j = Finset.univ.filter (fun k => k < j) := by
    ext k; simp
  have hsplit (j : Fin n) :
      (∑ k : Fin n, Complex.normSq (z j - z k)) =
        (∑ k ∈ Finset.Ioi j, Complex.normSq (z j - z k)) +
        ∑ k ∈ Finset.Iio j, Complex.normSq (z j - z k) := by
    rw [hio, hii]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => j < k)]
    apply congrArg (fun t : ℝ => (∑ k with j < k, Complex.normSq (z j - z k)) + t)
    apply Eq.symm
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      simpa using hk.le
    · intro k hk hk'
      have he : k = j := by simp_all; omega
      subst k
      simp
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  have heq : (∑ j : Fin n, ∑ k ∈ Finset.Iio j, Complex.normSq (z j - z k)) =
      pairwiseRadius z := by
    simp only [hii, hio, pairwiseRadius]
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [normSq_sub_symm]
  rw [heq]
  unfold pairwiseRadius
  ring

/-- Pair-distance radius in terms of the unrecentered quadratic norm. -/
theorem pairwiseRadius_eq_normSq {n : ℕ} (z : Configuration n) :
    pairwiseRadius z = n * configurationNormSq z - Complex.normSq (coordinateSum z) := by
  have hd := double_sum_pairwise z
  have hexp : (∑ j : Fin n, ∑ k : Fin n, Complex.normSq (z j - z k)) =
      2 * ((n : ℝ) * configurationNormSq z - Complex.normSq (coordinateSum z)) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      coordinateSum, Complex.re_sum, Complex.im_sum, configurationNormSq]
    simp only [← sq]
    simp_rw [sub_sq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  linarith

/-- The unordered-pair radius is exactly the centered radius used by the Gamma law. -/
theorem pairwiseRadius_eq_radialObservable {n : ℕ} (z : Configuration n) :
    pairwiseRadius z = radialObservable n z := by
  rw [pairwiseRadius_eq_normSq]
  by_cases hn : n = 0
  · subst n
    simp [coordinateSum, radialObservable, recenteredSqNorm, configurationNormSq]
  · have hp := pythagorean_identity n z
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    unfold radialObservable
    unfold centerOfMassSqNorm at hp
    field_simp at hp
    nlinarith

/-- The pair-distance observable is symmetric under particle relabeling. -/
theorem pairwiseRadius_permute {n : ℕ} (σ : ParticlePermutation n) (z : Configuration n) :
    pairwiseRadius (permute σ z) = pairwiseRadius z := by
  have hnorm : configurationNormSq (permute σ z) = configurationNormSq z := by
    simpa [configurationNormSq, permute] using
      (Equiv.sum_comp σ (fun j => Complex.normSq (z j)))
  simp only [pairwiseRadius_eq_normSq, hnorm, coordinateSum_permute]

/-- The actual unordered-pair radius has the paper's Gamma law. -/
theorem pairwiseRadius_ginibre_gamma (n : ℕ) (hn : 2 ≤ n) :
    (ginibreMeasure n).map (pairwiseRadius : Configuration n → ℝ) =
      ProbabilityTheory.gammaMeasure (((n : ℝ) - 1) * ((n : ℝ) + 2) / 2) 1 := by
  have heq : (pairwiseRadius : Configuration n → ℝ) = radialObservable n := by
    funext z; exact pairwiseRadius_eq_radialObservable z
  rw [heq]
  exact radialObservable_ginibre_gamma n hn

/-- Independence of the Gaussian sum and the actual unordered-pair radius. -/
theorem coordinateSum_pairwiseRadius_indepFun (n : ℕ) (hn : 0 < n) :
    ProbabilityTheory.IndepFun (coordinateSum : Configuration n → ℂ)
      (pairwiseRadius : Configuration n → ℝ) (ginibreMeasure n) := by
  have heq : (pairwiseRadius : Configuration n → ℝ) =
      (fun w : Configuration n => (n : ℝ) * configurationNormSq w) ∘ recenteredConfiguration n := by
    funext z
    exact pairwiseRadius_eq_radialObservable z
  rw [heq]
  exact (coordinateSum_recentered_indepFun n hn).comp measurable_id (by
    unfold configurationNormSq
    fun_prop)

end
end GinibrePoincare
