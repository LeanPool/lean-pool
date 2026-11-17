/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreValueTruncationL2.lean.
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

public import LeanPool.GinibrePoincare.Analysis.SobolevValueTruncation
public import LeanPool.GinibrePoincare.Analysis.GinibreWeakSobolevTruncation

/-! # Weighted L² limits of concrete nonlinear value truncations

The proposed chain-rule vector is defined and converges for every actual L²
value-gradient pair. This module does not assert a distributional chain rule
for nonsmooth weak values; that rule remains a separate analytic obligation.
-/


@[expose] public section


open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- Nonlinear value truncation preserves actual Ginibre L². -/
theorem ginibreValueTruncation_memLp (n m : ℕ) (f : Configuration n → ℝ)
    (hf : MemLp f 2 (ginibreMeasure n)) :
    MemLp (fun z => sobolevValueTruncation m (f z)) 2 (ginibreMeasure n) := by
  apply hf.of_le ((sobolevValueTruncation_smooth m).continuous.comp_aestronglyMeasurable
    hf.aestronglyMeasurable)
  exact ae_of_all _ (fun z => sobolevValueTruncation_norm_le m (f z))

/-- The actual chain-rule expression is square integrable; boundedness of the
original value is not required. -/
theorem ginibreValueTruncation_vector_memLp {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (n m : ℕ) (f : Configuration n → ℝ)
    (hf : AEStronglyMeasurable f (ginibreMeasure n)) (g : Configuration n → V)
    (hg : MemLp g 2 (ginibreMeasure n)) :
    MemLp (fun z => deriv (sobolevValueTruncation m) (f z) • g z) 2 (ginibreMeasure n) := by
  obtain ⟨B, hB0, hB⟩ := sobolevValueTruncation_deriv_bound
  apply (hg.const_smul B).of_le
    ((((sobolevValueTruncation_smooth m).continuous_deriv (by simp)).comp_aestronglyMeasurable
      hf).smul hg.aestronglyMeasurable)
  apply ae_of_all
  intro z
  change ‖deriv (sobolevValueTruncation m) (f z) • g z‖ ≤ ‖B • g z‖
  rw [norm_smul, norm_smul, Real.norm_eq_abs B, abs_of_nonneg hB0]
  exact mul_le_mul_of_nonneg_right (hB m (f z)) (norm_nonneg _)

/-- Squared weighted value errors converge to zero for every L² value. -/
theorem ginibreValueTruncation_value_error_tendsto (n : ℕ)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (ginibreMeasure n)) :
    Tendsto (fun m => ∫ z, ‖sobolevValueTruncation m (f z) - f z‖ ^ 2
      ∂ginibreMeasure n) atTop (𝓝 0) := by
  have hb (m : ℕ) (z : Configuration n) :
      ‖sobolevValueTruncation m (f z) - f z‖ ^ 2 ≤ ‖f z‖ ^ 2 := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    have he : (sobolevValueTruncation m (f z) - f z) ^ 2 =
        (sobolevCutoff m (f z) - 1) ^ 2 * f z ^ 2 := by unfold sobolevValueTruncation; ring
    rw [he]
    obtain ⟨h0, h1⟩ := sobolevCutoff_mem_unit m (f z)
    have hh : (sobolevCutoff m (f z) - 1) ^ 2 ≤ 1 := by nlinarith
    simpa using mul_le_mul_of_nonneg_right hh (sq_nonneg (f z))
  have ht := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
    (fun z => ‖f z‖ ^ 2)
    (fun m => (((sobolevValueTruncation_smooth m).continuous.comp_aestronglyMeasurable
      hf.aestronglyMeasurable).sub hf.aestronglyMeasurable).norm.pow 2)
    ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf)
    (fun m => ae_of_all _ (fun z => by
      change ‖‖sobolevValueTruncation m (f z) - f z‖ ^ 2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hb m z))
    (ae_of_all _ (fun z => by
      simpa using (((sobolevValueTruncation_tendsto (f z)).1).sub_const (f z)).norm.pow 2))
  simpa using ht

/-- Squared weighted errors of the actual chain-rule expression tend to zero,
for arbitrary square-integrable vectors and values. -/
theorem ginibreValueTruncation_vector_error_tendsto {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (n : ℕ) (f : Configuration n → ℝ)
    (hf : AEStronglyMeasurable f (ginibreMeasure n)) (g : Configuration n → V)
    (hg : MemLp g 2 (ginibreMeasure n)) :
    Tendsto (fun m => ∫ z, ‖deriv (sobolevValueTruncation m) (f z) • g z - g z‖ ^ 2
      ∂ginibreMeasure n) atTop (𝓝 0) := by
  obtain ⟨B, hB0, hB⟩ := sobolevValueTruncation_deriv_bound
  have hb (m : ℕ) (z : Configuration n) :
      ‖deriv (sobolevValueTruncation m) (f z) • g z - g z‖ ^ 2 ≤
      (B + 1) ^ 2 * ‖g z‖ ^ 2 := by
    have he : deriv (sobolevValueTruncation m) (f z) • g z - g z =
        (deriv (sobolevValueTruncation m) (f z) - 1) • g z := by rw [sub_smul, one_smul]
    rw [he, norm_smul, mul_pow]
    have hnorm : ‖deriv (sobolevValueTruncation m) (f z) - 1‖ ≤ B + 1 := by
      have he : ‖deriv (sobolevValueTruncation m) (f z)‖ + ‖(1 : ℝ)‖ ≤ B + 1 := by
        simpa only [norm_one] using add_le_add (hB m (f z)) (le_refl (1 : ℝ))
      exact (norm_sub_le _ (1 : ℝ)).trans he
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    nlinarith [norm_nonneg (deriv (sobolevValueTruncation m) (f z) - 1)]
  have hi := ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg).const_mul ((B + 1)
    ^ 2)
  have ht := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
    (fun z => (B + 1) ^ 2 * ‖g z‖ ^ 2)
    (fun m => (((((sobolevValueTruncation_smooth m).continuous_deriv (by
      simp)).comp_aestronglyMeasurable hf).smul hg.aestronglyMeasurable).sub
      hg.aestronglyMeasurable).norm.pow 2)
    hi
    (fun m => ae_of_all _ (fun z => by
      change ‖‖deriv (sobolevValueTruncation m) (f z) • g z - g z‖ ^ 2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hb m z))
    (ae_of_all _ (fun z => by
      simpa using ((((sobolevValueTruncation_tendsto (f z)).2).smul_const (g z)).sub_const (g
        z)).norm.pow 2))
  simpa using ht

/-- Actual value truncation classes converge in Ginibre L². -/
theorem ginibreValueTruncation_L2_tendsto (n : ℕ) (u : Lp ℝ 2 (ginibreMeasure n)) :
    Tendsto (fun m => (ginibreValueTruncation_memLp n m u (Lp.memLp u)).toLp
      (fun z => sobolevValueTruncation m (u z))) atTop (𝓝 u) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have he (m : ℕ) : dist ((ginibreValueTruncation_memLp n m u (Lp.memLp u)).toLp
      (fun z => sobolevValueTruncation m (u z))) u =
      Real.sqrt (∫ z, ‖sobolevValueTruncation m (u z) - u z‖ ^ 2 ∂ginibreMeasure n) := by
    rw [L2_dist_eq_sqrt_integral_norm_error]
    congr 1
    apply integral_congr_ae
    filter_upwards [(ginibreValueTruncation_memLp n m u (Lp.memLp u)).coeFn_toLp] with z hz
    rw [hz]
  simp_rw [he]
  simpa using (ginibreValueTruncation_value_error_tendsto n u (Lp.memLp u)).sqrt

/-- Actual chain-rule expression classes converge in vector Ginibre L². This
is an analytic convergence theorem, not yet a weak chain-rule theorem. -/
theorem ginibreValueTruncation_vector_L2_tendsto {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (n : ℕ) (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp V 2 (ginibreMeasure n)) :
    Tendsto (fun m => (ginibreValueTruncation_vector_memLp n m u (Lp.aestronglyMeasurable u) g
      (Lp.memLp g)).toLp (fun z => deriv (sobolevValueTruncation m) (u z) • g z))
      atTop (𝓝 g) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have he (m : ℕ) : dist ((ginibreValueTruncation_vector_memLp n m u (Lp.aestronglyMeasurable u) g
      (Lp.memLp g)).toLp (fun z => deriv (sobolevValueTruncation m) (u z) • g z)) g =
      Real.sqrt (∫ z, ‖deriv (sobolevValueTruncation m) (u z) • g z - g z‖ ^ 2 ∂ginibreMeasure n)
        := by
    rw [L2_dist_eq_sqrt_integral_norm_error]
    congr 1
    apply integral_congr_ae
    filter_upwards [(ginibreValueTruncation_vector_memLp n m u (Lp.aestronglyMeasurable u) g
      (Lp.memLp g)).coeFn_toLp] with z hz
    rw [hz]
  simp_rw [he]
  simpa using (ginibreValueTruncation_vector_error_tendsto n u (Lp.aestronglyMeasurable u) g
    (Lp.memLp g)).sqrt

/-- Classical smooth values satisfy the actual Euclidean chain rule for these
nonlinear truncations. -/
theorem ginibreValueTruncation_smooth_gradient (n m : ℕ) (f : Configuration n → ℝ)
    (hf : ContDiff ℝ ∞ f) (z : Configuration n) :
    ginibreEuclideanGradient (fun w => sobolevValueTruncation m (f w)) z =
      deriv (sobolevValueTruncation m) (f z) • ginibreEuclideanGradient f z := by
  have hd := (((sobolevValueTruncation_smooth m).differentiable (by simp) (f
    z)).hasDerivAt).comp_hasFDerivAt z
    ((hf.differentiable (by simp) z).hasFDerivAt)
  ext k
  simp only [ginibreEuclideanGradient, PiLp.smul_apply]
  have hd' : fderiv ℝ (fun w => sobolevValueTruncation m (f w)) z =
      deriv (sobolevValueTruncation m) (f z) • fderiv ℝ f z := hd.fderiv
  rw [hd']
  by_cases hk : k.2 = 0 <;> simp [hk]
/-- Value truncation preserves permutation symmetry pointwise. -/
theorem ginibreValueTruncation_symmetric (n m : ℕ) (f : Configuration n → ℝ)
    (hs : IsSymmetric f) : IsSymmetric (fun z => sobolevValueTruncation m (f z)) := by
  intro σ z
  change sobolevValueTruncation m (f (permute σ z)) = sobolevValueTruncation m (f z)
  rw [hs σ z]

/-- Value truncation preserves individual-radius radiality pointwise. -/
theorem ginibreValueTruncation_radial (n m : ℕ) (f : Configuration n → ℝ)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    ∃ F : (Fin n → ℝ) → ℝ, ∀ z,
      sobolevValueTruncation m (f z) = F (fun i => Complex.normSq (z i)) := by
  obtain ⟨F, hF⟩ := hr
  exact ⟨fun r => sobolevValueTruncation m (F r), fun z => by rw [hF]⟩

/-- The concrete bounded value truncation does not enlarge spatial support. -/
theorem ginibreValueTruncation_support_subset (n m : ℕ) (f : Configuration n → ℝ) :
    tsupport (fun z => sobolevValueTruncation m (f z)) ⊆ tsupport f := by
  apply closure_mono
  intro z hz
  by_contra hf
  have he : f z = 0 := by simpa only [Function.mem_support, not_not] using hf
  exact hz (by simp only [he, sobolevValueTruncation_zero])
end
end GinibrePoincare
