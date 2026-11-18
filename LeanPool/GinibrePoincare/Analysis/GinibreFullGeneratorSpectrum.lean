/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-poincare.

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

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorComplexification

/-! # Positivity and spectrum of the symmetric Ginibre resolvent -/

@[expose] public section

namespace GinibrePoincare
noncomputable section

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A positive Hilbert-space contraction has real spectrum in the unit interval. -/
theorem ginibreFull_positive_contraction_spectrum (R : H →L[ℂ] H)
    (hp : R.IsPositive) (hnorm : ‖R‖ ≤ 1) : spectrum ℝ R ⊆ Set.Icc 0 1 := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · let := hH
    rw [spectrum.of_subsingleton]
    exact Set.empty_subset _
  let := hH
  intro r hr
  have hpos : 0 ≤ R := ContinuousLinearMap.nonneg_iff_isPositive.mpr hp
  exact ⟨spectrum_nonneg_of_nonneg hpos hr,
    (Real.le_norm_self r).trans ((spectrum.norm_le_norm_of_mem hr).trans hnorm)⟩

end

/-- The actual full symmetric resolvent contracts the original real L² norm. -/
theorem ginibreFullSymmetricResolvent_norm_le (n : ℕ) (hn : 0 < n)
    (f : ginibreFullSymmetricValues n) : ‖ginibreFullSymmetricResolvent n hn f‖ ≤ ‖f‖ :=
  (WithLp.norm_fst_le (α := GinibreFullValueL2 n) (β := GinibreFullGradientL2 n)
    (ginibreFullFormResolvent n hn f.val).val).trans (ginibreFullFormResolvent_norm_le n hn f.val)

/-- The complex extension contracts the original complex Ginibre L² norm. -/
theorem ginibreFullComplexResolvent_norm_le (n : ℕ) (hn : 0 < n)
    (f : ginibreSymmetricL2 n) : ‖ginibreFullComplexResolvent n hn f‖ ≤ ‖f‖ := by
  have hr := ginibreFullComplex_norm_sq n (ginibreFullComplexResolvent n hn f).val
  have hf := ginibreFullComplex_norm_sq n f.val
  change ‖ginibreFullComplexResolvent n hn f‖ ^ 2 =
    ‖ginibreFullSymmetricRe n (ginibreFullComplexResolvent n hn f)‖ ^ 2 +
      ‖ginibreFullSymmetricIm n (ginibreFullComplexResolvent n hn f)‖ ^ 2 at hr
  change ‖f‖ ^ 2 = ‖ginibreFullSymmetricRe n f‖ ^ 2 + ‖ginibreFullSymmetricIm n f‖ ^ 2 at hf
  rw [ginibreFullComplexResolvent_re, ginibreFullComplexResolvent_im] at hr
  have hRe := ginibreFullSymmetricResolvent_norm_le n hn (ginibreFullSymmetricRe n f)
  have hIm := ginibreFullSymmetricResolvent_norm_le n hn (ginibreFullSymmetricIm n f)
  have hReSq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hRe
  have hImSq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hIm
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hr, hf]
  exact add_le_add hReSq hImSq

theorem ginibreFullComplexResolvent_opNorm_le (n : ℕ) (hn : 0 < n) :
    ‖ginibreFullComplexResolvent n hn‖ ≤ 1 :=
  (ginibreFullComplexResolvent n hn).opNorm_le_bound (by norm_num) (by
    intro f
    simpa using ginibreFullComplexResolvent_norm_le n hn f)

/-- Positivity is inherited from the two genuine real Dirichlet resolvents. -/
theorem ginibreFullComplexResolvent_inner_nonneg (n : ℕ) (hn : 0 < n)
    (f : ginibreSymmetricL2 n) : 0 ≤ (inner ℂ f (ginibreFullComplexResolvent n hn f)).re := by
  rw [ginibreFullSymmetric_inner_re, ginibreFullComplexResolvent_re, ginibreFullComplexResolvent_im]
  have hR := ginibreFullValueResolvent_positive n hn (ginibreFullSymmetricRe n f).val
  have hI := ginibreFullValueResolvent_positive n hn (ginibreFullSymmetricIm n f).val
  change 0 ≤ inner ℝ (ginibreFullSymmetricRe n f).val
      (ginibreFullValueResolvent n hn (ginibreFullSymmetricRe n f).val) +
    inner ℝ (ginibreFullSymmetricIm n f).val
      (ginibreFullValueResolvent n hn (ginibreFullSymmetricIm n f).val)
  rw [hR, hI]
  positivity

theorem ginibreFullComplexResolvent_isPositive (n : ℕ) (hn : 0 < n) :
    (ginibreFullComplexResolvent n hn).IsPositive := by
  refine ⟨ginibreFullComplexResolvent_symmetric n hn, ?_⟩
  intro f
  change 0 ≤ (inner ℂ (ginibreFullComplexResolvent n hn f) f).re
  have h := inner_re_symm (𝕜 := ℂ) (ginibreFullComplexResolvent n hn f) f
  change (inner ℂ (ginibreFullComplexResolvent n hn f) f).re =
    (inner ℂ f (ginibreFullComplexResolvent n hn f)).re at h
  rw [h]
  exact ginibreFullComplexResolvent_inner_nonneg n hn f

/-- The spectrum of the actual full symmetric resolvent lies in `[0,1]`. -/
theorem ginibreFullComplexResolvent_spectrum (n : ℕ) (hn : 0 < n) :
    spectrum ℝ (ginibreFullComplexResolvent n hn) ⊆ Set.Icc 0 1 :=
  ginibreFull_positive_contraction_spectrum (ginibreFullComplexResolvent n hn)
    (ginibreFullComplexResolvent_isPositive n hn) (ginibreFullComplexResolvent_opNorm_le n hn)

end
end GinibrePoincare
