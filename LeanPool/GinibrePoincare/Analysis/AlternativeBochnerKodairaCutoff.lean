/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBochnerKodairaCutoff.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeBochnerKodairaClosure
public import LeanPool.GinibrePoincare.Analysis.GaussianDbarCompactCore

/-!
# Alternative Bochner Kodaira cutoff

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `bkCutoff_second_derivative_tendsto`, `bkAdjoint_cutoff_product`,
`bkCutoff_product_second`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped ContDiff ComplexConjugate BigOperators Topology
namespace GinibrePoincare
noncomputable section

theorem bkCutoff_second_derivative (m : ℕ) (x : ℝ) :
    deriv (deriv (sobolevCutoff m)) x =
      deriv (deriv (sobolevCutoffBump : ℝ → ℝ)) (x / ((m : ℝ) + 1)) /
        ((m : ℝ) + 1) ^ 2 := by
  have hb : ContDiff ℝ ∞ (deriv (sobolevCutoffBump : ℝ → ℝ)) :=
    (show ContDiff ℝ ((∞ : ℕ∞ω) + 1) (sobolevCutoffBump : ℝ → ℝ) by
      simpa using
        (sobolevCutoffBump.contDiff : ContDiff ℝ ∞ (sobolevCutoffBump : ℝ → ℝ))).deriv'
  have h := (hb.differentiable (by simp) (x / ((m : ℝ) + 1))).hasDerivAt
    |>.comp x ((hasDerivAt_id x).div_const ((m : ℝ) + 1))
    |>.div_const ((m : ℝ) + 1)
  rw [show deriv (sobolevCutoff m) = fun x =>
    deriv (sobolevCutoffBump : ℝ → ℝ) (x / ((m : ℝ) + 1)) / ((m : ℝ) + 1) by
    funext x; exact sobolevCutoff_deriv m x]
  have he := h.deriv
  change deriv (fun x => deriv (sobolevCutoffBump : ℝ → ℝ) (x / ((m : ℝ) + 1)) / ((m : ℝ) + 1)) x =
      _ at he
  rw [he]
  field_simp

theorem bkCutoff_second_derivative_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ m x,
    |deriv (deriv (sobolevCutoff m)) x| ≤ M / ((m : ℝ) + 1) ^ 2 := by
  have hb : ContDiff ℝ ∞ (deriv (sobolevCutoffBump : ℝ → ℝ)) :=
    (show ContDiff ℝ ((∞ : ℕ∞ω) + 1) (sobolevCutoffBump : ℝ → ℝ) by
      simpa using
        (sobolevCutoffBump.contDiff : ContDiff ℝ ∞ (sobolevCutoffBump : ℝ → ℝ))).deriv'
  obtain ⟨M, hM⟩ := (hb.continuous_deriv (by simp)).bounded_above_of_compact_support
    sobolevCutoffBump.hasCompactSupport.deriv.deriv
  refine ⟨M, (norm_nonneg _).trans (hM 0), ?_⟩
  intro m x
  rw [bkCutoff_second_derivative, abs_div, abs_of_pos (by positivity : 0 < ((m : ℝ) + 1) ^ 2)]
  exact div_le_div_of_nonneg_right (by simpa [Real.norm_eq_abs] using hM _) (by positivity)

theorem bkCutoff_second_derivative_tendsto (x : ℝ) :
    Tendsto (fun m => deriv (deriv (sobolevCutoff m)) x) atTop (𝓝 0) := by
  obtain ⟨M, hM0, hM⟩ := bkCutoff_second_derivative_bound
  have hi : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1 : ℝ)
      tendsto_natCast_atTop_atTop)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun m => by simpa using hM m x)
  simpa [div_eq_mul_inv, inv_pow] using (hi.pow 2).const_mul M

/-- The radial chain rule for the actual antiholomorphic derivative. -/
theorem bkRadial_dbar (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) {n : ℕ}
    (j : Fin n) (z : Configuration n) :
    dbarComponent (fun w => (g (configurationNormSq w) : ℂ)) j z =
      ((deriv g (configurationNormSq z) : ℝ) : ℂ) * z j := by
  have hq := (contDiff_configurationNormSq.differentiable (by simp)).differentiableAt (x := z)
  have hb := (hg.differentiable (by simp) (configurationNormSq z)).hasDerivAt
  have hd := Complex.ofRealCLM.hasFDerivAt.comp z (hb.comp_hasFDerivAt z hq.hasFDerivAt)
  change HasFDerivAt (fun w => (g (configurationNormSq w) : ℂ)) _ z at hd
  unfold dbarComponent
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    smul_apply, smul_eq_mul]
  rw [fderiv_configurationNormSq_apply, fderiv_configurationNormSq_apply]
  have hr : (∑ x : Fin n, (conj (z x) * realCoordinateDirection j x).re) = (z j).re := by
    simp only [realCoordinateDirection, coordinateDirection]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj; simp [hbj]
    · simp
  have hi : (∑ x : Fin n, (conj (z x) * imaginaryCoordinateDirection j x).re) = (z j).im := by
    simp only [imaginaryCoordinateDirection, coordinateDirection]
    rw [Finset.sum_eq_single j]
    · simp [Complex.mul_re]
    · intro b hb hbj; simp [hbj]
    · simp
  rw [hr, hi]
  apply Complex.ext <;> simp <;> ring

theorem bkCutoff_partial {n : ℕ} (m : ℕ) (j : Fin n) (z : Configuration n) :
    bkPartial (fun w => (ginibreSpatialCutoff n m w : ℂ)) j z =
      ((deriv (sobolevCutoff m) (configurationNormSq z) : ℝ) : ℂ) * conj (z j) := by
  have hχ : Differentiable ℝ (fun w : Configuration n => (ginibreSpatialCutoff n m w : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp (ginibreSpatialCutoff_smooth n m)).differentiable (by simp)
  rw [bkPartial_eq_conj_dbar hχ]
  rw [show (fun w : Configuration n => conj (ginibreSpatialCutoff n m w : ℂ)) =
    (fun w => (ginibreSpatialCutoff n m w : ℂ)) by funext w; simp]
  rw [dbarComponent_gaussianSpatialCutoff]
  simp

theorem bkAdjoint_cutoff_product {n : ℕ} (m : ℕ) {f : Configuration n → ℂ}
    (hf : ContDiff ℝ ∞ f) (j : Fin n) (z : Configuration n) :
    gaussianDbarAdjointTest j (fun w => (ginibreSpatialCutoff n m w : ℂ) * f w) z =
      (ginibreSpatialCutoff n m z : ℂ) * gaussianDbarAdjointTest j f z -
        ((deriv (sobolevCutoff m) (configurationNormSq z) : ℝ) : ℂ) * (conj (z j) * f z) := by
  have hχ : Differentiable ℝ (fun w : Configuration n => (ginibreSpatialCutoff n m w : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp (ginibreSpatialCutoff_smooth n m)).differentiable (by simp)
  have hprod : Differentiable ℝ (fun w : Configuration n => (ginibreSpatialCutoff n m w : ℂ) * f w)
      :=
    hχ.mul (hf.differentiable (by simp))
  rw [bkAdjoint_eq hprod]
  dsimp only
  rw [bkPartial_mul hχ (hf.differentiable (by simp)),
    bkCutoff_partial, bkAdjoint_eq (hf.differentiable (by simp))]
  dsimp only
  ring

/-- Exact second antiholomorphic derivative of the actual radial cutoff. -/
theorem bkCutoff_second_dbar {n : ℕ} (m : ℕ) (j k : Fin n) (z : Configuration n) :
    dbarComponent (dbarComponent (fun w => (ginibreSpatialCutoff n m w : ℂ)) j) k z =
      ((deriv (deriv (sobolevCutoff m)) (configurationNormSq z) : ℝ) : ℂ) * z k * z j := by
  rw [show dbarComponent (fun w => (ginibreSpatialCutoff n m w : ℂ)) j =
    fun w => ((deriv (sobolevCutoff m) (configurationNormSq w) : ℝ) : ℂ) * w j by
      funext w; exact dbarComponent_gaussianSpatialCutoff n m j w]
  have hg : ContDiff ℝ ∞ (deriv (sobolevCutoff m)) := (show ContDiff ℝ ((∞ : ℕ∞ω) + 1)
      (sobolevCutoff m) by simpa using sobolevCutoff_smooth m).deriv'
  have hcomp : Differentiable ℝ (fun w : Configuration n =>
      ((deriv (sobolevCutoff m) (configurationNormSq w) : ℝ) : ℂ)) := by
    exact (Complex.ofRealCLM.contDiff.comp (hg.comp contDiff_configurationNormSq)).differentiable
        (by simp)
  rw [dbarComponent_mul hcomp
    (show Differentiable ℝ (fun w : Configuration n => w j) by fun_prop),
    bkRadial_dbar _ hg,
    dbarComponent_eq_zero_of_differentiable_complex
      (show Differentiable ℂ (fun w : Configuration n => w j) by fun_prop)]
  ring

/-- The full second-order product rule for radial truncation. -/
theorem bkCutoff_product_second {n : ℕ} (m : ℕ) {f : Configuration n → ℂ}
    (hf : ContDiff ℝ ∞ f) (j k : Fin n) (z : Configuration n) :
    dbarComponent (dbarComponent (fun w => (ginibreSpatialCutoff n m w : ℂ) * f w) j) k z =
      (ginibreSpatialCutoff n m z : ℂ) * dbarComponent (dbarComponent f j) k z +
      ((deriv (sobolevCutoff m) (configurationNormSq z) : ℝ) : ℂ) *
        (z j * dbarComponent f k z + z k * dbarComponent f j z) +
      ((deriv (deriv (sobolevCutoff m)) (configurationNormSq z) : ℝ) : ℂ) * z k * z j * f z := by
  let χ : Configuration n → ℂ := fun w => (ginibreSpatialCutoff n m w : ℂ)
  have hχ : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp (ginibreSpatialCutoff_smooth n m)
  have hχd := hχ.differentiable (by simp)
  have hfd := hf.differentiable (by simp)
  have hfirst : dbarComponent (fun w => χ w * f w) j =
      fun w => dbarComponent χ j w * f w + χ w * dbarComponent f j w := by
    funext w; exact dbarComponent_mul hχd hfd j w
  rw [hfirst]
  have hA := ((bkDbar_contDiff hχ j).mul hf).differentiable (by simp) z
  have hB := (hχ.mul (bkDbar_contDiff hf j)).differentiable (by simp) z
  have hadd : dbarComponent (fun w => dbarComponent χ j w * f w + χ w * dbarComponent f j w) k z =
      dbarComponent (fun w => dbarComponent χ j w * f w) k z +
        dbarComponent (fun w => χ w * dbarComponent f j w) k z := by
    have he := (hA.hasFDerivAt.add hB.hasFDerivAt).fderiv
    change fderiv ℝ (fun w => dbarComponent χ j w * f w + χ w * dbarComponent f j w) z = _ at he
    unfold dbarComponent
    dsimp only [dbarComponent] at he
    rw [he]
    simp only [add_apply]
    ring
  rw [hadd, dbarComponent_mul ((bkDbar_contDiff hχ j).differentiable (by simp)) hfd,
    dbarComponent_mul hχd ((bkDbar_contDiff hf j).differentiable (by simp))]
  dsimp [χ]
  rw [bkCutoff_second_dbar, dbarComponent_gaussianSpatialCutoff,
    dbarComponent_gaussianSpatialCutoff]
  ring

end
end GinibrePoincare

