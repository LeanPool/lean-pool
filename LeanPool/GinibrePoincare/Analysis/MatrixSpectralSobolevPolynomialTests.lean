/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevPolynomialTests.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevPolynomialWeak
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevWeakMultiplier

/-! # Full compact-test identities without any collision boundary term -/

@[expose] public section
open MeasureTheory Filter MvPolynomial
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem polynomial_collision_real_first_weak_test (d : ℕ)
    (p : MvPolynomial (Fin (d + 1)) ℂ) (hp : p ≠ 0)
    (F : Configuration (d + 1) → ℝ) (hF : Continuous F)
    (hd : ∀ z, MvPolynomial.eval z p ≠ 0 → DifferentiableAt ℝ F z)
    (hf : LocallyIntegrable F volume)
    (hg : LocallyIntegrable (fun z => fderiv ℝ F z (Fin.cons (1 : ℂ) 0)) volume)
    (θ : Configuration (d + 1) → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hc : HasCompactSupport θ) :
    (∫ z, fderiv ℝ F z (Fin.cons (1 : ℂ) 0) * θ z) =
      -(∫ z, F z * fderiv ℝ θ z (Fin.cons (1 : ℂ) 0)) := by
  let T := configurationRealFirstSplit d
  let ψ := θ ∘ T
  have hψ : ContDiff ℝ ∞ ψ := hθ.comp T.contDiff
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph T.toHomeomorph
  obtain ⟨C, hC⟩ := hψc.exists_bound_of_continuousOn
    (continuous_fst : Continuous (fun q : ℝ × (ℝ × Configuration d) => q.1)).continuousOn
  have hsupp (y : ℝ × Configuration d) :
      tsupport (fun t => ψ (t, y)) ⊆ Set.Ioo (-|C| - 1) (|C| + 1) := by
    intro t ht
    have ht' : (t, y) ∈ tsupport ψ :=
      tsupport_comp_subset_preimage ψ
        (show Continuous (fun t : ℝ => (t, y)) from by fun_prop) ht
    have hb : |t| ≤ C := by simpa using hC (t, y) ht'
    have hab : |t| ≤ |C| := hb.trans (le_abs_self C)
    constructor <;> linarith [neg_abs_le t, le_abs_self t]
  have hgi := local_integrable_mul_compact_test (d + 1)
    (fun z => fderiv ℝ F z (Fin.cons (1 : ℂ) 0)) θ hg hθ.continuous hc
  have hfi := local_integrable_mul_compact_test (d + 1) F
    (fun z => fderiv ℝ θ z (Fin.cons (1 : ℂ) 0)) hf
    ((hθ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ _)
  have hMP := configurationRealFirstSplit_volume_preserving d
  have hline (t : ℝ) (y : ℝ × Configuration d) :
      deriv (fun s => ψ (s, y)) t =
        fderiv ℝ θ (T (t, y)) (Fin.cons (1 : ℂ) 0) :=
    ((hθ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
      (configurationRealFirstSplit_line_hasDerivAt d y t)).deriv
  have h := product_weak_derivative_identity_of_finite_crossings
    (volume : Measure (ℝ × Configuration d))
    (F ∘ T) ((fun z => fderiv ℝ F z (Fin.cons (1 : ℂ) 0)) ∘ T)
    ψ ((fun z => fderiv ℝ θ z (Fin.cons (1 : ℂ) 0)) ∘ T)
    (-|C| - 1) (|C| + 1) (by linarith [abs_nonneg C])
    (fun y => (hψ.comp (by fun_prop)).of_le (by simp)) hline hsupp
    (polynomial_collision_real_first_slices d p hp F hF hd hg)
    (hMP.integrable_comp_of_integrable hgi) (hMP.integrable_comp_of_integrable hfi)
  rw [← hMP.integral_comp T.toHomeomorph.measurableEmbedding
      (fun z => fderiv ℝ F z (Fin.cons (1 : ℂ) 0) * θ z),
    ← hMP.integral_comp T.toHomeomorph.measurableEmbedding
      (fun z => F z * fderiv ℝ θ z (Fin.cons (1 : ℂ) 0))]
  exact h

end
end GinibrePoincare
