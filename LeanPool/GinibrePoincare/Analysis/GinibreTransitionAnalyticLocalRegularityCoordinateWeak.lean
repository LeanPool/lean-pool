/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityCoordinateWeak.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityCoordinateLp
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityCoordinateBasis

/-!
# Ginibre transition analytic local regularity coordinate weak

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalRegularity_coordinate_weak_derivative`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalRegularity_coordinate_weak_derivative
    (n : ℕ) (w : Configuration n → ℂ)
    (g : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))))
    (k : Fin n × Fin 2)
    (hg : ∀ θ : EuclideanSpace ℝ (Fin n × Fin 2) → ℂ,
      ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, θ x*g x) = -(∫ x, fderiv ℝ θ x (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ k)*
        w ((configurationEuclideanEquiv n).symm x))) :
    MemLp (fun z => g (configurationEuclideanEquiv n z)) 2 (volume : Measure (Configuration n)) ∧
    ∀ θ : Configuration n → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ z, θ z*g (configurationEuclideanEquiv n z)) =
        -(∫ z, fderiv ℝ θ z (ginibreCoordinateDirection k)*w z) := by
  refine ⟨ginibreLocalRegularity_coordinate_pullback_memLp n g (MeasureTheory.Lp.memLp g),?_⟩
  intro θ hθ hc
  let e := configurationEuclideanEquiv n
  let ψ := θ ∘ e.symm
  have hψ : ContDiff ℝ ∞ ψ := hθ.comp e.symm.contDiff
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph e.symm.toHomeomorph
  have hd (x) : fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ k) =
      fderiv ℝ θ (e.symm x) (ginibreCoordinateDirection k) := by
    have hh := ((hθ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp x
        e.symm.hasFDerivAt
    have he := congrArg (fun L => L (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ k)) hh.fderiv
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      e, ψ, ginibreLocalRegularity_coordinate_basis] using he
  have he := hg ψ hψ hψc
  simp_rw [hd] at he
  obtain ⟨c, hcpos, hchange⟩ := ginibreLocalRegularity_coordinate_integral n
  have hl := hchange (fun x => θ (e.symm x)*g x)
  have hr := hchange (fun x => fderiv ℝ θ (e.symm x) (ginibreCoordinateDirection k)*w (e.symm x))
  simp only [e, ContinuousLinearEquiv.symm_apply_apply] at hl hr
  rw [hl]
  rw [show (∫ x, θ (e.symm x)*g x) = ∫ x, ψ x*g x by rfl, he, smul_neg]
  rw [hr]

end
end GinibrePoincare
