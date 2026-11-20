/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceCurvatureHessian.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceCurvatureGradient
/-!
# Correspondence curvature hessian

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondence_hamiltonian_interaction_hessian`.
-/

@[expose] public section
open Set Filter
open scoped ContDiff BigOperators ComplexConjugate Topology
namespace GinibrePoincare
noncomputable section

theorem correspondence_configurationNormSq_hessian {n : ℕ} (z v w : Configuration n) :
    fderiv ℝ (fderiv ℝ configurationNormSq) z v w =
      2*∑ j, (conj (v j)*w j).re := by
  rw [← bochnerDirectionalDerivative_iterated v w configurationNormSq z
      contDiff_configurationNormSq.contDiffAt]
  have he : bochnerDirectionalDerivative w configurationNormSq =
      fun x : Configuration n => 2*∑ j, (conj (x j)*w j).re := by
    funext x
    exact fderiv_configurationNormSq_apply x w
  rw [he]
  let L : Configuration n →L[ℝ] ℝ :=
    2 • ∑ j, (Complex.reCLM.comp (((ContinuousLinearMap.mul ℝ ℂ).flip (w j)).comp
      (Complex.conjCLE.toContinuousLinearMap.comp
        (ContinuousLinearMap.proj j : Configuration n →L[ℝ] ℂ))))
  have heL : (fun x : Configuration n => 2*∑ j, (conj (x j)*w j).re) = L := by
    funext x
    simp [L, mul_comm]
  rw [heL]
  unfold bochnerDirectionalDerivative
  rw [L.fderiv]
  simp [L, mul_comm]

theorem correspondence_hamiltonian_interaction_hessian {n : ℕ}
    (z v w : Configuration n) (hz : CollisionFree z) :
    fderiv ℝ (fderiv ℝ (ginibreHamiltonian n)) z v w =
      2*(n : ℝ)*(∑ j, (conj (v j)*w j).re) +
        fderiv ℝ (fderiv ℝ (ginibreInteractionPotential n)) z v w := by
  have hQ := contDiff_configurationNormSq (n := n)
  have hI := ginibreInteractionPotential_contDiffAt n z hz
  have hH : ginibreHamiltonian n =
      fun x => (n : ℝ)*configurationNormSq x + ginibreInteractionPotential n x := by
    funext x
    simp only [ginibreHamiltonian, ginibreInteractionPotential, sub_eq_add_neg]
  have he : fderiv ℝ (ginibreHamiltonian n) =ᶠ[𝓝 z]
      (fun x => (n : ℝ) • fderiv ℝ configurationNormSq x +
        fderiv ℝ (ginibreInteractionPotential n) x) := by
    filter_upwards [(isOpen_collisionFree n).mem_nhds hz] with x hx
    rw [hH]
    have hh := ((hQ.differentiable (by simp)).differentiableAt.hasFDerivAt.fun_const_smul (n :
        ℝ)).fun_add
      (((ginibreInteractionPotential_contDiffAt n x hx).differentiableAt (by simp)).hasFDerivAt)
    simpa only [Pi.add_apply, smul_eq_mul] using hh.fderiv
  rw [he.fderiv_eq]
  have hQD := (hQ.contDiffAt.fderiv_right (m := ∞) (by simp)).differentiableAt (x := z) (by simp)
  have hID := (hI.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  rw [fderiv_fun_add (hQD.fun_const_smul (n : ℝ)) hID,
    fderiv_fun_const_smul hQD (n : ℝ)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [correspondence_configurationNormSq_hessian]
  ring

end
end GinibrePoincare
