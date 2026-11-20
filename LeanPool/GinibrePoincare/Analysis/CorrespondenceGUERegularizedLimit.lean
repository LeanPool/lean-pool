/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUERegularizedLimit.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUERegularizedPotential
public import LeanPool.GinibrePoincare.Analysis.CorrespondencePolynomialRealGaussianDensity
/-!
# Correspondence GUE regularized limit

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueRegularizedPairWeight_tendsto`, `gueRegularizedPairWeight_bound`,
`gueGaussianPolynomial_integrable`.
-/

@[expose] public section
open MeasureTheory Filter Set
open scoped Topology ContDiff ENNReal NNReal BigOperators
namespace GinibrePoincare
noncomputable section

/-- The regularization scales `1 / (k + 1)`. -/
def gueRegularizationScale (k : ℕ) : ℝ := 1/(k+1 : ℝ)

/-- The ordered pair weight: `u ^ 2` for `0 < u` and `0` otherwise. -/
def gueOrderedPairWeight (u : ℝ) : ℝ := if 0<u then u^2 else 0

theorem gueRegularizationScale_pos (k : ℕ) : 0<gueRegularizationScale k := by
  unfold gueRegularizationScale
  positivity

theorem gueRegularizationScale_le_one (k : ℕ) : gueRegularizationScale k≤1 := by
  unfold gueRegularizationScale
  apply (div_le_one (by positivity : (0 : ℝ)<(k : ℝ)+1)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

theorem gueRegularizationScale_tendsto : Tendsto gueRegularizationScale atTop (nhds 0) := by
  change Tendsto (fun k : ℕ => 1/((k : ℝ)+1)) atTop (nhds 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

/-- The smooth positive pair densities converge to the ordered positive-gap
weight, vanishing also for reversed and colliding particle gaps. -/
theorem gueRegularizedPairWeight_tendsto (u : ℝ) :
    Tendsto (fun k => Real.exp (-2*gueLogBarrier (gueRegularizationScale k) u)) atTop
      (nhds (gueOrderedPairWeight u)) := by
  by_cases hu : 0<u
  · have hε : ∀ᶠ k in atTop, gueRegularizationScale k<u :=
      gueRegularizationScale_tendsto.eventually (gt_mem_nhds hu)
    apply tendsto_const_nhds.congr'
    filter_upwards [hε] with k hk
    unfold gueLogBarrier gueOrderedPairWeight
    rw [ite_eq_right (not_le.mpr hk), ite_eq_left hu]
    have he : -2 * -Real.log u = Real.log u+Real.log u := by ring
    rw [he, Real.exp_add, Real.exp_log hu]
    ring
  · unfold gueOrderedPairWeight
    rw [ite_eq_right hu]
    apply squeeze_zero (fun k => (Real.exp_pos _).le)
      (fun k => gueLogBarrier_exp_bound (gueRegularizationScale_pos k)
        ((le_of_not_gt hu).trans (gueRegularizationScale_pos k).le))
    simpa only [zero_pow (by decide : 2≠0)] using gueRegularizationScale_tendsto.pow 2

/-- Uniform domination of all smooth pair factors by an actual polynomial. -/
theorem gueRegularizedPairWeight_bound (k : ℕ) (u : ℝ) :
    Real.exp (-2*gueLogBarrier (gueRegularizationScale k) u) ≤ 2*(1+u^2) := by
  have h := gueLogBarrier_exp_polynomial_bound (gueRegularizationScale_pos k)
    (gueRegularizationScale_le_one k) (u := u)
  apply h.trans
  nlinarith [sq_nonneg (|u|-1), sq_abs u]

/-- Literal Gaussian confinement times an arbitrary polynomial is Lebesgue
integrable in real Hilbert coordinates; the Gaussian normalization is internal. -/
theorem gueGaussianPolynomial_integrable {ι : Type*} [Fintype ι]
    {a : ℝ} (ha : 0 < a) (P : MvPolynomial ι ℝ) :
    Integrable (fun x : EuclideanSpace ℝ ι => Real.exp (-a*‖x‖^2) * MvPolynomial.eval (WithLp.ofLp
        x) P) volume := by
  classical
  rw [← (PiLp.volume_preserving_toLp ι).integrable_comp_emb
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  let v : ℝ≥0 := ⟨(2*a)⁻¹, by positivity⟩
  have hv : v≠0 := by
    apply ne_of_gt
    change (0 : ℝ)<(2*a)⁻¹
    positivity
  have hh := correspondencePolynomial_realGaussian_density_integrable v hv P
  convert hh using 1
  funext x
  simp only [Function.comp_apply]
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [show (v : ℝ) = (2*a)⁻¹ from rfl]
  field_simp [ha.ne']

end
end GinibrePoincare
