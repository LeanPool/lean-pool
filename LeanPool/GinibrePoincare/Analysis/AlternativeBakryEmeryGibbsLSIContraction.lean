/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryGibbsLSIContraction.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianEndpoint
/-!
# Alternative Bakry Emery Gibbs LSI contraction

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryLangevinEndpoint_initial_distance_tendsto`,
`bakryEmery_uniformObservable_difference_tendsto`.
-/

@[expose] public section
open Set Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Exact synchronous contraction of the constructed finite-horizon endpoint.
This includes its actual selected global solution, with no flow hypothesis. -/
theorem bakryEmeryLangevinEndpoint_synchronous_contraction
    (W : E → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z w : E) (T : ℝ) (hT : 0 ≤ T) (N : C(Icc 0 T, E)) :
    Real.exp (2*κ*T) *
      ‖bakryEmeryLangevinEndpoint W κ hκ hW hc z T hT N -
       bakryEmeryLangevinEndpoint W κ hκ hW hc w T hT N‖^2 ≤ ‖z-w‖^2 := by
  let NN := bkWeightedExtension T hT N
  let X := bakryEmeryLangevinCorrectionOn W κ hκ hW hc NN
    (bkWeightedExtension_continuous T hT N) z T hT
  let Y := bakryEmeryLangevinCorrectionOn W κ hκ hW hc NN
    (bkWeightedExtension_continuous T hT N) w T hT
  obtain ⟨hX, hX0, _, hXD⟩ := bakryEmeryLangevinCorrectionOn_spec W κ hκ hW hc NN
    (bkWeightedExtension_continuous T hT N) z T hT
  obtain ⟨hY, hY0, _, hYD⟩ := bakryEmeryLangevinCorrectionOn_spec W κ hκ hW hc NN
    (bkWeightedExtension_continuous T hT N) w T hT
  have hh := bakryEmeryLangevin_synchronous_contraction W κ
    (hW.differentiable (by norm_num)) hc NN X Y T hT hX.continuousOn hY.continuousOn
    hXD hYD T ⟨hT, le_rfl⟩
  simp only [bakryEmeryLangevinEndpoint, bakryEmeryLangevinStateOn,
    add_sub_add_right_eq_sub]
  change Real.exp (2*κ*T)*‖X T-Y T‖^2 ≤ ‖z-w‖^2
  change Real.exp (2*κ*T)*‖X T-Y T‖^2 ≤ ‖X 0-Y 0‖^2 at hh
  rw [show X 0=z from hX0, show Y 0=w from hY0] at hh
  exact hh

theorem bakryEmeryLangevinEndpoint_synchronous_norm
    (W : E → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z w : E) (T : ℝ) (hT : 0 ≤ T) (N : C(Icc 0 T, E)) :
    ‖bakryEmeryLangevinEndpoint W κ hκ hW hc z T hT N -
       bakryEmeryLangevinEndpoint W κ hκ hW hc w T hT N‖ ≤
      Real.exp (-κ*T)*‖z-w‖ := by
  have hh := bakryEmeryLangevinEndpoint_synchronous_contraction W κ hκ hW hc z w T hT N
  have he : Real.exp (2*κ*T) = Real.exp (κ*T)^2 := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  rw [he,←mul_pow] at hh
  have hnorm := (sq_le_sq₀ (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    (norm_nonneg (z-w))).mp hh
  have hex : Real.exp (-κ*T)*Real.exp (κ*T)=1 := by
    rw [←Real.exp_add]
    convert Real.exp_zero using 1; ring_nf
  have hb := mul_le_mul_of_nonneg_left hnorm (Real.exp_pos (-κ*T)).le
  simpa only [←mul_assoc, hex, one_mul] using hb

/-- The constructed flow forgets any finite initial point under common noise;
no integrable moment of a random initial point is required. -/
theorem bakryEmeryLangevinEndpoint_initial_distance_tendsto
    (W : E → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z w : E) (N : ∀ n : ℕ, C(Icc 0 (n+1 : ℝ), E)) :
    Tendsto (fun n : ℕ =>
      ‖bakryEmeryLangevinEndpoint W κ hκ hW hc z (n+1 : ℝ) (by positivity) (N n)-
       bakryEmeryLangevinEndpoint W κ hκ hW hc w (n+1 : ℝ) (by positivity) (N n)‖)
      atTop (nhds 0) := by
  have hn : Tendsto (fun n : ℕ => κ*(n+1 : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop hκ
  have he := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hn).mul_const ‖z-w‖
  simp only [zero_mul] at he
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n : ℕ => bakryEmeryLangevinEndpoint_synchronous_norm W κ hκ hW hc z w
      (n+1 : ℝ) (by positivity) (N n))
  simpa only [Function.comp_def, neg_mul] using he

/-- Uniformly continuous observables compare moving coupled states whose
separation vanishes, without requiring either state itself to converge. -/
theorem bakryEmery_uniformObservable_difference_tendsto
    {A : Type*} [PseudoMetricSpace A] (g : A → ℝ) (hg : UniformContinuous g)
    (X Y : ℕ → A) (hXY : Tendsto (fun n => dist (X n) (Y n)) atTop (nhds 0)) :
    Tendsto (fun n => g (X n)-g (Y n)) atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hgδ⟩ := Metric.uniformContinuous_iff.mp hg ε hε
  have hh := (Metric.tendsto_nhds.mp hXY) δ hδ
  filter_upwards [hh] with n hn
  have hnn : dist (X n) (Y n) < δ := by simpa only [Real.dist_eq, sub_zero, abs_of_nonneg
                                          (dist_nonneg)] using hn
  simpa only [Real.dist_eq, sub_zero] using hgδ hnn

end
end GinibrePoincare
