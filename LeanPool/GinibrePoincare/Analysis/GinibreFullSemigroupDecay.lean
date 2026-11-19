/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullSemigroupDecay.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupDynamics
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorEnergy
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Sharp full-space equilibrium decay -/

@[expose] public section
open MeasureTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Scalar multiplication gives every full equilibrium constant. -/
theorem ginibreFullConstant_eq_smul_one (n : ℕ) (hn : 0 < n) (c : ℂ) :
    ginibreFullConstant n hn c = c • ginibreFullConstant n hn 1 := by
  apply Subtype.ext
  change ginibreConstantL2 n hn c = c • ginibreConstantL2 n hn 1
  simpa only [smul_eq_mul, mul_one] using (ginibreConstantL2 n hn).map_smul c 1

/-- The scalar full Hilbert mean has the actual real and imaginary equilibrium means. -/
theorem ginibreFullMean_parts (n : ℕ) (hn : 0 < n) (u : ginibreSymmetricL2 n) :
    inner ℂ (ginibreFullConstant n hn 1) u =
      ⟨ginibreL2Mean n (ginibreFullSymmetricRe n u).val,
        ginibreL2Mean n (ginibreFullSymmetricIm n u).val⟩ := by
  have hre : ginibreFullComplexRe n (ginibreFullConstant n hn 1).val =
      ginibreRealConstantL2 n hn 1 := ginibreFullConstant_re n hn 1
  have him : ginibreFullComplexIm n (ginibreFullConstant n hn 1).val = 0 := by
    have hi := ginibreFullConstant_im n hn 1
    change ginibreFullComplexIm n (ginibreFullConstant n hn 1).val = ginibreRealConstantL2 n hn
        0 at hi
    simpa only [ginibreRealConstantL2_zero] using hi
  apply Complex.ext
  · have h := ginibreFullComplex_inner_re n (ginibreFullConstant n hn 1).val u.val
    change (inner ℂ (ginibreFullConstant n hn 1) u).re = _ at h
    rw [h, hre, him, inner_zero_left, add_zero]
    exact ginibreRealConstantL2_one_inner n hn _
  · have h := ginibreFullComplex_inner_im n (ginibreFullConstant n hn 1).val u.val
    change (inner ℂ (ginibreFullConstant n hn 1) u).im = _ at h
    rw [h, hre, him, inner_zero_left, sub_zero]
    exact ginibreRealConstantL2_one_inner n hn _

/-- Zero complex mean gives the exact sum-of-real-variances norm. -/
theorem ginibreFullVariance_eq_norm_sq_of_mean_zero (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) (hu : inner ℂ (ginibreFullConstant n hn 1) u = 0) :
    ginibreL2Variance n hn (ginibreFullSymmetricRe n u).val +
      ginibreL2Variance n hn (ginibreFullSymmetricIm n u).val = ‖u‖ ^ 2 := by
  have hm := ginibreFullMean_parts n hn u
  rw [hu] at hm
  have hr : ginibreL2Mean n (ginibreFullSymmetricRe n u).val = 0 := by
    exact (congrArg Complex.re hm).symm
  have hi : ginibreL2Mean n (ginibreFullSymmetricIm n u).val = 0 := by
    exact (congrArg Complex.im hm).symm
  simp only [ginibreL2Variance, hr, hi, ginibreRealConstantL2_zero, sub_zero]
  exact (ginibreFullComplex_norm_sq n u.val).symm

/-- The full semigroup preserves zero-mean observables. -/
theorem ginibreFullEvolution_mean_zero (n : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (u : ginibreSymmetricL2 n) (hu : inner ℂ (ginibreFullConstant n hn 1) u = 0) :
    inner ℂ (ginibreFullConstant n hn 1) (ginibreFullEvolution n hn t u) = 0 := by
  rw [ginibreFullConstant_one_inner, ginibreFullEvolution_integral,
    ← ginibreFullConstant_one_inner]
  exact hu

/-- Sharp exponential decay on the actual full generator domain. -/
theorem ginibreFullEvolution_decay_sq_on_domain (n : ℕ) (hn : 0 < n)
    (u v : ginibreSymmetricL2 n) (hgraph : (u, v) ∈ (ginibreFullGenerator n hn).graph)
    (hmean : inner ℂ (ginibreFullConstant n hn 1) u = 0) (t : ℝ≥0) :
    ‖ginibreFullEvolution n hn t u‖ ^ 2 ≤ Real.exp (-4 * (t : ℝ)) * ‖u‖ ^ 2 := by
  let : InnerProductSpace ℝ (ginibreSymmetricL2 n) := InnerProductSpace.complexToReal
  let orbit := fun s : ℝ => ginibreFullEvolution n hn (Real.toNNReal s) u
  let velocity := fun s : ℝ => ginibreFullEvolution n hn (Real.toNNReal s) v
  let F := fun s : ℝ => Real.exp (4 * s) * ‖orbit s‖ ^ 2
  let D := fun s : ℝ => Real.exp (4 * s) *
    (4 * ‖orbit s‖ ^ 2 + 2 * inner ℝ (orbit s) (velocity s))
  have horbit : Continuous orbit :=
    (continuous_ginibreFullEvolution n hn u).comp continuous_real_toNNReal
  have hF : Continuous F := by fun_prop
  have hder : ∀ s ∈ Set.Ioi (0 : ℝ), HasDerivAt F (D s) s := by
    intro s hs
    have hd : HasDerivAt (fun r : ℝ => ‖orbit r‖ ^ 2)
        (2 * inner ℝ (orbit s) (velocity s)) s :=
      (ginibreFullEvolution_hasDerivAt n hn u v hgraph hs).norm_sq
    have hexp : HasDerivAt (fun r : ℝ => Real.exp (4 * r)) (4 * Real.exp (4 * s)) s := by
      convert (((hasDerivAt_id s).const_mul 4).exp) using 1 <;> simp [mul_comm]
    exact (hexp.mul hd).congr_deriv (by dsimp only [D]; ring)
  have hnonpos : ∀ s ∈ Set.Ioi (0 : ℝ), D s ≤ 0 := by
    intro s hs
    have hp := ginibreFullGenerator_complex_poincare hn (orbit s) (velocity s)
      (ginibreFullEvolution_preserves_generator_graph n hn (Real.toNNReal s) u v hgraph)
    have hm := ginibreFullEvolution_mean_zero n hn (Real.toNNReal s) u hmean
    rw [ginibreFullVariance_eq_norm_sq_of_mean_zero n hn (orbit s) hm] at hp
    have hi : inner ℝ (orbit s) (velocity s) = (inner ℂ (velocity s) (orbit s)).re := by
      rw [real_inner_eq_re_inner ℂ]
      exact inner_re_symm _ _
    dsimp only [D]
    rw [hi]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
  have hanti : AntitoneOn F (Set.Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0 : ℝ)) hF.continuousOn
    · intro s hs
      rw [interior_Ici] at hs
      exact (hder s hs).hasDerivWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      exact hnonpos s hs
  have hb := hanti (by simp : (0 : ℝ) ∈ Set.Ici 0) t.coe_nonneg t.coe_nonneg
  have hz : orbit 0 = u := by simp only [orbit, Real.toNNReal_zero,
    ginibreFullEvolution_zero n hn, one_apply_eq_self]
  have ht : orbit (t : ℝ) = ginibreFullEvolution n hn t u := by
    simp only [orbit, Real.toNNReal_coe]
  change Real.exp (4 * (t : ℝ)) * ‖orbit (t : ℝ)‖ ^ 2 ≤ Real.exp (4 * 0) * ‖orbit 0‖ ^ 2 at hb
  rw [ht, hz, mul_zero, Real.exp_zero, one_mul] at hb
  have hm := mul_le_mul_of_nonneg_left hb (Real.exp_pos (-4 * (t : ℝ))).le
  rw [← mul_assoc, ← Real.exp_add, show -4 * (t : ℝ) + 4 * (t : ℝ) = 0 by ring,
    Real.exp_zero, one_mul] at hm
  exact hm

/-- Full equilibrium centering as a bounded complex-linear map. -/
def ginibreFullComplexCenter (n : ℕ) (hn : 0 < n) :
    ginibreSymmetricL2 n →L[ℂ] ginibreSymmetricL2 n :=
  ContinuousLinearMap.id ℂ _ - (innerSL ℂ (ginibreFullConstant n hn 1)).smulRight
    (ginibreFullConstant n hn 1)

theorem ginibreFullComplexCenter_apply (n : ℕ) (hn : 0 < n) (u : ginibreSymmetricL2 n) :
    ginibreFullComplexCenter n hn u = u - ginibreFullConstant n hn
      (inner ℂ (ginibreFullConstant n hn 1) u) := by
  change u - inner ℂ (ginibreFullConstant n hn 1) u • ginibreFullConstant n hn 1 = _
  rw [ginibreFullConstant_eq_smul_one n hn (inner ℂ (ginibreFullConstant n hn 1) u)]

theorem ginibreFullConstant_norm_one (n : ℕ) (hn : 0 < n) :
    ‖ginibreFullConstant n hn 1‖ = 1 := by
  change ‖ginibreConstantL2 n hn 1‖ = 1
  rw [(ginibreConstantL2 n hn).norm_map, norm_one]

theorem ginibreFullComplexCenter_mean_zero (n : ℕ) (hn : 0 < n) (u : ginibreSymmetricL2 n) :
    inner ℂ (ginibreFullConstant n hn 1) (ginibreFullComplexCenter n hn u) = 0 := by
  rw [ginibreFullComplexCenter_apply, ginibreFullConstant_eq_smul_one n hn
    (inner ℂ (ginibreFullConstant n hn 1) u), inner_sub_right]
  have hsmul : inner ℂ (ginibreFullConstant n hn 1)
      (inner ℂ (ginibreFullConstant n hn 1) u • ginibreFullConstant n hn 1) =
      inner ℂ (ginibreFullConstant n hn 1) u *
        inner ℂ (ginibreFullConstant n hn 1) (ginibreFullConstant n hn 1) := by
    change inner ℂ (ginibreFullConstant n hn 1).val
      (inner ℂ (ginibreFullConstant n hn 1) u • (ginibreFullConstant n hn 1).val) = _
    exact inner_smul_right _ _ _
  rw [hsmul, inner_self_eq_norm_sq_to_K, ginibreFullConstant_norm_one]
  simp

theorem ginibreFullComplexCenter_graph (n : ℕ) (hn : 0 < n) (u v : ginibreSymmetricL2 n)
    (hgraph : (u, v) ∈ (ginibreFullGenerator n hn).graph) :
    (ginibreFullComplexCenter n hn u, v) ∈ (ginibreFullGenerator n hn).graph := by
  have hconst := ginibreFullGenerator_constant n hn (inner ℂ (ginibreFullConstant n hn 1) u)
  have hsub := (ginibreFullGenerator n hn).graph.sub_mem hgraph hconst
  change (u - ginibreFullConstant n hn (inner ℂ (ginibreFullConstant n hn 1) u), v - 0) ∈ _ at hsub
  simpa only [sub_zero, ginibreFullComplexCenter_apply] using hsub

/-- Full-space squared equilibrium decay, extended by genuine generator-domain density. -/
theorem ginibreFullEvolution_centered_decay_sq (n : ℕ) (hn : 0 < n)
    (t : ℝ≥0) (u : ginibreSymmetricL2 n) :
    ‖ginibreFullEvolution n hn t (ginibreFullComplexCenter n hn u)‖ ^ 2 ≤
      Real.exp (-4 * (t : ℝ)) * ‖ginibreFullComplexCenter n hn u‖ ^ 2 := by
  have hc : IsClosed {x : ginibreSymmetricL2 n |
      ‖ginibreFullEvolution n hn t (ginibreFullComplexCenter n hn x)‖ ^ 2 ≤
        Real.exp (-4 * (t : ℝ)) * ‖ginibreFullComplexCenter n hn x‖ ^ 2} := by
    apply isClosed_le <;> fun_prop
  have hsub : ((ginibreFullGenerator n hn).domain : Set (ginibreSymmetricL2 n)) ⊆
      {x : ginibreSymmetricL2 n |
      ‖ginibreFullEvolution n hn t (ginibreFullComplexCenter n hn x)‖ ^ 2 ≤
        Real.exp (-4 * (t : ℝ)) * ‖ginibreFullComplexCenter n hn x‖ ^ 2} := by
    intro x hx
    let v := ginibreFullGenerator n hn ⟨x, hx⟩
    have hg : (x, v) ∈ (ginibreFullGenerator n hn).graph := (ginibreFullGenerator n hn).mem_graph
        ⟨x, hx⟩
    exact ginibreFullEvolution_decay_sq_on_domain n hn _ v
      (ginibreFullComplexCenter_graph n hn x v hg) (ginibreFullComplexCenter_mean_zero n hn x) t
  apply closure_minimal hsub hc
  rw [(ginibreFullGenerator_dense_domain n hn).closure_eq]
  trivial

/-- The sharp norm decay rate `2` holds on the entire full symmetric L² space. -/
theorem ginibreFullEvolution_centered_decay (n : ℕ) (hn : 0 < n)
    (t : ℝ≥0) (u : ginibreSymmetricL2 n) :
    ‖ginibreFullEvolution n hn t (ginibreFullComplexCenter n hn u)‖ ≤
      Real.exp (-2 * (t : ℝ)) * ‖ginibreFullComplexCenter n hn u‖ := by
  have hsq := ginibreFullEvolution_centered_decay_sq n hn t u
  have he : Real.exp (-4 * (t : ℝ)) = Real.exp (-2 * (t : ℝ)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he] at hsq
  have hb : 0 ≤ Real.exp (-2 * (t : ℝ)) * ‖ginibreFullComplexCenter n hn u‖ :=
    mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hs' : ‖ginibreFullEvolution n hn t (ginibreFullComplexCenter n hn u)‖ ^ 2 ≤
      (Real.exp (-2 * (t : ℝ)) * ‖ginibreFullComplexCenter n hn u‖) ^ 2 := by
    simpa only [mul_pow] using hsq
  exact (sq_le_sq₀ (norm_nonneg _) hb).mp hs'

/-- Centering commutes with full evolution. -/
theorem ginibreFullEvolution_center (n : ℕ) (hn : 0 < n)
    (t : ℝ≥0) (u : ginibreSymmetricL2 n) :
    ginibreFullEvolution n hn t (ginibreFullComplexCenter n hn u) =
      ginibreFullComplexCenter n hn (ginibreFullEvolution n hn t u) := by
  rw [ginibreFullComplexCenter_apply, map_sub, ginibreFullEvolution_constant,
    ginibreFullComplexCenter_apply]
  have hm : inner ℂ (ginibreFullConstant n hn 1) (ginibreFullEvolution n hn t u) =
      inner ℂ (ginibreFullConstant n hn 1) u := by
    rw [ginibreFullConstant_one_inner, ginibreFullEvolution_integral,
      ← ginibreFullConstant_one_inner]
  rw [hm]

/-- Sharp convergence bound to the actual equilibrium constant for every full L² observable. -/
theorem ginibreFullEvolution_equilibrium_bound (n : ℕ) (hn : 0 < n)
    (t : ℝ≥0) (u : ginibreSymmetricL2 n) :
    dist (ginibreFullEvolution n hn t u)
      (ginibreFullConstant n hn (inner ℂ (ginibreFullConstant n hn 1) u)) ≤
      Real.exp (-2 * (t : ℝ)) * ‖ginibreFullComplexCenter n hn u‖ := by
  rw [dist_eq_norm]
  have he : ginibreFullEvolution n hn t u -
      ginibreFullConstant n hn (inner ℂ (ginibreFullConstant n hn 1) u) =
      ginibreFullEvolution n hn t (ginibreFullComplexCenter n hn u) := by
    rw [ginibreFullComplexCenter_apply, map_sub, ginibreFullEvolution_constant]
  rw [he]
  exact ginibreFullEvolution_centered_decay n hn t u

/-- Full L² ergodic convergence, with the exact equilibrium integral as limit. -/
theorem ginibreFullEvolution_tendsto_equilibrium (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) :
    Tendsto (fun t : ℝ≥0 => ginibreFullEvolution n hn t u) atTop
      (𝓝 (ginibreFullConstant n hn (∫ z, u.val z ∂ginibreMeasure n))) := by
  rw [← ginibreFullConstant_one_inner n hn]
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have htimes : Tendsto (fun t : ℝ≥0 => (2 : ℝ) * (t : ℝ)) atTop atTop :=
    hcoe.const_mul_atTop (by norm_num)
  have hexp : Tendsto (fun t : ℝ≥0 => Real.exp (-2 * (t : ℝ))) atTop (𝓝 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp htimes using 1
    funext t
    change Real.exp (-2 * (t : ℝ)) = Real.exp (-(2 * (t : ℝ)))
    congr 1
    ring
  have hb := hexp.mul_const ‖ginibreFullComplexCenter n hn u‖
  simp only [zero_mul] at hb
  exact squeeze_zero (fun _ => dist_nonneg)
    (fun t => ginibreFullEvolution_equilibrium_bound n hn t u) hb

end
end GinibrePoincare
