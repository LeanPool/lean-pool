/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteDimensionalItoLocalTaylor.lean.
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

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoTaylor
public import Mathlib.Topology.MetricSpace.Thickening

/-! # C² Taylor control on an open domain

The segment versions of the Taylor formula and Hessian-oscillation bound
require C² regularity only along `x + t • h`, for `0 ≤ t ≤ 1`. They therefore
apply to functions defined smoothly away from a singular set.

For a compact subset `K` of an open domain `U`, choose a positive closed
thickening of `K` still contained in `U`. Properness makes this thickening
compact, so the Hessian is uniformly continuous there. Taking increments
shorter than both the thickening radius and the continuity threshold keeps
the entire segment in `U` and gives a uniform quadratic remainder estimate.
The domain and `K` need not be convex in this local version. -/

@[expose] public section

open MeasureTheory Metric
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem itoTaylor_integral_of_segment (f : E → ℝ) (x h : E)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (x + t • h)) :
    f (x+h) = f x + fderiv ℝ f x h +
      ∫ t in (0 : ℝ)..1, (1-t)*itoDirectionalHessian f (x+t•h) h := by
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv (n := 1) (x := x) (y := h) hf
  simpa [Finset.sum_range_succ, iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply,
    itoDirectionalHessian] using ht

theorem itoTaylorRemainder_eq_integral_of_segment (f : E → ℝ) (x h : E)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (x + t • h)) :
    itoTaylorRemainder f x h = ∫ t in (0 : ℝ)..1,
      (1 - t) * (itoDirectionalHessian f (x + t • h) h - itoDirectionalHessian f x h) := by
  have hc : ContinuousOn (fun t : ℝ => itoDirectionalHessian f (x+t•h) h) (Set.Icc 0 1) := by
    intro t ht
    have hd : ContinuousAt (iteratedFDeriv ℝ 2 f) (x+t•h) :=
      (hf t ht).continuousAt_iteratedFDeriv (k := 2) (by norm_num)
    have hl : ContinuousAt (fun s : ℝ => x+s•h) t := by fun_prop
    exact ((continuous_eval_const (fun _ : Fin 2 => h)).continuousAt.comp
      (hd.comp (f := fun s : ℝ => x+s•h) (x := t) hl)).continuousWithinAt
  have hi : IntervalIntegrable (fun t : ℝ => (1-t)*itoDirectionalHessian f (x+t•h) h) volume 0 1 :=
    ((continuous_const.sub continuous_id).continuousOn.mul hc).intervalIntegrable_of_Icc zero_le_one
  have hj : IntervalIntegrable (fun t : ℝ => (1-t)*itoDirectionalHessian f x h) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => (1-t)*itoDirectionalHessian f x h)).intervalIntegrable _
        _
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub hi hj, intervalIntegral.integral_mul_const]
  have hw : ∫ t in (0 : ℝ)..1, 1-t = (1/2 : ℝ) := by
    rw [intervalIntegral.integral_sub
      (show IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 from
          continuous_const.intervalIntegrable _ _)
      (show IntervalIntegrable (fun t : ℝ => t) volume 0 1 from continuous_id.intervalIntegrable _
          _),
      intervalIntegral.integral_const, integral_id]
    norm_num
  rw [hw]
  unfold itoTaylorRemainder
  rw [itoTaylor_integral_of_segment f x h hf]
  ring

/-- A quantitative C² remainder bound from the actual operator-norm Hessian oscillation. -/
theorem itoTaylorRemainder_norm_le_of_segment (f : E → ℝ) (x h : E)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (x + t • h)) (ε : ℝ) (hε : 0 ≤ ε)
    (hosc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ 2 f (x + t • h) - iteratedFDeriv ℝ 2 f x‖ ≤ ε) :
    ‖itoTaylorRemainder f x h‖ ≤ ε * ‖h‖ ^ 2 := by
  rw [itoTaylorRemainder_eq_integral_of_segment f x h hf]
  have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖(1-t)*(itoDirectionalHessian f (x+t•h) h - itoDirectionalHessian f x h)‖ ≤
        ε * ‖h‖^2 := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
       simpa [Set.uIoc, min_eq_left zero_le_one, max_eq_right zero_le_one] using
           Set.Ioc_subset_Icc_self ht
    have hd : ‖itoDirectionalHessian f (x+t•h) h - itoDirectionalHessian f x h‖ ≤
        ε * ‖h‖^2 := by
      have hop := (iteratedFDeriv ℝ 2 f (x+t•h) - iteratedFDeriv ℝ 2 f x).le_opNorm (fun _ => h)
      simp only [sub_apply, Fin.prod_univ_two, pow_two] at hop ⊢
      exact hop.trans (mul_le_mul_of_nonneg_right (hosc t ht') (mul_self_nonneg _))
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht'.2)]
    exact (mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr ht'.2)).trans
      (mul_le_of_le_one_left (by positivity) (by linarith [ht'.1]))
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hb

/-- Uniform quadratic remainder on any compact subset of an open C² domain.
The domain need not be convex; short increment segments stay inside it. -/
theorem itoTaylorRemainder_uniform_compact_open [ProperSpace E]
    (f : E → ℝ) (U K : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ K, ∀ h : E, ‖h‖ < δ →
      ‖itoTaylorRemainder f x h‖ ≤ ε * ‖h‖^2 := by
  obtain ⟨η, hη, hth⟩ := hK.exists_cthickening_subset_open hU hKU
  have hc : ContinuousOn (iteratedFDeriv ℝ 2 f) (cthickening η K) :=
    (ContinuousOn.continuousOn_iteratedFDeriv hf hU (by norm_num)).mono hth
  have hu := hK.cthickening.uniformContinuousOn_of_continuous hc
  intro ε hε
  obtain ⟨r, hr, hu⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨min η r, lt_min hη hr, fun x hx h hh => ?_⟩
  have hdist (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : dist (x+t•h) x < min η r := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt hh
  have hseg (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : x+t•h ∈ cthickening η K :=
    mem_cthickening_of_dist_le _ x η K hx ((hdist t ht).le.trans (min_le_left _ _))
  apply itoTaylorRemainder_norm_le_of_segment f x h
    (fun t ht => hf.contDiffAt (hU.mem_nhds (hth (hseg t ht)))) ε hε.le
  intro t ht
  simpa only [dist_eq_norm] using (hu _ (hseg t ht) x (self_subset_cthickening K hx)
    ((hdist t ht).trans_le (min_le_right _ _))).le

end
end GinibrePoincare
