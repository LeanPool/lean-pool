/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteDimensionalItoTaylor.lean.
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

public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.Convex.Basic

/-! # Deterministic C² Taylor estimates for Itô sums

`itoDirectionalHessian f x h` evaluates the second Fréchet derivative twice
on the increment `h`. The exact integral Taylor formula subtracts its
value at `x` to express the quadratic remainder through Hessian oscillation.
This avoids any assumption of a third derivative.

The operator-norm oscillation bound gives a remainder bounded by
`ε * ‖h‖²`. On a compact convex set, uniform continuity of the Hessian
provides a single increment threshold `δ`; convexity keeps the connecting
segments inside the set. These deterministic estimates are used when
controlling the remainder in stochastic partition sums. -/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual second directional derivative used in the quadratic Taylor term. -/
def itoDirectionalHessian (f : E → ℝ) (x h : E) : ℝ :=
  iteratedFDeriv ℝ 2 f x (fun _ => h)

/-- Exact second-order integral Taylor formula along a segment on which the test is C². -/
theorem itoTaylor_integral_of_segment (f : E → ℝ) (x h : E)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (x + t • h)) :
    f (x+h) = f x + fderiv ℝ f x h +
      ∫ t in (0 : ℝ)..1, (1-t)*itoDirectionalHessian f (x+t•h) h := by
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv (n := 1) (x := x) (y := h) hf
  simpa [Finset.sum_range_succ, iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply,
    itoDirectionalHessian] using ht

/-- Exact second-order integral Taylor formula for a genuine C² test. -/
theorem itoTaylor_integral (f : E → ℝ) (hf : ContDiff ℝ 2 f) (x h : E) :
    f (x + h) = f x + fderiv ℝ f x h +
      ∫ t in (0 : ℝ)..1, (1 - t) * itoDirectionalHessian f (x + t • h) h :=
  itoTaylor_integral_of_segment f x h fun _ _ => hf.contDiffAt

/-- The quadratic Taylor error is exactly the averaged Hessian oscillation. -/
def itoTaylorRemainder (f : E → ℝ) (x h : E) : ℝ :=
  f (x + h) - f x - fderiv ℝ f x h - (1 / 2 : ℝ) * itoDirectionalHessian f x h

/-- Exact centered Hessian remainder along a segment on which the test is C²,
with no third differentiability assumption. -/
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

/-- Exact centered Hessian remainder, with no third differentiability assumption. -/
theorem itoTaylorRemainder_eq_integral (f : E → ℝ) (hf : ContDiff ℝ 2 f) (x h : E) :
    itoTaylorRemainder f x h = ∫ t in (0 : ℝ)..1,
      (1 - t) * (itoDirectionalHessian f (x + t • h) h - itoDirectionalHessian f x h) :=
  itoTaylorRemainder_eq_integral_of_segment f x h fun _ _ => hf.contDiffAt

/-- A quantitative C² remainder bound along a segment on which the test is C². -/
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

/-- A quantitative C² remainder bound from the actual operator-norm Hessian oscillation. -/
theorem itoTaylorRemainder_norm_le (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (x h : E) (ε : ℝ) (hε : 0 ≤ ε)
    (hosc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ 2 f (x + t • h) - iteratedFDeriv ℝ 2 f x‖ ≤ ε) :
    ‖itoTaylorRemainder f x h‖ ≤ ε * ‖h‖ ^ 2 :=
  itoTaylorRemainder_norm_le_of_segment f x h (fun _ _ => hf.contDiffAt) ε hε hosc

/-- The genuine quadratic Taylor remainder is uniformly small on a compact convex set. -/
theorem itoTaylorRemainder_uniform_compact (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (K : Set E) (hK : IsCompact K) (hconv : Convex ℝ K) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ K, ‖y-x‖ < δ →
      ‖itoTaylorRemainder f x (y-x)‖ ≤ ε * ‖y-x‖^2 := by
  have hu := hK.uniformContinuousOn_of_continuous
    (hf.continuous_iteratedFDeriv (m := 2) (by norm_num)).continuousOn
  intro ε hε
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
  apply itoTaylorRemainder_norm_le f hf x (y-x) ε hε.le
  intro t ht
  have hz : x + t • (y-x) ∈ K :=
    hconv.add_smul_mem hx (by simpa using hy) ht
  have hd : dist (x+t•(y-x)) x < δ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt hxy
  simpa only [dist_eq_norm] using (hu _ hz x hx hd).le

end
end GinibrePoincare
