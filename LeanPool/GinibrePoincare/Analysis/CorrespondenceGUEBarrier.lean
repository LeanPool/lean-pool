/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUEBarrier.lean.
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
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.Piecewise
/-!
# Correspondence GUE barrier

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueLogBarrier_convex`.
-/

@[expose] public section
open Set
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

private theorem hasDerivAt_splice {a x : ℝ} {f g df dg : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (df x) x)
    (hg : ∀ x, a ≤ x → HasDerivAt g (dg x) x)
    (hfg : f a = g a) (hd : df a = dg a) :
    HasDerivAt (fun y => if y≤a then f y else g y)
      (if x≤a then df x else dg x) x := by
  by_cases hlt : x<a
  · rw [ite_eq_left hlt.le]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hlt] with y hy
    simp [hy.le]
  by_cases hgt : a<x
  · rw [ite_eq_right (not_le.mpr hgt)]
    apply (hg x hgt.le).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hgt] with y hy
    simp [not_le.mpr hy]
  have hx : x=a := le_antisymm (not_lt.mp hgt) (not_lt.mp hlt)
  subst x
  rw [ite_eq_left le_rfl]
  have hlow : HasDerivWithinAt (fun y => if y≤a then f y else g y) (df a) (Iic a) a :=
    (hf a).hasDerivWithinAt.congr_of_mem (fun y hy => by simp [show y≤a from hy]) le_rfl
  have hhigh : HasDerivWithinAt (fun y => if y≤a then f y else g y) (df a) (Ici a) a := by
    rw [hd]
    apply (hg a le_rfl).hasDerivWithinAt.congr_of_mem _ le_rfl
    intro y hy
    by_cases h : y≤a
    · have he : y=a := le_antisymm h hy
      simpa [he] using hfg
    · simp [h]
  have hu := hlow.union hhigh
  rw [Iic_union_Ici] at hu
  exact hu.hasDerivAt (by simp)

private theorem continuous_splice {a : ℝ} {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : ContinuousOn g (Ici a)) (hfg : f a = g a) :
    Continuous (fun y => if y≤a then f y else g y) := by
  apply continuous_if
  · intro y hy
    change y ∈ frontier (Iic a) at hy
    have he : y=a := by simpa only [frontier_Iic, mem_singleton_iff] using hy
    simpa [he] using hfg
  · change ContinuousOn f (closure (Iic a))
    simpa only [closure_Iic] using hf.continuousOn (s := Iic a)
  · change ContinuousOn g (closure ((Iic a)ᶜ))
    simpa only [compl_Iic, closure_Ioi] using hg

/-- C² convex extension of -log from [ε,∞), used to approximate the ordered
GUE's singular chamber potential without altering its curvature. -/
def gueLogBarrier (ε u : ℝ) : ℝ :=
  if u≤ε then -Real.log ε-(u-ε)/ε+(u-ε)^2/(2*ε^2) else -Real.log u

/-- The derivative of `gueLogBarrier ε`: `-1/ε + (u - ε)/ε^2` for `u ≤ ε` and `-1/u` otherwise. -/
def gueLogBarrierDeriv (ε u : ℝ) : ℝ :=
  if u≤ε then -1/ε+(u-ε)/ε^2 else -1/u

/-- The second derivative of `gueLogBarrier ε`: `1/ε^2` for `u ≤ ε` and `1/u^2` otherwise. -/
def gueLogBarrierDerivTwo (ε u : ℝ) : ℝ :=
  if u≤ε then 1/ε^2 else 1/u^2

theorem gueLogBarrier_hasDerivAt {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    HasDerivAt (gueLogBarrier ε) (gueLogBarrierDeriv ε u) u := by
  unfold gueLogBarrier gueLogBarrierDeriv
  apply hasDerivAt_splice
  · intro x
    convert ((hasDerivAt_const x (-Real.log ε)).sub
      (((hasDerivAt_id x).sub_const ε).div_const ε)).add
      ((((hasDerivAt_id x).sub_const ε).pow 2).div_const (2*ε^2)) using 1 <;>
      (try funext y) <;> dsimp; field_simp [hε.ne']; ring
  · intro x hx
    convert (Real.hasDerivAt_log (ne_of_gt (hε.trans_le hx))).neg using 1; simp [one_div,
        neg_div]
  · simp
  · simp

theorem gueLogBarrierDeriv_hasDerivAt {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    HasDerivAt (gueLogBarrierDeriv ε) (gueLogBarrierDerivTwo ε u) u := by
  unfold gueLogBarrierDeriv gueLogBarrierDerivTwo
  apply hasDerivAt_splice
  · intro x
    convert (hasDerivAt_const x (-1/ε)).add
      (((hasDerivAt_id x).sub_const ε).div_const (ε^2)) using 1 <;> (try funext y) <;> simp
  · intro x hx
    convert (hasDerivAt_const x (-1 : ℝ)).div (hasDerivAt_id x)
      (ne_of_gt (hε.trans_le hx)) using 1 <;> (try funext y) <;> simp
  · simp
  · simp

theorem gueLogBarrier_contDiff {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 2 (gueLogBarrier ε) := by
  have he : deriv (gueLogBarrier ε)=gueLogBarrierDeriv ε :=
    funext (fun u => (gueLogBarrier_hasDerivAt hε u).deriv)
  have he2 : deriv (gueLogBarrierDeriv ε)=gueLogBarrierDerivTwo ε :=
    funext (fun u => (gueLogBarrierDeriv_hasDerivAt hε u).deriv)
  rw [show (2 : ℕ∞ω) = 1+1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun u => (gueLogBarrier_hasDerivAt hε u).differentiableAt, by simp,?_⟩
  rw [he, contDiff_one_iff_deriv, he2]
  refine ⟨fun u => (gueLogBarrierDeriv_hasDerivAt hε u).differentiableAt,?_⟩
  unfold gueLogBarrierDerivTwo
  apply continuous_splice continuous_const
  · apply continuousOn_const.div (continuousOn_id.pow 2)
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (hε.trans_le hx))
  · rfl

theorem gueLogBarrier_convex {ε : ℝ} (hε : 0 < ε) : ConvexOn ℝ univ (gueLogBarrier ε) := by
  have he : deriv (gueLogBarrier ε)=gueLogBarrierDeriv ε :=
    funext (fun u => (gueLogBarrier_hasDerivAt hε u).deriv)
  apply convexOn_of_deriv2_nonneg convex_univ (gueLogBarrier_contDiff hε).continuous.continuousOn
    (fun u _ => (gueLogBarrier_hasDerivAt hε u).differentiableAt.differentiableWithinAt)
  · rw [he]
    exact fun u _ => (gueLogBarrierDeriv_hasDerivAt hε u).differentiableAt.differentiableWithinAt
  · intro u hu
    change 0 ≤ deriv (deriv (gueLogBarrier ε)) u
    rw [he, (gueLogBarrierDeriv_hasDerivAt hε u).deriv]
    unfold gueLogBarrierDerivTwo
    split_ifs <;> positivity

end
end GinibrePoincare
