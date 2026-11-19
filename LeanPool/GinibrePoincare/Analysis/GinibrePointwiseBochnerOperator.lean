/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibrePointwiseBochnerOperator.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibrePointwiseBochnerDirectional

/-!
# Ginibre pointwise Bochner operator

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `bochnerCoordinateOperator_directional_commutation`,
`bochnerCoordinateOperator_mul`, `bochnerCoordinateOperator_mul_at`.
-/

@[expose] public section

open scoped ContDiff BigOperators Topology
open Filter
namespace GinibrePoincare
noncomputable section
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- Actual finite-coordinate diffusion operator with scalar diffusion constant. -/
def bochnerCoordinateOperator (e : ι → E) (c : ℝ) (b : ι → E → ℝ)
    (f : E → ℝ) (x : E) : ℝ :=
  c*(∑ i, bochnerDirectionalDerivative (e i) (bochnerDirectionalDerivative (e i) f) x)-
    ∑ i, b i x*bochnerDirectionalDerivative (e i) f x

theorem bochnerDirectionalDerivative_third_comm (u v : E) (f : E → ℝ) (x : E)
    (hf : ContDiff ℝ ∞ f) :
    bochnerDirectionalDerivative u (bochnerDirectionalDerivative v (bochnerDirectionalDerivative v
        f)) x=
      bochnerDirectionalDerivative v (bochnerDirectionalDerivative v (bochnerDirectionalDerivative u
          f)) x := by
  rw [bochnerDirectionalDerivative_comm u v (bochnerDirectionalDerivative v f) x
    (bochnerDirectionalDerivative_contDiff v f hf).contDiffAt]
  have he : bochnerDirectionalDerivative u (bochnerDirectionalDerivative v f)=
      bochnerDirectionalDerivative v (bochnerDirectionalDerivative u f) := by
    funext y
    exact bochnerDirectionalDerivative_comm u v f y hf.contDiffAt
  rw [he]

theorem bochnerCoordinateOperator_directional_commutation (e : ι → E) (c : ℝ)
    (b : ι → E → ℝ) (f : E → ℝ) (x u : E) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ i, DifferentiableAt ℝ (b i) x) :
    bochnerDirectionalDerivative u (bochnerCoordinateOperator e c b f) x=
      bochnerCoordinateOperator e c b (bochnerDirectionalDerivative u f) x-
        ∑ i, bochnerDirectionalDerivative u (b i) x*bochnerDirectionalDerivative (e i) f x := by
  have hd (v : E) : ContDiff ℝ ∞ (bochnerDirectionalDerivative v f) :=
      bochnerDirectionalDerivative_contDiff v f hf
  have hdd (v : E) : ContDiff ℝ ∞ (bochnerDirectionalDerivative v (bochnerDirectionalDerivative v
      f)) :=
    bochnerDirectionalDerivative_contDiff v _ (hd v)
  have hs1 : DifferentiableAt ℝ (fun y => ∑ i, bochnerDirectionalDerivative (e i)
      (bochnerDirectionalDerivative (e i) f) y) x :=
    DifferentiableAt.fun_sum (fun i _ => (hdd (e i)).differentiable (by simp) x)
  have hs2 : DifferentiableAt ℝ (fun y => ∑ i, b i y*bochnerDirectionalDerivative (e i) f y) x :=
    DifferentiableAt.fun_sum (fun i _ => (hb i).mul ((hd (e i)).differentiable (by simp) x))
  unfold bochnerCoordinateOperator
  rw [bochnerDirectionalDerivative_sub _ _ _ _ (hs1.const_mul c) hs2,
    bochnerDirectionalDerivative_const_mul _ _ _ _ hs1,
    bochnerDirectionalDerivative_sum _ _ _ (fun i => (hdd (e i)).differentiable (by simp) x),
    bochnerDirectionalDerivative_sum u (fun i y => b i y*bochnerDirectionalDerivative (e i) f y) x
      (fun i => (hb i).mul ((hd (e i)).differentiable (by simp) x))]
  simp_rw [bochnerDirectionalDerivative_mul u (b _) _ x (hb _) ((hd _).differentiable (by simp) x),
    bochnerDirectionalDerivative_third_comm u _ f x hf,
    bochnerDirectionalDerivative_comm u _ f x hf.contDiffAt]
  rw [Finset.sum_add_distrib]
  ring

theorem bochnerDirectionalDerivative_second_mul (u : E) (f g : E → ℝ) (x : E)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    bochnerDirectionalDerivative u (bochnerDirectionalDerivative u (fun y => f y*g y)) x=
      bochnerDirectionalDerivative u (bochnerDirectionalDerivative u f) x*g x+
        2*bochnerDirectionalDerivative u f x*bochnerDirectionalDerivative u g x+
          f x*bochnerDirectionalDerivative u (bochnerDirectionalDerivative u g) x := by
  have hdf := bochnerDirectionalDerivative_contDiff u f hf
  have hdg := bochnerDirectionalDerivative_contDiff u g hg
  have he : bochnerDirectionalDerivative u (fun y => f y*g y)=
      (fun y => bochnerDirectionalDerivative u f y*g y+f y*bochnerDirectionalDerivative u g y) := by
    funext y
    exact bochnerDirectionalDerivative_mul u f g y (hf.differentiable (by simp) y)
        (hg.differentiable (by simp) y)
  rw [he, bochnerDirectionalDerivative_add u (fun y => bochnerDirectionalDerivative u f y*g y) (fun
      y => f y*bochnerDirectionalDerivative u g y) x
    ((hdf.differentiable (by simp) x).mul (hg.differentiable (by simp) x))
    ((hf.differentiable (by simp) x).mul (hdg.differentiable (by simp) x)),
    bochnerDirectionalDerivative_mul u (bochnerDirectionalDerivative u f) g x (hdf.differentiable
        (by simp) x) (hg.differentiable (by simp) x),
    bochnerDirectionalDerivative_mul u f (bochnerDirectionalDerivative u g) x (hf.differentiable (by
        simp) x) (hdg.differentiable (by simp) x)]
  ring

theorem bochnerCoordinateOperator_mul (e : ι → E) (c : ℝ) (b : ι → E → ℝ)
    (f g : E → ℝ) (x : E) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    bochnerCoordinateOperator e c b (fun y => f y*g y) x=
      f x*bochnerCoordinateOperator e c b g x+g x*bochnerCoordinateOperator e c b f x+
        2*c*∑ i, bochnerDirectionalDerivative (e i) f x*bochnerDirectionalDerivative (e i) g x := by
  unfold bochnerCoordinateOperator
  simp_rw [bochnerDirectionalDerivative_second_mul _ f g x hf hg,
    bochnerDirectionalDerivative_mul _ f g x (hf.differentiable (by simp) x) (hg.differentiable (by
        simp) x)]
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, ← Finset.sum_mul] at *
  have hs (a : ℝ) (h : E → ℝ) : (∑ i, a*b i x*bochnerDirectionalDerivative (e i) h x)=a*∑ i, b i
      x*bochnerDirectionalDerivative (e i) h x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  ring_nf
  rw [hs (g x) f, hs (f x) g]
  simp only [← Finset.sum_mul]
  ring

theorem bochnerDirectionalDerivative_second_mul_at (u : E) (f g : E → ℝ) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    bochnerDirectionalDerivative u (bochnerDirectionalDerivative u (fun y => f y*g y)) x=
      bochnerDirectionalDerivative u (bochnerDirectionalDerivative u f) x*g x+
        2*bochnerDirectionalDerivative u f x*bochnerDirectionalDerivative u g x+
          f x*bochnerDirectionalDerivative u (bochnerDirectionalDerivative u g) x := by
  have hdf := bochnerDirectionalDerivative_contDiffAt u f x hf
  have hdg := bochnerDirectionalDerivative_contDiffAt u g x hg
  have hfe : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := by
    filter_upwards [(hf.of_le (by simp : (1 : WithTop ℕ∞)≤∞)).eventually (by simp)] with y hy
    exact hy.differentiableAt (by simp)
  have hge : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y := by
    filter_upwards [(hg.of_le (by simp : (1 : WithTop ℕ∞)≤∞)).eventually (by simp)] with y hy
    exact hy.differentiableAt (by simp)
  have he : bochnerDirectionalDerivative u (fun y => f y*g y)=ᶠ[𝓝 x]
      (fun y => bochnerDirectionalDerivative u f y*g y+f y*bochnerDirectionalDerivative u g y) := by
    filter_upwards [hfe, hge] with y hy hy'
    exact bochnerDirectionalDerivative_mul u f g y hy hy'
  have hh : bochnerDirectionalDerivative u (bochnerDirectionalDerivative u (fun y => f y*g y)) x=
    bochnerDirectionalDerivative u (fun y => bochnerDirectionalDerivative u f y*g y+f
        y*bochnerDirectionalDerivative u g y) x := by
    exact congrArg (fun a : E →L[ℝ] ℝ => a u) (he.fderiv_eq (𝕜 := ℝ))
  rw [hh, bochnerDirectionalDerivative_add u (fun y => bochnerDirectionalDerivative u f y*g y) (fun
      y => f y*bochnerDirectionalDerivative u g y) x
    ((hdf.differentiableAt (by simp)).mul (hg.differentiableAt (by simp)))
    ((hf.differentiableAt (by simp)).mul (hdg.differentiableAt (by simp))),
    bochnerDirectionalDerivative_mul u (bochnerDirectionalDerivative u f) g x (hdf.differentiableAt
        (by simp)) (hg.differentiableAt (by simp)),
    bochnerDirectionalDerivative_mul u f (bochnerDirectionalDerivative u g) x (hf.differentiableAt
        (by simp)) (hdg.differentiableAt (by simp))]
  ring

theorem bochnerCoordinateOperator_mul_at (e : ι → E) (c : ℝ) (b : ι → E → ℝ)
    (f g : E → ℝ) (x : E) (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    bochnerCoordinateOperator e c b (fun y => f y*g y) x=
      f x*bochnerCoordinateOperator e c b g x+g x*bochnerCoordinateOperator e c b f x+
        2*c*∑ i, bochnerDirectionalDerivative (e i) f x*bochnerDirectionalDerivative (e i) g x := by
  unfold bochnerCoordinateOperator
  simp_rw [bochnerDirectionalDerivative_second_mul_at _ f g x hf hg,
    bochnerDirectionalDerivative_mul _ f g x (hf.differentiableAt (by simp)) (hg.differentiableAt
        (by simp))]
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, ← Finset.sum_mul] at *
  have hs (a : ℝ) (h : E → ℝ) : (∑ i, a*b i x*bochnerDirectionalDerivative (e i) h x)=a*∑ i, b i
      x*bochnerDirectionalDerivative (e i) h x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  ring_nf
  rw [hs (g x) f, hs (f x) g]
  simp only [← Finset.sum_mul]
  ring

end
end GinibrePoincare
