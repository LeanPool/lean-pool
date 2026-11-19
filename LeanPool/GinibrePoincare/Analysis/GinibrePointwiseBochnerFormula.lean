/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibrePointwiseBochnerFormula.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibrePointwiseBochnerOperator

/-!
# Ginibre pointwise Bochner formula

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `bochnerGamma_eq`, `bochnerGammaTwo_eq`.
-/

@[expose] public section

open scoped ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
variable {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [Fintype κ]

/-- Pointwise carré du champ defined through the actual diffusion operator. -/
def bochnerGamma (e : ι → E) (c : ℝ) (b : ι → E → ℝ) (f g : E → ℝ) (x : E) :=
 (bochnerCoordinateOperator e c b (fun y => f y*g y) x -
 f x*bochnerCoordinateOperator e c b g x-g x*bochnerCoordinateOperator e c b f x)/2

theorem bochnerGamma_eq (e : ι → E) (c : ℝ) (b : ι → E → ℝ)
 (f g : E → ℝ) (x : E) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
 bochnerGamma e c b f g x=c*∑ i, bochnerDirectionalDerivative (e i) f x*bochnerDirectionalDerivative
     (e i) g x := by
 unfold bochnerGamma
 rw [bochnerCoordinateOperator_mul e c b f g x hf hg]
 ring

theorem bochnerCoordinateOperator_const_mul (e : ι → E) (c a : ℝ)
 (b : ι → E → ℝ) (f : E → ℝ) (x : E) (hf : ContDiff ℝ ∞ f) :
 bochnerCoordinateOperator e c b (fun y => a*f y) x=a*bochnerCoordinateOperator e c b f x := by
 have hd i := bochnerDirectionalDerivative_contDiff (e i) f hf
 have he i : bochnerDirectionalDerivative (e i) (fun y => a*f y)=fun y =>
     a*bochnerDirectionalDerivative (e i) f y := by
  funext y
  exact bochnerDirectionalDerivative_const_mul _ _ _ _ (hf.differentiable (by simp) y)
 unfold bochnerCoordinateOperator
 simp_rw [he, bochnerDirectionalDerivative_const_mul _ a _ x ((hd _).differentiable (by simp) x)]
 simp only [← Finset.mul_sum]
 ring_nf
 congr 1
 rw [Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro i hi
 ring

theorem bochnerCoordinateOperator_sum (e : ι → E) (c : ℝ)
 (b : ι → E → ℝ) (f : κ → E → ℝ) (x : E) (hf : ∀ k, ContDiff ℝ ∞ (f k)) :
 bochnerCoordinateOperator e c b (fun y => ∑ k, f k y) x=∑ k, bochnerCoordinateOperator e c b (f k)
     x := by
 have hd i k := bochnerDirectionalDerivative_contDiff (e i) (f k) (hf k)
 have he i : bochnerDirectionalDerivative (e i) (fun y => ∑ k, f k y)=fun y => ∑ k,
     bochnerDirectionalDerivative (e i) (f k) y := by
  funext y
  exact bochnerDirectionalDerivative_sum _ _ _ (fun k => (hf k).differentiable (by simp) y)
 unfold bochnerCoordinateOperator
 simp_rw [he, bochnerDirectionalDerivative_sum _ _ x (fun k => (hd _ k).differentiable (by simp) x)]
 simp only [Finset.mul_sum, Finset.sum_sub_distrib]
 rw [Finset.sum_comm]
 congr 1
 rw [Finset.sum_comm]

/-- Iterated carré du champ expressed by the actual operator and its gradient. -/
def bochnerGammaTwo (e : ι → E) (c : ℝ) (b : ι → E → ℝ) (f : E → ℝ) (x : E) :=
 (bochnerCoordinateOperator e c b (fun y => c*∑ i, (bochnerDirectionalDerivative (e i) f y)^2) x)/2-
 c*∑ i, bochnerDirectionalDerivative (e i) f x*bochnerDirectionalDerivative (e i)
     (bochnerCoordinateOperator e c b f) x

theorem bochnerGammaTwo_eq (e : ι → E) (c : ℝ) (b : ι → E → ℝ)
 (f : E → ℝ) (x : E) (hf : ContDiff ℝ ∞ f)
 (hb : ∀ i, DifferentiableAt ℝ (b i) x) :
 bochnerGammaTwo e c b f x=
 c^2*∑ i, ∑ j, (bochnerDirectionalDerivative (e j) (bochnerDirectionalDerivative (e i) f) x)^2+
 c*∑ i, ∑ j, bochnerDirectionalDerivative (e i) f x*bochnerDirectionalDerivative (e i) (b j)
     x*bochnerDirectionalDerivative (e j) f x := by
 have hd i := bochnerDirectionalDerivative_contDiff (e i) f hf
 have hs : ContDiff ℝ ∞ (fun y => ∑ i, (bochnerDirectionalDerivative (e i) f y)^2) :=
  ContDiff.sum (fun i _ => (hd i).pow 2)
 unfold bochnerGammaTwo
 rw [bochnerCoordinateOperator_const_mul e c c b _ x hs,
   bochnerCoordinateOperator_sum e c b _ x (fun i => (hd i).pow 2)]
 have hp i : bochnerCoordinateOperator e c b (fun y => (bochnerDirectionalDerivative (e i) f y)^2)
     x=
  2*bochnerDirectionalDerivative (e i) f x*bochnerCoordinateOperator e c b
      (bochnerDirectionalDerivative (e i) f) x+
  2*c*∑ j, (bochnerDirectionalDerivative (e j) (bochnerDirectionalDerivative (e i) f) x)^2 := by
  simpa only [pow_two] using (bochnerCoordinateOperator_mul e c b (bochnerDirectionalDerivative (e
      i) f) (bochnerDirectionalDerivative (e i) f) x (hd i) (hd i)) |>.trans (by ring)
 simp_rw [hp, bochnerCoordinateOperator_directional_commutation e c b f x _ hf hb,
   mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
 simp only [Finset.mul_sum]
 simp only [mul_assoc, ← Finset.mul_sum]
 ring

end
end GinibrePoincare
