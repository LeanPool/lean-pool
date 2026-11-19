/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibrePointwiseBochnerDirectional.lean.
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

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Tactic

/-!
# Ginibre pointwise Bochner directional

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `bochnerDirectionalDerivative_sub`, `bochnerDirectionalDerivative_const_mul`,
`bochnerDirectionalDerivative_mul`, `bochnerDirectionalDerivative_sum`.
-/

@[expose] public section

open scoped ContDiff BigOperators
namespace GinibrePoincare
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The directional derivative `fderiv ℝ f x v` of `f` at `x` in the direction `v`. -/
def bochnerDirectionalDerivative (v : E) (f : E → ℝ) (x : E) : ℝ := fderiv ℝ f x v

theorem bochnerDirectionalDerivative_contDiffAt (v : E) (f : E → ℝ) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) : ContDiffAt ℝ ∞ (bochnerDirectionalDerivative v f) x := by
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

theorem bochnerDirectionalDerivative_contDiff (v : E) (f : E → ℝ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (bochnerDirectionalDerivative v f) := by
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem bochnerDirectionalDerivative_iterated (u v : E) (f : E → ℝ) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) :
    bochnerDirectionalDerivative u (bochnerDirectionalDerivative v f) x=
      fderiv ℝ (fderiv ℝ f) x u v := by
  unfold bochnerDirectionalDerivative
  rw [fderiv_clm_apply ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
      (differentiableAt_const v)]
  simp

theorem bochnerDirectionalDerivative_comm (u v : E) (f : E → ℝ) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) :
    bochnerDirectionalDerivative u (bochnerDirectionalDerivative v f) x=
      bochnerDirectionalDerivative v (bochnerDirectionalDerivative u f) x := by
  rw [bochnerDirectionalDerivative_iterated u v f x hf,
    bochnerDirectionalDerivative_iterated v u f x hf]
  exact (hf.isSymmSndFDerivAt (by simp)).eq u v

theorem bochnerDirectionalDerivative_add (u : E) (f g : E → ℝ) (x : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    bochnerDirectionalDerivative u (fun x => f x+g x) x=
      bochnerDirectionalDerivative u f x+bochnerDirectionalDerivative u g x := by
  unfold bochnerDirectionalDerivative
  rw [fderiv_fun_add hf hg]
  rfl

theorem bochnerDirectionalDerivative_sub (u : E) (f g : E → ℝ) (x : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    bochnerDirectionalDerivative u (fun x => f x-g x) x=
      bochnerDirectionalDerivative u f x-bochnerDirectionalDerivative u g x := by
  unfold bochnerDirectionalDerivative
  rw [fderiv_fun_sub hf hg]
  rfl

theorem bochnerDirectionalDerivative_const_mul (u : E) (c : ℝ) (f : E → ℝ) (x : E)
    (hf : DifferentiableAt ℝ f x) :
    bochnerDirectionalDerivative u (fun x => c*f x) x=c*bochnerDirectionalDerivative u f x := by
  unfold bochnerDirectionalDerivative
  rw [fderiv_const_mul hf]
  rfl

theorem bochnerDirectionalDerivative_mul (u : E) (f g : E → ℝ) (x : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    bochnerDirectionalDerivative u (fun x => f x*g x) x=
      bochnerDirectionalDerivative u f x*g x+f x*bochnerDirectionalDerivative u g x := by
  unfold bochnerDirectionalDerivative
  rw [fderiv_fun_mul hf hg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem bochnerDirectionalDerivative_sum {ι : Type*} [Fintype ι]
    (u : E) (f : ι → E → ℝ) (x : E) (hf : ∀ i, DifferentiableAt ℝ (f i) x) :
    bochnerDirectionalDerivative u (fun x => ∑ i, f i x) x=∑ i, bochnerDirectionalDerivative u (f i)
        x := by
  unfold bochnerDirectionalDerivative
  rw [fderiv_fun_sum (fun i _ => hf i)]
  simp

end
end GinibrePoincare
