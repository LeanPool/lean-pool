/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticDissipativeUniqueness.lean.
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
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Hilbert-space orbit uniqueness from actual differential dissipation.
This is used after identification of the full resolvent domain. -/

@[expose] public section
open Set
namespace GinibrePoincare

theorem realHilbert_orbit_unique_of_dissipative_derivative {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y vx vy : ℝ → E) (T : ℝ) (hT : 0 ≤ T)
    (hx : ContinuousOn x (Icc 0 T)) (hy : ContinuousOn y (Icc 0 T))
    (hdx : ∀ s ∈ Ioo 0 T, HasDerivAt x (vx s) s)
    (hdy : ∀ s ∈ Ioo 0 T, HasDerivAt y (vy s) s)
    (hdiss : ∀ s ∈ Ioo 0 T, inner ℝ (x s - y s) (vx s - vy s) ≤ 0)
    (hinit : x 0 = y 0) : ∀ s ∈ Icc 0 T, x s=y s := by
  let F := fun s => ‖x s-y s‖^2
  have hd (s : ℝ) (hs : s ∈ Ioo 0 T) : HasDerivAt F
      (2*inner ℝ (x s-y s) (vx s-vy s)) s := ((hdx s hs).sub (hdy s hs)).norm_sq
  have hdiff : DifferentiableOn ℝ F (interior (Icc 0 T)) := by
    rw [interior_Icc]
    exact fun s hs => (hd s hs).differentiableAt.differentiableWithinAt
  have hnonpos : ∀ s ∈ interior (Icc 0 T), deriv F s ≤ 0 := by
    rw [interior_Icc]
    intro s hs
    rw [(hd s hs).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (hdiss s hs)
  have hanti : AntitoneOn F (Icc 0 T) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 T) ((hx.sub hy).norm.pow 2) hdiff hnonpos
  intro s hs
  have hh := hanti ⟨le_rfl, hT⟩ hs hs.1
  have hz : F 0=0 := by simp [F, hinit]
  rw [hz] at hh
  have hn : ‖x s-y s‖=0 := by dsimp [F] at hh; nlinarith [norm_nonneg (x s-y s)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end GinibrePoincare
