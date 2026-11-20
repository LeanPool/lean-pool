/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryLangevinContraction.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryLangevinEnergy

/-! # Synchronous contraction of the actual gradient Langevin flow -/

@[expose] public section

open Set
open scoped ContDiff NNReal Topology
namespace GinibrePoincare
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The literal Langevin flow contracts under common continuous additive
noise, with no global upper Hessian bound and exact exponent `κ`. -/
theorem bakryEmeryLangevin_synchronous_contraction (W : E → ℝ) (κ : ℝ)
    (hW : Differentiable ℝ W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (N X Y : ℝ → E) (T : ℝ) (hT : 0 ≤ T)
    (hX : ContinuousOn X (Icc 0 T)) (hY : ContinuousOn Y (Icc 0 T))
    (hEqX : ∀ t ∈ Ioo 0 T, HasDerivAt X (bakryEmeryLangevinDrift W (X t + N t)) t)
    (hEqY : ∀ t ∈ Ioo 0 T, HasDerivAt Y (bakryEmeryLangevinDrift W (Y t + N t)) t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    Real.exp (2 * κ * t) * ‖X t - Y t‖ ^ 2 ≤ ‖X 0 - Y 0‖ ^ 2 := by
  let D : ℝ → ℝ := fun s => Real.exp (2 * κ * s) * ‖X s - Y s‖ ^ 2
  have hDc : ContinuousOn D (Icc 0 T) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      ((hX.sub hY).norm.pow 2)
  have hd (s : ℝ) (hs : s ∈ Ioo 0 T) : HasDerivAt D
      (2 * Real.exp (2 * κ * s) * (κ * ‖X s - Y s‖ ^ 2 +
        inner ℝ (X s - Y s)
          (bakryEmeryLangevinDrift W (X s + N s) - bakryEmeryLangevinDrift W (Y s + N s)))) s := by
    have he := (((hasDerivAt_id s).const_mul (2 * κ)).exp).mul
      (((hEqX s hs).sub (hEqY s hs)).norm_sq)
    convert he using 1 <;> dsimp [D] <;> try ring_nf
    funext x
    simp only [Pi.mul_apply]
  have hmono : AntitoneOn D (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hDc
    · intro s hs
      have hs' : s ∈ Ioo 0 T := by simpa only [interior_Icc] using hs
      exact (hd s hs').differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Ioo 0 T := by simpa only [interior_Icc] using hs
      rw [(hd s hs').deriv]
      have hh := bakryEmeryLangevinDrift_dissipative W κ hc (X s + N s) (Y s + N s)
        (hW _) (hW _)
      simp only [add_sub_add_right_eq_sub] at hh
      apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
      linarith
  have hb := hmono (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩) ht ht.1
  simpa [D] using hb

omit [FiniteDimensional ℝ E] in
/-- Pathwise uniqueness for the actual gradient Langevin equation driven by
one continuous additive noise path. -/
theorem bakryEmeryLangevin_pathwise_unique (W : E → ℝ) (κ : ℝ)
    (hW : Differentiable ℝ W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (N X Y : ℝ → E) (T : ℝ) (hT : 0 ≤ T)
    (hX : ContinuousOn X (Icc 0 T)) (hY : ContinuousOn Y (Icc 0 T))
    (hEqX : ∀ t ∈ Ioo 0 T, HasDerivAt X (bakryEmeryLangevinDrift W (X t + N t)) t)
    (hEqY : ∀ t ∈ Ioo 0 T, HasDerivAt Y (bakryEmeryLangevinDrift W (Y t + N t)) t)
    (h0 : X 0 = Y 0) : ∀ t ∈ Icc 0 T, X t = Y t := by
  intro t ht
  have h := bakryEmeryLangevin_synchronous_contraction W κ hW hc N X Y T hT hX hY hEqX hEqY t ht
  rw [h0, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
  have he : ‖X t - Y t‖ ^ 2 = 0 := by
    have hp := Real.exp_pos (2 * κ * t)
    nlinarith [sq_nonneg ‖X t - Y t‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp he))

end
end GinibrePoincare
