/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryLangevinEnergy.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryLangevinLocal
public import LeanPool.GinibrePoincare.Analysis.BakryEmeryDirectionalCurvature

/-! # Finite-time confinement of the actual driven Langevin equation -/

@[expose] public section

open Set Metric
open scoped ContDiff NNReal Topology
namespace GinibrePoincare
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Strong convexity gives dissipativity of the actual Euclidean gradient drift. -/
theorem bakryEmeryLangevinDrift_dissipative (W : E → ℝ) (κ : ℝ)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (x y : E) (hx : DifferentiableAt ℝ W x) (hy : DifferentiableAt ℝ W y) :
    inner ℝ (x - y) (bakryEmeryLangevinDrift W x - bakryEmeryLangevinDrift W y) ≤
      -κ * ‖x - y‖ ^ 2 := by
  have h := bakryEmery_gradient_strong_monotonicity W κ hc y x hy hx
  have he : inner ℝ (x - y) (bakryEmeryLangevinDrift W x - bakryEmeryLangevinDrift W y) =
      -((fderiv ℝ W x) (x - y) - (fderiv ℝ W y) (x - y)) := by
    simp only [bakryEmeryLangevinDrift, inner_sub_right, inner_neg_right]
    simp only [inner_gradient_right, conj_trivial]
    ring
  rw [he]
  linarith

omit [FiniteDimensional ℝ E] in
/-- Actual continuous forcing and strong confinement prevent finite-time
escape: the corrected trajectory's squared norm has an explicit linear bound.
The coefficient is derived from the drift evaluated on the compact noise path. -/
theorem bakryEmeryLangevin_driven_energy_bound (W : E → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (N Y : ℝ → E) (hN : Continuous N) (T : ℝ) (hT : 0 ≤ T)
    (hY : ContinuousOn Y (Icc 0 T))
    (hEq : ∀ s ∈ Ioo 0 T, HasDerivAt Y (bakryEmeryLangevinDrift W (Y s + N s)) s) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ s ∈ Icc 0 T, ‖bakryEmeryLangevinDrift W (N s)‖ ≤ C) ∧
      ∀ t ∈ Icc 0 T, ‖Y t‖ ^ 2 ≤ ‖Y 0‖ ^ 2 + (C ^ 2 / κ) * t := by
  have hb : Continuous (bakryEmeryLangevinDrift W) := continuous_iff_continuousAt.mpr
    (fun x => (bakryEmeryLangevinDrift_contDiffAt W x hW.contDiffAt).continuousAt)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn
    (hb.comp hN).continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, hT⟩)
  refine ⟨C, hC0, hC, ?_⟩
  have hd (s : ℝ) (hs : s ∈ Ioo 0 T) :
      HasDerivAt (fun t => ‖Y t‖ ^ 2)
        (2 * inner ℝ (Y s) (bakryEmeryLangevinDrift W (Y s + N s))) s :=
    (hEq s hs).norm_sq
  have hbound (s : ℝ) (hs : s ∈ Ioo 0 T) :
      2 * inner ℝ (Y s) (bakryEmeryLangevinDrift W (Y s + N s)) ≤ C ^ 2 / κ := by
    have hdis := bakryEmeryLangevinDrift_dissipative W κ hc (Y s + N s) (N s)
      ((hW.differentiable (by norm_num)) _) ((hW.differentiable (by norm_num)) _)
    simp only [add_sub_cancel_right, inner_sub_right] at hdis
    have hnoise : inner ℝ (Y s) (bakryEmeryLangevinDrift W (N s)) ≤ ‖Y s‖ * C :=
      (real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hC s ⟨hs.1.le, hs.2.le⟩) (norm_nonneg _))
    have hcancel : κ * (C ^ 2 / κ) = C ^ 2 := mul_div_cancel₀ _ hκ.ne'
    have hfirst : 2 * inner ℝ (Y s) (bakryEmeryLangevinDrift W (Y s + N s)) ≤
        -2 * κ * ‖Y s‖ ^ 2 + 2 * ‖Y s‖ * C := by linarith
    have hscaled := mul_le_mul_of_nonneg_left hfirst hκ.le
    apply (mul_le_mul_iff_right₀ hκ).mp
    nlinarith [sq_nonneg (κ * ‖Y s‖ - C), sq_nonneg (‖Y s‖)]
  intro t ht
  have hfinal := (convex_Icc (0 : ℝ) T).image_sub_le_mul_sub_of_deriv_le
    (hY.norm.pow 2) (C := C ^ 2 / κ)
    (by
      intro s hs
      have hs' : s ∈ Ioo 0 T := by simpa only [interior_Icc] using hs
      exact (hd s hs').differentiableAt.differentiableWithinAt)
    (by
      intro s hs
      have hs' : s ∈ Ioo 0 T := by simpa only [interior_Icc] using hs
      change deriv (fun t => ‖Y t‖ ^ 2) s ≤ C ^ 2 / κ
      rw [(hd s hs').deriv]
      exact hbound s hs')
    0 ⟨le_rfl, hT⟩ t ht ht.1
  simp only [sub_zero, Pi.pow_apply] at hfinal
  linarith

end
end GinibrePoincare
