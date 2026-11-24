/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.CircleSubmean
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.SubmeanLaplacian

/-!
# Nonnegative Levi forms give actual plurisubharmonic functions

This implication joins the actual real Hessian chain rule, the classical
Laplacian submean theorem, and the extended-real disc definition. No PSH
or current correspondence is supplied as an assumption.
-/

@[expose] public section

open Set Metric Laplacian

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The smooth Levi criterion implies the extended-real disc inequalities. -/
theorem discPshOn_of_levi_nonneg {u : E → ℝ} {U : Set E}
    (hu : ContDiff ℝ 2 u) (hL : ∀ x ∈ U, ∀ v : E, 0 ≤ leviForm u x v) :
    DiscPshOn (fun y => (u y : EReal)) U := by
  apply discPshOn_of_circleAverage hu.continuous
  intro x v r hr hD
  have hline : ContDiff ℝ 2 (fun z : ℂ => u (x + z • v)) := by
    exact hu.comp (contDiff_const.add (complexLineLinear v).contDiff)
  have hΔ : ∀ z ∈ closedBall (0 : ℂ) r,
      0 ≤ Δ (fun t : ℂ => u (x + t • v)) z := by
    intro z hz
    apply (laplacian_complexLine_nonneg_iff hu x v z).mpr
    exact hL _ (hD ⟨z, hz, rfl⟩) v
  simpa only [zero_smul, add_zero] using
    submean_of_laplacian_nonneg hline 0 hr.le hΔ

theorem plurisubharmonicOn_of_levi_nonneg {u : E → ℝ} {U : Set E}
    (hu : ContDiff ℝ 2 u) (hU : IsOpen U)
    (hL : ∀ x ∈ U, ∀ v : E, 0 ≤ leviForm u x v) :
    PlurisubharmonicOn (fun y => (u y : EReal)) U :=
  (discPshOn_of_levi_nonneg hu hL).plurisubharmonicOn hU

section QuadraticPotential

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedSpace ℂ H] [IsScalarTower ℝ ℂ H]

/-- A concrete nonconstant PSH potential, established by genuine calculus. -/
theorem discPshOn_norm_sq (U : Set H) :
    DiscPshOn (fun y : H => ((‖y‖ ^ 2 : ℝ) : EReal)) U :=
  discPshOn_of_levi_nonneg (contDiff_norm_sq ℝ)
    (fun x _ v => leviForm_norm_sq_nonneg x v)

theorem plurisubharmonicAt_norm_sq (x : H) :
    PlurisubharmonicAt (fun y : H => ((‖y‖ ^ 2 : ℝ) : EReal)) x :=
  (discPshOn_norm_sq univ).plurisubharmonicOn isOpen_univ x (mem_univ x)

end QuadraticPotential

end SGPT.Foundations.Analysis
