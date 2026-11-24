/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CircleMove
public import Mathlib.Analysis.Complex.Circle
import LeanPool.GraphMinor.GM12.Section4CircleInterpolation
import LeanPool.GraphMinor.GM12.Section4DiscTwist

/-!
# Matching four cyclically ordered circle marks

XII (4.5), claim (1), page 253, uses the cyclic order at a crossing.
Rotate the first source and target marks to one. Match the remaining
three increasing positions inside a full turn by the interpolation
map, then undo the target rotation. The resulting homeomorphism
keeps orientation and sends all four marks to their assigned marks.
-/

public section

namespace GraphMinor.GM12

open Set Surface

private theorem ee_sub (x y : ℝ) : (ee x)⁻¹ * ee y = ee (y - x) := by
  unfold ee
  rw [← Circle.exp_neg, ← Circle.exp_add]
  congr 1
  ring

private theorem ee_restore (x y : ℝ) : ee x * ee (y - x) = ee y := by
  rw [← ee_sub x y, mul_inv_cancel_left]

/-- The ordered four-point circle adjustment used at crossings in
XII (4.5), claim (1), page 253. The parameters span less than one
full turn on both circles. -/
theorem exists_circle_four_point_move
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : ℝ}
    (ha₀₁ : a₀ < a₁) (ha₁₂ : a₁ < a₂) (ha₂₃ : a₂ < a₃) (ha₃ : a₃ < a₀ + 1)
    (hb₀₁ : b₀ < b₁) (hb₁₂ : b₁ < b₂) (hb₂₃ : b₂ < b₃) (hb₃ : b₃ < b₀ + 1) :
    ∃ h : Circle ≃ₜ Circle, PreservesCircleOrientation h ∧
      h (ee a₀) = ee b₀ ∧ h (ee a₁) = ee b₁ ∧
      h (ee a₂) = ee b₂ ∧ h (ee a₃) = ee b₃ := by
  obtain ⟨g, hg, hg0, hg1, hg2, hg3⟩ := exists_circle_three_point_move
    (a := a₁ - a₀) (b := a₂ - a₀) (c := a₃ - a₀)
    (a' := b₁ - b₀) (b' := b₂ - b₀) (c' := b₃ - b₀)
    (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
  let h := (Homeomorph.mulLeft (ee a₀)⁻¹).trans (g.trans (Homeomorph.mulLeft (ee b₀)))
  have ho : PreservesCircleOrientation h :=
    PreservesCircleOrientation.comp
      (PreservesCircleOrientation.comp (preservesCircleOrientation_mul (ee b₀)) hg)
      (preservesCircleOrientation_mul _)
  refine ⟨h, ho, ?_, ?_, ?_, ?_⟩
  · change ee b₀ * g ((ee a₀)⁻¹ * ee a₀) = ee b₀
    rw [inv_mul_cancel, hg0, mul_one]
  · change ee b₀ * g ((ee a₀)⁻¹ * ee a₁) = ee b₁
    rw [ee_sub, hg1, ee_restore]
  · change ee b₀ * g ((ee a₀)⁻¹ * ee a₂) = ee b₂
    rw [ee_sub, hg2, ee_restore]
  · change ee b₀ * g ((ee a₀)⁻¹ * ee a₃) = ee b₃
    rw [ee_sub, hg3, ee_restore]

end GraphMinor.GM12
