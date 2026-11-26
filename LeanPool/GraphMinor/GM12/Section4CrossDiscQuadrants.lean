/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4CrossDiscParam
public import LeanPool.GraphMinor.Surface.CircleMove
import LeanPool.GraphMinor.GM12.Section4CircleAvoidance

/-!
# Four ordered marks on a crossing disc

In XII (4.5), claim (1), page 253, the two crossing arcs give
four boundary marks in alternating order. Parametrize them at
zero, one quarter, one half, and three quarters of a turn. The
parametrization is injective on these positions. Its opposite
pairs are the real-axis and imaginary-axis contact pairs.
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Surface

private theorem ee_quarter : (ee (1 / 4) : ℂ) = Complex.I := by
  unfold ee
  have he : 2 * Real.pi * (1 / 4 : ℝ) = Real.pi / 2 := by ring
  rw [he, Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp

private theorem ee_half : (ee (1 / 2) : ℂ) = -1 := by
  unfold ee
  have he : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by ring
  rw [he, Circle.coe_exp]
  exact Complex.exp_pi_mul_I

private theorem ee_three_quarters : (ee (3 / 4) : ℂ) = -Complex.I := by
  unfold ee
  have he : 2 * Real.pi * (3 / 4 : ℝ) = Real.pi + Real.pi / 2 := by ring
  rw [he, Circle.coe_exp, Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp

/-- The four marks in their order in the coordinate circle. -/
noncomputable def crossDiscMarks (A : ℂ ≃L[ℝ] ℂ) (x : ℂ) (r : ℝ) (i : Fin 4) : ℂ :=
  crossDiscParam A x r (ee ((i.val : ℝ) / 4))

/-- The four quarter-turn marks are distinct on every positive
radius crossing disc. -/
theorem crossDiscMarks_injective (A : ℂ ≃L[ℝ] ℂ) (x : ℂ)
    {r : ℝ} (hr : 0 < r) : Function.Injective (crossDiscMarks A x r) := by
  intro i j hij
  have he : ee ((i.val : ℝ) / 4) = ee ((j.val : ℝ) / 4) :=
    (crossDiscParam_properties A x hr).2.1 hij
  have hi3 : (i.val : ℝ) ≤ 3 := by exact_mod_cast (show i.val ≤ 3 by omega)
  have hj3 : (j.val : ℝ) ≤ 3 := by exact_mod_cast (show j.val ≤ 3 by omega)
  have h := ee_injOn_short_interval (a := -(1 / 8 : ℝ)) (b := 7 / 8) (by norm_num)
    (show (i.val : ℝ) / 4 ∈ Ioo (-(1 / 8 : ℝ)) (7 / 8) from
      ⟨by linarith [Nat.cast_nonneg (α := ℝ) i.val], by linarith⟩)
    (show (j.val : ℝ) / 4 ∈ Ioo (-(1 / 8 : ℝ)) (7 / 8) from
      ⟨by linarith [Nat.cast_nonneg (α := ℝ) j.val], by linarith⟩) he
  apply Fin.ext
  have hv : (i.val : ℝ) = (j.val : ℝ) := by linarith
  exact_mod_cast hv

/-- The mark set has four points and is contained in the disc
boundary, as required in XII (4.5), claim (1), page 253. -/
theorem crossDiscMarks_card_boundary (A : ℂ ≃L[ℝ] ℂ) (x : ℂ)
    {r : ℝ} (hr : 0 < r) :
    (range (crossDiscMarks A x r)).ncard = 4 ∧
      range (crossDiscMarks A x r) ⊆
        discBd ((fun z => x + A z) '' Metric.closedBall 0 r) := by
  refine ⟨?_, ?_⟩
  · simpa using ncard_range_of_injective (crossDiscMarks_injective A x hr)
  · rintro z ⟨i, rfl⟩
    rw [← (crossDiscParam_properties A x hr).2.2]
    exact mem_range_self (ee ((i.val : ℝ) / 4))

/-- The ordered quarter-turn marks give the two opposite pairs
from the coordinate axes. -/
theorem crossDiscMarks_values (A : ℂ ≃L[ℝ] ℂ) (x : ℂ) (r : ℝ) :
    crossDiscMarks A x r 0 = x + A (r • (1 : ℂ)) ∧
    crossDiscMarks A x r 1 = x + A (r • Complex.I) ∧
    crossDiscMarks A x r 2 = x + A ((-r) • (1 : ℂ)) ∧
    crossDiscMarks A x r 3 = x + A ((-r) • Complex.I) := by
  have he0 : (ee 0 : ℂ) = 1 := by simp [ee]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [crossDiscMarks, crossDiscParam, Fin.val_zero, Nat.cast_zero, zero_div, he0]
  · simp only [crossDiscMarks, crossDiscParam, Fin.val_one, Nat.cast_one, ee_quarter]
  · change x + A (r • (ee (2 / 4) : ℂ)) = _
    have he2 : (2 : ℝ) / 4 = 1 / 2 := by norm_num
    simp only [he2, ee_half, smul_neg, neg_smul]
  · change x + A (r • (ee (3 / 4) : ℂ)) = _
    simp only [ee_three_quarters, smul_neg, neg_smul]

/-- The literal quarter-turn boundary parameters give the real
and imaginary axis contacts of a crossing disc. -/
theorem crossDiscParam_quarter_values (A : ℂ ≃L[ℝ] ℂ) (x : ℂ) (r : ℝ) :
    crossDiscParam A x r (ee 0) = x + A (r • (1 : ℂ)) ∧
    crossDiscParam A x r (ee (1 / 4)) = x + A (r • Complex.I) ∧
    crossDiscParam A x r (ee (1 / 2)) = x + A ((-r) • (1 : ℂ)) ∧
    crossDiscParam A x r (ee (3 / 4)) = x + A ((-r) • Complex.I) := by
  obtain ⟨h0, h1, h2, h3⟩ := crossDiscMarks_values A x r
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [crossDiscMarks, Fin.val_zero, Nat.cast_zero, zero_div] using h0
  · simpa only [crossDiscMarks, Fin.val_one, Nat.cast_one] using h1
  · change crossDiscParam A x r (ee ((2 : ℝ) / 4)) = _ at h2
    have he2 : (2 : ℝ) / 4 = 1 / 2 := by norm_num
    simpa only [he2] using h2
  · exact h3

end GraphMinor.GM12
