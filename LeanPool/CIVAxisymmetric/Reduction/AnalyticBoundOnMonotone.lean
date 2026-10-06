/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.AnalyticBoundOn

/-!
# Analytic Bound On Monotone

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- Monotonicity of `AnalyticBoundOn`/`eq:analytic:interior:force` in the constant `M`:
increasing `M` preserves the bound. -/
theorem analyticBoundOn_mono_const {g : ParabolicPoint → Vec3} {R' M M' a : ℝ} {J : Set ℝ}
    (ha : 0 < a) (hM : M ≤ M') (h : AnalyticBoundOn g R' J M a) :
    AnalyticBoundOn g R' J M' a := by
  intro α t ht x hx i
  have hb := h α t ht x hx i
  have hnn : 0 ≤ a ^ (-((α 0 + α 1 + α 2 : ℕ) : ℝ)) * (Nat.factorial (α 0 + α 1 + α 2) : ℝ) := by
    positivity
  have h2 := mul_le_mul_of_nonneg_right hM hnn
  calc
    |multiPartial (fun w => g w i) α (x, t)|
        ≤ M * a ^ (-((α 0 + α 1 + α 2 : ℕ) : ℝ)) * Nat.factorial (α 0 + α 1 + α 2) := hb
    _ ≤ M' * a ^ (-((α 0 + α 1 + α 2 : ℕ) : ℝ)) * Nat.factorial (α 0 + α 1 + α 2) := by
      nlinarith only [hM, hnn]

/-- Monotonicity of `AnalyticBoundOn`/`eq:analytic:interior:force` in the analyticity rate `a`:
decreasing `a` (with `0 < a' ≤ a`) preserves the bound. -/
theorem analyticBoundOn_mono_scale {g : ParabolicPoint → Vec3} {R' M a a' : ℝ} {J : Set ℝ}
    (hM : 0 ≤ M) (ha' : 0 < a') (haa' : a' ≤ a) (h : AnalyticBoundOn g R' J M a) :
    AnalyticBoundOn g R' J M a' := by
  intro α t ht x hx i
  have hb := h α t ht x hx i
  set n := α 0 + α 1 + α 2 with hn
  have ha : 0 < a := ha'.trans_le haa'
  have hle : a' ^ (n : ℝ) ≤ a ^ (n : ℝ) :=
    Real.rpow_le_rpow ha'.le haa' (Nat.cast_nonneg n)
  have hainv : a ^ (-(n : ℝ)) ≤ a' ^ (-(n : ℝ)) := by
    rw [Real.rpow_neg ha.le, Real.rpow_neg ha'.le, ← one_div, ← one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos ha' n) hle
  have h2 : M * a ^ (-(n : ℝ)) * (Nat.factorial n : ℝ) ≤
      M * a' ^ (-(n : ℝ)) * (Nat.factorial n : ℝ) := by
    gcongr
  calc
    |multiPartial (fun w => g w i) α (x, t)|
        ≤ M * a ^ (-((α 0 + α 1 + α 2 : ℕ) : ℝ)) * Nat.factorial (α 0 + α 1 + α 2) := hb
    _ = M * a ^ (-(n : ℝ)) * (Nat.factorial n : ℝ) := by
      simp [hn]
    _ ≤ M * a' ^ (-(n : ℝ)) * (Nat.factorial n : ℝ) := h2
    _ = M * a' ^ (-((α 0 + α 1 + α 2 : ℕ) : ℝ)) * Nat.factorial (α 0 + α 1 + α 2) := by
      simp [hn]

/-- Monotonicity of `AnalyticBoundOn`/`eq:analytic:interior:force` in the spatial radius `R'`:
shrinking the ball preserves the bound. -/
theorem analyticBoundOn_mono_ball {g : ParabolicPoint → Vec3} {R' R'' M a : ℝ} {J : Set ℝ}
    (hR'' : R'' ≤ R') (h : AnalyticBoundOn g R' J M a) :
    AnalyticBoundOn g R'' J M a := by
  intro α t ht x hx i
  exact h α t ht x (vec3Ball_mono hR'' hx) i

/-- Monotonicity of `AnalyticBoundOn`/`eq:analytic:interior:force` in the time set `J`:
shrinking the time set preserves the bound. -/
theorem analyticBoundOn_mono_time {g : ParabolicPoint → Vec3} {R' M a : ℝ} {J J' : Set ℝ}
    (hJ : J' ⊆ J) (h : AnalyticBoundOn g R' J M a) :
    AnalyticBoundOn g R' J' M a := by
  intro α t ht x hx i
  exact h α t (hJ ht) x hx i

/-- Composite monotonicity of `AnalyticBoundOn`/`eq:analytic:interior:force` in all four
parameters: the bound can be transferred to a smaller ball, a smaller time set, a larger
constant, and a slower analyticity rate simultaneously. -/
theorem analyticBoundOn_mono {g : ParabolicPoint → Vec3} {R' R'' M M' a a' : ℝ} {J J' : Set ℝ}
    (ha' : 0 < a') (hM : 0 ≤ M) (hMM' : M ≤ M') (haa' : a' ≤ a) (hR'' : R'' ≤ R')
    (hJ : J' ⊆ J) (h : AnalyticBoundOn g R' J M a) :
    AnalyticBoundOn g R'' J' M' a' :=
  analyticBoundOn_mono_scale (hM.trans hMM') ha' haa'
    (analyticBoundOn_mono_const (ha'.trans_le haa') hMM'
      (analyticBoundOn_mono_time hJ
        (analyticBoundOn_mono_ball hR'' h)))

end CIV
