/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.Continuous
meta import Mathlib.Tactic.Abel
meta import Mathlib.Tactic.FieldSimp
meta import Mathlib.Tactic.Linarith
meta import Mathlib.Tactic.Positivity

/-!
# Gradients of Moreau–Yosida envelopes

The upper and lower inequalities imply strong lower bounds, cocoercivity and Lipschitz continuity.
-/

@[expose] public section

open RealInnerProductSpace

namespace DFT

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `g` is a gradient of `F` in the Moreau–Yosida sense: supporting hyperplanes from below,
curvature at most `1/ε` from above. -/
structure IsMYSmooth (ε : ℝ) (F : E → ℝ) (g : E → E) : Prop where
  lower : ∀ x y, F x + ⟪g x, y - x⟫ ≤ F y
  upper : ∀ x y, F y ≤ F x + ⟪g x, y - x⟫ + ‖y - x‖ ^ 2 / (2 * ε)

namespace IsMYSmooth

variable {ε : ℝ} {F : E → ℝ} {g : E → E}

/-- Adding a linear term keeps the structure. -/
lemma add_linear (h : IsMYSmooth ε F g) (v : E) :
    IsMYSmooth ε (fun y => F y + ⟪v, y⟫) (fun y => g y + v) where
  lower x y := by
    have := h.lower x y
    rw [inner_add_left, inner_sub_right v]; linarith
  upper x y := by
    have := h.upper x y
    rw [inner_add_left, inner_sub_right v]; linarith

/-- Improved lower bound. -/
lemma lower_strong (h : IsMYSmooth ε F g) (hε : 0 < ε) (x y : E) :
    F x + ⟪g x, y - x⟫ + ε / 2 * ‖g y - g x‖ ^ 2 ≤ F y := by
  set a := g x; set b := g y
  set z := y - ε • (b - a)
  have h1 := h.lower x z
  have h2 := h.upper y z
  have hz1 : z - x = (y - x) - ε • (b - a) := by simp only [z]; abel
  have hz2 : z - y = -(ε • (b - a)) := by simp only [z]; abel
  rw [hz1] at h1; rw [hz2] at h2
  rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hε] at h2
  rw [inner_sub_right, inner_smul_right] at h1
  rw [inner_neg_right, inner_smul_right] at h2
  have e1 : ⟪b, b - a⟫ - ⟪a, b - a⟫ = ‖b - a‖ ^ 2 := by
    rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  have e2 : (ε * ‖b - a‖) ^ 2 / (2 * ε) = ε / 2 * ‖b - a‖ ^ 2 := by field_simp
  rw [e2] at h2
  nlinarith

/-- Co-coercivity of the gradient. -/
lemma cocoercive (h : IsMYSmooth ε F g) (hε : 0 < ε) (x y : E) :
    ε * ‖g x - g y‖ ^ 2 ≤ ⟪g x - g y, x - y⟫ := by
  have h1 := h.lower_strong hε x y
  have h2 := h.lower_strong hε y x
  rw [norm_sub_rev (g y) (g x)] at h1
  have e2 : ⟪g x - g y, x - y⟫ = -⟪g x, y - x⟫ - ⟪g y, x - y⟫ := by
    rw [inner_sub_left, ← neg_sub y x, inner_neg_right]
  rw [e2]
  linarith

/-- The gradient is `1/ε`-Lipschitz. -/
lemma norm_sub_le (h : IsMYSmooth ε F g) (hε : 0 < ε) (x y : E) :
    ε * ‖g x - g y‖ ≤ ‖x - y‖ := by
  have h1 := h.cocoercive hε x y
  have h2 := real_inner_le_norm (g x - g y) (x - y)
  rcases (norm_nonneg (g x - g y)).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · nlinarith

lemma continuous (h : IsMYSmooth ε F g) (hε : 0 < ε) : Continuous g := by
  refine (LipschitzWith.of_dist_le_mul (K := ⟨1 / ε, by positivity⟩) fun x y => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  change _ ≤ (1 / ε) * _
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hε, mul_comm]
  exact h.norm_sub_le hε x y

lemma norm_le (h : IsMYSmooth ε F g) (hε : 0 < ε) (x : E) : ‖g x‖ ≤ ‖g 0‖ + ‖x‖ / ε := by
  have := h.norm_sub_le hε x 0
  rw [sub_zero] at this
  have h3 : ‖g x - g 0‖ ≤ ‖x‖ / ε := by rw [le_div_iff₀ hε]; linarith
  calc ‖g x‖ = ‖(g x - g 0) + g 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖g x - g 0‖ + ‖g 0‖ := norm_add_le _ _
    _ ≤ _ := by linarith

end IsMYSmooth

end DFT
