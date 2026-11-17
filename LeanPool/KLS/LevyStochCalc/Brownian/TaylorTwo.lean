/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Second-order Taylor bound with a Lipschitz second derivative

For a twice-differentiable real function whose second derivative is `K`-Lipschitz, the
second-order Taylor polynomial approximates the function to within `K|y − x|³`.

## Main statements

* `LevyStochCalc.abs_sub_taylor_one_le` — the first-order Taylor remainder bound.
* `LevyStochCalc.abs_sub_taylor_two_le` — the second-order Taylor remainder bound.
* `LevyStochCalc.abs_sub_sum_taylor_two_le` — the telescoped form along a sequence.
* `LevyStochCalc.taylorRemainder` — the telescoped remainder as a function of the sequence.
* `LevyStochCalc.abs_taylorRemainder_le` — its bound.
-/

@[expose] public section

namespace LevyStochCalc

/-- On the segment between `x` and `y`, no point is further from `x` than `y` is. -/
theorem abs_sub_le_of_mem_uIcc {x y w : ℝ} (hw : w ∈ Set.uIcc x y) : |w - x| ≤ |y - x| := by
  rcases Set.mem_uIcc.mp hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ w - x),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - x)]
    linarith
  · rw [abs_of_nonpos (by linarith : w - x ≤ 0), abs_of_nonpos (by linarith : y - x ≤ 0)]
    linarith

/-- **First-order Taylor remainder for a Lipschitz derivative.** -/
theorem abs_sub_taylor_one_le {f f' : ℝ → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ u v : ℝ, |f' u - f' v| ≤ K * |u - v|)
    (x y : ℝ) : |f y - f x - f' x * (y - x)| ≤ K * |y - x| * |y - x| := by
  have hconv : Convex ℝ (Set.uIcc x y) := convex_uIcc x y
  have hg : ∀ w ∈ Set.uIcc x y, HasDerivWithinAt (fun z => f z - f x - f' x * (z - x))
      (f' w - f' x) (Set.uIcc x y) w := by
    intro w _
    have hA : HasDerivAt (fun z : ℝ => f z - f x) (f' w) w := (hf w).sub_const (f x)
    have hB : HasDerivAt (fun z : ℝ => z - x) (1 : ℝ) w := (hasDerivAt_id w).sub_const x
    have hC : HasDerivAt (fun z : ℝ => f' x * (z - x)) (f' x * 1) w := hB.const_mul (f' x)
    have h1 : HasDerivAt (fun z : ℝ => f z - f x - f' x * (z - x)) (f' w - f' x * 1) w :=
      hA.sub hC
    rw [mul_one] at h1
    exact h1.hasDerivWithinAt
  have hbound : ∀ w ∈ Set.uIcc x y, ‖f' w - f' x‖ ≤ K * |y - x| := by
    intro w hw
    rw [Real.norm_eq_abs]
    exact (hf' w x).trans (mul_le_mul_of_nonneg_left (abs_sub_le_of_mem_uIcc hw) hK0)
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hbound hconv
    Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs] using hmain

/-- **Second-order Taylor remainder for a Lipschitz second derivative.** -/
theorem abs_sub_taylor_two_le {f f' f'' : ℝ → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ u v : ℝ, |f'' u - f'' v| ≤ K * |u - v|) (x y : ℝ) :
    |f y - f x - f' x * (y - x) - f'' x * (y - x) ^ 2 / 2| ≤ K * |y - x| ^ 3 := by
  have hconv : Convex ℝ (Set.uIcc x y) := convex_uIcc x y
  have hg : ∀ w ∈ Set.uIcc x y, HasDerivWithinAt
      (fun z => f z - f x - f' x * (z - x) - f'' x * (z - x) ^ 2 / 2)
      (f' w - f' x - f'' x * (w - x)) (Set.uIcc x y) w := by
    intro w _
    have hA : HasDerivAt (fun z : ℝ => f z - f x) (f' w) w := (hf w).sub_const (f x)
    have hB : HasDerivAt (fun z : ℝ => z - x) (1 : ℝ) w := (hasDerivAt_id w).sub_const x
    have hC : HasDerivAt (fun z : ℝ => f' x * (z - x)) (f' x * 1) w := hB.const_mul (f' x)
    have hD : HasDerivAt (fun z : ℝ => (z - x) ^ 2) (2 * (w - x)) w := by
      have hmul : HasDerivAt (fun z : ℝ => (z - x) * (z - x))
          (1 * (w - x) + (w - x) * 1) w := hB.mul hB
      have hfun : (fun z : ℝ => (z - x) ^ 2) = fun z : ℝ => (z - x) * (z - x) := by
        funext z; ring
      have hval : 1 * (w - x) + (w - x) * 1 = 2 * (w - x) := by ring
      rw [hfun, ← hval]
      exact hmul
    have hE : HasDerivAt (fun z : ℝ => f'' x * (z - x) ^ 2)
        (f'' x * (2 * (w - x))) w := hD.const_mul (f'' x)
    have hF : HasDerivAt (fun z : ℝ => f'' x * (z - x) ^ 2 / 2)
        (f'' x * (2 * (w - x)) / 2) w := hE.div_const 2
    have h1 : HasDerivAt (fun z : ℝ => f z - f x - f' x * (z - x) - f'' x * (z - x) ^ 2 / 2)
        (f' w - f' x * 1 - f'' x * (2 * (w - x)) / 2) w := (hA.sub hC).sub hF
    have h2 : f' w - f' x * 1 - f'' x * (2 * (w - x)) / 2
        = f' w - f' x - f'' x * (w - x) := by ring
    rw [h2] at h1
    exact h1.hasDerivWithinAt
  have hbound : ∀ w ∈ Set.uIcc x y,
      ‖f' w - f' x - f'' x * (w - x)‖ ≤ K * |y - x| * |y - x| := by
    intro w hw
    rw [Real.norm_eq_abs]
    refine (abs_sub_taylor_one_le hK0 hf' hf'' x w).trans ?_
    have h1 := abs_sub_le_of_mem_uIcc hw
    have h2 : |w - x| * |w - x| ≤ |y - x| * |y - x| :=
      mul_le_mul h1 h1 (abs_nonneg _) (abs_nonneg _)
    calc K * |w - x| * |w - x| = K * (|w - x| * |w - x|) := by ring
      _ ≤ K * (|y - x| * |y - x|) := mul_le_mul_of_nonneg_left h2 hK0
      _ = K * |y - x| * |y - x| := by ring
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hbound hconv
    Set.left_mem_uIcc Set.right_mem_uIcc
  have hzero : f x - f x - f' x * (x - x) - f'' x * (x - x) ^ 2 / 2 = 0 := by ring
  rw [hzero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmain
  calc |f y - f x - f' x * (y - x) - f'' x * (y - x) ^ 2 / 2|
      ≤ K * |y - x| * |y - x| * |y - x| := hmain
    _ = K * |y - x| ^ 3 := by ring


/-- **Telescoped second-order Taylor expansion along a sequence.** -/
theorem abs_sub_sum_taylor_two_le {f f' f'' : ℝ → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ u v : ℝ, |f'' u - f'' v| ≤ K * |u - v|) (x : ℕ → ℝ) (m : ℕ) :
    |f (x m) - f (x 0)
        - ((∑ i ∈ Finset.range m, f' (x i) * (x (i + 1) - x i))
          + ∑ i ∈ Finset.range m, f'' (x i) * (x (i + 1) - x i) ^ 2 / 2)|
      ≤ K * ∑ i ∈ Finset.range m, |x (i + 1) - x i| ^ 3 := by
  have htel : f (x m) - f (x 0) = ∑ i ∈ Finset.range m, (f (x (i + 1)) - f (x i)) :=
    (Finset.sum_range_sub (fun i => f (x i)) m).symm
  rw [htel, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have heq : f (x (i + 1)) - f (x i)
      - (f' (x i) * (x (i + 1) - x i) + f'' (x i) * (x (i + 1) - x i) ^ 2 / 2)
      = f (x (i + 1)) - f (x i) - f' (x i) * (x (i + 1) - x i)
        - f'' (x i) * (x (i + 1) - x i) ^ 2 / 2 := by ring
  rw [heq]
  exact abs_sub_taylor_two_le hK0 hf hf' hf'' (x i) (x (i + 1))

/-- The second-order Taylor remainder of `f` along the first `m` steps of the sequence `x`. -/
noncomputable def taylorRemainder (f f' f'' : ℝ → ℝ) (x : ℕ → ℝ) (m : ℕ) : ℝ :=
  f (x m) - f (x 0)
    - ((∑ i ∈ Finset.range m, f' (x i) * (x (i + 1) - x i))
      + ∑ i ∈ Finset.range m, f'' (x i) * (x (i + 1) - x i) ^ 2 / 2)

/-- The second-order Taylor remainder along a sequence is bounded by the Lipschitz constant of
`f''` times the sum of the cubed increments. -/
theorem abs_taylorRemainder_le {f f' f'' : ℝ → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ u v : ℝ, |f'' u - f'' v| ≤ K * |u - v|) (x : ℕ → ℝ) (m : ℕ) :
    |taylorRemainder f f' f'' x m| ≤ K * ∑ i ∈ Finset.range m, |x (i + 1) - x i| ^ 3 :=
  abs_sub_sum_taylor_two_le hK0 hf hf' hf'' x m

end LevyStochCalc
