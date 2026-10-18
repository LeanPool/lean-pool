/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Slope


/-!
# Decreasing increments of a concave function

A concave function's increment over an interval of fixed length shrinks as the interval
slides right. In economics this is the increasing-differences (supermodularity) condition
that monotone-comparative-statics arguments run on, usually stated as a cross partial
`-u'' > 0`. Stated this way it needs no derivatives and no smoothness at all.

The proof is two applications of concavity. Writing `L = (c₂ + Δ) - c₁`, the two interior
points `c₁ + Δ` and `c₂` are *complementary* convex combinations of the endpoints `c₁` and
`c₂ + Δ`: the weights on `c₂ + Δ` are `Δ / L` and `(c₂ - c₁) / L`, which sum to one. Adding
the two concavity inequalities makes the weights cancel.
-/

@[expose] public section

open Set

/-- **Decreasing increments.** For a concave `u`, sliding an interval to the right by `Δ`
cannot increase the increment of `u` across it. -/
theorem ConcaveOn.sub_le_sub_of_shift {s : Set ℝ} {u : ℝ → ℝ} (hu : ConcaveOn ℝ s u)
    {c₁ c₂ Δ : ℝ} (h₁ : c₁ ∈ s) (h₂ : c₂ + Δ ∈ s) (hc : c₁ ≤ c₂) (hΔ : 0 ≤ Δ) :
    u (c₂ + Δ) - u (c₁ + Δ) ≤ u c₂ - u c₁ := by
  rcases eq_or_lt_of_le (show c₁ ≤ c₂ + Δ by linarith) with hdeg | hpos
  · -- `c₁ = c₂ + Δ` forces `Δ = 0` and `c₁ = c₂`, and the claim is an equality
    have hΔ0 : Δ = 0 := by linarith
    have hcc : c₁ = c₂ := by linarith
    subst hΔ0
    simp [hcc]
  · have hL : 0 < c₂ + Δ - c₁ := by linarith
    set θ : ℝ := Δ / (c₂ + Δ - c₁) with hθdef
    have hθ0 : 0 ≤ θ := div_nonneg hΔ hL.le
    have hθ1 : 0 ≤ 1 - θ := by
      rw [hθdef, sub_nonneg, div_le_one hL]
      linarith
    -- `c₁ + Δ` and `c₂` are complementary convex combinations of `c₁` and `c₂ + Δ`
    have e1 : (1 - θ) * c₁ + θ * (c₂ + Δ) = c₁ + Δ := by
      rw [hθdef]; field_simp; ring
    have e2 : θ * c₁ + (1 - θ) * (c₂ + Δ) = c₂ := by
      rw [hθdef]; field_simp; ring
    have i1 := hu.2 h₁ h₂ hθ1 hθ0 (by ring)
    have i2 := hu.2 h₁ h₂ hθ0 hθ1 (by ring)
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, e1] at i1
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, e2] at i2
    nlinarith [i1, i2]

/-! ### Lipschitz away from the left endpoint

A concave function on `Ioi 0` need not be Lipschitz there -- utility functions used in
economics are exactly the ones that are not, diverging at zero -- but it IS Lipschitz on
`[δ, ∞)` for any `δ > 0`, with a constant read off a single secant. No differentiability is
needed: the bound comes from antitonicity of secant slopes.

This is what lets a marginal argument be run without a derivative. Where the textbook
argument bounds the marginal utility of consumption by `u'(δ)`, this bounds it by the slope
of `u` across `[δ/2, δ]`, which is available from concavity alone. -/

/-- The secant slope of `u` across `[δ/2, δ]`, which bounds every slope further right. -/
noncomputable def slopeBound (u : ℝ → ℝ) (δ : ℝ) : ℝ := (u δ - u (δ / 2)) / (δ / 2)

theorem slopeBound_nonneg {u : ℝ → ℝ} (hmono : MonotoneOn u (Ioi 0)) {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ slopeBound u δ := by
  refine div_nonneg (sub_nonneg.mpr (hmono ?_ ?_ (by linarith))) (by linarith)
  · exact mem_Ioi.mpr (by linarith)
  · exact mem_Ioi.mpr hδ

/-- The one-sided bound: moving right from `a ≥ δ` raises `u` by at most the slope bound
times the distance. -/
theorem ConcaveOn.sub_le_slopeBound_mul {u : ℝ → ℝ} (hu : ConcaveOn ℝ (Ioi 0) u) {δ : ℝ}
    (hδ : 0 < δ) {a b : ℝ} (ha : δ ≤ a) (hab : a ≤ b) :
    u b - u a ≤ slopeBound u δ * (b - a) := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  have hhalf : (0 : ℝ) < δ / 2 := by linarith
  have hmemh : δ / 2 ∈ Ioi (0 : ℝ) := mem_Ioi.mpr hhalf
  have hmemd : δ ∈ Ioi (0 : ℝ) := mem_Ioi.mpr hδ
  have hmema : a ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (by linarith)
  have hmemb : b ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (by linarith)
  -- the slope across `[a, b]` is at most the slope bound
  have hkey : (u b - u a) / (b - a) ≤ slopeBound u δ := by
    rcases eq_or_lt_of_le ha with rfl | hgt
    · -- `a = δ`: one step
      have h := hu.slope_anti_adjacent hmemh hmemb (by linarith) hlt
      simpa only [slopeBound, show δ - δ / 2 = δ / 2 by ring] using h
    · -- `a > δ`: chain two steps through `δ`
      have h1 := hu.slope_anti_adjacent hmemd hmemb hgt hlt
      have h2 := hu.slope_anti_adjacent hmemh hmema (by linarith) hgt
      simp only [slopeBound, show δ - δ / 2 = δ / 2 by ring] at h2 ⊢
      linarith
  rw [div_le_iff₀ (by linarith)] at hkey
  linarith

/-- **A concave function is Lipschitz away from the left endpoint**, with an explicit
constant and no appeal to differentiability. -/
theorem ConcaveOn.abs_sub_le_slopeBound_mul {u : ℝ → ℝ} (hu : ConcaveOn ℝ (Ioi 0) u)
    (hmono : MonotoneOn u (Ioi 0)) {δ : ℝ} (hδ : 0 < δ) {x y : ℝ}
    (hx : δ ≤ x) (hy : δ ≤ y) :
    |u x - u y| ≤ slopeBound u δ * |x - y| := by
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (hmono (mem_Ioi.mpr (by linarith))
      (mem_Ioi.mpr (by linarith)) h)), abs_of_nonneg (by linarith)]
    exact hu.sub_le_slopeBound_mul hδ hy h
  · rw [abs_sub_comm, abs_sub_comm x y,
      abs_of_nonneg (sub_nonneg.mpr (hmono (mem_Ioi.mpr (by linarith))
        (mem_Ioi.mpr (by linarith)) h)), abs_of_nonneg (by linarith)]
    exact hu.sub_le_slopeBound_mul hδ hx h

/-! ### Scaling a concave function

For a concave, strictly positive `z`, the ratio `α / z (α x)` rises with `α`. This is Lemma 3
of Light (2018), one of the three ingredients of his Theorem 1 (savings rise with the interest
rate when relative risk aversion is at most one).

Like the increments lemma above, it needs no derivative: `α₁ x` is a convex combination of `0`
and `α₂ x` with weight `α₁ / α₂`, so concavity gives the inequality directly, and strict
positivity at the origin is what turns it from weak into the stated form.
-/

/-- **Light (2018), Lemma 3**, on any convex set containing the origin. In the application `z`
is the consumption function, which is concave on the asset region and nowhere else, so the
original statement over `[0, ∞)` would not reach it. Positivity is needed only at the origin
and at the far point: concavity carries it to everything in between. -/
theorem ConcaveOn.div_le_div_of_scale {z : ℝ → ℝ} {s : Set ℝ} (hz : ConcaveOn ℝ s z)
    (h0 : (0 : ℝ) ∈ s) (hz0 : 0 < z 0) {α₁ α₂ x : ℝ} (h1 : 0 < α₁) (h12 : α₁ ≤ α₂) (hx : 0 < x)
    (hm2 : α₂ * x ∈ s) (hp2 : 0 < z (α₂ * x)) :
    α₁ / z (α₁ * x) ≤ α₂ / z (α₂ * x) := by
  have h2 : 0 < α₂ := lt_of_lt_of_le h1 h12
  -- `α₁ x` is a convex combination of `0` and `α₂ x`
  have hcomb : (1 - α₁ / α₂) • (0 : ℝ) + (α₁ / α₂) • (α₂ * x) = α₁ * x := by
    simp only [smul_eq_mul, mul_zero, zero_add]
    field_simp
  have hw1 : (0 : ℝ) ≤ 1 - α₁ / α₂ := by
    rw [sub_nonneg, div_le_one h2]; exact h12
  have hw2 : (0 : ℝ) < α₁ / α₂ := div_pos h1 h2
  have hcc := hz.2 h0 hm2 hw1 hw2.le (by ring)
  rw [hcomb] at hcc
  simp only [smul_eq_mul] at hcc
  -- concavity carries positivity from the endpoints to `α₁ x`
  have hp1 : 0 < z (α₁ * x) := by
    nlinarith [mul_nonneg hw1 hz0.le, mul_pos hw2 hp2]
  rw [div_le_div_iff₀ hp1 hp2]
  have hkey : α₁ * z (α₂ * x) ≤ α₂ * z (α₁ * x) := by
    have hmul := mul_le_mul_of_nonneg_left hcc h2.le
    have hexp : α₂ * ((1 - α₁ / α₂) * z 0 + α₁ / α₂ * z (α₂ * x))
        = (α₂ - α₁) * z 0 + α₁ * z (α₂ * x) := by field_simp
    rw [hexp] at hmul
    have hz0' : 0 ≤ (α₂ - α₁) * z 0 := mul_nonneg (by linarith) hz0.le
    linarith
  linarith
