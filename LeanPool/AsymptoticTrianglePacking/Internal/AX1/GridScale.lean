/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — scale equalisation for the sub-block grid

One triple of clusters `U, W, X` of a regularity-reduced graph, with pair densities `x = d(U,W)`,
`y = d(U,X)`, `z = d(W,X)` all at least `δ`, is split into vertex blocks whose sizes are
proportional to the *opposite* density (`|X-block| ≈ τ·z`, and symmetrically).  The point of that
choice is that the triangle degree of an edge of the `U × W` block pair, which is (up to the
uniformity error) `d(U,X)·d(W,X)·|X-block|`, then sits in the window `(1 ± μ)·d` around the *same*
scale `d = τ·x·y·z` for all three of the pairs — the hypotheses `hClo … hAhi` of
`Nibble.AX1.IsSubTripleDesign`.

`Nibble.AX1.scale_window` is that computation, in the abstract: `x'` and `y'` are the *measured*
sub-block densities (within `e` of the cluster densities `x`, `y`), `ε` is the uniformity slack of
the codegree count, and `s` is the integer block size (within `1` of `τ·z`).  Provided the total
error `e + 2ε` is at most `μδ³/12` and the scale `τ` is at least `2/(μδ³)`, the resulting count lies
in `[(1−μ)d, (1+μ)d]`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Positivity

/-! # GridScale -/

@[expose] public section

namespace Nibble.AX1

/-- Elementary two-variable bound: shrinking both factors by `E` costs at most `2E`. -/
private theorem shrink_lower {x y E : ℝ} (hE : 0 ≤ E) (hx1 : x ≤ 1) (hy1 : y ≤ 1) :
    x * y - 2 * E ≤ (x - E) * (y - E) := by
  linarith only [mul_nonneg hE (by linarith : (0:ℝ) ≤ 2 - x - y), sq_nonneg E]

/-- Elementary two-variable bound: growing both factors by `E ≤ 1` costs at most `3E`. -/
private theorem grow_upper {x y E : ℝ} (hE : 0 ≤ E) (hE1 : E ≤ 1) (hx1 : x ≤ 1) (hy1 : y ≤ 1) :
    (x + E) * (y + E) ≤ x * y + 3 * E := by
  nlinarith [mul_nonneg hE (by linarith : (0:ℝ) ≤ 1 - E)]

/-- The purely multiplicative heart of the scale window: with `τ` large enough compared with the
error `e + 2ε`, the products `(xy ∓ cE)(τz ± 1)` are within a factor `1 ± μ` of `τxyz`. -/
private theorem scale_core {x y z τ μ δ ε e : ℝ}
    (hz1 : z ≤ 1) (hE0 : 0 < e + 2 * ε) (hEone : e + 2 * ε ≤ 1 / 12)
    (hxy1 : x * y ≤ 1) (hT2 : 2 ≤ μ * τ * δ ^ 3) (hmul : μ * τ * δ ^ 3 ≤ μ * (τ * (x * y * z)))
    (hEτ : (e + 2 * ε) * τ ≤ μ * τ * δ ^ 3 / 12) (hτpos : 0 < τ) :
    ((1 - μ) * (τ * (x * y * z)) ≤ (x * y - 2 * (e + 2 * ε)) * (τ * z - 1))
      ∧ ((x * y + 3 * (e + 2 * ε)) * (τ * z + 1) ≤ (1 + μ) * (τ * (x * y * z))) := by
  have h1 : (e + 2 * ε) * τ * z ≤ (e + 2 * ε) * τ := by
    have : 0 ≤ (e + 2 * ε) * τ := by positivity
    nlinarith only [hz1, this]
  exact ⟨by linarith, by linarith⟩

/-- Lower half of the window, from the multiplicative core. -/
private theorem window_lower {x y z x' y' s τ μ ε e : ℝ}
    (hx1 : x ≤ 1) (hy1 : y ≤ 1) (hE0 : 0 < e + 2 * ε) (hε : 0 < ε)
    (hxE : 0 < x - (e + 2 * ε)) (hyE : 0 < y - (e + 2 * ε))
    (hx'lo : x - e ≤ x') (hy'lo : y - e ≤ y')
    (hslo : τ * z - 1 ≤ s) (hτz : 2 ≤ τ * z)
    (hcore : (1 - μ) * (τ * (x * y * z)) ≤ (x * y - 2 * (e + 2 * ε)) * (τ * z - 1)) :
    (1 - μ) * (τ * (x * y * z)) ≤ (x' - ε) * (y' - 2 * ε) * s := by
  have step1 : x * y - 2 * (e + 2 * ε) ≤ (x - (e + 2 * ε)) * (y - (e + 2 * ε)) :=
    shrink_lower hE0.le hx1 hy1
  have step1' : (x - (e + 2 * ε)) * (y - (e + 2 * ε)) ≤ (x' - ε) * (y' - 2 * ε) :=
    mul_le_mul (by linarith) (by linarith) hyE.le (by linarith)
  have hp : 0 ≤ (x' - ε) * (y' - 2 * ε) := mul_nonneg (by linarith) (by linarith)
  have h1 : (x * y - 2 * (e + 2 * ε)) * (τ * z - 1) ≤ (x' - ε) * (y' - 2 * ε) * (τ * z - 1) :=
    mul_le_mul_of_nonneg_right (le_trans step1 step1') (by linarith)
  have h2 : (x' - ε) * (y' - 2 * ε) * (τ * z - 1) ≤ (x' - ε) * (y' - 2 * ε) * s :=
    mul_le_mul_of_nonneg_left hslo hp
  linarith only [hcore, h1, h2]

/-- Upper half of the window, from the multiplicative core. -/
private theorem window_upper {x y z x' y' s τ μ ε e : ℝ}
    (hx1 : x ≤ 1) (hy1 : y ≤ 1) (hE0 : 0 < e + 2 * ε) (hE1 : e + 2 * ε ≤ 1) (hε : 0 < ε)
    (hx'hi : x' ≤ x + e) (hy'hi : y' ≤ y + e)
    (hx'lo : x - e ≤ x') (hy'lo : y - e ≤ y')
    (hxE : 0 < x - (e + 2 * ε)) (hyE : 0 < y - (e + 2 * ε))
    (hshi : s ≤ τ * z + 1) (hτz : 2 ≤ τ * z)
    (hcore : (x * y + 3 * (e + 2 * ε)) * (τ * z + 1) ≤ (1 + μ) * (τ * (x * y * z))) :
    (x' + ε) * (y' + 2 * ε) * s ≤ (1 + μ) * (τ * (x * y * z)) := by
  have step1 : (x' + ε) * (y' + 2 * ε) ≤ x * y + 3 * (e + 2 * ε) := by
    have h1 : (x' + ε) * (y' + 2 * ε) ≤ (x + (e + 2 * ε)) * (y + (e + 2 * ε)) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have h2 : (x + (e + 2 * ε)) * (y + (e + 2 * ε)) ≤ x * y + 3 * (e + 2 * ε) :=
      grow_upper hE0.le hE1 hx1 hy1
    linarith only [h1, h2]
  have hpos : 0 ≤ (x' + ε) * (y' + 2 * ε) := mul_nonneg (by linarith) (by linarith)
  have h1 : (x' + ε) * (y' + 2 * ε) * s ≤ (x' + ε) * (y' + 2 * ε) * (τ * z + 1) :=
    mul_le_mul_of_nonneg_left hshi hpos
  have h2 : (x' + ε) * (y' + 2 * ε) * (τ * z + 1) ≤ (x * y + 3 * (e + 2 * ε)) * (τ * z + 1) :=
    mul_le_mul_of_nonneg_right step1 (by linarith)
  linarith only [hcore, h1, h2]

/-- **Scale equalisation.**  If the three cluster densities `x, y, z` lie in `[δ, 1]`, the measured
sub-block densities `x', y'` are within `e` of `x, y`, the block size `s` is within `1` of `τ·z`,
the total error satisfies `e + 2ε ≤ μδ³/12` and the scale satisfies `τ ≥ 2/(μδ³)`, then the
two-sided codegree count `(x' ∓ ε)(y' ∓ 2ε)·s` lies in the window `(1 ± μ)·d` around the common
scale `d = τ·x·y·z`. -/
theorem scale_window {x y z x' y' s τ d δ μ ε e : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hx : δ ≤ x) (hx1 : x ≤ 1) (hy : δ ≤ y) (hy1 : y ≤ 1) (hz : δ ≤ z) (hz1 : z ≤ 1)
    (hx' : |x' - x| ≤ e) (hy' : |y' - y| ≤ e)
    (hs : |s - τ * z| ≤ 1)
    (he : 0 ≤ e) (hε : 0 < ε)
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (hE : e + 2 * ε ≤ μ * δ ^ 3 / 12)
    (hτ : 2 / (μ * δ ^ 3) ≤ τ)
    (hd : d = τ * (x * y * z)) :
    (1 - μ) * d ≤ (x' - ε) * (y' - 2 * ε) * s ∧ (x' + ε) * (y' + 2 * ε) * s ≤ (1 + μ) * d := by
  have hδ3 : (0:ℝ) < δ ^ 3 := by positivity
  have hμδ : (0:ℝ) < μ * δ ^ 3 := by positivity
  have hτpos : 0 < τ := lt_of_lt_of_le (by positivity) hτ
  have hT2 : 2 ≤ μ * τ * δ ^ 3 := by
    rw [div_le_iff₀ hμδ] at hτ; linarith only [hτ]
  have hδcube : δ ^ 3 ≤ δ := by nlinarith [sq_nonneg δ, mul_pos hδ0 hδ0]
  have hE0 : 0 < e + 2 * ε := by linarith only [he, hε]
  have hEone : e + 2 * ε ≤ 1 / 12 := by nlinarith only [hz, hz1, hμ0, hμ1, hE, hδcube]
  have hEδ : e + 2 * ε ≤ δ / 12 := by nlinarith only [hμ0, hμ1, hE, hδcube, hE0]
  have hτ1 : 1 ≤ τ := by nlinarith
  have hz0 : 0 ≤ z := le_trans hδ0.le hz
  have hτz : 2 ≤ τ * z := by nlinarith
  have hxy : δ * δ ≤ x * y := by nlinarith
  have hA : δ ^ 3 ≤ x * y * z := by nlinarith
  have hxy1 : x * y ≤ 1 := by nlinarith
  have hmul : μ * τ * δ ^ 3 ≤ μ * (τ * (x * y * z)) := by
    calc μ * τ * δ ^ 3 = (μ * τ) * δ ^ 3 := by ring
      _ ≤ (μ * τ) * (x * y * z) := mul_le_mul_of_nonneg_left hA (by positivity)
      _ = μ * (τ * (x * y * z)) := by ring
  have hEτ : (e + 2 * ε) * τ ≤ μ * τ * δ ^ 3 / 12 := by
    calc (e + 2 * ε) * τ ≤ (μ * δ ^ 3 / 12) * τ := mul_le_mul_of_nonneg_right hE hτpos.le
      _ = μ * τ * δ ^ 3 / 12 := by ring
  have hx'lo : x - e ≤ x' := by have := abs_le.mp hx'; linarith only [this.1]
  have hx'hi : x' ≤ x + e := by have := abs_le.mp hx'; linarith only [this.2]
  have hy'lo : y - e ≤ y' := by have := abs_le.mp hy'; linarith only [this.1]
  have hy'hi : y' ≤ y + e := by have := abs_le.mp hy'; linarith only [this.2]
  have hslo : τ * z - 1 ≤ s := by have := abs_le.mp hs; linarith only [this.1]
  have hshi : s ≤ τ * z + 1 := by have := abs_le.mp hs; linarith only [this.2]
  have hxE : 0 < x - (e + 2 * ε) := by linarith
  have hyE : 0 < y - (e + 2 * ε) := by linarith
  obtain ⟨core1, core2⟩ := scale_core (δ := δ) hz1 hE0 hEone hxy1 hT2 hmul hEτ hτpos
  subst hd
  exact ⟨window_lower hx1 hy1 hE0 hε hxE hyE hx'lo hy'lo hslo hτz core1,
    window_upper hx1 hy1 hE0 (by linarith) hε hx'hi hy'hi hx'lo hy'lo hxE hyE hshi hτz core2⟩

end Nibble.AX1
