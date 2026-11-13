/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.AnnularClosePairCounting
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Two equidistant witnesses of a long chord in a thin annulus

Formalizes part (i) of Lemma J (the κ-image length gap) of
`docs/results/explicit-constant-gain-1-40-2026-10-21.md` (§2), in the squared form that
row J of `docs/results/short-chain-constant-gain-1-60-2026-10-21.md` uses. There are no
square roots: the bisector offset `h₀² = (1 - s²)²/(4l)` is replaced by an upper bound `H`,
and the radius `√(s² - h₀²)` by a lower bound `u`.

Let `a, b, z, z'` lie in the annulus `s²ρ² ≤ |x - c|² ≤ ρ²`, let `|ab|² > lρ²`, and let each of
`z, z'` be equidistant from `a` and `b`. Put `e = b - a`, `E = |e|²`, `k = ⟨z - c, e⟩` and
`τ = det(z - c, e)`. Then `|z - c|² E = k² + τ²`, the equidistance gives
`2k = |b - c|² - |a - c|²` for both witnesses, and so `|zz'|² E = (τ - τ')²`. The annulus gives
`k² ≤ Hρ²E`.

* Witnesses on opposite sides of the foot of the perpendicular from `c` (`ττ' ≤ 0`) are far
  apart: `(τ - τ')² ≥ 4(s² - H)ρ²E`, so `|zz'|² > G'ρ²` when `G' < 4(s² - H)`.
* Witnesses on the same side are close: `τ² - τ'²` is at most `(1 - s²)ρ²E` and the smaller of
  `|τ|, |τ'|` is at least `uρ√E`, so `|zz'|² ≤ g²ρ²` when `1 - s² ≤ g² + 2gu`.

No `z ≠ z'` hypothesis is needed.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry

/-- Same-side case of the scalar dichotomy, for two absolute values `x ≥ y ≥ 0`. If
`x² - y² ≤ (1 - s²)V` and `y² ≥ u²V`, then `(x - y)² ≤ g²V` whenever
`1 - s² ≤ g² + 2gu`. -/
private lemma sub_sq_le_of_sq_sub_sq_le {V s g u x y : ℝ} (hV : 0 ≤ V) (hy : 0 ≤ y)
    (hyx : y ≤ x) (hyu : u ^ 2 * V ≤ y ^ 2) (hxy : x ^ 2 - y ^ 2 ≤ (1 - s ^ 2) * V)
    (hu0 : 0 ≤ u) (hg0 : 0 ≤ g) (hg : 1 - s ^ 2 ≤ g ^ 2 + 2 * g * u) :
    (x - y) ^ 2 ≤ g ^ 2 * V := by
  by_contra h
  rw [not_le] at h
  have hd0 : 0 ≤ x - y := by linarith
  have hprod : (g * u * V) ^ 2 ≤ ((x - y) * y) ^ 2 := by
    have := mul_le_mul h.le hyu (by positivity) (by positivity)
    calc (g * u * V) ^ 2 = g ^ 2 * V * (u ^ 2 * V) := by ring
      _ ≤ (x - y) ^ 2 * y ^ 2 := this
      _ = ((x - y) * y) ^ 2 := by ring
  have hdy : g * u * V ≤ (x - y) * y :=
    (pow_le_pow_iff_left₀ (by positivity) (mul_nonneg hd0 hy) two_ne_zero).mp hprod
  have hsplit : x ^ 2 - y ^ 2 = (x - y) ^ 2 + 2 * ((x - y) * y) := by ring
  have hgV : (1 - s ^ 2) * V ≤ (g ^ 2 + 2 * g * u) * V := mul_le_mul_of_nonneg_right hg hV
  nlinarith

/-- The scalar dichotomy with the product `ρ²E` written as one positive number `V`. -/
private lemma scalar_dichotomy_of_pos {V k τ τ' s H G' g u : ℝ} (hV : 0 < V)
    (hk : k ^ 2 ≤ H * V)
    (hlo : s ^ 2 * V ≤ k ^ 2 + τ ^ 2) (hhi : k ^ 2 + τ ^ 2 ≤ V)
    (hlo' : s ^ 2 * V ≤ k ^ 2 + τ' ^ 2) (hhi' : k ^ 2 + τ' ^ 2 ≤ V)
    (hG' : G' < 4 * (s ^ 2 - H)) (hu0 : 0 ≤ u) (hu : u ^ 2 ≤ s ^ 2 - H)
    (hg0 : 0 ≤ g) (hg : 1 - s ^ 2 ≤ g ^ 2 + 2 * g * u) :
    (τ - τ') ^ 2 ≤ g ^ 2 * V ∨ G' * V < (τ - τ') ^ 2 := by
  have hsH : 0 ≤ s ^ 2 - H := le_trans (sq_nonneg u) hu
  have hm : (s ^ 2 - H) * V ≤ τ ^ 2 := by nlinarith
  have hm' : (s ^ 2 - H) * V ≤ τ' ^ 2 := by nlinarith
  have hm0 : 0 ≤ (s ^ 2 - H) * V := mul_nonneg hsH hV.le
  rcases le_or_gt (τ * τ') 0 with hopp | hsame
  · -- Opposite sides: `-ττ' ≥ (s² - H)V`, so `(τ - τ')² ≥ 4(s² - H)V > G'V`.
    right
    have hprod : ((s ^ 2 - H) * V) ^ 2 ≤ (-(τ * τ')) ^ 2 := by
      calc ((s ^ 2 - H) * V) ^ 2 = ((s ^ 2 - H) * V) * ((s ^ 2 - H) * V) := by ring
        _ ≤ τ ^ 2 * τ' ^ 2 := mul_le_mul hm hm' hm0 (sq_nonneg τ)
        _ = (-(τ * τ')) ^ 2 := by ring
    have hneg : (s ^ 2 - H) * V ≤ -(τ * τ') :=
      (pow_le_pow_iff_left₀ hm0 (by linarith) two_ne_zero).mp hprod
    have hGV : G' * V < 4 * (s ^ 2 - H) * V := mul_lt_mul_of_pos_right hG' hV
    nlinarith
  · -- Same side: compare the absolute values.
    left
    have habs : (τ - τ') ^ 2 = (|τ| - |τ'|) ^ 2 := by
      have hmul : |τ| * |τ'| = τ * τ' := by rw [← abs_mul, abs_of_pos hsame]
      calc (τ - τ') ^ 2 = τ ^ 2 + τ' ^ 2 - 2 * (τ * τ') := by ring
        _ = |τ| ^ 2 + |τ'| ^ 2 - 2 * (|τ| * |τ'|) := by rw [sq_abs, sq_abs, hmul]
        _ = (|τ| - |τ'|) ^ 2 := by ring
    have hu' : u ^ 2 * V ≤ (s ^ 2 - H) * V := mul_le_mul_of_nonneg_right hu hV.le
    rw [habs]
    rcases le_total |τ'| |τ| with hle | hle
    · refine sub_sq_le_of_sq_sub_sq_le hV.le (abs_nonneg _) hle ?_ ?_ hu0 hg0 hg
      · rw [sq_abs]; linarith
      · rw [sq_abs, sq_abs]; nlinarith
    · rw [show (|τ| - |τ'|) ^ 2 = (|τ'| - |τ|) ^ 2 by ring]
      refine sub_sq_le_of_sq_sub_sq_le hV.le (abs_nonneg _) hle ?_ ?_ hu0 hg0 hg
      · rw [sq_abs]; linarith
      · rw [sq_abs, sq_abs]; nlinarith

/-- Scalar form of Lemma J (i). Let `k² + τ²` and `k² + τ'²` lie in `[s²ρ₂E, ρ₂E]` with
`k² ≤ Hρ₂E`. Then either `(τ - τ')² ≤ g²ρ₂E` (same side) or `(τ - τ')² > G'ρ₂E`
(opposite sides), whenever `G' < 4(s² - H)`, `0 ≤ u`, `u² ≤ s² - H`, `0 ≤ g` and
`1 - s² ≤ g² + 2gu`. -/
lemma bisector_scalar_dichotomy {E k τ τ' ρ2 s H G' g u : ℝ} (hE : 0 < E) (hρ2 : 0 < ρ2)
    (hk : k ^ 2 ≤ H * ρ2 * E)
    (hlo : s ^ 2 * ρ2 * E ≤ k ^ 2 + τ ^ 2) (hhi : k ^ 2 + τ ^ 2 ≤ ρ2 * E)
    (hlo' : s ^ 2 * ρ2 * E ≤ k ^ 2 + τ' ^ 2) (hhi' : k ^ 2 + τ' ^ 2 ≤ ρ2 * E)
    (hG' : G' < 4 * (s ^ 2 - H)) (hu0 : 0 ≤ u) (hu : u ^ 2 ≤ s ^ 2 - H)
    (hg0 : 0 ≤ g) (hg : 1 - s ^ 2 ≤ g ^ 2 + 2 * g * u) :
    (τ - τ') ^ 2 ≤ g ^ 2 * ρ2 * E ∨ G' * ρ2 * E < (τ - τ') ^ 2 := by
  have e : ∀ x : ℝ, x * ρ2 * E = x * (ρ2 * E) := fun x ↦ mul_assoc _ _ _
  rw [e] at hk hlo hlo' ⊢
  rw [e]
  exact scalar_dichotomy_of_pos (mul_pos hρ2 hE) hk hlo hhi hlo' hhi' hG' hu0 hu hg0 hg

/-- Lemma J (i), squared form. Let `a, b, z, z'` lie in the annulus
`s²ρ² ≤ |x - c|² ≤ ρ²`, let `|ab|² > lρ²` with `(1 - s²)² ≤ 4lH`, and let each of `z, z'` be
equidistant from `a` and `b`. Then `|zz'|² ≤ g²ρ²` or `|zz'|² > G'ρ²`, whenever
`G' < 4(s² - H)`, `0 ≤ u`, `u² ≤ s² - H`, `0 ≤ g` and `1 - s² ≤ g² + 2gu`. -/
theorem bisector_witness_dist_sq_dichotomy {c a b z z' : Point} {ρ s l H G' g u : ℝ}
    (hρ : 0 < ρ)
    (hloa : s ^ 2 * ρ ^ 2 ≤ dist a c ^ 2) (hhia : dist a c ^ 2 ≤ ρ ^ 2)
    (hlob : s ^ 2 * ρ ^ 2 ≤ dist b c ^ 2) (hhib : dist b c ^ 2 ≤ ρ ^ 2)
    (hloz : s ^ 2 * ρ ^ 2 ≤ dist z c ^ 2) (hhiz : dist z c ^ 2 ≤ ρ ^ 2)
    (hloz' : s ^ 2 * ρ ^ 2 ≤ dist z' c ^ 2) (hhiz' : dist z' c ^ 2 ≤ ρ ^ 2)
    (hl : 0 < l) (hH : (1 - s ^ 2) ^ 2 ≤ 4 * l * H) (hab : l * ρ ^ 2 < dist a b ^ 2)
    (hza : dist z a = dist z b) (hz'a : dist z' a = dist z' b)
    (hG' : G' < 4 * (s ^ 2 - H)) (hu0 : 0 ≤ u) (hu : u ^ 2 ≤ s ^ 2 - H)
    (hg0 : 0 ≤ g) (hg : 1 - s ^ 2 ≤ g ^ 2 + 2 * g * u) :
    dist z z' ^ 2 ≤ g ^ 2 * ρ ^ 2 ∨ G' * ρ ^ 2 < dist z z' ^ 2 := by
  have hza2 : dist z a ^ 2 = dist z b ^ 2 := by rw [hza]
  have hz'a2 : dist z' a ^ 2 = dist z' b ^ 2 := by rw [hz'a]
  simp only [point_dist_sq_coordinates] at hloa hhia hlob hhib hloz hhiz hloz' hhiz'
  simp only [point_dist_sq_coordinates] at hab hza2 hz'a2 ⊢
  -- Coordinates relative to `c`, with `e = b - a`.
  set E := (b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2 with hEdef
  set k := (z 0 - c 0) * (b 0 - a 0) + (z 1 - c 1) * (b 1 - a 1) with hkdef
  set k' := (z' 0 - c 0) * (b 0 - a 0) + (z' 1 - c 1) * (b 1 - a 1) with hk'def
  set τ := (z 0 - c 0) * (b 1 - a 1) - (z 1 - c 1) * (b 0 - a 0) with hτdef
  set τ' := (z' 0 - c 0) * (b 1 - a 1) - (z' 1 - c 1) * (b 0 - a 0) with hτ'def
  set α := (a 0 - c 0) ^ 2 + (a 1 - c 1) ^ 2 with hαdef
  set β := (b 0 - c 0) ^ 2 + (b 1 - c 1) ^ 2 with hβdef
  have hEab : (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 = E := by rw [hEdef]; ring
  rw [hEab] at hab
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hE : 0 < E := lt_trans (mul_pos hl hρ2) hab
  have hk2 : 2 * k = β - α := by
    rw [hkdef, hαdef, hβdef]; linear_combination hza2
  have hkk' : k' = k := by
    rw [hkdef, hk'def]; linear_combination (hz'a2 - hza2) / 2
  have hlag : ((z 0 - c 0) ^ 2 + (z 1 - c 1) ^ 2) * E = k ^ 2 + τ ^ 2 := by
    rw [hEdef, hkdef, hτdef]; ring
  have hlag' : ((z' 0 - c 0) ^ 2 + (z' 1 - c 1) ^ 2) * E = k ^ 2 + τ' ^ 2 := by
    rw [← hkk', hEdef, hk'def, hτ'def]; ring
  have hlagd : ((z 0 - z' 0) ^ 2 + (z 1 - z' 1) ^ 2) * E = (τ - τ') ^ 2 := by
    have h : ((z 0 - z' 0) ^ 2 + (z 1 - z' 1) ^ 2) * E = (k - k') ^ 2 + (τ - τ') ^ 2 := by
      rw [hEdef, hkdef, hk'def, hτdef, hτ'def]; ring
    rw [h, hkk', sub_self]; ring
  -- `k² ≤ Hρ²E` from the annulus and the long chord.
  have hH0 : 0 ≤ H := by
    by_contra hneg
    rw [not_le] at hneg
    have : 4 * l * H < 0 := mul_neg_of_pos_of_neg (by linarith) hneg
    linarith [sq_nonneg (1 - s ^ 2)]
  have hβα : (β - α) ^ 2 ≤ ((1 - s ^ 2) * ρ ^ 2) ^ 2 := sq_le_sq' (by linarith) (by linarith)
  have hk : k ^ 2 ≤ H * ρ ^ 2 * E := by
    have h4 : 4 * k ^ 2 ≤ 4 * l * H * (ρ ^ 2) ^ 2 := by
      calc 4 * k ^ 2 = (β - α) ^ 2 := by rw [← hk2]; ring
        _ ≤ ((1 - s ^ 2) * ρ ^ 2) ^ 2 := hβα
        _ = (1 - s ^ 2) ^ 2 * (ρ ^ 2) ^ 2 := by ring
        _ ≤ 4 * l * H * (ρ ^ 2) ^ 2 := mul_le_mul_of_nonneg_right hH (by positivity)
    have h5 : H * ρ ^ 2 * (l * ρ ^ 2) ≤ H * ρ ^ 2 * E :=
      mul_le_mul_of_nonneg_left hab.le (mul_nonneg hH0 hρ2.le)
    linarith
  have hzlo : s ^ 2 * ρ ^ 2 * E ≤ k ^ 2 + τ ^ 2 := by
    rw [← hlag]; exact mul_le_mul_of_nonneg_right hloz hE.le
  have hzhi : k ^ 2 + τ ^ 2 ≤ ρ ^ 2 * E := by
    rw [← hlag]; exact mul_le_mul_of_nonneg_right hhiz hE.le
  have hz'lo : s ^ 2 * ρ ^ 2 * E ≤ k ^ 2 + τ' ^ 2 := by
    rw [← hlag']; exact mul_le_mul_of_nonneg_right hloz' hE.le
  have hz'hi : k ^ 2 + τ' ^ 2 ≤ ρ ^ 2 * E := by
    rw [← hlag']; exact mul_le_mul_of_nonneg_right hhiz' hE.le
  rcases bisector_scalar_dichotomy hE hρ2 hk hzlo hzhi hz'lo hz'hi hG' hu0 hu hg0 hg with
    h | h
  · left
    rw [← hlagd] at h
    exact le_of_mul_le_mul_right h hE
  · right
    rw [← hlagd] at h
    exact lt_of_mul_lt_mul_right h hE.le

end Esgk
