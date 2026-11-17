/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Existence

/-!
# Quadratic expansion from first-order support expansion

Supporting convex infrastructure for Letwin arXiv:2607.24164v1
Theorem 1.2 and Lemma 2.2. Mathematical scopes and source attributions
are retained in the individual declarations.
-/

@[expose] public section

noncomputable section
open Set
open scoped RealInnerProductSpace

section SubgradientExpansionTaylor

open Set Filter
open scoped RealInnerProductSpace Topology

/-! A first-order expansion of the subgradient gives a second-order Taylor expansion of the
function. -/

namespace FunctionalInequalities.Analysis

private lemma riemann_sum_affine (N : ℕ) (hN : (N : ℝ) ≠ 0)
    (a b c s : ℝ) :
    (∑ k ∈ Finset.range N,
      (1 / (N : ℝ)) * (a + ((k : ℝ) + s) / N * b + c)) =
      a + (1 / 2 + (s - 1 / 2) / (N : ℝ)) * b + c := by
  have hs : ∀ (n : ℕ) (u v : ℝ),
      (∑ k ∈ Finset.range n, (u + (k : ℝ) * v)) =
        (n : ℝ) * u + ((n : ℝ) * ((n : ℝ) - 1) / 2) * v := by
    intro n u v
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have he :
      (fun k : ℕ => (1 / (N : ℝ)) * (a + ((k : ℝ) + s) / N * b + c)) =
      (fun k : ℕ =>
        (a + s / (N : ℝ) * b + c) / (N : ℝ) +
          (k : ℝ) * (b / (N : ℝ) ^ 2)) := by
    funext k
    ring
  rw [he, hs]
  field_simp [hN]
  ring

private lemma riemann_sum_sandwich (F s : ℕ → ℝ) (N : ℕ)
    (a b c : ℝ) (hN : 0 < (N : ℝ))
    (hstep : ∀ k < N,
      (1 / (N : ℝ)) * s k ≤ F (k + 1) - F k ∧
        F (k + 1) - F k ≤ (1 / (N : ℝ)) * s (k + 1))
    (hs : ∀ k ≤ N, |s k - a - (k : ℝ) / N * b| ≤ c) :
    (∑ k ∈ Finset.range N,
      (1 / (N : ℝ)) * (a + ((k : ℝ) + 0) / N * b + (-c))) ≤ F N - F 0 ∧
    F N - F 0 ≤ ∑ k ∈ Finset.range N,
      (1 / (N : ℝ)) * (a + ((k : ℝ) + 1) / N * b + c) := by
  rw [← Finset.sum_range_sub F N]
  constructor
  · apply Finset.sum_le_sum
    intro k hk
    have hkN := Finset.mem_range.mp hk
    have hb := (abs_le.mp (hs k (Nat.le_of_lt hkN))).1
    have hm := mul_le_mul_of_nonneg_left
      (show a + ((k : ℝ) + 0) / N * b + (-c) ≤ s k by
        simp only [add_zero]
        linarith)
      (le_of_lt (one_div_pos.mpr hN))
    exact hm.trans (hstep k hkN).1
  · apply Finset.sum_le_sum
    intro k hk
    have hkN := Finset.mem_range.mp hk
    have hb := (abs_le.mp (hs (k + 1) hkN)).2
    have hb' : s (k + 1) ≤ a + ((k : ℝ) + 1) / N * b + c := by
      push_cast at hb
      linarith
    exact (hstep k hkN).2.trans
      (mul_le_mul_of_nonneg_left hb' (le_of_lt (one_div_pos.mpr hN)))

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma inner_slope_error
    (p q h : E) (B : E →L[ℝ] E) (t e : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (he : 0 ≤ e)
    (hex : ‖q - p - B (t • h)‖ ≤ e * ‖t • h‖) :
    |⟪q, h⟫ - ⟪p, h⟫ - t * ⟪B h, h⟫| ≤ e * ‖h‖ ^ 2 := by
  have hn : ‖t • h‖ ≤ ‖h‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    nlinarith [norm_nonneg h]
  have hb := (abs_real_inner_le_norm (q - p - B (t • h)) h).trans
    (mul_le_mul_of_nonneg_right
      (hex.trans (mul_le_mul_of_nonneg_left hn he)) (norm_nonneg h))
  rw [inner_sub_left, inner_sub_left, map_smul, real_inner_smul_left] at hb
  simpa only [pow_two, mul_assoc] using hb

/-- **First-order expansion of the subdifferential gives a second-order Taylor expansion**
(Alexandrov's theorem): if every subgradient `q` of the convex `f` at points `y` near `x`
satisfies `‖q − p − B (y − x)‖ ≤ ε ‖y − x‖`, then
`|f y − f x − ⟪p, y − x⟫ − ½ ⟪B (y − x), y − x⟫| ≤ ε' ‖y − x‖²` near `x`. -/
theorem eventually_abs_sub_quadratic_le_of_subgradient_expansion [FiniteDimensional ℝ E]
    {f : E → ℝ} (hconv : ConvexOn ℝ univ f) {x p : E} {B : E →L[ℝ] E}
    (hexp :
      ∀ ε > 0,
        ∀ᶠ y in 𝓝 x,
          ∀ q : E, (∀ w, f y + ⟪q, w - y⟫ ≤ f w) → ‖q - p - B (y - x)‖ ≤ ε * ‖y - x‖) :
    ∀ ε > 0,
      ∀ᶠ y in 𝓝 x, |f y - f x - ⟪p, y - x⟫ - (1 / 2) * ⟪B (y - x), y - x⟫| ≤ ε * ‖y - x‖ ^ 2 := by
  classical
  intro ε hε
  have hε₂ : 0 < ε / 2 := by positivity
  obtain ⟨r, hr, hex⟩ := Metric.eventually_nhds_iff_ball.mp (hexp (ε / 2) hε₂)
  obtain ⟨N, hlarge⟩ := exists_nat_gt (‖B‖ / ε + 1)
  have hN : 0 < (N : ℝ) := by
    have : 0 ≤ ‖B‖ / ε := div_nonneg (norm_nonneg B) (le_of_lt hε)
    linarith
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hN
  have hmesh : (1 / (2 * (N : ℝ))) * ‖B‖ ≤ ε / 2 := by
    have hb : ‖B‖ < (N : ℝ) * ε := (div_lt_iff₀ hε).mp (by linarith : ‖B‖ / ε < (N : ℝ))
    have hd : ‖B‖ / (2 * (N : ℝ)) ≤ ε / 2 :=
      (div_le_iff₀ (by positivity : 0 < 2 * (N : ℝ))).2 (by nlinarith)
    convert hd using 1
    ring
  apply Metric.eventually_nhds_iff_ball.mpr
  refine ⟨r, hr, ?_⟩
  intro y hy
  let h : E := y - x
  let z : ℕ → E := fun k => x + ((k : ℝ) / N) • h
  have hh : ‖h‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
  have ht0 (k : ℕ) : 0 ≤ (k : ℝ) / N := div_nonneg (Nat.cast_nonneg k) (le_of_lt hN)
  have ht1 (k : ℕ) (hk : k ≤ N) : (k : ℝ) / N ≤ 1 := (div_le_one hN).2 (by exact_mod_cast hk)
  have hzsub (k : ℕ) : z k - x = ((k : ℝ) / N) • h := by
    dsimp only [z]
    exact add_sub_cancel_left x _
  have hzball (k : ℕ) (hk : k ≤ N) : z k ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_eq_norm, hzsub k]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ht0 k)]
    have hle : (k : ℝ) / N * ‖h‖ ≤ ‖h‖ := by nlinarith [ht1 k hk, norm_nonneg h]
    exact hle.trans_lt hh
  have hz0 : z 0 = x := by simp [z]
  have hzN : z N = y := by simp [z, h, hN0]
  have hzstep (k : ℕ) : z (k + 1) - z k = (1 / (N : ℝ)) • h := by
    dsimp only [z]
    rw [add_sub_add_left_eq_sub, ← sub_smul]
    congr 1
    push_cast
    ring
  let q : ℕ → E := fun k =>
    Classical.choose (exists_subgradient_slope_le_inner_add hconv (z k) h)
  have hq (k : ℕ) : ∀ w, f (z k) + ⟪q k, w - z k⟫ ≤ f w :=
    (Classical.choose_spec (exists_subgradient_slope_le_inner_add hconv (z k) h)).1
  have hslope (k : ℕ) (hk : k ≤ N) :
    |⟪q k, h⟫ - ⟪p, h⟫ - (k : ℝ) / N * ⟪B h, h⟫| ≤ (ε / 2) * ‖h‖ ^ 2 := by
    have he := hex (z k) (hzball k hk) (q k) (hq k)
    rw [hzsub k] at he
    exact
      inner_slope_error p (q k) h B ((k : ℝ) / N) (ε / 2) (ht0 k) (ht1 k hk) (le_of_lt hε₂) he
  have hstep (k : ℕ) (_hk : k < N) :
    (1 / (N : ℝ)) * ⟪q k, h⟫ ≤ f (z (k + 1)) - f (z k) ∧
      f (z (k + 1)) - f (z k) ≤ (1 / (N : ℝ)) * ⟪q (k + 1), h⟫ := by
    have hl := hq k (z (k + 1))
    rw [hzstep k, real_inner_smul_right] at hl
    have hu := hq (k + 1) (z k)
    rw [← neg_sub (z (k + 1)) (z k), hzstep k, inner_neg_right, real_inner_smul_right] at hu
    constructor <;> linarith
  obtain ⟨hl, hu⟩ :=
    riemann_sum_sandwich (fun k => f (z k)) (fun k => ⟪q k, h⟫) N ⟪p, h⟫ ⟪B h, h⟫
      ((ε / 2) * ‖h‖ ^ 2) hN hstep hslope
  rw [riemann_sum_affine N hN0] at hl hu
  have hc0 : (1 / 2 : ℝ) + (0 - 1 / 2) / (N : ℝ) = 1 / 2 - 1 / (2 * (N : ℝ)) := by ring
  have hc1 : (1 / 2 : ℝ) + (1 - 1 / 2) / (N : ℝ) = 1 / 2 + 1 / (2 * (N : ℝ)) := by ring
  rw [hc0, hzN, hz0] at hl
  rw [hc1, hzN, hz0] at hu
  have hB : |⟪B h, h⟫| ≤ ‖B‖ * ‖h‖ ^ 2 := by
    calc
      |⟪B h, h⟫| ≤ ‖B h‖ * ‖h‖ := abs_real_inner_le_norm (B h) h
      _ ≤ (‖B‖ * ‖h‖) * ‖h‖ := mul_le_mul_of_nonneg_right (B.le_opNorm h) (norm_nonneg h)
      _ = ‖B‖ * ‖h‖ ^ 2 := by ring
  have hd0 : 0 ≤ 1 / (2 * (N : ℝ)) := by positivity
  have hdisc : (1 / (2 * (N : ℝ))) * ⟪B h, h⟫ ≤ (ε / 2) * ‖h‖ ^ 2 := by
    calc
      (1 / (2 * (N : ℝ))) * ⟪B h, h⟫ ≤ (1 / (2 * (N : ℝ))) * |⟪B h, h⟫| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hd0
      _ ≤ (1 / (2 * (N : ℝ))) * (‖B‖ * ‖h‖ ^ 2) := mul_le_mul_of_nonneg_left hB hd0
      _ = ((1 / (2 * (N : ℝ))) * ‖B‖) * ‖h‖ ^ 2 := by ring
      _ ≤ (ε / 2) * ‖h‖ ^ 2 := mul_le_mul_of_nonneg_right hmesh (sq_nonneg ‖h‖)
  change |f y - f x - ⟪p, h⟫ - (1 / 2) * ⟪B h, h⟫| ≤ ε * ‖h‖ ^ 2
  apply abs_le.mpr
  constructor <;> nlinarith only [hl, hu, hdisc]

end InnerProduct

end FunctionalInequalities.Analysis

end SubgradientExpansionTaylor
