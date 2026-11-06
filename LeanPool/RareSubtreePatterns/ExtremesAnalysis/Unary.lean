/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.ExtremesAnalysis.TwoPoint
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Unary centering: the lattice-modulated Gumbel exponent

Deterministic part of Theorem `thm:max_string`(i) (source lines 480–485, proof 2815–2850,
inventory P20) and of Theorem `thm:max_lh`(i) (source lines 537–541, proof 3298–3326,
inventory P24).

Fix `q = μ_1 ∈ (0, 1)`, `c > 0` (the declumping constant `c_B = 1 - μ_1`) and `C > 0`, and let
`x_n = (log n + log (c C)) / log (1/q)`. For `t ∈ ℝ` the paper's level is
`h_n = m_n + 1 = ⌊x_n + t⌋ + 1 ∈ ℤ` (which may be `≤ 0` for finitely many `n`; the mark index is
`h_n.toNat`, and `TwoPoint.natCast_le_iff_not_toNat_le` identifies `{H ≤ ⌊x_n + t⌋}` with
`{h_n.toNat ≤ H}ᶜ` for every `n`). Put `Λ_n = q^{t + 1 - {x_n + t}} ∈ (q^{t+1}, q^t]`.

* Exact identity (`natCast_mul_mul_zpow_floor_add_one`): `n c C q^{⌊x_n + t⌋ + 1} = Λ_n` for
  `n ≥ 1` (integer power). With `C = 1`, `c = 1 - μ_1` and `x_n = t_n^*` this is the display of
  source line 2821 (`tStar_identity`).
* If `p_k / q^k → C` (`π_k ∼ C_μ μ_1^k`, Lemma `lem:ell_asymp`(i)), then
  `c n p_{h_n} - Λ_n → 0` (source lines 3305–3309), hence
  `exp(-c n p_{h_n}) - exp(-Λ_n) → 0` (source lines 3320–3326); also `n p_{h_n}` is bounded
  (`π_{h_n} = O(1/n)`, needed by Corollary `cor:declump_zero`) and `h_n = n^{o(1)}` (needed by
  Lemmas `lem:S_rary`(i), `lem:S_lh`(i); the source writes `h_n = O(log n)`).
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace PoissonDeclumping
namespace ExtremesAnalysis

/-! ### `O(log n)` sequences are `n^{o(1)}` -/

/-- `log n ≤ ε n^δ` eventually, for every `ε, δ > 0`. -/
theorem eventually_log_le_mul_rpow {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.log n ≤ ε * (n : ℝ) ^ δ := by
  have h := ((isLittleO_log_rpow_atTop hδ).comp_tendsto
    tendsto_natCast_atTop_atTop).def hε
  filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1'
  have hpow : 0 ≤ (n : ℝ) ^ δ := Real.rpow_nonneg (by linarith) δ
  simpa [Function.comp, Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg hpow] using hn

/-- If `f_n ≤ A log n + B` eventually along `l ≤ atTop` (with `A ≥ 0`), then `f_n ≤ n^δ`
eventually along `l`, for every `δ > 0` (the form `n^{o(1)}` of the hypotheses of Lemmas
`lem:S_rary`(i) and `lem:S_lh`(i)). -/
theorem eventually_le_rpow_of_le_log {l : Filter ℕ} (hl : l ≤ atTop) {f : ℕ → ℝ} {A B : ℝ}
    (hA : 0 ≤ A) (hf : ∀ᶠ n in l, f n ≤ A * Real.log n + B) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in l, f n ≤ (n : ℝ) ^ δ := by
  intro δ hδ
  have hε : 0 < 1 / (2 * (A + 1)) := by positivity
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  filter_upwards [hf, hl (eventually_log_le_mul_rpow hδ hε), hl (ht.eventually_ge_atTop (2 * B)),
    hl (eventually_ge_atTop 1)] with n hn hlog hB hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hpow : 0 ≤ (n : ℝ) ^ δ := Real.rpow_nonneg (by linarith) δ
  have h1 : A * Real.log n ≤ A * (1 / (2 * (A + 1)) * (n : ℝ) ^ δ) :=
    mul_le_mul_of_nonneg_left hlog hA
  have hA' : A * (1 / (2 * (A + 1))) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  have h2 : A * (1 / (2 * (A + 1)) * (n : ℝ) ^ δ) ≤ 1 / 2 * (n : ℝ) ^ δ := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hA' hpow
  linarith

/-! ### The unary centering -/

variable {q c : ℝ} {x : ℕ → ℝ}

/-- `x_n → ∞`. -/
theorem tendsto_unaryCenter (hq0 : 0 < q) (hq1 : q < 1) {a : ℝ}
    (hx : ∀ n, x n = (Real.log n + a) / Real.log (1 / q)) : Tendsto x atTop atTop := by
  have hL : 0 < Real.log (1 / q) := Real.log_pos (by rw [lt_div_iff₀ hq0]; linarith)
  have h : Tendsto (fun n : ℕ => (Real.log n + a) / Real.log (1 / q)) atTop atTop :=
    (tendsto_atTop_add_const_right _ a
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).atTop_div_const hL
  exact h.congr fun n => (hx n).symm

/-- `q^{x_n} = (n c)⁻¹` for `n ≥ 1`. -/
theorem rpow_unaryCenter (hq0 : 0 < q) (hq1 : q < 1) (hc : 0 < c)
    (hx : ∀ n, x n = (Real.log n + Real.log c) / Real.log (1 / q)) {n : ℕ} (hn : 0 < n) :
    q ^ x n = ((n : ℝ) * c)⁻¹ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : Real.log (1 / q) ≠ 0 :=
    (Real.log_pos (by rw [lt_div_iff₀ hq0]; linarith)).ne'
  have hlog : Real.log (1 / q) = -Real.log q := by
    rw [one_div, Real.log_inv]
  rw [Real.rpow_def_of_pos hq0, hx, ← Real.exp_log (inv_pos.mpr (mul_pos hn' hc)), Real.log_inv,
    Real.log_mul hn'.ne' hc.ne']
  congr 1
  have hq : Real.log q ≠ 0 := fun h => hL (by rw [hlog, h, neg_zero])
  rw [hlog]
  field_simp

/-- Exact unary identity: `n c q^{⌊x_n + t⌋ + 1} = q^{t + 1 - {x_n + t}}` for `n ≥ 1`
(integer power on the left; the level `⌊x_n + t⌋ + 1` may be nonpositive). -/
theorem natCast_mul_mul_zpow_floor_add_one (hq0 : 0 < q) (hq1 : q < 1) (hc : 0 < c)
    (hx : ∀ n, x n = (Real.log n + Real.log c) / Real.log (1 / q)) {n : ℕ} (hn : 0 < n)
    (t : ℝ) :
    (n : ℝ) * c * q ^ (⌊x n + t⌋ + 1) = q ^ (t + 1 - Int.fract (x n + t)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.rpow_intCast]
  have hexp : (((⌊x n + t⌋ + 1 : ℤ) : ℝ)) = x n + (t + 1 - Int.fract (x n + t)) := by
    rw [Int.fract]
    push_cast
    ring
  rw [hexp, Real.rpow_add hq0, rpow_unaryCenter hq0 hq1 hc hx hn, ← mul_assoc,
    mul_inv_cancel₀ (mul_pos hn' hc).ne', one_mul]

/-- Theorem `thm:max_string`(i), source line 2821: with `t_n^* = tStar μ_1 n`,
`n (1 - μ_1) μ_1^{⌊t_n^* + t⌋ + 1} = μ_1^{t + 1 - {t_n^* + t}}` exactly, for `n ≥ 1`. -/
theorem tStar_identity (hq0 : 0 < q) (hq1 : q < 1) {n : ℕ} (hn : 0 < n) (t : ℝ) :
    (n : ℝ) * (1 - q) * q ^ (⌊tStar q n + t⌋ + 1) =
      q ^ (t + 1 - Int.fract (tStar q n + t)) :=
  natCast_mul_mul_zpow_floor_add_one hq0 hq1 (by linarith) (fun _ => rfl) hn t

/-- The lattice exponent `Λ = q^{t + 1 - {y}}` lies in `(0, q^t]`. -/
theorem rpow_lattice_bounds (hq0 : 0 < q) (hq1 : q < 1) (t y : ℝ) :
    0 < q ^ (t + 1 - Int.fract y) ∧ q ^ (t + 1 - Int.fract y) ≤ q ^ t := by
  refine ⟨Real.rpow_pos_of_pos hq0 _, ?_⟩
  apply Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le
  linarith [Int.fract_lt_one y]

/-- The unary levels `⌊x_n + t⌋ + 1` are eventually nonnegative, so their natural indices have
the same value. -/
theorem eventually_unaryLevel (hq0 : 0 < q) (hq1 : q < 1) {a : ℝ}
    (hx : ∀ n, x n = (Real.log n + a) / Real.log (1 / q)) (t : ℝ) :
    ∀ᶠ n in atTop, 0 ≤ ⌊x n + t⌋ + 1 ∧
      ((((⌊x n + t⌋ + 1).toNat : ℕ) : ℝ) = ((⌊x n + t⌋ + 1 : ℤ) : ℝ)) := by
  refine eventually_cast_toNat_eq (K := -t) (tendsto_unaryCenter hq0 hq1 hx)
    (Eventually.of_forall fun n => ?_)
  have := Int.lt_floor_add_one (x n + t)
  push_cast
  linarith

/-- The natural unary levels tend to infinity. -/
theorem tendsto_unaryLevel (hq0 : 0 < q) (hq1 : q < 1) {a : ℝ}
    (hx : ∀ n, x n = (Real.log n + a) / Real.log (1 / q)) (t : ℝ) :
    Tendsto (fun n => (⌊x n + t⌋ + 1).toNat) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [(tendsto_unaryCenter hq0 hq1 hx).eventually_ge_atTop ((b : ℝ) - t)] with n hn
  have := Int.lt_floor_add_one (x n + t)
  have h1 : ((b : ℤ) : ℝ) < ((⌊x n + t⌋ + 1 : ℤ) : ℝ) := by push_cast; linarith
  have h2 : (b : ℤ) < ⌊x n + t⌋ + 1 := by exact_mod_cast h1
  omega

/-- The unary levels are `O(log n)`, hence `n^{o(1)}` (hypothesis of Lemmas `lem:S_rary`(i) with
`r = 1` and `lem:S_lh`(i) with `κ = 1`). -/
theorem unaryLevel_le_rpow (hq0 : 0 < q) (hq1 : q < 1) {a : ℝ}
    (hx : ∀ n, x n = (Real.log n + a) / Real.log (1 / q)) (t : ℝ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ((((⌊x n + t⌋ + 1).toNat : ℕ)) : ℝ) ≤ (n : ℝ) ^ δ := by
  have hL : 0 < Real.log (1 / q) := Real.log_pos (by rw [lt_div_iff₀ hq0]; linarith)
  refine eventually_le_rpow_of_le_log le_rfl (A := 1 / Real.log (1 / q))
    (B := a / Real.log (1 / q) + |t| + 1) (by positivity) ?_
  filter_upwards [eventually_unaryLevel hq0 hq1 hx t] with n hn
  rw [hn.2]
  have := Int.floor_le (x n + t)
  have := le_abs_self t
  have hxn : x n = 1 / Real.log (1 / q) * Real.log n + a / Real.log (1 / q) := by
    rw [hx]; ring
  push_cast
  linarith

/-- If `p_k / q^k → C` with `C > 0` and `x_n = (log n + log (c C)) / log (1/q)`, then
`c n p_{⌊x_n + t⌋ + 1} - q^{t + 1 - {x_n + t}} → 0` (source lines 3305–3309, and line 2821 with
`p_k = q^k`). -/
theorem tendsto_mul_sub_lattice (hq0 : 0 < q) (hq1 : q < 1) (hc : 0 < c) {C : ℝ} (hC : 0 < C)
    {p : ℕ → ℝ} (hp : Tendsto (fun k => p k / q ^ k) atTop (𝓝 C))
    (hx : ∀ n, x n = (Real.log n + Real.log (c * C)) / Real.log (1 / q)) (t : ℝ) :
    Tendsto (fun n : ℕ => c * ((n : ℝ) * p (⌊x n + t⌋ + 1).toNat) -
      q ^ (t + 1 - Int.fract (x n + t))) atTop (𝓝 0) := by
  set h : ℕ → ℕ := fun n => (⌊x n + t⌋ + 1).toNat with h_def
  set Λ : ℕ → ℝ := fun n => q ^ (t + 1 - Int.fract (x n + t)) with hΛ
  have hR : Tendsto (fun n => p (h n) / q ^ (h n) / C - 1) atTop (𝓝 0) := by
    have := ((hp.comp (tendsto_unaryLevel hq0 hq1 hx t)).div_const C).sub_const 1
    rwa [div_self hC.ne', sub_self] at this
  have heq : ∀ᶠ n : ℕ in atTop, c * ((n : ℝ) * p (h n)) - Λ n =
      (p (h n) / q ^ (h n) / C - 1) * Λ n := by
    filter_upwards [eventually_unaryLevel hq0 hq1 hx t, eventually_gt_atTop 0] with n hn hn0
    have hid := natCast_mul_mul_zpow_floor_add_one hq0 hq1 (mul_pos hc hC) hx hn0 t
    have hz : q ^ (⌊x n + t⌋ + 1) = q ^ (h n) := by
      rw [h_def, ← zpow_natCast, Int.toNat_of_nonneg hn.1]
    rw [hz] at hid
    have hqh : q ^ (h n) ≠ 0 := (pow_pos hq0 _).ne'
    change c * ((n : ℝ) * p (h n)) - q ^ (t + 1 - Int.fract (x n + t)) =
      (p (h n) / q ^ (h n) / C - 1) * q ^ (t + 1 - Int.fract (x n + t))
    rw [← hid]
    field_simp
  refine (tendsto_congr' heq).mpr ?_
  refine squeeze_zero_norm (a := fun n : ℕ => ‖p (h n) / q ^ (h n) / C - 1‖ * q ^ t)
    (fun n => ?_) ?_
  · rw [norm_mul]
    obtain ⟨h0, h1⟩ := rpow_lattice_bounds hq0 hq1 t (x n + t)
    rw [Real.norm_of_nonneg h0.le]
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  · simpa using hR.norm.mul_const (q ^ t)

/-- `|e^{-a} - e^{-b}| ≤ |e^{-(a-b)} - 1|` for `b ≥ 0`. -/
theorem norm_exp_neg_sub_exp_neg_le (a : ℝ) {b : ℝ} (hb : 0 ≤ b) :
    ‖Real.exp (-a) - Real.exp (-b)‖ ≤ ‖Real.exp (-(a - b)) - 1‖ := by
  have heq : Real.exp (-a) - Real.exp (-b) = Real.exp (-b) * (Real.exp (-(a - b)) - 1) := by
    rw [mul_sub, ← Real.exp_add, mul_one]
    ring_nf
  rw [heq, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by linarith))

/-- `exp(-c n p_{⌊x_n + t⌋ + 1}) - exp(-q^{t + 1 - {x_n + t}}) → 0`: combined with
Corollary `cor:declump_zero` this is the lattice Gumbel limit (source lines 2840–2850,
3320–3326). -/
theorem tendsto_exp_sub_lattice (hq0 : 0 < q) (hq1 : q < 1) (hc : 0 < c) {C : ℝ} (hC : 0 < C)
    {p : ℕ → ℝ} (hp : Tendsto (fun k => p k / q ^ k) atTop (𝓝 C))
    (hx : ∀ n, x n = (Real.log n + Real.log (c * C)) / Real.log (1 / q)) (t : ℝ) :
    Tendsto (fun n : ℕ => Real.exp (-(c * ((n : ℝ) * p (⌊x n + t⌋ + 1).toNat))) -
      Real.exp (-(q ^ (t + 1 - Int.fract (x n + t))))) atTop (𝓝 0) := by
  have hd := tendsto_mul_sub_lattice hq0 hq1 hc hC hp hx t
  have hE := (hd.neg.rexp).sub_const 1
  rw [neg_zero, Real.exp_zero, sub_self] at hE
  exact squeeze_zero_norm (fun n => norm_exp_neg_sub_exp_neg_le _
    (rpow_lattice_bounds hq0 hq1 t (x n + t)).1.le) (tendsto_zero_iff_norm_tendsto_zero.mp hE)

/-- Bounded mean: `n p_{⌊x_n + t⌋ + 1}` is eventually bounded, i.e. `π_{h_n} = O(1/n)`
(hypothesis of Corollary `cor:declump_zero`, source lines 2836 and 3318). -/
theorem exists_eventually_mul_le (hq0 : 0 < q) (hq1 : q < 1) (hc : 0 < c) {C : ℝ}
    (hC : 0 < C) {p : ℕ → ℝ} (hp : Tendsto (fun k => p k / q ^ k) atTop (𝓝 C))
    (hx : ∀ n, x n = (Real.log n + Real.log (c * C)) / Real.log (1 / q)) (t : ℝ) :
    ∃ K : ℝ, ∀ᶠ n : ℕ in atTop, (n : ℝ) * p (⌊x n + t⌋ + 1).toNat ≤ K := by
  refine ⟨(q ^ t + 1) / c, ?_⟩
  have hd := tendsto_mul_sub_lattice hq0 hq1 hc hC hp hx t
  filter_upwards [hd.eventually (gt_mem_nhds one_pos)] with n hn
  have := (rpow_lattice_bounds hq0 hq1 t (x n + t)).2
  rw [le_div_iff₀ hc]
  linarith

/-! ### Specialization to Theorem `thm:max_string`(i) -/

/-- Theorem `thm:max_string`(i): with `π_k = μ_1^k`, `c_B = 1 - μ_1` and `t_n^* = tStar μ_1 n`,
`exp(-c_B n π_{⌊t_n^* + t⌋ + 1}) - exp(-μ_1^{t + 1 - {t_n^* + t}}) → 0`. -/
theorem tStar_tendsto_exp_sub (hq0 : 0 < q) (hq1 : q < 1) (t : ℝ) :
    Tendsto (fun n : ℕ => Real.exp (-((1 - q) * ((n : ℝ) * q ^ (⌊tStar q n + t⌋ + 1).toNat))) -
      Real.exp (-(q ^ (t + 1 - Int.fract (tStar q n + t))))) atTop (𝓝 0) := by
  have hp : Tendsto (fun k => q ^ k / q ^ k) atTop (𝓝 1) :=
    tendsto_const_nhds.congr fun k => (div_self (pow_pos hq0 k).ne').symm
  exact tendsto_exp_sub_lattice (c := 1 - q) (C := 1) hq0 hq1 (by linarith) one_pos hp
    (fun n => by rw [mul_one]; rfl) t

/-- Theorem `thm:max_string`(i): `n μ_1^{⌊t_n^* + t⌋ + 1}` is eventually bounded. -/
theorem tStar_exists_eventually_mul_le (hq0 : 0 < q) (hq1 : q < 1) (t : ℝ) :
    ∃ K : ℝ, ∀ᶠ n : ℕ in atTop, (n : ℝ) * q ^ (⌊tStar q n + t⌋ + 1).toNat ≤ K := by
  have hp : Tendsto (fun k => q ^ k / q ^ k) atTop (𝓝 1) :=
    tendsto_const_nhds.congr fun k => (div_self (pow_pos hq0 k).ne').symm
  exact exists_eventually_mul_le (c := 1 - q) (C := 1) hq0 hq1 (by linarith) one_pos hp
    (fun n => by rw [mul_one]; rfl) t

end ExtremesAnalysis
end PoissonDeclumping
