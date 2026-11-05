/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.Definitions
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import LeanPool.IwaniecLinearSieve.SieveFunctions.Defs
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Polynomial.Basic

/-!
# Lemmas 3 and 4 of [I71, §3]

* Lemma 3: `ψ(s) = s⁻¹ e^{s-3} (1 + 3 log (3/(s-1)))` satisfies `ψ(s) ≤ ψ(2)` on `[2, 4]`.
* Lemma 4: with `a = sup_{2 ≤ s ≤ 4} g₂(s) s⁻¹ eˢ` (`gLead`) and
  `A = (e/3) ψ(2) = (1 + 3 log 3)/6 < 0.72` (`gRatio`),
  `g_{2n+1}(s) ≤ a (e/3) A^{n-1} s e^{-s}` for `s ≥ 1`, `n ≥ 1` (3.4), and
  `g_{2n+2}(s) ≤ a Aⁿ s e^{-s}` for `s ≥ 2`, `n ≥ 0` (3.5).
-/

@[expose] public section

open Real Set MeasureTheory intervalIntegral

namespace IwaniecLinearSieve

/-! ### Numerical facts -/
theorem log_three_sub_log_two_lt : log 3 - log 2 < 5 / 12 := by
  have h1 := log_three_lt_d9
  have h2 := log_two_gt_d9
  norm_num at h1 h2 ⊢
  linarith

theorem one_lt_log_three : 1 < log 3 := by
  have := log_three_gt_d9; norm_num at this ⊢; linarith

theorem exp_one_sq_lt : exp 1 ^ 2 < 2 + 6 * log 3 := by
  have h1 := exp_one_lt_d9
  have h0 := exp_pos 1
  have h3 := one_lt_log_three
  norm_num at h1
  nlinarith

/-- `s e^{-s}` is decreasing for `s ≥ 1`. -/
theorem mul_exp_neg_le_of_one_le {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) :
    v * exp (-v) ≤ u * exp (-u) := by
  have h1 : v ≤ u * exp (v - u) := by
    have := add_one_le_exp (v - u)
    nlinarith
  have h2 : exp (-u) = exp (v - u) * exp (-v) := by rw [← exp_add]; ring_nf
  rw [h2]
  have := exp_pos (-v)
  nlinarith

/-! ### Lemma 3 -/

/-- Iwaniec's `ψ(s) = s⁻¹ e^{s-3} (1 + 3 log (3/(s-1)))` [I71, Lemma 3]. -/
noncomputable def psi (s : ℝ) : ℝ := s⁻¹ * exp (s - 3) * (1 + 3 * log (3 / (s - 1)))

theorem psi_two : psi 2 = (1 + 3 * log 3) / (2 * exp 1) := by
  have : exp ((2 : ℝ) - 3) = (exp 1)⁻¹ := by rw [← exp_neg]; norm_num
  rw [psi, this]; norm_num; field_simp

/-- The key inequality behind Lemma 3: `(x-1)(1 + 3 log (3/(x-1))) ≤ 3x/(x-1)` on `(2, 4)`. -/
theorem psi_deriv_aux {x : ℝ} (hx : 2 < x) :
    (x - 1) * (1 + 3 * log (3 / (x - 1))) ≤ 3 * x / (x - 1) := by
  set y := x - 1 with hy
  have hy0 : 0 < y := by linarith
  have hx' : x = y + 1 := by ring
  rw [hx']
  have hlog : log (2 / y) ≤ 2 / y - 1 := log_le_sub_one_of_pos (by positivity)
  rw [log_div (by norm_num) hy0.ne'] at hlog
  have hL : 1 + 3 * log (3 / y) ≤ -3 / 4 + 6 / y := by
    rw [log_div (by norm_num) hy0.ne']
    have : 6 / y = 3 * (2 / y) := by ring
    linarith [log_three_sub_log_two_lt]
  have h6 : y * (6 / y) = 6 := by field_simp
  have : y * (1 + 3 * log (3 / y)) ≤ -3 / 4 * y + 6 := by
    have := mul_le_mul_of_nonneg_left hL hy0.le
    rw [mul_add y (-3 / 4), h6] at this; linarith
  rw [le_div_iff₀ hy0]
  nlinarith [sq_nonneg (y - 2)]

theorem hasDerivAt_psi {x : ℝ} (hx : 1 < x) :
    HasDerivAt psi
      (exp (x - 3) * ((x - 1) * (1 + 3 * log (3 / (x - 1))) - 3 * x / (x - 1)) /
        x ^ 2) x := by
  have hx0 : x ≠ 0 := by positivity
  have hx1 : x - 1 ≠ 0 := by linarith
  have h3 : (3 : ℝ) / (x - 1) ≠ 0 := div_ne_zero (by norm_num) hx1
  have h := (((hasDerivAt_id' x).inv hx0).mul ((hasDerivAt_id' x).sub_const 3).exp).mul
    ((((hasDerivAt_const x (3 : ℝ)).div ((hasDerivAt_id' x).sub_const 1) hx1).log h3).const_mul
      3 |>.const_add 1)
  convert h using 1
  · funext s; simp [psi]
  · simp only [Pi.div_apply, Pi.inv_apply, Pi.mul_apply]
    field_simp
    ring

/-- [I71, Lemma 3]: `ψ(s) ≤ ψ(2)` for `2 ≤ s ≤ 4`. -/
theorem psi_le_psi_two {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 4) : psi s ≤ psi 2 := by
  have hanti : AntitoneOn psi (Icc 2 4) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 2 4)
      (f' := fun x => exp (x - 3) * ((x - 1) * (1 + 3 * log (3 / (x - 1))) - 3 * x / (x - 1)) /
        x ^ 2) ?_ ?_ ?_
    · intro x hx
      exact (hasDerivAt_psi (by linarith [hx.1])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_psi (by linarith [hx.1])).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx1 : 0 < x - 1 := by linarith [hx.1]
      refine div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le (sub_nonpos.2 (psi_deriv_aux hx.1)))
        (by positivity)
  exact hanti ⟨le_rfl, by norm_num⟩ hs hs.1

/-! ### Lemma 4 -/

/-- Iwaniec's constant `a = sup_{2 ≤ s ≤ 4} g₂(s) s⁻¹ eˢ` [I71, Lemma 4]. -/
noncomputable def gLead : ℝ := sSup ((fun s => g 2 s * s⁻¹ * exp s) '' Icc 2 4)

/-- Iwaniec's constant `A = (e/3) ψ(2) = (1 + 3 log 3)/6` [I71, Lemma 4]. -/
noncomputable def gRatio : ℝ := (1 + 3 * log 3) / 6

theorem gRatio_eq : gRatio = exp 1 / 3 * psi 2 := by
  rw [psi_two, gRatio]; field_simp; ring

theorem gRatio_lt : gRatio < 0.72 := by
  have := log_three_lt_d9
  rw [gRatio]; norm_num at this ⊢; linarith

theorem gRatio_pos : 0 < gRatio := by
  rw [gRatio]; have := one_lt_log_three; positivity

theorem gRatio_lt_one : gRatio < 1 := gRatio_lt.trans (by norm_num)

theorem bddAbove_gLead : BddAbove ((fun s => g 2 s * s⁻¹ * exp s) '' Icc 2 4) :=
  isCompact_Icc.bddAbove_image <|
    (((continuous_g 2).continuousOn.mul (continuousOn_inv₀.mono fun x hx => by
      simp only [mem_compl_iff, mem_singleton_iff]; linarith [hx.1])).mul
      continuous_exp.continuousOn)

theorem le_gLead {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 4) : g 2 s * s⁻¹ * exp s ≤ gLead :=
  le_csSup bddAbove_gLead (mem_image_of_mem _ hs)

theorem gLead_nonneg : 0 ≤ gLead := by
  refine le_trans ?_ (le_gLead (s := 2) ⟨le_rfl, by norm_num⟩)
  have := g_nonneg 2 2
  positivity

/-- If `h(u) ≤ C u e^{-u}` for `u ≥ s - 1`, then `∫_s^b h(t-1)/(t-1) dt ≤ C e^{1-s}`. -/
theorem integral_shift_le {h : ℝ → ℝ} (hh : Continuous h) {C s b : ℝ} (hC : 0 ≤ C)
    (hs : 2 ≤ s) (hsb : s ≤ b) (hb : ∀ u, s - 1 ≤ u → h u ≤ C * u * exp (-u)) :
    ∫ t in s..b, h (t - 1) / (t - 1) ≤ C * exp (1 - s) := by
  have hint1 : IntervalIntegrable (fun t => h (t - 1) / (t - 1)) volume s b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hsb]
    exact (hh.comp (continuous_sub_right 1)).continuousOn.div
      (continuous_sub_right 1).continuousOn fun t ht => by linarith [ht.1]
  have hcont : Continuous fun t : ℝ => C * exp (1 - t) :=
    continuous_const.mul (continuous_exp.comp (continuous_const.sub continuous_id))
  calc ∫ t in s..b, h (t - 1) / (t - 1) ≤ ∫ t in s..b, C * exp (1 - t) := by
        refine integral_mono_on hsb hint1 (hcont.intervalIntegrable _ _) fun t ht => ?_
        have ht1 : 0 < t - 1 := by linarith [ht.1]
        rw [div_le_iff₀ ht1]
        have := hb (t - 1) (by linarith [ht.1])
        have e : exp (-(t - 1)) = exp (1 - t) := by ring_nf
        rw [e] at this; linarith
    _ = C * exp (1 - s) - C * exp (1 - b) := by
        rw [integral_eq_sub_of_hasDerivAt (f := fun t => -(C * exp (1 - t))) (fun t _ => ?_)
          (hcont.intervalIntegrable _ _)]
        · ring
        · have := (((hasDerivAt_id' t).const_sub 1).exp.const_mul C).neg
          convert this using 1; ring
    _ ≤ C * exp (1 - s) := by
        have := mul_nonneg hC (exp_pos (1 - b)).le
        linarith

/-- The inductive step of [I71, Lemma 4] in uniform form. -/
theorem g_add_three_le {n : ℕ} {C s : ℝ} (hC : 0 ≤ C) (hs : gLower (n + 3) ≤ s)
    (hb : ∀ u, s - 1 ≤ u → g (n + 2) u ≤ C * u * exp (-u)) : g (n + 3) s ≤ C * exp (1 - s) := by
  rcases le_or_gt s ((n : ℝ) + 5) with hsb | hsb
  · rw [g_add_three_eq n hs]
    exact integral_shift_le (continuous_g _) hC ((two_le_gLower _).trans hs) hsb hb
  · rw [g_eq_zero_of_le (n + 3) (by push_cast; linarith)]
    positivity

theorem gLower_two_mul_add_three (n : ℕ) : gLower (2 * n + 3) = 3 :=
  gLower_odd (not_even_two_mul_add_three n)

theorem gLower_two_mul_add_four (n : ℕ) : gLower (2 * n + 1 + 3) = 2 :=
  gLower_even (by rw [show 2 * n + 1 + 3 = 2 * n + 4 by ring]; exact even_two_mul_add_four n)

/-- For `2 ≤ s ≤ 4`: `g_{2n+4}(s) = g_{2n+4}(4) + g_{2n+3}(3) log (3/(s-1))`
(proof of [I71, Lemma 4]). -/
theorem g_even_eq_on_Icc (n : ℕ) {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 4) :
    g (2 * n + 4) s = g (2 * n + 4) 4 + g (2 * n + 3) 3 * log (3 / (s - 1)) := by
  rw [show 2 * n + 4 = 2 * n + 1 + 3 by ring]
  have h := g_add_three_sub (2 * n + 1) (u := s) (v := 4)
    (by rw [gLower_two_mul_add_four]; exact hs.1) (by rw [gLower_two_mul_add_four]; norm_num)
  have hc : ∫ t in s..4, shiftKernel (g (2 * n + 1 + 2)) t =
      ∫ t in s..4, g (2 * n + 3) 3 * (1 / (t - 1)) := by
    refine integral_congr fun t ht => ?_
    rw [uIcc_of_le hs.2] at ht
    rw [shiftKernel_of_two_le _ (by linarith [ht.1, hs.1]), show 2 * n + 1 + 2 = 2 * n + 3 by ring,
      g_eq_of_le_gLower _ (s := t - 1) (by rw [gLower_two_mul_add_three]; linarith [ht.2]),
      gLower_two_mul_add_three, mul_one_div]
  have hs1 : 0 < s - 1 := by linarith [hs.1]
  rw [hc, intervalIntegral.integral_const_mul,
    integral_comp_sub_right (fun x => 1 / x), integral_one_div_of_pos hs1 (by norm_num)] at h
  norm_num at h
  linarith

private theorem g_odd_le_of_even (n : ℕ)
    (H : ∀ s, 2 ≤ s → g (2 * n + 2) s ≤ gLead * gRatio ^ n * s * exp (-s)) {s : ℝ} (hs : 1 ≤ s) :
    g (2 * n + 3) s ≤ gLead * (exp 1 / 3) * gRatio ^ n * s * exp (-s) := by
  have hC : 0 ≤ gLead * gRatio ^ n := mul_nonneg gLead_nonneg (pow_nonneg gRatio_pos.le _)
  have h3 : ∀ s, 3 ≤ s → g (2 * n + 3) s ≤ gLead * gRatio ^ n * exp (1 - s) := fun s hs =>
    g_add_three_le hC (by rw [gLower_two_mul_add_three]; exact hs)
      fun u hu => H u (by linarith)
  have key : ∀ s, 3 ≤ s → gLead * gRatio ^ n * exp (1 - s) ≤
      gLead * (exp 1 / 3) * gRatio ^ n * s * exp (-s) := fun s hs => by
    have e : exp (1 - s) = exp 1 * exp (-s) := by rw [← exp_add]; ring_nf
    rw [e]
    have := mul_nonneg (mul_nonneg (mul_nonneg hC (exp_pos (-s)).le) (exp_pos 1).le)
      (sub_nonneg.2 hs)
    nlinarith
  rcases le_total 3 s with hs3 | hs3
  · exact (h3 s hs3).trans (key s hs3)
  · have e : g (2 * n + 3) s = g (2 * n + 3) 3 := by
      have := g_eq_of_le_gLower (2 * n + 3) (s := s) (by rw [gLower_two_mul_add_three]; exact hs3)
      rwa [gLower_two_mul_add_three] at this
    rw [e]
    refine (h3 3 le_rfl).trans ((key 3 le_rfl).trans ?_)
    have := mul_exp_neg_le_of_one_le hs hs3
    have h0 : 0 ≤ gLead * (exp 1 / 3) * gRatio ^ n := by
      have := exp_pos 1; have := gLead_nonneg; have := gRatio_pos; positivity
    have := mul_le_mul_of_nonneg_left this h0
    linarith

private theorem g_even_le_of_odd (n : ℕ)
    (H : ∀ s, 1 ≤ s → g (2 * n + 3) s ≤ gLead * (exp 1 / 3) * gRatio ^ n * s * exp (-s))
    {s : ℝ} (hs : 2 ≤ s) : g (2 * n + 4) s ≤ gLead * gRatio ^ (n + 1) * s * exp (-s) := by
  have hC : 0 ≤ gLead * (exp 1 / 3) * gRatio ^ n := by
    have := exp_pos 1; have := gLead_nonneg; have := gRatio_pos; positivity
  have h4 : ∀ s, 2 ≤ s → g (2 * n + 4) s ≤ gLead * (exp 1 / 3) * gRatio ^ n * exp (1 - s) :=
    fun s hs => by
      rw [show 2 * n + 4 = 2 * n + 1 + 3 by ring]
      exact g_add_three_le hC (by rw [gLower_two_mul_add_four]; exact hs)
        fun u hu => by rw [show 2 * n + 1 + 2 = 2 * n + 3 by ring]; exact H u (by linarith)
  have hA := gRatio_pos
  have he := exp_one_sq_lt
  rcases le_total 4 s with hs4 | hs4
  · refine (h4 s hs).trans ?_
    have e : exp (1 - s) = exp 1 * exp (-s) := by rw [← exp_add]; ring_nf
    rw [e, pow_succ]
    have h1 : exp 1 ^ 2 / 3 ≤ gRatio * s := by
      rw [gRatio]; nlinarith
    have h0 : 0 ≤ gLead * gRatio ^ n * exp (-s) :=
      mul_nonneg (mul_nonneg gLead_nonneg (pow_nonneg hA.le _)) (exp_pos _).le
    have := mul_le_mul_of_nonneg_left h1 h0
    nlinarith
  · rw [g_even_eq_on_Icc n ⟨hs, hs4⟩]
    have hg4 := h4 4 (by norm_num)
    have hg3 := H 3 (by norm_num)
    have hlog : 0 ≤ log (3 / (s - 1)) :=
      log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
    have hpsi := psi_le_psi_two ⟨hs, hs4⟩
    have hpsi' : psi s * s * exp (-s) = exp (-3) * (1 + 3 * log (3 / (s - 1))) := by
      rw [psi]
      have : exp (s - 3) * exp (-s) = exp (-3) := by rw [← exp_add]; ring_nf
      rw [← this]
      field_simp
    have e4 : exp (1 - 4) = exp (-3) := by ring_nf
    have hsum : g (2 * n + 4) 4 + g (2 * n + 3) 3 * log (3 / (s - 1)) ≤
        gLead * (exp 1 / 3) * gRatio ^ n * (psi s * s * exp (-s)) := by
      rw [hpsi']
      rw [e4] at hg4
      have := mul_le_mul_of_nonneg_right hg3 hlog
      nlinarith
    have hs0 : 0 ≤ s * exp (-s) := by positivity
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpsi hs0) hC
    calc _ ≤ gLead * (exp 1 / 3) * gRatio ^ n * (psi 2 * (s * exp (-s))) := by
          refine hsum.trans (le_of_eq_of_le ?_ this); ring
      _ = gLead * gRatio ^ (n + 1) * s * exp (-s) := by rw [pow_succ, gRatio_eq]; ring

/-- (3.5) of [I71, Lemma 4]: `g_{2n+2}(s) ≤ a Aⁿ s e^{-s}` for `s ≥ 2`, `n ≥ 0`. -/
theorem g_even_le (n : ℕ) {s : ℝ} (hs : 2 ≤ s) :
    g (2 * n + 2) s ≤ gLead * gRatio ^ n * s * exp (-s) := by
  induction n generalizing s with
  | zero =>
    simp only [mul_zero, zero_add, pow_zero, mul_one]
    rcases le_total s 4 with hs4 | hs4
    · have := le_gLead ⟨hs, hs4⟩
      have hs0 : 0 < s := by linarith
      have e : g 2 s = g 2 s * s⁻¹ * exp s * (s * exp (-s)) := by
        rw [exp_neg]; field_simp
      rw [e]
      exact (mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ s * exp (-s))).trans_eq
        (by ring)
    · rw [g_two_of_four_le hs4]
      have := gLead_nonneg
      have : 0 ≤ s := by linarith
      positivity
  | succ n ih =>
    rw [show 2 * (n + 1) + 2 = 2 * n + 4 by ring]
    exact g_even_le_of_odd n (fun s hs => g_odd_le_of_even n (fun s hs => ih hs) hs) hs

/-- (3.4) of [I71, Lemma 4] (with `n` shifted by one):
`g_{2n+3}(s) ≤ a (e/3) Aⁿ s e^{-s}` for `s ≥ 1`. -/
theorem g_odd_le (n : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    g (2 * n + 3) s ≤ gLead * (exp 1 / 3) * gRatio ^ n * s * exp (-s) :=
  g_odd_le_of_even n (fun _ hs => g_even_le n hs) hs

/-- (3.4) of [I71, Lemma 4]: `g_{2n+1}(s) ≤ a (e/3) A^{n-1} s e^{-s}` for `s ≥ 1`, `n ≥ 1`. -/
theorem g_odd_le' {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : 1 ≤ s) :
    g (2 * n + 1) s ≤ gLead * (exp 1 / 3) * gRatio ^ (n - 1) * s * exp (-s) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring, Nat.add_sub_cancel]
  exact g_odd_le m hs

end IwaniecLinearSieve
