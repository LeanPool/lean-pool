/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.SieveFunctions.Bounds
import LeanPool.IwaniecLinearSieve.SieveFunctions.Defs
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Polynomial.Basic

/-!
# The functions `f` and `F` of [I71, §3]

`f(s) = Σ_{i ≥ 1} g_{2i}(s)` (`fSieve`) and `F(s) = Σ_{i ≥ 1} g_{2i+1}(s)` (`FSieve`), defined in
`IwaniecLinearSieve.Definitions`. This module proves the
Corollary to Lemma 4 of [I71]: convergence (with geometric majorants), continuity, positivity,
`f, F = O(s e^{-s})`, and the integral equations (3.6), (3.7).

Since the `g_i` are clamped (see `IwaniecLinearSieve.SieveFunctions.Defs`), the series converge
for all real `s`; `f` is constant on `s ≤ 2` and `F` on `s ≤ 3`.
-/

@[expose] public section

open Real Set MeasureTheory intervalIntegral Filter Topology

namespace IwaniecLinearSieve

/-- `f_r = f` for even `r` and `F` for odd `r` ([I71], before Lemma 7). -/
noncomputable def fr (r : ℕ) (s : ℝ) : ℝ := if Even r then fSieve s else FSieve s

/-! ### Clamping and uniform bounds -/
theorem g_odd_of_le_three' (n : ℕ) {s : ℝ} (hs : s ≤ 3) : g (2 * n + 3) s = g (2 * n + 3) 3 := by
  have := g_eq_of_le_gLower (2 * n + 3) (s := s) (by rw [gLower_two_mul_add_three]; exact hs)
  rwa [gLower_two_mul_add_three] at this

theorem g_even_le_at_two (n : ℕ) (s : ℝ) : g (2 * n + 2) s ≤ g (2 * n + 2) 2 := by
  rcases le_total 2 s with h | h
  · exact g_antitone _ h
  · rw [g_even_of_le_two n h]

theorem g_odd_le_at_three (n : ℕ) (s : ℝ) : g (2 * n + 3) s ≤ g (2 * n + 3) 3 := by
  rcases le_total 3 s with h | h
  · exact g_antitone _ h
  · rw [g_odd_of_le_three' n h]

theorem g_even_le_uniform (n : ℕ) (s : ℝ) :
    g (2 * n + 2) s ≤ gLead * 2 * exp (-2) * gRatio ^ n :=
  (g_even_le_at_two n s).trans ((g_even_le n le_rfl).trans_eq (by ring))

theorem g_odd_le_uniform (n : ℕ) (s : ℝ) :
    g (2 * n + 3) s ≤ gLead * (exp 1 / 3) * 3 * exp (-3) * gRatio ^ n :=
  (g_odd_le_at_three n s).trans ((g_odd_le n (by norm_num)).trans_eq (by ring))

theorem summable_geom_gRatio (c : ℝ) : Summable fun n : ℕ => c * gRatio ^ n :=
  (summable_geometric_of_lt_one gRatio_pos.le gRatio_lt_one).mul_left c

theorem summable_g_even (s : ℝ) : Summable fun n : ℕ => g (2 * n + 2) s :=
  Summable.of_nonneg_of_le (fun _ => g_nonneg _ _) (fun n => g_even_le_uniform n s)
    (summable_geom_gRatio _)

theorem summable_g_odd (s : ℝ) : Summable fun n : ℕ => g (2 * n + 3) s :=
  Summable.of_nonneg_of_le (fun _ => g_nonneg _ _) (fun n => g_odd_le_uniform n s)
    (summable_geom_gRatio _)

/-! ### Basic properties of `f` and `F` -/
theorem continuous_fSieve : Continuous fSieve :=
  continuous_tsum (fun _ => continuous_g _) (summable_geom_gRatio _) fun n s => by
    rw [norm_of_nonneg (g_nonneg _ _)]; exact g_even_le_uniform n s

theorem continuous_FSieve : Continuous FSieve :=
  continuous_tsum (fun _ => continuous_g _) (summable_geom_gRatio _) fun n s => by
    rw [norm_of_nonneg (g_nonneg _ _)]; exact g_odd_le_uniform n s

theorem fSieve_nonneg (s : ℝ) : 0 ≤ fSieve s := tsum_nonneg fun _ => g_nonneg _ _

theorem FSieve_nonneg (s : ℝ) : 0 ≤ FSieve s := tsum_nonneg fun _ => g_nonneg _ _

theorem fSieve_pos (s : ℝ) : 0 < fSieve s := by
  set n := ⌈s⌉₊
  have h : 0 < g (2 * n + 2) s :=
    g_pos _ (by omega) (by push_cast; linarith [Nat.le_ceil s, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  exact h.trans_le ((summable_g_even s).le_tsum n fun _ _ => g_nonneg _ _)

theorem FSieve_pos (s : ℝ) : 0 < FSieve s := by
  set n := ⌈s⌉₊
  have h : 0 < g (2 * n + 3) s :=
    g_pos _ (by omega) (by push_cast; linarith [Nat.le_ceil s, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  exact h.trans_le ((summable_g_odd s).le_tsum n fun _ _ => g_nonneg _ _)

theorem fSieve_antitone : Antitone fSieve := fun _ _ h =>
  Summable.tsum_le_tsum (fun _ => g_antitone _ h) (summable_g_even _) (summable_g_even _)

theorem FSieve_antitone : Antitone FSieve := fun _ _ h =>
  Summable.tsum_le_tsum (fun _ => g_antitone _ h) (summable_g_odd _) (summable_g_odd _)

theorem fSieve_of_le_two {s : ℝ} (hs : s ≤ 2) : fSieve s = fSieve 2 :=
  tsum_congr fun n => g_even_of_le_two n hs

/-- [I71, (3.7)], second line: `F(s) = F(3)` for `s ≤ 3`. -/
theorem FSieve_of_le_three {s : ℝ} (hs : s ≤ 3) : FSieve s = FSieve 3 :=
  tsum_congr fun n => g_odd_of_le_three' n hs

/-- `f(s) ≤ a (1 - A)⁻¹ s e^{-s}` for `s ≥ 2`. -/
theorem fSieve_le {s : ℝ} (hs : 2 ≤ s) : fSieve s ≤ gLead * (1 - gRatio)⁻¹ * s * exp (-s) :=
  calc fSieve s ≤ ∑' n : ℕ, gLead * s * exp (-s) * gRatio ^ n :=
        Summable.tsum_le_tsum (fun n => (g_even_le n hs).trans_eq (by ring)) (summable_g_even s)
          (summable_geom_gRatio _)
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one gRatio_pos.le gRatio_lt_one]; ring

/-- `F(s) ≤ a (e/3) (1 - A)⁻¹ s e^{-s}` for `s ≥ 1`. -/
theorem FSieve_le {s : ℝ} (hs : 1 ≤ s) :
    FSieve s ≤ gLead * (exp 1 / 3) * (1 - gRatio)⁻¹ * s * exp (-s) :=
  calc FSieve s ≤ ∑' n : ℕ, gLead * (exp 1 / 3) * s * exp (-s) * gRatio ^ n :=
        Summable.tsum_le_tsum (fun n => (g_odd_le n hs).trans_eq (by ring)) (summable_g_odd s)
          (summable_geom_gRatio _)
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one gRatio_pos.le gRatio_lt_one]; ring

theorem fSieve_isBigO : fSieve =O[atTop] fun s => s * exp (-s) := by
  refine Asymptotics.IsBigO.of_bound (gLead * (1 - gRatio)⁻¹) ?_
  filter_upwards [eventually_ge_atTop 2] with s hs
  rw [norm_of_nonneg (fSieve_nonneg s), norm_of_nonneg (by positivity)]
  exact (fSieve_le hs).trans_eq (by ring)

theorem FSieve_isBigO : FSieve =O[atTop] fun s => s * exp (-s) := by
  refine Asymptotics.IsBigO.of_bound (gLead * (exp 1 / 3) * (1 - gRatio)⁻¹) ?_
  filter_upwards [eventually_ge_atTop 2] with s hs
  rw [norm_of_nonneg (FSieve_nonneg s), norm_of_nonneg (by positivity)]
  exact (FSieve_le (by linarith)).trans_eq (by ring)

theorem g_even_le_fSieve (n : ℕ) (s : ℝ) : g (2 * n + 2) s ≤ fSieve s :=
  (summable_g_even s).le_tsum n fun _ _ => g_nonneg _ _

theorem g_odd_le_FSieve (n : ℕ) (s : ℝ) : g (2 * n + 3) s ≤ FSieve s :=
  (summable_g_odd s).le_tsum n fun _ _ => g_nonneg _ _

/-- Partial sums of the series for `f` are at most `f`. -/
theorem sum_g_even_le_fSieve (N : ℕ) (s : ℝ) :
    ∑ n ∈ Finset.range N, g (2 * n + 2) s ≤ fSieve s :=
  (summable_g_even s).sum_le_tsum _ fun _ _ => g_nonneg _ _

/-- Partial sums of the series for `F` are at most `F`. -/
theorem sum_g_odd_le_FSieve (N : ℕ) (s : ℝ) :
    ∑ n ∈ Finset.range N, g (2 * n + 3) s ≤ FSieve s :=
  (summable_g_odd s).sum_le_tsum _ fun _ _ => g_nonneg _ _

theorem hasSum_g_fSieve (s : ℝ) : HasSum (fun n : ℕ => g (2 * n + 2) s) (fSieve s) :=
  (summable_g_even s).hasSum

theorem hasSum_g_FSieve (s : ℝ) : HasSum (fun n : ℕ => g (2 * n + 3) s) (FSieve s) :=
  (summable_g_odd s).hasSum

/-- `Σ_{k ≥ 2} g_k(s) = f(s) + F(s)`. -/
theorem hasSum_g (s : ℝ) : HasSum (fun k : ℕ => g (k + 2) s) (fSieve s + FSieve s) :=
  HasSum.even_add_odd (hasSum_g_fSieve s) (by simpa [add_assoc] using hasSum_g_FSieve s)

theorem fr_of_even {r : ℕ} (hr : Even r) : fr r = fSieve := funext fun _ => by simp [fr, hr]

theorem fr_of_odd {r : ℕ} (hr : ¬ Even r) : fr r = FSieve := funext fun _ => by simp [fr, hr]

/-! ### The integral equations (3.6), (3.7) -/
theorem shift_div_le {h : ℝ → ℝ} {C t : ℝ} (ht : 1 < t)
    (hb : h (t - 1) ≤ C * (t - 1) * exp (-(t - 1))) :
    h (t - 1) / (t - 1) ≤ C * exp 1 * exp (-t) := by
  have ht1 : 0 < t - 1 := by linarith
  rw [div_le_iff₀ ht1]
  have e : exp (-(t - 1)) = exp 1 * exp (-t) := by rw [← exp_add]; ring_nf
  rw [e] at hb; linarith

/-- An exponentially decaying `h` gives an integrable kernel `h(t-1)/(t-1)` on `(s, ∞)`. -/
theorem integrableOn_shift {h : ℝ → ℝ} (hh : Continuous h) {C s : ℝ} (hs : 2 ≤ s)
    (hnn : ∀ u, 0 ≤ h u) (hb : ∀ u, s - 1 ≤ u → h u ≤ C * u * exp (-u)) :
    IntegrableOn (fun t => h (t - 1) / (t - 1)) (Ioi s) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi s one_pos).const_mul (C * exp 1)) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact (hh.comp (continuous_sub_right 1)).continuousOn.div
      (continuous_sub_right 1).continuousOn fun t ht => by
        have : s < t := ht; linarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : s < t := ht
    rw [norm_of_nonneg (div_nonneg (hnn _) (by linarith))]
    have := shift_div_le (C := C) (by linarith) (hb (t - 1) (by linarith))
    simpa using this

/-- Interchange of `Σ` and `∫_s^∞` for nonnegative kernels. -/
theorem tsum_integral_Ioi_shift {φ : ℕ → ℝ → ℝ} {s : ℝ} (hs : 2 ≤ s)
    (hnn : ∀ n x, 0 ≤ φ n x) (hint : ∀ n, IntegrableOn (fun t => φ n (t - 1) / (t - 1)) (Ioi s))
    (hsum : Summable fun n => ∫ t in Ioi s, φ n (t - 1) / (t - 1)) :
    ∑' n, ∫ t in Ioi s, φ n (t - 1) / (t - 1) = ∫ t in Ioi s, (∑' n, φ n (t - 1)) / (t - 1) := by
  rw [integral_tsum_of_summable_integral_norm hint]
  · congr 1; funext t; exact tsum_div_const
  · refine hsum.congr fun n => setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have : s < t := ht
    exact (norm_of_nonneg (div_nonneg (hnn _ _) (by linarith))).symm

theorem integrableOn_FSieve_shift {s : ℝ} (hs : 2 ≤ s) :
    IntegrableOn (fun t => FSieve (t - 1) / (t - 1)) (Ioi s) :=
  integrableOn_shift (C := gLead * (exp 1 / 3) * (1 - gRatio)⁻¹) continuous_FSieve hs
    FSieve_nonneg fun u hu =>
    (FSieve_le (by linarith)).trans_eq (by ring)

theorem integrableOn_fSieve_shift {s : ℝ} (hs : 3 ≤ s) :
    IntegrableOn (fun t => fSieve (t - 1) / (t - 1)) (Ioi s) :=
  integrableOn_shift (C := gLead * (1 - gRatio)⁻¹) continuous_fSieve (by linarith)
    fSieve_nonneg fun u hu =>
    (fSieve_le (by linarith)).trans_eq (by ring)

theorem g_even_add_four_eq_Ioi (n : ℕ) {s : ℝ} (hs : 2 ≤ s) :
    IntegrableOn (fun t => g (2 * n + 3) (t - 1) / (t - 1)) (Ioi s) ∧
      g (2 * n + 4) s = ∫ t in Ioi s, g (2 * n + 3) (t - 1) / (t - 1) := by
  have := g_add_three_eq_Ioi (2 * n + 1) (s := s) (by rw [gLower_two_mul_add_four]; exact hs)
  rwa [show 2 * n + 1 + 3 = 2 * n + 4 by ring, show 2 * n + 1 + 2 = 2 * n + 3 by ring] at this

theorem g_odd_add_three_eq_Ioi (n : ℕ) {s : ℝ} (hs : 3 ≤ s) :
    IntegrableOn (fun t => g (2 * n + 2) (t - 1) / (t - 1)) (Ioi s) ∧
      g (2 * n + 3) s = ∫ t in Ioi s, g (2 * n + 2) (t - 1) / (t - 1) :=
  g_add_three_eq_Ioi (2 * n) (by rw [gLower_two_mul_add_three]; exact hs)

/-- [I71, (3.6)]: `f(s) = ∫_s^∞ F(t-1)/(t-1) dt + g₂(s)` for `s ≥ 2`. -/
theorem fSieve_eq_integral {s : ℝ} (hs : 2 ≤ s) :
    fSieve s = (∫ t in Ioi s, FSieve (t - 1) / (t - 1)) + g 2 s := by
  have e : ∀ n : ℕ, g (2 * (n + 1) + 2) s = ∫ t in Ioi s, g (2 * n + 3) (t - 1) / (t - 1) :=
    fun n => by rw [show 2 * (n + 1) + 2 = 2 * n + 4 by ring]; exact (g_even_add_four_eq_Ioi n hs).2
  have hsum : Summable fun n : ℕ => g (2 * (n + 1) + 2) s :=
    (summable_nat_add_iff (f := fun n : ℕ => g (2 * n + 2) s) 1).mpr (summable_g_even s)
  have hsum' : Summable fun n : ℕ => ∫ t in Ioi s, g (2 * n + 3) (t - 1) / (t - 1) :=
    hsum.congr e
  have hT := tsum_integral_Ioi_shift (φ := fun n => g (2 * n + 3)) hs (fun _ _ => g_nonneg _ _)
    (fun n => (g_even_add_four_eq_Ioi n hs).1) hsum'
  have h0 := (summable_g_even s).tsum_eq_zero_add
  rw [tsum_congr e, hT] at h0
  rw [fSieve, h0, add_comm]
  rfl

/-- [I71, (3.7)], first line: `F(s) = ∫_s^∞ f(t-1)/(t-1) dt` for `s ≥ 3`. -/
theorem FSieve_eq_integral {s : ℝ} (hs : 3 ≤ s) :
    FSieve s = ∫ t in Ioi s, fSieve (t - 1) / (t - 1) := by
  have e : ∀ n : ℕ, g (2 * n + 3) s = ∫ t in Ioi s, g (2 * n + 2) (t - 1) / (t - 1) :=
    fun n => (g_odd_add_three_eq_Ioi n hs).2
  rw [FSieve, tsum_congr e, tsum_integral_Ioi_shift (φ := fun n => g (2 * n + 2)) (by linarith)
    (fun _ _ => g_nonneg _ _)
    (fun n => (g_odd_add_three_eq_Ioi n hs).1) ((summable_g_odd s).congr e)]
  rfl

end IwaniecLinearSieve
