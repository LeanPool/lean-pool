/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.PrimeSums.Error
public import LeanPool.IwaniecLinearSieve.Definitions
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Mertens' second theorem with the de la Vallée Poussin error term

`S x = ∑_{p ≤ x} 1/p = log (log x) + c₅ + O(pntE x)`, by partial summation against `θ`.
-/

@[expose] public section

open Real Filter Topology MeasureTheory Finset intervalIntegral
open scoped Chebyshev

namespace IwaniecLinearSieve

/-- If `|T y - T x| ≤ g x` whenever `a ≤ x ≤ y` and `g → 0`, then `T` has a limit `c` with
`|T x - c| ≤ g x` for `x ≥ a`. -/
theorem exists_abs_sub_le_of_cauchy {T g : ℝ → ℝ} {a : ℝ}
    (h : ∀ x y, a ≤ x → x ≤ y → |T y - T x| ≤ g x) (hg : Tendsto g atTop (𝓝 0)) :
    ∃ c, ∀ x ≥ a, |T x - c| ≤ g x := by
  set u : ℕ → ℝ := fun n ↦ T (a + n)
  have hu : CauchySeq u := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨X, hX⟩ := eventually_atTop.1 (hg.eventually (eventually_lt_nhds hε))
    obtain ⟨N, hN⟩ := exists_nat_ge (X - a)
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [Real.dist_eq]
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    calc |u n - u N| ≤ g (a + N) := h _ _ (by simp) (by linarith)
      _ < ε := hX _ (by linarith)
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hu
  refine ⟨c, fun x hx ↦ ?_⟩
  have h1 : Tendsto (fun n : ℕ ↦ |u n - T x|) atTop (𝓝 |c - T x|) := (hc.sub_const _).abs
  have h2 : ∀ᶠ n : ℕ in atTop, |u n - T x| ≤ g x := by
    obtain ⟨N, hN⟩ := exists_nat_ge (x - a)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    exact h x (a + n) hx (by linarith)
  rw [abs_sub_comm]
  exact le_of_tendsto h1 h2

/-- `S x = ∑_{p ≤ x} 1/p`. -/
noncomputable def S (x : ℝ) : ℝ := ∑ p ∈ primesLT (⌊x⌋₊ + 1), (p : ℝ)⁻¹

theorem S_eq_sum (x : ℝ) :
    S x = ∑ k ∈ range (⌊x⌋₊ + 1), if k.Prime then (k : ℝ)⁻¹ else 0 := by
  rw [S, primesLT, show ⌈(⌊x⌋₊ : ℝ) + 1⌉₊ = ⌊x⌋₊ + 1 by exact_mod_cast Nat.ceil_natCast _,
    Nat.primesBelow, sum_filter]

/-- The weight `log p` at primes `p`, and `0` elsewhere. -/
noncomputable def logPrime (k : ℕ) : ℝ := if k.Prime then log k else 0

theorem sum_logPrime_eq_theta (t : ℝ) :
    ∑ k ∈ Icc 0 ⌊t⌋₊, logPrime k = Chebyshev.theta t := by
  rw [Chebyshev.theta_eq_sum_Icc, sum_filter]
  rfl

theorem S_sub_S {x y : ℝ} (hxy : x ≤ y) :
    S y - S x = ∑ k ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, ((k : ℝ) * log k)⁻¹ * logPrime k := by
  rw [S_eq_sum, S_eq_sum, ← sum_Ico_eq_sub _ (by gcongr), Finset.Ico_add_one_add_one_eq_Ioc]
  refine sum_congr rfl fun k _ ↦ ?_
  unfold logPrime
  split_ifs with hk
  · have : 0 < log k := log_pos (by exact_mod_cast hk.one_lt)
    field_simp
  · simp

theorem hasDerivAt_inv_mul_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t ↦ (t * log t)⁻¹) (-((log t + 1) / (t * log t) ^ 2)) t := by
  have h0 : t ≠ 0 := by linarith
  have h1 : HasDerivAt (fun t ↦ t * log t) (1 * log t + t * t⁻¹) t :=
    (hasDerivAt_id t).mul (hasDerivAt_log h0)
  convert h1.inv (mul_ne_zero h0 (log_pos ht).ne') using 1
  rw [mul_inv_cancel₀ h0]
  ring

theorem hasDerivAt_log_log_sub_inv_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t ↦ log (log t) - (log t)⁻¹) ((log t + 1) / (t * log t) ^ 2 * t) t := by
  have h0 : t ≠ 0 := by linarith
  have hl : log t ≠ 0 := (log_pos ht).ne'
  convert ((hasDerivAt_log h0).log hl).sub ((hasDerivAt_log h0).inv hl) using 1
  field_simp
  ring

theorem continuousOn_log_add_one_div {x y : ℝ} (hx : 1 < x) :
    ContinuousOn (fun t ↦ (log t + 1) / (t * log t) ^ 2) (Set.Icc x y) := by
  have hlog : ContinuousOn log (Set.Icc x y) :=
    continuousOn_log.mono fun t ht ↦ by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht ↦ ?_
  have : 1 < t := by linarith [ht.1]
  have := log_pos this
  positivity

/-- Partial summation: the variation of `S x - log (log x)` in terms of `θ x - x`. -/
theorem S_sub_loglog_eq {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    (S y - log (log y)) - (S x - log (log x)) =
      (y * log y)⁻¹ * (θ y - y) - (x * log x)⁻¹ * (θ x - x) +
        ∫ t in x..y, (log t + 1) / (t * log t) ^ 2 * (θ t - t) := by
  have hpos : ∀ t ∈ Set.Icc x y, 1 < t := fun t ht ↦ by linarith [ht.1]
  have hderiv : ∀ t ∈ Set.Icc x y,
      HasDerivAt (fun t ↦ (t * log t)⁻¹) (-((log t + 1) / (t * log t) ^ 2)) t :=
    fun t ht ↦ hasDerivAt_inv_mul_log (hpos t ht)
  have hcont := continuousOn_log_add_one_div (y := y) (show 1 < x by linarith)
  have hint : IntegrableOn (deriv fun t ↦ (t * log t)⁻¹) (Set.Icc x y) :=
    hcont.neg.integrableOn_Icc.congr_fun (fun t ht ↦ ((hderiv t ht).deriv).symm)
      measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul logPrime (f := fun t ↦ (t * log t)⁻¹)
    (by linarith) hxy (fun t ht ↦ (hderiv t ht).differentiableAt) hint
  rw [← S_sub_S hxy] at habel
  simp only [sum_logPrime_eq_theta] at habel
  rw [setIntegral_congr_fun measurableSet_Ioc
    (g := fun t ↦ -((log t + 1) / (t * log t) ^ 2) * θ t)
    (fun t ht ↦ by rw [(hderiv t (Set.Ioc_subset_Icc_self ht)).deriv]),
    ← intervalIntegral.integral_of_le hxy] at habel
  have hcont' : ContinuousOn (fun t ↦ (log t + 1) / (t * log t) ^ 2) (Set.uIcc x y) := by
    rwa [Set.uIcc_of_le hxy]
  have hθ : IntervalIntegrable θ volume x y := Chebyshev.theta_mono.intervalIntegrable
  have hi1 := hθ.continuousOn_mul hcont'
  have hi2 : IntervalIntegrable (fun t ↦ (log t + 1) / (t * log t) ^ 2 * t) volume x y :=
    (continuousOn_id.mono (Set.subset_univ _)).intervalIntegrable.continuousOn_mul hcont'
  have hsplit : ∫ t in x..y, (log t + 1) / (t * log t) ^ 2 * (θ t - t) =
      (∫ t in x..y, (log t + 1) / (t * log t) ^ 2 * θ t) -
        ∫ t in x..y, (log t + 1) / (t * log t) ^ 2 * t := by
    rw [← integral_sub hi1 hi2]
    congr 1
    ext t
    ring
  have hneg : ∫ t in x..y, -((log t + 1) / (t * log t) ^ 2) * θ t =
      -∫ t in x..y, (log t + 1) / (t * log t) ^ 2 * θ t := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    ext t
    ring
  have hftc : ∫ t in x..y, (log t + 1) / (t * log t) ^ 2 * t =
      (log (log y) - (log y)⁻¹) - (log (log x) - (log x)⁻¹) :=
    integral_eq_sub_of_hasDerivAt
      (fun t ht ↦ hasDerivAt_log_log_sub_inv_log (hpos t (by rwa [Set.uIcc_of_le hxy] at ht)))
      hi2
  have hy0 : y ≠ 0 := by linarith
  have hx0 : x ≠ 0 := by linarith
  have hfy : (y * log y)⁻¹ * y = (log y)⁻¹ := by field_simp
  have hfx : (x * log x)⁻¹ * x = (log x)⁻¹ := by field_simp
  rw [hneg] at habel
  rw [hsplit, hftc]
  linear_combination habel - hfx + hfy

theorem half_le_log {t : ℝ} (ht : 2 ≤ t) : 1 / 2 ≤ log t := by
  have := log_two_gt_d9
  have := log_le_log (by norm_num) ht
  linarith

theorem continuousOn_deriv_pntE {x y : ℝ} (hx : 1 < x) :
    ContinuousOn (fun t ↦ pntE t * (-pntκ * (t⁻¹ / (2 * √(log t))))) (Set.Icc x y) := by
  have hpos : ∀ t ∈ Set.Icc x y, 1 < t := fun t ht ↦ by linarith [ht.1]
  have hlog : ContinuousOn log (Set.Icc x y) :=
    continuousOn_log.mono fun t ht ↦ by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hpos t ht]
  unfold pntE
  refine ContinuousOn.mul (by fun_prop) (ContinuousOn.mul (by fun_prop) ?_)
  refine ContinuousOn.div (continuousOn_inv₀.mono fun t ht ↦ ?_) (by fun_prop) fun t ht ↦ ?_
  · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hpos t ht]
  · have := sqrt_pos.2 (log_pos (hpos t ht))
    positivity

/-- The integrand in `S_sub_loglog_eq` is dominated by a multiple of `-pntE'`. -/
theorem abs_integrand_le {C t : ℝ} (hC : 0 ≤ C) (ht : 2 ≤ t)
    (hθ : |θ t - t| ≤ C * t * pntE t) :
    |(log t + 1) / (t * log t) ^ 2 * (θ t - t)| ≤
      -(12 * C / pntκ) * (pntE t * (-pntκ * (t⁻¹ / (2 * √(log t))))) := by
  have ht0 : 0 < t := by linarith
  have hL := half_le_log ht
  have hL0 : 0 < log t := by linarith
  have hs : 1 / 2 ≤ √(log t) := (le_sqrt (by norm_num) hL0.le).2 (by linarith)
  have hs0 : 0 < √(log t) := by linarith
  have hss := mul_self_sqrt hL0.le
  have hE := pntE_pos t
  have hκ := pntκ_pos
  have key : (log t + 1) * √(log t) ≤ 6 * log t ^ 2 := by nlinarith
  calc |(log t + 1) / (t * log t) ^ 2 * (θ t - t)|
      = (log t + 1) / (t * log t) ^ 2 * |θ t - t| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (log t + 1) / (t * log t) ^ 2 * (C * t * pntE t) := by gcongr
    _ = C * pntE t * ((log t + 1) / (t * log t ^ 2)) := by field_simp
    _ ≤ C * pntE t * (6 / (t * √(log t))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    _ = -(12 * C / pntκ) * (pntE t * (-pntκ * (t⁻¹ / (2 * √(log t))))) := by
        field_simp
        ring

theorem exists_abs_S_sub_loglog_sub_le :
    ∃ K, 0 ≤ K ∧ ∀ x y, 2 ≤ x → x ≤ y →
      |(S y - log (log y)) - (S x - log (log x))| ≤ K * pntE x := by
  obtain ⟨C, hC0, hC⟩ := theta_asymp
  have hκ := pntκ_pos
  refine ⟨4 * C + 12 * C / pntκ, by positivity, fun x y hx hxy ↦ ?_⟩
  rw [S_sub_loglog_eq hx hxy]
  have hy : 2 ≤ y := hx.trans hxy
  have hbd : ∀ t, x ≤ t → |(t * log t)⁻¹ * (θ t - t)| ≤ 2 * C * pntE x := by
    intro t hxt
    have ht : 2 ≤ t := hx.trans hxt
    have ht0 : 0 < t := by linarith
    have hL := half_le_log ht
    have hE := pntE_pos t
    calc |(t * log t)⁻¹ * (θ t - t)| = (t * log t)⁻¹ * |θ t - t| := by
          rw [abs_mul, abs_of_pos (inv_pos.2 (by positivity))]
      _ ≤ (t * log t)⁻¹ * (C * t * pntE t) := by gcongr; exact hC t ht
      _ = C * pntE t / log t := by field_simp
      _ ≤ 2 * C * pntE t := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith [mul_nonneg hC0 hE.le]
      _ ≤ 2 * C * pntE x := by gcongr; exact pntE_le_pntE (by linarith) hxt
  have hderivE : ∀ t ∈ Set.uIcc x y,
      HasDerivAt pntE (pntE t * (-pntκ * (t⁻¹ / (2 * √(log t))))) t := fun t ht ↦
    hasDerivAt_pntE (by rw [Set.uIcc_of_le hxy] at ht; linarith [ht.1])
  have hcontE := continuousOn_deriv_pntE (y := y) (show 1 < x by linarith)
  rw [← Set.uIcc_of_le hxy] at hcontE
  have hintE := hcontE.intervalIntegrable (μ := volume)
  have hftc : ∫ t in x..y, -(12 * C / pntκ) * (pntE t * (-pntκ * (t⁻¹ / (2 * √(log t))))) =
      12 * C / pntκ * (pntE x - pntE y) := by
    rw [intervalIntegral.integral_const_mul, integral_eq_sub_of_hasDerivAt hderivE hintE]
    ring
  have hint : |∫ t in x..y, (log t + 1) / (t * log t) ^ 2 * (θ t - t)| ≤
      12 * C / pntκ * pntE x := by
    rw [← norm_eq_abs]
    refine (norm_integral_le_of_norm_le hxy (ae_of_all _ fun t ht ↦ ?_)
      (hintE.const_mul (-(12 * C / pntκ)))).trans ?_
    · rw [norm_eq_abs]
      have ht2 : 2 ≤ t := by linarith [ht.1]
      exact abs_integrand_le hC0 ht2 (hC t ht2)
    · rw [hftc]
      have := pntE_pos y
      have : 0 ≤ 12 * C / pntκ := by positivity
      nlinarith
  have h1 := hbd y hxy
  have h2 := hbd x le_rfl
  calc _ ≤ |(y * log y)⁻¹ * (θ y - y)| + |(x * log x)⁻¹ * (θ x - x)| +
        |∫ t in x..y, (log t + 1) / (t * log t) ^ 2 * (θ t - t)| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ (4 * C + 12 * C / pntκ) * pntE x := by linarith

/-- Mertens' second theorem with the de la Vallée Poussin error term. -/
theorem S_asymp : ∃ c₅ C : ℝ, ∀ x ≥ 2, |S x - log (log x) - c₅| ≤ C * pntE x := by
  obtain ⟨K, -, hK⟩ := exists_abs_S_sub_loglog_sub_le
  obtain ⟨c, hc⟩ := exists_abs_sub_le_of_cauchy (T := fun x ↦ S x - log (log x))
    (g := fun x ↦ K * pntE x) (a := 2) hK (by simpa using tendsto_pntE.const_mul K)
  exact ⟨c, K, hc⟩

end IwaniecLinearSieve
