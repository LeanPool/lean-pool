/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.LinearSieve.Defs
public import LeanPool.IwaniecLinearSieve.SieveFunctions.LemmaFive
import LeanPool.IwaniecLinearSieve.SieveFunctions.Defs
import LeanPool.IwaniecLinearSieve.SieveMajorants.Properties
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.CompletePartialOrder
import Std.Tactic.BVDecide.Normalize.Bool

/-!
# Calculus identities for the majorants of [I71, §4]

* `fSieve_eq_integral_mainMaj`: `f(s) = ∫_s^∞ M⁺(t-1)/(t-1) dt` for `s ≥ 2`, where
  `M⁺ = mainMaj false = F + (3 - ·)⁺`; this combines (3.6) with
  `g₂(s) = ∫_s^∞ (3 - (t-1))⁺/(t-1) dt` (`g_two_eq_integral`).
* `mainMaj_false_eq_integral`: `M⁺(s) = (3 - s)⁺ + ∫_{max s 3}^∞ f(t-1)/(t-1) dt`.
* `errMaj_eq_integral`: (3.13), (3.14) for `G lower`, on `s ≥ 2` (lower sieve) and `s ≥ 3`
  (upper sieve); `errMaj false = 𝔉 = 1` on `s ≤ 3`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace IwaniecLinearSieve

/-! ### `mainMaj` -/

@[simp] theorem mainMaj_true (s : ℝ) : mainMaj true s = fSieve s := rfl

@[simp] theorem mainMaj_false (s : ℝ) : mainMaj false s = FSieve s + max (3 - s) 0 := rfl

theorem continuous_mainMaj : ∀ lower, Continuous (mainMaj lower)
  | true => continuous_fSieve
  | false => continuous_FSieve.add ((continuous_const.sub continuous_id).max continuous_const)

theorem mainMaj_nonneg : ∀ (lower : Bool) (s : ℝ), 0 ≤ mainMaj lower s
  | true, s => fSieve_nonneg s
  | false, s => add_nonneg (FSieve_nonneg s) (le_max_right _ _)

theorem mainMaj_antitone : ∀ lower, Antitone (mainMaj lower)
  | true => fSieve_antitone
  | false => fun u v h => by
    simp only [mainMaj_false]
    exact add_le_add (FSieve_antitone h) (max_le_max (by linarith) le_rfl)

theorem mainMaj_le_MSieve : ∀ (lower : Bool) (s : ℝ), mainMaj lower s ≤ MSieve s
  | true, s => by
    have := FSieve_nonneg s; have := le_max_right (3 - s) 0
    simp only [mainMaj_true, MSieve]; linarith
  | false, s => by
    have := fSieve_nonneg s
    simp only [mainMaj_false, MSieve]; linarith

/-- `g₂(s) = ∫_s^∞ (3 - (t-1))⁺/(t-1) dt` for `s ≥ 2`. -/
theorem g_two_eq_integral {s : ℝ} (hs : 2 ≤ s) :
    IntegrableOn (fun t => max (3 - (t - 1)) 0 / (t - 1)) (Ioi s) ∧
      g 2 s = ∫ t in Ioi s, max (3 - (t - 1)) 0 / (t - 1) := by
  have hz : ∀ t : ℝ, 4 ≤ t → max (3 - (t - 1)) 0 / (t - 1) = 0 := fun t ht => by
    rw [max_eq_right (by linarith), zero_div]
  rcases le_or_gt s 4 with hs4 | hs4
  · have heq : EqOn (fun t : ℝ => max (3 - (t - 1)) 0 / (t - 1)) (fun t => 3 / (t - 1) - 1)
        (Icc s 4) := fun t ht => by
      have : 0 < t - 1 := by linarith [ht.1]
      simp only
      rw [max_eq_left (by linarith [ht.2])]
      field_simp
    have hcont : ContinuousOn (fun t : ℝ => 3 / (t - 1) - 1) (Icc s 4) :=
      (continuousOn_const.div (continuousOn_id.sub continuousOn_const) fun t ht => by
        simp only [Pi.sub_apply, id]; linarith [ht.1]).sub continuousOn_const
    obtain ⟨hI, hE⟩ := integral_Ioi_eq_of_eq_zero hs4
      (((hcont.congr heq).integrableOn_Icc).mono_set Ioc_subset_Icc_self) hz
    refine ⟨hI, ?_⟩
    rw [hE, intervalIntegral.integral_congr (heq.mono (uIcc_of_le hs4).subset)]
    have hderiv : ∀ t ∈ uIcc s 4, HasDerivAt (fun t => 3 * log (t - 1) - t) (3 / (t - 1) - 1) t :=
      fun t ht => by
        rw [uIcc_of_le hs4] at ht
        have h1 : t - 1 ≠ 0 := by linarith [ht.1]
        have := ((((hasDerivAt_id' t).sub_const 1).log h1).const_mul 3).sub (hasDerivAt_id' t)
        convert this using 1; field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.mono (uIcc_of_le hs4).subset |>.intervalIntegrable), g_two_eq ⟨hs, hs4⟩,
      log_div (by norm_num) (by linarith)]
    norm_num; ring
  · obtain ⟨hI, hE⟩ := integral_Ioi_eq_of_eq_zero le_rfl (by simp) fun t ht => hz t (by linarith)
    exact ⟨hI, by rw [hE, intervalIntegral.integral_same, g_two_of_four_le hs4.le]⟩

theorem integrableOn_mainMaj_false_shift {s : ℝ} (hs : 2 ≤ s) :
    IntegrableOn (fun t => mainMaj false (t - 1) / (t - 1)) (Ioi s) := by
  simp only [mainMaj_false, add_div]
  exact (integrableOn_FSieve_shift hs).add (g_two_eq_integral hs).1

/-- `f(s) = ∫_s^∞ M⁺(t-1)/(t-1) dt` for `s ≥ 2`, with `M⁺ = F + (3 - ·)⁺` ((3.6) together with
`g_two_eq_integral`). -/
theorem fSieve_eq_integral_mainMaj {s : ℝ} (hs : 2 ≤ s) :
    fSieve s = ∫ t in Ioi s, mainMaj false (t - 1) / (t - 1) := by
  simp only [mainMaj_false, add_div]
  rw [integral_add (integrableOn_FSieve_shift hs) (g_two_eq_integral hs).1,
    ← (g_two_eq_integral hs).2, fSieve_eq_integral hs]

/-- `M⁺(s) = (3 - s)⁺ + ∫_{max s 3}^∞ f(t-1)/(t-1) dt` for every `s` ((3.7)). -/
theorem mainMaj_false_eq_integral (s : ℝ) :
    mainMaj false s = max (3 - s) 0 + ∫ t in Ioi (max s 3), fSieve (t - 1) / (t - 1) := by
  have hF : FSieve s = FSieve (max s 3) := by
    rcases le_total s 3 with h | h
    · rw [max_eq_right h, FSieve_of_le_three h]
    · rw [max_eq_left h]
  rw [mainMaj_false, hF, FSieve_eq_integral (le_max_right _ _), add_comm]

/-- `mainMaj` in terms of `fr`: `M true = f` and, on `s ≥ 3`, `M false = F`. -/
theorem mainMaj_false_of_three_le {s : ℝ} (hs : 3 ≤ s) : mainMaj false s = FSieve s := by
  rw [mainMaj_false, max_eq_right (by linarith), add_zero]

/-! ### `errMaj` -/

@[simp] theorem errMaj_true : errMaj true = majf := rfl

@[simp] theorem errMaj_false : errMaj false = majF := rfl

/-- The left end of the domain of the identities (3.13), (3.14): `2` for `𝔣`, `3` for `𝔉`. -/
def errLower : Bool → ℝ
  | true => 2
  | false => 3

@[simp] theorem errLower_true : errLower true = 2 := rfl

@[simp] theorem errLower_false : errLower false = 3 := rfl

theorem two_le_errLower (lower : Bool) : 2 ≤ errLower lower := by
  cases lower <;> norm_num [errLower]

theorem errLower_le_three (lower : Bool) : errLower lower ≤ 3 := by
  cases lower <;> norm_num [errLower]

theorem sMin_le_errLower (lower : Bool) : sMin lower ≤ errLower lower := by
  cases lower <;> norm_num [sMin, errLower]

theorem errMaj_eq_majG {lower : Bool} {r : ℕ} (h : Even r ↔ lower = true) :
    errMaj lower = majG r := by
  cases lower
  · rw [majG_of_odd (Nat.not_even_iff_odd.1 fun h' => by simpa using h.1 h')]; rfl
  · rw [majG_of_even (h.2 rfl)]; rfl

theorem majG_add_two (r : ℕ) : majG (r + 2) = majG r := by
  rcases Nat.even_or_odd r with hr | hr
  · rw [majG_of_even hr, majG_of_even (hr.add (by decide))]
  · rw [majG_of_odd hr, majG_of_odd (hr.add_even (by decide))]

theorem continuous_errMaj : ∀ lower, Continuous (errMaj lower)
  | true => continuous_majf
  | false => continuous_majF

theorem errMaj_pos : ∀ (lower : Bool) (s : ℝ), 0 < errMaj lower s
  | true, s => majf_pos s
  | false, s => majF_pos s

theorem errMaj_antitone : ∀ lower, Antitone (errMaj lower)
  | true => majf_antitone
  | false => majF_antitone

theorem errMaj_mem : ∀ (lower : Bool) (s : ℝ),
    bigM s / 3 ≤ errMaj lower s ∧ errMaj lower s ≤ 2 * bigM s / 3
  | true, s => majf_mem s
  | false, s => majF_mem s

theorem errMaj_le_two (lower : Bool) (s : ℝ) : errMaj lower s ≤ 2 := by
  linarith [(errMaj_mem lower s).2, bigM_le_three s]

theorem errMaj_false_of_le_three {s : ℝ} (hs : s ≤ 3) : errMaj false s = 1 :=
  majF_of_le_three hs

/-- The derivative of `G lower` is `-G (!lower) (t-1) t/(t-1)²` for `t > 2` (`𝔣`) and
`t > 3` (`𝔉`). -/
theorem hasDerivAt_errMaj : ∀ (lower : Bool) {t : ℝ}, errLower lower < t →
    HasDerivAt (errMaj lower) (-(errMaj (!lower) (t - 1) * t / (t - 1) ^ 2)) t
  | true, _, ht => (hasDerivAt_majf ht).congr_deriv (by simp; ring)
  | false, _, ht => (hasDerivAt_majF ht).congr_deriv (by simp; ring)

theorem tendsto_errMaj_atTop : ∀ lower, Tendsto (errMaj lower) atTop (𝓝 0)
  | true => tendsto_majf_atTop
  | false => tendsto_majF_atTop

theorem errMaj_shift_pos (lower : Bool) {t : ℝ} (ht : 1 < t) :
    0 < errMaj lower (t - 1) * t / (t - 1) ^ 2 := by
  have h1 : 0 < t - 1 := by linarith
  have := errMaj_pos lower (t - 1)
  have : 0 < t := by linarith
  positivity

/-- (3.13), (3.14): for `s ≥ 2` (`lower = true`) or `s ≥ 3` (`lower = false`),
`G lower (s) = ∫_s^∞ G (!lower) (t-1) t/(t-1)² dt`, the integrand being integrable. -/
theorem errMaj_eq_integral (lower : Bool) {s : ℝ} (hs : errLower lower ≤ s) :
    IntegrableOn (fun t => errMaj (!lower) (t - 1) * t / (t - 1) ^ 2) (Ioi s) ∧
      errMaj lower s = ∫ t in Ioi s, errMaj (!lower) (t - 1) * t / (t - 1) ^ 2 := by
  have h2 := two_le_errLower lower
  have hcont : ContinuousWithinAt (fun t => -errMaj lower t) (Ici s) s :=
    (continuous_errMaj lower).neg.continuousWithinAt
  have hderiv : ∀ t ∈ Ioi s, HasDerivAt (fun t => -errMaj lower t)
      (errMaj (!lower) (t - 1) * t / (t - 1) ^ 2) t := fun t ht =>
    (hasDerivAt_errMaj lower (hs.trans_lt ht)).neg.congr_deriv (by ring)
  have hpos : ∀ t ∈ Ioi s, 0 ≤ errMaj (!lower) (t - 1) * t / (t - 1) ^ 2 := fun t ht =>
    (errMaj_shift_pos _ (by linarith [ht.out])).le
  have hlim : Tendsto (fun t => -errMaj lower t) atTop (𝓝 0) := by
    simpa using (tendsto_errMaj_atTop lower).neg
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos hlim]; ring

/-- The finite-interval form: `∫_s^b G (!lower) (t-1) t/(t-1)² dt = G lower (s) - G lower (b)`. -/
theorem integral_errMaj_shift (lower : Bool) {s b : ℝ} (hs : errLower lower ≤ s) (hsb : s ≤ b) :
    ∫ t in s..b, errMaj (!lower) (t - 1) * t / (t - 1) ^ 2 = errMaj lower s - errMaj lower b := by
  obtain ⟨hI, hE⟩ := errMaj_eq_integral lower hs
  rw [hE, (errMaj_eq_integral lower (hs.trans hsb)).2, intervalIntegral.integral_Ioi_sub_Ioi hI hsb]

end IwaniecLinearSieve
