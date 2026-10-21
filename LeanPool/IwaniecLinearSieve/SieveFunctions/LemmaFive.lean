/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.SieveFunctions.Series
import LeanPool.IwaniecLinearSieve.SieveFunctions.Defs
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Polynomial.Basic

/-!
# `f(2) = 2` ([I71, Lemma 5], the part we need)

We prove (3.9), `f(s) = f(4) + (F(3) + 3) log (3/(s-1)) + s - 4` on `[2, 4]`, and `f(2) = 2`,
following Iwaniec: `M = f + F` satisfies `M'(s) = -M(s-1)/(s-1)` for `s > 3` once it is extended
to `[2, 3]` by `M(s) = 3 + F(3) - s + f(s)` (`MSieve`). Then
`Q(s) = (s-1) M(s) - ∫_{s-1}^s M` has derivative `0` on `(3, 4) ∪ (4, ∞)`, so it is constant on
`[3, ∞)`, and it tends to `0` because `M(s) = O(s e^{-s})`. Evaluating `Q(3) = 0` gives
`f(4) + (F(3) + 3) log 3 = 4`, i.e. `f(s) = s - (F(3) + 3) log (s - 1)` on `[2, 4]`.

The value `F(3) = 2e^γ - 3` is not needed; only `F(3) ≥ 0` is used for the final inequality
`1 - f(s)/s ≥ 3 log (s - 1) / s` on `[2, 4]`. The rest of Lemma 5 (`F(3) = 2e^γ - 3` via Buchstab's
function) is in `IwaniecLinearSieve.EulerGamma.LemmaFive`.
-/

@[expose] public section

open Real Set MeasureTheory intervalIntegral Filter Topology

namespace IwaniecLinearSieve

/-! ### (3.9) -/

/-- [I71, (3.9)]: `f(s) = f(4) + (F(3) + 3) log (3/(s-1)) + s - 4` for `2 ≤ s ≤ 4`. -/
theorem fSieve_eq_on_Icc' {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 4) :
    fSieve s = fSieve 4 + (FSieve 3 + 3) * log (3 / (s - 1)) + s - 4 := by
  have hs' := (summable_g_even s).tsum_eq_zero_add
  have h4 := (summable_g_even 4).tsum_eq_zero_add
  have e : ∀ n : ℕ, g (2 * (n + 1) + 2) s =
      g (2 * (n + 1) + 2) 4 + g (2 * n + 3) 3 * log (3 / (s - 1)) := fun n => by
    rw [show 2 * (n + 1) + 2 = 2 * n + 4 by ring]; exact g_even_eq_on_Icc n hs
  have hsum4 : Summable fun n : ℕ => g (2 * (n + 1) + 2) 4 :=
    (summable_nat_add_iff (f := fun n : ℕ => g (2 * n + 2) 4) 1).mpr (summable_g_even 4)
  rw [tsum_congr e, Summable.tsum_add hsum4 ((summable_g_odd 3).mul_right _), tsum_mul_right]
    at hs'
  rw [fSieve, fSieve, hs', h4, FSieve]
  simp only [mul_zero, zero_add]
  rw [g_two_eq hs, g_two_of_four_le le_rfl]
  ring

/-! ### Derivatives -/

/-- Derivative of `u ↦ ∫_u^∞ k`. -/
theorem hasDerivAt_integral_Ioi {k : ℝ → ℝ} {a s : ℝ} (hint : IntegrableOn k (Ioi a))
    (hc : ContinuousOn k (Ioi a)) (has : a < s) :
    HasDerivAt (fun u => ∫ t in Ioi u, k t) (-k s) s := by
  have hd : HasDerivAt (fun u => (∫ t in Ioi a, k t) - ∫ t in a..u, k t) (-k s) s := by
    refine (integral_hasDerivAt_right ?_ (hc.stronglyMeasurableAtFilter isOpen_Ioi s has)
      (hc.continuousAt (Ioi_mem_nhds has))).const_sub _
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le has.le).2
      (hint.mono_set Ioc_subset_Ioi_self)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds has] with u hu
  have := integral_Ioi_sub_Ioi hint (le_of_lt hu)
  linarith

theorem continuousOn_shift {h : ℝ → ℝ} (hh : Continuous h) :
    ContinuousOn (fun t => h (t - 1) / (t - 1)) (Ioi 1) :=
  (hh.comp (continuous_sub_right 1)).continuousOn.div (continuous_sub_right 1).continuousOn
    fun t ht => by have : (1 : ℝ) < t := ht; linarith

/-- `F'(s) = -f(s-1)/(s-1)` for `s > 3`. -/
theorem hasDerivAt_FSieve {s : ℝ} (hs : 3 < s) :
    HasDerivAt FSieve (-(fSieve (s - 1) / (s - 1))) s := by
  have hd := hasDerivAt_integral_Ioi (integrableOn_fSieve_shift le_rfl)
    ((continuousOn_shift continuous_fSieve).mono (Ioi_subset_Ioi (by norm_num))) hs
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with u hu
  exact FSieve_eq_integral (le_of_lt hu)

/-- `f'(s) = -F(s-1)/(s-1)` for `s > 4`. -/
theorem hasDerivAt_fSieve_of_four_lt {s : ℝ} (hs : 4 < s) :
    HasDerivAt fSieve (-(FSieve (s - 1) / (s - 1))) s := by
  have hd := hasDerivAt_integral_Ioi (integrableOn_FSieve_shift le_rfl)
    ((continuousOn_shift continuous_FSieve).mono (Ioi_subset_Ioi (by norm_num))) (by linarith)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with u hu
  have hu' : (4 : ℝ) < u := hu
  rw [fSieve_eq_integral (by linarith), g_two_of_four_le hu'.le, add_zero]

/-- `f'(s) = 1 - (F(3) + 3)/(s-1)` for `2 < s < 4`. -/
theorem hasDerivAt_fSieve_of_lt_four {s : ℝ} (hs2 : 2 < s) (hs4 : s < 4) :
    HasDerivAt fSieve (1 - (FSieve 3 + 3) / (s - 1)) s := by
  have hne : s - 1 ≠ 0 := by linarith
  have hd : HasDerivAt
      (fun u => fSieve 4 + (FSieve 3 + 3) * (log 3 - log (u - 1)) + u - 4)
      (1 - (FSieve 3 + 3) / (s - 1)) s := by
    have := ((((((hasDerivAt_id' s).sub_const 1).log hne).const_sub (log 3)).const_mul
      (FSieve 3 + 3)).const_add (fSieve 4)).add (hasDerivAt_id' s) |>.sub_const 4
    convert this using 1
    field_simp
    ring
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hs2 hs4] with u hu
  rw [fSieve_eq_on_Icc' ⟨hu.1.le, hu.2.le⟩, log_div (by norm_num) (by linarith [hu.1])]

/-! ### Iwaniec's `M` -/

/-- Iwaniec's `M(s)`: `f(s) + F(s)` for `s ≥ 3`, extended by `M(s) = 3 + F(3) - s + f(s)` for
`s ≤ 3` (which is `-s M'(s+1)` on `[2, 3]`). -/
noncomputable def MSieve (s : ℝ) : ℝ := fSieve s + FSieve s + max (3 - s) 0

theorem MSieve_of_three_le {s : ℝ} (hs : 3 ≤ s) : MSieve s = fSieve s + FSieve s := by
  rw [MSieve, max_eq_right (by linarith), add_zero]

theorem MSieve_of_le_three {s : ℝ} (hs : s ≤ 3) : MSieve s = 3 + FSieve 3 - s + fSieve s := by
  rw [MSieve, max_eq_left (by linarith), FSieve_of_le_three hs]; ring

theorem continuous_MSieve : Continuous MSieve :=
  (continuous_fSieve.add continuous_FSieve).add ((continuous_const.sub continuous_id).max
    continuous_const)

theorem MSieve_nonneg (s : ℝ) : 0 ≤ MSieve s := by
  have := fSieve_nonneg s; have := FSieve_nonneg s; have := le_max_right (3 - s) 0
  rw [MSieve]; linarith

theorem MSieve_antitone : Antitone MSieve := fun u v h => by
  have := fSieve_antitone h; have := FSieve_antitone h
  have : max (3 - v) 0 ≤ max (3 - u) 0 := max_le_max (by linarith) le_rfl
  rw [MSieve, MSieve]; linarith

/-- `Σ_{k ≥ 2} g_k(s) = M(s)` for `s ≥ 3`. -/
theorem hasSum_g_MSieve {s : ℝ} (hs : 3 ≤ s) : HasSum (fun k : ℕ => g (k + 2) s) (MSieve s) := by
  rw [MSieve_of_three_le hs]; exact hasSum_g s

/-- `f_r(s) < M(s)` (first step of [I71, Lemma 7]). -/
theorem fr_lt_MSieve (r : ℕ) (s : ℝ) : fr r s < MSieve s := by
  have hf := fSieve_pos s; have hF := FSieve_pos s; have := le_max_right (3 - s) 0
  unfold fr MSieve; split_ifs <;> linarith

/-- `M(s) = O(s e^{-s})`: `M(s) ≤ C s e^{-s}` for `s ≥ 3`. -/
theorem MSieve_le {s : ℝ} (hs : 3 ≤ s) :
    MSieve s ≤ (gLead * (1 - gRatio)⁻¹ + gLead * (exp 1 / 3) * (1 - gRatio)⁻¹) * s * exp (-s) := by
  rw [MSieve_of_three_le hs]
  have := fSieve_le (by linarith : (2 : ℝ) ≤ s)
  have := FSieve_le (by linarith : (1 : ℝ) ≤ s)
  linarith

/-- The derivative of `M` for `s > 3`, `s ≠ 4`: `(s - 1) M'(s) = -M(s - 1)`. -/
theorem hasDerivAt_MSieve {s : ℝ} (hs3 : 3 < s) (hs4 : s ≠ 4) :
    HasDerivAt MSieve (-(MSieve (s - 1) / (s - 1))) s := by
  have hne : s - 1 ≠ 0 := by linarith
  have hev : MSieve =ᶠ[𝓝 s] fun u => fSieve u + FSieve u := by
    filter_upwards [Ioi_mem_nhds hs3] with u hu
    exact MSieve_of_three_le (le_of_lt hu)
  rcases lt_or_gt_of_ne hs4 with h4 | h4
  · have hd := (hasDerivAt_fSieve_of_lt_four (by linarith) h4).add (hasDerivAt_FSieve hs3)
    refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [MSieve_of_le_three (by linarith)]
    field_simp
    ring
  · have hd := (hasDerivAt_fSieve_of_four_lt h4).add (hasDerivAt_FSieve hs3)
    refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [MSieve_of_three_le (by linarith)]
    field_simp
    ring

/-! ### The conserved quantity -/

/-- `Q(s) = (s - 1) M(s) - ∫_{s-1}^s M`. -/
noncomputable def lemma5Q (s : ℝ) : ℝ := (s - 1) * MSieve s - ∫ x in (s - 1)..s, MSieve x

theorem lemma5Q_eq (s : ℝ) : lemma5Q s =
    (s - 1) * MSieve s - ((∫ x in (0 : ℝ)..s, MSieve x) - ∫ x in (0 : ℝ)..(s - 1), MSieve x) := by
  rw [lemma5Q, integral_interval_sub_left (continuous_MSieve.intervalIntegrable _ _)
    (continuous_MSieve.intervalIntegrable _ _)]

theorem continuous_lemma5Q : Continuous lemma5Q := by
  have hP : Continuous fun u => ∫ x in (0 : ℝ)..u, MSieve x :=
    continuous_primitive (fun _ _ => continuous_MSieve.intervalIntegrable _ _) 0
  rw [funext lemma5Q_eq]
  exact ((continuous_id.sub continuous_const).mul continuous_MSieve).sub
    (hP.sub (hP.comp (continuous_id.sub continuous_const)))

theorem hasDerivAt_lemma5Q {s : ℝ} (hs3 : 3 < s) (hs4 : s ≠ 4) : HasDerivAt lemma5Q 0 s := by
  have hM := hasDerivAt_MSieve hs3 hs4
  have hP : ∀ u, HasDerivAt (fun u => ∫ x in (0 : ℝ)..u, MSieve x) (MSieve u) u := fun u =>
    (continuous_MSieve.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hP1 : HasDerivAt (fun u => ∫ x in (0 : ℝ)..(u - 1), MSieve x) (MSieve (s - 1)) s :=
    HasDerivAt.comp_sub_const s 1 (hP (s - 1))
  have hd := (((hasDerivAt_id' s).sub_const 1).mul hM).sub ((hP s).sub hP1)
  rw [funext lemma5Q_eq]
  refine hd.congr_deriv ?_
  have hne : s - 1 ≠ 0 := by linarith
  field_simp
  ring

theorem lemma5Q_eq_of_deriv {a b : ℝ} (hab : a ≤ b) (hd : ∀ x ∈ Ioo a b, HasDerivAt lemma5Q 0 x) :
    lemma5Q b = lemma5Q a := by
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope lemma5Q (fun _ => (0 : ℝ)) h
      continuous_lemma5Q.continuousOn hd
    have hba : b - a ≠ 0 := by linarith
    rw [eq_div_iff hba, zero_mul] at hc
    linarith

theorem lemma5Q_const {b : ℝ} (hb : 3 ≤ b) : lemma5Q b = lemma5Q 3 := by
  rcases le_total b 4 with h4 | h4
  · exact lemma5Q_eq_of_deriv hb fun x hx => hasDerivAt_lemma5Q hx.1 (by linarith [hx.2])
  · rw [lemma5Q_eq_of_deriv h4 fun x hx => hasDerivAt_lemma5Q (by linarith [hx.1])
      (by linarith [hx.1]),
      lemma5Q_eq_of_deriv (by norm_num) fun x hx => hasDerivAt_lemma5Q hx.1 (by linarith [hx.2])]

theorem abs_lemma5Q_le {b : ℝ} (hb : 4 ≤ b) :
    |lemma5Q b| ≤ ((gLead * (1 - gRatio)⁻¹ + gLead * (exp 1 / 3) * (1 - gRatio)⁻¹) * exp 1) *
      (b ^ 2 * exp (-b)) := by
  set C := gLead * (1 - gRatio)⁻¹ + gLead * (exp 1 / 3) * (1 - gRatio)⁻¹
  have hM1 : MSieve (b - 1) ≤ C * (b - 1) * exp (-(b - 1)) := MSieve_le (s := b - 1) (by linarith)
  have hMb : MSieve b ≤ MSieve (b - 1) := MSieve_antitone (by linarith)
  have hI0 : 0 ≤ ∫ x in (b - 1)..b, MSieve x :=
    integral_nonneg (by linarith) fun x _ => MSieve_nonneg x
  have hI1 : ∫ x in (b - 1)..b, MSieve x ≤ MSieve (b - 1) := by
    have := integral_mono_on (μ := volume) (by linarith : b - 1 ≤ b)
      (continuous_MSieve.intervalIntegrable _ _)
      (intervalIntegrable_const (c := MSieve (b - 1))) fun x hx => MSieve_antitone hx.1
    simpa using this
  have hQ : |lemma5Q b| ≤ b * MSieve (b - 1) := by
    rw [lemma5Q, abs_le]
    have := MSieve_nonneg b
    constructor <;> nlinarith
  have he : exp (-(b - 1)) = exp 1 * exp (-b) := by rw [← exp_add]; ring_nf
  rw [he] at hM1
  refine hQ.trans ?_
  have := mul_le_mul_of_nonneg_left hM1 (by linarith : (0 : ℝ) ≤ b)
  have hb' : 0 ≤ C * exp 1 * exp (-b) * b := by
    have : 0 ≤ C := by
      have := gLead_nonneg; have := gRatio_lt_one; have := exp_pos 1
      have : 0 ≤ (1 - gRatio)⁻¹ := inv_nonneg.2 (by linarith)
      positivity
    have := exp_pos 1; have := exp_pos (-b); positivity
  nlinarith

theorem lemma5Q_three : lemma5Q 3 = 0 := by
  set C := (gLead * (1 - gRatio)⁻¹ + gLead * (exp 1 / 3) * (1 - gRatio)⁻¹) * exp 1
  have hlim : Tendsto lemma5Q atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by
      simpa using (tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul C)
    filter_upwards [eventually_ge_atTop 4] with b hb
    rw [norm_eq_abs]; exact abs_lemma5Q_le hb
  have hconst : Tendsto lemma5Q atTop (𝓝 (lemma5Q 3)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 3] with b hb
    exact (lemma5Q_const hb).symm
  exact tendsto_nhds_unique hconst hlim

/-! ### `f(2) = 2` -/

/-- `∫_2^3 M = F(3) - 1 + f(4) + (F(3) + 3)(2 log (3/2) - log 3 + 1)`. -/
theorem integral_MSieve_two_three :
    ∫ x in (2 : ℝ)..3, MSieve x = FSieve 3 - 1 + fSieve 4 +
      (FSieve 3 + 3) * (2 * (log 3 - log 2) - log 3 + 1) := by
  set K := FSieve 3 + 3
  set c := FSieve 3 - 1 + fSieve 4
  have hcongr :
      ∫ x in (2 : ℝ)..3, MSieve x = ∫ x in (2 : ℝ)..3, (c + K * (log 3 - log (x - 1))) := by
    refine integral_congr fun x hx => ?_
    rw [uIcc_of_le (by norm_num)] at hx
    rw [MSieve_of_le_three hx.2, fSieve_eq_on_Icc' ⟨hx.1, by linarith [hx.2]⟩,
      log_div (by norm_num) (by linarith [hx.1])]
    ring
  rw [hcongr, integral_eq_sub_of_hasDerivAt
    (f := fun x => c * x + K * ((x - 1) * (log 3 - log (x - 1)) + x))]
  · norm_num
    ring
  · intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    have hne : x - 1 ≠ 0 := by linarith [hx.1]
    have := ((hasDerivAt_id' x).const_mul c).add
      (((((hasDerivAt_id' x).sub_const 1).mul
        ((((hasDerivAt_id' x).sub_const 1).log hne).const_sub (log 3))).add
        (hasDerivAt_id' x)).const_mul K)
    convert this using 1
    field_simp
    ring
  · refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.add (continuousOn_const.mul (continuousOn_const.sub ?_))
    refine ((continuous_sub_right 1).continuousOn).log fun x hx => ?_
    rw [uIcc_of_le (by norm_num)] at hx
    linarith [hx.1]

/-- The key identity `f(4) + (F(3) + 3) log 3 = 4`. -/
theorem fSieve_four_add : fSieve 4 + (FSieve 3 + 3) * log 3 = 4 := by
  have h := lemma5Q_three
  rw [lemma5Q, show (3 : ℝ) - 1 = 2 by norm_num, integral_MSieve_two_three,
    MSieve_of_three_le le_rfl, fSieve_eq_on_Icc' ⟨by norm_num, by norm_num⟩,
    show (3 : ℝ) / (3 - 1) = 3 / 2 by norm_num, log_div (by norm_num) (by norm_num)] at h
  linarith

/-- [I71, Lemma 5] in the form we need: `f(s) = s - (F(3) + 3) log (s - 1)` for `2 ≤ s ≤ 4`
(Iwaniec: `F(3) + 3 = 2e^γ`). -/
theorem fSieve_eq_on_Icc {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 4) :
    fSieve s = s - (FSieve 3 + 3) * log (s - 1) := by
  rw [fSieve_eq_on_Icc' hs, log_div (by norm_num) (by linarith [hs.1])]
  linarith [fSieve_four_add]

/-- [I71, (3.10)]: `f(2) = 2`. -/
theorem fSieve_two : fSieve 2 = 2 := by
  rw [fSieve_eq_on_Icc ⟨le_rfl, by norm_num⟩]; norm_num

/-- The consequence of Lemma 5 used for the sieve: `1 - f(s)/s ≥ 3 log (s - 1) / s` on `[2, 4]`. -/
theorem le_one_sub_fSieve_div {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 4) :
    3 * log (s - 1) / s ≤ 1 - fSieve s / s := by
  have hs0 : 0 < s := by linarith [hs.1]
  have hlog : 0 ≤ log (s - 1) := log_nonneg (by linarith [hs.1])
  have hF := FSieve_nonneg 3
  rw [fSieve_eq_on_Icc hs, div_le_iff₀ hs0, sub_mul, div_mul_cancel₀ _ hs0.ne']
  nlinarith

/-- `le_one_sub_fSieve_div` in the form used by the linear-sieve modules. -/
theorem one_sub_fSieve_div_ge : ∀ s ∈ Icc (2 : ℝ) 4, 1 - fSieve s / s ≥ 3 * Real.log (s - 1) / s :=
  fun _ hs => le_one_sub_fSieve_div hs

end IwaniecLinearSieve
