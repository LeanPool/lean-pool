/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Scalar cutoff profile for the noncompact integration by parts

Letwin arXiv:2607.24164v1, Lemma A.4 (p. 17), scalar part: the profile `η t = smoothTransition (2 −
t)` with its
support and derivative bounds (`smoothTransition_two_sub_cutoff`), a smooth compactly supported
majorant `w ≥ |η''|`
(`exists_majorant_abs_deriv_deriv_smoothTransition_two_sub`), and the monotone exhaustion
`η(a/(n+1)) ↑ 1`
(`monotone_and_tendsto_smoothTransition_two_sub_div_succ`), and the tail primitive `q_R t = R⁻¹
∫_{t/R}^3 w` of a
smooth nonnegative `w` vanishing off `(0, 3)` with `q_R′ t = −R⁻² w(t/R)`, `0 ≤ q_R ≤ R⁻¹ ∫_0^3 w`
and `q_R = 0` on
`t ≥ 3R` (`inv_mul_intervalIntegral_div_three_cutoff`), and the affine rescaling
`(f((· − c)/R))′(t) = R⁻¹ f′((t − c)/R)`, `'' = (R⁻¹)² f''((t − c)/R)` for arbitrary `f`, `c`, `R`,
`t`
(`deriv_comp_sub_div_and_deriv_deriv`; Lean total-derivative conventions, `R = 0` included), and the
real-parameter
exhaustion: `R ↦ η(a/R)` is monotone on `(0, ∞)` and tends to `1`
(`monotoneOn_and_tendsto_smoothTransition_two_sub_div`).
Generic real-variable tools; the cutoffs `η(W/R)` and the
quantitative generator defect of Lemma A.4 are not provided here.

Smooth bounded-range profiles (`exists_smooth_compact_extension_on_nonnegative_interval` and its
shifted logarithm and
real-power cases): a function smooth on `(-δ, ∞)` and vanishing at `0` agrees, with its derivative,
on `[0, B]` with a
smooth compactly supported Lipschitz `Φ`, `Φ 0 = 0`; used for weak chain rules of bounded
nonnegative test functions.
-/

@[expose] public section

open scoped ContDiff

namespace FunctionalInequalities.Analysis

/-- A scalar profile vanishing beyond a compact sublevel has compact support
after composition. No differentiability or convexity premise is needed. -/
theorem hasCompactSupport_comp_of_isCompact_sublevel {E : Type*} [TopologicalSpace E]
    {φ : E → ℝ} {g : ℝ → ℝ} {T : ℝ} (hφ : Continuous φ) (hsub : IsCompact {y | φ y ≤ T})
    (hg : ∀ s, T ≤ s → g s = 0) : HasCompactSupport (fun x => g (φ x)) := by
  refine HasCompactSupport.intro' hsub (isClosed_le hφ continuous_const) ?_
  intro x hx
  have hx' : ¬φ x ≤ T := hx
  exact hg (φ x) (le_of_lt (lt_of_not_ge hx'))


/--
**The cutoff profile** `η t = smoothTransition (2 − t)` (Letwin Lemma A.4, p. 17): smooth, antitone,
with values in
`[0, 1]`, equal to `1` on `t ≤ 1` and to `0` on `t ≥ 2`; `η′` and `η''` vanish off `[1, 2]`, are
compactly supported and
share a finite bound `B`. -/
theorem smoothTransition_two_sub_cutoff :
    ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (2 - s)) ∧
      Antitone (fun s : ℝ => Real.smoothTransition (2 - s)) ∧
        (∀ t : ℝ, 0 ≤ Real.smoothTransition (2 - t) ∧ Real.smoothTransition (2 - t) ≤ 1) ∧
          (∀ t : ℝ, t ≤ 1 → Real.smoothTransition (2 - t) = 1) ∧
            (∀ t : ℝ, 2 ≤ t → Real.smoothTransition (2 - t) = 0) ∧
              (∀ t : ℝ,
                  t < 1 ∨ 2 < t →
                    deriv (fun s : ℝ => Real.smoothTransition (2 - s)) t = 0 ∧
                      deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) t = 0) ∧
                HasCompactSupport (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) ∧
                  HasCompactSupport
                      (deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s)))) ∧
                    ∃ B : ℝ,
                      0 ≤ B ∧
                        ∀ t : ℝ,
                          |deriv (fun s : ℝ => Real.smoothTransition (2 - s)) t| ≤ B ∧
                            |deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) t| ≤
                              B := by
  classical
  let f : ℝ → ℝ := fun s => Real.smoothTransition (2 - s)
  have hf : ContDiff ℝ ∞ f :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)
  have hleft (t : ℝ) (ht : t ≤ 1) : f t = 1 := by
    exact Real.smoothTransition.one_of_one_le (by linarith)
  have hright (t : ℝ) (ht : 2 ≤ t) : f t = 0 := by
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  have hd (t : ℝ) (ht : t < 1 ∨ 2 < t) : deriv f t = 0 := by
    rcases ht with ht | ht
    · have he : f =ᶠ[nhds t] (fun _ : ℝ => (1 : ℝ)) := by
        filter_upwards [eventually_lt_nhds ht] with s hs
        exact hleft s hs.le
      calc
        deriv f t = deriv (fun _ : ℝ => (1 : ℝ)) t := he.deriv_eq
        _ = 0 := by simp
    · have he : f =ᶠ[nhds t] (fun _ : ℝ => (0 : ℝ)) := by
        filter_upwards [eventually_gt_nhds ht] with s hs
        exact hright s hs.le
      calc
        deriv f t = deriv (fun _ : ℝ => (0 : ℝ)) t := he.deriv_eq
        _ = 0 := by simp
  have hdd (t : ℝ) (ht : t < 1 ∨ 2 < t) : deriv (deriv f) t = 0 := by
    have he : deriv f =ᶠ[nhds t] (fun _ : ℝ => (0 : ℝ)) := by
      rcases ht with ht | ht
      · filter_upwards [eventually_lt_nhds ht] with s hs
        exact hd s (Or.inl hs)
      · filter_upwards [eventually_gt_nhds ht] with s hs
        exact hd s (Or.inr hs)
    calc
      deriv (deriv f) t = deriv (fun _ : ℝ => (0 : ℝ)) t := he.deriv_eq
      _ = 0 := by simp
  have hout (t : ℝ) (ht : t ∉ Set.Icc (1 : ℝ) 2) : t < 1 ∨ 2 < t := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using ht
  have hc : HasCompactSupport (deriv f) := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 2))
    intro t ht
    exact hd t (hout t ht)
  have hcc : HasCompactSupport (deriv (deriv f)) := hc.deriv
  have hca : HasCompactSupport (fun t => |deriv f t|) := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 2))
    intro t ht
    rw [hd t (hout t ht), abs_zero]
  have hcca : HasCompactSupport (fun t => |deriv (deriv f) t|) := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 2))
    intro t ht
    rw [hdd t (hout t ht), abs_zero]
  have hfd : ContDiff ℝ ∞ (deriv f) := by simpa using hf.iterate_deriv 1
  have hdcont : Continuous (deriv f) := by exact hf.continuous_deriv (by simp)
  have hddcont : Continuous (deriv (deriv f)) := by exact hfd.continuous_deriv (by simp)
  obtain ⟨B₁, hB₁⟩ := hdcont.abs.bounded_above_of_compact_support hca
  obtain ⟨B₂, hB₂⟩ := hddcont.abs.bounded_above_of_compact_support hcca
  have hb₁ (t : ℝ) : |deriv f t| ≤ B₁ := by simpa [Real.norm_eq_abs, abs_abs] using hB₁ t
  have hb₂ (t : ℝ) : |deriv (deriv f) t| ≤ B₂ := by
    simpa [Real.norm_eq_abs, abs_abs] using hB₂ t
  refine ⟨hf, ?_, ?_, hleft, hright, ?_, hc, hcc, ?_⟩
  · apply Real.smoothTransition.monotone.comp_antitone
    intro a b hab
    linarith
  · intro t
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro t ht
    exact ⟨hd t ht, hdd t ht⟩
  · refine ⟨max 0 (max B₁ B₂), le_max_left _ _, ?_⟩
    intro t
    exact
      ⟨(hb₁ t).trans ((le_max_left B₁ B₂).trans (le_max_right _ _)),
        (hb₂ t).trans ((le_max_right B₁ B₂).trans (le_max_right _ _))⟩

/--
**A smooth majorant of `|η''|`** (Letwin Lemma A.4, p. 17, "w ≥ |η''|"): a smooth, compactly
supported,
nonnegative `w`, zero off `(0, 3)`, with `|η''| ≤ w`. -/
theorem exists_majorant_abs_deriv_deriv_smoothTransition_two_sub :
    ∃ w : ℝ → ℝ,
      ContDiff ℝ ∞ w ∧
        HasCompactSupport w ∧
          (∀ t, 0 ≤ w t) ∧
            (∀ t, t ≤ 0 ∨ 3 ≤ t → w t = 0) ∧
              ∀ t, |deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) t| ≤ w t := by
  classical
  obtain ⟨_, _, _, _, _, houtside, _, _, ⟨B, hB, hbound⟩⟩ := smoothTransition_two_sub_cutoff
  let w : ℝ → ℝ := fun t =>
    B * Real.smoothTransition (2 * t - 1) * Real.smoothTransition (5 - 2 * t)
  have hg : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (2 * t - 1)) :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hh : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (5 - 2 * t)) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))
  refine ⟨w, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [w]
    exact (contDiff_const.mul hg).mul hh
  · dsimp [w]
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 3))
    intro t ht
    have ht' : t < 0 ∨ 3 < t := by simpa only [Set.mem_Icc, not_and_or, not_le] using ht
    rcases ht' with ht' | ht'
    · have hz : Real.smoothTransition (2 * t - 1) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      simp [hz]
    · have hz : Real.smoothTransition (5 - 2 * t) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      simp [hz]
  · intro t
    dsimp [w]
    exact
      mul_nonneg (mul_nonneg hB (Real.smoothTransition.nonneg _))
        (Real.smoothTransition.nonneg _)
  · intro t ht
    rcases ht with ht | ht
    · have hz : Real.smoothTransition (2 * t - 1) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      dsimp [w]
      simp [hz]
    · have hz : Real.smoothTransition (5 - 2 * t) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      dsimp [w]
      simp [hz]
  · intro t
    have hw (x : ℝ) : 0 ≤ w x := by
      dsimp [w]
      exact
        mul_nonneg (mul_nonneg hB (Real.smoothTransition.nonneg _))
          (Real.smoothTransition.nonneg _)
    by_cases ht : t ∈ Set.Icc (1 : ℝ) 2
    · have h₁ : Real.smoothTransition (2 * t - 1) = 1 :=
        Real.smoothTransition.one_of_one_le (by linarith [ht.1])
      have h₂ : Real.smoothTransition (5 - 2 * t) = 1 :=
        Real.smoothTransition.one_of_one_le (by linarith [ht.2])
      have hw_eq : w t = B := by simp [w, h₁, h₂]
      rw [hw_eq]
      exact (hbound t).2
    · have hout : t < 1 ∨ 2 < t := by simpa only [Set.mem_Icc, not_and_or, not_le] using ht
      have hzero := houtside t hout
      rw [hzero.2, abs_zero]
      exact hw t

/--
**Monotone exhaustion** (Letwin Lemma A.4, p. 17, `χ_R ↑ 1`): for every real `a`, `n ↦ η(a/(n+1))`
is monotone and
tends to `1`. -/
theorem monotone_and_tendsto_smoothTransition_two_sub_div_succ (a : ℝ) :
    Monotone (fun n : ℕ => Real.smoothTransition (2 - a / ((n : ℝ) + 1))) ∧
      Filter.Tendsto (fun n : ℕ => Real.smoothTransition (2 - a / ((n : ℝ) + 1))) Filter.atTop
        (nhds 1) := by
  constructor
  · intro m n hmn
    by_cases ha : 0 ≤ a
    · apply Real.smoothTransition.monotone
      have hden : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
      have hdiv : a / ((n : ℝ) + 1) ≤ a / ((m : ℝ) + 1) :=
        div_le_div_of_nonneg_left ha (by positivity) hden
      linarith
    · have hconst (k : ℕ) : Real.smoothTransition (2 - a / ((k : ℝ) + 1)) = 1 := by
        apply Real.smoothTransition.one_of_one_le
        have hdiv : a / ((k : ℝ) + 1) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
        linarith
      simp only [hconst, le_refl]
  · obtain ⟨N, hN⟩ := exists_nat_gt a
    have hevent : ∀ᶠ n : ℕ in Filter.atTop, Real.smoothTransition (2 - a / ((n : ℝ) + 1)) = 1 := by
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      apply Real.smoothTransition.one_of_one_le
      have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hpos : 0 < (n : ℝ) + 1 := by positivity
      have hdiv : a / ((n : ℝ) + 1) ≤ 1 := (div_le_one hpos).2 (by linarith)
      linarith
    exact
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1)).congr'
        (hevent.mono fun n hn => hn.symm)

/--
**Tail primitive of the majorant** (Letwin Lemma A.4, p. 17, `q_R(t) = R⁻¹ ∫_{t/R}^∞ w`): for smooth
nonnegative
`w` vanishing for `t ≤ 0` and `t ≥ 3` and `R > 0`, `q_R t = R⁻¹ ∫_{t/R}^3 w` is smooth with `q_R′ t
= −R⁻² w(t/R)`,
`0 ≤ q_R ≤ R⁻¹ ∫_0^3 w`, and `q_R t = 0` for `t ≥ 3R`. -/
theorem inv_mul_intervalIntegral_div_three_cutoff {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hw0 : ∀ t, 0 ≤ w t) (hws : ∀ t, t ≤ 0 ∨ 3 ≤ t → w t = 0) {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ ∞ (fun t => R⁻¹ * ∫ s in t / R..3, w s) ∧
      (∀ t, deriv (fun t => R⁻¹ * ∫ s in t / R..3, w s) t = -((R ^ 2)⁻¹ * w (t / R))) ∧
        (∀ t, 0 ≤ R⁻¹ * ∫ s in t / R..3, w s) ∧
          (∀ t, R⁻¹ * ∫ s in t / R..3, w s ≤ R⁻¹ * ∫ s in (0 : ℝ)..3, w s) ∧
            (∀ t, 3 * R ≤ t → R⁻¹ * ∫ s in t / R..3, w s = 0) := by
  let q : ℝ → ℝ := fun t => R⁻¹ * ∫ s in t / R..3, w s
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hRinv : 0 ≤ R⁻¹ := le_of_lt (inv_pos.mpr hR)
  have hF : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ∫ s in t..3, w s) (-w t) t := by
    intro t
    exact
      intervalIntegral.integral_hasDerivAt_left (hw.continuous.intervalIntegrable t 3)
        (hw.continuous.stronglyMeasurableAtFilter MeasureTheory.volume (nhds t))
        hw.continuous.continuousAt
  have hq_deriv : ∀ t : ℝ, HasDerivAt q (-((R ^ 2)⁻¹ * w (t / R))) t := by
    intro t
    change HasDerivAt (fun t : ℝ => R⁻¹ * ∫ s in t / R..3, w s) (-((R ^ 2)⁻¹ * w (t / R))) t
    have hcoef : R⁻¹ * ((-w (t / R)) * (1 / R)) = -((R ^ 2)⁻¹ * w (t / R)) := by
      field_simp [hR0]
    have h := ((hF (t / R)).comp t ((hasDerivAt_id t).div_const R)).const_mul R⁻¹
    simpa only [Function.comp_apply, id_eq, hcoef] using h
  have hq_diff : Differentiable ℝ q := by
    intro t
    exact (hq_deriv t).differentiableAt
  have hderiv_eq : deriv q = fun t : ℝ => -((R ^ 2)⁻¹ * w (t / R)) := by
    funext t
    exact (hq_deriv t).deriv
  have hcomp : ContDiff ℝ ∞ (fun t => w (t / R)) := by exact hw.comp (contDiff_id.div_const R)
  have hexpl : ContDiff ℝ ∞ (fun t => -((R ^ 2)⁻¹ * w (t / R))) := by
    simpa only [smul_eq_mul, Function.comp_def, id_eq] using
      (ContDiff.const_smul ((R ^ 2)⁻¹) hcomp).neg
  have hq_smooth : ContDiff ℝ ∞ q := by
    exact contDiff_infty_iff_deriv.mpr ⟨hq_diff, by rw [hderiv_eq]; exact hexpl⟩
  have hleft (a : ℝ) (ha : a ≤ 0) : (∫ s in a..0, w s) = 0 := by
    calc
      (∫ s in a..0, w s) = ∫ s in a..0, (fun _ : ℝ => 0) s := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Set.Icc a 0 := by simpa [Set.uIcc_of_le ha] using hx
        simpa using hws x (Or.inl hx'.2)
      _ = 0 := by simp
  have hright (b : ℝ) (hb : 3 ≤ b) : (∫ s in 3..b, w s) = 0 := by
    calc
      (∫ s in 3..b, w s) = ∫ s in 3..b, (fun _ : ℝ => 0) s := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Set.Icc 3 b := by simpa [Set.uIcc_of_le hb] using hx
        simpa using hws x (Or.inr hx'.1)
      _ = 0 := by simp
  have hnonneg (a b : ℝ) (hab : a ≤ b) : 0 ≤ (∫ s in a..b, w s) := by
    exact intervalIntegral.integral_nonneg hab (fun x _ => hw0 x)
  have hzero_ge (a : ℝ) (ha : 3 ≤ a) : (∫ s in a..3, w s) = 0 := by
    calc
      (∫ s in a..3, w s) = -(∫ s in 3..a, w s) := intervalIntegral.integral_symm 3 a
      _ = 0 := by rw [hright a ha]; simp
  have hadd (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ s in a..c, w s) = (∫ s in a..b, w s) + ∫ s in b..c, w s := by
    symm
    exact
      intervalIntegral.integral_add_adjacent_intervals (hw.continuous.intervalIntegrable a b)
        (hw.continuous.intervalIntegrable b c)
  have hupper (a : ℝ) : (∫ s in a..3, w s) ≤ ∫ s in (0 : ℝ)..3, w s := by
    by_cases ha : a ≤ 0
    · calc
        (∫ s in a..3, w s) = (∫ s in a..0, w s) + ∫ s in (0 : ℝ)..3, w s :=
          hadd a 0 3 ha (by norm_num)
        _ ≤ ∫ s in (0 : ℝ)..3, w s := by
          simpa only [hleft a ha, zero_add] using (le_refl (∫ s in (0 : ℝ)..3, w s))
    · have ha0 : 0 ≤ a := le_of_not_ge ha
      by_cases h3 : 3 ≤ a
      · have htot : 0 ≤ ∫ s in (0 : ℝ)..3, w s := hnonneg 0 3 (by norm_num)
        rw [hzero_ge a h3]
        linarith
      · have ha3 : a ≤ 3 := le_of_not_ge h3
        have hnon : 0 ≤ (∫ s in (0 : ℝ)..a, w s) := hnonneg 0 a ha0
        have heq : (∫ s in (0 : ℝ)..3, w s) = (∫ s in (0 : ℝ)..a, w s) + ∫ s in a..3, w s :=
          hadd 0 a 3 ha0 ha3
        rw [heq]
        linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [q] using hq_smooth
  · intro t
    simpa [q] using (hq_deriv t).deriv
  · intro t
    rcases le_total (t / R) 3 with ht | ht
    · exact mul_nonneg hRinv (hnonneg (t / R) 3 ht)
    · rw [hzero_ge (t / R) ht]
      simp
  · intro t
    exact mul_le_mul_of_nonneg_left (hupper (t / R)) hRinv
  · intro t ht
    have ht' : 3 ≤ t / R := by exact (le_div_iff₀ hR).2 ht
    change R⁻¹ * ∫ s in t / R..3, w s = 0
    rw [hzero_ge (t / R) ht']
    simp


/--
**Affine rescaling of derivatives** (Letwin Lemma A.4, p. 17, `η(W/R)` with `W = φ − c`): for
arbitrary `f`, `c`,
`R`, `t`, `(f((· − c)/R))′(t) = R⁻¹ f′((t − c)/R)` and
`(f((· − c)/R))''(t) = (R⁻¹)² f''((t − c)/R)`,
with Lean's
total-derivative conventions (no differentiability or `R ≠ 0` hypothesis). -/
theorem deriv_comp_sub_div_and_deriv_deriv (f : ℝ → ℝ) (c R t : ℝ) :
    deriv (fun s => f ((s - c) / R)) t = R⁻¹ * deriv f ((t - c) / R) ∧
      deriv (deriv (fun s => f ((s - c) / R))) t = (R⁻¹) ^ 2 * deriv (deriv f) ((t - c) / R) := by
  have hcomp :
    ∀ (g : ℝ → ℝ) (x : ℝ), deriv (fun s => g ((s - c) / R)) x = R⁻¹ * deriv g ((x - c) / R) := by
    intro g x
    calc
      deriv (fun s => g ((s - c) / R)) x = deriv (fun s => g (R⁻¹ * (s - c))) x := by
        apply congrArg (fun q : ℝ → ℝ => deriv q x)
        funext s
        simp [div_eq_mul_inv, mul_comm]
      _ = deriv (fun u => g (R⁻¹ * u)) (x - c) := by
        exact deriv_comp_sub_const (fun u : ℝ => g (R⁻¹ * u)) c x
      _ = R⁻¹ * deriv g (R⁻¹ * (x - c)) := by rw [deriv_comp_mul_left]; ring
      _ = R⁻¹ * deriv g ((x - c) / R) := by simp [div_eq_mul_inv, mul_comm]
  constructor
  · exact hcomp f t
  · have hfun : deriv (fun s => f ((s - c) / R)) = (fun s => R⁻¹ * deriv f ((s - c) / R)) := by
      funext s
      exact hcomp f s
    rw [hfun]
    calc
      deriv (fun s => R⁻¹ * deriv f ((s - c) / R)) t =
          R⁻¹ * deriv (fun s => deriv f ((s - c) / R)) t := by
        rw [deriv_const_mul_field']
      _ = R⁻¹ * (R⁻¹ * deriv (deriv f) ((t - c) / R)) := by rw [hcomp (deriv f) t]
      _ = (R⁻¹) ^ 2 * deriv (deriv f) ((t - c) / R) := by ring


/--
**Real-parameter monotone exhaustion** (Letwin Lemma A.4, p. 17, `χ_R ↑ 1` for real `R`): for every
real `a`,
`R ↦ η(a/R)` is monotone on `(0, ∞)` and tends to `1` at `atTop`, for `η t = smoothTransition (2 −
t)`. -/
theorem monotoneOn_and_tendsto_smoothTransition_two_sub_div (a : ℝ) :
    MonotoneOn (fun R : ℝ => Real.smoothTransition (2 - a / R)) (Set.Ioi 0) ∧
      Filter.Tendsto (fun R : ℝ => Real.smoothTransition (2 - a / R)) Filter.atTop (nhds 1) := by
  constructor
  · intro x hx y hy hxy
    change 0 < x at hx
    change 0 < y at hy
    by_cases ha : a < 0
    · have hax : a / x < 0 := div_neg_of_neg_of_pos ha hx
      have hay : a / y < 0 := div_neg_of_neg_of_pos ha hy
      have hxval : Real.smoothTransition (2 - a / x) = 1 :=
        Real.smoothTransition.one_of_one_le (by linarith)
      have hyval : Real.smoothTransition (2 - a / y) = 1 :=
        Real.smoothTransition.one_of_one_le (by linarith)
      change Real.smoothTransition (2 - a / x) ≤ Real.smoothTransition (2 - a / y)
      rw [hxval, hyval]
    · have ha0 : 0 ≤ a := le_of_not_gt ha
      have hquot : a / y ≤ a / x := by
        apply (div_le_div_iff₀ hy hx).2
        exact mul_le_mul_of_nonneg_left hxy ha0
      have harg : 2 - a / x ≤ 2 - a / y := by linarith
      exact Real.smoothTransition.monotone harg
  · have h_inv : Filter.Tendsto (fun R : ℝ => R⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    have hmul : Filter.Tendsto (fun R : ℝ => a * R⁻¹) Filter.atTop (nhds (a * 0)) :=
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => a) Filter.atTop (nhds a)).mul h_inv
    have hdiv : Filter.Tendsto (fun R : ℝ => a / R) Filter.atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using hmul
    have hbelow : Set.Iio (1 : ℝ) ∈ nhds (0 : ℝ) := Iio_mem_nhds (by norm_num)
    have hevent : ∀ᶠ R : ℝ in Filter.atTop, a / R < 1 := by
      simpa only [Set.mem_Iio] using hdiv.eventually hbelow
    have heq :
      (fun R : ℝ => Real.smoothTransition (2 - a / R)) =ᶠ[Filter.atTop]
        (fun _ : ℝ => (1 : ℝ)) := by
      filter_upwards [hevent] with R hR
      apply Real.smoothTransition.one_of_one_le
      linarith
    exact
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1)).congr'
        heq.symm

section BoundedRangeProfiles

open Set Filter Metric
open scoped Topology

/--
**Smooth compact extension from a bounded nonnegative range**: if `F` is smooth on `(-δ, ∞)` with `F
0 = 0` (`δ > 0`,
`B ≥ 0`), then `Φ = χ F` with a bump `χ` centred at `B/2` (support the closed interval `[-δ/2, B +
δ/2]`, equal to `1` near
`[0, B]`) is smooth, compactly supported, Lipschitz, `Φ 0 = 0`, and `Φ = F`, `Φ' = F'` on the closed
interval `[0, B]`. -/
theorem exists_smooth_compact_extension_on_nonnegative_interval {δ B : ℝ} (hδ : 0 < δ)
    (hB : 0 ≤ B) {F : ℝ → ℝ} (hF : ContDiffOn ℝ ∞ F (Ioi (-δ))) (hFzero : F 0 = 0) :
    ∃ (Φ : ℝ → ℝ) (D : NNReal),
      ContDiff ℝ ∞ Φ ∧
        HasCompactSupport Φ ∧
          LipschitzWith D Φ ∧
            Φ 0 = 0 ∧ ∀ t ∈ Icc (0 : ℝ) B, Φ t = F t ∧ deriv Φ t = deriv F t := by
  classical
  let χ : ContDiffBump (B / 2 : ℝ) := ⟨B / 2 + δ / 4, B / 2 + δ / 2, by positivity, by linarith⟩
  let Φ : ℝ → ℝ := fun t => χ t * F t
  have hΦ : ContDiff ℝ ∞ Φ := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport χ
    · have hd : dist x (B / 2) ≤ B / 2 + δ / 2 := by
        simpa only [χ.tsupport_eq, mem_closedBall] using hx
      rw [Real.dist_eq] at hd
      have hxδ : -δ < x := by linarith [(abs_le.mp hd).1]
      exact χ.contDiff.contDiffAt.mul (hF.contDiffAt (isOpen_Ioi.mem_nhds hxδ))
    · have heχ : χ =ᶠ[𝓝 x] (fun _ : ℝ => 0) := notMem_tsupport_iff_eventuallyEq.mp hx
      have he : Φ =ᶠ[𝓝 x] (fun _ : ℝ => 0) := by
        filter_upwards [heχ] with t ht
        change χ t * F t = 0
        rw [ht, zero_mul]
      exact
        (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) x).congr_of_eventuallyEq he
  have hΦc : HasCompactSupport Φ := χ.hasCompactSupport.mul_right
  obtain ⟨D, hDLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hΦc hΦ (by simp)
  refine ⟨Φ, D, hΦ, hΦc, hDLip, ?_, ?_⟩
  · simp only [Φ, hFzero, mul_zero]
  · intro t ht
    have htBall : t ∈ ball (B / 2) χ.rIn := by
      change dist t (B / 2) < B / 2 + δ / 4
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    have heχ := χ.eventuallyEq_one_of_mem_ball htBall
    have he : Φ =ᶠ[𝓝 t] F := by
      filter_upwards [heχ] with s hs
      change χ s = 1 at hs
      change χ s * F s = F s
      rw [hs, one_mul]
    exact ⟨he.eq_of_nhds, he.deriv_eq⟩

/--
Smooth compact extension of the shifted logarithm `log(δ + t) - log δ` from `[0, B]` (`δ > 0`), with
derivative
`(δ + t)⁻¹` there. -/
theorem exists_smooth_compact_log_shift_extension {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) :
    ∃ (Φ : ℝ → ℝ) (D : NNReal),
      ContDiff ℝ ∞ Φ ∧
        HasCompactSupport Φ ∧
          LipschitzWith D Φ ∧
            Φ 0 = 0 ∧
              ∀ t ∈ Icc (0 : ℝ) B,
                Φ t = Real.log (δ + t) - Real.log δ ∧ deriv Φ t = (δ + t)⁻¹ := by
  have hc : ContDiffOn ℝ ∞ (fun t : ℝ => δ + t) (Ioi (-δ)) := contDiffOn_const.add contDiffOn_id
  have hne : ∀ t ∈ Ioi (-δ), δ + t ≠ 0 := by
    intro t ht
    exact ne_of_gt (by simpa only [mem_Ioi, neg_lt_iff_pos_add'] using ht)
  obtain ⟨Φ, D, hΦ, hΦc, hLip, hzero, he⟩ :=
    exists_smooth_compact_extension_on_nonnegative_interval hδ hB
      ((hc.log hne).sub contDiffOn_const) (show Real.log (δ + 0) - Real.log δ = 0 by simp)
  refine ⟨Φ, D, hΦ, hΦc, hLip, hzero, ?_⟩
  intro t ht
  refine ⟨(he t ht).1, (he t ht).2.trans ?_⟩
  have hp : δ + t ≠ 0 := ne_of_gt (lt_of_lt_of_le hδ (le_add_of_nonneg_right ht.1))
  simpa only [one_div, id_eq] using
    (((hasDerivAt_id t).const_add δ).log hp).sub_const (Real.log δ) |>.deriv

/--
Smooth compact extension of the shifted real power `(δ + t)^q - δ^q` from `[0, B]` (`δ > 0`, every
real `q`), with
derivative `q (δ + t)^(q - 1)` there. -/
theorem exists_smooth_compact_rpow_shift_extension {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) (q : ℝ) :
    ∃ (Φ : ℝ → ℝ) (D : NNReal),
      ContDiff ℝ ∞ Φ ∧
        HasCompactSupport Φ ∧
          LipschitzWith D Φ ∧
            Φ 0 = 0 ∧
              ∀ t ∈ Icc (0 : ℝ) B,
                Φ t = (δ + t) ^ q - δ ^ q ∧ deriv Φ t = q * (δ + t) ^ (q - 1) := by
  have hc : ContDiffOn ℝ ∞ (fun t : ℝ => δ + t) (Ioi (-δ)) := contDiffOn_const.add contDiffOn_id
  have hne : ∀ t ∈ Ioi (-δ), δ + t ≠ 0 := by
    intro t ht
    exact ne_of_gt (by simpa only [mem_Ioi, neg_lt_iff_pos_add'] using ht)
  obtain ⟨Φ, D, hΦ, hΦc, hLip, hzero, he⟩ :=
    exists_smooth_compact_extension_on_nonnegative_interval hδ hB
      ((hc.rpow_const_of_ne hne).sub contDiffOn_const) (show (δ + 0) ^ q - δ ^ q = 0 by simp)
  refine ⟨Φ, D, hΦ, hΦc, hLip, hzero, ?_⟩
  intro t ht
  refine ⟨(he t ht).1, (he t ht).2.trans ?_⟩
  have hp : δ + t ≠ 0 := ne_of_gt (lt_of_lt_of_le hδ (le_add_of_nonneg_right ht.1))
  simpa only [one_mul, id_eq] using
    (((hasDerivAt_id t).const_add δ).rpow_const (Or.inl hp)).sub_const (δ ^ q) |>.deriv

end BoundedRangeProfiles

/--
Translate the smooth inverse-scale interval-integral cutoff and its derivative, bound and vanishing
region. -/
theorem shifted_inv_mul_intervalIntegral_div_three_cutoff {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hw0 : ∀ t, 0 ≤ w t) (hws : ∀ t, t ≤ 0 ∨ 3 ≤ t → w t = 0) {R : ℝ} (hR : 0 < R) (c : ℝ) :
    ContDiff ℝ ∞ (fun s => R⁻¹ * ∫ t in (s - c) / R..3, w t) ∧
      (∀ s,
          deriv (fun s => R⁻¹ * ∫ t in (s - c) / R..3, w t) s =
            -((R ^ 2)⁻¹ * w ((s - c) / R))) ∧
        (∀ s, |R⁻¹ * ∫ t in (s - c) / R..3, w t| ≤ R⁻¹ * ∫ t in (0 : ℝ)..3, w t) ∧
          (∀ s, c + 3 * R ≤ s → R⁻¹ * ∫ t in (s - c) / R..3, w t = 0) := by
  obtain ⟨hq, hqd, hq0, hqBound, hqZero⟩ :=
    inv_mul_intervalIntegral_div_three_cutoff hw hw0 hws hR
  let q : ℝ → ℝ := fun t => R⁻¹ * ∫ u in t / R..3, w u
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hq.comp (contDiff_id.sub contDiff_const)
  · intro s
    have hshift : deriv (fun t => q (t - c)) s = deriv q (s - c) := by
      simpa only [div_one, inv_one, one_mul] using
        (deriv_comp_sub_div_and_deriv_deriv q c 1 s).1
    calc
      deriv (fun t => R⁻¹ * ∫ u in (t - c) / R..3, w u) s = deriv q (s - c) := hshift
      _ = -((R ^ 2)⁻¹ * w ((s - c) / R)) := hqd (s - c)
  · intro s
    rw [abs_of_nonneg (hq0 (s - c))]
    exact hqBound (s - c)
  · intro s hs
    exact hqZero (s - c) (by linarith)

end FunctionalInequalities.Analysis
