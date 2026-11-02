/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.SieveMajorants.Defs
import LeanPool.IwaniecLinearSieve.SieveMajorants.Properties
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.Chebyshev

/-!
# The functions `𝔣`, `𝔉`, `G_r` ([I71, §3])

`𝔣 = (𝔐 + 𝔚)/2`, `𝔉 = (𝔐 - 𝔚)/2`; `G_r = 𝔣` for `r` even and `𝔉` for `r` odd.
We prove (3.13), (3.14), the Corollary to Lemma 6, and positivity, continuity and monotonicity.

With our extension of `𝔐`, `𝔚` to `ℝ`, `𝔉 = 1` on `(-∞, 3]` (as in [I71], where `𝔉 = 1` on
`[1, 3]`), and `𝔣 = 2` on `(-∞, 2]`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace IwaniecLinearSieve

/-- Iwaniec's `𝔣 = (𝔐 + 𝔚)/2`. -/
noncomputable def majf (s : ℝ) : ℝ := (bigM s + bigW s) / 2

/-- Iwaniec's `𝔉 = (𝔐 - 𝔚)/2`. -/
noncomputable def majF (s : ℝ) : ℝ := (bigM s - bigW s) / 2

/-- Iwaniec's `G_r`: `𝔣` for `r` even, `𝔉` for `r` odd. -/
noncomputable def majG (r : ℕ) (s : ℝ) : ℝ := if Even r then majf s else majF s

theorem majG_of_even {r : ℕ} (hr : Even r) : majG r = majf := by
  ext s; simp [majG, hr]

theorem majG_of_odd {r : ℕ} (hr : Odd r) : majG r = majF := by
  ext s; simp [majG, Nat.not_even_iff_odd.2 hr]

theorem continuous_majf : Continuous majf :=
  (continuous_bigM.add continuous_bigW).div_const 2

theorem continuous_majF : Continuous majF :=
  (continuous_bigM.sub continuous_bigW).div_const 2

theorem continuous_majG (r : ℕ) : Continuous (majG r) := by
  rcases Nat.even_or_odd r with hr | hr
  · rw [majG_of_even hr]; exact continuous_majf
  · rw [majG_of_odd hr]; exact continuous_majF

/-- `𝔉 = 1` for `s ≤ 3`. -/
theorem majF_of_le_three {s : ℝ} (hs : s ≤ 3) : majF s = 1 := by
  simp only [majF, bigM_of_le_three hs, bigW_of_le_three hs]; ring

/-- `𝔣(s) = 1 + 1/(s-1) - log(s-1)` for `2 ≤ s ≤ 3`. -/
theorem majf_eq {s : ℝ} (hs : 2 ≤ s) (hs' : s ≤ 3) :
    majf s = 1 + 1 / (s - 1) - log (s - 1) := by
  simp only [majf, bigM_eq hs hs', bigW_eq hs hs']; ring

theorem majf_of_le_two {s : ℝ} (hs : s ≤ 2) : majf s = 2 := by
  simp only [majf, bigM_of_le_two hs, bigW_of_le_two hs]; norm_num

/-- Corollary to [I71, Lemma 6]: `𝔐/3 ≤ 𝔣 ≤ 2𝔐/3`. -/
theorem majf_mem (s : ℝ) : bigM s / 3 ≤ majf s ∧ majf s ≤ 2 * bigM s / 3 := by
  have := abs_le.1 (abs_bigW_le s)
  unfold majf; constructor <;> linarith [this.1, this.2]

/-- Corollary to [I71, Lemma 6]: `𝔐/3 ≤ 𝔉 ≤ 2𝔐/3`. -/
theorem majF_mem (s : ℝ) : bigM s / 3 ≤ majF s ∧ majF s ≤ 2 * bigM s / 3 := by
  have := abs_le.1 (abs_bigW_le s)
  unfold majF; constructor <;> linarith [this.1, this.2]

/-- Corollary to [I71, Lemma 6] for `G_r`. -/
theorem majG_mem (r : ℕ) (s : ℝ) : bigM s / 3 ≤ majG r s ∧ majG r s ≤ 2 * bigM s / 3 := by
  unfold majG; split_ifs
  · exact majf_mem s
  · exact majF_mem s

theorem majG_le_two (r : ℕ) (s : ℝ) : majG r s ≤ 2 := by
  linarith [(majG_mem r s).2, bigM_le_three s]

theorem majG_pos (r : ℕ) (s : ℝ) : 0 < majG r s :=
  lt_of_lt_of_le (by linarith [bigM_pos s]) (majG_mem r s).1

theorem majf_pos (s : ℝ) : 0 < majf s := by
  simpa [majG_of_even (⟨0, rfl⟩ : Even 0)] using majG_pos 0 s

theorem majF_pos (s : ℝ) : 0 < majF s := by
  simpa [majG_of_odd odd_one] using majG_pos 1 s

/-! ### Derivatives -/
theorem hasDerivAt_majF {s : ℝ} (hs : 3 < s) :
    HasDerivAt majF (-(s / (s - 1) ^ 2 * majf (s - 1))) s := by
  refine ((hasDerivAt_bigM hs).sub (hasDerivAt_bigW hs)).div_const 2 |>.congr_deriv ?_
  simp only [majf]; ring

theorem hasDerivWithinAt_majf_Ici {s : ℝ} (hs : 3 ≤ s) :
    HasDerivWithinAt majf (-(s / (s - 1) ^ 2 * majF (s - 1))) (Ici s) s := by
  refine ((hasDerivWithinAt_bigM_Ici hs).add (hasDerivWithinAt_bigW_Ici hs)).div_const 2
    |>.congr_deriv ?_
  simp only [majF]; ring

/-- `𝔣' (s) = -s/(s-1)² 𝔉(s-1)` for `s > 2`. -/
theorem hasDerivAt_majf {s : ℝ} (hs : 2 < s) :
    HasDerivAt majf (-(s / (s - 1) ^ 2 * majF (s - 1))) s := by
  have hexp : ∀ x, 2 < x → x ≤ 4 → HasDerivAt (fun x => 1 + (1 / (x - 1) - log (x - 1)))
      (-(x / (x - 1) ^ 2 * majF (x - 1))) x := by
    intro x hx hx4
    rw [majF_of_le_three (by linarith), mul_one]
    exact (hasDerivAt_initForm (by linarith)).const_add 1
  have heq : ∀ x, 2 ≤ x → x ≤ 3 → majf x = 1 + (1 / (x - 1) - log (x - 1)) := by
    intro x hx hx3; rw [majf_eq hx hx3]; ring
  rcases lt_trichotomy s 3 with h3 | rfl | h3
  · refine (hexp s hs (by linarith)).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hs h3] with x hx
    exact heq x hx.1.le hx.2.le
  · have hl : HasDerivWithinAt majf (-(3 / (3 - 1) ^ 2 * majF (3 - 1))) (Iic 3) 3 := by
      refine (hexp 3 (by norm_num) (by norm_num)).hasDerivWithinAt.congr_of_eventuallyEq ?_
        (heq 3 (by norm_num) le_rfl)
      filter_upwards [inter_mem_nhdsWithin (Iic 3) (Ioi_mem_nhds (show (2 : ℝ) < 3 by norm_num)),
        self_mem_nhdsWithin] with x hx _
      exact heq x hx.2.out.le hx.1
    have := hl.union (hasDerivWithinAt_majf_Ici le_rfl)
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · refine ((hasDerivAt_bigM h3).add (hasDerivAt_bigW h3)).div_const 2 |>.congr_deriv ?_
    simp only [majF]; ring

/-- The derivative of `G_{r+1}` is `-G_r(t-1) t/(t-1)²`, for `t > 3`, and for `t > 2` if `r` is
odd; i.e. for `t > (5 + (-1)^r)/2` as in [I71, proof of Lemma 11]. -/
theorem hasDerivAt_majG_succ (r : ℕ) {t : ℝ} (ht : (5 + (-1) ^ r) / 2 < t) :
    HasDerivAt (majG (r + 1)) (-(majG r (t - 1) * t / (t - 1) ^ 2)) t := by
  rcases Nat.even_or_odd r with hr | hr
  · rw [majG_of_odd hr.add_one, majG_of_even hr]
    rw [hr.neg_one_pow] at ht
    exact (hasDerivAt_majF (by linarith)).congr_deriv (by ring)
  · rw [majG_of_even hr.add_one, majG_of_odd hr]
    rw [hr.neg_one_pow] at ht
    exact (hasDerivAt_majf (by linarith)).congr_deriv (by ring)

/-! ### Monotonicity -/
theorem majF_antitone : Antitone majF := by
  refine antitone_of_antitoneOn_Iic_Ici (a := 3) ?_ ?_
  · intro s hs t ht _
    rw [majF_of_le_three hs, majF_of_le_three ht]
  · refine antitoneOn_of_deriv_nonpos (convex_Ici 3) continuous_majF.continuousOn
      (fun x hx => ?_) (fun x hx => ?_) <;> rw [interior_Ici] at hx
    · exact (hasDerivAt_majF hx).differentiableAt.differentiableWithinAt
    · rw [(hasDerivAt_majF hx).deriv]
      have := mul_pos (kernel_pos (by linarith [hx.out] : (1 : ℝ) < x)) (majf_pos (x - 1))
      linarith

theorem majf_antitone : Antitone majf := by
  refine antitone_of_antitoneOn_Iic_Ici (a := 2) ?_ ?_
  · intro s hs t ht _
    rw [majf_of_le_two hs, majf_of_le_two ht]
  · refine antitoneOn_of_deriv_nonpos (convex_Ici 2) continuous_majf.continuousOn
      (fun x hx => ?_) (fun x hx => ?_) <;> rw [interior_Ici] at hx
    · exact (hasDerivAt_majf hx).differentiableAt.differentiableWithinAt
    · rw [(hasDerivAt_majf hx).deriv]
      have := mul_pos (kernel_pos (by linarith [hx.out] : (1 : ℝ) < x)) (majF_pos (x - 1))
      linarith

/-- [I71, Remark after Lemma 6]: `G_r` is decreasing. -/
theorem majG_antitone (r : ℕ) : Antitone (majG r) := by
  rcases Nat.even_or_odd r with hr | hr
  · rw [majG_of_even hr]; exact majf_antitone
  · rw [majG_of_odd hr]; exact majF_antitone

/-! ### (3.13), (3.14) -/
theorem tendsto_majG_atTop (r : ℕ) : Tendsto (majG r) atTop (𝓝 0) := by
  have h : Tendsto (fun s => 2 * bigM s / 3) atTop (𝓝 0) := by
    simpa using (tendsto_bigM_atTop.const_mul 2).div_const 3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun s => (majG_pos r s).le) fun s => (majG_mem r s).2

theorem tendsto_majf_atTop : Tendsto majf atTop (𝓝 0) := by
  simpa [majG_of_even (⟨0, rfl⟩ : Even 0)] using tendsto_majG_atTop 0

theorem tendsto_majF_atTop : Tendsto majF atTop (𝓝 0) := by
  simpa [majG_of_odd odd_one] using tendsto_majG_atTop 1

/-- [I71, (3.13)]: `𝔉(s) = ∫_s^∞ 𝔣(t-1) t/(t-1)² dt` for `s ≥ 3`. -/
theorem majF_eq_integral {s : ℝ} (hs : 3 ≤ s) :
    majF s = ∫ t in Ioi s, majf (t - 1) * t / (t - 1) ^ 2 := by
  have := integral_Ioi_of_hasDerivAt_of_nonneg (g := fun t => -majF t) (l := 0)
    (g' := fun t => majf (t - 1) * t / (t - 1) ^ 2)
    continuous_majF.neg.continuousWithinAt
    (fun t ht => (hasDerivAt_majF (hs.trans_lt ht)).neg.congr_deriv (by ring))
    (fun t ht => by
      have h1 : 0 < t - 1 := by linarith [ht.out]
      have := majf_pos (t - 1)
      have : 0 < t := by linarith
      positivity)
    (by simpa using tendsto_majF_atTop.neg)
  rw [this]; ring

/-- [I71, (3.14)]: `𝔣(s) = ∫_s^∞ 𝔉(t-1) t/(t-1)² dt` for `s ≥ 2`. -/
theorem majf_eq_integral {s : ℝ} (hs : 2 ≤ s) :
    majf s = ∫ t in Ioi s, majF (t - 1) * t / (t - 1) ^ 2 := by
  have := integral_Ioi_of_hasDerivAt_of_nonneg (g := fun t => -majf t) (l := 0)
    (g' := fun t => majF (t - 1) * t / (t - 1) ^ 2)
    continuous_majf.neg.continuousWithinAt
    (fun t ht => (hasDerivAt_majf (hs.trans_lt ht)).neg.congr_deriv (by ring))
    (fun t ht => by
      have h1 : 0 < t - 1 := by linarith [ht.out]
      have := majF_pos (t - 1)
      have : 0 < t := by linarith
      positivity)
    (by simpa using tendsto_majf_atTop.neg)
  rw [this]; ring

end IwaniecLinearSieve
