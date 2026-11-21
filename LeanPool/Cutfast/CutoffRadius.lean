/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.Cutfast.Cutoff

/-!
# Cutoff for other sizes of the set of initial points (Section 1.4.3)
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Real
open scoped ENNReal InnerProductSpace BoundedContinuousFunction MatrixOrder

namespace Cutfast

namespace CutoffRadius

open Cutoff

/-! ### Lower bounds on the dilation term for every `α` -/

/-- `min(1,α) u ≤ 1 - (1-u)^α` for `u ∈ [0,1]` and `α > 0`. -/
lemma min_mul_le_one_sub_rpow {α u : ℝ} (hα : 0 < α) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    min 1 α * u ≤ 1 - (1 - u) ^ α := by
  rcases le_total 1 α with h | h
  · rw [min_eq_left h, one_mul]; exact le_one_sub_rpow h hu0 hu1
  · rw [min_eq_right h]
    have := rpow_one_add_le_one_add_mul_self (by linarith : (-1 : ℝ) ≤ -u) hα.le h
    rw [← sub_eq_add_neg] at this
    linarith

/-- `α/2 (1-w)² ≤ g(κ, w^α)` for `α ≤ 1`, `α ≠ 1/2`. -/
lemma le_entropyProfile_of_le_one {α w : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hα2 : α ≠ 1 / 2)
    (hw : 1 / 2 ≤ w) (hw1 : w ≤ 1) :
    α / 2 * (1 - w) ^ 2 ≤ entropyProfile (2 - 1 / α) (w ^ α) := by
  have hw0 : 0 < w := by linarith
  rw [entropyProfile_eq_integral hα hα2 hw0 hw1,
    show α / 2 * (1 - w) ^ 2 = α * (1 - w) ^ 2 / 2 by ring, ← integral_mul_one_sub]
  apply intervalIntegral.integral_mono_on hw1
  · exact (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.sub
    · exact continuousOn_id.rpow_const fun x hx => Or.inl (by
        rw [Set.uIcc_of_le hw1] at hx; exact ne_of_gt (by simp only [id]; linarith [hx.1]))
    · exact continuousOn_id.rpow_const fun x hx => Or.inl (by
        rw [Set.uIcc_of_le hw1] at hx; exact ne_of_gt (by simp only [id]; linarith [hx.1]))
  intro s hs
  have hs0 : 0 < s := by linarith [hs.1]
  rw [entropy_integrand_eq hs0]
  have h1 : 1 ≤ s ^ (2 * α - 2) :=
    one_le_rpow_of_pos_of_le_one_of_nonpos hs0 hs.2 (by linarith)
  have : 0 ≤ 1 - s := by linarith [hs.2]
  have := mul_le_mul_of_nonneg_left h1 hα.le
  nlinarith

/-- A uniform quadratic lower bound on the entropy profile near `w = 1`. -/
lemma exists_le_entropyProfile {α : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) :
    ∃ c > 0, ∀ w : ℝ, 1 / 2 ≤ w → w ≤ 1 →
      c * (1 - w) ^ 2 ≤ entropyProfile (2 - 1 / α) (w ^ α) := by
  rcases le_total 1 α with h | h
  · refine ⟨α * (1 / 2) ^ (2 * α - 2) / 2, ?_, fun w hw hw1 => le_entropyProfile h hw hw1⟩
    have := rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2) (2 * α - 2)
    positivity
  · exact ⟨α / 2, by positivity, fun w hw hw1 => le_entropyProfile_of_le_one hα h hα2 hw hw1⟩

variable {d : ℕ} {m : ℝ}

lemma le_wassersteinSq_scale (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) {t : ℝ}
    (ht : 0 < t) (hu : exp (-t / alpha d m) ≤ 1 / 2) (x₀ : E d) :
    ENNReal.ofReal (min 1 (alpha d m) ^ 2 * exp (-t / alpha d m) ^ 2 * eqSecondMoment d m) ≤
      wassersteinSq (densityMeasure (solution d m x₀ t)) (densityMeasure (equilibrium d m)) := by
  rw [wassersteinSq_solution h h2 x₀ ht, scaleFactor_eq]
  apply ENNReal.ofReal_le_ofReal
  have hM := (eqSecondMoment_pos h h2).le
  have hu0 : 0 ≤ exp (-t / alpha d m) := (exp_pos _).le
  have h1 := min_mul_le_one_sub_rpow (alpha_pos h) hu0 (by linarith)
  have h0 : 0 ≤ min 1 (alpha d m) * exp (-t / alpha d m) :=
    mul_nonneg (le_min zero_le_one (alpha_pos h).le) hu0
  have h3 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h1 2) hM
  have : 0 ≤ exp (-t) ^ 2 * ‖x₀‖ ^ 2 := by positivity
  rw [mul_pow] at h3
  linarith

lemma le_relEntropy_scale (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) {t : ℝ}
    (ht : 0 < t) (hu : exp (-t / alpha d m) ≤ 1 / 2) (x₀ : E d) {c : ℝ}
    (hc : ∀ w : ℝ, 1 / 2 ≤ w → w ≤ 1 →
      c * (1 - w) ^ 2 ≤ entropyProfile (2 - 1 / alpha d m) (w ^ alpha d m)) :
    c * exp (-t / alpha d m) ^ 2 * eqSecondMoment d m ≤
      relEntropy m (solution d m x₀ t) (equilibrium d m) := by
  rw [relEntropy_eq h h2 ht]
  have hM := (eqSecondMoment_pos h h2).le
  have hu0 : 0 ≤ exp (-t / alpha d m) := (exp_pos _).le
  have h1 := hc (1 - exp (-t / alpha d m)) (by linarith) (by linarith)
  rw [sub_sub_cancel] at h1
  have h3 := mul_le_mul_of_nonneg_left h1 hM
  have : 0 ≤ exp (-t) ^ 2 * ‖x₀‖ ^ 2 / 2 := by positivity
  linarith

/-! ### Generic cutoff statements for a general radius `R d` -/

section Generic

variable {m t R : ℕ → ℝ}

export Cutoff.GeneralRadius (sq_le_of_mem ShiftHyp wassersteinSq_lower_shift
  relEntropy_lower_shift fisherInfo_lower_shift)

/-- Hypotheses for the upper bounds, for initial points in the ball of radius `R d`. -/
def UpperHyp (m t R : ℕ → ℝ) (A K : ℝ) : Prop :=
  (∀ᶠ d : ℕ in atTop, Admissible d (m d) ∧ (d : ℝ) / (d + 2) < m d ∧ 0 < t d ∧
    alpha d (m d) ≤ A ∧ eqSecondMoment d (m d) ≤ K * d ∧ 0 ≤ R d) ∧
  Tendsto (fun d : ℕ => (d : ℝ) * exp (-t d / alpha d (m d)) ^ 2) atTop (𝓝 0) ∧
  Tendsto (fun d : ℕ => R d ^ 2 * exp (-t d) ^ 2) atTop (𝓝 0)

private lemma UpperHyp.generalRadius {A K : ℝ} (H : UpperHyp m t R A K) :
    Cutoff.GeneralRadius.UpperHyp m t R A K :=
  ⟨H.1.mono (fun _ hd => ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1⟩), H.2⟩

lemma wassersteinSq_upper {A K : ℝ} (H : UpperHyp m t R A K) :
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (R d),
      wassersteinSq (densityMeasure (solution d (m d) x₀ (t d)))
        (densityMeasure (equilibrium d (m d)))) atTop (𝓝 0) :=
  Cutoff.GeneralRadius.wassersteinSq_upper H.generalRadius

lemma relEntropy_upper {A K : ℝ} (H : UpperHyp m t R A K) :
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (R d),
      (relEntropy (m d) (solution d (m d) x₀ (t d)) (equilibrium d (m d)) : EReal))
        atTop (𝓝 0) :=
  Cutoff.GeneralRadius.relEntropy_upper H.generalRadius (H.1.mono fun _ hd => hd.2.2.2.2.2)

lemma fisherInfo_upper {A K : ℝ} (H : UpperHyp m t R A K) :
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (R d),
      fisherInfo (m d) (solution d (m d) x₀ (t d))) atTop (𝓝 0) :=
  Cutoff.GeneralRadius.fisherInfo_upper H.generalRadius

lemma scaleHyp_eventually {α k : ℝ} (H : ScaleHyp m t α k) (hR : ∀ᶠ d : ℕ in atTop, 0 ≤ R d) :
    ∀ᶠ d : ℕ in atTop, Admissible d (m d) ∧ (d : ℝ) / (d + 2) < m d ∧ 0 < t d ∧
      alpha d (m d) = α ∧ k * d ≤ eqSecondMoment d (m d) ∧ exp (-t d / α) ≤ 1 / 2 ∧
      (0 : E d) ∈ closedBall (0 : E d) (R d) := by
  filter_upwards [H.eventually, hR] with d hd hRd
  exact ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2,
    mem_closedBall_self hRd⟩

lemma wassersteinSq_lower_scale {α k : ℝ} (hα : 0 < α) (hk : 0 < k)
    (H : ScaleHyp m t α k) (hR : ∀ᶠ d : ℕ in atTop, 0 ≤ R d) :
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (R d),
      wassersteinSq (densityMeasure (solution d (m d) x₀ (t d)))
        (densityMeasure (equilibrium d (m d)))) atTop (𝓝 ⊤) := by
  have hc : 0 < min 1 α ^ 2 := by have := lt_min one_pos hα; positivity
  refine tendsto_iSup_ennreal_top (H.2.1.const_mul_atTop (mul_pos hc hk)) ?_
  filter_upwards [scaleHyp_eventually H hR] with d ⟨h, h2, ht, hαd, hk', hu, h0⟩
  refine ⟨0, h0, le_trans ?_ (le_wassersteinSq_scale h h2 ht (hαd ▸ hu) 0)⟩
  rw [hαd]
  exact ENNReal.ofReal_le_ofReal (lower_scale_bound hc.le hk')

lemma relEntropy_lower_scale {α k : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hk : 0 < k)
    (H : ScaleHyp m t α k) (hR : ∀ᶠ d : ℕ in atTop, 0 ≤ R d) :
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (R d),
      (relEntropy (m d) (solution d (m d) x₀ (t d)) (equilibrium d (m d)) : EReal))
        atTop (𝓝 ⊤) := by
  obtain ⟨c, hc, hg⟩ := exists_le_entropyProfile hα hα2
  refine tendsto_iSup_ereal_top (H.2.1.const_mul_atTop (mul_pos hc hk)) ?_
  filter_upwards [scaleHyp_eventually H hR] with d ⟨h, h2, ht, hαd, hk', hu, h0⟩
  refine ⟨0, h0, le_trans ?_ (le_relEntropy_scale h h2 ht (hαd ▸ hu) 0 (hαd ▸ hg))⟩
  rw [hαd]
  exact lower_scale_bound hc.le hk'

lemma fisherInfo_lower_scale {α k : ℝ} (hk : 0 < k)
    (H : ScaleHyp m t α k) (hR : ∀ᶠ d : ℕ in atTop, 0 ≤ R d) :
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (R d),
      fisherInfo (m d) (solution d (m d) x₀ (t d))) atTop (𝓝 ⊤) := by
  have hc : 0 < ((1 / 2 : ℝ) ^ α) ^ 2 := by
    have := rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2) α
    positivity
  refine tendsto_iSup_ennreal_top (H.2.1.const_mul_atTop (mul_pos hc hk)) ?_
  filter_upwards [scaleHyp_eventually H hR] with d ⟨h, h2, ht, hαd, hk', hu, h0⟩
  refine ⟨0, h0, le_trans ?_ (le_fisherInfo_of_one_le h h2 ht (hαd ▸ hu) 0)⟩
  rw [hαd]
  exact ENNReal.ofReal_le_ofReal (lower_scale_bound hc.le hk')

end Generic

/-! ### The radius `r d^θ` -/

lemma radius_sq_mul_exp_sq {r θ c : ℝ} {d : ℕ} (hd : 1 ≤ d) :
    (r * (d : ℝ) ^ θ) ^ 2 * exp (-(c * log d)) ^ 2 = r ^ 2 * exp ((2 * θ - 2 * c) * log d) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have e : ∀ x : ℝ, exp x ^ 2 = exp (2 * x) := fun x => by rw [sq, ← exp_add]; ring_nf
  rw [rpow_def_of_pos hd', mul_pow, e, e, mul_assoc, ← exp_add]
  ring_nf

lemma tendsto_radius_zero {r θ c : ℝ} (hk : 2 * θ - 2 * c < 0) :
    Tendsto (fun d : ℕ => (r * (d : ℝ) ^ θ) ^ 2 * exp (-(c * log d)) ^ 2) atTop (𝓝 0) := by
  have : Tendsto (fun d : ℕ => r ^ 2 * exp ((2 * θ - 2 * c) * log d)) atTop (𝓝 0) := by
    simpa using (tendsto_exp_atBot.comp
      (tendsto_log_natCast.const_mul_atTop_of_neg hk)).const_mul (r ^ 2)
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with d hd using (radius_sq_mul_exp_sq hd).symm

lemma tendsto_radius_top {r θ c : ℝ} (hr : 0 < r) (hk : 0 < 2 * θ - 2 * c) :
    Tendsto (fun d : ℕ => (r * (d : ℝ) ^ θ) ^ 2 * exp (-(c * log d)) ^ 2) atTop atTop := by
  have : Tendsto (fun d : ℕ => r ^ 2 * exp ((2 * θ - 2 * c) * log d)) atTop atTop :=
    (tendsto_exp_atTop.comp (tendsto_log_natCast.const_mul_atTop hk)).const_mul_atTop
      (by positivity)
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with d hd using (radius_sq_mul_exp_sq hd).symm

lemma radius_nonneg {r θ : ℝ} (hr : 0 < r) (d : ℕ) : 0 ≤ r * (d : ℝ) ^ θ :=
  mul_nonneg hr.le (rpow_nonneg (Nat.cast_nonneg _) _)

/-! ### Parameters of Theorem 1.1 -/

lemma upperHyp_alpha {α r ε θ : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hr : 0 < r) (hε : 0 < ε) :
    ∃ K, UpperHyp (fun d => exponentOfAlpha α d) (fun d => (1 + ε) * max (α / 2) θ * log d)
      (fun d => r * (d : ℝ) ^ θ) α K := by
  obtain ⟨K, hK, hM⟩ := tendsto_eqSecondMoment_div hα hα2
  have hmax : α / 2 ≤ max (α / 2) θ := le_max_left _ _
  have hmaxθ : θ ≤ max (α / 2) θ := le_max_right _ _
  have hc : 0 < (1 + ε) * max (α / 2) θ := mul_pos (by linarith) (by linarith)
  refine ⟨2 * K, ?_, ?_, ?_⟩
  · filter_upwards [eventually_admissible_exponentOfAlpha hα hα2, bounds_of_tendsto_div hK hM]
      with d ⟨h, h2, hαd, hd⟩ hb
    exact ⟨h, h2, mul_pos hc (log_natCast_pos hd), hαd.le, hb.2, radius_nonneg hr d⟩
  · have : Tendsto (fun d : ℕ => (d : ℝ) *
        exp (-((1 + ε) * max (α / 2) θ / α * log d)) ^ 2) atTop (𝓝 0) := by
      apply tendsto_mul_exp_sq_zero
      have h1 : 1 ≤ 2 * max (α / 2) θ / α := by rw [le_div_iff₀ hα]; linarith
      have : 2 * ((1 + ε) * max (α / 2) θ / α) = (1 + ε) * (2 * max (α / 2) θ / α) := by ring
      rw [this]; nlinarith
    refine this.congr' ?_
    filter_upwards [eventually_admissible_exponentOfAlpha hα hα2] with d ⟨_, _, hαd, _⟩
    rw [hαd, neg_mul_div_eq]
  · exact tendsto_radius_zero (by nlinarith)

lemma shiftHyp_alpha {α r ε θ : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hr : 0 < r) (hε1 : ε < 1)
    (hε : 0 < ε) (hθ : α / 2 < θ) :
    ShiftHyp (fun d => exponentOfAlpha α d) (fun d => (1 - ε) * max (α / 2) θ * log d)
      (fun d => r * (d : ℝ) ^ θ) := by
  have hmax : max (α / 2) θ = θ := max_eq_right hθ.le
  have hθ0 : 0 < θ := by linarith
  refine ⟨?_, ?_⟩
  · filter_upwards [eventually_admissible_exponentOfAlpha hα hα2] with d ⟨h, h2, _, hd⟩
    refine ⟨h, h2, mul_pos ?_ (log_natCast_pos hd), radius_nonneg hr d⟩
    rw [hmax]; exact mul_pos (by linarith) hθ0
  · apply tendsto_radius_top hr
    rw [hmax]; nlinarith

lemma scaleHyp_alpha {α ε θ : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hε : 0 < ε) (hε1 : ε < 1)
    (hθ : θ ≤ α / 2) :
    ∃ k > 0, ScaleHyp (fun d => exponentOfAlpha α d)
      (fun d => (1 - ε) * max (α / 2) θ * log d) α k := by
  have hmax : max (α / 2) θ = α / 2 := max_eq_left hθ
  obtain ⟨K, hK, hM⟩ := tendsto_eqSecondMoment_div hα hα2
  refine ⟨K / 2, by positivity, ?_, ?_, ?_⟩
  · filter_upwards [eventually_admissible_exponentOfAlpha hα hα2, bounds_of_tendsto_div hK hM]
      with d ⟨h, h2, hαd, hd⟩ hb
    refine ⟨h, h2, mul_pos ?_ (log_natCast_pos hd), hαd, hb.1⟩
    rw [hmax]; exact mul_pos (by linarith) (by linarith)
  · simp_rw [neg_mul_div_eq]
    apply tendsto_mul_exp_sq_atTop
    rw [hmax, show 2 * ((1 - ε) * (α / 2) / α) = 1 - ε by field_simp]
    linarith
  · simp_rw [neg_mul_div_eq]
    apply tendsto_exp_neg_mul_log
    rw [hmax]
    have : 0 < 1 - ε := by linarith
    positivity

/-! ### Parameters of Theorem 1.2 -/

lemma upperHyp_fixed {m r ε θ : ℝ} (hm : 1 < m) (hr : 0 < r) (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ K, UpperHyp (fun _ => m) (fun d => (1 + ε) * θ * log d) (fun d => r * (d : ℝ) ^ θ)
      (1 / 2) K := by
  have hK : (0 : ℝ) < 1 / (2 * π * exp 1) := by positivity
  have he : Tendsto (fun d : ℕ => (d : ℝ) * exp (-(1 * log d)) ^ 2) atTop (𝓝 0) :=
    tendsto_mul_exp_sq_zero (by norm_num)
  have hc : 0 < (1 + ε) * θ := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ((1 + ε) * θ * (m - 1)))
  refine ⟨2 * (1 / (2 * π * exp 1)), ?_, ?_, tendsto_radius_zero (by nlinarith)⟩
  · filter_upwards [eventually_ge_atTop 2, bounds_of_tendsto_div hK
      (tendsto_eqSecondMoment_div_fixed hm)] with d hd hb
    obtain ⟨h, h2⟩ := admissible_of_one_lt hm (by omega : 1 ≤ d)
    exact ⟨h, h2, mul_pos hc (log_natCast_pos hd), alpha_le_half hm d, hb.2,
      radius_nonneg hr d⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
      (Eventually.of_forall fun d => by positivity) ?_
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop N] with d hd hdN
    have hdN' : (N : ℝ) ≤ d := by exact_mod_cast hdN
    have hinv : 1 / alpha d m = 2 - d * (1 - m) := by unfold alpha; rw [one_div_one_div]
    have hX : 1 ≤ (1 + ε) * θ * (2 - d * (1 - m)) := by
      have h1 : 1 / ((1 + ε) * θ * (m - 1)) < d := by linarith
      rw [div_lt_iff₀ (by have : 0 < m - 1 := by linarith
                          positivity)] at h1
      nlinarith
    have hL := log_natCast_nonneg d
    have : exp (-((1 + ε) * θ * log d) / alpha d m) ≤ exp (-(1 * log d)) := by
      apply exp_le_exp.2
      rw [div_eq_mul_one_div, hinv]
      nlinarith
    have h0 := (exp_pos (-((1 + ε) * θ * log d) / alpha d m)).le
    have := pow_le_pow_left₀ h0 this 2
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)

lemma shiftHyp_fixed {m r ε θ : ℝ} (hm : 1 < m) (hr : 0 < r) (hε : 0 < ε) (hε1 : ε < 1)
    (hθ : 0 < θ) :
    ShiftHyp (fun _ => m) (fun d => (1 - ε) * θ * log d) (fun d => r * (d : ℝ) ^ θ) := by
  refine ⟨?_, tendsto_radius_top hr (by nlinarith)⟩
  filter_upwards [eventually_ge_atTop 2] with d hd
  obtain ⟨h, h2⟩ := admissible_of_one_lt hm (by omega : 1 ≤ d)
  exact ⟨h, h2, mul_pos (mul_pos (by linarith) hθ) (log_natCast_pos hd), radius_nonneg hr d⟩

end CutoffRadius

open CutoffRadius


/-- **Section 1.4.3, Theorem 1.1 for other initial data, Wasserstein.** For initial points in the
ball of radius `r d^θ` (`θ ∈ ℝ`), the critical time becomes `max(α/2, θ) log d`. -/
theorem cutoff_wassersteinSq_radius' {α r ε θ : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hr : 0 < r)
    (hε : 0 < ε) :
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        wassersteinSq
          (densityMeasure (solution d (exponentOfAlpha α d) x₀ ((1 - ε) * max (α / 2) θ * log d)))
          (densityMeasure (equilibrium d (exponentOfAlpha α d)))) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        wassersteinSq
          (densityMeasure (solution d (exponentOfAlpha α d) x₀ ((1 + ε) * max (α / 2) θ * log d)))
          (densityMeasure (equilibrium d (exponentOfAlpha α d)))) atTop (𝓝 0) := by
  refine ⟨fun hε1 => ?_, ?_⟩
  · rcases lt_or_ge (α / 2) θ with hθ | hθ
    · exact wassersteinSq_lower_shift (shiftHyp_alpha hα hα2 hr hε1 hε hθ)
    · obtain ⟨k, hk, H⟩ := scaleHyp_alpha hα hα2 hε hε1 hθ
      exact wassersteinSq_lower_scale hα hk H (Eventually.of_forall fun d => radius_nonneg hr d)
  · obtain ⟨K, H⟩ := upperHyp_alpha (θ := θ) hα hα2 hr hε
    exact wassersteinSq_upper H

/-- **Section 1.4.3, Theorem 1.1 for other initial data, relative entropy.** As in
`cutoff_relEntropy`, the entropy integrand is integrable for large `d`, for all `t > 0` and all
initial points in the ball. -/
theorem cutoff_relEntropy_radius' {α r ε θ : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hr : 0 < r)
    (hε : 0 < ε) :
    (∀ᶠ d : ℕ in atTop, ∀ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ), ∀ t > 0,
      Integrable (relEntropyDensity (exponentOfAlpha α d) (solution d (exponentOfAlpha α d) x₀ t)
        (equilibrium d (exponentOfAlpha α d)))) ∧
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        (relEntropy (exponentOfAlpha α d)
          (solution d (exponentOfAlpha α d) x₀ ((1 - ε) * max (α / 2) θ * log d))
          (equilibrium d (exponentOfAlpha α d)) : EReal)) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        (relEntropy (exponentOfAlpha α d)
          (solution d (exponentOfAlpha α d) x₀ ((1 + ε) * max (α / 2) θ * log d))
          (equilibrium d (exponentOfAlpha α d)) : EReal)) atTop (𝓝 0) := by
  refine ⟨?_, fun hε1 => ?_, ?_⟩
  · filter_upwards [Cutoff.eventually_admissible_exponentOfAlpha hα hα2] with d ⟨h, h2, _,
    _⟩ x₀ _ t ht
    exact integrable_relEntropyDensity_solution h h2 x₀ ht
  · rcases lt_or_ge (α / 2) θ with hθ | hθ
    · exact relEntropy_lower_shift (shiftHyp_alpha hα hα2 hr hε1 hε hθ)
    · obtain ⟨k, hk, H⟩ := scaleHyp_alpha hα hα2 hε hε1 hθ
      exact relEntropy_lower_scale hα hα2 hk H (Eventually.of_forall fun d => radius_nonneg hr d)
  · obtain ⟨K, H⟩ := upperHyp_alpha (θ := θ) hα hα2 hr hε
    exact relEntropy_upper H

/-- **Section 1.4.3, Theorem 1.1 for other initial data, Fisher information.** -/
theorem cutoff_fisherInfo_radius' {α r ε θ : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hr : 0 < r)
    (hε : 0 < ε) :
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        fisherInfo (exponentOfAlpha α d)
          (solution d (exponentOfAlpha α d) x₀ ((1 - ε) * max (α / 2) θ * log d))) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        fisherInfo (exponentOfAlpha α d)
          (solution d (exponentOfAlpha α d) x₀ ((1 + ε) * max (α / 2) θ * log d))) atTop (𝓝 0) := by
  refine ⟨fun hε1 => ?_, ?_⟩
  · rcases lt_or_ge (α / 2) θ with hθ | hθ
    · exact fisherInfo_lower_shift (shiftHyp_alpha hα hα2 hr hε1 hε hθ)
    · obtain ⟨k, hk, H⟩ := scaleHyp_alpha hα hα2 hε hε1 hθ
      exact fisherInfo_lower_scale hk H (Eventually.of_forall fun d => radius_nonneg hr d)
  · obtain ⟨K, H⟩ := upperHyp_alpha (θ := θ) hα hα2 hr hε
    exact fisherInfo_upper H

/-- **Section 1.4.3, Theorem 1.2 for other initial data, Wasserstein.** For initial points in the
ball of radius `r d^θ` (`θ > 0`), the critical time becomes `θ log d`. -/
theorem cutoff_fixedExponent_wassersteinSq_radius' {m r ε θ : ℝ} (hm : 1 < m) (hr : 0 < r)
    (hε : 0 < ε) (hθ : 0 < θ) :
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        wassersteinSq (densityMeasure (solution d m x₀ ((1 - ε) * θ * log d)))
          (densityMeasure (equilibrium d m))) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        wassersteinSq (densityMeasure (solution d m x₀ ((1 + ε) * θ * log d)))
          (densityMeasure (equilibrium d m))) atTop (𝓝 0) := by
  obtain ⟨K, H⟩ := upperHyp_fixed hm hr hε hθ
  exact ⟨fun hε1 => wassersteinSq_lower_shift (shiftHyp_fixed hm hr hε hε1 hθ),
    wassersteinSq_upper H⟩

/-- **Section 1.4.3, Theorem 1.2 for other initial data, relative entropy.** As in
`cutoff_fixedExponent_relEntropy`, the entropy integrand is integrable for large `d`, for all
`t > 0` and all initial points in the ball. -/
theorem cutoff_fixedExponent_relEntropy_radius' {m r ε θ : ℝ} (hm : 1 < m) (hr : 0 < r)
    (hε : 0 < ε) (hθ : 0 < θ) :
    (∀ᶠ d : ℕ in atTop, ∀ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ), ∀ t > 0,
      Integrable (relEntropyDensity m (solution d m x₀ t) (equilibrium d m))) ∧
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        (relEntropy m (solution d m x₀ ((1 - ε) * θ * log d)) (equilibrium d m) : EReal))
        atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        (relEntropy m (solution d m x₀ ((1 + ε) * θ * log d)) (equilibrium d m) : EReal))
        atTop (𝓝 0) := by
  obtain ⟨K, H⟩ := upperHyp_fixed hm hr hε hθ
  refine ⟨?_, fun hε1 => relEntropy_lower_shift (shiftHyp_fixed hm hr hε hε1 hθ),
    relEntropy_upper H⟩
  filter_upwards [eventually_ge_atTop 1] with d hd x₀ _ t ht
  obtain ⟨h, h2⟩ := Cutoff.admissible_of_one_lt hm hd
  exact integrable_relEntropyDensity_solution h h2 x₀ ht

/-- **Section 1.4.3, Theorem 1.2 for other initial data, Fisher information.** -/
theorem cutoff_fixedExponent_fisherInfo_radius' {m r ε θ : ℝ} (hm : 1 < m) (hr : 0 < r)
    (hε : 0 < ε) (hθ : 0 < θ) :
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        fisherInfo m (solution d m x₀ ((1 - ε) * θ * log d))) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        fisherInfo m (solution d m x₀ ((1 + ε) * θ * log d))) atTop (𝓝 0) := by
  obtain ⟨K, H⟩ := upperHyp_fixed hm hr hε hθ
  exact ⟨fun hε1 => fisherInfo_lower_shift (shiftHyp_fixed hm hr hε hε1 hθ), fisherInfo_upper H⟩

private lemma max_half_cutoffTime (α : ℝ) : max (α / 2) (1 / 2 : ℝ) = max 1 α / 2 := by
  rw [max_div_div_right (by norm_num : (0 : ℝ) ≤ 2), max_comm]

/-- **Theorem 1.1, Wasserstein distance.** Fix `α ∈ (0,1/2) ∪ (1/2,∞)`, `r > 0`, and let
`m = ((d-2)α+1)/(dα)`. Then `sup_{|x₀| ≤ r√d} W₂²(v(t_d), v_∞)` tends to `+∞` if
`t_d = (1-ε) max(1,α)/2 log d` and to `0` if `t_d = (1+ε) max(1,α)/2 log d`. -/
theorem cutoff_wassersteinSq' {α r ε : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hr : 0 < r)
    (hε : 0 < ε) :
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        wassersteinSq
          (densityMeasure (solution d (exponentOfAlpha α d) x₀ ((1 - ε) * (max 1 α / 2) * log d)))
          (densityMeasure (equilibrium d (exponentOfAlpha α d)))) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        wassersteinSq
          (densityMeasure (solution d (exponentOfAlpha α d) x₀ ((1 + ε) * (max 1 α / 2) * log d)))
          (densityMeasure (equilibrium d (exponentOfAlpha α d)))) atTop (𝓝 0) := by
  simpa only [← Real.sqrt_eq_rpow, max_half_cutoffTime] using
    cutoff_wassersteinSq_radius' (θ := 1 / 2) hα hα2 hr hε


/-- **Theorem 1.1, relative entropy.** Same setting as `cutoff_wassersteinSq`. For large `d`
the entropy integrand is integrable for all `t > 0` and `|x₀| ≤ r√d`, and
`sup_{|x₀| ≤ r√d} Hₘ(v(t_d) | v_∞)` tends to `+∞` if `t_d = (1-ε) max(1,α)/2 log d`
and to `0` if `t_d = (1+ε) max(1,α)/2 log d`. -/
theorem cutoff_relEntropy' {α r ε : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hr : 0 < r)
    (hε : 0 < ε) :
    (∀ᶠ d : ℕ in atTop, ∀ x₀ ∈ closedBall (0 : E d) (r * √d), ∀ t > 0,
      Integrable (relEntropyDensity (exponentOfAlpha α d) (solution d (exponentOfAlpha α d) x₀ t)
        (equilibrium d (exponentOfAlpha α d)))) ∧
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        (relEntropy (exponentOfAlpha α d)
          (solution d (exponentOfAlpha α d) x₀ ((1 - ε) * (max 1 α / 2) * log d))
          (equilibrium d (exponentOfAlpha α d)) : EReal)) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        (relEntropy (exponentOfAlpha α d)
          (solution d (exponentOfAlpha α d) x₀ ((1 + ε) * (max 1 α / 2) * log d))
          (equilibrium d (exponentOfAlpha α d)) : EReal)) atTop (𝓝 0) := by
  simpa only [← Real.sqrt_eq_rpow, max_half_cutoffTime] using
    cutoff_relEntropy_radius' (θ := 1 / 2) hα hα2 hr hε


/-- **Theorem 1.1, Fisher information.** Same setting as `cutoff_wassersteinSq`:
`sup_{|x₀| ≤ r√d} Iₘ(v(t_d) | v_∞)` tends to `+∞` if `t_d = (1-ε) max(1,α)/2 log d`
and to `0` if `t_d = (1+ε) max(1,α)/2 log d`. -/
theorem cutoff_fisherInfo' {α r ε : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hr : 0 < r)
    (hε : 0 < ε) :
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        fisherInfo (exponentOfAlpha α d)
          (solution d (exponentOfAlpha α d) x₀ ((1 - ε) * (max 1 α / 2) * log d))) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        fisherInfo (exponentOfAlpha α d)
          (solution d (exponentOfAlpha α d) x₀ ((1 + ε) * (max 1 α / 2) * log d))) atTop (𝓝 0) := by
  simpa only [← Real.sqrt_eq_rpow, max_half_cutoffTime] using
    cutoff_fisherInfo_radius' (θ := 1 / 2) hα hα2 hr hε


/-- **Theorem 1.2, Wasserstein distance.** Fix `m > 1` and `r > 0` (so that
`α = 1/(2 - d(1-m)) → 0`). Then `sup_{|x₀| ≤ r√d} W₂²(v(t_d), v_∞)` tends to `+∞` if
`t_d = (1-ε)/2 log d` and to `0` if `t_d = (1+ε)/2 log d`. -/
theorem cutoff_fixedExponent_wassersteinSq' {m r ε : ℝ} (hm : 1 < m) (hr : 0 < r)
    (hε : 0 < ε) :
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        wassersteinSq (densityMeasure (solution d m x₀ ((1 - ε) / 2 * log d)))
          (densityMeasure (equilibrium d m))) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        wassersteinSq (densityMeasure (solution d m x₀ ((1 + ε) / 2 * log d)))
          (densityMeasure (equilibrium d m))) atTop (𝓝 0) := by
  simpa only [Real.sqrt_eq_rpow, div_eq_mul_inv, one_mul] using
    cutoff_fixedExponent_wassersteinSq_radius' (θ := 1 / 2) hm hr hε (by norm_num)


/-- **Theorem 1.2, relative entropy.** Same setting as `cutoff_fixedExponent_wassersteinSq`,
with integrability of the entropy integrand for large `d`. -/
theorem cutoff_fixedExponent_relEntropy' {m r ε : ℝ} (hm : 1 < m) (hr : 0 < r) (hε : 0 < ε) :
    (∀ᶠ d : ℕ in atTop, ∀ x₀ ∈ closedBall (0 : E d) (r * √d), ∀ t > 0,
      Integrable (relEntropyDensity m (solution d m x₀ t) (equilibrium d m))) ∧
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        (relEntropy m (solution d m x₀ ((1 - ε) / 2 * log d)) (equilibrium d m) : EReal))
        atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        (relEntropy m (solution d m x₀ ((1 + ε) / 2 * log d)) (equilibrium d m) : EReal))
        atTop (𝓝 0) := by
  simpa only [Real.sqrt_eq_rpow, div_eq_mul_inv, one_mul] using
    cutoff_fixedExponent_relEntropy_radius' (θ := 1 / 2) hm hr hε (by norm_num)


/-- **Theorem 1.2, Fisher information.** Same setting as
`cutoff_fixedExponent_wassersteinSq`. -/
theorem cutoff_fixedExponent_fisherInfo' {m r ε : ℝ} (hm : 1 < m) (hr : 0 < r) (hε : 0 < ε) :
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        fisherInfo m (solution d m x₀ ((1 - ε) / 2 * log d))) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        fisherInfo m (solution d m x₀ ((1 + ε) / 2 * log d))) atTop (𝓝 0) := by
  simpa only [Real.sqrt_eq_rpow, div_eq_mul_inv, one_mul] using
    cutoff_fixedExponent_fisherInfo_radius' (θ := 1 / 2) hm hr hε (by norm_num)

/-- **After Lemma 4.2.** The compactly supported Barenblatt profile is positive exactly on the
open ball of radius `√(c/b)`, and for fixed `m > 1` (`p = 1/(m-1)`, `b = (m-1)/(2m)`) this
radius is equivalent to `√(d/(2πe))` as `d → ∞`. -/
theorem compactBarenblatt_support' {m : ℝ} (hm : 1 < m) :
    (∀ (d : ℕ) {p b : ℝ}, 0 < p → 0 < b → ∀ x : E d,
      0 < compactBarenblatt d p b x ↔ ‖x‖ < √(compactBarenblattConst d p b / b)) ∧
    Asymptotics.IsEquivalent atTop
      (fun d : ℕ => √(compactBarenblattConst d (1 / (m - 1)) ((m - 1) / (2 * m)) /
        ((m - 1) / (2 * m))))
      (fun d => √(d / (2 * π * exp 1))) := by
  refine ⟨fun d p b hp hb x => ?_, ?_⟩
  · unfold compactBarenblatt
    rw [lt_sqrt (norm_nonneg _), lt_div_iff₀ hb]
    constructor
    · intro h
      by_contra hc
      push Not at hc
      rw [max_eq_right (by linarith), zero_rpow hp.ne'] at h
      exact lt_irrefl _ h
    · intro h
      exact rpow_pos_of_pos (lt_max_of_lt_left (by linarith)) _
  · set b := (m - 1) / (2 * m) with hb_def
    have hb : 0 < b := div_pos (by linarith) (by linarith)
    have h1 := (compactBarenblatt_fixedExponent_asymptotics' hm).1
    have h2 : Asymptotics.IsEquivalent atTop
        (fun d : ℕ => compactBarenblattConst d (1 / (m - 1)) b / b)
        (fun d : ℕ => b * d / (2 * π * exp 1) / b) :=
      h1.div (Asymptotics.IsEquivalent.refl (u := fun _ : ℕ => b))
    have h3 : Asymptotics.IsEquivalent atTop
        (fun d : ℕ => compactBarenblattConst d (1 / (m - 1)) b / b)
        (fun d : ℕ => (d : ℝ) / (2 * π * exp 1)) := by
      refine h2.congr_right ?_
      filter_upwards with d
      field_simp
    have hz : ∀ᶠ d : ℕ in atTop, (d : ℝ) / (2 * π * exp 1) ≠ 0 := by
      filter_upwards [eventually_ge_atTop 1] with d hd
      have : (0 : ℝ) < d := by exact_mod_cast hd
      positivity
    have h4 := (Asymptotics.isEquivalent_iff_tendsto_one hz).1 h3
    have h5 := (continuous_sqrt.tendsto 1).comp h4
    rw [sqrt_one] at h5
    refine Asymptotics.isEquivalent_of_tendsto_one (h5.congr' ?_)
    filter_upwards with d
    simp only [Function.comp_apply, Pi.div_apply]
    rw [sqrt_div' _ (by positivity)]

/-- **Theorem 1.1, Wasserstein distance.** Fix `α ∈ (0,1/2) ∪ (1/2,∞)`, `r > 0`, and let
`m = ((d-2)α+1)/(dα)`. Then `sup_{|x₀| ≤ r√d} W₂²(v(t_d), v_∞)` tends to `+∞` if
`t_d = (1-ε) max(1,α)/2 log d` and to `0` if `t_d = (1+ε) max(1,α)/2 log d`. -/
alias cutoff_wassersteinSq := cutoff_wassersteinSq'

/-- **Theorem 1.1, relative entropy.** Same setting as `cutoff_wassersteinSq`. For large `d`
the entropy integrand is integrable for all `t > 0` and `|x₀| ≤ r√d`, and
`sup_{|x₀| ≤ r√d} Hₘ(v(t_d) | v_∞)` tends to `+∞` if `t_d = (1-ε) max(1,α)/2 log d`
and to `0` if `t_d = (1+ε) max(1,α)/2 log d`. -/
alias cutoff_relEntropy := cutoff_relEntropy'

/-- **Theorem 1.1, Fisher information.** Same setting as `cutoff_wassersteinSq`:
`sup_{|x₀| ≤ r√d} Iₘ(v(t_d) | v_∞)` tends to `+∞` if `t_d = (1-ε) max(1,α)/2 log d`
and to `0` if `t_d = (1+ε) max(1,α)/2 log d`. -/
alias cutoff_fisherInfo := cutoff_fisherInfo'

/-- **Theorem 1.2, Wasserstein distance.** Fix `m > 1` and `r > 0` (so that
`α = 1/(2 - d(1-m)) → 0`). Then `sup_{|x₀| ≤ r√d} W₂²(v(t_d), v_∞)` tends to `+∞` if
`t_d = (1-ε)/2 log d` and to `0` if `t_d = (1+ε)/2 log d`. -/
alias cutoff_fixedExponent_wassersteinSq := cutoff_fixedExponent_wassersteinSq'

/-- **Theorem 1.2, relative entropy.** Same setting as `cutoff_fixedExponent_wassersteinSq`,
with integrability of the entropy integrand for large `d`. -/
alias cutoff_fixedExponent_relEntropy := cutoff_fixedExponent_relEntropy'

/-- **Theorem 1.2, Fisher information.** Same setting as
`cutoff_fixedExponent_wassersteinSq`. -/
alias cutoff_fixedExponent_fisherInfo := cutoff_fixedExponent_fisherInfo'

/-- **Section 1.4.3, Theorem 1.1 for other initial data, Wasserstein.** For initial points in the
ball of radius `r d^θ` (`θ ∈ ℝ`), the critical time becomes `max(α/2, θ) log d`. -/
alias cutoff_wassersteinSq_radius := cutoff_wassersteinSq_radius'

/-- **Section 1.4.3, Theorem 1.1 for other initial data, relative entropy.** As in
`cutoff_relEntropy`, the entropy integrand is integrable for large `d`, for all `t > 0` and all
initial points in the ball. -/
alias cutoff_relEntropy_radius := cutoff_relEntropy_radius'

/-- **Section 1.4.3, Theorem 1.1 for other initial data, Fisher information.** -/
alias cutoff_fisherInfo_radius := cutoff_fisherInfo_radius'

/-- **Section 1.4.3, Theorem 1.2 for other initial data, Wasserstein.** For initial points in the
ball of radius `r d^θ` (`θ > 0`), the critical time becomes `θ log d`. -/
alias cutoff_fixedExponent_wassersteinSq_radius := cutoff_fixedExponent_wassersteinSq_radius'

/-- **Section 1.4.3, Theorem 1.2 for other initial data, relative entropy.** As in
`cutoff_fixedExponent_relEntropy`, the entropy integrand is integrable for large `d`, for all
`t > 0` and all initial points in the ball. -/
alias cutoff_fixedExponent_relEntropy_radius := cutoff_fixedExponent_relEntropy_radius'

/-- **Section 1.4.3, Theorem 1.2 for other initial data, Fisher information.** -/
alias cutoff_fixedExponent_fisherInfo_radius := cutoff_fixedExponent_fisherInfo_radius'

/-- **After Lemma 4.2.** The compactly supported Barenblatt profile is positive exactly on the
open ball of radius `√(c/b)`, and for fixed `m > 1` (`p = 1/(m-1)`, `b = (m-1)/(2m)`) this
radius is equivalent to `√(d/(2πe))` as `d → ∞`. -/
alias compactBarenblatt_support := compactBarenblatt_support'

end Cutfast
