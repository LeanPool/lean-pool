/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Taylor vanishing orders and integral remainders

Real normed-space functions have equivalent smooth vanishing-order and power bounds.

## Main results

* `TrotterError.taylorWithinEval_eq_smul_of_iteratedDeriv_eq_zero_below`.
* `TrotterError.isBigO_norm_iff_iteratedDeriv_eq_zero`.
* `TrotterError.taylorWithinEval_eq_zero_of_iteratedDeriv_eq_zero`.
* `TrotterError.taylor_paper_scalar_eq`.
* `TrotterError.taylor_integral_remainder_iteratedDeriv_zero`.
* `TrotterError.taylor_integral_remainder_iteratedDeriv_zero_paper`.
-/

@[expose] public section

namespace TrotterError

open NormedSpace Asymptotics Finset
open scoped Topology BigOperators ContDiff algebraMap

/-- If the first `n` iterated derivatives of `F` at `x₀` vanish, then the `n`-th Taylor
polynomial of `F` at `x₀` is just the leading term `(x - x₀)^n • ((n! : ℝ)⁻¹ • F⁽ⁿ⁾(x₀))`. -/
lemma taylorWithinEval_eq_smul_of_iteratedDeriv_eq_zero_below
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (n : ℕ) {x₀ x : ℝ}
    (h0 : ∀ k < n, iteratedDeriv k F x₀ = 0) :
    taylorWithinEval F n Set.univ x₀ x =
      (x - x₀) ^ n • ((Nat.factorial n : ℝ)⁻¹ • iteratedDeriv n F x₀) := by
  rw [taylor_within_apply, Finset.sum_range_succ]
  have hsum : (∑ k ∈ Finset.range n, ((Nat.factorial k : ℝ)⁻¹ * (x - x₀) ^ k) •
      iteratedDerivWithin k F Set.univ x₀) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : k < n := Finset.mem_range.mp hk
    rw [iteratedDerivWithin_univ, h0 k hkn, smul_zero]
  rw [hsum, zero_add]
  simp only [iteratedDerivWithin_univ]
  rw [mul_smul, smul_comm]

/-- A smooth function `F` satisfies `‖F t‖ = O(t^(p + 1))` as `t → 0` if and only if its
iterated derivatives of orders zero through `p` vanish at `0` (CS19, Supplementary Lemma 1). -/
theorem isBigO_norm_iff_iteratedDeriv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (p : ℕ) (hF : ContDiff ℝ ∞ F) :
    (fun t : ℝ => ‖F t‖) =O[𝓝 (0 : ℝ)] (fun t : ℝ => t ^ (p + 1)) ↔
      ∀ j : ℕ, j ≤ p → iteratedDeriv j F 0 = 0 := by
  classical
  constructor
  · intro hbig; by_contra hnot
    have hex : ∃ j : ℕ, j ≤ p ∧ iteratedDeriv j F 0 ≠ 0 := by
      by_contra h; apply hnot
      intro j hj; by_contra hjz
      exact h ⟨j, hj, hjz⟩
    rcases hex with ⟨j₀, hj₀_le, hj₀_nz⟩
    have hex' : ∃ j : ℕ, iteratedDeriv j F 0 ≠ 0 := ⟨j₀, hj₀_nz⟩
    let j := Nat.find hex'
    have hj_nz : iteratedDeriv j F 0 ≠ 0 := Nat.find_spec hex'
    have hj_min : ∀ k < j, iteratedDeriv k F 0 = 0 := by
      intro k hk
      by_contra hk'
      exact (Nat.find_min hex' hk) hk'
    have hj_le : j ≤ p := le_trans (Nat.find_min' hex' hj₀_nz) hj₀_le
    have hbigF : F =O[𝓝 (0 : ℝ)] (fun t : ℝ => t ^ (p + 1)) := isBigO_norm_left.mp hbig
    rw [isBigO_iff] at hbigF
    rcases hbigF with ⟨C₁, hbigF⟩
    have hbigF' : ∀ᶠ t in 𝓝 (0 : ℝ), ‖F t‖ ≤ C₁ * |t| ^ (p + 1) := by
      filter_upwards [hbigF] with t ht
      simpa [norm_pow] using ht
    have hFj : ContDiff ℝ j F := hF.of_le (mod_cast le_top)
    have htaylor : (fun x : ℝ => F x - taylorWithinEval F j Set.univ 0 x) =o[𝓝 (0 : ℝ)]
        (fun x : ℝ => x ^ j) := by
      simpa using (taylor_isLittleO_univ (f := F) (x₀ := 0) (n := j) hFj)
    let c : E := ((Nat.factorial j : ℝ)⁻¹) • iteratedDeriv j F 0
    have htaylor' : (fun x : ℝ => F x - x ^ j • c) =o[𝓝 (0 : ℝ)] (fun x : ℝ => x ^ j) := by
      refine htaylor.congr_left (fun x => ?_)
      rw [taylorWithinEval_eq_smul_of_iteratedDeriv_eq_zero_below F j (x₀ := 0) (x := x) hj_min]
      simp [c]
    have hc_nz : c ≠ 0 := smul_ne_zero (inv_ne_zero (by positivity)) hj_nz
    have hrem : ∀ᶠ x in 𝓝 (0 : ℝ), ‖F x - x ^ j • c‖ ≤ (‖c‖ / 2) * |x| ^ j := by
      filter_upwards [htaylor'.def (show 0 < ‖c‖ / 2 by positivity)] with x hx
      simpa [norm_pow] using hx
    have hlower : ∀ᶠ x in 𝓝 (0 : ℝ), (‖c‖ / 2) * |x| ^ j ≤ ‖F x‖ := by
      filter_upwards [hrem] with x hx
      have hnorm : ‖x ^ j • c‖ = ‖c‖ * |x| ^ j := by
        rw [norm_smul, norm_pow, Real.norm_eq_abs, mul_comm]
      have htri : ‖x ^ j • c‖ - ‖F x‖ ≤ ‖F x - x ^ j • c‖ := by
        have h := norm_sub_norm_le (x ^ j • c) (F x)
        simpa [norm_sub_rev] using h
      linarith [hnorm, htri, hx]
    have hcombine : ∀ᶠ x in 𝓝 (0 : ℝ), (‖c‖ / 2) * |x| ^ j ≤ C₁ * |x| ^ (p + 1) := by
      filter_upwards [hlower, hbigF'] with x hlow hbig
      exact hlow.trans hbig
    have hO_scaled : (fun x : ℝ => (‖c‖ / 2) * |x| ^ j) =O[𝓝 (0 : ℝ)]
        (fun x : ℝ => |x| ^ (p + 1)) := by
      refine IsBigO.of_bound C₁ ?_
      filter_upwards [hcombine] with x hx
      rwa [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have hO : (fun x : ℝ => |x| ^ j) =O[𝓝 (0 : ℝ)] (fun x : ℝ => |x| ^ (p + 1)) :=
      (isBigO_const_mul_left_iff (f := fun x : ℝ => |x| ^ j) (g := fun x : ℝ => |x| ^ (p + 1))
        (c := ‖c‖ / 2) (l := 𝓝 (0 : ℝ)) (by positivity)).1 hO_scaled
    have ho : (fun x : ℝ => |x| ^ (p + 1)) =o[𝓝 (0 : ℝ)] (fun x : ℝ => |x| ^ j) := by
      simpa [Real.norm_eq_abs] using
        (isLittleO_norm_pow_norm_pow (E' := ℝ) (m := j) (n := p + 1) (by lia))
    have hfreq0 : ∃ᶠ x in 𝓝 (0 : ℝ), x ≠ 0 := by
      rw [Filter.frequently_iff]
      intro U hU
      rcases Metric.mem_nhds_iff.mp hU with ⟨ε, hε, hU⟩
      refine ⟨ε / 2, hU ?_, ne_of_gt (div_pos hε (by norm_num))⟩
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_of_nonneg (by positivity)]
      linarith
    have hfreq : ∃ᶠ x in 𝓝 (0 : ℝ), |x| ^ j ≠ 0 :=
      hfreq0.mono fun x hx => pow_ne_zero j (abs_ne_zero.mpr hx)
    exact (isLittleO_irrefl hfreq) (hO.trans_isLittleO ho)
  · intro h0
    have hFp1 : ContDiff ℝ (p + 1) F := hF.of_le (mod_cast le_top)
    have htaylor : (fun x : ℝ => F x - taylorWithinEval F (p + 1) Set.univ 0 x) =o[𝓝 (0 : ℝ)]
        (fun x : ℝ => x ^ (p + 1)) := by
      simpa using (taylor_isLittleO_univ (f := F) (x₀ := 0) (n := p + 1) hFp1)
    let a : E := ((Nat.factorial (p + 1) : ℝ)⁻¹) • iteratedDeriv (p + 1) F 0
    have htaylor' : (fun x : ℝ => F x - x ^ (p + 1) • a) =o[𝓝 (0 : ℝ)]
        (fun x : ℝ => x ^ (p + 1)) := by
      refine htaylor.congr_left (fun x => ?_)
      rw [taylorWithinEval_eq_smul_of_iteratedDeriv_eq_zero_below F (p + 1) (x₀ := 0) (x := x)
        (fun k hk => h0 k (Nat.lt_succ_iff.mp hk))]
      simp [a]
    have hbig_smul : (fun x : ℝ => x ^ (p + 1) • a) =O[𝓝 (0 : ℝ)] (fun x : ℝ => x ^ (p + 1)) := by
      refine IsBigO.of_bound ‖a‖ ?_
      filter_upwards with x
      simp [norm_smul, mul_comm]
    have hbig_F : (fun x : ℝ => F x) =O[𝓝 (0 : ℝ)] (fun x : ℝ => x ^ (p + 1)) :=
      (hbig_smul.add htaylor'.isBigO).congr_left (fun x => by abel)
    exact isBigO_norm_left.mpr hbig_F

/-- If the iterated derivatives of `f` of orders zero through `p` vanish at `0`, its Taylor
polynomial on `uIcc 0 t` (with base point `0`) vanishes, provided `t ≠ 0`. -/
lemma taylorWithinEval_eq_zero_of_iteratedDeriv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {p : ℕ} {t : ℝ}
    (hf : ContDiff ℝ (p + 1) f)
    (h0 : ∀ k ≤ p, iteratedDeriv k f 0 = 0)
    (ht : t ≠ 0) :
    taylorWithinEval f p (Set.uIcc 0 t) 0 t = 0 := by
  rw [taylor_within_apply]
  have hud : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) t) := uniqueDiffOn_uIcc (Ne.symm ht)
  apply Finset.sum_eq_zero
  intro k hk
  have hk_le_p : k ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hk_le : k ≤ p + 1 := le_trans hk_le_p (Nat.le_succ p)
  rw [iteratedDerivWithin_eq_iteratedDeriv hud (hf.contDiffAt.of_le (mod_cast hk_le))
    (by simp)]
  simp [h0 k hk_le_p]

/-- The scalar identity used to pass from the standard integral remainder to the paper's
substituted form: `t * (t - u * t)^p / p! = (p + 1) * (1 - u)^p * t^(p + 1) / (p + 1)!`. -/
lemma taylor_paper_scalar_eq (p : ℕ) (t u : ℝ) :
    t * ((t - u * t) ^ p / (Nat.factorial p : ℝ)) =
      (p + 1 : ℝ) * ((1 - u) ^ p * (t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ))) := by
  rw [Nat.factorial_succ, Nat.cast_mul]
  field_simp
  rw [mul_pow]
  push_cast
  ring

/-- Taylor's theorem with integral remainder when the derivatives of orders zero through `p`
vanish at `0`: `f t = ∫₀ᵗ ((t - s)^p / p!) • f⁽ᵖ⁺¹⁾(s) ds`. -/
theorem taylor_integral_remainder_iteratedDeriv_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {p : ℕ} {t : ℝ}
    (hf : ContDiff ℝ (p + 1) f)
    (h0 : ∀ k ≤ p, iteratedDeriv k f 0 = 0) :
    f t = ∫ s in (0 : ℝ)..t,
      ((t - s) ^ p / (Nat.factorial p : ℝ)) • iteratedDeriv (p + 1) f s := by
  by_cases ht : t = 0
  · subst t
    simpa using (h0 0 (Nat.zero_le p))
  · have hud : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) t) := uniqueDiffOn_uIcc (Ne.symm ht)
    have hpoly : taylorWithinEval f p (Set.uIcc (0 : ℝ) t) 0 t = 0 :=
      taylorWithinEval_eq_zero_of_iteratedDeriv_eq_zero hf h0 ht
    have hmain := taylor_integral_remainder (f := f) (x₀ := 0) (x := t) (n := p) hf.contDiffOn
    have hf_t : f t = ∫ s in (0 : ℝ)..t,
        ((t - s) ^ p / (Nat.factorial p : ℝ)) •
          iteratedDerivWithin (p + 1) f (Set.uIcc (0 : ℝ) t) s := by
      simpa [hpoly] using hmain
    rw [hf_t]
    apply intervalIntegral.integral_congr_uIoo
    intro s hs
    exact congrArg (fun y => ((t - s) ^ p / (Nat.factorial p : ℝ)) • y)
      (iteratedDerivWithin_eq_iteratedDeriv hud hf.contDiffAt (Set.uIoo_subset_uIcc_self hs))

/-- Taylor's theorem with the integral remainder in the paper's substituted form
(`s = u * t`): `f t = (p + 1) • ∫₀¹ (1 - u)^p * t^(p + 1) / (p + 1)! • f⁽ᵖ⁺¹⁾(u * t) du`. -/
theorem taylor_integral_remainder_iteratedDeriv_zero_paper
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {p : ℕ} {t : ℝ}
    (hf : ContDiff ℝ (p + 1) f)
    (h0 : ∀ k ≤ p, iteratedDeriv k f 0 = 0) :
    f t = (p + 1 : ℝ) • ∫ u in (0 : ℝ)..(1 : ℝ),
      ((1 - u) ^ p * (t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ))) •
        iteratedDeriv (p + 1) f (u * t) := by
  rw [taylor_integral_remainder_iteratedDeriv_zero hf h0]
  calc
    ∫ s in (0 : ℝ)..t, ((t - s) ^ p / (Nat.factorial p : ℝ)) • iteratedDeriv (p + 1) f s
        = t • ∫ u in (0 : ℝ)..(1 : ℝ),
            ((t - u * t) ^ p / (Nat.factorial p : ℝ)) • iteratedDeriv (p + 1) f (u * t) := by
            simpa [mul_zero, one_mul] using
              (intervalIntegral.smul_integral_comp_mul_right
                (f := fun s => ((t - s) ^ p / (Nat.factorial p : ℝ)) • iteratedDeriv (p + 1) f s)
                (a := 0) (b := 1) (c := t)).symm
    _ = (p + 1 : ℝ) • ∫ u in (0 : ℝ)..(1 : ℝ),
          ((1 - u) ^ p * (t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ))) •
            iteratedDeriv (p + 1) f (u * t) := by
          simp only [← intervalIntegral.integral_smul]
          apply intervalIntegral.integral_congr_uIoo
          intro u _
          simp only [smul_smul]
          exact congrArg₂ (fun r y => r • y) (taylor_paper_scalar_eq p t u) rfl

end TrotterError
