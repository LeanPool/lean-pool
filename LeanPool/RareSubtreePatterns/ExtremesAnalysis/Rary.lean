/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.ExtremesAnalysis.Unary


/-!
# Doubly exponential level intensities: centering, thresholds, two-point levels

Deterministic part of Theorem `thm:max_string`(ii) (source lines 486–501, proof 2851–2897,
inventory P20) and of the case `μ_1 = 0`, `c > 0` of Theorem `thm:max_lh`(ii) (source lines
542–558, proof 3328–3383, inventory P24).

Let `r ≥ 2` be an integer, `D ∈ (0, 1)` and `x_n = log_r log n - log_r log(1/D)`, so that
`r^{x_n} = log n / log(1/D)` for `n ≥ 2` (`rpow_doubleLogCenter`). Write `m_n = ⌊x_n⌋`,
`θ_n = {x_n}`.

* Exact identity (`natCast_mul_pow_pow_eq`): `n D^{r^k} = n^{1 - r^{k - x_n}}` for `n ≥ 2`, every
  `k ∈ ℕ`. For `k = m_n + j` this is `n^{1 - r^{j - θ_n}}`.
* If `p_k ∼ A D^{r^k}` with `A > 0` then for every fixed `j ∈ ℤ`,
  `n p_{m_n + j} ∼ A n^{1 - r^{j - θ_n}}` (`isEquivalent_level`; source lines 2855–2858 and
  3336–3342; the levels `m_n + j` are eventually nonnegative).
* Thresholds, along any filter `l ≤ atTop` (a subsequence, e.g. admissible sizes or the indices
  with `θ_n ≤ 1/2`): if the integer level `h_n` satisfies `h_n ≥ x_n + δ` eventually then
  `n p_{h_n} → 0`; if `x_n - K ≤ h_n ≤ x_n - δ` eventually then `n p_{h_n} → ∞`
  (`tendsto_mul_zero_of_isEquivalent`, `tendsto_mul_atTop_of_isEquivalent`). These are the
  inputs of `eq:threshold_rary` / `eq:threshold_lh`.
* Two-point levels: with `a_n = twoPointLow x_n`, `J_n = {a_n, a_n + 1}`,
  `n p_{a_n} → ∞` and `n p_{a_n + 2} → 0` along the whole sequence (`twoPoint_thresholds`); the
  source's split at `θ_n = 1/2` is also provided (`fract_le_half_thresholds`,
  `half_lt_fract_thresholds`). Interior phase (`δ ≤ min(θ_n, 1 - θ_n)` eventually along `l`):
  `n p_{m_n} → ∞`, `n p_{m_n + 1} → 0` along `l` (`interior_thresholds`).
* Level sizes: every level `h_n ≤ x_n + K` satisfies `r^{h_n} = O(log n)`, hence
  `r^{h_n} ≤ n^δ` eventually for every `δ > 0` (`pow_level_le_rpow`), the hypothesis of Lemmas
  `lem:S_rary`(i) and `lem:S_lh`(i).
* Complete `r`-ary specialization (`D = μ_r^{1/(r-1)}`, `A = μ_r^{-1/(r-1)}`):
  `π_k = μ_r^{(r^k-1)/(r-1)} = A D^{r^k}` exactly (`rary_pi_eq`), the centering is
  `t_n^{**} = tStarStar r μ_r n` (`tStarStar_eq`), and
  `n π_k = μ_r^{-1/(r-1)} n^{1 - r^{k - t_n^{**}}}` exactly for `n ≥ 2` (`rary_natCast_mul_eq`).
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace PoissonDeclumping
namespace ExtremesAnalysis

variable {r : ℕ} {D : ℝ} {x : ℕ → ℝ}

theorem log_one_div_pos (hD0 : 0 < D) (hD1 : D < 1) : 0 < Real.log (1 / D) :=
  Real.log_pos (by rw [lt_div_iff₀ hD0]; linarith)

section Generic

variable (hr : 2 ≤ r) (hD0 : 0 < D) (hD1 : D < 1)
  (hx : ∀ n, x n = Real.logb r (Real.log n) - Real.logb r (Real.log (1 / D)))
include hr hD0 hD1 hx

omit hD0 hD1 in
/-- `x_n → ∞`. -/
theorem tendsto_doubleLogCenter : Tendsto x atTop atTop := by
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have h : Tendsto (fun n : ℕ => Real.logb r (Real.log n) - Real.logb r (Real.log (1 / D)))
      atTop atTop :=
    tendsto_atTop_add_const_right _ _ ((Real.tendsto_logb_atTop hr1).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  exact h.congr fun n => (hx n).symm

/-- `r^{x_n} = log n / log(1/D)` for `n ≥ 2` (source lines 2853 and 3335). -/
theorem rpow_doubleLogCenter {n : ℕ} (hn : 2 ≤ n) :
    (r : ℝ) ^ x n = Real.log n / Real.log (1 / D) := by
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  rw [hx, Real.rpow_sub (by linarith), Real.rpow_logb (by linarith) hr1.ne'
    (Real.log_pos hn'), Real.rpow_logb (by linarith) hr1.ne' (log_one_div_pos hD0 hD1)]

/-- Exact identity: `n D^{r^k} = n^{1 - r^{k - x_n}}` for `n ≥ 2`. -/
theorem natCast_mul_pow_pow_eq {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    (n : ℝ) * D ^ (r ^ k) = (n : ℝ) ^ (1 - (r : ℝ) ^ ((k : ℝ) - x n)) := by
  have hr0 : (0 : ℝ) < r := by have : (2 : ℝ) ≤ r := by exact_mod_cast hr
                               linarith
  have hn0 : (0 : ℝ) < n := by have : (2 : ℝ) ≤ n := by exact_mod_cast hn
                               linarith
  have hL := log_one_div_pos hD0 hD1
  have hrk : ((r ^ k : ℕ) : ℝ) = (r : ℝ) ^ ((k : ℝ) - x n) * (Real.log n / Real.log (1 / D)) := by
    rw [← rpow_doubleLogCenter hr hD0 hD1 hx hn, ← Real.rpow_add hr0, sub_add_cancel,
      Real.rpow_natCast, Nat.cast_pow]
  have hlogD : Real.log D = -Real.log (1 / D) := by rw [one_div, Real.log_inv, neg_neg]
  rw [← Real.rpow_natCast D, Real.rpow_def_of_pos hD0, Real.rpow_def_of_pos hn0]
  conv_lhs => rw [← Real.exp_log hn0]
  rw [← Real.exp_add, hrk, hlogD]
  congr 1
  field_simp
  ring

/-- If `h_n ≥ x_n + δ` eventually along `l`, then `n D^{r^{h_n}} → 0` along `l`. -/
theorem tendsto_mul_pow_pow_zero {l : Filter ℕ} (hl : l ≤ atTop) {h : ℕ → ℤ} {δ : ℝ}
    (hδ : 0 < δ) (hh : ∀ᶠ n in l, x n + δ ≤ h n) :
    Tendsto (fun n : ℕ => (n : ℝ) * D ^ (r ^ (h n).toNat)) l (𝓝 0) := by
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hε : 0 < (r : ℝ) ^ δ - 1 := by
    have := Real.one_lt_rpow hr1 hδ
    linarith
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-((r : ℝ) ^ δ - 1))) l (𝓝 0) :=
    ((tendsto_rpow_neg_atTop hε).comp tendsto_natCast_atTop_atTop).mono_left hl
  refine squeeze_zero' ?_ ?_ hlim
  · exact Eventually.of_forall fun n => mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hD0.le _)
  · filter_upwards [eventually_cast_toNat_eq (K := -δ)
      ((tendsto_doubleLogCenter hr hx).mono_left hl) (by simpa using hh), hh,
      hl (eventually_ge_atTop 2)] with n hn hhn hn2
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    rw [natCast_mul_pow_pow_eq hr hD0 hD1 hx hn2, hn.2]
    apply Real.rpow_le_rpow_of_exponent_le hn1
    have : (r : ℝ) ^ δ ≤ (r : ℝ) ^ ((h n : ℝ) - x n) :=
      Real.rpow_le_rpow_of_exponent_le hr1.le (by linarith)
    linarith

/-- If `h_n ≤ x_n - δ` eventually along `l`, then `n D^{r^{h_n}} → ∞` along `l` (no lower bound
on `h_n` is needed for the exact intensity). -/
theorem tendsto_mul_pow_pow_atTop {l : Filter ℕ} (hl : l ≤ atTop) {h : ℕ → ℤ} {δ : ℝ}
    (hδ : 0 < δ) (hh : ∀ᶠ n in l, (h n : ℝ) ≤ x n - δ) :
    Tendsto (fun n : ℕ => (n : ℝ) * D ^ (r ^ (h n).toNat)) l atTop := by
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hε : 0 < 1 - (r : ℝ) ^ (-δ) := by
    have := Real.rpow_lt_one_of_one_lt_of_neg hr1 (neg_lt_zero.mpr hδ)
    linarith
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - (r : ℝ) ^ (-δ))) l atTop :=
    ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).mono_left hl
  refine tendsto_atTop_mono' l ?_ hlim
  filter_upwards [hh, hl ((tendsto_doubleLogCenter hr hx).eventually_ge_atTop δ),
    hl (eventually_ge_atTop 2)] with n hhn hxn hn2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hk : (((h n).toNat : ℕ) : ℝ) ≤ x n - δ := by
    rcases le_or_gt 0 (h n) with h0 | h0
    · rw [cast_toNat_of_nonneg h0]; exact hhn
    · rw [Int.toNat_of_nonpos h0.le]; push_cast; linarith
  rw [natCast_mul_pow_pow_eq hr hD0 hD1 hx hn2]
  apply Real.rpow_le_rpow_of_exponent_le hn1
  have : (r : ℝ) ^ ((((h n).toNat : ℕ) : ℝ) - x n) ≤ (r : ℝ) ^ (-δ) :=
    Real.rpow_le_rpow_of_exponent_le hr1.le (by linarith)
  linarith

/-- Every level `h_n ≤ x_n + K` satisfies `r^{h_n} ≤ n^δ` eventually, for every `δ > 0`
(`r^{h_n} = O(log n)`; source lines 2860, 2881, 2889 and 3344). -/
theorem pow_level_le_rpow {h : ℕ → ℤ} {K : ℝ} (hh : ∀ᶠ n in atTop, (h n : ℝ) ≤ x n + K) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, (r : ℝ) ^ (h n).toNat ≤ (n : ℝ) ^ δ := by
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hL := log_one_div_pos hD0 hD1
  refine eventually_le_rpow_of_le_log le_rfl (A := (r : ℝ) ^ K / Real.log (1 / D)) (B := 0)
    (by positivity) ?_
  filter_upwards [hh, (tendsto_doubleLogCenter hr hx).eventually_ge_atTop (-K),
    eventually_ge_atTop 2] with n hhn hxn hn2
  have hk : (((h n).toNat : ℕ) : ℝ) ≤ x n + K := by
    rcases le_or_gt 0 (h n) with h0 | h0
    · rw [cast_toNat_of_nonneg h0]; exact hhn
    · rw [Int.toNat_of_nonpos h0.le]; push_cast; linarith
  rw [← Real.rpow_natCast, add_zero]
  calc (r : ℝ) ^ ((((h n).toNat : ℕ) : ℝ)) ≤ (r : ℝ) ^ (x n + K) :=
        Real.rpow_le_rpow_of_exponent_le hr1.le hk
    _ = (r : ℝ) ^ K / Real.log (1 / D) * Real.log n := by
        rw [Real.rpow_add (by linarith), rpow_doubleLogCenter hr hD0 hD1 hx hn2]
        ring

/-! #### Transfer to `p_k ∼ A D^{r^k}` -/

variable {p : ℕ → ℝ} {A : ℝ} (hp : p ~[atTop] fun k => A * D ^ (r ^ k))
include hp

omit hr hD0 hD1 hx in
/-- If the natural levels `k_n → ∞` along `l`, then `n p_{k_n} ∼ A n D^{r^{k_n}}` along `l`. -/
theorem isEquivalent_mul_comp {l : Filter ℕ} {k : ℕ → ℕ} (hk : Tendsto k l atTop) :
    (fun n : ℕ => (n : ℝ) * p (k n)) ~[l] fun n => A * ((n : ℝ) * D ^ (r ^ k n)) := by
  have h1 := (IsEquivalent.refl (u := fun n : ℕ => (n : ℝ)) (l := l)).mul (hp.comp_tendsto hk)
  refine h1.congr_right (Eventually.of_forall fun n => ?_)
  simp only [Pi.mul_apply, Function.comp]
  ring

/-- `n p_{h_n} → 0` along `l` whenever `h_n ≥ x_n + δ` eventually along `l`. -/
theorem tendsto_mul_zero_of_isEquivalent {l : Filter ℕ} (hl : l ≤ atTop) {h : ℕ → ℤ} {δ : ℝ}
    (hδ : 0 < δ) (hh : ∀ᶠ n in l, x n + δ ≤ h n) :
    Tendsto (fun n : ℕ => (n : ℝ) * p (h n).toNat) l (𝓝 0) := by
  have hk : Tendsto (fun n => (h n).toNat) l atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [hh, hl ((tendsto_doubleLogCenter hr hx).eventually_ge_atTop b)]
      with n hhn hxn
    have : ((b : ℤ) : ℝ) ≤ (h n : ℝ) := by push_cast; linarith
    have : (b : ℤ) ≤ h n := by exact_mod_cast this
    omega
  have h0 := (tendsto_mul_pow_pow_zero hr hD0 hD1 hx hl hδ hh).const_mul A
  rw [mul_zero] at h0
  exact (isEquivalent_mul_comp hp hk).symm.tendsto_nhds h0

/-- `n p_{h_n} → ∞` along `l` whenever `x_n - K ≤ h_n ≤ x_n - δ` eventually along `l`
(`A > 0`). -/
theorem tendsto_mul_atTop_of_isEquivalent (hA : 0 < A) {l : Filter ℕ} (hl : l ≤ atTop)
    {h : ℕ → ℤ} {δ K : ℝ} (hδ : 0 < δ) (hlow : ∀ᶠ n in l, x n - K ≤ h n)
    (hh : ∀ᶠ n in l, (h n : ℝ) ≤ x n - δ) :
    Tendsto (fun n : ℕ => (n : ℝ) * p (h n).toNat) l atTop := by
  have hk : Tendsto (fun n => (h n).toNat) l atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [hlow, hl ((tendsto_doubleLogCenter hr hx).eventually_ge_atTop
      (b + K))] with n hhn hxn
    have : ((b : ℤ) : ℝ) ≤ (h n : ℝ) := by push_cast; linarith
    have : (b : ℤ) ≤ h n := by exact_mod_cast this
    omega
  have h0 := (tendsto_mul_pow_pow_atTop hr hD0 hD1 hx hl hδ hh).const_mul_atTop hA
  exact (isEquivalent_mul_comp hp hk).symm.tendsto_atTop h0

/-- Source lines 2855–2858 and 3336–3342: for every fixed `j ∈ ℤ`,
`n p_{m_n + j} ∼ A n^{1 - r^{j - θ_n}}` with `m_n = ⌊x_n⌋`, `θ_n = {x_n}`. -/
theorem isEquivalent_level (j : ℤ) :
    (fun n : ℕ => (n : ℝ) * p (⌊x n⌋ + j).toNat) ~[atTop]
      fun n => A * (n : ℝ) ^ (1 - (r : ℝ) ^ ((j : ℝ) - Int.fract (x n))) := by
  have hev := eventually_cast_toNat_eq (K := 1 - j) (z := fun n => ⌊x n⌋ + j)
    (tendsto_doubleLogCenter hr hx) (Eventually.of_forall fun n => by
      have := Int.sub_one_lt_floor (x n)
      push_cast
      linarith)
  have hk : Tendsto (fun n => (⌊x n⌋ + j).toNat) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [hev, (tendsto_doubleLogCenter hr hx).eventually_ge_atTop
      (b + 1 - j)] with n hn hxn
    have := Int.sub_one_lt_floor (x n)
    have h1 : (b : ℝ) ≤ (((⌊x n⌋ + j).toNat : ℕ) : ℝ) := by
      rw [hn.2]; push_cast; linarith
    exact_mod_cast h1
  refine (isEquivalent_mul_comp hp hk).congr_right ?_
  filter_upwards [hev, eventually_ge_atTop 2] with n hn hn2
  rw [natCast_mul_pow_pow_eq hr hD0 hD1 hx hn2, hn.2, Int.fract]
  push_cast
  ring_nf

/-! #### The two-point and interior levels -/

/-- Two-point levels (source lines 2862–2880 and 3358–3374, without splitting): with
`a_n = twoPointLow x_n` (so `J_n = {a_n, a_n + 1}`), `n p_{a_n} → ∞` and `n p_{a_n + 2} → 0`
along any `l ≤ atTop`. -/
theorem twoPoint_thresholds (hA : 0 < A) {l : Filter ℕ} (hl : l ≤ atTop) :
    Tendsto (fun n : ℕ => (n : ℝ) * p (twoPointLow (x n)).toNat) l atTop ∧
      Tendsto (fun n : ℕ => (n : ℝ) * p (twoPointLow (x n) + 2).toNat) l (𝓝 0) := by
  refine ⟨tendsto_mul_atTop_of_isEquivalent hr hD0 hD1 hx hp hA hl (K := 3 / 2) (δ := 1 / 2)
    (by norm_num) (Eventually.of_forall fun n => sub_le_twoPointLow (x n))
    (Eventually.of_forall fun n => twoPointLow_le (x n)), ?_⟩
  exact tendsto_mul_zero_of_isEquivalent hr hD0 hD1 hx hp hl (δ := 1 / 2) (by norm_num)
    (Eventually.of_forall fun n => add_half_le_twoPointLow_add_two (x n))

/-- Source's split, indices with `θ_n ≤ 1/2` (source lines 2862–2870, 3363–3366):
`n p_{m_n - 1} → ∞` and `n p_{m_n + 1} → 0`. -/
theorem fract_le_half_thresholds (hA : 0 < A) {l : Filter ℕ} (hl : l ≤ atTop)
    (hθ : ∀ᶠ n in l, Int.fract (x n) ≤ 1 / 2) :
    Tendsto (fun n : ℕ => (n : ℝ) * p (⌊x n⌋ - 1).toNat) l atTop ∧
      Tendsto (fun n : ℕ => (n : ℝ) * p (⌊x n⌋ + 1).toNat) l (𝓝 0) := by
  refine ⟨tendsto_mul_atTop_of_isEquivalent hr hD0 hD1 hx hp hA hl (K := 2) (δ := 1)
    one_pos (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => ?_), ?_⟩
  · have := Int.sub_one_lt_floor (x n)
    push_cast
    linarith
  · have := Int.floor_le (x n)
    push_cast
    linarith
  · refine tendsto_mul_zero_of_isEquivalent hr hD0 hD1 hx hp hl (δ := 1 / 2) (by norm_num) ?_
    filter_upwards [hθ] with n hn
    have := Int.floor_add_fract (x n)
    push_cast
    linarith

/-- Source's split, indices with `θ_n > 1/2` (source lines 2872–2877, 3366–3368):
`n p_{m_n} → ∞` and `n p_{m_n + 2} → 0`. -/
theorem half_lt_fract_thresholds (hA : 0 < A) {l : Filter ℕ} (hl : l ≤ atTop)
    (hθ : ∀ᶠ n in l, 1 / 2 < Int.fract (x n)) :
    Tendsto (fun n : ℕ => (n : ℝ) * p (⌊x n⌋).toNat) l atTop ∧
      Tendsto (fun n : ℕ => (n : ℝ) * p (⌊x n⌋ + 2).toNat) l (𝓝 0) := by
  refine ⟨tendsto_mul_atTop_of_isEquivalent hr hD0 hD1 hx hp hA hl (K := 1) (δ := 1 / 2)
    (by norm_num) (Eventually.of_forall fun n => ?_) ?_, ?_⟩
  · have := Int.sub_one_lt_floor (x n)
    linarith
  · filter_upwards [hθ] with n hn
    have := Int.floor_add_fract (x n)
    linarith
  · refine tendsto_mul_zero_of_isEquivalent hr hD0 hD1 hx hp hl (δ := 1) one_pos
      (Eventually.of_forall fun n => ?_)
    have := Int.floor_add_fract (x n)
    have := Int.fract_lt_one (x n)
    push_cast
    linarith

/-- Interior phase (source lines 2882–2895, 3375–3381): if `δ ≤ min(θ_n, 1 - θ_n)` eventually
along `l`, then `n p_{m_n} → ∞` and `n p_{m_n + 1} → 0` along `l`. -/
theorem interior_thresholds (hA : 0 < A) {l : Filter ℕ} (hl : l ≤ atTop) {δ : ℝ} (hδ : 0 < δ)
    (hθ : ∀ᶠ n in l, δ ≤ min (Int.fract (x n)) (1 - Int.fract (x n))) :
    Tendsto (fun n : ℕ => (n : ℝ) * p (⌊x n⌋).toNat) l atTop ∧
      Tendsto (fun n : ℕ => (n : ℝ) * p (⌊x n⌋ + 1).toNat) l (𝓝 0) := by
  refine ⟨tendsto_mul_atTop_of_isEquivalent hr hD0 hD1 hx hp hA hl (K := 1) hδ
    (Eventually.of_forall fun n => ?_) ?_, ?_⟩
  · have := Int.sub_one_lt_floor (x n)
    linarith
  · filter_upwards [hθ] with n hn
    exact floor_le_sub_of_le_min hn
  · refine tendsto_mul_zero_of_isEquivalent hr hD0 hD1 hx hp hl hδ ?_
    filter_upwards [hθ] with n hn
    exact add_le_floor_add_one_of_le_min hn

omit hp in
/-- Level sizes for all levels used: `r^{a_n}`, `r^{a_n + 2}`, `r^{m_n + j}` (`j ≤ 2`) are
`≤ n^δ` eventually, for every `δ > 0`. -/
theorem levels_le_rpow :
    (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, (r : ℝ) ^ (twoPointLow (x n)).toNat ≤ (n : ℝ) ^ δ) ∧
    (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, (r : ℝ) ^ (twoPointLow (x n) + 2).toNat ≤ (n : ℝ) ^ δ) ∧
    (∀ j : ℤ, j ≤ 2 → ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      (r : ℝ) ^ (⌊x n⌋ + j).toNat ≤ (n : ℝ) ^ δ) := by
  refine ⟨pow_level_le_rpow hr hD0 hD1 hx (K := 0) (Eventually.of_forall fun n => ?_),
    pow_level_le_rpow hr hD0 hD1 hx (K := 3 / 2)
      (Eventually.of_forall fun n => twoPointLow_add_two_le (x n)),
    fun j hj => pow_level_le_rpow hr hD0 hD1 hx (K := 2) (Eventually.of_forall fun n => ?_)⟩
  · have := twoPointLow_le (x n)
    linarith
  · have := Int.floor_le (x n)
    have hj' : (j : ℝ) ≤ 2 := by exact_mod_cast hj
    push_cast
    linarith

end Generic

/-! ### Complete `r`-ary trees (Theorem `thm:max_string`(ii)) -/

section Rary

variable {μ : ℝ}

/-- `log(1/μ^{1/(r-1)}) = log(1/μ)/(r - 1)`. -/
theorem log_one_div_rpow_inv (hμ0 : 0 < μ) :
    Real.log (1 / μ ^ (1 / ((r : ℝ) - 1))) = Real.log (1 / μ) / ((r : ℝ) - 1) := by
  rw [one_div (μ ^ _), Real.log_inv, Real.log_rpow hμ0, one_div μ, Real.log_inv]
  ring

/-- The centering `t_n^{**}` is the doubly logarithmic centering with `D = μ_r^{1/(r-1)}`. -/
theorem tStarStar_eq (hμ0 : 0 < μ) (n : ℕ) :
    tStarStar r μ n =
      Real.logb r (Real.log n) - Real.logb r (Real.log (1 / μ ^ (1 / ((r : ℝ) - 1)))) := by
  rw [log_one_div_rpow_inv hμ0, tStarStar]

/-- `π_k = μ_r^{(r^k - 1)/(r - 1)} = μ_r^{-1/(r-1)} (μ_r^{1/(r-1)})^{r^k}` (source line 2855,
with the natural-number exponent of `Patterns.Complete`). -/
theorem rary_pi_eq (hr : 2 ≤ r) (hμ0 : 0 < μ) (k : ℕ) :
    μ ^ ((r ^ k - 1) / (r - 1)) =
      μ ^ (-1 / ((r : ℝ) - 1)) * (μ ^ (1 / ((r : ℝ) - 1))) ^ (r ^ k) := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hne : (r : ℝ) - 1 ≠ 0 := by linarith
  have hcast : (((r ^ k - 1) / (r - 1) : ℕ) : ℝ) = ((r : ℝ) ^ k - 1) / ((r : ℝ) - 1) := by
    rw [← Nat.geomSum_eq hr, ← geom_sum_eq (by linarith : (r : ℝ) ≠ 1)]
    push_cast
    rfl
  rw [← Real.rpow_natCast μ, hcast, ← Real.rpow_natCast (μ ^ _), ← Real.rpow_mul hμ0.le,
    ← Real.rpow_add hμ0]
  congr 1
  push_cast
  field_simp
  ring

/-- Source lines 2853–2858, exact form: `n π_k = μ_r^{-1/(r-1)} n^{1 - r^{k - t_n^{**}}}` for
`n ≥ 2` and every level `k`; with `k = m_n + j` this is `μ_r^{-1/(r-1)} n^{1 - r^{j - θ_n}}`. -/
theorem rary_natCast_mul_eq (hr : 2 ≤ r) (hμ0 : 0 < μ) (hμ1 : μ < 1) {n : ℕ} (hn : 2 ≤ n)
    (k : ℕ) :
    (n : ℝ) * μ ^ ((r ^ k - 1) / (r - 1)) =
      μ ^ (-1 / ((r : ℝ) - 1)) * (n : ℝ) ^ (1 - (r : ℝ) ^ ((k : ℝ) - tStarStar r μ n)) := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hD0 : 0 < μ ^ (1 / ((r : ℝ) - 1)) := Real.rpow_pos_of_pos hμ0 _
  have hD1 : μ ^ (1 / ((r : ℝ) - 1)) < 1 :=
    Real.rpow_lt_one hμ0.le hμ1 (by apply div_pos one_pos; linarith)
  rw [rary_pi_eq hr hμ0, mul_left_comm,
    natCast_mul_pow_pow_eq hr hD0 hD1 (tStarStar_eq hμ0) hn]

/-- The same identity at the level `k = m_n + j ≥ 0`, `m_n = ⌊t_n^{**}⌋`, `θ_n = {t_n^{**}}`. -/
theorem rary_natCast_mul_level_eq (hr : 2 ≤ r) (hμ0 : 0 < μ) (hμ1 : μ < 1) {n : ℕ}
    (hn : 2 ≤ n) {j : ℤ} (hj : 0 ≤ ⌊tStarStar r μ n⌋ + j) :
    (n : ℝ) * μ ^ ((r ^ (⌊tStarStar r μ n⌋ + j).toNat - 1) / (r - 1)) =
      μ ^ (-1 / ((r : ℝ) - 1)) *
        (n : ℝ) ^ (1 - (r : ℝ) ^ ((j : ℝ) - Int.fract (tStarStar r μ n))) := by
  rw [rary_natCast_mul_eq hr hμ0 hμ1 hn, cast_toNat_of_nonneg hj, Int.fract]
  push_cast
  ring_nf

/-- `π_k = μ_r^{(r^k - 1)/(r - 1)}` is (trivially) asymptotically equivalent to its exact form
`A D^{r^k}`; this feeds the generic threshold lemmas. -/
theorem rary_isEquivalent (hr : 2 ≤ r) (hμ0 : 0 < μ) :
    (fun k => μ ^ ((r ^ k - 1) / (r - 1))) ~[atTop]
      fun k => μ ^ (-1 / ((r : ℝ) - 1)) * (μ ^ (1 / ((r : ℝ) - 1))) ^ (r ^ k) := by
  refine IsEquivalent.refl.congr_right (Eventually.of_forall fun k => ?_)
  exact rary_pi_eq hr hμ0 k

/-- Source lines 2855–2858 in the asymptotic form stated there: for every fixed `j ∈ ℤ`,
`n π_{m_n + j} ∼ μ_r^{-1/(r-1)} n^{1 - r^{j - θ_n}}` (with `π_k = μ_r^{(r^k-1)/(r-1)}`). -/
theorem rary_isEquivalent_level (hr : 2 ≤ r) (hμ0 : 0 < μ) (hμ1 : μ < 1) (j : ℤ) :
    (fun n : ℕ => (n : ℝ) * μ ^ ((r ^ (⌊tStarStar r μ n⌋ + j).toNat - 1) / (r - 1))) ~[atTop]
      fun n : ℕ => μ ^ (-1 / ((r : ℝ) - 1)) *
        (n : ℝ) ^ (1 - (r : ℝ) ^ ((j : ℝ) - Int.fract (tStarStar r μ n))) := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  exact isEquivalent_level hr (Real.rpow_pos_of_pos hμ0 _)
    (Real.rpow_lt_one hμ0.le hμ1 (by apply div_pos one_pos; linarith)) (tStarStar_eq hμ0)
    (rary_isEquivalent hr hμ0) j

/-- Theorem `thm:max_string`(ii), deterministic inputs: two-point levels (along any `l ≤ atTop`,
in particular admissible sizes), with `π_k = μ_r^{(r^k-1)/(r-1)}` and `t_n^{**}`. -/
theorem rary_twoPoint_thresholds (hr : 2 ≤ r) (hμ0 : 0 < μ) (hμ1 : μ < 1) {l : Filter ℕ}
    (hl : l ≤ atTop) :
    Tendsto (fun n : ℕ => (n : ℝ) *
        μ ^ ((r ^ (twoPointLow (tStarStar r μ n)).toNat - 1) / (r - 1))) l atTop ∧
      Tendsto (fun n : ℕ => (n : ℝ) *
        μ ^ ((r ^ (twoPointLow (tStarStar r μ n) + 2).toNat - 1) / (r - 1))) l (𝓝 0) := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  exact twoPoint_thresholds hr (Real.rpow_pos_of_pos hμ0 _)
    (Real.rpow_lt_one hμ0.le hμ1 (by apply div_pos one_pos; linarith)) (tStarStar_eq hμ0)
    (rary_isEquivalent hr hμ0) (Real.rpow_pos_of_pos hμ0 _) hl

/-- Theorem `thm:max_string`(ii), deterministic inputs: interior phase. -/
theorem rary_interior_thresholds (hr : 2 ≤ r) (hμ0 : 0 < μ) (hμ1 : μ < 1) {l : Filter ℕ}
    (hl : l ≤ atTop) {δ : ℝ} (hδ : 0 < δ)
    (hθ : ∀ᶠ n in l, δ ≤ min (Int.fract (tStarStar r μ n)) (1 - Int.fract (tStarStar r μ n))) :
    Tendsto (fun n : ℕ => (n : ℝ) *
        μ ^ ((r ^ (⌊tStarStar r μ n⌋).toNat - 1) / (r - 1))) l atTop ∧
      Tendsto (fun n : ℕ => (n : ℝ) *
        μ ^ ((r ^ (⌊tStarStar r μ n⌋ + 1).toNat - 1) / (r - 1))) l (𝓝 0) := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  exact interior_thresholds hr (Real.rpow_pos_of_pos hμ0 _)
    (Real.rpow_lt_one hμ0.le hμ1 (by apply div_pos one_pos; linarith)) (tStarStar_eq hμ0)
    (rary_isEquivalent hr hμ0) (Real.rpow_pos_of_pos hμ0 _) hl hδ hθ

/-- Theorem `thm:max_string`(ii), level sizes: `r^{a_n}`, `r^{a_n+2}`, `r^{m_n + j}` (`j ≤ 2`)
are `n^{o(1)}`. -/
theorem rary_levels_le_rpow (hr : 2 ≤ r) (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      (r : ℝ) ^ (twoPointLow (tStarStar r μ n)).toNat ≤ (n : ℝ) ^ δ) ∧
    (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      (r : ℝ) ^ (twoPointLow (tStarStar r μ n) + 2).toNat ≤ (n : ℝ) ^ δ) ∧
    (∀ j : ℤ, j ≤ 2 → ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      (r : ℝ) ^ (⌊tStarStar r μ n⌋ + j).toNat ≤ (n : ℝ) ^ δ) := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  exact levels_le_rpow hr (Real.rpow_pos_of_pos hμ0 _)
    (Real.rpow_lt_one hμ0.le hμ1 (by apply div_pos one_pos; linarith)) (tStarStar_eq hμ0)

end Rary

end ExtremesAnalysis
end PoissonDeclumping
