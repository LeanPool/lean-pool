/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.LeafHeight.Asymptotics

/-!
# Consequences of the root leaf-height asymptotics

* Remark after Lemma `lem:ell_asymp` (source lines 3007–3025, inventory R7.2): the exact
  root leaf-height probabilities `ℓ_k = π_k - π_{k+1}` satisfy `π_{k+1}/π_k → μ_1`,
  `ℓ_k ∼ (1 - μ_1) C_μ μ_1^k` if `μ_1 > 0`, and `ℓ_k ∼ π_k ∼ μ_κ^{-1/(κ-1)} D_μ^{κ^k}` if
  `μ_1 = 0`.
* Inventory U13 (source lines 3473–3491): if `μ_1 = 0` and `n π_{k_n}` is bounded then
  `n π_{k_n + 1} → 0`, i.e. `n |π_{k_n} - ℓ_{k_n}| → 0`.
* Inventory U09 (source lines 3031–3042, 3274–3296): `c = E[k_∅ 1{k_∅ ≥ κ+1}] = 1 - κ μ_κ ≥ 0`;
  `c = 0` forces `μ_1 = 0`, `supp μ ⊆ {0, κ}` and `μ_κ = 1/κ`; then
  `π_k = μ_κ^{(κ^k - 1)/(κ - 1)}`, `D_μ = μ_κ^{1/(κ-1)}`,
  `log(1/D_μ) = log(1/μ_κ)/(κ - 1)`, and the centerings `k_n^{**}` and `t_n^{**}` agree.
-/

@[expose] public section

open Filter Topology Asymptotics
open scoped ENNReal

namespace PoissonDeclumping
namespace LeafHeight

variable {μ : PMF ℕ}

/-! ### Consecutive ratios and `ℓ_k` (Remark R7.2) -/

section Ratio

variable (hc : IsCritical μ) (h1 : μ 1 ≠ 1)
include hc h1

/-- `μ_1 π_k ≤ π_{k+1} ≤ μ_1 π_k + π_k^2`. -/
theorem piSeq_succ_bounds (k : ℕ) :
    mass μ 1 * piSeq μ k ≤ piSeq μ (k + 1) ∧
      piSeq μ (k + 1) ≤ mass μ 1 * piSeq μ k + piSeq μ k ^ 2 := by
  have hx := piSeq_pos hc h1 k
  have hx1 := piSeq_le_one hc h1 k
  rw [piSeq_succ]
  refine ⟨by simpa using mass_mul_pow_le_g (μ := μ) le_rfl hx.le hx1, ?_⟩
  simpa using g_le_mass_mul_pow_add (μ := μ) le_rfl (fun j hj hj1 => by omega) hx.le hx1

/-- `π_{k+1} / π_k → μ_1` (in both cases of the remark). -/
theorem tendsto_piSeq_succ_div :
    Tendsto (fun k => piSeq μ (k + 1) / piSeq μ k) atTop (𝓝 (mass μ 1)) := by
  have hup : Tendsto (fun k => mass μ 1 + piSeq μ k) atTop (𝓝 (mass μ 1)) := by
    simpa using (tendsto_piSeq_zero hc h1).const_add (mass μ 1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun k => ?_)
    (fun k => ?_)
  · have hx := piSeq_pos hc h1 k
    rw [le_div_iff₀ hx]
    exact (piSeq_succ_bounds hc h1 k).1
  · have hx := piSeq_pos hc h1 k
    rw [div_le_iff₀ hx]
    nlinarith [(piSeq_succ_bounds hc h1 k).2]

/-- `ℓ_k / π_k → 1 - μ_1`. -/
theorem tendsto_ellSeq_div_piSeq :
    Tendsto (fun k => ellSeq μ k / piSeq μ k) atTop (𝓝 (1 - mass μ 1)) := by
  refine ((tendsto_piSeq_succ_div hc h1).const_sub 1).congr fun k => ?_
  have hx := (piSeq_pos hc h1 k).ne'
  simp only [ellSeq]
  field_simp

/-- `ℓ_k ∼ (1 - μ_1) π_k`. -/
theorem ellSeq_isEquivalent_mul_piSeq :
    ellSeq μ ~[atTop] fun k => (1 - mass μ 1) * piSeq μ k := by
  have hq : 1 - mass μ 1 ≠ 0 := by linarith [mass_one_lt_one h1]
  apply isEquivalent_of_tendsto_one
  have h := (tendsto_ellSeq_div_piSeq hc h1).div_const (1 - mass μ 1)
  rw [div_self hq] at h
  refine h.congr fun k => ?_
  have hx := (piSeq_pos hc h1 k).ne'
  simp only [Pi.div_apply]
  field_simp

/-- Remark R7.2, case `μ_1 > 0`: `ℓ_k ∼ (1 - μ_1) C_μ μ_1^k`. -/
theorem ellSeq_isEquivalent_of_pos (hpos : 0 < μ 1) :
    ellSeq μ ~[atTop] fun k => (1 - mass μ 1) * leafC μ * mass μ 1 ^ k := by
  have h := (ellSeq_isEquivalent_mul_piSeq hc h1).trans
    ((IsEquivalent.refl (u := fun _ : ℕ => 1 - mass μ 1)).mul
      (piSeq_isEquivalent_leafC hc h1 hpos))
  refine h.congr_right (Eventually.of_forall fun k => ?_)
  simp only [Pi.mul_apply]
  ring

/-- If `μ_1 = 0`, then `π_{k+1} ≤ π_k^2`. -/
theorem piSeq_succ_le_sq (h0 : μ 1 = 0) (k : ℕ) : piSeq μ (k + 1) ≤ piSeq μ k ^ 2 := by
  have h := (piSeq_succ_bounds hc h1 k).2
  rwa [show mass μ 1 = 0 by simp [mass, h0], zero_mul, zero_add] at h

/-- Remark R7.2, case `μ_1 = 0`: `π_{k+1} / π_k → 0`. -/
theorem tendsto_piSeq_succ_div_zero (h0 : μ 1 = 0) :
    Tendsto (fun k => piSeq μ (k + 1) / piSeq μ k) atTop (𝓝 0) := by
  have h := tendsto_piSeq_succ_div hc h1
  rwa [show mass μ 1 = 0 by simp [mass, h0]] at h

/-- Remark R7.2, case `μ_1 = 0`: `ℓ_k ∼ π_k`. -/
theorem ellSeq_isEquivalent_piSeq (h0 : μ 1 = 0) : ellSeq μ ~[atTop] piSeq μ := by
  have h := ellSeq_isEquivalent_mul_piSeq hc h1
  simpa [show mass μ 1 = 0 by simp [mass, h0]] using h

/-- Remark R7.2, case `μ_1 = 0`: `ℓ_k ∼ μ_κ^{-1/(κ-1)} D_μ^{κ^k}`. -/
theorem ellSeq_isEquivalent_of_zero (h0 : μ 1 = 0) :
    ellSeq μ ~[atTop] fun k =>
      mass μ (kappa μ) ^ (-1 / ((kappa μ : ℝ) - 1)) * leafD μ ^ (kappa μ ^ k) :=
  (ellSeq_isEquivalent_piSeq hc h1 h0).trans (piSeq_isEquivalent_leafD hc h1 h0)

/-! ### Interchangeability of the Poisson parameters (U13) -/

/-- U13, general form: if `μ_1 = 0`, `n_i → ∞` and `n_i π_{k_i}` is bounded above, then
`n_i π_{k_i + 1} → 0`. -/
theorem tendsto_mul_piSeq_succ_of_bounded (h0 : μ 1 = 0) {ι : Type*} {l : Filter ι}
    {n : ι → ℝ} {k : ι → ℕ} (hn : Tendsto n l atTop)
    (hbd : IsBoundedUnder (· ≤ ·) l fun i => n i * piSeq μ (k i)) :
    Tendsto (fun i => n i * piSeq μ (k i + 1)) l (𝓝 0) := by
  obtain ⟨M, hM⟩ := hbd
  rw [eventually_map] at hM
  have hnpos : ∀ᶠ i in l, 0 < n i := hn.eventually_gt_atTop 0
  refine squeeze_zero' (g := fun i => M ^ 2 / n i) ?_ ?_
    (tendsto_const_nhds.div_atTop hn)
  · filter_upwards [hnpos] with i hi
    exact mul_nonneg hi.le (piSeq_pos hc h1 _).le
  · filter_upwards [hnpos, hM] with i hi hMi
    have hx := piSeq_pos hc h1 (k i)
    have hsq := piSeq_succ_le_sq hc h1 h0 (k i)
    have hnx : 0 ≤ n i * piSeq μ (k i) := mul_nonneg hi.le hx.le
    have hsq' : (n i * piSeq μ (k i)) ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hnx hMi 2
    rw [le_div_iff₀ hi]
    calc n i * piSeq μ (k i + 1) * n i ≤ n i * piSeq μ (k i) ^ 2 * n i := by
          gcongr
      _ = (n i * piSeq μ (k i)) ^ 2 := by ring
      _ ≤ M ^ 2 := hsq'

/-- U13 as used in the source: if `μ_1 = 0` and `(n π_{k_n})_n` is bounded, then
`n π_{k_n+1} → 0` and `n |π_{k_n} - ℓ_{k_n}| → 0`. -/
theorem tendsto_natCast_mul_piSeq_succ (h0 : μ 1 = 0) {k : ℕ → ℕ}
    (hbd : IsBoundedUnder (· ≤ ·) atTop fun n : ℕ => (n : ℝ) * piSeq μ (k n)) :
    Tendsto (fun n : ℕ => (n : ℝ) * piSeq μ (k n + 1)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (n : ℝ) * |piSeq μ (k n) - ellSeq μ (k n)|) atTop (𝓝 0) := by
  have h := tendsto_mul_piSeq_succ_of_bounded hc h1 h0 tendsto_natCast_atTop_atTop hbd
  refine ⟨h, h.congr fun n => ?_⟩
  simp only [ellSeq, sub_sub_cancel, abs_of_pos (piSeq_pos hc h1 _)]

/-- `μ_0 π_k ≤ ℓ_k`, so boundedness of `n ℓ_{k_n}` and of `n π_{k_n}` are equivalent. -/
theorem mass_zero_mul_piSeq_le_ellSeq (k : ℕ) : mass μ 0 * piSeq μ k ≤ ellSeq μ k := by
  have := piSeq_succ_le_mul hc h1 k
  simp only [ellSeq]
  linarith

/-- U13 with the bounded-mean hypothesis stated for `n ℓ_{k_n}` instead of `n π_{k_n}`. -/
theorem tendsto_natCast_mul_piSeq_succ_of_ell (h0 : μ 1 = 0) {k : ℕ → ℕ}
    (hbd : IsBoundedUnder (· ≤ ·) atTop fun n : ℕ => (n : ℝ) * ellSeq μ (k n)) :
    Tendsto (fun n : ℕ => (n : ℝ) * piSeq μ (k n + 1)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (n : ℝ) * |piSeq μ (k n) - ellSeq μ (k n)|) atTop (𝓝 0) := by
  have hm := mass_zero_pos hc h1
  refine tendsto_natCast_mul_piSeq_succ hc h1 h0 ?_
  obtain ⟨M, hM⟩ := hbd
  rw [eventually_map] at hM
  refine ⟨M / mass μ 0, ?_⟩
  rw [eventually_map]
  filter_upwards [hM] with n hn
  rw [le_div_iff₀ hm]
  have := mul_le_mul_of_nonneg_left (mass_zero_mul_piSeq_le_ellSeq hc h1 (k n))
    (Nat.cast_nonneg n)
  nlinarith

end Ratio

/-! ### The constant `c = 1 - κ μ_κ` (U09) -/

variable (μ) in
/-- `c = 1 - κ μ_κ` (source line 3031). -/
noncomputable def cConst : ℝ := 1 - (kappa μ : ℝ) * mass μ (kappa μ)

section CConst

variable (hc : IsCritical μ) (h1 : μ 1 ≠ 1)
include hc h1

omit h1 in
/-- `c = E[k_∅ 1{k_∅ ≥ κ + 1}] = ∑_{j ≥ κ + 1} j μ_j` (source line 3031). -/
theorem hasSum_cConst :
    HasSum (fun j : ℕ => if kappa μ + 1 ≤ j then (j : ℝ) * mass μ j else 0) (cConst μ) := by
  have h := (hasSum_mean hc).sub
    (hasSum_ite_eq (kappa μ) ((kappa μ : ℝ) * mass μ (kappa μ)))
  refine h.congr_fun fun j => ?_
  rcases lt_trichotomy j (kappa μ) with hj | rfl | hj
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp
    · simp [mass_eq_zero_of_lt_kappa hj0 hj]
  · simp
  · rw [ite_eq_left (by omega), ite_eq_right (by omega), sub_zero]

omit h1 in
/-- U09: `c ≥ 0`. -/
theorem cConst_nonneg : 0 ≤ cConst μ :=
  hasSum_le (fun j => by
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg j) (mass_nonneg j)
    · exact le_rfl) hasSum_zero (hasSum_cConst hc)

omit hc in
/-- If `μ_1 > 0` then `κ = 1` and `c = 1 - μ_1 > 0` (source line 3299). -/
theorem cConst_pos_of_pos (hpos : 0 < μ 1) : 0 < cConst μ := by
  simp only [cConst, kappa_eq_one hpos, Nat.cast_one, one_mul, sub_pos]
  exact mass_one_lt_one h1

omit h1 in
/-- U09: if `c = 0` then `μ_j = 0` for every `j ∉ {0, κ}`. -/
theorem mass_eq_zero_of_cConst_eq_zero (hc0 : cConst μ = 0) {j : ℕ} (hj0 : j ≠ 0)
    (hjk : j ≠ kappa μ) : mass μ j = 0 := by
  rcases lt_or_gt_of_ne hjk with hj | hj
  · exact mass_eq_zero_of_lt_kappa (by omega) hj
  · have h := hasSum_cConst hc
    rw [hc0, hasSum_zero_iff_of_nonneg (fun i => by
      split_ifs
      · exact mul_nonneg (Nat.cast_nonneg i) (mass_nonneg i)
      · exact le_rfl)] at h
    have hj' := congrFun h j
    simp only [Pi.zero_apply] at hj'
    rw [ite_eq_left (by omega)] at hj'
    rcases mul_eq_zero.mp hj' with h' | h'
    · exact absurd h' (by exact_mod_cast hj0)
    · exact h'

omit h1 in
/-- U09: if `c = 0` then the support of `μ` is contained in `{0, κ}`. -/
theorem support_subset_of_cConst_eq_zero (hc0 : cConst μ = 0) :
    μ.support ⊆ {0, kappa μ} := by
  intro j hj
  by_contra hj'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hj'
  have := mass_eq_zero_of_cConst_eq_zero hc hc0 hj'.1 hj'.2
  rw [mass, ENNReal.toReal_eq_zero_iff] at this
  rcases this with h | h
  · exact (μ.mem_support_iff j).mp hj h
  · exact μ.apply_ne_top j h

/-- U09: if `c = 0` then `μ_κ = 1/κ`. -/
theorem mass_kappa_of_cConst_eq_zero (hc0 : cConst μ = 0) :
    mass μ (kappa μ) = 1 / (kappa μ : ℝ) := by
  have hk : (1 : ℝ) ≤ kappa μ := by exact_mod_cast one_le_kappa hc h1
  rw [eq_div_iff (by linarith)]
  simp only [cConst] at hc0
  linarith

omit h1 in
/-- U09: `c = 0` exactly when `μ` is supported on `{0, κ}` (source lines 3040–3041). -/
theorem cConst_eq_zero_iff : cConst μ = 0 ↔ μ.support ⊆ {0, kappa μ} := by
  refine ⟨support_subset_of_cConst_eq_zero hc, fun hsupp => ?_⟩
  refine (hasSum_cConst hc).unique ?_
  convert hasSum_zero with j
  split_ifs with hj
  · have : μ j = 0 := by
      by_contra hne
      have := hsupp ((μ.mem_support_iff j).mpr hne)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      omega
    simp [mass, this]
  · rfl

/-- U09: if `c = 0` then `κ ≥ 2` and `μ_1 = 0` (the case `c = 0` is a case of `μ_1 = 0`). -/
theorem two_le_kappa_of_cConst_eq_zero (hc0 : cConst μ = 0) :
    2 ≤ kappa μ ∧ μ 1 = 0 := by
  have hk1 := one_le_kappa hc h1
  have h2 : 2 ≤ kappa μ := by
    by_contra! h
    have hk : kappa μ = 1 := by omega
    have hm := mass_kappa_of_cConst_eq_zero hc h1 hc0
    rw [hk, Nat.cast_one, div_one] at hm
    apply h1
    have := μ.coe_le_one 1
    rw [mass] at hm
    rw [← ENNReal.ofReal_toReal (μ.apply_ne_top 1), hm, ENNReal.ofReal_one]
  refine ⟨h2, ?_⟩
  have := mass_eq_zero_of_lt_kappa (μ := μ) le_rfl (by omega : 1 < kappa μ)
  rw [mass, ENNReal.toReal_eq_zero_iff] at this
  exact this.resolve_right (μ.apply_ne_top 1)

/-- In the two-point case `c = 0`: `g(x) = μ_κ x^κ`. -/
theorem g_eq_of_cConst_eq_zero (hc0 : cConst μ = 0) (x : ℝ) :
    g μ x = mass μ (kappa μ) * x ^ kappa μ := by
  have hk1 := one_le_kappa hc h1
  rw [g, tsum_eq_single (kappa μ - 1)]
  · rw [Nat.sub_add_cancel hk1]
  · intro j hj
    rw [mass_eq_zero_of_cConst_eq_zero hc hc0 (by omega) (by omega), zero_mul]

/-- In the two-point case `c = 0`: `π_k = μ_κ^{1 + κ + ⋯ + κ^{k-1}}`. -/
theorem piSeq_eq_pow_of_cConst_eq_zero (hc0 : cConst μ = 0) (k : ℕ) :
    piSeq μ k = mass μ (kappa μ) ^ (∑ i ∈ Finset.range k, kappa μ ^ i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [piSeq_succ, g_eq_of_cConst_eq_zero hc h1 hc0, ih, ← pow_mul, ← pow_succ',
      Finset.sum_range_succ', pow_zero, Finset.sum_mul]
    congr 2

/-- In the two-point case `c = 0` (source lines 3283–3287):
`π_k = μ_κ^{(κ^k - 1)/(κ - 1)} = μ_κ^{-1/(κ-1)} (μ_κ^{1/(κ-1)})^{κ^k}`. -/
theorem piSeq_eq_rpow_of_cConst_eq_zero (hc0 : cConst μ = 0) (k : ℕ) :
    piSeq μ k = mass μ (kappa μ) ^ (((kappa μ : ℝ) ^ k - 1) / ((kappa μ : ℝ) - 1)) ∧
      piSeq μ k = mass μ (kappa μ) ^ (-1 / ((kappa μ : ℝ) - 1)) *
        (mass μ (kappa μ) ^ (1 / ((kappa μ : ℝ) - 1))) ^ (kappa μ ^ k) := by
  have ha := mass_kappa_pos hc h1
  have h2 : (2 : ℝ) ≤ kappa μ := by exact_mod_cast (two_le_kappa_of_cConst_eq_zero hc h1 hc0).1
  have hne : (kappa μ : ℝ) ≠ 1 := by linarith
  have hne' : (kappa μ : ℝ) - 1 ≠ 0 := by linarith
  have h₁ : piSeq μ k =
      mass μ (kappa μ) ^ (((kappa μ : ℝ) ^ k - 1) / ((kappa μ : ℝ) - 1)) := by
    rw [piSeq_eq_pow_of_cConst_eq_zero hc h1 hc0, ← geom_sum_eq hne, ← Real.rpow_natCast]
    push_cast
    rfl
  refine ⟨h₁, ?_⟩
  rw [h₁, ← Real.rpow_natCast (mass μ (kappa μ) ^ (1 / ((kappa μ : ℝ) - 1))),
    ← Real.rpow_mul ha.le, ← Real.rpow_add ha]
  congr 1
  push_cast
  field_simp
  ring

/-- In the two-point case `c = 0`: `D_μ = μ_κ^{1/(κ-1)}` (source line 3288). -/
theorem leafD_of_cConst_eq_zero (hc0 : cConst μ = 0) :
    leafD μ = mass μ (kappa μ) ^ (1 / ((kappa μ : ℝ) - 1)) := by
  obtain ⟨h2n, h0⟩ := two_le_kappa_of_cConst_eq_zero hc h1 hc0
  have ha := mass_kappa_pos hc h1
  have herr : ∀ k, errSeq μ k = 0 := fun k => by
    have hx := piSeq_pos hc h1 k
    simp only [errSeq]
    rw [piSeq_succ, g_eq_of_cConst_eq_zero hc h1 hc0, Real.log_mul ha.ne' (pow_pos hx _).ne',
      Real.log_pow]
    ring
  have hv : ∀ k, vSeq μ k = betaC μ := fun k => by
    induction k with
    | zero => simp [vSeq]
    | succ k ih => rw [vSeq_succ h2n, ih, herr, zero_div, add_zero]
  have hlogD : logD μ = betaC μ := by
    simp only [logD, hv, ciSup_const]
  rw [leafD_eq_exp_logD hc h1 h0, hlogD, Real.rpow_def_of_pos ha, betaC]
  ring_nf

/-- In the two-point case `c = 0`: `log(1/D_μ) = log(1/μ_κ)/(κ - 1)` (source line 3290). -/
theorem log_inv_leafD_of_cConst_eq_zero (hc0 : cConst μ = 0) :
    Real.log (1 / leafD μ) = Real.log (1 / mass μ (kappa μ)) / ((kappa μ : ℝ) - 1) := by
  have ha := mass_kappa_pos hc h1
  rw [leafD_of_cConst_eq_zero hc h1 hc0, Real.log_div one_ne_zero (Real.rpow_pos_of_pos ha _).ne',
    Real.log_one, Real.log_rpow ha, Real.log_div one_ne_zero ha.ne', Real.log_one]
  ring

/-- In the two-point case `c = 0`, the centering
`k_n^{**} = log_κ log n - log_κ log(1/D_μ)` of Theorem `thm:max_lh`(ii) equals the centering
`t_n^{**} = log_r log n - log_r (log(1/μ_r)/(r - 1))` of Theorem `thm:max_string`(ii) with
`r = κ` (source lines 3291–3293). -/
theorem centering_eq_of_cConst_eq_zero (hc0 : cConst μ = 0) (n : ℕ) :
    Real.logb (kappa μ) (Real.log n) - Real.logb (kappa μ) (Real.log (1 / leafD μ)) =
      Real.logb (kappa μ) (Real.log n) -
        Real.logb (kappa μ) (Real.log (1 / mass μ (kappa μ)) / ((kappa μ : ℝ) - 1)) := by
  rw [log_inv_leafD_of_cConst_eq_zero hc h1 hc0]

end CConst

end LeafHeight
end PoissonDeclumping
