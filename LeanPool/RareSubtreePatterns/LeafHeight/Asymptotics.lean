/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.LeafHeight.Recursion

/-!
# Asymptotics of the root leaf-height tail

Lemma `lem:ell_asymp` of the paper (source lines 2937–3005) and the identification of the
constants `C_μ`, `D_μ` as limits (source lines 562–586, inventory U03), for the analytic
sequence `π_0 = 1`, `π_{k+1} = g(π_k)` of `PoissonDeclumping.LeafHeight.Recursion`.

* If `μ_1 > 0`: `π_k / μ_1^k` is nondecreasing and bounded, so it converges to
  `C_μ = lim π_k / μ_1^k ≥ 1`, and `π_k ∼ C_μ μ_1^k`.
* If `μ_1 = 0`, let `κ = min{j ≥ 2 : μ_j > 0}` and `a = μ_κ`. With
  `β = log a / (κ - 1)`, `v_k = (log π_k + β) / κ^k` is nondecreasing and
  `u_k = v_k + π_k / (a (κ - 1) κ^k)` is nonincreasing; both converge to `log D_μ < 0`, and
  `0 ≤ κ^k log D_μ - (log π_k + β) ≤ π_k / (a (κ - 1)) → 0`. Hence
  `π_k ∼ μ_κ^{-1/(κ-1)} D_μ^{κ^k}` (an asymptotic equivalent, not just a logarithmic
  estimate), and `D_μ = lim π_k^{1/κ^k} ∈ (0, 1)`.

The proof follows the paper's route; in the second case the paper bounds the tail error using
the superexponential bound `π_k ≤ A ξ^{κ^k}`, while we use the monotone sandwich
`v_k ≤ log D_μ ≤ u_k`, which only needs `π_k ↓ 0`.
-/

@[expose] public section

open Filter Topology Asymptotics
open scoped ENNReal

namespace PoissonDeclumping
namespace LeafHeight

variable {μ : PMF ℕ}

/-- `∑_{j < k} π_j ≤ 1/μ_0` (geometric domination). -/
theorem sum_piSeq_le (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (k : ℕ) :
    ∑ j ∈ Finset.range k, piSeq μ j ≤ (mass μ 0)⁻¹ := by
  have h0 := mass_zero_pos hc h1
  have hr0 : 0 ≤ 1 - mass μ 0 := by linarith [mass_le_one (μ := μ) 0]
  have hr1 : 1 - mass μ 0 < 1 := by linarith
  calc ∑ j ∈ Finset.range k, piSeq μ j ≤ ∑ j ∈ Finset.range k, (1 - mass μ 0) ^ j :=
        Finset.sum_le_sum fun j _ => piSeq_le_pow hc h1 j
    _ ≤ ∑' j, (1 - mass μ 0) ^ j :=
        (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (fun j _ => pow_nonneg hr0 j)
    _ = (mass μ 0)⁻¹ := by rw [tsum_geometric_of_lt_one hr0 hr1, sub_sub_cancel]

theorem mass_one_lt_one (h1 : μ 1 ≠ 1) : mass μ 1 < 1 := by
  have : μ 1 < 1 := lt_of_le_of_ne (μ.coe_le_one 1) h1
  exact ENNReal.toReal_lt_of_lt_ofReal (by simpa using this)

/-! ### Case `μ_1 > 0` -/

section Unary

variable (μ) in
/-- `C_μ = lim_{k → ∞} π_k / μ_1^k` (source lines 576–579). -/
noncomputable def leafC : ℝ := limUnder atTop (fun k => piSeq μ k / mass μ 1 ^ k)

variable (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (hpos : 0 < μ 1)
include hc h1 hpos

/-- For `μ_1 > 0`: `μ_1 x ≤ g(x) ≤ μ_1 x + x^2` on `[0, 1]`. -/
theorem g_bounds_of_pos {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    mass μ 1 * x ≤ g μ x ∧ g μ x ≤ mass μ 1 * x + x ^ 2 := by
  have h := g_bounds hc h1 hx0 hx1
  rw [kappa_eq_one hpos] at h
  simpa using h

theorem ratio_le_ratio_succ (k : ℕ) :
    piSeq μ k / mass μ 1 ^ k ≤ piSeq μ (k + 1) / mass μ 1 ^ (k + 1) := by
  have hq := (mass_pos_iff 1).mpr hpos
  have hx := piSeq_pos hc h1 k
  have hb := (g_bounds_of_pos hc h1 hpos hx.le (piSeq_le_one hc h1 k)).1
  rw [piSeq_succ, div_le_div_iff₀ (pow_pos hq _) (pow_pos hq _), pow_succ]
  calc piSeq μ k * (mass μ 1 ^ k * mass μ 1) = (mass μ 1 * piSeq μ k) * mass μ 1 ^ k := by
        ring
    _ ≤ g μ (piSeq μ k) * mass μ 1 ^ k := mul_le_mul_of_nonneg_right hb (pow_nonneg hq.le _)

theorem monotone_ratio : Monotone (fun k => piSeq μ k / mass μ 1 ^ k) :=
  monotone_nat_of_le_succ (ratio_le_ratio_succ hc h1 hpos)

theorem ratio_succ_le (k : ℕ) :
    piSeq μ (k + 1) / mass μ 1 ^ (k + 1) ≤
      piSeq μ k / mass μ 1 ^ k * (1 + piSeq μ k / mass μ 1) := by
  have hq := (mass_pos_iff 1).mpr hpos
  have hx := piSeq_pos hc h1 k
  have hb := (g_bounds_of_pos hc h1 hpos hx.le (piSeq_le_one hc h1 k)).2
  rw [piSeq_succ]
  calc g μ (piSeq μ k) / mass μ 1 ^ (k + 1)
      ≤ (mass μ 1 * piSeq μ k + piSeq μ k ^ 2) / mass μ 1 ^ (k + 1) :=
        div_le_div_of_nonneg_right hb (pow_nonneg hq.le _)
    _ = piSeq μ k / mass μ 1 ^ k * (1 + piSeq μ k / mass μ 1) := by
        field_simp
        ring

theorem ratio_le_exp (k : ℕ) :
    piSeq μ k / mass μ 1 ^ k ≤
      Real.exp ((∑ j ∈ Finset.range k, piSeq μ j) / mass μ 1) := by
  have hq := (mass_pos_iff 1).mpr hpos
  induction k with
  | zero => simp
  | succ k ih =>
    have hx := piSeq_pos hc h1 k
    calc piSeq μ (k + 1) / mass μ 1 ^ (k + 1)
        ≤ piSeq μ k / mass μ 1 ^ k * (1 + piSeq μ k / mass μ 1) := ratio_succ_le hc h1 hpos k
      _ ≤ Real.exp ((∑ j ∈ Finset.range k, piSeq μ j) / mass μ 1) *
            Real.exp (piSeq μ k / mass μ 1) :=
          mul_le_mul ih (by linarith [Real.add_one_le_exp (piSeq μ k / mass μ 1)])
            (add_nonneg zero_le_one (div_nonneg hx.le hq.le)) (Real.exp_pos _).le
      _ = Real.exp ((∑ j ∈ Finset.range (k + 1), piSeq μ j) / mass μ 1) := by
          rw [← Real.exp_add, Finset.sum_range_succ, add_div]

theorem bddAbove_ratio : BddAbove (Set.range fun k => piSeq μ k / mass μ 1 ^ k) := by
  have hq := (mass_pos_iff 1).mpr hpos
  refine ⟨Real.exp ((mass μ 0)⁻¹ / mass μ 1), ?_⟩
  rintro _ ⟨k, rfl⟩
  exact (ratio_le_exp hc h1 hpos k).trans
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (sum_piSeq_le hc h1 k) hq.le))

/-- `π_k / μ_1^k → C_μ` (source lines 576–579 and the proof of Lemma `lem:ell_asymp`(i)). -/
theorem tendsto_ratio_leafC :
    Tendsto (fun k => piSeq μ k / mass μ 1 ^ k) atTop (𝓝 (leafC μ)) := by
  have ht := tendsto_atTop_ciSup (monotone_ratio hc h1 hpos) (bddAbove_ratio hc h1 hpos)
  rw [leafC, ht.limUnder_eq]
  exact ht

theorem one_le_leafC : 1 ≤ leafC μ := by
  have := (monotone_ratio hc h1 hpos).ge_of_tendsto (tendsto_ratio_leafC hc h1 hpos) 0
  simpa using this

theorem leafC_pos : 0 < leafC μ := lt_of_lt_of_le one_pos (one_le_leafC hc h1 hpos)

/-- Lemma `lem:ell_asymp`(i), with the explicit constant: `π_k ∼ C_μ μ_1^k`. -/
theorem piSeq_isEquivalent_leafC :
    piSeq μ ~[atTop] fun k => leafC μ * mass μ 1 ^ k := by
  have hq := (mass_pos_iff 1).mpr hpos
  have hC := (leafC_pos hc h1 hpos).ne'
  apply isEquivalent_of_tendsto_one
  have h := (tendsto_ratio_leafC hc h1 hpos).div_const (leafC μ)
  rw [div_self hC] at h
  refine h.congr fun k => ?_
  have := (pow_pos hq k).ne'
  simp only [Pi.div_apply]
  field_simp

/-- Lemma `lem:ell_asymp`(i): if `μ_1 > 0` there is `C_μ > 0` with `π_k ∼ C_μ μ_1^k`. -/
theorem lem_ell_asymp_i :
    ∃ C : ℝ, 0 < C ∧ piSeq μ ~[atTop] fun k => C * mass μ 1 ^ k :=
  ⟨leafC μ, leafC_pos hc h1 hpos, piSeq_isEquivalent_leafC hc h1 hpos⟩

end Unary

/-! ### Case `μ_1 = 0` -/

section Superexp

variable (μ)

/-- `β = log μ_κ / (κ - 1)`, so that `μ_κ^{-1/(κ-1)} = exp (-β)`. -/
noncomputable def betaC : ℝ := Real.log (mass μ (kappa μ)) / ((kappa μ : ℝ) - 1)

/-- `v_k = (log π_k + β) / κ^k` (`κ^{-k} log y_k` in the paper, with `y_k = μ_κ^{1/(κ-1)} π_k`). -/
noncomputable def vSeq (k : ℕ) : ℝ :=
  (Real.log (piSeq μ k) + betaC μ) / (kappa μ : ℝ) ^ k

/-- The error `log π_{k+1} - κ log π_k - log μ_κ` (`log (1 + ε(π_k))` in the paper). -/
noncomputable def errSeq (k : ℕ) : ℝ :=
  Real.log (piSeq μ (k + 1)) - (kappa μ : ℝ) * Real.log (piSeq μ k) -
    Real.log (mass μ (kappa μ))

/-- The upper companion `u_k = v_k + π_k / (μ_κ (κ - 1) κ^k)` of `v_k`. -/
noncomputable def uSeq (k : ℕ) : ℝ :=
  vSeq μ k + piSeq μ k / (mass μ (kappa μ) * ((kappa μ : ℝ) - 1) * (kappa μ : ℝ) ^ k)

/-- `log D_μ = lim v_k = sup_k v_k`. -/
noncomputable def logD : ℝ := ⨆ k, vSeq μ k

/-- `D_μ = lim_{k → ∞} π_k^{1/κ^k}` (source lines 576–579), as used in Lemma
`lem:ell_asymp`(ii) (where `μ_1 = 0`). -/
noncomputable def leafD : ℝ :=
  limUnder atTop (fun k => piSeq μ k ^ (1 / (kappa μ : ℝ) ^ k))

variable {μ}

theorem vSeq_succ (h2 : 2 ≤ kappa μ) (k : ℕ) :
    vSeq μ (k + 1) = vSeq μ k + errSeq μ k / (kappa μ : ℝ) ^ (k + 1) := by
  have h2' : (2 : ℝ) ≤ kappa μ := by exact_mod_cast h2
  have hk : (kappa μ : ℝ) - 1 ≠ 0 := by linarith
  have hk0 : (kappa μ : ℝ) ≠ 0 := by linarith
  simp only [vSeq, errSeq, betaC]
  field_simp
  ring

variable (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (h0 : μ 1 = 0)
include hc h1 h0

omit h0 in
theorem errSeq_bounds (k : ℕ) :
    0 ≤ errSeq μ k ∧ errSeq μ k ≤ piSeq μ k / mass μ (kappa μ) := by
  have ha := mass_kappa_pos hc h1
  have hx := piSeq_pos hc h1 k
  have hb := g_bounds hc h1 hx.le (piSeq_le_one hc h1 k)
  have hpow : 0 < piSeq μ k ^ kappa μ := pow_pos hx _
  have hlow : Real.log (mass μ (kappa μ)) + (kappa μ : ℝ) * Real.log (piSeq μ k) ≤
      Real.log (piSeq μ (k + 1)) := by
    rw [← Real.log_pow, ← Real.log_mul ha.ne' hpow.ne', piSeq_succ]
    exact Real.log_le_log (mul_pos ha hpow) hb.1
  have hup : Real.log (piSeq μ (k + 1)) ≤ Real.log (mass μ (kappa μ)) +
      (kappa μ : ℝ) * Real.log (piSeq μ k) + piSeq μ k / mass μ (kappa μ) := by
    have hq : 0 < 1 + piSeq μ k / mass μ (kappa μ) := add_pos one_pos (div_pos hx ha)
    have h2 : piSeq μ (k + 1) ≤
        (mass μ (kappa μ) * piSeq μ k ^ kappa μ) * (1 + piSeq μ k / mass μ (kappa μ)) := by
      rw [piSeq_succ]
      calc g μ (piSeq μ k) ≤ mass μ (kappa μ) * piSeq μ k ^ kappa μ +
            piSeq μ k ^ (kappa μ + 1) := hb.2
        _ = _ := by
          field_simp
          ring
    have h3 := Real.log_le_log (piSeq_pos hc h1 (k + 1)) h2
    rw [Real.log_mul (mul_pos ha hpow).ne' hq.ne', Real.log_mul ha.ne' hpow.ne',
      Real.log_pow] at h3
    have h4 := Real.log_le_sub_one_of_pos hq
    linarith
  unfold errSeq
  constructor <;> linarith

theorem monotone_vSeq : Monotone (vSeq μ) := by
  have h2 := two_le_kappa hc h1 h0
  refine monotone_nat_of_le_succ fun k => ?_
  rw [vSeq_succ h2]
  have := (errSeq_bounds hc h1 k).1
  have : (0 : ℝ) ≤ (kappa μ : ℝ) ^ (k + 1) := by positivity
  have : 0 ≤ errSeq μ k / (kappa μ : ℝ) ^ (k + 1) := by positivity
  linarith

theorem vSeq_le_uSeq (k : ℕ) : vSeq μ k ≤ uSeq μ k := by
  have h2 : (2 : ℝ) ≤ kappa μ := by exact_mod_cast two_le_kappa hc h1 h0
  have ha := mass_kappa_pos hc h1
  have hx := piSeq_pos hc h1 k
  have : 0 ≤ piSeq μ k / (mass μ (kappa μ) * ((kappa μ : ℝ) - 1) * (kappa μ : ℝ) ^ k) := by
    apply div_nonneg hx.le
    apply mul_nonneg (mul_nonneg ha.le (by linarith)) (pow_nonneg (by linarith) _)
  simp only [uSeq]
  linarith

theorem uSeq_succ_le (k : ℕ) : uSeq μ (k + 1) ≤ uSeq μ k := by
  have h2n := two_le_kappa hc h1 h0
  have h2 : (2 : ℝ) ≤ kappa μ := by exact_mod_cast h2n
  have ha := mass_kappa_pos hc h1
  have hx := piSeq_pos hc h1 k
  have he := (errSeq_bounds hc h1 k).2
  have hxs := (piSeq_succ_lt hc h1 k).le
  have hK : 0 < (kappa μ : ℝ) ^ k := pow_pos (by linarith) _
  have hK1 : 0 < (kappa μ : ℝ) ^ (k + 1) := pow_pos (by linarith) _
  have hden : 0 < mass μ (kappa μ) * ((kappa μ : ℝ) - 1) * (kappa μ : ℝ) ^ (k + 1) :=
    mul_pos (mul_pos ha (by linarith)) hK1
  have key : errSeq μ k / (kappa μ : ℝ) ^ (k + 1) + piSeq μ (k + 1) /
      (mass μ (kappa μ) * ((kappa μ : ℝ) - 1) * (kappa μ : ℝ) ^ (k + 1)) ≤
      piSeq μ k / (mass μ (kappa μ) * ((kappa μ : ℝ) - 1) * (kappa μ : ℝ) ^ k) := by
    calc errSeq μ k / (kappa μ : ℝ) ^ (k + 1) + piSeq μ (k + 1) /
          (mass μ (kappa μ) * ((kappa μ : ℝ) - 1) * (kappa μ : ℝ) ^ (k + 1))
        ≤ piSeq μ k / mass μ (kappa μ) / (kappa μ : ℝ) ^ (k + 1) + piSeq μ k /
          (mass μ (kappa μ) * ((kappa μ : ℝ) - 1) * (kappa μ : ℝ) ^ (k + 1)) :=
          add_le_add (div_le_div_of_nonneg_right he hK1.le)
            (div_le_div_of_nonneg_right hxs hden.le)
      _ = piSeq μ k / (mass μ (kappa μ) * ((kappa μ : ℝ) - 1) * (kappa μ : ℝ) ^ k) := by
          have : (kappa μ : ℝ) - 1 ≠ 0 := by linarith
          field_simp
          ring
  simp only [uSeq]
  rw [vSeq_succ h2n]
  linarith

theorem antitone_uSeq : Antitone (uSeq μ) :=
  antitone_nat_of_succ_le (uSeq_succ_le hc h1 h0)

theorem bddAbove_vSeq : BddAbove (Set.range (vSeq μ)) := by
  refine ⟨uSeq μ 0, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact (vSeq_le_uSeq hc h1 h0 k).trans (antitone_uSeq hc h1 h0 (Nat.zero_le k))

theorem tendsto_vSeq_logD : Tendsto (vSeq μ) atTop (𝓝 (logD μ)) :=
  tendsto_atTop_ciSup (monotone_vSeq hc h1 h0) (bddAbove_vSeq hc h1 h0)

theorem vSeq_le_logD (k : ℕ) : vSeq μ k ≤ logD μ := le_ciSup (bddAbove_vSeq hc h1 h0) k

theorem logD_le_uSeq (k : ℕ) : logD μ ≤ uSeq μ k := by
  apply ciSup_le
  intro m
  rcases le_total m k with hmk | hkm
  · exact (monotone_vSeq hc h1 h0 hmk).trans (vSeq_le_uSeq hc h1 h0 k)
  · exact (vSeq_le_uSeq hc h1 h0 m).trans (antitone_uSeq hc h1 h0 hkm)

/-- The tail error estimate after multiplying by `κ^k`:
`0 ≤ κ^k log D_μ - (log π_k + β) ≤ π_k / (μ_κ (κ - 1))`. -/
theorem logD_error_bounds (k : ℕ) :
    0 ≤ (kappa μ : ℝ) ^ k * logD μ - (Real.log (piSeq μ k) + betaC μ) ∧
      (kappa μ : ℝ) ^ k * logD μ - (Real.log (piSeq μ k) + betaC μ) ≤
        piSeq μ k / (mass μ (kappa μ) * ((kappa μ : ℝ) - 1)) := by
  have h2 : (2 : ℝ) ≤ kappa μ := by exact_mod_cast two_le_kappa hc h1 h0
  have ha := mass_kappa_pos hc h1
  have hK : 0 < (kappa μ : ℝ) ^ k := pow_pos (by linarith) _
  have hv : (kappa μ : ℝ) ^ k * vSeq μ k = Real.log (piSeq μ k) + betaC μ := by
    simp only [vSeq]
    field_simp
  have hu : (kappa μ : ℝ) ^ k * uSeq μ k = Real.log (piSeq μ k) + betaC μ +
      piSeq μ k / (mass μ (kappa μ) * ((kappa μ : ℝ) - 1)) := by
    have : (kappa μ : ℝ) - 1 ≠ 0 := by linarith
    simp only [uSeq, vSeq]
    field_simp
  have h₁ := mul_le_mul_of_nonneg_left (vSeq_le_logD hc h1 h0 k) hK.le
  have h₂ := mul_le_mul_of_nonneg_left (logD_le_uSeq hc h1 h0 k) hK.le
  constructor <;> linarith

/-- `κ^k log D_μ - log π_k - β → 0`: the error of the paper's final display, multiplied
by `κ^k`, tends to zero. -/
theorem tendsto_logD_error :
    Tendsto (fun k => (kappa μ : ℝ) ^ k * logD μ - (Real.log (piSeq μ k) + betaC μ))
      atTop (𝓝 0) := by
  have h := (tendsto_piSeq_zero hc h1).div_const (mass μ (kappa μ) * ((kappa μ : ℝ) - 1))
  rw [zero_div] at h
  exact squeeze_zero (fun k => (logD_error_bounds hc h1 h0 k).1)
    (fun k => (logD_error_bounds hc h1 h0 k).2) h

theorem logD_neg : logD μ < 0 := by
  have h2 : (2 : ℝ) ≤ kappa μ := by exact_mod_cast two_le_kappa hc h1 h0
  have ha := mass_kappa_pos hc h1
  have hlog : Tendsto (fun k => Real.log (piSeq μ k)) atTop atBot := by
    refine Real.tendsto_log_nhdsGT_zero.comp ?_
    exact tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_piSeq_zero hc h1, Eventually.of_forall fun k => piSeq_pos hc h1 k⟩
  obtain ⟨k, hk⟩ := (tendsto_atBot.mp hlog
    (-betaC μ - 1 / (mass μ (kappa μ) * ((kappa μ : ℝ) - 1)) - 1)).exists
  have hK : 0 < (kappa μ : ℝ) ^ k := pow_pos (by linarith) _
  have hb := (logD_error_bounds hc h1 h0 k).2
  have hx1 : piSeq μ k / (mass μ (kappa μ) * ((kappa μ : ℝ) - 1)) ≤
      1 / (mass μ (kappa μ) * ((kappa μ : ℝ) - 1)) :=
    div_le_div_of_nonneg_right (piSeq_le_one hc h1 k)
      (mul_nonneg ha.le (by linarith))
  have : (kappa μ : ℝ) ^ k * logD μ < 0 := by linarith
  by_contra! hD
  have := mul_nonneg hK.le hD
  linarith

theorem tendsto_piSeq_rpow :
    Tendsto (fun k => piSeq μ k ^ (1 / (kappa μ : ℝ) ^ k)) atTop
      (𝓝 (Real.exp (logD μ))) := by
  have h2 : (2 : ℝ) ≤ kappa μ := by exact_mod_cast two_le_kappa hc h1 h0
  have hβ : Tendsto (fun k => betaC μ / (kappa μ : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by linarith))
  have h := ((tendsto_vSeq_logD hc h1 h0).sub hβ).rexp
  rw [sub_zero] at h
  refine h.congr fun k => ?_
  have hK : 0 < (kappa μ : ℝ) ^ k := pow_pos (by linarith) _
  rw [Real.rpow_def_of_pos (piSeq_pos hc h1 k)]
  congr 1
  simp only [vSeq]
  field_simp
  ring

/-- `D_μ = exp (log D_μ)`, i.e. the limit `lim π_k^{1/κ^k}` exists (inventory U03). -/
theorem leafD_eq_exp_logD : leafD μ = Real.exp (logD μ) :=
  (tendsto_piSeq_rpow hc h1 h0).limUnder_eq

/-- `π_k^{1/κ^k} → D_μ` (source lines 576–579). -/
theorem tendsto_piSeq_rpow_leafD :
    Tendsto (fun k => piSeq μ k ^ (1 / (kappa μ : ℝ) ^ k)) atTop (𝓝 (leafD μ)) := by
  rw [leafD_eq_exp_logD hc h1 h0]
  exact tendsto_piSeq_rpow hc h1 h0

theorem leafD_pos : 0 < leafD μ := by
  rw [leafD_eq_exp_logD hc h1 h0]
  exact Real.exp_pos _

theorem leafD_lt_one : leafD μ < 1 := by
  rw [leafD_eq_exp_logD hc h1 h0, Real.exp_lt_one_iff]
  exact logD_neg hc h1 h0

/-- `π_k / (μ_κ^{-1/(κ-1)} D_μ^{κ^k}) → 1`. -/
theorem tendsto_piSeq_div_leafD :
    Tendsto (fun k => piSeq μ k /
      (mass μ (kappa μ) ^ (-1 / ((kappa μ : ℝ) - 1)) * leafD μ ^ (kappa μ ^ k)))
      atTop (𝓝 1) := by
  have ha := mass_kappa_pos hc h1
  have h := (tendsto_logD_error hc h1 h0).neg.rexp
  rw [neg_zero, Real.exp_zero] at h
  refine h.congr fun k => ?_
  rw [leafD_eq_exp_logD hc h1 h0, Real.rpow_def_of_pos ha, ← Real.exp_nat_mul, Nat.cast_pow,
    ← Real.exp_add]
  conv_rhs => rw [← Real.exp_log (piSeq_pos hc h1 k), ← Real.exp_sub]
  congr 1
  simp only [betaC]
  ring

/-- Lemma `lem:ell_asymp`(ii), with the explicit constant:
`π_k ∼ μ_κ^{-1/(κ-1)} D_μ^{κ^k}`. -/
theorem piSeq_isEquivalent_leafD :
    piSeq μ ~[atTop] fun k =>
      mass μ (kappa μ) ^ (-1 / ((kappa μ : ℝ) - 1)) * leafD μ ^ (kappa μ ^ k) :=
  isEquivalent_of_tendsto_one (tendsto_piSeq_div_leafD hc h1 h0)

/-- Lemma `lem:ell_asymp`(ii): if `μ_1 = 0` there is `D_μ ∈ (0, 1)` with
`π_k ∼ μ_κ^{-1/(κ-1)} D_μ^{κ^k}`, where `κ = min{j ≥ 2 : μ_j > 0}` (`kappa_eq_sInf_two`). -/
theorem lem_ell_asymp_ii :
    ∃ D : ℝ, 0 < D ∧ D < 1 ∧
      piSeq μ ~[atTop] fun k =>
        mass μ (kappa μ) ^ (-1 / ((kappa μ : ℝ) - 1)) * D ^ (kappa μ ^ k) :=
  ⟨leafD μ, leafD_pos hc h1 h0, leafD_lt_one hc h1 h0, piSeq_isEquivalent_leafD hc h1 h0⟩

end Superexp

end LeafHeight
end PoissonDeclumping
