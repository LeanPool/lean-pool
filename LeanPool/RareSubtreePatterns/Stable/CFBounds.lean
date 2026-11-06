/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Stable.Normalization
public import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Uniform characteristic-function bounds (Stage 3)

Source lines 862–883 (the analytic input of the local limit theorem, Ibragimov–Linnik
Theorem 4.2.1). With `φ = stepCF μ`:

* `PoissonDeclumping.Stable.exists_norm_stepCF_pow_le_exp`: there are `γ, c, δ > 0`, `A` and
  `N` with `|φ(t/a_n)|^n ≤ exp(-c|t|^γ)` for `n ≥ N`, `A ≤ |t| ≤ δ a_n`;
* `PoissonDeclumping.Stable.exists_norm_stepCF_le_of_le_abs`: `sup_{δ ≤ |θ| ≤ π/d} |φ(θ)| < 1`.

**Departure from the classical route.** The classical proof bounds `1 - |φ(θ)|` below by the
truncated second moment `θ² ∑_{j ≤ 1/|θ|} j² μ_j` and uses its regular variation. Here we use
instead only the already-proved convergence `|φ(s/a_m)|^m → exp(cos(πα/2)|s|^α)` uniformly for
`s ∈ [1,2]` (a compactness argument), `a_{m+1}/a_m → 1` and the Potter bound for the monotone
regularly varying sequence `a`: for `θ` small, the first `m` with `θ a_m ≥ 1` satisfies
`|φ(θ)|^m ≤ q < 1`, and `n/m ≥ (|t|/2C)^{1/β}`. The truncated-second-moment clause of `(H_α)`
(whose slowly varying witness need not be measurable) is not used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Filter Set
open scoped Topology

namespace PoissonDeclumping.Stable

variable {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}

lemma stepCF_neg (μ : PMF ℕ) (θ : ℝ) : stepCF μ (-θ) = (starRingEnd ℂ) (stepCF μ θ) := by
  rw [stepCF, stepCF, ← integral_conj]
  congr 1; funext z
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast]
  push_cast; ring

lemma norm_stepCF_neg (μ : PMF ℕ) (θ : ℝ) : ‖stepCF μ (-θ)‖ = ‖stepCF μ θ‖ := by
  rw [stepCF_neg, Complex.norm_conj]

/-- Uniformly on a compact range `s ∈ [1, K]` of the rescaled argument, `|φ(s/a_m)|^m` stays
below a constant `q < 1` for all large `m`. -/
theorem exists_norm_stepCF_pow_le_of_mem_Icc (h : StableDomain μ α a) (K : ℝ) :
    ∃ q : ℝ, q < 1 ∧ ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ s : ℝ, s ∈ Icc 1 K →
      ‖stepCF μ (s / a m)‖ ^ m ≤ q := by
  have hα := h.alpha_mem
  have hα0 : 0 < α := by linarith
  set c0 := Real.cos (Real.pi * α / 2) with hc0
  have hc0neg : c0 < 0 := cos_pi_mul_div_two_neg hα
  set G : ℝ → ℝ := fun s => Real.exp (c0 * |s| ^ α) with hG
  have hG1 : G 1 < 1 := by
    simp only [hG, abs_one, Real.one_rpow, mul_one]; exact Real.exp_lt_one_iff.2 hc0neg
  have hGle : ∀ s, 1 ≤ |s| → G s ≤ G 1 := by
    intro s hs
    simp only [hG, abs_one, Real.one_rpow, mul_one]
    apply Real.exp_le_exp.2
    have : 1 ≤ |s| ^ α := Real.one_le_rpow hs hα0.le
    nlinarith
  refine ⟨(1 + G 1) / 2, by linarith, ?_⟩
  by_contra hcon
  push Not at hcon
  -- choose violating times and arguments
  choose m hm s hs hviol using hcon
  have hmtop : Tendsto m atTop atTop := tendsto_atTop_mono hm tendsto_id
  obtain ⟨sstar, hsstar, φ, hφ, hsφ⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc 1 K) hs
  have hlim := tendsto_norm_stepCF_pow h (hmtop.comp hφ.tendsto_atTop) hsφ
  rw [closure_Icc] at hsstar
  have hle : G sstar ≤ G 1 := hGle sstar (by rw [abs_of_pos (by linarith [hsstar.1])]; exact
    hsstar.1)
  have hge : (1 + G 1) / 2 ≤ G sstar := by
    apply ge_of_tendsto hlim
    exact Eventually.of_forall fun j => (hviol (φ j)).le
  linarith

/-- **Characteristic-function bound (Stage 3).** There are `γ, c > 0`, `A`, `δ > 0` and `N` such
that for `n ≥ N` and `A ≤ |t| ≤ δ a_n`, `|φ(t/a_n)|^n ≤ exp(-c |t|^γ)`. The proof uses only the
convergence `|φ(s/a_m)|^m → exp(cos(πα/2)|s|^α)` uniformly for `s ∈ [1,2]`, the ratio
`a_{m+1}/a_m → 1`, and the Potter bound `a_n ≤ C (n/m)^β a_m` (`β = 1/α + 1`). -/
theorem exists_norm_stepCF_pow_le_exp (h : StableDomain μ α a) :
    ∃ γ c A δ : ℝ, 0 < γ ∧ 0 < c ∧ 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t : ℝ, A ≤ |t| →
      |t| ≤ δ * a n → ‖stepCF μ (t / a n)‖ ^ n ≤ Real.exp (-c * |t| ^ γ) := by
  have hα := h.alpha_mem
  have hα0 : 0 < α := by linarith
  have hrv := regularlyVaryingSeq h
  obtain ⟨q, hq1, N₀, hN₀⟩ := exists_norm_stepCF_pow_le_of_mem_Icc h 2
  -- `q ≥ 0` may be assumed
  set q' : ℝ := max q (1 / 2) with hq'
  have hq'1 : q' < 1 := max_lt hq1 (by norm_num)
  have hq'0 : 0 < q' := lt_max_of_lt_right (by norm_num)
  obtain ⟨C, hC, hCP⟩ := hrv.exists_potter_global h.monotone h.pos (by positivity : (0:ℝ) ≤ 1 / α)
    one_pos
  set β : ℝ := 1 / α + 1 with hβ
  have hβ0 : 0 < β := by positivity
  -- eventually `a (m+1) ≤ 2 a m`
  obtain ⟨N₂, hN₂⟩ := ((tendsto_succ_div h).eventually (gt_mem_nhds (by norm_num : (1:ℝ) <
    2))).exists_forall_of_atTop
  set N₁ : ℕ := max (max N₀ N₂) 1 with hN₁
  have haN₁ : 0 < a N₁ := h.pos _ (le_max_right _ _)
  set δ : ℝ := 1 / (2 * a N₁) with hδ
  have hδ0 : 0 < δ := by positivity
  set A : ℝ := 4 * C with hA
  set γ : ℝ := 1 / β with hγ
  have hγ0 : 0 < γ := by positivity
  set c : ℝ := -Real.log q' / 2 * (2 * C) ^ (-γ) with hc
  have hlogq : Real.log q' < 0 := Real.log_neg hq'0 hq'1
  have hc0 : 0 < c := by
    apply mul_pos (by linarith) (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨γ, c, A, δ, hγ0, hc0, hδ0, N₁, fun n hn t hAt htδ => ?_⟩
  have hat := tendsto_atTop h
  set θ : ℝ := |t| / a n with hθ
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have han : 0 < a n := h.pos n hn1
  have ht0 : 0 < |t| := lt_of_lt_of_le (by positivity) hAt
  have hθ0 : 0 < θ := div_pos ht0 han
  have hθδ : θ ≤ δ := by rw [hθ, div_le_iff₀ han]; exact htδ
  -- reduce to `t ≥ 0`
  have hnorm : ‖stepCF μ (t / a n)‖ = ‖stepCF μ θ‖ := by
    rcases le_or_gt 0 t with ht | ht
    · rw [hθ, abs_of_nonneg ht]
    · rw [hθ, abs_of_neg ht, neg_div, norm_stepCF_neg]
  rw [hnorm]
  -- the first time `m` with `θ a_m ≥ 1`
  have hex : ∃ m : ℕ, 1 ≤ θ * a m := by
    obtain ⟨m, hm⟩ := (hat.eventually_ge_atTop (1 / θ)).exists
    exact ⟨m, by rwa [div_le_iff₀ hθ0, mul_comm] at hm⟩
  classical
  set m := Nat.find hex with hmdef
  have hm1 : 1 ≤ θ * a m := Nat.find_spec hex
  have hmN : N₁ < m := by
    by_contra hle
    push Not at hle
    have h1 : θ * a m ≤ θ * a N₁ := mul_le_mul_of_nonneg_left (h.monotone hle) hθ0.le
    have h2 : θ * a N₁ ≤ 1 / 2 := by
      calc θ * a N₁ ≤ δ * a N₁ := mul_le_mul_of_nonneg_right hθδ haN₁.le
        _ = 1 / 2 := by rw [hδ]; field_simp
    linarith
  have hmpred : θ * a (m - 1) < 1 := by
    have := Nat.find_min hex (show m - 1 < m by omega)
    push Not at this
    exact this
  have hm2 : θ * a m ≤ 2 := by
    have hN2 : N₂ ≤ m - 1 := by
      have : N₂ ≤ N₁ := le_trans (le_max_right _ _) (le_max_left _ _)
      omega
    have h1 := hN₂ (m - 1) hN2
    have hpos' : 0 < a (m - 1) := h.pos _ (by omega)
    rw [show m - 1 + 1 = m by omega, div_lt_iff₀ hpos'] at h1
    calc θ * a m ≤ θ * (2 * a (m - 1)) :=
          mul_le_mul_of_nonneg_left h1.le hθ0.le
      _ = 2 * (θ * a (m - 1)) := by ring
      _ ≤ 2 := by linarith only [hmpred]
  have hm0 : 1 ≤ m := by omega
  have ham : 0 < a m := h.pos m hm0
  have hNm : N₀ ≤ m := by
    have : N₀ ≤ N₁ := le_trans (le_max_left _ _) (le_max_left _ _)
    omega
  have hqm : ‖stepCF μ θ‖ ^ m ≤ q' := by
    have := hN₀ m hNm (θ * a m) ⟨hm1, hm2⟩
    rw [mul_div_assoc, div_self ham.ne', mul_one] at this
    exact this.trans (le_max_left _ _)
  -- `n > m` and `n/m` large
  have hta : |t| = θ * a n := by rw [hθ]; field_simp
  have hmn : m ≤ n := by
    by_contra hlt
    push Not at hlt
    have : a n ≤ a m := h.monotone hlt.le
    have : |t| ≤ 2 := by
      rw [hta]
      exact (mul_le_mul_of_nonneg_left this hθ0.le).trans hm2
    have : (2 : ℝ) < A := by
      have : (1 : ℝ) ≤ C := by
        have := (hCP 1 1 le_rfl le_rfl).1
        have ha1 := h.pos 1 le_rfl
        simp only [Nat.cast_one, div_self one_ne_zero, Real.one_rpow, mul_one] at this
        nlinarith only [this, ha1]
      rw [hA]; linarith
    linarith
  have hPot := (hCP m n hm0 hmn).1
  have hratio : |t| / (2 * C) ≤ ((n : ℝ) / m) ^ β := by
    rw [div_le_iff₀ (by positivity), hta]
    calc θ * a n ≤ θ * (C * ((n : ℝ) / m) ^ β * a m) := by
          apply mul_le_mul_of_nonneg_left hPot hθ0.le
      _ = C * ((n : ℝ) / m) ^ β * (θ * a m) := by ring
      _ ≤ C * ((n : ℝ) / m) ^ β * 2 := by
          apply mul_le_mul_of_nonneg_left hm2 (by positivity)
      _ = ((n : ℝ) / m) ^ β * (2 * C) := by ring
  have hnm1 : (1 : ℝ) ≤ (n : ℝ) / m := by
    rw [le_div_iff₀ (by positivity), one_mul]; exact_mod_cast hmn
  -- the power bound
  set k := n / m with hk
  have hk_le : m * k ≤ n := Nat.mul_div_le n m
  have hk_ge : (n : ℝ) / m / 2 ≤ k := by
    have := PoissonDeclumping.half_le_natFloor hnm1
    rwa [Nat.floor_div_eq_div] at this
  have hφ1 : ‖stepCF μ θ‖ ≤ 1 := norm_stepCF_le μ θ
  have hpow : ‖stepCF μ θ‖ ^ n ≤ q' ^ k := by
    calc ‖stepCF μ θ‖ ^ n ≤ ‖stepCF μ θ‖ ^ (m * k) :=
          pow_le_pow_of_le_one (norm_nonneg _) hφ1 hk_le
      _ = (‖stepCF μ θ‖ ^ m) ^ k := pow_mul _ _ _
      _ ≤ q' ^ k := pow_le_pow_left₀ (by positivity) hqm k
  refine hpow.trans ?_
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hq'0]
  apply Real.exp_le_exp.2
  -- `log q' * k ≤ -c |t|^γ`
  have h1 : (|t| / (2 * C)) ^ γ ≤ (n : ℝ) / m := by
    calc (|t| / (2 * C)) ^ γ ≤ (((n : ℝ) / m) ^ β) ^ γ :=
          Real.rpow_le_rpow (by positivity) hratio hγ0.le
      _ = (n : ℝ) / m := by
          rw [← Real.rpow_mul (by positivity), hγ, mul_one_div_cancel hβ0.ne', Real.rpow_one]
  have h2 : (|t| / (2 * C)) ^ γ = |t| ^ γ * (2 * C) ^ (-γ) := by
    rw [Real.div_rpow (abs_nonneg _) (by positivity), Real.rpow_neg (by positivity), div_eq_mul_inv]
  have h3 : -c * |t| ^ γ = Real.log q' / 2 * (|t| / (2 * C)) ^ γ := by
    rw [h2, hc]; ring
  rw [h3]
  calc Real.log q' / 2 * (|t| / (2 * C)) ^ γ ≥ Real.log q' / 2 * ((n : ℝ) / m) := by
        apply mul_le_mul_of_nonpos_left h1 (by linarith)
    _ = Real.log q' * ((n : ℝ) / m / 2) := by ring
    _ ≥ Real.log q' * k := by
        apply mul_le_mul_of_nonpos_left hk_ge hlogq.le

/-- Away from the dual lattice: `sup_{δ ≤ |θ| ≤ π/d} |φ(θ)| < 1`. -/
theorem exists_norm_stepCF_le_of_le_abs (hc : IsCritical μ) (hne : μ 1 ≠ 1) {δ : ℝ}
    (hδ : 0 < δ) : ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ θ : ℝ, δ ≤ |θ| →
      |θ| ≤ Real.pi / latticeSpan μ → ‖stepCF μ θ‖ ≤ q := by
  set K : Set ℝ := {θ | δ ≤ |θ|} ∩ {θ | |θ| ≤ Real.pi / latticeSpan μ} with hK
  have hKc : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact (isClosed_le continuous_const continuous_abs).inter
        (isClosed_le continuous_abs continuous_const)
    · refine (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := Real.pi / latticeSpan μ)).subset ?_
      intro θ hθ
      simpa [Metric.mem_closedBall, Real.dist_eq] using hθ.2
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨0, le_rfl, one_pos, fun θ h1 h2 => ?_⟩
    have : θ ∈ K := ⟨h1, h2⟩
    rw [hKe] at this
    exact absurd this (Set.notMem_empty θ)
  · obtain ⟨θ₀, hθ₀, hmax⟩ := hKc.exists_isMaxOn hKne
      (continuous_norm.comp (continuous_stepCF μ)).continuousOn
    have h0 : θ₀ ≠ 0 := by
      intro h; have := hθ₀.1; simp only [mem_ofPred_eq] at this; rw [h, abs_zero] at this; linarith
    refine ⟨‖stepCF μ θ₀‖, norm_nonneg _, norm_stepCF_lt_one hc hne h0 hθ₀.2, fun θ h1 h2 => ?_⟩
    exact hmax ⟨h1, h2⟩

end PoissonDeclumping.Stable
