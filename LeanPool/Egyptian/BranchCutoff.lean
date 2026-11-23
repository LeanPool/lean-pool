/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.Payoff
import Mathlib.Tactic.TypeStar

/-!
# Attainment after truncating long branches

Kovač and Tang, §3.3 (Lemmas 14–15) and §4. A strictly superior witness excludes
all sufficiently long initial blocks. This gives both an attained maximum and
finitely many maximizing first blocks, allowing different blocks to tie. The
estimates on the two kinds of block are separate from the optimization lemma.
-/

@[expose] public section

namespace Egyptian.BranchCutoff

open Filter Set
open scoped Topology

/-- A finite family at each bounded length and decay below the reward of a
fixed witness give a maximum. All maximizing branches form a finite set. -/
theorem finite_and_attained {α : Type*} (S : Set α) (length : α → ℕ)
    (reward : α → ℝ) (a : α) (ha : a ∈ S)
    (hfinite : ∀ M : ℕ, {x | x ∈ S ∧ length x < M}.Finite)
    (hcut : ∃ M : ℕ, ∀ x ∈ S, M ≤ length x → reward x < reward a) :
    ∃ b ∈ S, (∀ x ∈ S, reward x ≤ reward b) ∧
      {x | x ∈ S ∧ reward x = reward b}.Finite := by
  classical
  obtain ⟨M, hM⟩ := hcut
  let N := max M (length a + 1)
  let good := {x | x ∈ S ∧ length x < N}
  have finiteGood : good.Finite := hfinite N
  have haGood : a ∈ good := ⟨ha, Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right ..)⟩
  obtain ⟨b, hb, hbest⟩ := finiteGood.toFinset.exists_max_image reward
    ⟨a, finiteGood.mem_toFinset.mpr haGood⟩
  have hbGood := finiteGood.mem_toFinset.mp hb
  have hab := hbest a (finiteGood.mem_toFinset.mpr haGood)
  have short {x : α} (hx : x ∈ S) (hbetter : reward a ≤ reward x) : x ∈ good := by
    refine ⟨hx, ?_⟩
    by_contra! hlong
    exact (not_lt_of_ge hbetter) (hM x hx ((le_max_left ..).trans hlong))
  refine ⟨b, hbGood.1, ?_, finiteGood.subset ?_⟩
  · intro x hx
    by_cases hax : reward a ≤ reward x
    · exact hbest x (finiteGood.mem_toFinset.mpr (short hx hax))
    · exact (le_of_not_ge hax).trans hab
  · intro x hx
    exact short hx.1 (hx.2 ▸ hab)

/-- If every branch reward lies below a bound depending on its length, and
that bound converges below the witness, the cutoff hypothesis holds. -/
theorem cutoff_of_tendsto {α : Type*} (S : Set α) (length : α → ℕ)
    (reward : α → ℝ) (upper : ℕ → ℝ) {v : ℝ} (a : α)
    (hbound : ∀ x ∈ S, reward x ≤ upper (length x))
    (hlim : Tendsto upper atTop (𝓝 v)) (hgap : v < reward a) :
    ∃ M : ℕ, ∀ x ∈ S, M ≤ length x → reward x < reward a := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hlim.eventually_lt_const hgap)
  exact ⟨M, fun x hx hl => (hbound x hx).trans_lt (hM (length x) hl)⟩

/-- The first-descent branch bound H(t) + 2 Γ_P / 2^r tends to H(t). -/
theorem first_descent_limit (h Γ : ℝ) :
    Tendsto (fun r : ℕ => h + (2 * Γ) / 2^r) atTop (𝓝 h) := by
  have hzero := Payoff.const_div_two_pow_tendsto_zero 1
  simpa [div_eq_mul_inv] using (hzero.const_mul (2*Γ)).const_add h

/-- The entrance branch bound for an initial remainder P/Q > 1. -/
noncomputable def entranceUpper (Q : ℕ) (r : ℕ) : ℝ :=
  (Real.log Q + ((r : ℝ)^2 + 2) * Real.log 2) / 2^r

/-- The polynomial factor in the entrance bound is harmless under the
discount. We use mathlib's polynomial-over-exponential limit for k=0,2. -/
theorem entrance_limit (Q : ℕ) :
    Tendsto (entranceUpper Q) atTop (𝓝 0) := by
  have hzero := Payoff.const_div_two_pow_tendsto_zero 1
  have hquad := tendsto_pow_const_div_const_pow_of_one_lt 2 (r := 2) (by norm_num)
  have h := (hzero.const_mul (Real.log Q + 2 * Real.log 2)).add
    (hquad.const_mul (Real.log 2))
  convert h using 1
  · ext r
    simp only [entranceUpper]
    ring
  · simp

end Egyptian.BranchCutoff

namespace Egyptian.Payoff

/-- Strong induction may use the paper's elementary majorant log(2p) at each
cleared numerator p. At a first drop from p to d, the factor p/d in the
reciprocal error cancels the d in this majorant. This gives the decay in r
used to prune long blocks, without introducing the smaller recursive Γ_p. -/
theorem fall_envelope {t t' p d : ℝ} {r : ℕ}
    (ht : 1 ≤ t) (ht' : 1 ≤ t') (hp : 1 ≤ p) (hd : 1 ≤ d) (hr : 0 < r)
    (htr : t' < p / d * orbit t r) :
    (value t' + Real.log (2*d)) / 2^r ≤ value t + Real.log (4*p) / 2^r ∧
      value t + Real.log (4*p) / 2^r ≤ value t + Real.log (2*p) := by
  have hp' : 0 < p := by linarith
  have hd' : 0 < d := by linarith
  have ho : 0 < orbit t r := by have := one_le_orbit ht r; linarith
  have h2 : (0 : ℝ) < 2^r := by positivity
  have logtr := Real.log_lt_log (by linarith : 0 < t') htr
  rw [Real.log_mul (div_ne_zero hp'.ne' hd'.ne') ho.ne',
    Real.log_div hp'.ne' hd'.ne'] at logtr
  have hlog2d : Real.log (2*d) = Real.log 2 + Real.log d :=
    Real.log_mul (by norm_num) hd'.ne'
  have hlog2p : Real.log (2*p) = Real.log 2 + Real.log p :=
    Real.log_mul (by norm_num) hp'.ne'
  have hlog4p : Real.log (4*p) = 2 * Real.log 2 + Real.log p := by
    rw [show 4 * p = 2 * (2 * p) by ring,
      Real.log_mul (by norm_num) (by positivity : 0 < 2 * p).ne', hlog2p]
    ring
  have horbit := log_le_value (one_le_orbit ht r)
  rw [value_orbit ht r] at horbit
  constructor
  · apply (div_le_iff₀ h2).mpr
    rw [add_mul, div_mul_cancel₀ _ h2.ne', hlog4p, hlog2d]
    linarith [value_le_log_add ht', mul_comm ((2:ℝ)^r) (value t)]
  · apply add_le_add_right
    apply (div_le_iff₀ h2).mpr
    have logp := Real.log_nonneg hp
    have log2p : 0 ≤ Real.log (2*p) := Real.log_nonneg (by linarith)
    have htwo : (2:ℝ) ≤ 2^r := by
      simpa using (pow_le_pow_right₀ (a := (2:ℝ)) (by norm_num) (show 1 ≤ r by omega))
    have hmul := mul_le_mul_of_nonneg_left htwo log2p
    rw [hlog4p, hlog2p]
    rw [hlog2p] at hmul
    linarith

/-- Entrance estimate for improper initial targets. The factors P' cancel
when the induction envelope for the successor is simplified. A non-strict
upper bound on its common denominator Q' suffices. -/
theorem entrance_envelope {P' Q' Q r : ℕ}
    (hp : 0 < P') (hpq : P' ≤ Q') (hq : 0 < Q)
    (hbound : (Q' : ℝ) ≤ (Q : ℝ) * (2 : ℝ) ^ (r ^ 2)) :
    (value ((Q':ℝ) / P') + Real.log (2 * (P':ℝ))) / 2^r ≤
      BranchCutoff.entranceUpper Q r := by
  have hp' : (0:ℝ) < P' := by exact_mod_cast hp
  have hq' : (0:ℝ) < Q' := by exact_mod_cast hp.trans_le hpq
  have hQ : (0:ℝ) < Q := by exact_mod_cast hq
  have ht : (1:ℝ) ≤ Q'/P' := (one_le_div hp').mpr (by exact_mod_cast hpq)
  have hv := value_le_log_add ht
  rw [Real.log_div hq'.ne' hp'.ne'] at hv
  have hlog := Real.log_le_log hq' hbound
  rw [Real.log_mul hQ.ne' (by positivity : (0:ℝ) < 2^(r^2)).ne', Real.log_pow] at hlog
  push_cast at hlog
  unfold BranchCutoff.entranceUpper
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [Real.log_mul (by norm_num) hp'.ne']
  linarith

end Egyptian.Payoff
