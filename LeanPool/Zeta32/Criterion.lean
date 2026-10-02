/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang, Moritz Firsching
-/
module
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Positivity

/-! Generic criterion adapted from the Li₂ light-certificate project and the
Apéry criterion in mo271/Zeta5 (Apache-2.0), with attribution retained. -/

@[expose] public section

open Polynomial Filter Topology
namespace Zeta32

lemma pow_mul_aeval_div_eq_intCast (p : ℤ[X]) {d : ℕ} (hd : p.natDegree ≤ d) (a b : ℤ)
    (hb : b ≠ 0) :
    (b : ℝ) ^ d * aeval ((a : ℝ) / b) p =
      ((∑ k ∈ Finset.range (d + 1), p.coeff k * a ^ k * b ^ (d - k) : ℤ) : ℝ) := by
  have hbr : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hlt : (p.map (algebraMap ℤ ℝ)).natDegree < d + 1 :=
    lt_of_le_of_lt natDegree_map_le (by omega)
  rw [aeval_def, eval₂_eq_eval_map, eval_eq_sum_range' hlt, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hpow : (b : ℝ) ^ d = (b : ℝ) ^ (d - k) * (b : ℝ) ^ k := by
    rw [← pow_add]
    congr 1
    omega
  rw [coeff_map, hpow, div_pow]
  simp only [algebraMap_int_eq, eq_intCast]
  field_simp

theorem one_le_den_pow_mul_abs (Q : ℤ[X]) (q : ℚ) (d : ℕ)
    (hdeg : Q.natDegree ≤ d) (hne : aeval (q : ℝ) Q ≠ 0) :
    1 ≤ (q.den : ℝ)^d * |aeval (q : ℝ) Q| := by
  let m : ℤ := ∑ k ∈ Finset.range (d+1), Q.coeff k * q.num^k * (q.den : ℤ)^(d-k)
  have hb : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hm : (q.den : ℝ)^d * aeval (q : ℝ) Q = (m : ℝ) := by
    simpa [Rat.cast_def, Int.cast_natCast, m] using
      pow_mul_aeval_div_eq_intCast Q hdeg q.num (q.den : ℤ)
        (by exact_mod_cast q.den_pos.ne')
  have hm0 : m ≠ 0 := by
    intro hz
    have : (q.den : ℝ)^d * aeval (q : ℝ) Q = 0 := by simpa [hz] using hm
    exact hne ((mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hb.ne'))
  have hge : (1 : ℝ) ≤ |(m : ℝ)| := by
    have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm0
    exact_mod_cast this
  rw [← hm, abs_mul, abs_of_pos (pow_pos hb _)] at hge
  exact hge

theorem irrational_of_int_polynomials (ξ : ℝ) (P : ℕ → ℤ[X]) (d : ℕ → ℕ)
    (hdeg : ∀ n, (P n).natDegree ≤ d n)
    (hdecay : ∀ b : ℕ, 0 < b →
      Tendsto (fun n => (b : ℝ)^(d n) * |aeval ξ (P n)|) atTop (𝓝 0))
    (hnonzero : ∀ q : ℚ, ∃ᶠ n in atTop, aeval (q : ℝ) (P n) ≠ 0) :
    Irrational ξ := by
  rintro ⟨q, hq⟩
  have hsmall : ∀ᶠ n in atTop, (q.den : ℝ)^(d n) * |aeval ξ (P n)| < 1 :=
    (hdecay q.den q.den_pos).eventually (gt_mem_nhds one_pos)
  obtain ⟨n, hn, hs⟩ := ((hnonzero q).and_eventually hsmall).exists
  have hge := one_le_den_pow_mul_abs (P n) q (d n) (hdeg n) hn
  rw [hq] at hge
  linarith

theorem tendsto_pow_mul_exp_neg_sq_of_pos {c : ℝ} (hc : 0 < c) (D b : ℕ) (hb : 0 < b) :
    Tendsto (fun n : ℕ => (b : ℝ) ^ (D * n) * Real.exp (-c * (n : ℝ) ^ 2)) atTop (𝓝 0) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hrw : ∀ n : ℕ, (b : ℝ) ^ (D * n) * Real.exp (-c * (n : ℝ) ^ 2) =
      Real.exp ((D * n) * Real.log b - c * (n : ℝ) ^ 2) := by
    intro n
    have hbpow : (0 : ℝ) < (b : ℝ) ^ (D * n) := pow_pos hbR _
    rw [← Real.exp_log hbpow, ← Real.exp_add, Real.log_pow]
    congr 1
    push_cast
    ring
  simp_rw [hrw]
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  refine squeeze_zero' (Eventually.of_forall fun n => (Real.exp_pos _).le) ?_ hexp
  filter_upwards [eventually_ge_atTop (⌈(D * Real.log b + 1) / c⌉₊)] with n hn
  apply Real.exp_le_exp.mpr
  have hn' : (D * Real.log b + 1) / c ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have hn'' : D * Real.log b + 1 ≤ c * n := by
    rw [div_le_iff₀ hc] at hn'
    linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_left hn'' hn0]

end Zeta32
end
