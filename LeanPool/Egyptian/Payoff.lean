/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The payoff function

This is the construction in the payoff lemma of Kovač and Tang. The upper bound
`log (t+1)` follows by comparing `Φ(t)+1` with `(t+1)^2`. It sharpens the
paper's upper bound and simplifies the proof of strict increase.
-/

@[expose] public section

namespace Egyptian.Payoff

open Set Filter
open scoped Topology

/-- The reciprocal remainder after the next greedy term at a unit fraction. -/
def phi (t : ℝ) : ℝ := t * (t + 1)

/-- Iteration of the real recurrence, with the initial point at index zero. -/
def orbit (t : ℝ) : ℕ → ℝ
  | 0 => t
  | n + 1 => phi (orbit t n)

theorem one_le_phi {t : ℝ} (ht : 1 ≤ t) : 1 ≤ phi t := by
  exact ht.trans (le_mul_of_one_le_right (zero_le_one.trans ht) (by linarith only [ht]))

theorem one_le_orbit {t : ℝ} (ht : 1 ≤ t) (n : ℕ) : 1 ≤ orbit t n := by
  induction n with
  | zero => exact ht
  | succ n ih => exact one_le_phi ih

/-- The continuous comparison terms from the paper. -/
noncomputable def reference (t : ℝ) (i : ℕ) : ℝ := 1 / (orbit t i + 1)

theorem reference_pos {t : ℝ} (ht : 1 ≤ t) (i : ℕ) : 0 < reference t i := by
  have := one_le_orbit ht i
  unfold reference
  positivity

theorem reference_sum {t : ℝ} (ht : 1 ≤ t) (k : ℕ) :
    (∑ i ∈ Finset.range k, reference t i) = 1 / t - 1 / orbit t k := by
  induction k with
  | zero => simp [orbit]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, orbit, phi, reference]
    have h := one_le_orbit ht k
    field_simp [show orbit t k ≠ 0 by linarith, show orbit t k + 1 ≠ 0 by linarith]
    ring

theorem reference_prod {t : ℝ} (ht : 1 ≤ t) (k : ℕ) :
    (∏ i ∈ Finset.range k, reference t i) = t / orbit t k := by
  induction k with
  | zero => simp [orbit, show t ≠ 0 by linarith]
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, orbit, phi, reference, div_mul_eq_div_div, mul_one_div]

/-- The greedy reference terms saturate the prefix comparison bound. -/
theorem reference_identity {t : ℝ} (ht : 1 ≤ t) (k : ℕ) :
    (∑ i ∈ Finset.range k, reference t i) + (1 / t) *
      (∏ i ∈ Finset.range k, reference t i) = 1 / t := by
  rw [reference_sum ht, reference_prod ht]
  field_simp
  ring

theorem orbit_shift (t : ℝ) (n : ℕ) : orbit (phi t) n = orbit t (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg phi ih

theorem const_div_two_pow_tendsto_zero (c : ℝ) :
    Tendsto (fun n : ℕ => c / (2 : ℝ) ^ n) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

/-- The normalized logarithm in equation (Hformula). -/
noncomputable def normalized (t : ℝ) (j : ℕ) : ℝ := Real.log (orbit t j) / 2^j

/-- The supremum of normalized logarithms equals their monotone limit for `t ≥ 1`. -/
noncomputable def value (t : ℝ) : ℝ := ⨆ j : ℕ, normalized t j

private theorem log_phi_lower {t : ℝ} (ht : 1 ≤ t) :
    2 * Real.log t ≤ Real.log (phi t) := by
  have h : 0 < t := by linarith
  rw [phi, Real.log_mul h.ne' (by positivity)]
  linarith [Real.log_le_log h (show t ≤ t + 1 by linarith)]

private theorem log_phi_upper {t : ℝ} (ht : 1 ≤ t) :
    Real.log (phi t + 1) ≤ 2 * Real.log (t+1) := by
  have h := Real.log_le_log (by have := one_le_phi ht; linarith : 0 < phi t + 1)
    (show phi t + 1 ≤ (t+1)^2 by unfold phi; nlinarith)
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem normalized_mono {t : ℝ} (ht : 1 ≤ t) : Monotone (normalized t) := by
  apply monotone_nat_of_le_succ
  intro j
  have h := log_phi_lower (one_le_orbit ht j)
  unfold normalized
  rw [pow_succ, div_le_div_iff₀ (by positivity) (by positivity)]
  change _ ≤ Real.log (phi (orbit t j)) * _
  nlinarith only [mul_le_mul_of_nonneg_right h (show 0 ≤ (2 : ℝ) ^ j by positivity)]

theorem log_orbit_upper {t : ℝ} (ht : 1 ≤ t) (j : ℕ) :
    Real.log (orbit t j + 1) ≤ 2^j * Real.log (t+1) := by
  induction j with
  | zero => simp [orbit]
  | succ j ih =>
    have h := log_phi_upper (one_le_orbit ht j)
    rw [pow_succ]
    change Real.log (phi (orbit t j) + 1) ≤ _
    linarith

theorem normalized_upper {t : ℝ} (ht : 1 ≤ t) (j : ℕ) :
    normalized t j ≤ Real.log (t+1) := by
  apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ)^j)).2
  rw [mul_comm]
  exact le_trans (Real.log_le_log (by have := one_le_orbit ht j; linarith)
    (le_add_of_nonneg_right zero_le_one)) (log_orbit_upper ht j)

theorem normalized_bounded {t : ℝ} (ht : 1 ≤ t) :
    BddAbove (range (normalized t)) :=
  ⟨Real.log (t+1), by rintro _ ⟨j, rfl⟩; exact normalized_upper ht j⟩

theorem normalized_tendsto {t : ℝ} (ht : 1 ≤ t) :
    Tendsto (normalized t) atTop (𝓝 (value t)) :=
  tendsto_atTop_ciSup (normalized_mono ht) (normalized_bounded ht)

theorem log_le_value {t : ℝ} (ht : 1 ≤ t) : Real.log t ≤ value t := by
  apply ge_of_tendsto (normalized_tendsto ht)
  exact Eventually.of_forall (fun j => by
    simpa only [normalized, orbit, pow_zero, div_one] using (normalized_mono ht (Nat.zero_le j)))

theorem value_le_log_succ {t : ℝ} (ht : 1 ≤ t) : value t ≤ Real.log (t+1) :=
  ciSup_le (normalized_upper ht)

theorem value_le_log_add {t : ℝ} (ht : 1 ≤ t) :
    value t ≤ Real.log t + Real.log 2 := by
  have h : 0 < t := by linarith
  rw [← Real.log_mul h.ne' (by norm_num)]
  exact le_trans (value_le_log_succ ht)
    (Real.log_le_log (by positivity) (by linarith))

theorem value_phi {t : ℝ} (ht : 1 ≤ t) : value (phi t) = 2 * value t := by
  apply tendsto_nhds_unique (normalized_tendsto (one_le_phi ht))
  have h := (normalized_tendsto ht).comp (tendsto_add_atTop_nat 1)
  have h' := h.const_mul (2 : ℝ)
  apply h'.congr
  intro j
  change 2 * normalized t (j+1) = normalized (phi t) j
  unfold normalized
  rw [orbit_shift, pow_succ]
  ring

theorem value_orbit {t : ℝ} (ht : 1 ≤ t) (j : ℕ) :
    value (orbit t j) = 2^j * value t := by
  induction j with
  | zero => simp [orbit]
  | succ j ih =>
    rw [orbit, value_phi (one_le_orbit ht j), ih, pow_succ]
    ring

/-- The initial positive gap amplifies under the quadratic map. -/
private theorem orbit_gap {s t : ℝ} (hs : 1 ≤ s) (hst : s < t) (j : ℕ) :
    2^j * (t-s) ≤ orbit t j - orbit s j := by
  induction j with
  | zero => simp [orbit]
  | succ j ih =>
    have hgap : 0 ≤ orbit t j - orbit s j :=
      le_trans (by positivity) ih
    have hs' := one_le_orbit hs j
    have ht' := one_le_orbit (le_trans hs hst.le) j
    have hprod := mul_nonneg hgap (show 0 ≤ orbit t j + orbit s j - 1 by linarith)
    simp only [orbit, phi, pow_succ]
    nlinarith only [ih, hprod]

theorem value_strictMonoOn : StrictMonoOn value (Ici 1) := by
  intro s hs t ht hst
  have hg : Tendsto (fun j : ℕ => (2 : ℝ)^j * (t-s)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℝ))).atTop_mul_const
      (sub_pos.mpr hst)
  obtain ⟨j, hj⟩ := (hg.eventually_gt_atTop 1).exists
  have horb : orbit s j + 1 < orbit t j := by linarith [orbit_gap hs hst j]
  have hlogs := Real.log_lt_log (by have := one_le_orbit hs j; linarith) horb
  have hval := lt_of_le_of_lt (value_le_log_succ (one_le_orbit hs j))
    (lt_of_lt_of_le hlogs (log_le_value (one_le_orbit ht j)))
  rw [value_orbit hs, value_orbit ht] at hval
  exact lt_of_mul_lt_mul_left hval (by positivity)

/-- The doubling identity and additive logarithmic bounds determine the payoff
on its entire domain, even without an ordering assumption on the candidate. -/
theorem unique_on_Ici (F : ℝ → ℝ)
    (hF : ∀ t, 1 ≤ t → F (phi t) = 2 * F t)
    (hb : ∀ t, 1 ≤ t → Real.log t ≤ F t ∧ F t ≤ Real.log t + Real.log 2)
    {t : ℝ} (ht : 1 ≤ t) : F t = value t := by
  have hiter (j : ℕ) : F (orbit t j) = 2^j * F t := by
    induction j with
    | zero => simp [orbit]
    | succ j ih =>
      rw [orbit, hF _ (one_le_orbit ht j), ih, pow_succ]
      ring
  have hz := const_div_two_pow_tendsto_zero (Real.log 2)
  have hlim := (normalized_tendsto ht).add hz
  rw [add_zero] at hlim
  have hconst : Tendsto (fun _ : ℕ => F t) atTop (𝓝 (value t)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (normalized_tendsto ht) hlim
    · intro j
      have h := (hb _ (one_le_orbit ht j)).1
      rw [hiter] at h
      exact (div_le_iff₀ (by positivity)).2 (by linarith)
    · intro j
      have h := (hb _ (one_le_orbit ht j)).2
      rw [hiter] at h
      change F t ≤ Real.log (orbit t j) / 2^j + Real.log 2 / 2^j
      rw [← add_div]
      exact (le_div_iff₀ (by positivity)).2 (by linarith)
  exact tendsto_nhds_unique tendsto_const_nhds hconst

/-- The normalized logarithms converge to a nonnegative limit. -/
theorem value_nonneg {t : ℝ} (ht : 1 ≤ t) : 0 ≤ value t :=
  (Real.log_nonneg ht).trans (log_le_value ht)

/-- Exponential domination in the choice of the strict-convention cutoff.
The explicit threshold works for every initial reciprocal at least two. -/
theorem tail_growth {t : ℝ} (ht : 2 ≤ t) (N k : ℕ) (hk : max 4 (N + 1) ≤ k) :
    8 < orbit t k ∧ 2 * ((N+k : ℕ) : ℝ) * Real.log 2 < Real.log (orbit t k) := by
  have h4 : 4 ≤ k := (le_max_left _ _).trans hk
  have hN : N+1 ≤ k := (le_max_right _ _).trans hk
  have hexp (j : ℕ) (hj : 4 ≤ j) : 4*j ≤ 2^j := by
    induction j, hj using Nat.le_induction with
    | base => decide
    | succ j hj ih => rw [pow_succ]; omega
  have h2 : 2 * ((N+k : ℕ) : ℝ) < (2:ℝ)^k := by
    exact_mod_cast (show 2 * (N+k) < 2^k from by have := hexp k h4; omega)
  have h3 : (3 : ℝ) < (2:ℝ)^k := by
    exact_mod_cast (show 3 < 2^k from by have := hexp k h4; omega)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlo := normalized_mono (t := t) (by linarith) (Nat.zero_le k)
  change normalized t 0 ≤ normalized t k at hlo
  simp only [normalized, orbit, pow_zero, div_one] at hlo
  have hbase := (le_div_iff₀ (show 0 < (2:ℝ)^k by positivity)).1 hlo
  have htlog : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hbound : (2:ℝ)^k * Real.log 2 ≤ Real.log (orbit t k) := by
    calc
      _ ≤ (2 : ℝ) ^ k * Real.log t := mul_le_mul_of_nonneg_left htlog (by positivity)
      _ = Real.log t * (2 : ℝ) ^ k := mul_comm _ _
      _ ≤ _ := hbase
  constructor
  · have hx : Real.log (2^3 : ℝ) < Real.log (orbit t k) := by
      rw [Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      exact (mul_lt_mul_of_pos_right h3 hlog2).trans_le hbound
    exact lt_of_not_ge (fun hn => by
      have := Real.log_le_log (by have := one_le_orbit (t := t) (by linarith) k; linarith) hn
      norm_num at hx
      linarith)
  · exact (mul_lt_mul_of_pos_right h2 hlog2).trans_le hbound

/-- The uniform scaling inequality used after at most `n` denominator deletions
in the strictly increasing convention. -/
theorem deletion_scaling {t : ℝ} {r n : ℕ} (ht : 8 < t) (hr : r ≤ n)
    (hg : 2 * (n : ℝ) * Real.log 2 < Real.log t) :
    1 ≤ t / 2^r ∧ value t ≤ 2^r * value (t / 2^r) := by
  have hpos : 0 < t := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log (t / 2^r) = Real.log t - (r:ℝ)*Real.log 2 := by
    rw [Real.log_div hpos.ne' (by positivity), Real.log_pow]
  have hhalf : Real.log t / 2 < Real.log (t / 2^r) := by
    rw [hlog]
    have hnr : (r:ℝ) ≤ (n : ℝ) := by exact_mod_cast hr
    nlinarith only [mul_le_mul_of_nonneg_right hnr hlog2.le, hg]
  have h8 : 3 * Real.log 2 < Real.log t := by
    have h := Real.log_lt_log (by norm_num : (0:ℝ) < 2^3) (show (2:ℝ)^3 < t by norm_num; exact ht)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have h1 : 1 ≤ t / 2^r := by
    by_contra! h
    have hz := Real.log_nonpos (by positivity : 0 ≤ t / 2^r) h.le
    linarith
  refine ⟨h1, ?_⟩
  have hlo := log_le_value h1
  have hhi := value_le_log_add (t := t) (by linarith)
  rcases r with _ | r
  · simp
  rcases r with _ | r
  · norm_num only [pow_one] at hlog hlo ⊢
    norm_num at hlog
    linarith
  · have hp : (4:ℝ) ≤ 2^(r+2) := by
      rw [pow_add]
      norm_num
      nlinarith [one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num) (n := r)]
    have hnn : 0 ≤ value (t / 2^(r+2)) := value_nonneg h1
    nlinarith [mul_le_mul_of_nonneg_right hp hnn]

end Egyptian.Payoff

namespace Egyptian

/-- Casting the integer unit-denominator recurrence gives the real payoff orbit. -/
theorem real_unitIter (T j : ℕ) : (unitIter T j : ℝ) = Payoff.orbit (T : ℝ) j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [unitIter, Payoff.orbit, Payoff.phi, ih]

end Egyptian
