/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

module

public import LeanPool.GrahamLPT.Defs
import LeanPool.GrahamLPT.Basic
import LeanPool.GrahamLPT.CoffmanSethi
import LeanPool.GrahamLPT.Key
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity.Finset

/-!
# Certificates

The critical job's certificates: the smaller of `C(σ)` and `3 p_k` bounds every comparison
schedule, the observed third certifies optimality, equality in Graham's bound forces its proof's
inequalities to be equalities, and Della Croce–Scatamacchia's Proposition 4 from Chen's property.
Helpers carry the prefix `ct_`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- The key lemma against the makespan of `τ`: when `C(τ) < 3 p_k`, the machine of `k` ends by
`C(τ)`. -/
theorem ct_key_le {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (hanti : Antitone p)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (k : Fin n) (τ : Fin n → Fin m)
    (h3 : makespan p τ < 3 * p k) : loadBefore p σ k (σ k) + p k ≤ makespan p τ :=
  key_lemma p hp hanti σ hσ k τ (makespan p τ)
    (fun i => (bs_loadBefore_le_load p hp τ _ i).trans (load_le_makespan_internal p τ i)) h3

/-- The scalar step of the equality structure for `T > 0`: `L` the least load before `k`, `P =
p_k`, `S` the
length before `k`, `W` the total, `T = C(τ)`; the four inequalities of Graham's proof and equality
in the bound
force `3P = T` and the chain `mL = S`, `S + P = W`, `W = mT`. -/
theorem ct_eq_scalar (m L P S W T : ℝ) (hm : 2 ≤ m) (hT : 0 < T) (h1 : m * L ≤ S) (h2 : S + P ≤ W)
    (h3 : W ≤ m * T) (hkey : T < 3 * P → L + P ≤ T) (heq : 3 * m * (L + P) = (4 * m - 1) * T) :
    3 * P = T ∧ S = m * L ∧ W = S + P ∧ W = m * T := by
  have hm1 : 0 < m - 1 := by linarith
  have hC : T < L + P := by
    by_contra h
    have hle : L + P ≤ T := le_of_not_gt h
    have h4 := mul_le_mul_of_nonneg_left hle (by linarith : (0 : ℝ) ≤ 3 * m)
    have h5 := mul_pos hm1 hT
    nlinarith
  have hP1 : 3 * P ≤ T := by
    by_contra h
    exact absurd (hkey (lt_of_not_ge h)) (not_le_of_gt hC)
  have hP2 : T ≤ 3 * P := by
    by_contra h
    have h4 := mul_pos hm1 (by linarith [lt_of_not_ge h] : 0 < T - 3 * P)
    nlinarith
  have hP : 3 * P = T := le_antisymm hP1 hP2
  refine ⟨hP, ?_, ?_, ?_⟩ <;> nlinarith

/-- The scalar step of Proposition 4: `s` the least load before the critical job, `P` its length,
`s + P` the
makespan of `σ`, `W` the total, `T = C(τ)`; the load count `(m − 1) s + (q + 1) P ≤ W ≤ mT` and
Chen's
`qP ≤ T` give the bound when `q + 2 ≤ m`. -/
theorem ct_other_scalar (m q s P W T : ℝ) (hq : 0 ≤ q) (hmq : q + 2 ≤ m)
    (hwork : (m - 1) * s + (q + 1) * P ≤ W) (htotal : W ≤ m * T) (hsize : q * P ≤ T) :
    q * (m - 1) * (s + P) ≤ ((q + 1) * (m - 1) - 1) * T := by
  have h1 := mul_le_mul_of_nonneg_left (hwork.trans htotal) hq
  have h2 := mul_le_mul_of_nonneg_left hsize (by linarith : (0 : ℝ) ≤ m - q - 2)
  nlinarith

/-- The critical job's certificate: in a list schedule of a nonincreasing `p`, for a job `k` whose
completion time is
the makespan, the smaller of `C(σ)` and `3 p_k` is at most `C(τ)` for every assignment `τ` (the
key lemma read as a
lower bound on every comparison schedule). -/
theorem lpt_critical_min_le_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
  (hanti : Antitone p)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (k : Fin n) (hk : makespan p σ = loadBefore p σ
      k (σ k) + p k)
    (τ : Fin n → Fin m) : min (makespan p σ) (3 * p k) ≤ makespan p τ := by
  rcases le_or_gt (3 * p k) (makespan p τ) with h3 | h3
  · exact (min_le_right _ _).trans h3
  · have hkey := ct_key_le p hp hanti σ hσ k τ h3
    rw [← hk] at hkey
    exact (min_le_left _ _).trans hkey

/-- The observed-third certificate: in a list schedule of a nonincreasing `p`, when a critical job
`k` is at least a
third of the makespan it completes, the schedule is optimal (`lpt_eq_optMakespan_of_third_lt` asks
every job to exceed
a third of the unknown optimum). -/
theorem lpt_eq_optMakespan_of_critical_third_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀
  j, 0 ≤ p j)
    (hanti : Antitone p) (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (k : Fin n)
    (hk : makespan p σ = loadBefore p σ k (σ k) + p k) (h3 : makespan p σ ≤ 3 * p k) :
    makespan p σ = optMakespan m p := by
  obtain ⟨τ, hτ⟩ := exists_makespan_eq_optMakespan_internal (m := m) p
  have h := lpt_critical_min_le_internal p hp hanti σ hσ k hk τ
  rw [min_eq_left h3, hτ] at h
  exact le_antisymm h (optMakespan_le_internal p σ)

/-- In a list schedule `σ` of a nonincreasing `p` on `m ≥ 2` machines, with `k` a critical job,
equality in Graham's
LPT bound against `τ` forces the four inequalities of its proof to be equalities: `3 p_k = C(τ)`,
every machine of
`σ` carries the least load before `k`, every machine of `τ` carries exactly `C(τ)`, and every job
after `k` has
length `0`. -/
theorem lpt_eq_bound_structure_internal {m n : ℕ} [NeZero m] (hm : 2 ≤ m) (p : Fin n → ℝ) (hp : ∀
  j, 0 ≤ p j)
    (hanti : Antitone p) (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (k : Fin n)
    (hk : makespan p σ = loadBefore p σ k (σ k) + p k) (τ : Fin n → Fin m)
    (heq : 3 * m * makespan p σ = (4 * m - 1) * makespan p τ) :
    3 * p k = makespan p τ ∧ (∀ i, loadBefore p σ k i = loadBefore p σ k (σ k)) ∧
      (∀ i, load p τ i = makespan p τ) ∧ ∀ j : Fin n, (k : ℕ) < j → p j = 0 := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hT0 : 0 ≤ makespan p τ := bs_makespan_nonneg p hp τ
  rcases hT0.eq_or_lt with hT | hT
  · -- `C(τ) = 0`: then `C(σ) = 0` and every job has length `0`
    have hC0 : makespan p σ = 0 := by
      rw [← hT, mul_zero] at heq
      have h3m : (0 : ℝ) < 3 * m := by linarith
      exact (mul_eq_zero.mp heq).resolve_left h3m.ne'
    have hz : ∀ j, p j = 0 := by
      intro j
      have h := le_makespan_of_nonneg_internal p hp σ j
      rw [hC0] at h
      exact le_antisymm h (hp j)
    refine ⟨?_, ?_, ?_, fun j _ => hz j⟩
    · rw [hz k, ← hT]
      ring
    · intro i
      unfold loadBefore
      rw [Finset.sum_eq_zero (fun j _ => hz j), Finset.sum_eq_zero (fun j _ => hz j)]
    · intro i
      unfold load
      rw [Finset.sum_eq_zero (fun j _ => hz j)]
      exact hT
  · -- `C(τ) > 0`: the scalar step, then each tight inequality read off
    obtain ⟨hP, hS, hW, hWT⟩ := ct_eq_scalar (m : ℝ) (loadBefore p σ k (σ k)) (p k)
      (∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k), p j) (∑ j, p j) (makespan p τ) hm' hT
      (bs_mul_loadBefore_le p σ hσ k) (bs_sum_filter_add_le p hp k) (sum_le_mul_makespan_internal
        p τ)
      (ct_key_le p hp hanti σ hσ k τ) (by rw [← hk]; exact heq)
    refine ⟨hP, ?_, ?_, ?_⟩
    · -- The nonnegative excesses sum to zero.
      have hsum : ∑ i, (loadBefore p σ k i - loadBefore p σ k (σ k)) = 0 := by
        simp only [Finset.sum_sub_distrib, bs_sum_loadBefore, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        linarith
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.2 (hσ k i))).mp hsum
      intro i
      have hi := h i (mem_univ i)
      linarith
    · -- every load of `τ` is its makespan: the slacks are nonnegative and sum to `mT − W = 0`
      have hsum : ∑ i, (makespan p τ - load p τ i) = 0 := by
        simp only [Finset.sum_sub_distrib, bs_sum_load, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin,
          nsmul_eq_mul]
        linarith
      have h := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => sub_nonneg.2 (load_le_makespan_internal p τ i))).mp hsum
      intro i
      have hi := h i (mem_univ i)
      linarith
    · -- every job after `k` has length `0`: `S + P + p_j ≤ W = S + P`
      intro j hj
      have hkA : k ∉ univ.filter (fun j : Fin n => (j : ℕ) < k) := by simp
      have hjA : j ∉ insert k (univ.filter (fun j : Fin n => (j : ℕ) < k)) := by
        simp only [mem_insert, mem_filter, mem_univ, true_and, Fin.ext_iff]
        omega
      have hsub := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ (insert j (insert k (univ.filter (fun j : Fin n => (j : ℕ) < k)))))
        (fun x _ _ => hp x)
      rw [Finset.sum_insert hjA, Finset.sum_insert hkA] at hsub
      exact le_antisymm (by linarith) (hp j)

/-- Della Croce–Scatamacchia's Proposition 4, from Chen's property: in a list schedule `σ` of a
nonincreasing `p`, if a
machine `i` other than the critical job's holds at least `q` jobs before the critical job `k`, and
`q + 2 ≤ m`, then
`q(m − 1) · C(σ) ≤ ((q + 1)(m − 1) − 1) · C(τ)` for every assignment `τ`. -/
theorem lpt_bound_of_other_card_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
  (hanti : Antitone p)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (k : Fin n) (hk : makespan p σ = loadBefore p σ
      k (σ k) + p k)
    (i : Fin m) (hi : i ≠ σ k) (q : ℕ) (hq : q ≤ (univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j
      = i)).card)
    (hqm : q + 2 ≤ m) (τ : Fin n → Fin m) :
    (q : ℝ) * (m - 1) * makespan p σ ≤ ((q + 1) * (m - 1) - 1) * makespan p τ := by
  have hm' : (q : ℝ) + 2 ≤ m := by exact_mod_cast hqm
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hT0 : 0 ≤ makespan p τ := bs_makespan_nonneg p hp τ
  have hqF : (q : ℝ) ≤ (univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i)).card := by
    exact_mod_cast hq
  -- Chen's property at the last of the jobs before `k` on machine `i`: `q · p_k ≤ C(τ)`
  have hqP : (q : ℝ) * p k ≤ makespan p τ := by
    rcases Nat.eq_zero_or_pos q with hq0' | hqpos
    · rw [hq0', Nat.cast_zero, zero_mul]
      exact hT0
    · have hne : (univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i)).Nonempty :=
        Finset.card_pos.mp (by omega)
      obtain ⟨j₀, hj₀F, hj₀max⟩ := Finset.exists_max_image _ (fun j : Fin n => (j : ℕ)) hne
      have hj₀ : (j₀ : ℕ) < k ∧ σ j₀ = i := by simpa using hj₀F
      have eF : univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i) =
          insert j₀ (univ.filter (fun j : Fin n => (j : ℕ) < j₀ ∧ σ j = σ j₀)) := by
        ext j
        simp only [mem_filter, mem_univ, true_and, mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          have h3 : (j : ℕ) ≤ j₀ := hj₀max j (mem_filter.mpr ⟨mem_univ _, h1, h2⟩)
          by_cases hjj : j = j₀
          · exact Or.inl hjj
          · have : (j : ℕ) ≠ j₀ := fun e => hjj (Fin.ext e)
            exact Or.inr ⟨by omega, h2.trans hj₀.2.symm⟩
        · rintro (rfl | ⟨h1, h2⟩)
          · exact hj₀
          · exact ⟨by omega, h2.trans hj₀.2⟩
      have hnot : j₀ ∉ univ.filter (fun j : Fin n => (j : ℕ) < j₀ ∧ σ j = σ j₀) := by simp
      have hcard : ((univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i)).card : ℝ) =
          ((univ.filter (fun j : Fin n => (j : ℕ) < j₀ ∧ σ j = σ j₀)).card : ℝ) + 1 := by
        rw [eF, card_insert_of_notMem hnot]
        push_cast
        ring
      have hchen := lpt_job_position_le_internal p hp hanti σ hσ j₀ τ
      rw [← hcard] at hchen
      have hpk : p k ≤ p j₀ := hanti (Fin.le_iff_val_le_val.mpr hj₀.1.le)
      calc (q : ℝ) * p k ≤ (q : ℝ) * p j₀ := mul_le_mul_of_nonneg_left hpk hq0
        _ ≤ ((univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i)).card : ℝ) * p j₀ :=
          mul_le_mul_of_nonneg_right hqF (hp j₀)
        _ ≤ makespan p τ := hchen
  -- the loads of `σ`: the machine of `k` carries `C(σ)`, machine `i` at least `q · p_k`, the rest
  -- at least `L`
  have hCk : loadBefore p σ k (σ k) + p k ≤ load p σ (σ k) := by
    have h1 := bs_loadBefore_le_load p hp σ (k + 1) (σ k)
    rw [bs_loadBefore_succ, ite_eq_left rfl] at h1
    exact h1
  have hFi : (q : ℝ) * p k ≤ loadBefore p σ k i := by
    have h1 := key_card_mul_le_sum p hanti k (univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i))
      (fun j hj => by simp only [mem_filter, mem_univ, true_and] at hj; omega)
    exact (mul_le_mul_of_nonneg_right hqF (hp k)).trans h1
  have hload_i : (q : ℝ) * p k ≤ load p σ i := hFi.trans (bs_loadBefore_le_load p hp σ k i)
  have hload_other : ∀ i', loadBefore p σ k (σ k) ≤ load p σ i' :=
    fun i' => (hσ k i').trans (bs_loadBefore_le_load p hp σ k i')
  have hpt : ∀ i' : Fin m, loadBefore p σ k (σ k) + (if i' = σ k then p k else 0) +
      (if i' = i then (q : ℝ) * p k - loadBefore p σ k (σ k) else 0) ≤ load p σ i' := by
    intro i'
    by_cases h1 : i' = σ k
    · have h2 : i' ≠ i := fun h => hi (h.symm.trans h1)
      rw [ite_eq_left h1, ite_eq_right h2, add_zero, h1]
      exact hCk
    · rw [ite_eq_right h1, add_zero]
      by_cases h2 : i' = i
      · rw [ite_eq_left h2, h2]
        linarith
      · rw [ite_eq_right h2, add_zero]
        exact hload_other i'
  have hsum : (m : ℝ) * loadBefore p σ k (σ k) + p k + ((q : ℝ) * p k - loadBefore p σ k (σ k)) ≤
    ∑ j, p j := by
    have h := Finset.sum_le_sum (fun i' (_ : i' ∈ (univ : Finset (Fin m))) => hpt i')
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, bs_sum_load] at h
    exact h
  rw [hk]
  exact ct_other_scalar (m : ℝ) q (loadBefore p σ k (σ k)) (p k) (∑ j, p j) (makespan p τ) hq0 hm'
    (by linarith) (sum_le_mul_makespan_internal p τ) hqP

end GrahamLPT
