/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

module

public import LeanPool.GrahamLPT.Defs
import LeanPool.GrahamLPT.Basic
import LeanPool.GrahamLPT.Certificates
import LeanPool.GrahamLPT.Key
import LeanPool.GrahamLPT.TightLPT
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity.Finset

/-!
# Equality

The necessity half of Dósa's theorem, sorted form: equality forces `n = 2m + 1` and Graham's
instance up to a positive scale, by counting the jobs of each length on each machine of the two
schedules. Helpers carry the prefix `eq_`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-! ### Counting helpers -/

/-- On a two-element set whose values sum to `s`, the fibers at `x` and at `s − x` have the same
size. -/
theorem eq_card_filter_pair {n : ℕ} (p : Fin n → ℝ) (S : Finset (Fin n)) (s x : ℝ) (hS : S.card = 2)
    (hsum : ∑ j ∈ S, p j = s) :
    (S.filter (fun j => p j = x)).card = (S.filter (fun j => p j = s - x)).card := by
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hS
  rw [Finset.sum_pair huv] at hsum
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_pair huv, Finset.sum_pair huv]
  have h1 : (p u = s - x) = (p v = x) := propext ⟨fun h => by linarith, fun h => by linarith⟩
  have h2 : (p v = s - x) = (p u = x) := propext ⟨fun h => by linarith, fun h => by linarith⟩
  simp only [h1, h2]
  exact add_comm _ _

/-- On a set of constant value `t`, the fiber at `x ≠ t` is empty. -/
theorem eq_card_filter_const {n : ℕ} (p : Fin n → ℝ) (S : Finset (Fin n)) (t x : ℝ)
    (hS : ∀ j ∈ S, p j = t) (hx : x ≠ t) : (S.filter (fun j => p j = x)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j hj h
  exact hx (h ▸ hS j hj)

/-- The jobs of index below `k` number `k`. -/
theorem eq_card_lt {n : ℕ} (k : Fin n) : (univ.filter (fun j : Fin n => (j : ℕ) < k)).card = k := by
  have h : univ.filter (fun j : Fin n => (j : ℕ) < k) = Finset.Iio k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]
  rw [h, Fin.card_Iio]

/-- No job after the critical job: `n = k + 1`. -/
theorem eq_n_eq {n : ℕ} (k : Fin n) (hlast : ∀ j : Fin n, (j : ℕ) ≤ k) : n = (k : ℕ) + 1 := by
  have hk := k.isLt
  by_contra h
  have : (k : ℕ) + 1 ≤ k := hlast ⟨(k : ℕ) + 1, by omega⟩
  omega

/-! ### Step 3: two jobs on every machine before the critical job -/

/-- A set of jobs of index `≤ k` with sum `3t − δ` (`0 < δ`, `0 < t = p k`) has at most two jobs. -/
theorem eq_card_le_two {n : ℕ} (p : Fin n → ℝ) (hanti : Antitone p) (k : Fin n) (t δ : ℝ) (ht : 0
  < t)
    (hδ : 0 < δ) (hpk : p k = t) (S : Finset (Fin n)) (hS : ∀ j ∈ S, (j : ℕ) < (k : ℕ) + 1)
    (hsum : ∑ j ∈ S, p j = 3 * t - δ) : S.card ≤ 2 := by
  by_contra h
  have h3 : (3 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast (show 3 ≤ S.card by omega)
  have h1 := key_card_mul_le_sum p hanti k S hS
  rw [hpk, hsum] at h1
  nlinarith

/-- A set with sum `3t − δ > 0` is nonempty. -/
theorem eq_card_pos {n : ℕ} (p : Fin n → ℝ) (t δ : ℝ) (hδt : δ < t) (ht : 0 < t) (S : Finset (Fin
  n))
    (hsum : ∑ j ∈ S, p j = 3 * t - δ) : 1 ≤ S.card := by
  by_contra h
  have h0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
  rw [h0, Finset.sum_empty] at hsum
  linarith

/-- A set with sum `3t − δ` is not a single job: that job, of length `3t − δ`, would be alone on its
`τ`-machine (every other job is `≥ t > δ`), whose load `3t − δ` is not `3t`. -/
theorem eq_card_ne_one {m n : ℕ} (p : Fin n → ℝ) (t δ : ℝ) (ht : 0 < t) (hδ : 0 < δ) (hδt : δ < t)
    (hpt : ∀ j, t ≤ p j) (τ : Fin n → Fin m)
    (hG : ∀ i, ∑ j ∈ univ.filter (fun j : Fin n => τ j = i), p j = 3 * t) (S : Finset (Fin n))
    (hsum : ∑ j ∈ S, p j = 3 * t - δ) : S.card ≠ 1 := by
  intro h1
  obtain ⟨j₁, rfl⟩ := Finset.card_eq_one.mp h1
  rw [Finset.sum_singleton] at hsum
  have hp0 : ∀ j, 0 ≤ p j := fun j => ht.le.trans (hpt j)
  have hG1 := hG (τ j₁)
  have hsing : univ.filter (fun j : Fin n => τ j = τ j₁) = {j₁} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨by simp, fun j₂ hj₂ => ?_⟩
    by_contra hne
    have hsub : ({j₁, j₂} : Finset (Fin n)) ⊆ univ.filter (fun j : Fin n => τ j = τ j₁) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simp
      · rw [Finset.mem_singleton.mp hx]; exact hj₂
    have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hp0 x)
    rw [Finset.sum_pair (fun h => hne h.symm), hG1] at h2
    have := hpt j₂
    linarith
  rw [hsing, Finset.sum_singleton] at hG1
  linarith

/-- Step 3: every machine holds exactly two jobs before the critical job. -/
theorem eq_card_fiber_two {m n : ℕ} (p : Fin n → ℝ) (hanti : Antitone p) (k : Fin n) (t δ : ℝ) (ht
  : 0 < t)
    (hδ : 0 < δ) (hδt : δ < t) (hpk : p k = t) (hpt : ∀ j, t ≤ p j) (σ : Fin n → Fin m)
    (hF : ∀ i, loadBefore p σ k i = 3 * t - δ) (τ : Fin n → Fin m)
    (hG : ∀ i, ∑ j ∈ univ.filter (fun j : Fin n => τ j = i), p j = 3 * t) (i : Fin m) :
    (univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i)).card = 2 := by
  have hsum : ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i), p j = 3 * t - δ := hF i
  have hS : ∀ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i), (j : ℕ) < (k : ℕ) + 1 := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    omega
  have h1 := eq_card_le_two p hanti k t δ ht hδ hpk _ hS hsum
  have h2 := eq_card_pos p t δ hδt ht _ hsum
  have h3 := eq_card_ne_one p t δ ht hδ hδt hpt τ hG _ hsum
  omega

/-- Step 3: with two jobs on every machine before it, the critical job has index `2m`. -/
theorem eq_val_eq_two_mul {m n : ℕ} (σ : Fin n → Fin m) (k : Fin n)
    (hF2 : ∀ i, (univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i)).card = 2) : (k : ℕ) = 2 * m
      := by
  have h := Finset.card_eq_sum_card_fiberwise (f := σ) (s := univ.filter (fun j : Fin n => (j : ℕ)
    < k))
    (t := univ) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  rw [eq_card_lt] at h
  have h' : ∀ i : Fin m, (univ.filter (fun j : Fin n => (j : ℕ) < k)).filter (fun j => σ j = i) =
      univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i) := fun i => Finset.filter_filter _ _ _
  simp only [h', hF2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  omega

/-! ### Step 4: every job is at most `2t − δ` -/

theorem eq_le_two_t {m n : ℕ} (p : Fin n → ℝ) (hanti : Antitone p) (k : Fin n) (t δ : ℝ) (hδt : δ
  ≤ t)
    (hpk : p k = t) (hlast : ∀ j : Fin n, (j : ℕ) ≤ k) (σ : Fin n → Fin m)
    (hF : ∀ i, loadBefore p σ k i = 3 * t - δ)
    (hF2 : ∀ i, (univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i)).card = 2) (j : Fin n) :
    p j ≤ 2 * t - δ := by
  by_cases hjk : j = k
  · rw [hjk, hpk]; linarith
  · have hjlt : (j : ℕ) < k := lt_of_le_of_ne (hlast j) (fun h => hjk (Fin.ext h))
    obtain ⟨S, hSdef⟩ : ∃ S : Finset (Fin n),
        S = univ.filter (fun j' : Fin n => (j' : ℕ) < k ∧ σ j' = σ j) := ⟨_, rfl⟩
    have hjS : j ∈ S := by
      rw [hSdef]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_true]
      exact hjlt
    have hsum : ∑ j' ∈ S, p j' = 3 * t - δ := by rw [hSdef]; exact hF (σ j)
    have hcard : (S.erase j).card = 1 := by rw [Finset.card_erase_of_mem hjS, hSdef, hF2]
    have h1 := Finset.add_sum_erase S p hjS
    have h2 := key_card_mul_le_sum p hanti k (S.erase j) (fun j' hj' => by
      have := (Finset.mem_erase.mp hj').2
      rw [hSdef] at this
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      omega)
    rw [hcard, hpk] at h2
    simp only [Nat.cast_one, one_mul] at h2
    linarith

/-! ### Step 5: the machines of `τ` -/

/-- A set of jobs with sum `3t`, every job in `[t, 2t − δ]`, holds two jobs, or three jobs of
length `t`. -/
theorem eq_tau_cases {n : ℕ} (p : Fin n → ℝ) (hanti : Antitone p) (k : Fin n) (t δ : ℝ) (ht : 0 < t)
    (hδ : 0 < δ) (hδt : δ ≤ t) (hpk : p k = t) (hlast : ∀ j : Fin n, (j : ℕ) ≤ k) (hpt : ∀ j, t ≤
      p j)
    (hle : ∀ j, p j ≤ 2 * t - δ) (S : Finset (Fin n)) (hsum : ∑ j ∈ S, p j = 3 * t) :
    S.card = 2 ∨ (S.card = 3 ∧ ∀ j ∈ S, p j = t) := by
  have h3 : S.card ≤ 3 := by
    by_contra h
    have h4 : (4 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast (show 4 ≤ S.card by omega)
    have h1 := key_card_mul_le_sum p hanti k S (fun j _ => by have := hlast j; omega)
    rw [hpk, hsum] at h1
    nlinarith
  have h2 : 2 ≤ S.card := by
    by_contra h
    have hc : (S.card : ℝ) ≤ 1 := by exact_mod_cast (show S.card ≤ 1 by omega)
    have h1 := Finset.sum_le_card_nsmul S p (2 * t - δ) (fun j _ => hle j)
    rw [hsum, nsmul_eq_mul] at h1
    have h0 : (0 : ℝ) ≤ 2 * t - δ := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hc h0]
  rcases Nat.lt_or_ge S.card 3 with h | h
  · left; omega
  · right
    have hc3 : S.card = 3 := by omega
    refine ⟨hc3, ?_⟩
    have hz : ∑ j ∈ S, (p j - t) = 0 := by
      rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, hc3, nsmul_eq_mul]
      push_cast; ring
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.mpr (hpt j))).mp hz
    intro j hj
    linarith [this j hj]

/-- `2m + 1` jobs on `m` machines, at most three each: some machine holds three. -/
theorem eq_exists_three {m n : ℕ} (τ : Fin n → Fin m) (hn : n = 2 * m + 1)
    (hle : ∀ i, (univ.filter (fun j : Fin n => τ j = i)).card ≤ 3) :
    ∃ i, (univ.filter (fun j : Fin n => τ j = i)).card = 3 := by
  by_contra h
  push Not at h
  have h2 : ∀ i, (univ.filter (fun j : Fin n => τ j = i)).card ≤ 2 := fun i => by
    have := hle i; have := h i; omega
  have hs := Finset.card_eq_sum_card_fiberwise (f := τ) (s := (univ : Finset (Fin n))) (t := univ)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  rw [Finset.card_univ, Fintype.card_fin] at hs
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin m))) => h2 i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

/-! ### Step 6: the counts -/

/-- The jobs of length `x`: those before `k`, plus `k` itself when `p k = x`. -/
theorem eq_count_split {n : ℕ} (p : Fin n → ℝ) (k : Fin n) (hlast : ∀ j : Fin n, (j : ℕ) ≤ k) (x :
  ℝ) :
    (univ.filter (fun j => p j = x)).card =
      ((univ.filter (fun j : Fin n => (j : ℕ) < k)).filter (fun j => p j = x)).card +
        if p k = x then 1 else 0 := by
  have hJ : (univ : Finset (Fin n)).erase k = univ.filter (fun j : Fin n => (j : ℕ) < k) := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_filter, true_and, ne_eq,
      Fin.ext_iff]
    have := hlast j
    omega
  rw [Finset.card_filter, Finset.card_filter, ← Finset.add_sum_erase univ _ (Finset.mem_univ k), hJ,
    add_comm]

/-- The first count symmetry: summed over the machines of `σ`, each holding two jobs of total `A`
before `k`,
the jobs before `k` of length `x` and of length `A − x` are equally many. -/
theorem eq_count_sigma {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (k : Fin n) (A : ℝ)
    (hF : ∀ i, ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i), p j = A)
    (hF2 : ∀ i, (univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i)).card = 2) (x : ℝ) :
    ((univ.filter (fun j : Fin n => (j : ℕ) < k)).filter (fun j => p j = x)).card =
      ((univ.filter (fun j : Fin n => (j : ℕ) < k)).filter (fun j => p j = A - x)).card := by
  have key : ∀ y : ℝ, ((univ.filter (fun j : Fin n => (j : ℕ) < k)).filter (fun j => p j =
    y)).card =
      ∑ i : Fin m, ((univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i)).filter (fun j => p j =
        y)).card := by
    intro y
    rw [Finset.card_eq_sum_card_fiberwise (f := σ) (t := univ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [key, key]
  exact Finset.sum_congr rfl fun i _ => eq_card_filter_pair p _ A x (hF2 i) (hF i)

/-- The second count symmetry: summed over the machines of `τ`, each holding two jobs of total
`3t` or three
jobs of length `t`, the jobs of length `x` and of length `3t − x` are equally many when `x ≠ t,
2t`. -/
theorem eq_count_tau {m n : ℕ} (p : Fin n → ℝ) (τ : Fin n → Fin m) (t : ℝ)
    (hG : ∀ i, ∑ j ∈ univ.filter (fun j : Fin n => τ j = i), p j = 3 * t)
    (hGc : ∀ i, (univ.filter (fun j : Fin n => τ j = i)).card = 2 ∨
      ∀ j ∈ univ.filter (fun j : Fin n => τ j = i), p j = t) (x : ℝ) (hx : x ≠ t) (hx2 : x ≠ 2 *
        t) :
    (univ.filter (fun j => p j = x)).card = (univ.filter (fun j => p j = 3 * t - x)).card := by
  have key : ∀ y : ℝ, (univ.filter (fun j => p j = y)).card =
      ∑ i : Fin m, ((univ.filter (fun j : Fin n => τ j = i)).filter (fun j => p j = y)).card := by
    intro y
    rw [Finset.card_eq_sum_card_fiberwise (f := τ) (t := univ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [key, key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases hGc i with h2 | hconst
  · exact eq_card_filter_pair p _ (3 * t) x h2 (hG i)
  · rw [eq_card_filter_const p _ t x hconst hx,
      eq_card_filter_const p _ t (3 * t - x) hconst (by intro h; apply hx2; linarith)]

/-- One step of the chain: the two symmetries carry the count at `t + (i + 1)δ` to the count at `t
+ iδ`. -/
theorem eq_chain_step {m n : ℕ} (p : Fin n → ℝ) (σ τ : Fin n → Fin m) (k : Fin n) (t δ : ℝ) (hδ :
  0 < δ)
    (hmδ : (m : ℝ) * δ = t) (hpk : p k = t) (hlast : ∀ j : Fin n, (j : ℕ) ≤ k)
    (hF : ∀ i, ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i), p j = 3 * t - δ)
    (hF2 : ∀ i, (univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i)).card = 2)
    (hG : ∀ i, ∑ j ∈ univ.filter (fun j : Fin n => τ j = i), p j = 3 * t)
    (hGc : ∀ i, (univ.filter (fun j : Fin n => τ j = i)).card = 2 ∨
      ∀ j ∈ univ.filter (fun j : Fin n => τ j = i), p j = t) (i : ℕ) (hi : i + 1 < m) :
    ((univ.filter (fun j : Fin n => (j : ℕ) < k)).filter (fun j => p j = t + ((i : ℝ) + 1) *
      δ)).card =
      ((univ.filter (fun j : Fin n => (j : ℕ) < k)).filter (fun j => p j = t + (i : ℝ) * δ)).card
        := by
  have hpos : 0 < ((i : ℝ) + 1) * δ := mul_pos (by positivity) hδ
  have hi' : ((i : ℝ) + 1) * δ < t := by
    have h1 : ((i : ℝ) + 1) < m := by exact_mod_cast hi
    have := mul_lt_mul_of_pos_right h1 hδ
    linarith
  have hx1 : t + ((i : ℝ) + 1) * δ ≠ t := by intro h; linarith
  have hx2 : t + ((i : ℝ) + 1) * δ ≠ 2 * t := by intro h; linarith
  have hy1 : 2 * t - ((i : ℝ) + 1) * δ ≠ t := by intro h; linarith
  have e1 := eq_count_split p k hlast (t + ((i : ℝ) + 1) * δ)
  rw [hpk, ite_eq_right hx1.symm, add_zero] at e1
  have e2 := eq_count_tau p τ t hG hGc _ hx1 hx2
  have e3 := eq_count_split p k hlast (3 * t - (t + ((i : ℝ) + 1) * δ))
  rw [hpk, ite_eq_right (by intro h; apply hy1; linarith), add_zero] at e3
  have e4 := eq_count_sigma p σ k (3 * t - δ) hF hF2 (3 * t - (t + ((i : ℝ) + 1) * δ))
  have e5 : 3 * t - δ - (3 * t - (t + ((i : ℝ) + 1) * δ)) = t + (i : ℝ) * δ := by ring
  rw [e5] at e4
  rw [← e1, e2, e3, e4]

/-- The chain: every count `c'(t + iδ)`, `i < m`, equals `c'(t)`. -/
theorem eq_chain {m n : ℕ} (p : Fin n → ℝ) (σ τ : Fin n → Fin m) (k : Fin n) (t δ : ℝ) (hδ : 0 < δ)
    (hmδ : (m : ℝ) * δ = t) (hpk : p k = t) (hlast : ∀ j : Fin n, (j : ℕ) ≤ k)
    (hF : ∀ i, ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i), p j = 3 * t - δ)
    (hF2 : ∀ i, (univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i)).card = 2)
    (hG : ∀ i, ∑ j ∈ univ.filter (fun j : Fin n => τ j = i), p j = 3 * t)
    (hGc : ∀ i, (univ.filter (fun j : Fin n => τ j = i)).card = 2 ∨
      ∀ j ∈ univ.filter (fun j : Fin n => τ j = i), p j = t) (i : ℕ) (hi : i < m) :
    ((univ.filter (fun j : Fin n => (j : ℕ) < k)).filter (fun j => p j = t + (i : ℝ) * δ)).card =
      ((univ.filter (fun j : Fin n => (j : ℕ) < k)).filter (fun j => p j = t)).card := by
  induction i with
  | zero => simp only [Nat.cast_zero, zero_mul, add_zero]
  | succ i ih =>
    push_cast
    rw [eq_chain_step p σ τ k t δ hδ hmδ hpk hlast hF hF2 hG hGc i hi]
    exact ih (by omega)

/-- The fibers at `t + iδ`, `i < m`, are disjoint: their union has the summed size. -/
theorem eq_card_biUnion {n : ℕ} (p : Fin n → ℝ) (J : Finset (Fin n)) (m : ℕ) (t δ : ℝ) (hδ : 0 <
  δ) :
    ((Finset.range m).biUnion (fun i => J.filter (fun j => p j = t + (i : ℝ) * δ))).card =
      ∑ i ∈ Finset.range m, (J.filter (fun j => p j = t + (i : ℝ) * δ)).card := by
  apply Finset.card_biUnion
  intro i _ i' _ hne
  change Disjoint _ _
  rw [Finset.disjoint_filter]
  intro j _ h1 h2
  apply hne
  have h3 : (i : ℝ) * δ = (i' : ℝ) * δ := by linarith
  have h4 : (i : ℝ) = i' := mul_right_cancel₀ hδ.ne' h3
  exact_mod_cast h4

/-- Step 6: every fiber at `t + iδ`, `i < m`, has two jobs, and they exhaust the jobs before `k`. -/
theorem eq_step6 {n : ℕ} (p : Fin n → ℝ) (k : Fin n) (m : ℕ) (hm : 0 < m) (t δ : ℝ) (hδ : 0 < δ)
    (hk : (k : ℕ) = 2 * m) (hpk : p k = t) (hlast : ∀ j : Fin n, (j : ℕ) ≤ k)
    (hchain : ∀ i < m, ((univ.filter (fun j : Fin n => (j : ℕ) < k)).filter
      (fun j => p j = t + (i : ℝ) * δ)).card =
      ((univ.filter (fun j : Fin n => (j : ℕ) < k)).filter (fun j => p j = t)).card)
    (h3 : 3 ≤ (univ.filter (fun j => p j = t)).card) :
    (∀ i < m, ((univ.filter (fun j : Fin n => (j : ℕ) < k)).filter
      (fun j => p j = t + (i : ℝ) * δ)).card = 2) ∧
      ∀ j : Fin n, (j : ℕ) < k → ∃ i < m, p j = t + (i : ℝ) * δ := by
  obtain ⟨J, hJ⟩ : ∃ J : Finset (Fin n), J = univ.filter (fun j : Fin n => (j : ℕ) < k) := ⟨_, rfl⟩
  have hJcard : J.card = 2 * m := by rw [hJ, eq_card_lt, hk]
  rw [← hJ] at hchain ⊢
  have hsplit := eq_count_split p k hlast t
  rw [hpk, ite_eq_left rfl, ← hJ] at hsplit
  have hc2 : 2 ≤ (J.filter (fun j => p j = t)).card := by omega
  have hsub : (Finset.range m).biUnion (fun i => J.filter (fun j => p j = t + (i : ℝ) * δ)) ⊆ J :=
    Finset.biUnion_subset.mpr (fun i _ => Finset.filter_subset _ _)
  have hcard := eq_card_biUnion p J m t δ hδ
  have hsum : ∑ i ∈ Finset.range m, (J.filter (fun j => p j = t + (i : ℝ) * δ)).card =
      m * (J.filter (fun j => p j = t)).card := by
    rw [Finset.sum_congr rfl (fun i hi => hchain i (Finset.mem_range.mp hi)), Finset.sum_const,
      Finset.card_range, smul_eq_mul]
  have hle := Finset.card_le_card hsub
  rw [hcard, hsum, hJcard] at hle
  have hct : (J.filter (fun j => p j = t)).card = 2 := by
    have hle' : m * (J.filter (fun j => p j = t)).card ≤ m * 2 := by rw [Nat.mul_comm m 2]; exact
      hle
    have := Nat.le_of_mul_le_mul_left hle' hm
    omega
  have hfib : ∀ i < m, (J.filter (fun j => p j = t + (i : ℝ) * δ)).card = 2 :=
    fun i hi => by rw [hchain i hi, hct]
  refine ⟨hfib, fun j hj => ?_⟩
  have hunion : (Finset.range m).biUnion (fun i => J.filter (fun j => p j = t + (i : ℝ) * δ)) = J :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hsum, hct, hJcard]; omega)
  have hjJ : j ∈ J := by rw [hJ]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hj
  rw [← hunion] at hjJ
  obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hjJ
  exact ⟨i, Finset.mem_range.mp hi, (Finset.mem_filter.mp hji).2⟩

/-! ### Step 7: the function -/

/-- Two antitone functions on `Fin N` with the same fiber sizes are equal: their value lists are
sorted and are
permutations of each other. -/
theorem eq_antitone_eq_of_count {N : ℕ} (f g : Fin N → ℝ) (hf : Antitone f) (hg : Antitone g)
    (h : ∀ x, (univ.filter (fun j => f j = x)).card = (univ.filter (fun j => g j = x)).card) : f =
      g := by
  have hcount : ∀ (h : Fin N → ℝ) (x : ℝ), Multiset.count x (univ.val.map h) =
      (univ.filter (fun j => h j = x)).card := by
    intro h x
    rw [Multiset.count_map, Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr (fun j _ => eq_comm)
  have hms : (univ.val.map f) = (univ.val.map g) := by
    rw [Multiset.ext]
    intro x
    rw [hcount, hcount, h]
  rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at hms
  exact List.ofFn_injective (List.Perm.eq_of_sortedGE hf.sortedGE_ofFn hg.sortedGE_ofFn hms)

theorem eq_cast_iff (m q i : ℕ) : (2 * (m : ℝ) - 1 - (q : ℝ) = (m : ℝ) + i) ↔ q + 1 + i = m := by
  constructor
  · intro h
    have : (q : ℝ) + 1 + i = m := by linarith
    exact_mod_cast this
  · intro h
    have : (q : ℝ) + 1 + i = m := by exact_mod_cast h
    linarith

theorem eq_cast_iff' (m i : ℕ) : ((m : ℝ) = (m : ℝ) + i) ↔ i = 0 := by
  constructor
  · intro h
    have : (i : ℝ) = 0 := by linarith
    exact_mod_cast this
  · intro h
    subst h
    simp

/-- Graham's instance takes the value `m + i`, `i < m`, three times for `i = 0` and twice
otherwise. -/
theorem eq_grahamJobs_fiber (m i : ℕ) (hi : i < m) :
    (univ.filter (fun j : Fin (2 * m + 1) => grahamJobs m j = (m : ℝ) + i)).card =
      if i = 0 then 3 else 2 := by
  by_cases hi0 : i = 0
  · subst hi0
    have hfib : univ.filter (fun j : Fin (2 * m + 1) => grahamJobs m j = (m : ℝ) + (0 : ℕ)) =
        {(⟨2 * m - 2, by omega⟩ : Fin (2 * m + 1)), ⟨2 * m - 1, by omega⟩, ⟨2 * m, by omega⟩} := by
      ext j
      have hj := j.isLt
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton,
        Fin.ext_iff]
      unfold grahamJobs
      split_ifs with h
      · rw [eq_cast_iff]; omega
      · rw [eq_cast_iff']; omega
    rw [hfib, ite_eq_left rfl, Finset.card_insert_of_notMem, Finset.card_pair]
    · simp only [Ne, Fin.ext_iff]; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]; omega
  · have hfib : univ.filter (fun j : Fin (2 * m + 1) => grahamJobs m j = (m : ℝ) + i) =
        {(⟨2 * (m - 1 - i), by omega⟩ : Fin (2 * m + 1)), ⟨2 * (m - 1 - i) + 1, by omega⟩} := by
      ext j
      have hj := j.isLt
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton,
        Fin.ext_iff]
      unfold grahamJobs
      split_ifs with h
      · rw [eq_cast_iff]; omega
      · rw [eq_cast_iff']; omega
    rw [hfib, ite_eq_right hi0, Finset.card_pair]
    simp only [Ne, Fin.ext_iff]; omega

/-- Every value of Graham's instance is `m + i` for some `i < m`. -/
theorem eq_grahamJobs_lattice (m : ℕ) (hm : 1 ≤ m) (j : Fin (2 * m + 1)) :
    ∃ i < m, grahamJobs m j = (m : ℝ) + i := by
  have hj := j.isLt
  by_cases h : (j : ℕ) < 2 * m
  · refine ⟨m - 1 - (j : ℕ) / 2, by omega, ?_⟩
    rw [tg_grahamJobs_apply_lt m j h, eq_cast_iff]
    omega
  · refine ⟨0, hm, ?_⟩
    rw [tg_grahamJobs_apply_last m j (by omega), eq_cast_iff']

/-- The fiber sizes of `p` and of `δ · grahamJobs m` agree at every real `x`. -/
theorem eq_count_eq {m : ℕ} (hm : 0 < m) (p : Fin (2 * m + 1) → ℝ) (k : Fin (2 * m + 1)) (t δ : ℝ)
    (hδ : 0 < δ) (hmδ : (m : ℝ) * δ = t) (hpk : p k = t) (hlast : ∀ j : Fin (2 * m + 1), (j : ℕ) ≤
      k)
    (hfib : ∀ i < m, ((univ.filter (fun j : Fin (2 * m + 1) => (j : ℕ) < k)).filter
      (fun j => p j = t + (i : ℝ) * δ)).card = 2)
    (hlat : ∀ j : Fin (2 * m + 1), (j : ℕ) < k → ∃ i < m, p j = t + (i : ℝ) * δ) (x : ℝ) :
    (univ.filter (fun j => p j = x)).card =
      (univ.filter (fun j : Fin (2 * m + 1) => δ * grahamJobs m j = x)).card := by
  have hscale : ∀ i : ℕ, t + (i : ℝ) * δ = δ * ((m : ℝ) + i) := fun i => by rw [← hmδ]; ring
  have hg : ∀ i : ℕ, (univ.filter (fun j : Fin (2 * m + 1) =>
      δ * grahamJobs m j = δ * ((m : ℝ) + i))).card =
      (univ.filter (fun j : Fin (2 * m + 1) => grahamJobs m j = (m : ℝ) + i)).card := by
    intro i
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact mul_right_inj' hδ.ne'
  by_cases hx : ∃ i < m, x = t + (i : ℝ) * δ
  · obtain ⟨i, hi, rfl⟩ := hx
    rw [eq_count_split p k hlast, hfib i hi, hpk, hscale, hg, eq_grahamJobs_fiber m i hi]
    by_cases hi0 : i = 0
    · subst hi0
      rw [ite_eq_left (by rw [← hmδ]; push_cast; ring), ite_eq_left rfl]
    · have hne : t ≠ δ * ((m : ℝ) + i) := by
        intro h
        have h1 : (i : ℝ) * δ = 0 := by rw [← hmδ] at h; linarith
        rcases mul_eq_zero.mp h1 with h2 | h2
        · exact hi0 (by exact_mod_cast h2)
        · exact hδ.ne' h2
      rw [ite_eq_right hne, ite_eq_right hi0]
  · push Not at hx
    have h1 : univ.filter (fun j => p j = x) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro j _ hj
      rcases lt_or_eq_of_le (hlast j) with hlt | heq
      · obtain ⟨i, hi, hji⟩ := hlat j hlt
        exact hx i hi (by rw [← hj, hji])
      · have hjk : j = k := Fin.ext heq
        rw [hjk, hpk] at hj
        exact hx 0 hm (by rw [← hj]; simp)
    have h2 : univ.filter (fun j : Fin (2 * m + 1) => δ * grahamJobs m j = x) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro j _ hj
      obtain ⟨i, hi, hji⟩ := eq_grahamJobs_lattice m hm j
      rw [hji, ← hscale] at hj
      exact hx i hi hj.symm
    rw [h1, h2]

/-- Dósa's theorem (2004), the sorted form: a list schedule of a nonempty nonincreasing positive
`p` on `m ≥ 2` machines
attains Graham's bound against the optimum only for Graham's instance: then `n = 2m + 1` and `p`
is a positive
multiple of `grahamJobs m`. -/
theorem graham_of_listSchedule_eq_bound_internal {m n : ℕ} [NeZero m] (hm : 2 ≤ m) (hn : 0 < n) (p
  : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hanti : Antitone p) (σ : Fin n → Fin m) (hσ : IsListSchedule p σ)
    (heq : 3 * m * makespan p σ = (4 * m - 1) * optMakespan m p) :
    ∃ (a : ℝ) (h : n = 2 * m + 1), 0 < a ∧ ∀ j, p j = a * grahamJobs m (Fin.cast h j) := by
  have hm0 : 0 < m := NeZero.pos m
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp0 : ∀ j, 0 ≤ p j := fun j => (hp j).le
  -- Step 1: the optimum and the critical job
  obtain ⟨τ, hτ⟩ := exists_makespan_eq_optMakespan_internal (m := m) p
  rw [← hτ] at heq
  have hT : 0 < makespan p τ :=
    lt_of_lt_of_le (hp ⟨0, hn⟩) (le_makespan_of_nonneg_internal p hp0 τ ⟨0, hn⟩)
  have hCT : makespan p τ < makespan p σ := by
    by_contra h
    push Not at h
    have h1 : 3 * (m : ℝ) * makespan p σ ≤ 3 * m * makespan p τ :=
      mul_le_mul_of_nonneg_left h (by positivity)
    nlinarith [mul_pos (sub_pos.mpr (by linarith : (1 : ℝ) < m)) hT]
  obtain ⟨i₀, hi₀⟩ := bs_exists_load_eq_makespan p σ
  have hex : ∃ j, σ j = i₀ := by
    by_contra h
    push Not at h
    rw [bs_load_eq_zero p σ i₀ h] at hi₀
    linarith
  obtain ⟨k, hk, hload⟩ := bs_exists_last_job p σ i₀ hex
  have hk' : makespan p σ = loadBefore p σ k (σ k) + p k := by rw [← hi₀, hload, hk]
  -- Step 2: the structure
  obtain ⟨h3, hLB, hloadτ, hzero⟩ := lpt_eq_bound_structure_internal hm p hp0 hanti σ hσ k hk' τ heq
  have hlast : ∀ j : Fin n, (j : ℕ) ≤ k := fun j => by
    by_contra h
    push Not at h
    exact (hp j).ne' (hzero j h)
  obtain ⟨t, hpk⟩ : ∃ t : ℝ, p k = t := ⟨_, rfl⟩
  have ht : 0 < t := hpk ▸ hp k
  obtain ⟨δ, hδ_def⟩ : ∃ δ : ℝ, δ = t / m := ⟨_, rfl⟩
  have hmR0 : (0 : ℝ) < m := by linarith
  have hδ : 0 < δ := by rw [hδ_def]; exact div_pos ht hmR0
  have hmδ : (m : ℝ) * δ = t := by rw [hδ_def]; field_simp
  have hδt : δ < t := by
    rw [hδ_def, div_lt_iff₀ hmR0]
    nlinarith
  rw [hpk] at h3
  rw [hk', hpk, ← h3] at heq
  have hL : loadBefore p σ k (σ k) = 3 * t - δ := by
    have e : (m : ℝ) * loadBefore p σ k (σ k) = 3 * m * t - t := by linear_combination (1 / 3 : ℝ)
      * heq
    have e' : (m : ℝ) * loadBefore p σ k (σ k) = (m : ℝ) * (3 * t - δ) := by
      rw [mul_sub, hmδ]; linear_combination e
    exact mul_left_cancel₀ hmR0.ne' e'
  have hpt : ∀ j, t ≤ p j := fun j => hpk ▸ hanti (Fin.le_iff_val_le_val.mpr (hlast j))
  have hF : ∀ i, loadBefore p σ k i = 3 * t - δ := fun i => by rw [hLB i, hL]
  have hFsum : ∀ i, ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i), p j = 3 * t - δ :=
    fun i => hF i
  have hG : ∀ i, ∑ j ∈ univ.filter (fun j : Fin n => τ j = i), p j = 3 * t := fun i => by
    rw [h3]; exact hloadτ i
  -- Steps 3–5
  have hF2 := eq_card_fiber_two p hanti k t δ ht hδ hδt hpk hpt σ hF τ hG
  have hk2 : (k : ℕ) = 2 * m := eq_val_eq_two_mul σ k hF2
  have hn' : n = 2 * m + 1 := by rw [eq_n_eq k hlast, hk2]
  have hle : ∀ j, p j ≤ 2 * t - δ := eq_le_two_t p hanti k t δ hδt.le hpk hlast σ hF hF2
  have hcases := fun i => eq_tau_cases p hanti k t δ ht hδ hδt.le hpk hlast hpt hle _ (hG i)
  have hGc : ∀ i, (univ.filter (fun j : Fin n => τ j = i)).card = 2 ∨
      ∀ j ∈ univ.filter (fun j : Fin n => τ j = i), p j = t := fun i => (hcases i).imp_right
        And.right
  have hle3 : ∀ i, (univ.filter (fun j : Fin n => τ j = i)).card ≤ 3 := fun i => by
    rcases hcases i with h | h
    · omega
    · omega
  obtain ⟨i₃, hi₃⟩ := eq_exists_three τ hn' hle3
  have hconst : ∀ j ∈ univ.filter (fun j : Fin n => τ j = i₃), p j = t := by
    rcases hcases i₃ with h | h
    · omega
    · exact h.2
  have h3c : 3 ≤ (univ.filter (fun j => p j = t)).card := by
    rw [← hi₃]
    exact Finset.card_le_card (fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hconst j hj⟩)
  -- Step 6
  have hchain := fun i hi => eq_chain p σ τ k t δ hδ hmδ hpk hlast hFsum hF2 hG hGc i hi
  obtain ⟨hfib, hlat⟩ := eq_step6 p k m hm0 t δ hδ hk2 hpk hlast hchain h3c
  -- Step 7
  subst hn'
  refine ⟨δ, rfl, hδ, fun j => ?_⟩
  simp only [Fin.cast_refl, id]
  have hcount := eq_count_eq hm0 p k t δ hδ hmδ hpk hlast hfib hlat
  have hg_anti : Antitone (fun j => δ * grahamJobs m j) := fun a b hab =>
    mul_le_mul_of_nonneg_left (grahamJobs_antitone_internal m hab) hδ.le
  exact congrFun (eq_antitone_eq_of_count p (fun j => δ * grahamJobs m j) hanti hg_anti hcount) j

end GrahamLPT
