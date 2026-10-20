/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

module

public import LeanPool.GrahamLPT.Defs
public import Mathlib.Data.Fin.VecNotation
import LeanPool.GrahamLPT.Basic
import LeanPool.GrahamLPT.Certificates
import LeanPool.GrahamLPT.CoffmanSethi
import LeanPool.GrahamLPT.Counter
import LeanPool.GrahamLPT.Equality
import LeanPool.GrahamLPT.FixedCount
import LeanPool.GrahamLPT.GrahamScaled
import LeanPool.GrahamLPT.Key
import LeanPool.GrahamLPT.LPTBound
import LeanPool.GrahamLPT.LPTForm
import LeanPool.GrahamLPT.ListBound
import LeanPool.GrahamLPT.ListOptimum
import LeanPool.GrahamLPT.OptList
import LeanPool.GrahamLPT.Ratio
import LeanPool.GrahamLPT.TightLPT
import LeanPool.GrahamLPT.TightList
import Mathlib.Tactic.Positivity.Finset

/-!
# Scheduling theorem contracts

The named results of the upstream formalization, proved using the internal library.
The definitions and all theorem statements are preserved from that development.
-/

@[expose] public section

namespace GrahamLPT

open Finset

theorem exists_isListSchedule {m n : ℕ} [NeZero m] (p : Fin n → ℝ) :
    ∃ σ : Fin n → Fin m, IsListSchedule p σ :=
  exists_isListSchedule_internal p

theorem exists_isLPTSchedule {m n : ℕ} [NeZero m] (p : Fin n → ℝ) :
    ∃ σ : Fin n → Fin m, IsLPTSchedule p σ :=
  exists_isLPTSchedule_internal p

theorem optMakespan_le {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (τ : Fin n → Fin m) :
    optMakespan m p ≤ makespan p τ :=
  optMakespan_le_internal p τ

theorem exists_makespan_eq_optMakespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) :
    ∃ τ : Fin n → Fin m, makespan p τ = optMakespan m p :=
  exists_makespan_eq_optMakespan_internal p

theorem load_le_makespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (σ : Fin n → Fin m) (i : Fin m) :
    load p σ i ≤ makespan p σ :=
  load_le_makespan_internal p σ i

theorem le_makespan_of_nonneg {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (j : Fin n) : p j ≤ makespan p σ :=
  le_makespan_of_nonneg_internal p hp σ j

theorem sum_le_mul_makespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (σ : Fin n → Fin m) :
    ∑ j, p j ≤ (m : ℝ) * makespan p σ :=
  sum_le_mul_makespan_internal p σ

theorem makespan_comp {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (σ : Fin n → Fin m) (π : Equiv.Perm
  (Fin n)) :
    makespan (p ∘ π) (σ ∘ π) = makespan p σ :=
  makespan_comp_internal p σ π

theorem listSchedule_bound {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (τ : Fin n → Fin m) :
    (m : ℝ) * makespan p σ ≤ (2 * m - 1) * makespan p τ :=
  listSchedule_bound_internal p hp σ hσ τ

theorem listSchedule_le_optMakespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) :
    makespan p σ ≤ (2 - 1 / m) * optMakespan m p :=
  listSchedule_le_optMakespan_internal p hp σ hσ

theorem unitJobs_optMakespan (m : ℕ) [NeZero m] : optMakespan m (unitJobs m) = m :=
  unitJobs_optMakespan_internal m

theorem unitJobs_listSchedule_makespan (m : ℕ) [NeZero m] (σ : Fin (m * (m - 1) + 1) → Fin m)
    (hσ : IsListSchedule (unitJobs m) σ) : makespan (unitJobs m) σ = 2 * m - 1 :=
  unitJobs_listSchedule_makespan_internal m σ hσ

theorem isLeast_listSchedule_ratio (m : ℕ) [NeZero m] :
    IsLeast {c : ℝ | ∀ (n : ℕ) (p : Fin n → ℝ) (σ τ : Fin n → Fin m), (∀ j, 0 ≤ p j) →
      IsListSchedule p σ → makespan p σ ≤ c * makespan p τ} (2 - 1 / m) :=
  isLeast_listSchedule_ratio_internal m

theorem lpt_bound {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) (τ : Fin n → Fin m) :
    3 * (m : ℝ) * makespan p σ ≤ (4 * m - 1) * makespan p τ :=
  lpt_bound_internal p hp σ hσ τ

theorem lpt_le_optMakespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) :
    makespan p σ ≤ (4 / 3 - 1 / (3 * m)) * optMakespan m p :=
  lpt_le_optMakespan_internal p hp σ hσ

theorem lpt_optimal_of_third_lt {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) (τ : Fin n → Fin m)
    (h : ∀ j, makespan p τ < 3 * p j) : makespan p σ ≤ makespan p τ :=
  lpt_optimal_of_third_lt_internal p hp σ hσ τ h

theorem lpt_eq_optMakespan_of_third_lt {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) (h : ∀ j, optMakespan m p < 3 * p j) :
    makespan p σ = optMakespan m p :=
  lpt_eq_optMakespan_of_third_lt_internal p hp σ hσ h

theorem grahamJobs_antitone (m : ℕ) : Antitone (grahamJobs m) :=
  grahamJobs_antitone_internal m

theorem grahamJobs_optMakespan (m : ℕ) [NeZero m] : optMakespan m (grahamJobs m) = 3 * m :=
  grahamJobs_optMakespan_internal m

theorem grahamOrder_bijective (m : ℕ) : Function.Bijective (grahamOrder m) :=
  grahamOrder_bijective_internal m

theorem grahamJobs_grahamOrder (m : ℕ) (i : Fin (2 * m + 1)) :
    grahamJobs m (grahamOrder m i) =
      if (i : ℕ) < m - 1 then 2 * (m : ℝ) - 1 - ((i : ℕ) : ℝ)
      else if (i : ℕ) ≤ m then (m : ℝ)
      else if (i : ℕ) < 2 * m then 3 * (m : ℝ) - ((i : ℕ) : ℝ)
      else (m : ℝ) :=
  grahamJobs_grahamOrder_internal m i

theorem grahamJobs_exists_optimal_listSchedule (m : ℕ) [NeZero m] :
    ∃ σ : Fin (2 * m + 1) → Fin m,
      IsListSchedule (grahamJobs m ∘ grahamOrder m) (σ ∘ grahamOrder m) ∧ makespan (grahamJobs m)
        σ = 3 * m :=
  grahamJobs_exists_optimal_listSchedule_internal m

theorem grahamJobs_lpt_makespan (m : ℕ) [NeZero m] (σ : Fin (2 * m + 1) → Fin m)
    (hσ : IsLPTSchedule (grahamJobs m) σ) : makespan (grahamJobs m) σ = 4 * m - 1 :=
  grahamJobs_lpt_makespan_internal m σ hσ

theorem isLeast_lpt_ratio (m : ℕ) [NeZero m] :
    IsLeast {c : ℝ | ∀ (n : ℕ) (p : Fin n → ℝ) (σ τ : Fin n → Fin m), (∀ j, 0 ≤ p j) →
      IsLPTSchedule p σ → makespan p σ ≤ c * makespan p τ} (4 / 3 - 1 / (3 * m)) :=
  isLeast_lpt_ratio_internal m

theorem exists_listSchedule_le {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (τ : Fin n
  → Fin m) :
    ∃ (π : Equiv.Perm (Fin n)) (σ : Fin n → Fin m),
      IsListSchedule (p ∘ π) (σ ∘ π) ∧ makespan p σ ≤ makespan p τ :=
  exists_listSchedule_le_internal p hp τ

theorem isLeast_listSchedule_makespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) :
    IsLeast ((fun σ : Fin n → Fin m => makespan p σ) ''
      {σ | ∃ π : Equiv.Perm (Fin n), IsListSchedule (p ∘ π) (σ ∘ π)}) (optMakespan m p) :=
  isLeast_listSchedule_makespan_internal p hp

theorem nine_five_four_lpt_thirteen :
    IsLPTSchedule (![9, 5, 5, 4, 4, 4] : Fin 6 → ℝ) (![0, 1, 2, 1, 2, 0] : Fin 6 → Fin 3) ∧
      makespan (![9, 5, 5, 4, 4, 4] : Fin 6 → ℝ) (![0, 1, 2, 1, 2, 0] : Fin 6 → Fin 3) = 13 :=
  nine_five_four_lpt_thirteen_internal

theorem nine_five_four_optMakespan : optMakespan 3 (![9, 5, 5, 4, 4, 4] : Fin 6 → ℝ) = 12 :=
  nine_five_four_optMakespan_internal

theorem lpt_third_le_not_optimal :
    ∃ (p : Fin 6 → ℝ) (σ : Fin 6 → Fin 3), (∀ j, 0 ≤ p j) ∧ IsLPTSchedule p σ ∧
      (∀ j, optMakespan 3 p ≤ 3 * p j) ∧ optMakespan 3 p < makespan p σ :=
  lpt_third_le_not_optimal_internal

theorem lpt_job_position_le {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (hanti :
  Antitone p)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (k : Fin n) (τ : Fin n → Fin m) :
    (((univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = σ k)).card : ℝ) + 1) * p k ≤ makespan p τ
      :=
  lpt_job_position_le_internal p hp hanti σ hσ k τ

theorem lpt_bound_of_card {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) (τ : Fin n → Fin m) (i : Fin m)
    (hi : load p σ i = makespan p σ) :
    ((univ.filter (fun j : Fin n => σ j = i)).card : ℝ) * m * makespan p σ ≤
      (((univ.filter (fun j : Fin n => σ j = i)).card + 1) * m - 1) * makespan p τ :=
  lpt_bound_of_card_internal p hp σ hσ τ i hi

theorem lpt_critical_min_le {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (hanti :
  Antitone p)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (k : Fin n) (hk : makespan p σ = loadBefore p σ
      k (σ k) + p k)
    (τ : Fin n → Fin m) : min (makespan p σ) (3 * p k) ≤ makespan p τ :=
  lpt_critical_min_le_internal p hp hanti σ hσ k hk τ

theorem lpt_eq_optMakespan_of_critical_third {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p
  j)
    (hanti : Antitone p) (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (k : Fin n)
    (hk : makespan p σ = loadBefore p σ k (σ k) + p k) (h3 : makespan p σ ≤ 3 * p k) :
    makespan p σ = optMakespan m p :=
  lpt_eq_optMakespan_of_critical_third_internal p hp hanti σ hσ k hk h3

theorem lpt_eq_bound_structure {m n : ℕ} [NeZero m] (hm : 2 ≤ m) (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hanti : Antitone p) (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (k : Fin n)
    (hk : makespan p σ = loadBefore p σ k (σ k) + p k) (τ : Fin n → Fin m)
    (heq : 3 * m * makespan p σ = (4 * m - 1) * makespan p τ) :
    3 * p k = makespan p τ ∧ (∀ i, loadBefore p σ k i = loadBefore p σ k (σ k)) ∧
      (∀ i, load p τ i = makespan p τ) ∧ ∀ j : Fin n, (k : ℕ) < j → p j = 0 :=
  lpt_eq_bound_structure_internal hm p hp hanti σ hσ k hk τ heq

theorem lpt_bound_of_other_card {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (hanti :
  Antitone p)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (k : Fin n) (hk : makespan p σ = loadBefore p σ
      k (σ k) + p k)
    (i : Fin m) (hi : i ≠ σ k) (q : ℕ) (hq : q ≤ (univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j
      = i)).card)
    (hqm : q + 2 ≤ m) (τ : Fin n → Fin m) :
    (q : ℝ) * (m - 1) * makespan p σ ≤ ((q + 1) * (m - 1) - 1) * makespan p τ :=
  lpt_bound_of_other_card_internal p hp hanti σ hσ k hk i hi q hq hqm τ

theorem lpt_eq_bound_of_graham {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (a : ℝ) (ha : 0 < a)
    (e : Fin n ≃ Fin (2 * m + 1)) (he : ∀ j, p j = a * grahamJobs m (e j)) (σ : Fin n → Fin m)
    (hσ : IsLPTSchedule p σ) : 3 * m * makespan p σ = (4 * m - 1) * optMakespan m p :=
  lpt_eq_bound_of_graham_internal p a ha e he σ hσ

theorem graham_of_listSchedule_eq_bound {m n : ℕ} [NeZero m] (hm : 2 ≤ m) (hn : 0 < n) (p : Fin n
  → ℝ)
    (hp : ∀ j, 0 < p j) (hanti : Antitone p) (σ : Fin n → Fin m) (hσ : IsListSchedule p σ)
    (heq : 3 * m * makespan p σ = (4 * m - 1) * optMakespan m p) :
    ∃ (a : ℝ) (h : n = 2 * m + 1), 0 < a ∧ ∀ j, p j = a * grahamJobs m (Fin.cast h j) :=
  graham_of_listSchedule_eq_bound_internal hm hn p hp hanti σ hσ heq

theorem graham_of_lpt_eq_bound {m n : ℕ} [NeZero m] (hm : 2 ≤ m) (hn : 0 < n) (p : Fin n → ℝ) (hp
  : ∀ j, 0 < p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) (heq : 3 * m * makespan p σ = (4 * m - 1) *
      optMakespan m p) :
    ∃ (a : ℝ) (e : Fin n ≃ Fin (2 * m + 1)), 0 < a ∧ ∀ j, p j = a * grahamJobs m (e j) :=
  graham_of_lpt_eq_bound_internal hm hn p hp σ hσ heq

theorem lpt_eq_bound_iff_graham {m n : ℕ} [NeZero m] (hm : 2 ≤ m) (hn : 0 < n) (p : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) :
    (∃ σ : Fin n → Fin m, IsLPTSchedule p σ ∧ 3 * m * makespan p σ = (4 * m - 1) * optMakespan m
      p) ↔
      ∃ (a : ℝ) (e : Fin n ≃ Fin (2 * m + 1)), 0 < a ∧ ∀ j, p j = a * grahamJobs m (e j) :=
  lpt_eq_bound_iff_graham_internal hm hn p hp

theorem lpt_lt_bound_of_card_ne {m n : ℕ} [NeZero m] (hm : 2 ≤ m) (hn : 0 < n) (hn' : n ≠ 2 * m + 1)
    (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) :
    3 * m * makespan p σ < (4 * m - 1) * optMakespan m p :=
  lpt_lt_bound_of_card_ne_internal hm hn hn' p hp σ hσ

theorem isLUB_lpt_ratio_of_card {m n : ℕ} [NeZero m] (hn : 2 * m + 1 ≤ n) :
    IsLUB {r : ℝ | ∃ (p : Fin n → ℝ) (σ : Fin n → Fin m), (∀ j, 0 < p j) ∧ IsLPTSchedule p σ ∧
      r = makespan p σ / optMakespan m p} (4 / 3 - 1 / (3 * m)) :=
  isLUB_lpt_ratio_of_card_internal hn

end GrahamLPT
