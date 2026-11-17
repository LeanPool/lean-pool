/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

module

public import LeanPool.GrahamLPT.Defs
import LeanPool.GrahamLPT.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# Key

The key lemma by counting, and the optimality of LPT when every job exceeds a third of the optimum.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- Jobs of index at most `k` are at least `p k` long, so a set of them sums to at least its size
times `p k`. -/
theorem key_card_mul_le_sum {n : ℕ} (p : Fin n → ℝ) (hanti : Antitone p) (k : Fin n) (U : Finset
  (Fin n))
    (hU : ∀ j ∈ U, (j : ℕ) < (k : ℕ) + 1) : (U.card : ℝ) * p k ≤ ∑ j ∈ U, p j := by
  have h : ∑ _j ∈ U, p k ≤ ∑ j ∈ U, p j := by
    apply Finset.sum_le_sum
    intro j hj
    apply hanti
    have := hU j hj
    exact Fin.le_iff_val_le_val.mpr (by omega)
  simpa [Finset.sum_const, nsmul_eq_mul] using h

/-- The counting lemma: `p` nonincreasing and nonnegative, `σ` a list schedule, `τ` any
assignment
whose loads from the jobs of index `≤ k` are at most `T`, and `T < 3 p_k`: then the machine of `k`
ends by `T`. -/
theorem key_lemma {m n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (hanti : Antitone p) (σ : Fin n →
  Fin m)
    (hσ : IsListSchedule p σ) (k : Fin n) (τ : Fin n → Fin m) (T : ℝ)
    (hT : ∀ i, loadBefore p τ (k + 1) i ≤ T) (h3 : T < 3 * p k) :
    loadBefore p σ k (σ k) + p k ≤ T := by
  classical
  by_contra hcon
  have hlt : T < loadBefore p σ k (σ k) + p k := lt_of_not_ge hcon
  have hpk : 0 ≤ p k := hp k
  have hL0 : 0 ≤ loadBefore p σ k (σ k) := Finset.sum_nonneg (fun j _ => hp j)
  obtain ⟨E, hEdef⟩ : ∃ E : Fin m → Finset (Fin n),
      E = fun i => univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ) ∧ σ j = i) := ⟨_, rfl⟩
  obtain ⟨F, hFdef⟩ : ∃ F : Fin m → Finset (Fin n),
      F = fun i => univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ) + 1 ∧ τ j = i) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : Finset (Fin n),
      B = univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ) + 1 ∧ loadBefore p σ k (σ k) ≤ p j) :=
        ⟨_, rfl⟩
  have hE : ∀ i, ∑ j ∈ E i, p j = loadBefore p σ k i := by intro i; rw [hEdef]; rfl
  have hF : ∀ i, ∑ j ∈ F i, p j ≤ T := by intro i; rw [hFdef]; exact hT i
  have hmemE : ∀ i j, j ∈ E i ↔ (j : ℕ) < (k : ℕ) ∧ σ j = i := by intro i j; rw [hEdef]; simp
  have hmemF : ∀ i j, j ∈ F i ↔ (j : ℕ) < (k : ℕ) + 1 ∧ τ j = i := by intro i j; rw [hFdef]; simp
  have hmemB : ∀ j, j ∈ B ↔ (j : ℕ) < (k : ℕ) + 1 ∧ loadBefore p σ k (σ k) ≤ p j := by
    intro j; rw [hBdef]; simp
  -- at most two jobs per `τ`-fiber
  have hb2 : ∀ i, (F i).card ≤ 2 := by
    intro i
    by_contra h
    have h3n : 3 ≤ (F i).card := by omega
    have h3' : (3 : ℝ) ≤ ((F i).card : ℝ) := by exact_mod_cast h3n
    have h1 := key_card_mul_le_sum p hanti k (F i) (fun j hj => ((hmemF i j).mp hj).1)
    have h2 := hF i
    nlinarith
  -- (a) every machine has a `σ`-job before `k`
  have ha1 : ∀ i, 1 ≤ (E i).card := by
    intro i
    by_contra h
    have h0 : E i = ∅ := Finset.card_eq_zero.mp (by omega)
    have hl : loadBefore p σ k i = 0 := by rw [← hE i, h0, Finset.sum_empty]
    have hle := hσ k i
    have hkF : k ∈ F (τ k) := (hmemF _ _).mpr ⟨by omega, rfl⟩
    have h1 := Finset.single_le_sum (fun j _ => hp j) hkF
    have h2 := hF (τ k)
    linarith
  -- (c) a long job is alone on its `τ`-machine among the jobs up to `k`
  have hB1 : ∀ j ∈ B, ∀ j' : Fin n, (j' : ℕ) < (k : ℕ) + 1 → τ j' = τ j → j' = j := by
    intro j hj j' hj' hτ
    by_contra hne
    have hjB := (hmemB j).mp hj
    have hsub : ({j, j'} : Finset (Fin n)) ⊆ F (τ j) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (hmemF _ _).mpr ⟨hjB.1, rfl⟩
      · rw [Finset.mem_singleton.mp hx]; exact (hmemF _ _).mpr ⟨hj', hτ⟩
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hp x)
    rw [Finset.sum_pair (fun h => hne h.symm)] at h1
    have hpj' : p k ≤ p j' := hanti (Fin.le_iff_val_le_val.mpr (by omega))
    have h2 := hF (τ j)
    linarith [hjB.2]
  have hinj : Set.InjOn τ (B : Set (Fin n)) := by
    intro j hj j' hj' h
    exact (hB1 j (Finset.mem_coe.mp hj) j' ((hmemB j').mp (Finset.mem_coe.mp hj')).1 h.symm).symm
  have hRcard : (B.image τ).card = B.card := Finset.card_image_of_injOn hinj
  have hbR : ∀ i, (F i).card + (if i ∈ B.image τ then 1 else 0) ≤ 2 := by
    intro i
    split_ifs with hi
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      have hsub : F (τ j) ⊆ {j} := by
        intro j' hj'
        have h' := (hmemF _ _).mp hj'
        exact Finset.mem_singleton.mpr (hB1 j hj j' h'.1 h'.2)
      have := Finset.card_le_card hsub
      rw [Finset.card_singleton] at this
      omega
    · have := hb2 i; omega
  have haS : ∀ i, 2 ≤ (E i).card + (if (E i).card = 1 then 1 else 0) := by
    intro i
    have := ha1 i
    split_ifs with h <;> omega
  -- (d) a machine with a single `σ`-job before `k` holds a long job
  have hSsub : univ.filter (fun i => (E i).card = 1) ⊆ B.image σ := by
    intro i hi
    have h1 : (E i).card = 1 := (Finset.mem_filter.mp hi).2
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h1
    have hjE : j ∈ E i := by rw [hj]; exact Finset.mem_singleton_self j
    have hjm := (hmemE i j).mp hjE
    have hsum : loadBefore p σ k i = p j := by rw [← hE i, hj, Finset.sum_singleton]
    have hle := hσ k i
    exact Finset.mem_image.mpr ⟨j, (hmemB j).mpr ⟨by omega, by linarith⟩, hjm.2⟩
  have hSc : (univ.filter (fun i => (E i).card = 1)).card ≤ B.card :=
    (Finset.card_le_card hSsub).trans Finset.card_image_le
  -- (b) the fiber counts
  obtain ⟨A, hAdef⟩ : ∃ A : Finset (Fin n), A = univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ))
    := ⟨_, rfl⟩
  obtain ⟨A', hA'def⟩ : ∃ A' : Finset (Fin n),
      A' = univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ) + 1) := ⟨_, rfl⟩
  have hAA' : A' = insert k A := by
    ext j
    rw [hA'def, hAdef]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hkA : k ∉ A := by rw [hAdef]; simp
  have hA'card : A'.card = A.card + 1 := by rw [hAA', Finset.card_insert_of_notMem hkA]
  have hsumA : A.card = ∑ i, (E i).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := σ) (t := univ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hAdef, hEdef, Finset.filter_filter]
  have hsumA' : A'.card = ∑ i, (F i).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := τ) (t := univ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hA'def, hFdef, Finset.filter_filter]
  have hsumE : 2 * m ≤ ∑ i, (E i).card + (univ.filter (fun i => (E i).card = 1)).card := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin m))) => haS i)
    rw [Finset.sum_add_distrib, ← Finset.card_filter, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin,
      smul_eq_mul] at h
    omega
  have hsumF : ∑ i, (F i).card + (B.image τ).card ≤ 2 * m := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin m))) => hbR i)
    rw [Finset.sum_add_distrib, ← Finset.card_filter, Finset.filter_univ_mem, Finset.sum_const,
      Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at h
    omega
  omega

/-- The sorted form of `lpt_optimal_of_third_lt`. -/
theorem key_optimal_sorted {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (hanti :
  Antitone p)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (τ : Fin n → Fin m) (h : ∀ j, makespan p τ < 3 *
      p j) :
    makespan p σ ≤ makespan p τ := by
  rw [bs_makespan_le_iff]
  intro i
  by_cases hi : ∃ j, σ j = i
  · obtain ⟨k, hk, hload⟩ := bs_exists_last_job p σ i hi
    rw [hload]
    subst hk
    refine key_lemma p hp hanti σ hσ k τ (makespan p τ) (fun i' => ?_) (h k)
    exact (bs_loadBefore_le_load p hp τ _ i').trans (load_le_makespan p τ i')
  · push Not at hi
    rw [bs_load_eq_zero p σ i hi]
    exact bs_makespan_nonneg p hp τ

/-- When every job is longer than a third of the makespan of `τ`, every LPT schedule is at least
as good as `τ`. -/
theorem lpt_optimal_of_third_lt {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) (τ : Fin n → Fin m)
    (h : ∀ j, makespan p τ < 3 * p j) : makespan p σ ≤ makespan p τ := by
  obtain ⟨π, hπ, hlist⟩ := hσ
  have hs := key_optimal_sorted (p ∘ π) (fun j => hp (π j)) hπ (σ ∘ π) hlist (τ ∘ π)
    (fun j => by rw [makespan_comp]; exact h (π j))
  rwa [makespan_comp, makespan_comp] at hs

/-- LPT is optimal when every job is longer than a third of the optimal makespan. -/
theorem lpt_eq_optMakespan_of_third_lt {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0
  ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) (h : ∀ j, optMakespan m p < 3 * p j) :
    makespan p σ = optMakespan m p := by
  obtain ⟨τ, hτ⟩ := exists_makespan_eq_optMakespan (m := m) p
  apply le_antisymm
  · rw [← hτ]
    exact lpt_optimal_of_third_lt p hp σ hσ τ (fun j => by rw [hτ]; exact h j)
  · exact optMakespan_le p σ

end GrahamLPT
