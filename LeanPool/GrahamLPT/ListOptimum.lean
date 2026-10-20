/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

module

public import LeanPool.GrahamLPT.Defs
import LeanPool.GrahamLPT.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Positivity.Finset

/-!
# ListOptimum

Graham's `ω₀` is the optimum: for nonnegative lengths every assignment `τ` is matched or improved
by a list schedule
(helpers carry the prefix `lo_`). The order is the start times of `τ` with each machine's jobs
run back to back in index order, `s j = loadBefore p τ j (τ j)`. In that order every list schedule
starts each job of
positive length no later than `τ` does (`lo_core`): if job `k` found every machine busy past `s
k`, each machine would
carry an earlier job running at time `s k`; those `m` jobs run at `s k` under `τ` too, on `m`
distinct machines of `τ`,
one of them `τ k`, which overlaps `k`. Hence every list-schedule load is at most `max_j (s j + p
j) ≤ makespan p τ`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- A machine whose load before `k` exceeds `T ≥ 0` carries a job before `k` that is running at
time `T`. -/
theorem lo_exists_cover {m n : ℕ} (q : Fin n → ℝ) (σ : Fin n → Fin m) (T : ℝ) (hT : 0 ≤ T) (i :
  Fin m) :
    ∀ k : ℕ, T < loadBefore q σ k i →
      ∃ a : Fin n, (a : ℕ) < k ∧ σ a = i ∧ loadBefore q σ a i ≤ T ∧ T < loadBefore q σ a i + q a
        := by
  intro k
  induction k with
  | zero =>
    intro h
    rw [bs_loadBefore_zero] at h
    linarith
  | succ k ih =>
    intro h
    by_cases hk : T < loadBefore q σ k i
    · obtain ⟨a, ha, h1, h2, h3⟩ := ih hk
      exact ⟨a, by omega, h1, h2, h3⟩
    · have hk' : loadBefore q σ k i ≤ T := not_lt.mp hk
      by_cases hkn : k < n
      · have hs : loadBefore q σ (k + 1) i =
            loadBefore q σ k i + if σ ⟨k, hkn⟩ = i then q ⟨k, hkn⟩ else 0 :=
          bs_loadBefore_succ q σ ⟨k, hkn⟩ i
        by_cases hσk : σ ⟨k, hkn⟩ = i
        · rw [hs, ite_eq_left hσk] at h
          exact ⟨⟨k, hkn⟩, Nat.lt_succ_self k, hσk, hk', h⟩
        · rw [hs, ite_eq_right hσk] at h
          linarith
      · have e1 := bs_loadBefore_of_le q σ k (by omega) i
        have e2 := bs_loadBefore_of_le q σ (k + 1) (by omega) i
        linarith

/-- In an order by nondecreasing times `t` that are the start times of a schedule `ρ` (no two jobs
of one machine of
`ρ` overlap), every list schedule starts each job of positive length no later than `ρ` does. -/
theorem lo_core {m n : ℕ} (q : Fin n → ℝ) (σ : Fin n → Fin m) (hσ : IsListSchedule q σ)
    (ρ : Fin n → Fin m) (t : Fin n → ℝ) (ht : Monotone t) (ht0 : ∀ j, 0 ≤ t j)
    (hdisj : ∀ a b, a ≠ b → ρ a = ρ b → t a + q a ≤ t b ∨ t b + q b ≤ t a) :
    ∀ N : ℕ, ∀ k : Fin n, (k : ℕ) < N → 0 < q k → loadBefore q σ k (σ k) ≤ t k := by
  intro N
  induction N with
  | zero =>
    intro k hk
    omega
  | succ N ih =>
    intro k hkN hqk
    by_contra hcon
    have hcon' : t k < loadBefore q σ k (σ k) := lt_of_not_ge hcon
    have hall : ∀ i, t k < loadBefore q σ k i := fun i => lt_of_lt_of_le hcon' (hσ k i)
    have hcov : ∀ i, ∃ a : Fin n, (a : ℕ) < k ∧ σ a = i ∧ loadBefore q σ a i ≤ t k ∧
        t k < loadBefore q σ a i + q a :=
      fun i => lo_exists_cover q σ (t k) (ht0 k) i k (hall i)
    choose f hfk hfσ hf1 hf2 using hcov
    have hend : ∀ i, t k < t (f i) + q (f i) := by
      intro i
      have hpos : 0 < q (f i) := by linarith [hf1 i, hf2 i]
      have hL := ih (f i) (by have := hfk i; omega) hpos
      rw [hfσ i] at hL
      linarith [hf2 i]
    have hle : ∀ i, t (f i) ≤ t k := fun i => ht (Fin.le_iff_val_le_val.2 (Nat.le_of_lt (hfk i)))
    have hinj : Function.Injective (ρ ∘ f) := by
      intro i i' h
      by_contra hne
      have hab : f i ≠ f i' := by
        intro e
        apply hne
        rw [← hfσ i, ← hfσ i', e]
      rcases hdisj (f i) (f i') hab h with h1 | h1
      · linarith [hend i, hle i']
      · linarith [hend i', hle i]
    obtain ⟨i, hi⟩ := Finite.injective_iff_surjective.mp hinj (ρ k)
    have hne : f i ≠ k := by
      intro e
      have := hfk i
      rw [e] at this
      omega
    rcases hdisj (f i) k hne hi with h1 | h1
    · linarith [hend i]
    · linarith [hle i]

/-- Every list schedule in such an order has makespan at most any bound `C ≥ 0` on the completion
times `t j + q j`. -/
theorem lo_makespan_le {m n : ℕ} [NeZero m] (q : Fin n → ℝ) (hq : ∀ j, 0 ≤ q j) (σ : Fin n → Fin m)
    (hσ : IsListSchedule q σ) (ρ : Fin n → Fin m) (t : Fin n → ℝ) (ht : Monotone t) (ht0 : ∀ j, 0
      ≤ t j)
    (hdisj : ∀ a b, a ≠ b → ρ a = ρ b → t a + q a ≤ t b ∨ t b + q b ≤ t a) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ j, t j + q j ≤ C) : makespan q σ ≤ C := by
  have key := lo_core q σ hσ ρ t ht ht0 hdisj n
  have hstep : ∀ k : ℕ, ∀ i, loadBefore q σ k i ≤ C := by
    intro k
    induction k with
    | zero =>
      intro i
      rw [bs_loadBefore_zero]
      exact hC0
    | succ k ih =>
      intro i
      by_cases hkn : k < n
      · have hs : loadBefore q σ (k + 1) i =
            loadBefore q σ k i + if σ ⟨k, hkn⟩ = i then q ⟨k, hkn⟩ else 0 :=
          bs_loadBefore_succ q σ ⟨k, hkn⟩ i
        rw [hs]
        by_cases hσk : σ ⟨k, hkn⟩ = i
        · rw [ite_eq_left hσk]
          rcases (hq ⟨k, hkn⟩).lt_or_eq with hpos | hzero
          · have h1 : loadBefore q σ k (σ ⟨k, hkn⟩) ≤ t ⟨k, hkn⟩ := key ⟨k, hkn⟩ hkn hpos
            rw [hσk] at h1
            linarith [hC ⟨k, hkn⟩]
          · rw [← hzero]
            linarith [ih i]
        · rw [ite_eq_right hσk]
          linarith [ih i]
      · rw [bs_loadBefore_of_le q σ (k + 1) (by omega) i, ← bs_loadBefore_of_le q σ k (by omega) i]
        exact ih i
  rw [bs_makespan_le_iff]
  intro i
  rw [← bs_loadBefore_of_le q σ n le_rfl i]
  exact hstep n i

/-- Graham's `ω₀` is attained: for nonnegative lengths every assignment `τ` is matched or improved
by a list schedule
in some order (the jobs listed by their start times when each machine of `τ` runs its jobs in
index order). -/
theorem lo_exists_listSchedule_le {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (τ : Fin n → Fin m) :
    ∃ (π : Equiv.Perm (Fin n)) (σ : Fin n → Fin m),
      IsListSchedule (p ∘ π) (σ ∘ π) ∧ makespan p σ ≤ makespan p τ := by
  obtain ⟨s, hs⟩ : ∃ s : Fin n → ℝ, s = fun j : Fin n => loadBefore p τ j (τ j) := ⟨_, rfl⟩
  have hsucc : ∀ j : Fin n, s j + p j = loadBefore p τ ((j : ℕ) + 1) (τ j) := by
    intro j
    rw [hs, bs_loadBefore_succ, ite_eq_left rfl]
  have hs0 : ∀ j, 0 ≤ s j := by
    intro j
    rw [hs]
    exact Finset.sum_nonneg fun j' _ => hp j'
  have hone : ∀ a b : Fin n, a < b → τ a = τ b → s a + p a ≤ s b := by
    intro a b hab he
    rw [hsucc a, hs]
    change loadBefore p τ (a + 1) (τ a) ≤ loadBefore p τ b (τ b)
    rw [← he]
    exact bs_loadBefore_mono p hp τ (Fin.lt_def.1 hab) (τ a)
  have hdisj : ∀ a b : Fin n, a ≠ b → τ a = τ b → s a + p a ≤ s b ∨ s b + p b ≤ s a := by
    intro a b hab he
    rcases lt_or_gt_of_ne hab with h | h
    · exact Or.inl (hone a b h he)
    · exact Or.inr (hone b a h he.symm)
  have hC : ∀ j, s j + p j ≤ makespan p τ := by
    intro j
    rw [hsucc j]
    exact (bs_loadBefore_le_load p hp τ _ _).trans (bs_load_le_makespan p τ _)
  set π := Tuple.sort s with hπ
  have hmono : Monotone (s ∘ π) := Tuple.monotone_sort s
  obtain ⟨σ', hσ'⟩ := exists_isListSchedule (m := m) (p ∘ π)
  have e : (σ' ∘ ⇑π.symm) ∘ ⇑π = σ' := by
    funext j
    simp
  refine ⟨π, σ' ∘ π.symm, ?_, ?_⟩
  · rw [e]
    exact hσ'
  · have key := lo_makespan_le (p ∘ π) (fun j => hp (π j)) σ' hσ' (τ ∘ π) (s ∘ π) hmono
      (fun j => hs0 (π j)) (fun a b hab he => hdisj (π a) (π b) (π.injective.ne hab) he)
      (makespan p τ) (bs_makespan_nonneg p hp τ) (fun j => hC (π j))
    rw [← makespan_comp p (σ' ∘ π.symm) π, e]
    exact key

/-- The optimal makespan is the least makespan over the list schedules in all orders (Graham's
`ω₀` equals `optMakespan`). -/
theorem lo_optMakespan_eq {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) :
    IsLeast ((fun σ : Fin n → Fin m => makespan p σ) ''
      {σ | ∃ π : Equiv.Perm (Fin n), IsListSchedule (p ∘ π) (σ ∘ π)}) (optMakespan m p) := by
  constructor
  · obtain ⟨τ, hτ⟩ := exists_makespan_eq_optMakespan (m := m) p
    obtain ⟨π, σ, hσ, hle⟩ := lo_exists_listSchedule_le p hp τ
    refine ⟨σ, ⟨π, hσ⟩, le_antisymm ?_ (optMakespan_le p σ)⟩
    rw [← hτ]
    exact hle
  · rintro c ⟨σ, -, rfl⟩
    exact optMakespan_le p σ

theorem exists_listSchedule_le {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (τ : Fin n → Fin m) :
    ∃ (π : Equiv.Perm (Fin n)) (σ : Fin n → Fin m),
      IsListSchedule (p ∘ π) (σ ∘ π) ∧ makespan p σ ≤ makespan p τ :=
  lo_exists_listSchedule_le p hp τ

theorem isLeast_listSchedule_makespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤
  p j) :
    IsLeast ((fun σ : Fin n → Fin m => makespan p σ) ''
      {σ | ∃ π : Equiv.Perm (Fin n), IsListSchedule (p ∘ π) (σ ∘ π)}) (optMakespan m p) :=
  lo_optMakespan_eq p hp

end GrahamLPT
