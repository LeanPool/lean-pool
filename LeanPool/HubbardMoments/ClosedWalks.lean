/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import LeanPool.HubbardMoments.Defs
public import LeanPool.HubbardMoments.Torus
public import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.IntervalCases

/-!
# Permutations induced by closed walks

Labelled hard-core particles hop on a graph (`HubbardMoments.IsParticleHop`); a closed walk
of `h` hops returns the set of occupied sites to itself and so permutes the particles: the
particle `p` ends where the particle `σ p` started.

* `card_support_lt_of_closedWalk`: on every graph, a closed walk of `h` hops moves no
  particle or fewer than `h` of them;
* `closedWalk_four`: a closed walk of four hops induces the identity, a transposition or a
  3-cycle, never a 4-cycle or a double transposition (§6, App. C);
* `exists_closedWalk_swap`, `exists_closedWalk_threeCycle`: on every `L × L` torus,
  `L ≥ 3`, both nontrivial cases occur (ring exchange; the plaquette 3-cycle of App. C);
* `choose_three_add_choose_three`: `P₃ = C(N↑, 3) + C(N↓, 3)` is an affine function of
  `P_same = C(N↑, 2) + C(N↓, 2)` at fixed `n`, namely
  `P₃ = C(n, 3) - (n - 2)/2 · (C(n, 2) - P_same)` (§6).

The paper's argument is a dependency loop: if `h` particles move, each moves once, onto the
site where another one started, which must therefore have left first. Here the loop is
closed by a sum. With `t p` the time at which `p` moves, `t (σ p) < t p` for every moved `p`,
whereas `∑ t (σ p) = ∑ t p` because `σ` permutes the moved particles.

## Not covered

The fermionic signs and the spin conditions of these walks (App. C), and the consequences
for `μ₄`.
-/

@[expose] public section

namespace HubbardMoments

open Finset

variable {P V : Type*} [Fintype P] [DecidableEq P] {G : SimpleGraph V} {walk : ℕ → P → V}
  {h : ℕ}

omit [Fintype P] [DecidableEq P] in
/-- A particle that does not move between times `a` and `b` stays where it is. -/
theorem walk_eq_of_not_moved {p : P} {a b : ℕ} (hab : a ≤ b)
    (hp : ∀ i, a ≤ i → i < b → walk (i + 1) p = walk i p) : walk b p = walk a p := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    rw [hp b hab (Nat.lt_succ_self b), ih fun i hai hib => hp i hai (Nat.lt_succ_of_lt hib)]

omit [Fintype P] in
/-- In one hop exactly one particle moves: the hopping one, onto an empty site. -/
theorem IsParticleHop.exists_unique_moves {pos pos' : P → V} (hh : IsParticleHop G pos pos') :
    ∃ p, pos' p ∉ Set.range pos ∧ ∀ q, pos' q ≠ pos q → q = p := by
  obtain ⟨p, w, -, hw, rfl⟩ := hh
  refine ⟨p, by simpa using hw, fun q hq => ?_⟩
  by_contra hqp
  exact hq (Function.update_of_ne hqp _ _)

variable [DecidableEq V]

/-- The times before `h` at which particle `p` moves. -/
def moveTimes (walk : ℕ → P → V) (h : ℕ) (p : P) : Finset ℕ :=
  (range h).filter fun i => walk (i + 1) p ≠ walk i p

/-- Each hop moves one particle, so the numbers of moves add up to `h`. -/
theorem sum_card_moveTimes (hw : ∀ i < h, IsParticleHop G (walk i) (walk (i + 1))) :
    ∑ p, (moveTimes walk h p).card = h := by
  have hone : ∀ i ∈ range h, (univ.filter fun p => walk (i + 1) p ≠ walk i p).card = 1 := by
    intro i hi
    obtain ⟨p, hp, huniq⟩ := (hw i (mem_range.1 hi)).exists_unique_moves
    rw [card_eq_one]
    refine ⟨p, eq_singleton_iff_unique_mem.2 ⟨?_, fun q hq => huniq q (mem_filter.1 hq).2⟩⟩
    exact mem_filter.2 ⟨mem_univ p, fun h' => hp ⟨p, h'.symm⟩⟩
  simp only [moveTimes, card_filter]
  rw [sum_comm, sum_congr rfl fun i hi =>
    show (∑ p, if walk (i + 1) p ≠ walk i p then 1 else 0) = 1 by
      rw [← card_filter]; exact hone i hi]
  simp

omit [DecidableEq V] in
/-- **Closed walks move few particles.** On any graph, if a walk of `h` hops of hard-core
particles, starting from distinct sites, ends with the particles permuted by `σ ≠ 1`, then
fewer than `h` particles are moved. -/
theorem card_support_lt_of_closedWalk (hinj : Function.Injective (walk 0))
    (hw : ∀ i < h, IsParticleHop G (walk i) (walk (i + 1))) {σ : Equiv.Perm P}
    (hσ : ∀ p, walk h p = walk 0 (σ p)) (hne : σ ≠ 1) : σ.support.card < h := by
  classical
  set D := σ.support
  set T := moveTimes walk h
  have hD : ∀ p, p ∈ D ↔ walk h p ≠ walk 0 p := fun p => by
    rw [Equiv.Perm.mem_support, hσ, hinj.ne_iff]
  -- a moved particle moves at least once
  have hT : ∀ p ∈ D, (T p).Nonempty := by
    intro p hp
    by_contra hT
    rw [not_nonempty_iff_eq_empty] at hT
    refine (hD p).1 hp (walk_eq_of_not_moved (Nat.zero_le h) fun i _ hi => ?_)
    by_contra hm
    have : i ∈ T p := mem_filter.2 ⟨mem_range.2 hi, hm⟩
    rw [hT] at this
    exact notMem_empty i this
  by_contra hlt
  rw [not_lt] at hlt
  -- then every moved particle moves exactly once
  have hsum := sum_card_moveTimes hw
  have hle : ∑ p ∈ D, (T p).card ≤ h := hsum ▸ sum_le_sum_of_subset (subset_univ D)
  have hone : ∀ p ∈ D, (T p).card = 1 := by
    by_contra hc
    obtain ⟨p, hp, hcp⟩ : ∃ p ∈ D, (T p).card ≠ 1 := by simpa using hc
    have hlt' : ∑ p ∈ D, 1 < ∑ p ∈ D, (T p).card :=
      sum_lt_sum (fun q hq => card_pos.2 (hT q hq))
        ⟨p, hp, lt_of_le_of_ne (card_pos.2 (hT p hp)) (Ne.symm hcp)⟩
    rw [sum_const, smul_eq_mul, mul_one] at hlt'
    omega
  -- the time at which a moved particle moves
  let t : P → ℕ := fun p => if hp : p ∈ D then (T p).min' (hT p hp) else 0
  have ht_mem : ∀ p ∈ D, t p ∈ T p := fun p hp => by
    simp only [t, hp, ↓reduceDIte]
    exact min'_mem _ _
  have ht_lt : ∀ p ∈ D, t p < h := fun p hp => mem_range.1 (mem_filter.1 (ht_mem p hp)).1
  have ht_before : ∀ p ∈ D, ∀ j ≤ t p, walk j p = walk 0 p := by
    intro p hp j hj
    refine walk_eq_of_not_moved (Nat.zero_le _) fun i _ hi => ?_
    by_contra hm
    have hi' : i ∈ T p := mem_filter.2 ⟨mem_range.2 ((hi.trans_le hj).trans (ht_lt p hp)), hm⟩
    have := min'_le (T p) i hi'
    simp only [t, hp, ↓reduceDIte] at hj
    omega
  have ht_after : ∀ p ∈ D, walk h p = walk (t p + 1) p := by
    intro p hp
    refine walk_eq_of_not_moved (ht_lt p hp) fun i hi hih => ?_
    by_contra hm
    have hi' : i ∈ T p := mem_filter.2 ⟨mem_range.2 hih, hm⟩
    obtain ⟨x, hx⟩ := card_eq_one.1 (hone p hp)
    have h1 := ht_mem p hp
    rw [hx, mem_singleton] at hi' h1
    omega
  -- the particle that started on `p`'s target has left before `p` arrives
  have hdec : ∀ p ∈ D, t (σ p) < t p := by
    intro p hp
    have hq : σ p ∈ D := Equiv.Perm.apply_mem_support.2 hp
    obtain ⟨r, hr, huniq⟩ := (hw (t p) (ht_lt p hp)).exists_unique_moves
    have hmp : walk (t p + 1) p ≠ walk (t p) p := (mem_filter.1 (ht_mem p hp)).2
    have hrp : p = r := huniq p hmp
    subst hrp
    refine lt_of_not_ge fun hbefore => ?_
    have hstill := ht_before (σ p) hq (t p) hbefore
    exact hr ⟨σ p, by rw [hstill, ← hσ, ht_after p hp]⟩
  -- summing `t (σ p) < t p` over the moved particles contradicts `∑ t ∘ σ = ∑ t`
  have hDne : D.Nonempty := by
    rw [nonempty_iff_ne_empty, Ne, Equiv.Perm.support_eq_empty_iff]
    exact hne
  have hsumlt : ∑ p ∈ D, t (σ p) < ∑ p ∈ D, t p := sum_lt_sum_of_nonempty hDne hdec
  rw [Equiv.Perm.sum_comp σ D t (fun a ha => Equiv.Perm.mem_support.2 ha)] at hsumlt
  exact lt_irrefl _ hsumlt

omit [DecidableEq V] in
/-- **Four-hop closed walks** (§6, App. C): a closed walk of four hops of hard-core particles
on any graph induces the identity, a transposition or a 3-cycle. -/
theorem closedWalk_four (hinj : Function.Injective (walk 0))
    (hw : ∀ i < 4, IsParticleHop G (walk i) (walk (i + 1))) {σ : Equiv.Perm P}
    (hσ : ∀ p, walk 4 p = walk 0 (σ p)) : σ = 1 ∨ σ.IsSwap ∨ σ.IsThreeCycle := by
  by_cases hne : σ = 1
  · exact Or.inl hne
  have hlt := card_support_lt_of_closedWalk hinj hw hσ hne
  have h0 : σ.support.card ≠ 0 := by
    rw [Ne, card_eq_zero, Equiv.Perm.support_eq_empty_iff]
    exact hne
  have h1 := σ.card_support_ne_one
  rcases (by omega : σ.support.card = 2 ∨ σ.support.card = 3) with hc | hc
  · exact Or.inr (Or.inl (Equiv.Perm.card_support_eq_two.1 hc))
  · exact Or.inr (Or.inr (card_support_eq_three_iff.1 hc))

/-! ### Both nontrivial cases occur on the square lattice -/

open SimpleGraph

/-- The four sides of the unit square at the origin are bonds of the torus, `L ≥ 3`. -/
theorem torus_adj_square (m : ℕ) :
    (torus (m + 3)).Adj (0, 0) (1, 0) ∧ (torus (m + 3)).Adj (1, 0) (1, 1) ∧
    (torus (m + 3)).Adj (1, 1) (0, 1) ∧ (torus (m + 3)).Adj (0, 1) (0, 0) := by
  simp [torus, boxProd_adj, cycleGraph_adj]

/-- **Ring exchange in four hops.** On every `L × L` torus, `L ≥ 3`, two particles on opposite
corners of a plaquette exchange places in four hops through the two other corners. -/
theorem exists_closedWalk_swap {L : ℕ} (hL : 3 ≤ L) :
    ∃ (walk : ℕ → Fin 2 → Fin L × Fin L) (σ : Equiv.Perm (Fin 2)),
      Function.Injective (walk 0) ∧ (∀ i < 4, IsParticleHop (torus L) (walk i) (walk (i + 1))) ∧
        (∀ p, walk 4 p = walk 0 (σ p)) ∧ σ.IsSwap := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 3 := ⟨L - 3, by omega⟩
  have h10 : (1 : Fin (m + 3)) ≠ 0 := by simp
  have hadj := torus_adj_square m
  let walk : ℕ → Fin 2 → Fin (m + 3) × Fin (m + 3)
    | 0 => ![(0, 0), (1, 1)]
    | 1 => ![(1, 0), (1, 1)]
    | 2 => ![(1, 0), (0, 1)]
    | 3 => ![(1, 1), (0, 1)]
    | _ => ![(1, 1), (0, 0)]
  refine ⟨walk, Equiv.swap 0 1, ?_, ?_, ?_, ⟨0, 1, by decide, rfl⟩⟩
  · intro p q hpq
    fin_cases p <;> fin_cases q <;> first | rfl | simp [walk] at hpq
  · intro i hi
    interval_cases i
    · exact ⟨0, (1, 0), hadj.1, by simp [walk, h10],
        by funext q; fin_cases q <;> rfl⟩
    · exact ⟨1, (0, 1), hadj.2.2.1, by simp [walk, h10],
        by funext q; fin_cases q <;> rfl⟩
    · exact ⟨0, (1, 1), hadj.2.1, by simp [walk, h10],
        by funext q; fin_cases q <;> rfl⟩
    · exact ⟨1, (0, 0), hadj.2.2.2, by simp [walk],
        by funext q; fin_cases q <;> rfl⟩
  · intro p
    fin_cases p <;> simp [walk]

/-- **A 3-cycle in four hops.** On every `L × L` torus, `L ≥ 3`, three particles on three
corners of a plaquette are cyclically permuted in four hops through the fourth corner: the
first goes round two sides, the other two move one step each. -/
theorem exists_closedWalk_threeCycle {L : ℕ} (hL : 3 ≤ L) :
    ∃ (walk : ℕ → Fin 3 → Fin L × Fin L) (σ : Equiv.Perm (Fin 3)),
      Function.Injective (walk 0) ∧ (∀ i < 4, IsParticleHop (torus L) (walk i) (walk (i + 1))) ∧
        (∀ p, walk 4 p = walk 0 (σ p)) ∧ σ.IsThreeCycle := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 3 := ⟨L - 3, by omega⟩
  have h10 : (1 : Fin (m + 3)) ≠ 0 := by simp
  have hadj := torus_adj_square m
  let walk : ℕ → Fin 3 → Fin (m + 3) × Fin (m + 3)
    | 0 => ![(0, 0), (1, 0), (1, 1)]
    | 1 => ![(0, 1), (1, 0), (1, 1)]
    | 2 => ![(0, 1), (0, 0), (1, 1)]
    | 3 => ![(0, 1), (0, 0), (1, 0)]
    | _ => ![(1, 1), (0, 0), (1, 0)]
  let σ : Equiv.Perm (Fin 3) := ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩
  refine ⟨walk, σ, ?_, ?_, ?_, card_support_eq_three_iff.1 (by decide)⟩
  · intro p q hpq
    fin_cases p <;> fin_cases q <;> first | rfl | simp [walk] at hpq
  · intro i hi
    interval_cases i
    · exact ⟨0, (0, 1), hadj.2.2.2.symm, by simp [walk, h10],
        by funext q; fin_cases q <;> rfl⟩
    · exact ⟨1, (0, 0), hadj.1.symm, by simp [walk],
        by funext q; fin_cases q <;> rfl⟩
    · exact ⟨2, (1, 0), hadj.2.1.symm, by simp [walk, h10],
        by funext q; fin_cases q <;> rfl⟩
    · exact ⟨0, (1, 1), hadj.2.2.1.symm, by simp [walk, h10],
        by funext q; fin_cases q <;> rfl⟩
  · intro p
    fin_cases p <;> simp [walk, σ]

/-! ### The 3-cycle weight is affine in the same-spin pair count -/

theorem cast_choose_three (a : ℕ) : (a.choose 3 : ℚ) = a * (a - 1) * (a - 2) / 6 := by
  have h := Nat.descFactorial_eq_factorial_mul_choose a 3
  have h' : (a.descFactorial 3 : ℚ) = a * (a - 1) * (a - 2) := by
    rcases a with _ | _ | _ | a <;> simp [Nat.descFactorial]
    ring
  rw [h] at h'
  push_cast [Nat.factorial] at h'
  linarith

/-- `P₃ = C(N↑, 3) + C(N↓, 3)` is affine in `P_same = C(N↑, 2) + C(N↓, 2)` at fixed
`n = N↑ + N↓`. -/
theorem choose_three_add_choose_three (a b : ℕ) :
    ((a.choose 3 + b.choose 3 : ℕ) : ℚ) = (a + b).choose 3 -
      ((a + b : ℚ) - 2) / 2 * ((a + b).choose 2 - (a.choose 2 + b.choose 2 : ℕ)) := by
  push_cast
  rw [cast_choose_three, cast_choose_three, cast_choose_three, Nat.cast_choose_two,
    Nat.cast_choose_two, Nat.cast_choose_two]
  push_cast
  ring

end HubbardMoments
