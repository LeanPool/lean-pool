/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Components of a graph of maximum degree two

`exists_maxPath`: through every vertex `x` there is a path `p 0, …, p n` (injective, consecutive
vertices adjacent) of greatest length. If all degrees are at most `2`, its vertices are closed under
adjacency (`maxPath_closed`), and every edge between them joins consecutive vertices, or `p 0` and
`p n` (`maxPath_adj`): the component of `x` is a path or a cycle.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.Comp

open Finset

variable {E : Type*} [Fintype E] [DecidableEq E] (L : SimpleGraph E)

/-- `p 0, …, p n` is a path of `L`. -/
def IsPathFn (n : ℕ) (p : ℕ → E) : Prop :=
  (∀ i j, i ≤ n → j ≤ n → p i = p j → i = j) ∧ ∀ i, i < n → L.Adj (p i) (p (i + 1))

omit [DecidableEq E] in
theorem IsPathFn.le_card {n : ℕ} {p : ℕ → E} (h : IsPathFn L n p) : n + 1 ≤ Fintype.card E := by
  classical
  have : ((range (n + 1)).image p).card = n + 1 := by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj e
    exact h.1 i j (by have := mem_range.1 hi; omega) (by have := mem_range.1 hj; omega) e
  rw [← this]
  exact card_le_univ _

omit [DecidableEq E] [Fintype E] in
/-- **A longest path through `x`.** -/
theorem exists_maxPath [Finite E] (x : E) : ∃ n p, IsPathFn L n p ∧ (∃ i ≤ n, p i = x) ∧
    ∀ n' p', IsPathFn L n' p' → (∃ i ≤ n', p' i = x) → n' ≤ n := by
  classical
  let : Fintype E := Fintype.ofFinite E
  let P : ℕ → Prop := fun n => ∃ p, IsPathFn L n p ∧ ∃ i ≤ n, p i = x
  have h0 : P 0 := ⟨fun _ => x, ⟨fun i j hi hj _ => by omega, fun i hi => absurd hi (by omega)⟩,
    0, le_rfl, rfl⟩
  have hbd : ∀ n, P n → n ≤ Fintype.card E := fun n ⟨p, hp, _⟩ => by
    have := hp.le_card; omega
  set N := Nat.findGreatest P (Fintype.card E) with hN
  have hPN : P N := Nat.findGreatest_spec (P := P) (Nat.zero_le _) h0
  obtain ⟨p, hp, hx⟩ := hPN
  refine ⟨N, p, hp, hx, fun n' p' hp' hx' => ?_⟩
  exact Nat.le_findGreatest (hbd n' ⟨p', hp', hx'⟩) ⟨p', hp', hx'⟩
variable {L}

section Max

variable {n : ℕ} {p : ℕ → E} {x : E} (hp : IsPathFn L n p) (hx : ∃ i ≤ n, p i = x)
  (hmax : ∀ n' p', IsPathFn L n' p' → (∃ i ≤ n', p' i = x) → n' ≤ n)

include hp hx hmax in
omit [DecidableEq E] [Fintype E] in
/-- Every neighbour of the first vertex lies on the path. -/
theorem maxPath_head {y : E} (hy : L.Adj (p 0) y) : ∃ j ≤ n, p j = y := by
  classical
  by_contra hno
  push Not at hno
  let p' : ℕ → E := fun i => if i = 0 then y else p (i - 1)
  have hp' : IsPathFn L (n + 1) p' := by
    refine ⟨fun i j hi hj e => ?_, fun i hi => ?_⟩
    · simp only [p'] at e
      split_ifs at e with h1 h2 h2
      · omega
      · exact absurd e.symm (hno (j - 1) (by omega))
      · exact absurd e (hno (i - 1) (by omega))
      · have := hp.1 (i - 1) (j - 1) (by omega) (by omega) e; omega
    · simp only [p']
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simp only [ite_true, show (0 + 1 = 0) = False by simp, ite_false]
        exact hy.symm
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), show i + 1 - 1 = i - 1 + 1 by omega]
        exact hp.2 (i - 1) (by omega)
  obtain ⟨i, hi, hix⟩ := hx
  have := hmax (n + 1) p' hp' ⟨i + 1, by omega, by
    simp only [p', ite_eq_right (show i + 1 ≠ 0 by omega)]
    simpa⟩
  omega

include hp hx hmax in
omit [DecidableEq E] [Fintype E] in
/-- Every neighbour of the last vertex lies on the path. -/
theorem maxPath_last {y : E} (hy : L.Adj (p n) y) : ∃ j ≤ n, p j = y := by
  classical
  by_contra hno
  push Not at hno
  let p' : ℕ → E := fun i => if i = n + 1 then y else p i
  have hp' : IsPathFn L (n + 1) p' := by
    refine ⟨fun i j hi hj e => ?_, fun i hi => ?_⟩
    · simp only [p'] at e
      split_ifs at e with h1 h2 h2
      · omega
      · exact absurd e.symm (hno j (by omega))
      · exact absurd e (hno i (by omega))
      · exact hp.1 i j (by omega) (by omega) e
    · simp only [p']
      rcases Nat.lt_or_ge i n with hin | hin
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; exact hp.2 i hin
      · rw [ite_eq_right (by omega), ite_eq_left (by omega), show i = n by omega]; exact hy
  obtain ⟨i, hi, hix⟩ := hx
  have := hmax (n + 1) p' hp' ⟨i, by omega, by
    simp only [p', ite_eq_right (show i ≠ n + 1 by omega)]
    exact hix⟩
  omega
end Max

omit [DecidableEq E] in
/-- In a graph of maximum degree `2`, an interior vertex of a path has no other neighbours. -/
theorem interior_adj [DecidableRel L.Adj] (hdeg : ∀ v, L.degree v ≤ 2) {n : ℕ} {p : ℕ → E}
    (hp : IsPathFn L n p) {j : ℕ} (hj0 : 0 < j) (hjn : j < n) {y : E} (hy : L.Adj (p j) y) :
    y = p (j - 1) ∨ y = p (j + 1) := by
  classical
  have h1 : L.Adj (p j) (p (j - 1)) := by
    have := hp.2 (j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega] at this
    exact this.symm
  have h2 : L.Adj (p j) (p (j + 1)) := hp.2 j hjn
  have hne : p (j - 1) ≠ p (j + 1) := fun e => by
    have := hp.1 _ _ (by omega) (by omega) e; omega
  by_contra hc
  push Not at hc
  have hsub : ({p (j - 1), p (j + 1), y} : Finset E) ⊆ L.neighborFinset (p j) := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rw [SimpleGraph.mem_neighborFinset]
    rcases hz with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact hy
  have := card_le_card hsub
  rw [SimpleGraph.card_neighborFinset_eq_degree, card_insert_of_notMem (by
    simp only [mem_insert, mem_singleton, not_or]; exact ⟨hne, hc.1.symm⟩),
    card_insert_of_notMem (by simp only [mem_singleton]; exact hc.2.symm), card_singleton] at this
  have := hdeg (p j)
  omega

section Structure

variable [DecidableRel L.Adj] (hdeg : ∀ v, L.degree v ≤ 2) {n : ℕ} {p : ℕ → E} {x : E}
  (hp : IsPathFn L n p) (hx : ∃ i ≤ n, p i = x)
  (hmax : ∀ n' p', IsPathFn L n' p' → (∃ i ≤ n', p' i = x) → n' ≤ n)

include hdeg hp hx hmax in
omit [DecidableEq E] in
/-- **The path is closed under adjacency.** -/
theorem maxPath_closed {j : ℕ} (hj : j ≤ n) {y : E} (hy : L.Adj (p j) y) : ∃ k ≤ n, p k = y := by
  classical
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact maxPath_head hp hx hmax hy
  rcases Nat.lt_or_ge j n with hjn | hjn
  · rcases interior_adj hdeg hp hj0 hjn hy with rfl | rfl
    · exact ⟨j - 1, by omega, rfl⟩
    · exact ⟨j + 1, by omega, rfl⟩
  · have : j = n := by omega
    subst this
    exact maxPath_last hp hx hmax hy

include hdeg hp in
omit [DecidableEq E] in
/-- **The edges between path vertices** join consecutive vertices, or the two ends. -/
theorem maxPath_adj {i j : ℕ} (hij : i < j) (hjn : j ≤ n) (hadj : L.Adj (p i) (p j)) :
    j = i + 1 ∨ (i = 0 ∧ j = n) := by
  classical
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rcases Nat.lt_or_ge j n with hjn' | hjn'
    · rcases interior_adj hdeg hp (by omega) hjn' hadj.symm with h | h
      · have := hp.1 _ _ (by omega) (by omega) h; omega
      · have := hp.1 _ _ (by omega) (by omega) h; omega
    · exact Or.inr ⟨rfl, by omega⟩
  · rcases interior_adj hdeg hp hi0 (by omega) hadj with h | h
    · have := hp.1 _ _ (by omega) (by omega) h; omega
    · have := hp.1 _ _ (by omega) (by omega) h; omega
end Structure

end Bkls.Comp

end LeanPool.BalancedEdgeColourings
