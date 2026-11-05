/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Colouring a path greedily (Balister–Kostochka–Li–Schelp 2004, Corollary 4, paths)

A path with vertices `0, …, n` and edges `i = {i, i + 1}` (`i < n`); an edge colouring is
`f : ℕ → Fin 3` (only `f 0, …, f (n - 1)` matter), proper iff `f i ≠ f (i + 1)` for `i + 1 < n`.
The colour set of vertex `i` is `pathSet n f i` (the colours of the edges `i - 1` and `i` that
exist). Every vertex is free, or must avoid a given set (`ext F`), or must differ from its partner
`j` (`int j`, an involution). If both ends are free, a greedy choice of `f 0, f 1, …` succeeds:
at each step two colours keep the colouring proper and the constraint at the new vertex excludes
at most one (`exists_path_colouring`).
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls

/-- The state of a vertex. -/
inductive PState where
  | free : PState
  | ext (F : Finset (Fin 3)) : PState
  | int (j : ℕ) : PState

/-- The colour set of vertex `i` of the path `0, …, n`. -/
def pathSet (n : ℕ) (f : ℕ → Fin 3) (i : ℕ) : Finset (Fin 3) :=
  (if 0 < i then {f (i - 1)} else ∅) ∪ (if i < n then {f i} else ∅)

/-- The constraint at vertex `i` holds. -/
def PSat (n : ℕ) (st : ℕ → PState) (f : ℕ → Fin 3) (i : ℕ) : Prop :=
  match st i with
  | .free => True
  | .ext F => pathSet n f i ≠ F
  | .int j => pathSet n f i ≠ pathSet n f j

theorem pathSet_congr {n : ℕ} {f g : ℕ → Fin 3} {i : ℕ} (h : ∀ m < i + 1, f m = g m) :
    pathSet n f i = pathSet n g i := by
  unfold pathSet
  rw [h (i - 1) (by omega), h i (by omega)]

theorem pathSet_mid {n : ℕ} (f : ℕ → Fin 3) {i : ℕ} (h0 : 0 < i) (hn : i < n) :
    pathSet n f i = {f (i - 1), f i} := by
  unfold pathSet; rw [ite_eq_left h0, ite_eq_left hn]; rfl

/-- Some colour avoids `a` and the (at most one) colour `x ≠ a` with `{a, x} = T`. -/
theorem exists_avoid (a : Fin 3) (T : Finset (Fin 3)) : ∃ x, x ≠ a ∧ ({a, x} : Finset (Fin 3))
    ≠ T := by
  by_contra h
  push Not at h
  have h1 := h (a + 1) (by omega)
  have h2 := h (a + 2) (by omega)
  have : ({a, a + 1} : Finset (Fin 3)) = {a, a + 2} := h1.trans h2.symm
  have hm : a + 1 ∈ ({a, a + 2} : Finset (Fin 3)) := this ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  omega

/-- **Greedy colouring of a path with free ends.** -/
theorem exists_path_colouring (n : ℕ) (st : ℕ → PState)
    (h0 : st 0 = .free) (hn : st n = .free)
    (hint : ∀ i j, st i = .int j → st j = .int i ∧ j ≠ i ∧ j ≤ n)
    (hrange : ∀ i, n < i → st i = .free) :
    ∃ f : ℕ → Fin 3, (∀ i, i + 1 < n → f i ≠ f (i + 1)) ∧ ∀ i ≤ n, PSat n st f i := by
  have key : ∀ m ≤ n, ∃ f : ℕ → Fin 3, (∀ i, i + 1 < m → f i ≠ f (i + 1)) ∧
      ∀ i < m, (∀ j, st i = .int j → j < m → pathSet n f i ≠ pathSet n f j) ∧
        (∀ F, st i = .ext F → pathSet n f i ≠ F) := by
    intro m
    induction m with
    | zero => intro _; exact ⟨fun _ => 0, fun i h => absurd h (by omega), fun i h => absurd h
        (by omega)⟩
    | succ m ih =>
      intro hm
      obtain ⟨f, hprop, hsat⟩ := ih (by omega)
      -- the target set at vertex `m`
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · refine ⟨f, fun i h => absurd h (by omega), fun i hi => ?_⟩
        have : i = 0 := by omega
        subst this
        rw [h0]
        exact ⟨fun j h _ => PState.noConfusion h, fun F h => PState.noConfusion h⟩
      -- choose `f m`
      let T : Finset (Fin 3) := match st m with
        | .free => {f (m - 1)}
        | .ext F => F
        | .int j => pathSet n f j
      obtain ⟨x, hx1, hx2⟩ := exists_avoid (f (m - 1)) T
      let g := Function.update f m x
      have hg : ∀ i, i ≠ m → g i = f i := fun i h => Function.update_of_ne h _ _
      have hgm : g m = x := Function.update_self _ _ _
      have hold : ∀ i < m, pathSet n g i = pathSet n f i := fun i hi =>
        pathSet_congr fun k hk => hg k (by omega)
      have hnew : pathSet n g m = {f (m - 1), x} := by
        rw [pathSet_mid g hm0 (by omega), hgm, hg (m - 1) (by omega)]
      refine ⟨g, fun i hi => ?_, fun i hi => ?_⟩
      · by_cases him : i + 1 = m
        · rw [hg i (by omega), show i + 1 = m from him, hgm, show i = m - 1 by omega]
          exact hx1.symm
        · rw [hg i (by omega), hg (i + 1) him]; exact hprop i (by omega)
      · by_cases him : i = m
        · subst him
          refine ⟨fun j hj hjm => ?_, fun F hF => ?_⟩
          · have hjm' : j < i := by
              have := (hint i j hj).2.1; omega
            rw [hnew, hold j hjm']
            have : T = pathSet n f j := by simp only [T, hj]
            rw [← this]; exact hx2
          · rw [hnew]
            have : T = F := by simp only [T, hF]
            rw [← this]; exact hx2
        · have hi' : i < m := by omega
          obtain ⟨h1, h2⟩ := hsat i hi'
          refine ⟨fun j hj hjm => ?_, fun F hF => ?_⟩
          · by_cases hjm' : j = m
            · subst hjm'
              -- the pair `(i, m)` is checked at `m`
              have hji := (hint i j hj).1
              rw [hold i hi', hnew]
              have : T = pathSet n f i := by simp only [T, hji]
              rw [← this]; exact fun e => hx2 e.symm
            · rw [hold i hi', hold j (by omega)]; exact h1 j hj (by omega)
          · rw [hold i hi']; exact h2 F hF
  obtain ⟨f, hprop, hsat⟩ := key n le_rfl
  refine ⟨f, hprop, fun i hi => ?_⟩
  unfold PSat
  rcases Nat.lt_or_ge i n with hin | hin
  · obtain ⟨h1, h2⟩ := hsat i hin
    split
    · trivial
    · next F hF => exact h2 F hF
    · next j hj =>
      have hjn : j ≤ n := (hint i j hj).2.2
      rcases Nat.lt_or_ge j n with hjn' | hjn'
      · exact h1 j hj hjn'
      · have : j = n := by omega
        have h3 := (hint i j hj).1
        rw [this, hn] at h3
        exact PState.noConfusion h3
  · have : i = n := by omega
    subst this
    rw [hn]; trivial

end Bkls

end LeanPool.BalancedEdgeColourings
