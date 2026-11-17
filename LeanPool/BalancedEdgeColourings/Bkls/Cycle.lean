/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.Path

/-!
# Colouring one cycle (Balister–Kostochka–Li–Schelp 2004, Lemma 3, one cycle): the path step

`path_fixed`: a path with edges `g 0, …, g n` whose first edge `g 0 = α` is given; the inner
vertices `1, …, n` (vertex `i` sees `{g (i - 1), g i}`) are free, externally restricted, or matched
among themselves. If the last vertex's restriction contains `β` (or its partner is not adjacent),
a greedy colouring exists with `g n ≠ β`.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls

/-- The colour set of vertex `i` of a path with edges `g 0, g 1, …`. -/
def pset (g : ℕ → Fin 3) (i : ℕ) : Finset (Fin 3) := {g (i - 1), g i}

theorem pset_congr {f g : ℕ → Fin 3} {i : ℕ} (h : ∀ m < i + 1, f m = g m) :
    pset f i = pset g i := by
  unfold pset; rw [h (i - 1) (by omega), h i (by omega)]

theorem exists_hit (a β : Fin 3) : ∃ x, x ≠ a ∧ β ∈ ({a, x} : Finset (Fin 3)) := by
  by_cases h : a = β
  · exact ⟨a + 1, by omega, by simp [h]⟩
  · exact ⟨β, fun e => h e.symm, by simp⟩

theorem exists_close (a β : Fin 3) (T : Finset (Fin 3)) (hT : a ≠ β → β ∈ T) :
    ∃ x, x ≠ a ∧ x ≠ β ∧ ({a, x} : Finset (Fin 3)) ≠ T := by
  by_cases h : a = β
  · obtain ⟨x, h1, h2⟩ := exists_avoid a T
    exact ⟨x, h1, by rw [← h]; exact h1, h2⟩
  · obtain ⟨x, h1, h2⟩ : ∃ x : Fin 3, x ≠ a ∧ x ≠ β := by
      by_contra hc
      push Not at hc
      have := hc (a + 1) (by omega)
      have := hc (a + 2) (by omega)
      omega
    refine ⟨x, h1, h2, fun e => ?_⟩
    have hb : β ∈ ({a, x} : Finset (Fin 3)) := by rw [e]; exact hT h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with hb | hb
    · exact h hb.symm
    · exact h2 hb.symm

/-- **A path with a given first edge, greedily.** -/
theorem path_fixed (n : ℕ) (hn : 1 ≤ n) (α β : Fin 3) (st : ℕ → PState)
    (hint : ∀ i j, 1 ≤ i → i ≤ n → st i = .int j → st j = .int i ∧ j ≠ i ∧ 1 ≤ j ∧ j ≤ n)
    (hend : ∀ F, st n = .ext F → β ∈ F)
    (hends : ∀ s, st n = .int s → s + 2 ≤ n) :
    ∃ g : ℕ → Fin 3, g 0 = α ∧ (∀ i < n, g i ≠ g (i + 1)) ∧ g n ≠ β ∧
      (∀ i F, 1 ≤ i → i ≤ n → st i = .ext F → pset g i ≠ F) ∧
      (∀ i j, 1 ≤ i → i ≤ n → st i = .int j → pset g i ≠ pset g j) := by
  have key : ∀ m, 1 ≤ m → m ≤ n → ∃ g : ℕ → Fin 3, g 0 = α ∧
      (∀ i, i + 1 < m → g i ≠ g (i + 1)) ∧
      (∀ i, 1 ≤ i → i < m → (∀ F, st i = .ext F → pset g i ≠ F) ∧
        (∀ j, st i = .int j → j < m → pset g i ≠ pset g j) ∧
        (st i = .int n → β ∈ pset g i)) := by
    intro m hm1
    induction m, hm1 using Nat.le_induction with
    | base =>
      intro _
      exact ⟨fun _ => α, rfl, fun i h => absurd h (by omega), fun i h1 h2 => absurd h2 (by omega)⟩
    | succ m hm ih =>
      intro hmn
      obtain ⟨g, hg0, hprop, hsat⟩ := ih (by omega)
      obtain ⟨x, hx1, hx2, hx3, hx4⟩ : ∃ x, x ≠ g (m - 1) ∧
          (∀ F, st m = .ext F → ({g (m - 1), x} : Finset (Fin 3)) ≠ F) ∧
          (∀ j, st m = .int j → j ≠ n → ({g (m - 1), x} : Finset (Fin 3)) ≠ pset g j) ∧
          (st m = .int n → β ∈ ({g (m - 1), x} : Finset (Fin 3))) := by
        cases hs : st m with
        | free =>
          obtain ⟨x, h1, _⟩ := exists_avoid (g (m - 1)) ∅
          exact ⟨x, h1, fun F h => (by cases h), fun j h => (by cases h), fun h => (by cases h)⟩
        | ext F =>
          obtain ⟨x, h1, h2⟩ := exists_avoid (g (m - 1)) F
          exact ⟨x, h1, fun F' h => (by cases h; exact h2), fun j h => (by cases h),
            fun h => (by cases h)⟩
        | int j =>
          by_cases hj : j = n
          · obtain ⟨x, h1, h2⟩ := exists_hit (g (m - 1)) β
            exact ⟨x, h1, fun F h => (by cases h),
              fun j' h hj' => absurd ((PState.int.inj h).symm.trans hj) hj', fun _ => h2⟩
          · obtain ⟨x, h1, h2⟩ := exists_avoid (g (m - 1)) (pset g j)
            refine ⟨x, h1, fun F h => (by cases h), fun j' h _ => ?_, fun h => ?_⟩
            · rw [← PState.int.inj h]; exact h2
            · exact absurd (PState.int.inj h) hj
      let g' := Function.update g m x
      have hg : ∀ i, i ≠ m → g' i = g i := fun i h => Function.update_of_ne h _ _
      have hgm : g' m = x := Function.update_self _ _ _
      have hold : ∀ i < m, pset g' i = pset g i := fun i hi =>
        pset_congr fun k hk => hg k (by omega)
      have hnew : pset g' m = {g (m - 1), x} := by
        unfold pset; rw [hgm, hg (m - 1) (by omega)]
      refine ⟨g', by rw [hg 0 (by omega)]; exact hg0, fun i hi => ?_, fun i hi1 hi => ?_⟩
      · by_cases him : i + 1 = m
        · rw [hg i (by omega), him, hgm, show i = m - 1 by omega]; exact hx1.symm
        · rw [hg i (by omega), hg (i + 1) him]; exact hprop i (by omega)
      · by_cases him : i = m
        · rw [him]
          refine ⟨fun F hF => ?_, fun j hj hjm => ?_, fun h => ?_⟩
          · rw [hnew]; exact hx2 F hF
          · obtain ⟨_, hji2, _, _⟩ := hint m j (by omega) (by omega) hj
            rw [hnew, hold j (by omega)]; exact hx3 j hj (by omega)
          · rw [hnew]; exact hx4 h
        · have hi' : i < m := by omega
          obtain ⟨h1, h2, h3⟩ := hsat i hi1 hi'
          refine ⟨fun F hF => ?_, fun j hj hjm => ?_, fun h => ?_⟩
          · rw [hold i hi']; exact h1 F hF
          · by_cases hjm' : j = m
            · rw [hjm'] at hj
              have hji := (hint i m hi1 (by omega) hj).1
              rw [hjm', hold i hi', hnew]; exact fun e => hx3 i hji (by omega) e.symm
            · rw [hold i hi', hold j (by omega)]; exact h2 j hj (by omega)
          · rw [hold i hi']; exact h3 h
  obtain ⟨g, hg0, hprop, hsat⟩ := key n hn le_rfl
  obtain ⟨x, hx1, hx2, hx3, hx4⟩ : ∃ x, x ≠ g (n - 1) ∧ x ≠ β ∧
      (∀ F, st n = .ext F → ({g (n - 1), x} : Finset (Fin 3)) ≠ F) ∧
      (∀ s, st n = .int s → ({g (n - 1), x} : Finset (Fin 3)) ≠ pset g s) := by
    cases hs : st n with
    | free =>
      obtain ⟨x, h1, h2, _⟩ := exists_close (g (n - 1)) β {β} (fun _ => by simp)
      exact ⟨x, h1, h2, fun F h => (by cases h), fun s h => (by cases h)⟩
    | ext F =>
      obtain ⟨x, h1, h2, h3⟩ := exists_close (g (n - 1)) β F (fun _ => hend F hs)
      exact ⟨x, h1, h2, fun F' h => (by cases h; exact h3), fun s h => (by cases h)⟩
    | int s =>
      have hs2 := hends s hs
      obtain ⟨hsn1, _, hs1, _⟩ := hint n s hn le_rfl hs
      have hb : β ∈ pset g s := (hsat s hs1 (by omega)).2.2 hsn1
      obtain ⟨x, h1, h2, h3⟩ := exists_close (g (n - 1)) β (pset g s) (fun _ => hb)
      exact ⟨x, h1, h2, fun F h => (by cases h), fun s' h => (by rw [← PState.int.inj h]; exact h3)⟩
  let g' := Function.update g n x
  have hg : ∀ i, i ≠ n → g' i = g i := fun i h => Function.update_of_ne h _ _
  have hgn : g' n = x := Function.update_self _ _ _
  have hold : ∀ i < n, pset g' i = pset g i := fun i hi => pset_congr fun k hk => hg k (by omega)
  have hnew : pset g' n = {g (n - 1), x} := by unfold pset; rw [hgn, hg (n - 1) (by omega)]
  refine ⟨g', by rw [hg 0 (by omega)]; exact hg0, fun i hi => ?_, by rw [hgn]; exact hx2,
    fun i F hi1 hin hF => ?_, fun i j hi1 hin hj => ?_⟩
  · by_cases him : i + 1 = n
    · rw [hg i (by omega), him, hgn, show i = n - 1 by omega]; exact hx1.symm
    · rw [hg i (by omega), hg (i + 1) him]; exact hprop i (by omega)
  · rcases Nat.lt_or_ge i n with hi | hi
    · rw [hold i hi]; exact (hsat i hi1 hi).1 F hF
    · have hin' : i = n := by omega
      rw [hin'] at hF ⊢; rw [hnew]; exact hx3 F hF
  · obtain ⟨hji, hji2, hj1, hjn⟩ := hint i j hi1 hin hj
    rcases Nat.lt_or_ge i n with hi | hi
    · rcases Nat.lt_or_ge j n with hj' | hj'
      · rw [hold i hi, hold j hj']; exact (hsat i hi1 hi).2.1 j hj hj'
      · have hjn' : j = n := by omega
        rw [hjn'] at hji ⊢
        rw [hold i hi, hnew]; exact fun e => hx4 i hji e.symm
    · have hin' : i = n := by omega
      rw [hin'] at hj
      rw [hin', hnew, hold j (by omega)]; exact hx4 j hj

end Bkls

end LeanPool.BalancedEdgeColourings
