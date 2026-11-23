/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.BellmanFiniteness
public import LeanPool.Egyptian.BellmanArithmetic

/-! Splitting a path at its first numerator descent (§3.2–3.3). -/

@[expose] public section

namespace Egyptian.Control

theorem finish_small (s : State) (xs : List ℕ) (hs : s.p ≤ s.q) :
    (finish s xs).p ≤ (finish s xs).q := by
  induction xs generalizing s with
  | nil => exact hs
  | cons x xs ih => exact ih (step s x) ((Nat.sub_le _ _).trans (Nat.mul_le_mul_right _ hs))

/-- Every prefix keeps the cleared numerator at least its initial value. -/
def NoFall (s : State) (xs : List ℕ) : Prop :=
  ∀ k, k ≤ xs.length → s.p ≤ (finish s (xs.take k)).p

/-- A legal block ending at the first strict decrease of the cleared numerator. -/
def FallBlock (σ : Convention) (s : State) (xs : List ℕ) : Prop :=
  Controls σ s xs ∧ (finish s xs).p < s.p ∧
  ∀ k, k < xs.length → s.p ≤ (finish s (xs.take k)).p

theorem fall_ne_nil {σ s xs} (h : FallBlock σ s xs) : xs ≠ [] := by
  rintro rfl
  exact lt_irrefl _ h.2.1

theorem fall_interior {σ s xs} (hs : s.p ≤ s.q) (h : FallBlock σ s xs) :
    Interior (finish s xs) := by
  induction xs using List.reverseRecOn with
  | nil => exact (fall_ne_nil h rfl).elim
  | append_singleton ys x _ =>
    obtain ⟨_, hx⟩ := (controls_append s ys [x]).mp h.1
    have hprev := h.2.2 ys.length (by simp)
    rw [List.take_append_of_le_length le_rfl, List.take_length] at hprev
    have hh := h.2.1
    rw [finish_append] at hh ⊢
    exact first_fall_interior (by have := hx.1.2.1; omega)
      (finish_small s ys hs) hprev hh

/-- Exactly the two possibilities used in the stopped Bellman equation. -/
theorem split_at_fall {σ s xs} (hc : Controls σ s xs) :
    NoFall s xs ∨ ∃ b ys, xs = b ++ ys ∧ FallBlock σ s b := by
  classical
  by_cases h : NoFall s xs
  · exact Or.inl h
  · right
    have hex : ∃ k, k ≤ xs.length ∧ (finish s (xs.take k)).p < s.p := by
      simpa [NoFall, not_forall] using h
    let k := Nat.find hex
    obtain ⟨hkle, hfall⟩ := Nat.find_spec hex
    have hk : (xs.take k).length = k := by
      rw [List.length_take]
      exact Nat.min_eq_left hkle
    have hc' := controls_take hc k
    refine ⟨xs.take k, xs.drop k, (List.take_append_drop ..).symm, hc', hfall, ?_⟩
    intro j hj
    rw [hk] at hj
    have hmin := Nat.find_min hex hj
    have hle : j ≤ xs.length := hj.le.trans hkle
    have hstay : s.p ≤ (finish s (xs.take j)).p := by
      exact le_of_not_gt (fun bad => hmin ⟨hle,bad⟩)
    simpa [List.take_take, Nat.min_eq_left hj.le, Nat.min_eq_right hj.le] using hstay

theorem finite_short_falls (σ : Convention) (s : State) (M : ℕ) :
    Set.Finite {b | FallBlock σ s b ∧ b.length ≤ M} := by
  let pieces (n d : ℕ) := {b : List ℕ | b.length = n ∧ Controls σ s b ∧ (finish s b).p = d}
  have hfin := (Set.finite_le_nat M).biUnion (t := fun n =>
    ⋃ d ∈ {d : ℕ | d ≤ s.p}, pieces n d) (fun n _ =>
      (Set.finite_le_nat s.p).biUnion (fun d _ => finite_blocks σ n d s))
  apply hfin.subset
  intro b hb
  exact Set.mem_iUnion.mpr ⟨b.length, Set.mem_iUnion.mpr ⟨hb.2, Set.mem_iUnion.mpr
    ⟨(finish s b).p, Set.mem_iUnion.mpr ⟨hb.1.2.1.le,rfl,hb.1.1,rfl⟩⟩⟩⟩

/-- If p divides q at the initial state, every cleared numerator is divisible
by p. Positivity excludes a first descent in this case. -/
theorem noFall_unit {σ s xs} (hv : Valid s) (hd : s.p ∣ s.q) (hc : Controls σ s xs) :
    NoFall s xs := by
  have keep (s' : State) (ys : List ℕ) (hp : s.p ∣ s'.p) (hq : s.p ∣ s'.q) :
      s.p ∣ (finish s' ys).p := by
    induction ys generalizing s' with
    | nil => exact hp
    | cons x ys ih =>
      exact ih (step s' x) (Nat.dvd_sub (dvd_mul_of_dvd_left hp x) hq)
        (dvd_mul_of_dvd_left hq x)
  intro j _
  have hj := controls_take hc j
  exact Nat.le_of_dvd (finish_valid hv hj).1 (keep s _ (dvd_refl _) hd)

end Egyptian.Control
