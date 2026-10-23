/-
Copyright (c) 2026 Richard Bean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Bean
-/
module

public import Mathlib.Data.Fintype.Pi

/-!
# Latin squares and defining sets

Coordinates and symbols are labelled. A defining set specifies the symbols
of a fixed Latin square on a finite set of cells. No unproved mathematical
hypotheses are incorporated into these definitions.
-/

@[expose] public section

namespace LatinQuarter

/-- A labelled row-column position in an order-`n` square. -/
abbrev Cell (n : ℕ) := Fin n × Fin n
/-- A symbol assignment to every labelled cell, before imposing the Latin condition. -/
abbrev Square (n : ℕ) := Fin n → Fin n → Fin n

/-- Every row and column contains every symbol exactly once. -/
def IsLatin {n : ℕ} (L : Square n) : Prop :=
  (∀ r, Function.Bijective (L r)) ∧
  (∀ c, Function.Bijective (fun r => L r c))

/-- The square `M` retains the clues that `L` gives on `P`. -/
def Agrees {n : ℕ} (P : Finset (Cell n)) (L M : Square n) : Prop :=
  ∀ p ∈ P, M p.1 p.2 = L p.1 p.2

/-- The Latin square `L` is uniquely determined by its entries on `P`. -/
def IsDefining {n : ℕ} (P : Finset (Cell n)) (L : Square n) : Prop :=
  IsLatin L ∧ ∀ M, IsLatin M → Agrees P L M → M = L

/-- All labelled Latin squares extending the specified clues from `L`. -/
noncomputable def completions {n : ℕ} (P : Finset (Cell n))
    (L : Square n) : Finset (Square n) := by
  classical
  exact Finset.univ.filter (fun M => IsLatin M ∧ Agrees P L M)

@[simp] theorem mem_completions {n : ℕ} {P : Finset (Cell n)}
    {L M : Square n} :
    M ∈ completions P L ↔ IsLatin M ∧ Agrees P L M := by
  classical
  simp [completions]

theorem defining_iff_completions_eq_singleton {n : ℕ}
    (P : Finset (Cell n)) (L : Square n) :
    IsDefining P L ↔ completions P L = {L} := by
  classical
  constructor
  · rintro ⟨hL, hu⟩
    ext M
    simp only [mem_completions, Finset.mem_singleton]
    constructor
    · rintro ⟨hM, ha⟩
      exact hu M hM ha
    · rintro rfl
      exact ⟨hL, fun _ _ => rfl⟩
  · intro h
    have hL : L ∈ completions P L := by simp [h]
    refine ⟨(mem_completions.mp hL).1, ?_⟩
    intro M hM ha
    have hm : M ∈ completions P L := mem_completions.mpr ⟨hM, ha⟩
    simpa [h] using hm

theorem defining_completion_count {n : ℕ} {P : Finset (Cell n)}
    {L : Square n} (h : IsDefining P L) :
    (completions P L).card = 1 := by
  rw [(defining_iff_completions_eq_singleton P L).mp h]
  exact Finset.card_singleton L

end LatinQuarter
