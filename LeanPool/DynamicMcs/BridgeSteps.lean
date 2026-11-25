/-
Copyright (c) 2026 Md Thoriqul Islam Thonmay and Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Md Thoriqul Islam Thonmay, Gregory Morse
-/

-- Modified for Lean Pool.

module

public import LeanPool.DynamicMcs.Exec

/-! # Correctness of the executable tie break -/

@[expose] public section


namespace DynamicMcs

namespace BridgeSteps

variable {n : ℕ}

/-- R1: better never decreases cardinality w.r.t. the accumulated best. -/
lemma better_card_ge_acc (a : Adj) (chosen : List ℕ) (a0 v : ℕ) :
    cardC a chosen a0 ≤ cardC a chosen (better a chosen a0 v) := by
  by_cases h : cardC a chosen v > cardC a chosen a0 ∨
               (cardC a chosen v = cardC a chosen a0 ∧ v < a0)
  · have hle : cardC a chosen a0 ≤ cardC a chosen v := by
      rcases h with hgt | heq
      · exact le_of_lt hgt
      · exact le_of_eq heq.1.symm
    simpa [better, h] using hle
  · simp [better, h]

/-- R2: better never decreases cardinality w.r.t. the new candidate. -/
lemma better_card_ge_x (a : Adj) (chosen : List ℕ) (a0 v : ℕ) :
    cardC a chosen v ≤ cardC a chosen (better a chosen a0 v) := by
  by_cases h : cardC a chosen v > cardC a chosen a0 ∨
               (cardC a chosen v = cardC a chosen a0 ∧ v < a0)
  · simp [better, h]
  · have hle : cardC a chosen v ≤ cardC a chosen a0 := by
      by_contra hn
      exact h (Or.inl (lt_of_not_ge hn))
    simpa [better, h] using hle

/-- R3: if the accumulated best ties the result, the result is no larger
(keeps the smaller id on ties). -/
lemma better_tie_acc (a : Adj) (chosen : List ℕ) (a0 v : ℕ) :
    cardC a chosen a0 = cardC a chosen (better a chosen a0 v) →
      better a chosen a0 v ≤ a0 := by
  by_cases h : cardC a chosen v > cardC a chosen a0 ∨
               (cardC a chosen v = cardC a chosen a0 ∧ v < a0)
  · intro hEq
    have hcard : cardC a chosen a0 = cardC a chosen v := by
      simpa [better, h] using hEq
    by_cases hgt : cardC a chosen v > cardC a chosen a0
    · exfalso
      exact (not_lt_of_ge (le_of_eq hcard.symm)) hgt
    · have hle : v ≤ a0 := by
        rcases h with hge | heq
        · exact False.elim (hgt hge)
        · exact le_of_lt heq.2
      simpa [better, h] using hle
  · intro _
    simp [better, h]

/-- R4: if the new candidate ties the result, the result is no larger than it. -/
lemma better_tie_x (a : Adj) (chosen : List ℕ) (a0 v : ℕ) :
    cardC a chosen v = cardC a chosen (better a chosen a0 v) →
      better a chosen a0 v ≤ v := by
  by_cases h : cardC a chosen v > cardC a chosen a0 ∨
               (cardC a chosen v = cardC a chosen a0 ∧ v < a0)
  · intro _
    simp [better, h]
  · intro hEq
    have hcard : cardC a chosen v = cardC a chosen a0 := by
      simpa [better, h] using hEq
    have hnot_lt : ¬ v < a0 := by
      intro hvlt
      exact h (Or.inr ⟨hcard, hvlt⟩)
    simpa [better, h] using (le_of_not_gt hnot_lt)

/-- The foldl running-best invariant: after folding `better` over `l`
starting from seed `acc`, the result `w` is in `acc :: l`, dominates all of
`acc :: l` by cardinality, and is the smallest id among those achieving the
maximum cardinality. -/
def BetterInv (a : Adj) (chosen : List ℕ) (acc : ℕ) (l : List ℕ) (w : ℕ) : Prop :=
  w ∈ acc :: l ∧
  (∀ x ∈ acc :: l, cardC a chosen x ≤ cardC a chosen w) ∧
  (∀ x ∈ acc :: l, cardC a chosen x = cardC a chosen w → w ≤ x)

/-- One `better` step preserves `BetterInv`. -/
lemma better_step_inv (a : Adj) (chosen : List ℕ) (acc x : ℕ)
    (l : List ℕ) (w : ℕ) (h : BetterInv a chosen (better a chosen acc x) l w) :
    BetterInv a chosen acc (x :: l) w := by
  rcases h with ⟨hmem, hcard, htie⟩
  have hb_or : better a chosen acc x = acc ∨ better a chosen acc x = x := by
    unfold better
    by_cases c : cardC a chosen x > cardC a chosen acc ∨
                 (cardC a chosen x = cardC a chosen acc ∧ x < acc)
    · simp [c]
    · simp [c]
  constructor
  · -- w ∈ acc :: x :: l
    have hw_mem : w ∈ acc :: x :: l := by
      simp only [List.mem_cons]
      rcases hb_or with hba | hbx
      · rw [hba] at hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with hw1a | hw2a
        · exact Or.inl hw1a
        · exact Or.inr (Or.inr hw2a)
      · rw [hbx] at hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with hw1b | hw2b
        · exact Or.inr (Or.inl hw1b)
        · exact Or.inr (Or.inr hw2b)
    exact hw_mem
  constructor
  · -- dominance over acc :: x :: l
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with hyacc | hyx
    · subst y
      have hacc : cardC a chosen acc ≤ cardC a chosen (better a chosen acc x) :=
        better_card_ge_acc a chosen acc x
      have hb : cardC a chosen (better a chosen acc x) ≤ cardC a chosen w :=
        hcard (better a chosen acc x) (by simp)
      exact le_trans hacc hb
    · rcases hyx with hyeq | hyr
      · subst y
        have hx : cardC a chosen x ≤ cardC a chosen (better a chosen acc x) :=
          better_card_ge_x a chosen acc x
        have hb : cardC a chosen (better a chosen acc x) ≤ cardC a chosen w :=
          hcard (better a chosen acc x) (by simp)
        exact le_trans hx hb
      · exact hcard y (by simpa using (Or.inr hyr : y = better a chosen acc x ∨ y ∈ l))
  · -- tie-break over acc :: x :: l
    intro y hy hyEq
    simp only [List.mem_cons] at hy
    rcases hy with hyacc | hyx
    · subst y
      have hb : cardC a chosen (better a chosen acc x) ≤ cardC a chosen w :=
        hcard (better a chosen acc x) (by simp)
      have hEqb : cardC a chosen acc = cardC a chosen (better a chosen acc x) := by
        have h1 : cardC a chosen acc ≤ cardC a chosen (better a chosen acc x) :=
          better_card_ge_acc a chosen acc x
        have h2 : cardC a chosen (better a chosen acc x) ≤ cardC a chosen w := hb
        exact le_antisymm h1 (le_trans h2 (le_of_eq hyEq.symm))
      have hEqw : cardC a chosen (better a chosen acc x) = cardC a chosen w := by
        exact hEqb.symm.trans hyEq
      have h_le_b : better a chosen acc x ≤ acc := better_tie_acc a chosen acc x hEqb
      exact le_trans (htie (better a chosen acc x) (by simp) hEqw) h_le_b
    · rcases hyx with hyeq | hyr
      · subst y
        have hb : cardC a chosen (better a chosen acc x) ≤ cardC a chosen w :=
          hcard (better a chosen acc x) (by simp)
        have hEqb : cardC a chosen x = cardC a chosen (better a chosen acc x) := by
          have h1 : cardC a chosen x ≤ cardC a chosen (better a chosen acc x) :=
            better_card_ge_x a chosen acc x
          have h2 : cardC a chosen (better a chosen acc x) ≤ cardC a chosen w := hb
          exact le_antisymm h1 (le_trans h2 (le_of_eq hyEq.symm))
        have hEqw : cardC a chosen (better a chosen acc x) = cardC a chosen w := by
          exact hEqb.symm.trans hyEq
        have h_le_b : better a chosen acc x ≤ x := better_tie_x a chosen acc x hEqb
        exact le_trans (htie (better a chosen acc x) (by simp) hEqw) h_le_b
      · exact htie y (by simpa using (Or.inr hyr : y = better a chosen acc x ∨ y ∈ l)) hyEq

/-- Folding `better` over a list from a seed yields the lex-max (card desc,
id asc) of `acc :: l`. -/
lemma foldl_better_lex (a : Adj) (chosen : List ℕ) :
    ∀ (l : List ℕ) (acc : ℕ),
      BetterInv a chosen acc l (l.foldl (fun b v => better a chosen b v) acc) := by
  intro l
  induction l with
  | nil =>
      intro acc
      simp [BetterInv]
  | cons x tail ih =>
      intro acc
      have hstep := better_step_inv a chosen acc x tail
        (tail.foldl (fun b v => better a chosen b v) (better a chosen acc x))
        (ih (better a chosen acc x))
      simpa [List.foldl, better] using hstep

/-- `bestPick` returns a member of `rem` with maximum cardinality among
`rem` and smallest id on ties. -/
lemma bestPick_lex (a : Adj) (chosen : List ℕ) (rem : List ℕ) (hrem_ne : rem ≠ []) :
    let w := bestPick a chosen rem
    w ∈ rem ∧
    (∀ x ∈ rem, cardC a chosen x ≤ cardC a chosen w) ∧
    (∀ x ∈ rem, cardC a chosen x = cardC a chosen w → w ≤ x) := by
  intro w
  have hfold := foldl_better_lex a chosen rem (rem.headD 0)
  -- foldl over rem from seed headD 0 gives BetterInv seed rem w, w ∈ seed::rem
  have hmem0 : rem.headD 0 ∈ rem := by
    obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil hrem_ne
    rw [hy]
    simp [List.headD]
  rcases hfold with ⟨hwm, hcard, htie⟩
  constructor
  · -- w ∈ rem
    have hw_or : w = rem.headD 0 ∨ w ∈ rem := List.mem_cons.1 hwm
    rcases hw_or with hw | hw
    · simpa [hw] using hmem0
    · exact hw
  constructor
  · intro x hx
    exact hcard x (by simpa using (Or.inr hx : x = rem.headD 0 ∨ x ∈ rem))
  · intro x hx hEq
    exact htie x (by simpa using (Or.inr hx : x = rem.headD 0 ∨ x ∈ rem)) hEq

end BridgeSteps
end DynamicMcs
