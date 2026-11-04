/-
Copyright (c) 2026 Richard Bean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Bean
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.LatinQuarter.Main
public import LeanPool.LatinQuarter.Parity

/-!
# Theorems A and B in the paper's own terms

Written by Claude (Anthropic) at Richard Bean's request, October 2026, for
version 0.2.0.

This file restates Theorems A and B of the paper (Bean, arXiv:2610.18199)
with the definitions of its Section 1, written from scratch, and derives
them from the rest of the package. The definitions below do not use
`IsLatin`, `Agrees`, `IsDefining`, `IsCritical` or `scs`, so a reader can
check the claim against the paper by reading this file alone.

* A Latin square of order `n` has each symbol exactly once in every row and
  exactly once in every column. Rows, columns and symbols are `Fin n`, and
  squares are counted with their labels.
* A filled cell is a triple (row, column, symbol). Theorem A is stated for
  every finite set of triples, which covers every partial Latin square. A set
  that puts two symbols in one cell, or repeats a symbol in a row or column,
  has no completions.
* A completion of a set of filled cells is a Latin square that agrees with
  every one of them, and `numCompletions T` is their number (`N(P)` in the
  paper).
* A defining set of `L` agrees with `L` and has `L` as its only completion.
  It is critical if emptying any one of its filled cells leaves more than one
  completion.
* `scsOf L` is the smallest size of a critical set of `L`, and `scs n` is the
  minimum of `scsOf L` over all Latin squares `L` of order `n`.
-/

@[expose] public section

namespace LatinQuarter.Textbook

/-- Each symbol occurs exactly once in every row and exactly once in every
column. -/
def Latin {n : ℕ} (L : Fin n → Fin n → Fin n) : Prop :=
  (∀ r s, ∃! c, L r c = s) ∧ (∀ c s, ∃! r, L r c = s)

/-- `L` is a completion of `T`: a Latin square that agrees with every filled
cell (row, column, symbol) of `T`. -/
def Completes {n : ℕ} (T : Finset (Fin n × Fin n × Fin n))
    (L : Fin n → Fin n → Fin n) : Prop :=
  Latin L ∧ ∀ t ∈ T, L t.1 t.2.1 = t.2.2

/-- The number of completions of `T`, written `N(P)` in the paper. -/
noncomputable def numCompletions {n : ℕ} (T : Finset (Fin n × Fin n × Fin n)) : ℕ :=
  Nat.card {L : Fin n → Fin n → Fin n // Completes T L}

/-- `T` is a defining set of `L`: `L` is a completion of `T`, and the only one. -/
def DefiningSet {n : ℕ} (L : Fin n → Fin n → Fin n)
    (T : Finset (Fin n × Fin n × Fin n)) : Prop :=
  Completes T L ∧ ∀ M, Completes T M → M = L

/-- A defining set of `L` is critical if emptying any one of its filled cells
leaves more than one completion. -/
def CriticalSet {n : ℕ} (L : Fin n → Fin n → Fin n)
    (T : Finset (Fin n × Fin n × Fin n)) : Prop :=
  DefiningSet L T ∧ ∀ t ∈ T, 1 < numCompletions (T.erase t)

/-- `scs(L)`: the smallest number of filled cells in a critical set of `L`. -/
noncomputable def scsOf {n : ℕ} (L : Fin n → Fin n → Fin n) : ℕ :=
  sInf {m | ∃ T, CriticalSet L T ∧ T.card = m}

/-- `scs(n)`: the minimum of `scs(L)` over all Latin squares `L` of order `n`. -/
noncomputable def scs (n : ℕ) : ℕ :=
  sInf {m | ∃ L : Fin n → Fin n → Fin n, Latin L ∧ scsOf L = m}

/-- The cyclic square `B_n`, whose entry in cell `(r, c)` is `(r + c) mod n`. -/
def cyclicSquare (n : ℕ) : Fin n → Fin n → Fin n :=
  fun r c => ⟨(r.val + c.val) % n, Nat.mod_lt _ r.pos⟩

/-! ## Agreement with the package's definitions -/

theorem latin_iff {n : ℕ} (L : Fin n → Fin n → Fin n) : Latin L ↔ IsLatin L := by
  simp only [Latin, IsLatin, Function.bijective_iff_existsUnique]

theorem cyclicSquare_eq (n : ℕ) : cyclicSquare n = cyclic n := by
  funext r c
  apply Fin.ext
  rfl

/-- Once `L` completes `T`, the completions of `T` are the Latin squares that
agree with `L` on the cells of `T`. -/
theorem completes_iff {n : ℕ} {T : Finset (Fin n × Fin n × Fin n)}
    {L : Fin n → Fin n → Fin n} (hL : Completes T L) (M : Fin n → Fin n → Fin n) :
    Completes T M ↔ IsLatin M ∧ Agrees (T.image fun t => (t.1, t.2.1)) L M := by
  constructor
  · rintro ⟨hM, hMT⟩
    refine ⟨(latin_iff M).mp hM, ?_⟩
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    exact (hMT t ht).trans (hL.2 t ht).symm
  · rintro ⟨hM, hMa⟩
    refine ⟨(latin_iff M).mpr hM, ?_⟩
    intro t ht
    exact (hMa _ (Finset.mem_image.mpr ⟨t, ht, rfl⟩)).trans (hL.2 t ht)

theorem numCompletions_eq {n : ℕ} {T : Finset (Fin n × Fin n × Fin n)}
    {L : Fin n → Fin n → Fin n} (hL : Completes T L) :
    numCompletions T = (completions (T.image fun t => (t.1, t.2.1)) L).card := by
  rw [numCompletions, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun M =>
    (completes_iff hL M).trans mem_completions.symm)

theorem numCompletions_eq_one {n : ℕ} {L : Fin n → Fin n → Fin n}
    {T : Finset (Fin n × Fin n × Fin n)} (h : DefiningSet L T) :
    numCompletions T = 1 := by
  rw [numCompletions, Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => Subtype.ext ((h.2 a.1 a.2).trans (h.2 b.1 b.2).symm)⟩,
    ⟨⟨L, h.1⟩⟩⟩

/-! ## Theorem A -/

/-- **Theorem A.** A set of fewer than `⌊n²/4⌋` filled cells has an even
number of completions. -/
theorem completions_even {n : ℕ} (T : Finset (Fin n × Fin n × Fin n))
    (hT : T.card < n * n / 4) : Even (numCompletions T) := by
  by_cases h : ∃ L, Completes T L
  · obtain ⟨L, hL⟩ := h
    rw [numCompletions_eq hL]
    exact completions_card_even _ L ((latin_iff L).mp hL.1)
      (lt_of_le_of_lt Finset.card_image_le hT)
  · have : IsEmpty {L : Fin n → Fin n → Fin n // Completes T L} :=
      ⟨fun L => h ⟨L.1, L.2⟩⟩
    rw [numCompletions, Nat.card_of_isEmpty]
    exact Even.zero

/-- Since `1` is odd, Theorem A gives the lower bound: every defining set of
every Latin square of order `n` has at least `⌊n²/4⌋` filled cells. -/
theorem definingSet_card {n : ℕ} {L : Fin n → Fin n → Fin n}
    {T : Finset (Fin n × Fin n × Fin n)} (h : DefiningSet L T) :
    n * n / 4 ≤ T.card := by
  by_contra hlt
  have he := completions_even T (not_le.mp hlt)
  rw [numCompletions_eq_one h] at he
  exact Nat.not_even_one he

/-! ## Theorem B -/

/-- Emptying filled cells one at a time while the completion stays unique ends
at a critical set. -/
theorem exists_criticalSet_subset {n : ℕ} {L : Fin n → Fin n → Fin n} :
    ∀ (k : ℕ) (T : Finset (Fin n × Fin n × Fin n)), T.card = k →
      DefiningSet L T → ∃ T' ⊆ T, CriticalSet L T' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro T hk hT
    by_cases hc : ∀ t ∈ T, 1 < numCompletions (T.erase t)
    · exact ⟨T, subset_refl T, hT, hc⟩
    push Not at hc
    obtain ⟨t, ht, hle⟩ := hc
    have hLc : Completes (T.erase t) L :=
      ⟨hT.1.1, fun u hu => hT.1.2 u (Finset.mem_of_mem_erase hu)⟩
    rw [numCompletions] at hle
    have hsub := (Finite.card_le_one_iff_subsingleton).mp hle
    have hdef : DefiningSet L (T.erase t) :=
      ⟨hLc, fun M hM => congrArg Subtype.val
        (Subsingleton.elim (⟨M, hM⟩ : {M // Completes (T.erase t) M}) ⟨L, hLc⟩)⟩
    obtain ⟨T', hsub', hcrit⟩ := ih (T.erase t).card
      (hk ▸ Finset.card_erase_lt_of_mem ht) (T.erase t) rfl hdef
    exact ⟨T', hsub'.trans (Finset.erase_subset t T), hcrit⟩

/-- Every Latin square has a critical set: start from all `n²` filled cells. -/
theorem exists_criticalSet {n : ℕ} {L : Fin n → Fin n → Fin n} (hL : Latin L) :
    ∃ T, CriticalSet L T := by
  let T := (Finset.univ : Finset (Fin n × Fin n)).image
    (fun p => (p.1, p.2, L p.1 p.2))
  have hT : DefiningSet L T := by
    refine ⟨⟨hL, ?_⟩, ?_⟩
    · intro t ht
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ht
      rfl
    · intro M hM
      funext r c
      exact hM.2 (r, c, L r c) (Finset.mem_image.mpr ⟨(r, c), Finset.mem_univ _, rfl⟩)
  obtain ⟨T', _, hT'⟩ := exists_criticalSet_subset T.card T rfl hT
  exact ⟨T', hT'⟩

theorem quarter_le_scsOf {n : ℕ} {L : Fin n → Fin n → Fin n} (hL : Latin L) :
    n * n / 4 ≤ scsOf L := by
  obtain ⟨T, hT⟩ := exists_criticalSet hL
  unfold scsOf
  exact le_csInf ⟨T.card, T, hT, rfl⟩ (by
    rintro m ⟨T', hT', rfl⟩
    exact definingSet_card hT'.1)

/-- The two corner triangles of `B_n` form a critical set of size `⌊n²/4⌋`. -/
theorem cyclic_criticalSet (n : ℕ) (hn : 0 < n) :
    ∃ T, CriticalSet (cyclicSquare n) T ∧ T.card = n * n / 4 := by
  let f : Fin n × Fin n → Fin n × Fin n × Fin n :=
    fun p => (p.1, p.2, cyclicSquare n p.1 p.2)
  have hf : Function.Injective f := by
    intro p q h
    simp only [f, Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.1
  let T := (cornerSet n).image f
  have hcard : T.card = n * n / 4 := by
    rw [Finset.card_image_of_injective _ hf, cornerSet_card n hn]
  have hdef := cornerSet_isDefining n hn
  have hlat : Latin (cyclicSquare n) := by
    rw [latin_iff, cyclicSquare_eq]
    exact hdef.1
  have hcomp : Completes T (cyclicSquare n) := by
    refine ⟨hlat, ?_⟩
    intro t ht
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ht
    rfl
  have hT : DefiningSet (cyclicSquare n) T := by
    refine ⟨hcomp, ?_⟩
    intro M hM
    rw [cyclicSquare_eq]
    apply hdef.2 M ((latin_iff M).mp hM.1)
    intro p hp
    have hMp : M p.1 p.2 = cyclicSquare n p.1 p.2 :=
      hM.2 (f p) (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    rw [hMp, cyclicSquare_eq]
  refine ⟨T, ⟨hT, ?_⟩, hcard⟩
  intro t ht
  have hLc : Completes (T.erase t) (cyclicSquare n) :=
    ⟨hlat, fun u hu => hcomp.2 u (Finset.mem_of_mem_erase hu)⟩
  by_contra hle
  rw [not_lt, numCompletions] at hle
  have hsub := (Finite.card_le_one_iff_subsingleton).mp hle
  have hdef' : DefiningSet (cyclicSquare n) (T.erase t) :=
    ⟨hLc, fun M hM => congrArg Subtype.val
      (Subsingleton.elim (⟨M, hM⟩ : {M // Completes (T.erase t) M}) ⟨_, hLc⟩)⟩
  have h1 := definingSet_card hdef'
  have h2 := Finset.card_erase_lt_of_mem ht
  rw [hcard] at h2
  exact (not_le.mpr h2) h1

/-- **Theorem B.** For every `n ≥ 1`, `scs(n) = scs(B_n) = ⌊n²/4⌋`. -/
theorem scs_eq_quarter (n : ℕ) (hn : 0 < n) :
    scs n = n * n / 4 ∧ scsOf (cyclicSquare n) = n * n / 4 := by
  obtain ⟨T, hT, hcard⟩ := cyclic_criticalSet n hn
  have hlat : Latin (cyclicSquare n) := hT.1.1.1
  have hcyc : scsOf (cyclicSquare n) = n * n / 4 := by
    apply le_antisymm _ (quarter_le_scsOf hlat)
    rw [← hcard]
    unfold scsOf
    exact Nat.sInf_le ⟨T, hT, rfl⟩
  refine ⟨le_antisymm ?_ ?_, hcyc⟩
  · rw [← hcyc]
    unfold scs
    exact Nat.sInf_le ⟨cyclicSquare n, hlat, rfl⟩
  · unfold scs
    exact le_csInf ⟨_, cyclicSquare n, hlat, rfl⟩ (by
      rintro m ⟨L, hL, rfl⟩
      exact quarter_le_scsOf hL)

/-- A check of the definitions alone, at order 2: the empty set of filled cells
has a second completion besides `B_2`, so it is not a defining set. -/
example : ¬ DefiningSet (cyclicSquare 2) ∅ := by
  rintro ⟨_, huniq⟩
  have hM : Completes (∅ : Finset (Fin 2 × Fin 2 × Fin 2)) (fun r c => r + c + 1) :=
    ⟨(latin_iff _).mpr (by unfold IsLatin; decide), by simp⟩
  have h := congrFun (congrFun (huniq _ hM) 0) 0
  revert h
  decide

end LatinQuarter.Textbook
