/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.Betting

/-!
# Scans that read the two bits of a digit consecutively

A pair-respecting scan starts each pair at an even position and reads its odd
partner immediately, independently of the first answer.  The hit equivalence
below concerns prescribed answer sequences, as used by the pool construction.
-/

@[expose] public section

namespace Klr

/-- Reading the two bits of each base-four digit consecutively, even bit first. -/
def ScanRule.PairRespecting (π : ScanRule) : Prop :=
  ∀ v : List Bool, v.length % 2 = 0 →
    π.query v % 2 = 0 ∧ ∀ b : Bool, π.query (v ++ [b]) = π.query v + 1

/-- The strategy scans both bits of each pair consecutively in the prescribed order. -/
def BettingStrategy.PairRespecting (s : BettingStrategy) : Prop :=
  s.scan.PairRespecting

/-- Resistance to the binary strategies that read whole pairs of coordinates. -/
def PairRespectingRandom (X : Cantor) : Prop :=
  ∀ s : BettingStrategy, s.PairRespecting → ¬ s.Succeeds X

theorem ScanRule.monotone_pairRespecting : ScanRule.monotone.PairRespecting := by
  intro v hv
  refine ⟨hv, ?_⟩
  intro b
  simp [ScanRule.monotone]

theorem KolmogorovLovelandRandom.pairRespectingRandom {X : Cantor}
    (hX : KolmogorovLovelandRandom X) : PairRespectingRandom X :=
  fun s _ => hX s

namespace ScanRule.PairRespecting

variable {π : ScanRule} (hπ : π.PairRespecting)

include hπ

theorem even_query (Z : Cantor) (n : ℕ) :
    π.query (ScanRule.inputPrefix Z (2 * n)) % 2 = 0 :=
  (hπ _ (by simp [ScanRule.inputPrefix])).1

theorem odd_query (Z : Cantor) (n : ℕ) :
    π.query (ScanRule.inputPrefix Z (2 * n + 1)) =
      π.query (ScanRule.inputPrefix Z (2 * n)) + 1 := by
  have hs : ScanRule.inputPrefix Z (2 * n + 1) =
      ScanRule.inputPrefix Z (2 * n) ++ [Z (2 * n)] := by
    simp [ScanRule.inputPrefix, List.range_succ]
  rw [hs]
  exact (hπ _ (by simp [ScanRule.inputPrefix])).2 _

theorem query_parity (Z : Cantor) (t : ℕ) :
    π.query (ScanRule.inputPrefix Z t) % 2 = t % 2 := by
  have ht : t = 2 * (t / 2) + t % 2 := by omega
  have hmod : t % 2 = 0 ∨ t % 2 = 1 := by omega
  rcases hmod with h | h
  · have he : t = 2 * (t / 2) := by omega
    rw [he]
    simpa using hπ.even_query Z (t / 2)
  · have he : t = 2 * (t / 2) + 1 := by omega
    rw [he, hπ.odd_query]
    have hq := hπ.even_query Z (t / 2)
    omega

/-- Both members of a pair are read, or both are missed, on every answer path.
The statement deliberately uses eventual reads; finite horizons may end between
the two members of a pair. -/
theorem reads_even_iff_reads_odd (Z : Cantor) (n : ℕ) :
    (∃ t, π.query (ScanRule.inputPrefix Z t) = 2 * n) ↔
      (∃ t, π.query (ScanRule.inputPrefix Z t) = 2 * n + 1) := by
  constructor
  · rintro ⟨t, ht⟩
    have hp := hπ.query_parity Z t
    have he : t = 2 * (t / 2) := by omega
    refine ⟨t + 1, ?_⟩
    rw [he, hπ.odd_query]
    rw [← he, ht]
  · rintro ⟨t, ht⟩
    have hp := hπ.query_parity Z t
    have he : t = 2 * (t / 2) + 1 := by omega
    refine ⟨2 * (t / 2), ?_⟩
    rw [he, hπ.odd_query] at ht
    omega

/-- Dividing the query positions by two identifies either bit of a digit.
The divided query tree need not be fresh, since each digit is read twice. -/
theorem reads_div_two_iff (Z : Cantor) (n c : ℕ) (hc : c < 2) :
    (∃ t, π.query (ScanRule.inputPrefix Z t) / 2 = n) ↔
      (∃ t, π.query (ScanRule.inputPrefix Z t) = 2 * n + c) := by
  have hc' : c = 0 ∨ c = 1 := by omega
  constructor
  · rintro ⟨t, ht⟩
    have hq : π.query (ScanRule.inputPrefix Z t) = 2 * n ∨
        π.query (ScanRule.inputPrefix Z t) = 2 * n + 1 := by omega
    rcases hc' with rfl | rfl
    · simp only [Nat.add_zero]
      rcases hq with hq | hq
      · exact ⟨t, hq⟩
      · exact (hπ.reads_even_iff_reads_odd Z n).mpr ⟨t, hq⟩
    · rcases hq with hq | hq
      · exact (hπ.reads_even_iff_reads_odd Z n).mp ⟨t, hq⟩
      · exact ⟨t, hq⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, by omega⟩

end ScanRule.PairRespecting

end Klr
