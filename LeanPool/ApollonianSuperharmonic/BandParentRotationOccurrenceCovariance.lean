/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandSubtileOccurrence

-- [TABLET NODE: BandParentRotationOccurrenceCovariance]

/-!
# BandParentRotationOccurrenceCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandParentRotationOccurrenceCovariance
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (a : Fin 3) (T : ProtoTile) (_hT : BandPrototile (q 0) T)
    (S : Fin 3 → Bool → ProtoTile)
    (hS : ∀ i s, BandSubtileOccurrence q T i s (S i s))
    (hunion : ∀ x, x ∈ T.cells ↔ ∃ i s, x ∈ (S i s).cells) :
    let qa : Fin 4 → CircleCoordinates :=
      ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]
    let Sa : Fin 3 → Bool → ProtoTile := fun i s => S (a + i) s
    ProperBandQuadruple qa ∧
      (∀ i s, BandSubtileOccurrence qa T i s (Sa i s)) ∧
      (∀ x, x ∈ T.cells ↔ ∃ i s, x ∈ (Sa i s).cells) := by
-- BODY
  dsimp
  fin_cases a
  · refine ⟨?_, ?_, ?_⟩
    · have heq : ![q 0, q 1, q 2, q 3] = q := by
        funext i
        fin_cases i <;> rfl
      change ProperBandQuadruple ![q 0, q 1, q 2, q 3]
      rw [heq]
      exact hq
    · intro i s
      simp only [Fin.isValue, Fin.zero_eta, Fin.succ_zero_eq_one, zero_add,
        Fin.succ_one_eq_two, Fin.reduceSucc]
      have heq : ![q 0, q 1, q 2, q 3] = q := by
        funext j
        fin_cases j <;> rfl
      rw [heq]
      exact hS i s
    · simpa using hunion
  · refine ⟨?_, ?_, ?_⟩
    · refine ⟨SemiProperQuadruple.rotate hq.1, ?_⟩
      intro i
      fin_cases i
      · simpa using hq.2 (1 : Fin 3)
      · simpa using hq.2 (2 : Fin 3)
      · simpa using hq.2 (0 : Fin 3)
    · intro i s
      fin_cases i
      · simpa [BandSubtileOccurrence] using hS (1 : Fin 3) s
      · simpa [BandSubtileOccurrence] using hS (2 : Fin 3) s
      · simpa [BandSubtileOccurrence] using hS (0 : Fin 3) s
    · intro x
      constructor
      · intro hx
        rcases (hunion x).1 hx with ⟨i, s, hi⟩
        refine ⟨i - 1, s, ?_⟩
        simpa using hi
      · rintro ⟨i, s, hi⟩
        apply (hunion x).2
        exact ⟨1 + i, s, hi⟩
  · refine ⟨?_, ?_, ?_⟩
    · refine ⟨SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hq.1), ?_⟩
      intro i
      fin_cases i
      · simpa using hq.2 (2 : Fin 3)
      · simpa using hq.2 (0 : Fin 3)
      · simpa using hq.2 (1 : Fin 3)
    · intro i s
      fin_cases i
      · simpa [BandSubtileOccurrence] using hS (2 : Fin 3) s
      · simpa [BandSubtileOccurrence] using hS (0 : Fin 3) s
      · simpa [BandSubtileOccurrence] using hS (1 : Fin 3) s
    · intro x
      constructor
      · intro hx
        rcases (hunion x).1 hx with ⟨i, s, hi⟩
        refine ⟨i - 2, s, ?_⟩
        simpa using hi
      · rintro ⟨i, s, hi⟩
        apply (hunion x).2
        exact ⟨2 + i, s, hi⟩

end ApollonianSuperharmonic

end
