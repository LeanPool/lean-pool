/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesDataPrefix
public import LeanPool.GoldbergSeymour.TashkinovStoredColors
public import Mathlib.Data.Fintype.EquivFin

/-!
# Tashkinov Stored Colors Prefix

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashkinovStoredColorsPrefix {V E : Type*} [Finite V] [Fintype E]
     {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    (m : ℕ) (hm : m ≤ rounds) (data : TashkinovSeriesData G k rounds e0)
    (i : Fin (m + 1)) :
    TashkinovStoredColors (TashkinovSeriesDataPrefix m hm data) i =
      TashkinovStoredColors data (Fin.castLE (by omega) i) := by
  classical
  let _ := Fintype.ofFinite V
  unfold TashkinovStoredColors
  simp only [TashkinovSeriesDataPrefix]
  split <;> rename_i hz
  · rw [ite_eq_left]
    exact hz
  · rw [ite_eq_right]
    · congr 1
      ext c
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, hj⟩
        by_cases hji : j.val ≤ i.val
        · refine ⟨Fin.castLE (by omega) j, ?_⟩
          simpa [hji] using hj
        · simp [hji] at hj
      · rintro ⟨j, hj⟩
        by_cases hji : j.val ≤ i.val
        · let j' : Fin (m + 1) := ⟨j.val, by omega⟩
          refine ⟨j', ?_⟩
          simpa [j', hji] using hj
        · simp [hji] at hj
    · exact hz

end GoldbergSeymour

end
