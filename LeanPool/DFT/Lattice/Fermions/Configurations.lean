/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.HK.Basic

/-!
# Spinless lattice fermions: configurations and occupations

`Conf M N`: `N`-element subsets of the sites `Fin M`; `occF i s`: occupation of site `i`.
-/

@[expose] public section

namespace DFT

section

open Matrix

variable {M N : ℕ}

/-- Configurations of `N` spinless fermions on `M` sites. -/
abbrev Conf (M N : ℕ) := {s : Finset (Fin M) // s.card = N}

/-- Occupation numbers. -/
def occF (i : Fin M) (s : Conf M N) : ℝ := if i ∈ s.1 then 1 else 0

/-- Each configuration has exactly `N` occupied sites. -/
lemma sum_occF (s : Conf M N) : ∑ i, occF i s = (N : ℝ) := by
  simp [occF, Finset.sum_ite_mem, s.2]

/-- Occupations of `N`-particle configurations are rigid when `0 < N < M`. -/
theorem rigid_occF (hN0 : 0 < N) (hNM : N < M) : Rigid (occF : Fin M → Conf M N → ℝ) := by
  classical
  intro w κ h
  refine ⟨w ⟨0, by omega⟩, fun i => ?_⟩
  -- show w i = w j for all i, j
  have key : ∀ i j : Fin M, i ≠ j → w i = w j := by
    intro i j hij
    obtain ⟨s, hsi, hsj, hcard⟩ := Finset.exists_subsuperset_card_eq
      (s := {i}) (t := Finset.univ.erase j) (n := N)
      (by simpa using hij) (by simp; omega) (by simp; omega)
    have hi : i ∈ s := hsi (Finset.mem_singleton_self i)
    have hj : j ∉ s := fun h => (Finset.mem_erase.mp (hsj h)).1 rfl
    set s1 : Conf M N := ⟨s, hcard⟩
    have hcard2 : (insert j (s.erase i)).card = N := by
      rw [Finset.card_insert_of_notMem (fun h => hj (Finset.mem_of_mem_erase h)),
        Finset.card_erase_of_mem hi]; omega
    set s2 : Conf M N := ⟨insert j (s.erase i), hcard2⟩
    have e1 := h s1
    have e2 := h s2
    have hsum : ∀ (S : Finset (Fin M)), ∑ k, w k * (if k ∈ S then (1 : ℝ) else 0) =
        ∑ k ∈ S, w k := by
      intro S; simp [Finset.sum_ite_mem]
    simp only [occF] at e1 e2
    rw [hsum] at e1 e2
    simp only [s1, s2] at e1 e2
    rw [Finset.sum_insert (fun h => hj (Finset.mem_of_mem_erase h))] at e2
    rw [← Finset.add_sum_erase _ _ hi] at e1
    linarith
  by_cases hi : i = ⟨0, by omega⟩
  · rw [hi]
  · exact key i ⟨0, by omega⟩ hi

end

end DFT
