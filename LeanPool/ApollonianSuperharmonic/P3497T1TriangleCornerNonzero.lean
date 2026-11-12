/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3497T1StrictCornerSplice
public import Mathlib.Tactic.FinCases
public import LeanPool.ApollonianSuperharmonic.P3381T1PolygonBoundary

-- [TABLET NODE: P3497T1TriangleCornerNonzero]

/-!
# P3497T1TriangleCornerNonzero

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3497T1TriangleCornerNonzero (p : P3381T1PolygonBoundary 0) :
    ∀ i : Fin 3,
      P3381T1TriangleDeterminant (fun j : Fin 3 =>
        p.vertex (i + ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_left 3 0)⟩)) ≠ 0 := by
-- BODY
  intro i hd
  have hi1 : i ≠ i + 1 := by fin_cases i <;> decide
  have hi2 : i ≠ i + 2 := by fin_cases i <;> decide
  have h12 : i + 1 ≠ i + 2 := by fin_cases i <;> decide
  have hsucc : i + 1 + 1 = i + 2 := by fin_cases i <;> rfl
  have hclose : i + 2 + 1 = i := by fin_cases i <;> rfl
  let a := p.vertex i
  let b := p.vertex (i + 1)
  let c := p.vertex (i + 2)
  have hab : a ≠ b := p.injective.ne hi1
  have hac : a ≠ c := p.injective.ne hi2
  have hbc : b ≠ c := p.injective.ne h12
  have hf : (fun j : Fin 3 =>
      p.vertex (i + ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_left 3 0)⟩)) =
      ![a, b, c] := by
    funext j
    fin_cases j <;> simp [a, b, c]
  rw [hf] at hd
  have hint : segment Real a b ∩ segment Real b c = {b} := by
    have he := p.edge_intersection i (i + 1) hi1
    rw [hsucc] at he
    change segment Real a b ∩ segment Real b c =
      {x | (x = a ∨ x = b) ∧ (x = b ∨ x = c)} at he
    rw [he]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx | hx, hy | hy⟩
      · exact False.elim (hab (hx.symm.trans hy))
      · exact False.elim (hac (hx.symm.trans hy))
      · exact hx
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, Or.inl hx⟩
  obtain ⟨t, ht0, ht1, hformula, hsplice⟩ :=
    P3497T1StrictCornerSplice a b c hac hab hbc hd hint
  have hb : b ∈ segment Real a c := by
    rw [segment_eq_image]
    exact ⟨t, ⟨le_of_lt ht0, le_of_lt ht1⟩, hformula.symm⟩
  have he := p.edge_intersection i (i + 2) hi2
  rw [hclose] at he
  change segment Real a b ∩ segment Real c a =
    {x | (x = a ∨ x = b) ∧ (x = c ∨ x = a)} at he
  have hmem : b ∈ segment Real a b ∩ segment Real c a := by
    rw [segment_symm Real c a]
    exact ⟨right_mem_segment Real a b, hb⟩
  rw [he] at hmem
  rcases hmem.2 with h | h
  · exact hbc h
  · exact hab h.symm

end ApollonianSuperharmonic

end
