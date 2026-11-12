/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidence
public import LeanPool.ApollonianSuperharmonic.SixSubtileFaceVertices
public import Mathlib.Tactic.FinCases

-- [TABLET NODE: P4623T1ZeroBlockLinks]

/-!
# P4623T1ZeroBlockLinks

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4623T1ZeroBlockLinks :
    let K : Finset PeriodicSubtileIndex :=
      {⟨.A, 0, 0⟩, ⟨.B, 0, 0⟩, ⟨.C, 0, 0⟩,
        ⟨.D, 0, 0⟩, ⟨.E, 0, 0⟩, ⟨.F, 0, 0⟩}
    ∀ d ∈ K, ∃ (n : Nat) (neighbor : Fin n → PeriodicSubtileIndex)
        (face : Fin (n + 1) → PeriodicSubtileFaceIndex),
      0 < n ∧ Function.Injective neighbor ∧ Function.Injective face ∧
      (∀ b, b ∈ K.erase d ∧ AllowedSubtileIncidence d b ↔
        ∃ k, neighbor k = b) ∧
      ∀ k,
        (∃ i, SixSubtileFaceVertices (face (Fin.castSucc k)) i = d) ∧
        (∃ i, SixSubtileFaceVertices (face (Fin.castSucc k)) i = neighbor k) ∧
        (∃ i, SixSubtileFaceVertices (face k.succ) i = d) ∧
        (∃ i, SixSubtileFaceVertices (face k.succ) i = neighbor k) := by
-- BODY
  classical
  dsimp only
  let K : Finset PeriodicSubtileIndex :=
    {⟨.A, 0, 0⟩, ⟨.B, 0, 0⟩, ⟨.C, 0, 0⟩,
      ⟨.D, 0, 0⟩, ⟨.E, 0, 0⟩, ⟨.F, 0, 0⟩}
  let central : SixSubtileLabel → SixSubtileLabel → Prop := fun a b ↦
    match a, b with
    | .A, .B | .B, .A | .A, .C | .C, .A | .A, .D | .D, .A
    | .A, .F | .F, .A | .B, .C | .C, .B | .B, .D | .D, .B
    | .B, .E | .E, .B | .C, .F | .F, .C | .D, .E | .E, .D => True
    | _, _ => False
  have reverse (a b) : central a b → central b a := by
    cases a <;> cases b <;> decide
  have bound {a b : PeriodicSubtileIndex} (h : AllowedSubtileIncidence a b) :
      a.first = 0 → a.second = 0 → b.first = 0 → b.second = 0 →
        central a.label b.label := by
    induction h with
    | symm h ih =>
      intro ha hn hb hm
      exact reverse _ _ (ih hb hm ha hn)
    | AB m n | AB01 m n | AB11 m n | AC m n | AC11 m n
      | AD m n | AE01 m n | AF m n | BC m n | BDm1m1 m n
      | BD m n | BE m n | BF0m1 m n | CDm10 m n | CEm10 m n
      | CF m n | DE m n | DF10 m n =>
      dsimp [central]
      intros
      first | trivial | omega
  have adjzero (a b : SixSubtileLabel) :
      AllowedSubtileIncidence ⟨a, 0, 0⟩ ⟨b, 0, 0⟩ ↔ central a b := by
    constructor
    · intro h
      exact bound h rfl rfl rfl rfl
    · intro h
      cases a <;> cases b <;> dsimp [central] at h
      all_goals first
        | exact AllowedSubtileIncidence.AB 0 0
        | exact (AllowedSubtileIncidence.AB 0 0).symm
        | exact AllowedSubtileIncidence.AC 0 0
        | exact (AllowedSubtileIncidence.AC 0 0).symm
        | exact AllowedSubtileIncidence.AD 0 0
        | exact (AllowedSubtileIncidence.AD 0 0).symm
        | exact AllowedSubtileIncidence.AF 0 0
        | exact (AllowedSubtileIncidence.AF 0 0).symm
        | exact AllowedSubtileIncidence.BC 0 0
        | exact (AllowedSubtileIncidence.BC 0 0).symm
        | exact AllowedSubtileIncidence.BD 0 0
        | exact (AllowedSubtileIncidence.BD 0 0).symm
        | exact AllowedSubtileIncidence.BE 0 0
        | exact (AllowedSubtileIncidence.BE 0 0).symm
        | exact AllowedSubtileIncidence.CF 0 0
        | exact (AllowedSubtileIncidence.CF 0 0).symm
        | exact AllowedSubtileIncidence.DE 0 0
        | exact (AllowedSubtileIncidence.DE 0 0).symm
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
  | refine ⟨4, ![⟨.D, 0, 0⟩, ⟨.B, 0, 0⟩, ⟨.C, 0, 0⟩, ⟨.F, 0, 0⟩],
      ![⟨.J4, 0, 0⟩, ⟨.I2, 0, 0⟩, ⟨.I1, 0, 0⟩, ⟨.I3, 0, 0⟩,
        ⟨.J2, 0, 0⟩], by decide, by decide, by decide, ?_, by decide⟩
  | refine ⟨4, ![⟨.C, 0, 0⟩, ⟨.A, 0, 0⟩, ⟨.D, 0, 0⟩, ⟨.E, 0, 0⟩],
      ![⟨.J3, -1, -1⟩, ⟨.I1, 0, 0⟩, ⟨.I2, 0, 0⟩, ⟨.I4, 0, 0⟩,
        ⟨.J1, 0, -1⟩], by decide, by decide, by decide, ?_, by decide⟩
  | refine ⟨3, ![⟨.B, 0, 0⟩, ⟨.A, 0, 0⟩, ⟨.F, 0, 0⟩],
      ![⟨.J3, -1, -1⟩, ⟨.I1, 0, 0⟩, ⟨.I3, 0, 0⟩, ⟨.J8, 0, 0⟩],
      by decide, by decide, by decide, ?_, by decide⟩
  | refine ⟨3, ![⟨.A, 0, 0⟩, ⟨.B, 0, 0⟩, ⟨.E, 0, 0⟩],
      ![⟨.J4, 0, 0⟩, ⟨.I2, 0, 0⟩, ⟨.I4, 0, 0⟩, ⟨.J7, 1, 0⟩],
      by decide, by decide, by decide, ?_, by decide⟩
  | refine ⟨2, ![⟨.B, 0, 0⟩, ⟨.D, 0, 0⟩],
      ![⟨.J1, 0, -1⟩, ⟨.I4, 0, 0⟩, ⟨.J7, 1, 0⟩],
      by decide, by decide, by decide, ?_, by decide⟩
  | refine ⟨2, ![⟨.A, 0, 0⟩, ⟨.C, 0, 0⟩],
      ![⟨.J2, 0, 0⟩, ⟨.I3, 0, 0⟩, ⟨.J8, 0, 0⟩],
      by decide, by decide, by decide, ?_, by decide⟩
  all_goals
    intro b
    by_cases hb : b ∈ K
    · simp only [K, Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals rw [adjzero]; decide
    · constructor
      · intro h
        exact (hb (Finset.mem_of_mem_erase h.1)).elim
      · rintro ⟨k, rfl⟩
        exact (hb (by fin_cases k <;> decide)).elim

end ApollonianSuperharmonic

end
