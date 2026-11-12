/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4715T1IndexAction
public import LeanPool.ApollonianSuperharmonic.P4715T1Arc
public import LeanPool.ApollonianSuperharmonic.P4715T1Region
public import Mathlib.Tactic.Module

-- [TABLET NODE: P4715T1CoefficientTranslation]

/-!
# P4715T1CoefficientTranslation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4715T1CoefficientTranslation (k : Int × Int) :
    (∀ a, P4715T1Position (P4715T1VertexShift k a) =
      P4715T1Position a + ((k.1 : Real), (k.2 : Real))) ∧
    (∀ a b, P4715T1Arc (P4715T1VertexShift k a) (P4715T1VertexShift k b) =
      (fun p : Real × Real => p + ((k.1 : Real), (k.2 : Real))) '' P4715T1Arc a b) ∧
    ∀ f, P4715T1Region (P4715T1FaceShift k f) =
      (fun p : Real × Real => p + ((k.1 : Real), (k.2 : Real))) '' P4715T1Region f := by
-- BODY
  have hp (a) : P4715T1Position (P4715T1VertexShift k a) =
      P4715T1Position a + ((k.1 : Real), (k.2 : Real)) := by
    ext <;> simp [P4715T1Position, P4715T1VertexShift,
      add_comm, add_left_comm]
  refine ⟨hp, ?_, ?_⟩
  · intro a b
    simp only [P4715T1Arc, hp]
    simpa only [add_comm] using
      (segment_translate_image Real ((k.1 : Real), (k.2 : Real))
        (P4715T1Position a) (P4715T1Position b)).symm
  · intro f
    have hf := P4715T1IndexAction.2.2.2.2.2 k f
    let K : Real × Real := ((k.1 : Real), (k.2 : Real))
    have hcombo (s t : Real) (p q r : Real × Real) :
        (1 - s - t) • (p + K) + s • (q + K) + t • (r + K) =
          ((1 - s - t) • p + s • q + t • r) + K := by module
    ext z
    constructor
    · rintro ⟨s, t, hs, ht, hst, hz⟩
      simp only [hf, hp] at hz
      refine ⟨_, ⟨s, t, hs, ht, hst, rfl⟩, ?_⟩
      exact (hz.trans (hcombo s t _ _ _)).symm
    · rintro ⟨y, ⟨s, t, hs, ht, hst, hy⟩, rfl⟩
      refine ⟨s, t, hs, ht, hst, ?_⟩
      simp only [hf, hp]
      rw [hcombo, hy]

end ApollonianSuperharmonic

end
