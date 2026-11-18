/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4828T1Evaluate
public import LeanPool.ApollonianSuperharmonic.P4828T1LeftRootGeometry
public import LeanPool.ApollonianSuperharmonic.P4828T1RightRootGeometry
public import LeanPool.ApollonianSuperharmonic.P4828T1CircularPlacement
public import LeanPool.ApollonianSuperharmonic.P4828T1LinePlacement
public import LeanPool.ApollonianSuperharmonic.P4828T1ConstructorSupport
public import LeanPool.ApollonianSuperharmonic.P4828T1ResidualPatches

-- [TABLET NODE: P4828T1HistoryRealization]

/-!
# P4828T1HistoryRealization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4828T1HistoryRealization (a : GaussianInt) (side : Bool)
    (word : List (Fin 3)) :
    let L : Real := 2 * (a.re : Real)
    let q := P4828T1Evaluate a side word
    (ProperBandQuadruple q ∧ P4828T1LineSupport L q ∧
      P4828T1Disk (q 0) ⊆ P4828T1Gap L q) ∧
    (∀ b : Fin 3,
      P4828T1Gap L (P4828T1Evaluate a side (word ++ [b])) ⊆
        P4828T1Gap L q ∧
      Disjoint (P4828T1Gap L (P4828T1Evaluate a side (word ++ [b])))
        (P4828T1Disk (q 0))) ∧
    (∀ b c : Fin 3, b ≠ c →
      Disjoint (P4828T1Gap L (P4828T1Evaluate a side (word ++ [b])))
        (P4828T1Gap L (P4828T1Evaluate a side (word ++ [c])))) := by
-- BODY
  have state : ∀ w : List (Fin 3),
      let q := P4828T1Evaluate a side w
      ProperBandQuadruple q ∧ P4828T1LineSupport (2 * (a.re : Real)) q ∧
        P4828T1Disk (q 0) ⊆ P4828T1Gap (2 * (a.re : Real)) q := by
    intro w
    induction w using List.reverseRecOn with
    | nil =>
        cases side
        · exact ⟨(P4828T1LeftRootGeometry a).1,
            (P4828T1LeftRootGeometry a).2.1,
            (P4828T1LeftRootGeometry a).2.2.1⟩
        · exact ⟨(P4828T1RightRootGeometry a).1,
            (P4828T1RightRootGeometry a).2.1,
            (P4828T1RightRootGeometry a).2.2.1⟩
    | append_singleton w b ih =>
        obtain ⟨proper, signed, _⟩ := ih
        have inherited := P4828T1ConstructorSupport (2 * (a.re : Real))
          (P4828T1Evaluate a side w) proper signed b
        have heval : P4828T1Evaluate a side (w ++ [b]) =
            P4828T1Step (P4828T1Rotate (P4828T1Evaluate a side w) b) := by
          simp [P4828T1Evaluate, List.foldl_append]
        rw [heval]
        refine ⟨inherited.1, inherited.2, ?_⟩
        by_cases positive : ∀ j : Fin 3,
            0 < (P4828T1Step (P4828T1Rotate
              (P4828T1Evaluate a side w) b) j.succ).1
        · exact P4828T1CircularPlacement _ _ inherited.1 positive
        · push Not at positive
          obtain ⟨j, hj⟩ := positive
          have hn := (ProperBandCurvatureStructure _ inherited.1).2.1 j
          exact P4828T1LinePlacement _ _ inherited.1 inherited.2 ⟨j, by omega⟩
  have h := state word
  have patches := P4828T1ResidualPatches (2 * (a.re : Real))
    (P4828T1Evaluate a side word) h.1 h.2.1 h.2.2
  refine ⟨h, ?_, ?_⟩
  · intro b
    simpa only [P4828T1Evaluate, List.foldl_append, List.foldl_cons,
      List.foldl_nil] using patches.1 b
  · intro b c hbc
    simpa only [P4828T1Evaluate, List.foldl_append, List.foldl_cons,
      List.foldl_nil] using patches.2.1 b c hbc

end ApollonianSuperharmonic

end
