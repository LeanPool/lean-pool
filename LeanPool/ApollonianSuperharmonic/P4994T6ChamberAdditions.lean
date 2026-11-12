/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Ring

public import LeanPool.ApollonianSuperharmonic.P4994T6Chamber

-- [TABLET NODE: P4994T6ChamberAdditions]

/-!
# P4994T6ChamberAdditions

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4994T6ChamberAdditions (n : Nat) (p r : Int × Int)
    (hp : P4994T6Chamber n p) (hr : P4994T6Chamber n r) :
    P4994T6Chamber n (p + r) ∧
      p.1 * (p + r).2 - p.2 * (p + r).1 = p.1 * r.2 - p.2 * r.1 ∧
      (p + r).1 * r.2 - (p + r).2 * r.1 = p.1 * r.2 - p.2 * r.1 := by
-- BODY
  refine ⟨?_, ?_, ?_⟩
  · unfold P4994T6Chamber at *
    rw [map_add]
    exact ⟨add_nonneg hp.1 hr.1, add_le_add hp.2 hr.2⟩
  · simp only [Prod.fst_add, Prod.snd_add]
    ring
  · simp only [Prod.fst_add, Prod.snd_add]
    ring

end ApollonianSuperharmonic

end
