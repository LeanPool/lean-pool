/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3934T1LocalSide
public import Mathlib.Init


/-!
# LocalSideScaling

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace LocalSideScaling

/-- Shared positiveScale identity for LocalSideScaling. -/
theorem positiveScale :
    (by
      classical
      exact
        ∀ (W : Set (ℝ × ℝ)), ∀ (z : ℝ × ℝ), ∀ (w : ℝ × ℝ), ∀ (c : ℝ), ∀ (e : Bool), (0 : ℝ) < c →
            P3934T1LocalSide W z w e → P3934T1LocalSide W z (c • w) e ) := by
  classical
  intro W z w c e hc hside
  obtain ⟨r, hr, heq⟩ := hside
  refine ⟨r, hr, ?_⟩
  have hdet (q : Real × Real) :
      (c • w).1 * (q.2 - z.2) - (c • w).2 * (q.1 - z.1) =
        c * (w.1 * (q.2 - z.2) - w.2 * (q.1 - z.1)) := by
    simp only [Prod.smul_fst, Prod.smul_snd]
    ring
  ext q
  rw [heq]
  simp only [Set.mem_ofPred_eq]
  rw [hdet q]
  constructor
  · rintro ⟨hq, hs⟩
    refine ⟨hq, ?_⟩
    cases e <;> simp at hs ⊢ <;>
      nlinarith [hc]
  · rintro ⟨hq, hs⟩
    refine ⟨hq, ?_⟩
    cases e <;> simp at hs ⊢ <;>
      nlinarith [hc]

end LocalSideScaling
end ApollonianSuperharmonic

end
