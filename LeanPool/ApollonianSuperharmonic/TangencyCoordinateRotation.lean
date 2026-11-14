/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateNormLaw
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinatePolarizationLaw


-- [TABLET NODE: TangencyCoordinateRotation]

/-!
# TangencyCoordinateRotation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/-- The norm law is preserved by injective relabelling of the quadruple. -/
theorem TangencyCoordinateNormLaw.reindex {q : Fin 4 → CircleCoordinates}
    (h : TangencyCoordinateNormLaw q) {f : Fin 4 → Fin 4} (hf : Function.Injective f) :
    TangencyCoordinateNormLaw (q ∘ f) := by
  intro a b hab
  exact h (f a) (f b) (fun heq => hab (hf heq))

/-- The polarization law is preserved by injective relabelling of the quadruple. -/
theorem TangencyCoordinatePolarizationLaw.reindex {q : Fin 4 → CircleCoordinates}
    (h : TangencyCoordinatePolarizationLaw q) {f : Fin 4 → Fin 4}
    (hf : Function.Injective f) : TangencyCoordinatePolarizationLaw (q ∘ f) := by
  intro a b j hab haj hbj
  exact h (f a) (f b) (f j) (fun heq => hab (hf heq))
    (fun heq => haj (hf heq)) (fun heq => hbj (hf heq))

theorem TangencyCoordinateRotation (q : Fin 4 → CircleCoordinates)
    (hn : TangencyCoordinateNormLaw q)
    (hp : TangencyCoordinatePolarizationLaw q) :
    TangencyCoordinateNormLaw ![q 0, q 2, q 3, q 1] ∧
      TangencyCoordinatePolarizationLaw ![q 0, q 2, q 3, q 1] := by
  let rotation : Equiv.Perm (Fin 4) := (Equiv.swap 1 2).trans (Equiv.swap 1 3)
  have rotated : ![q 0, q 2, q 3, q 1] = q ∘ rotation := by
    funext i
    fin_cases i <;> rfl
  rw [rotated]
  exact ⟨hn.reindex rotation.injective, hp.reindex rotation.injective⟩

end ApollonianSuperharmonic

end
