/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetry
public import LeanPool.ApollonianSuperharmonic.GaussianQuarterTurn
public import LeanPool.ApollonianSuperharmonic.GaussianReflection

-- [TABLET NODE: BandPackingSymmetryVectorAction]

/-!
# BandPackingSymmetryVectorAction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The induced action of a band-packing symmetry word on a canonical Gaussian
lattice vector is defined as follows.  The identity fixes $v$, coordinate
negation acts by the quarter-turn $v\mapsto iv$, coordinate conjugation acts
by $v\mapsto-\overline v$, and every shift fixes $v$.  For
$\operatorname{comp}(g,h)$, first apply the action of $h$ and then the action
of $g$.  These choices use the canonical primitive orientation of the band
vectors; they do not attach data to a constructor history for a circle.
-/
def BandPackingSymmetryVectorAction :
    BandPackingSymmetry → GaussianInt → GaussianInt :=
-- BODY
  fun g v => match g with
    | .identity => v
    | .negate => GaussianQuarterTurn v
    | .conjugate => -GaussianReflection v
    | .shift _ => v
    | .comp g h =>
        BandPackingSymmetryVectorAction g
          (BandPackingSymmetryVectorAction h v)

namespace BandPackingSymmetryVectorAction

/-- The canonical Gaussian vector action commutes with negation. -/
theorem negation (a : BandPackingSymmetry) (v : GaussianInt) :
    BandPackingSymmetryVectorAction a (-v) = -BandPackingSymmetryVectorAction a v := by
  induction a generalizing v with
  | identity => rfl
  | negate => rcases v with ⟨x, y⟩; rfl
  | conjugate => rcases v with ⟨x, y⟩; rfl
  | shift w => rfl
  | comp a b iha ihb =>
    change BandPackingSymmetryVectorAction a (BandPackingSymmetryVectorAction b (-v)) =
      -BandPackingSymmetryVectorAction a (BandPackingSymmetryVectorAction b v)
    rw [ihb, iha]

/-- The vector action preserves a lattice point together with its four neighbors. -/
theorem neighborStar :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (b = a ∨ b = a + 1
            ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) → (BandPackingSymmetryVectorAction g b
            = BandPackingSymmetryVectorAction g a ∨ BandPackingSymmetryVectorAction g b =
            BandPackingSymmetryVectorAction g a + 1 ∨ BandPackingSymmetryVectorAction g b =
            BandPackingSymmetryVectorAction g a - 1 ∨ BandPackingSymmetryVectorAction g b =
            BandPackingSymmetryVectorAction g a + ⟨0, 1⟩ ∨ BandPackingSymmetryVectorAction g b =
            BandPackingSymmetryVectorAction g a - ⟨0, 1⟩) ) := by
  classical
  intro g
  induction g with
  | identity => intro a b hb; simpa [BandPackingSymmetryVectorAction] using hb
  | shift w => intro a b hb; simpa [BandPackingSymmetryVectorAction] using hb
  | negate =>
      intro a b hb
      rcases hb with hb | hb | hb | hb | hb
      · subst b
        simp [BandPackingSymmetryVectorAction]
      · subst b
        right; right; right; left
        ext <;> simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn]
      · subst b
        right; right; right; right
        ext <;> simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn]
      · subst b
        right; right; left
        ext <;> simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn]; try ring
      · subst b
        right; left
        ext <;> simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn]; try ring
  | conjugate =>
      intro a b hb
      rcases hb with hb | hb | hb | hb | hb
      · subst b
        simp [BandPackingSymmetryVectorAction]
      · subst b
        right; right; left
        ext <;> simp [BandPackingSymmetryVectorAction, GaussianReflection]; try ring
      · subst b
        right; left
        ext <;> simp [BandPackingSymmetryVectorAction, GaussianReflection]; try ring
      · subst b
        right; right; right; left
        ext <;> simp [BandPackingSymmetryVectorAction, GaussianReflection]
      · subst b
        right; right; right; right
        ext <;> simp [BandPackingSymmetryVectorAction, GaussianReflection]
  | comp g₁ g₂ ih₁ ih₂ =>
      intro a b hb
      exact ih₁ _ _ (ih₂ _ _ hb)


end BandPackingSymmetryVectorAction

end ApollonianSuperharmonic

end
