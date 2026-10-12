/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.CutoffProjection

/-!
# Fixed high-field representatives

The high field uses the same chosen L² representative at every cutoff.

Joint strong measurability holds for this fixed representative.
-/

public section

open MeasureTheory
open scoped FourierTransform

namespace LiebThirring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The high field uses the same chosen L² representative at every cutoff. -/
@[expose] noncomputable def highFourierField
    (h : Lp H 2 (volume : Measure Position)) (E : ℝ) (x : Position) : H :=
  h x - lowFourierField h E x

/-- Joint strong measurability holds for this fixed representative. -/
theorem stronglyMeasurable_highFourierField_canonical
    (h : Lp H 2 (volume : Measure Position)) :
    StronglyMeasurable (fun p : ℝ × Position => highFourierField h p.1 p.2) :=
  stronglyMeasurable_highFourierField h h (Lp.stronglyMeasurable h)

/-- Each nonnegative cutoff's high field represents its exact inverse L² class. -/
theorem highFourierField_ae (h : Lp H 2 (volume : Measure Position))
    (E : ℝ) (hE : 0 ≤ E) :
    ((𝓕⁻ (highFrequencyClass h E) : Lp H 2 volume) : Position → H) =ᵐ[volume]
      highFourierField h E :=
  highFourierProjection_ae h E hE h (Filter.EventuallyEq.rfl)

end LiebThirring
end
