/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreLocalDerivs
public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearCounterexample.FactorIBP
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport

/-!
# Vanishing integrals of compactly supported derivatives

Space-time boundary terms in `eq:carleman-commutator` of the Escauriaza–Seregin–Šverák manuscript
vanish for smooth
compactly supported scalar fields.
-/

public section

open MeasureTheory CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- The integral of a compactly supported smooth spatial derivative is zero. -/
theorem integral_spatialPartial_eq_zero
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (i : Fin 3) :
    (∫ z : Vec3 × ℝ, spatialPartial f i z ∂volume) = 0 := by
  have h := CKN.integral_mul_spatialPartial_eq_neg_spatialPartial_mul
    (F := fun _ => (1 : ℝ)) (G := f) contDiff_const hf hfc i
  simpa [spatialPartial] using h

/-- The integral of a compactly supported smooth time derivative is zero. -/
theorem integral_timePartial_eq_zero
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) :
    (∫ z : Vec3 × ℝ, timePartial f z ∂volume) = 0 := by
  have h := CKN.integral_mul_timePartial_eq_neg_timePartial_mul
    (F := fun _ => (1 : ℝ)) (G := f) contDiff_const hf hfc
  simpa [timePartial] using h

end CKN
