/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselRealPath

/-!
# Norm of the real physical part of a complete Sobolev path

Taking the physical realization and real part is contractive on
continuous complete H²ᵏ trajectories.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The real physical part of a complete H²ᵏ path has no larger
continuous trajectory norm. -/
theorem regularisedBesselRealPartPath_norm_le
    (k : ℕ) (T : ℝ)
    (u : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)) :
    ‖regularisedBesselRealPartPath k T u‖ ≤ ‖u‖ := by
  apply ((regularisedBesselRealPartPath k T u).norm_le (norm_nonneg u)).2
  intro t
  calc
    ‖regularisedBesselRealPartPath k T u t‖ ≤
      ‖regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
        (by positivity) (u t)‖ := realPartVectorL2_norm_le _
    _ ≤ ‖u t‖ := regularisedBesselSobolevToL2_norm_le
      ((2 * k : ℕ) : ℝ) (by positivity) (u t)
    _ ≤ ‖u‖ := u.norm_coe_le_norm t

end CKN.Leray

end
