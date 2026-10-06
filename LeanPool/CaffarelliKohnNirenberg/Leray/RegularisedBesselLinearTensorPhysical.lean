/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLinearTensorPath
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedTensorPhysicalCompatibility

/-!
# Physical realization of the linear complete Sobolev tensor path

The tensor formed from a prescribed L² coefficient and a complete
Sobolev path realizes the corresponding physical L² tensor.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The complete tensor path and the physical tensor agree at every time. -/
theorem regularisedBesselLinearTensorPath_physical
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (g : C(RegularizedMildTimeInterval T, ComplexVectorL2))
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (s : ℝ) :
    regularisedTensorBesselSobolevToL2 ((2 * k : ℕ) : ℝ) (by positivity)
      (regularisedBesselLinearTensorPath ρ ε hε k T hT g v s) =
    regularisedTensorPhysicalMap ρ ε hε
      (g (regularizedMildTimeClamp T hT s))
      (regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
        (by positivity) (v (regularizedMildTimeClamp T hT s))) := by
  exact regularisedBesselTensorMap_physical ρ ε hε k
    (g (regularizedMildTimeClamp T hT s))
    (v (regularizedMildTimeClamp T hT s))

end CKN.Leray

end
