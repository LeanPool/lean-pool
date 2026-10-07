/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselClampedTensorPath
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselTensorPhysicalRealification

/-!
# Physical realization of the complete tensor path

The complete Sobolev tensor path represents the real mild tensor path
whenever the Sobolev and real velocity paths represent the same field.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Under pointwise physical agreement of two velocity paths, their
clamped regularized tensors agree in physical L² at every real time. -/
theorem regularisedBesselClampedTensorPath_real_toLp
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (u : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (v : C(RegularizedMildTimeInterval T, RealVectorL2))
    (huv : ∀ t,
      regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
        (by positivity) (u t) = complexifyVectorL2 (v t))
    (s : ℝ) :
    regularisedTensorBesselSobolevToL2 ((2 * k : ℕ) : ℝ) (by positivity)
      (regularisedBesselClampedTensorPath ρ ε hε k T hT u s) =
    complexifyTensorL2
      (regularizedMildClampedTensorTrajectory ρ ε hε T hT v s) := by
  exact regularisedBesselTensorQuadratic_real_toLp ρ ε hε k
    (u (regularizedMildTimeClamp T hT s))
    (v (regularizedMildTimeClamp T hT s))
    (huv (regularizedMildTimeClamp T hT s))

end CKN.Leray

end
