/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLocalMap
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedHeatStokesRealification

/-!
# Real physical paths in the complete Sobolev trajectory space

The physical real-part path is continuous, and paths whose physical
realization equals that complexification form a closed subset.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The real physical part of a complete H²ᵏ velocity trajectory. -/
@[expose]
def regularisedBesselRealPartPath
    (k : ℕ) (T : ℝ)
    (u : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)) :
    C(RegularizedMildTimeInterval T, RealVectorL2) :=
  ⟨fun t => realPartVectorL2
      (regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
        (by positivity) (u t)),
    realPartVectorL2.continuous.comp
      ((regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
        (by positivity)).continuous.comp u.continuous)⟩

/-- The complete H²ᵏ trajectories representing real physical L² paths
form a closed subset of the continuous trajectory Banach space. -/
theorem regularisedBesselRealPath_isClosed
    (k : ℕ) (T : ℝ) :
    IsClosed {u : C(RegularizedMildTimeInterval T,
        BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) |
      ∀ t, regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
          (by positivity) (u t) =
        complexifyVectorL2 (regularisedBesselRealPartPath k T u t)} := by
  let E := regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ) (by positivity)
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro t
  change IsClosed {u : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) |
      E (u t) = complexifyVectorL2 (realPartVectorL2 (E (u t)))}
  have hEval : Continuous (fun u : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) =>
      E (u t)) := E.continuous.comp (continuous_eval_const t)
  exact isClosed_eq hEval
    (complexifyVectorL2.continuous.comp
      (realPartVectorL2.continuous.comp hEval))

end CKN.Leray

end
