/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLinearLocalMap
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLinearTensorPhysical
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselShiftedStokesIntegralPhysical
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselHeatRealization

/-!
# Physical equation of the linear complete Sobolev mild map

The H²ᵏ linear mild map realizes a complex L² Volterra equation
with the same prescribed physical coefficient path.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The complete Sobolev linear mild map represents the complex L²
heat evolution and translated Stokes integral of its physical path. -/
theorem regularisedBesselLinearLocalMap_physical
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (T : ℝ) (hT : 0 ≤ T)
    (g : C(RegularizedMildTimeInterval T, ComplexVectorL2))
    (B : ℝ) (hB : 0 ≤ B) (hg : ∀ q, ‖g q‖ ≤ B)
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (t : RegularizedMildTimeInterval T) :
    regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ) (by positivity)
      (regularisedBesselLinearLocalMap ρ ε hε k b T hT g B hB hg v t) =
    heatSemigroup t.1 t.2.1
      (regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
        (by positivity) b) -
      ∫ τ in (0 : ℝ)..T,
        if h : 0 < τ ∧ τ < t.1 then
          stokesL2Operator h.1
            (regularisedTensorPhysicalMap ρ ε hε
              (g (regularizedMildTimeClamp T hT (t.1 - τ)))
              (regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
                (by positivity)
                (v (regularizedMildTimeClamp T hT (t.1 - τ)))))
        else 0 := by
  let E := regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ) (by positivity)
  let F := regularisedBesselLinearTensorPath ρ ε hε k T hT g v
  have hFcont : Continuous F :=
    regularisedBesselLinearTensorPath_continuous ρ ε hε k T hT g v
  have hFbound : ∀ s, ‖F s‖ ≤
      regularisedBesselTensorConstant ρ ε hε k * B * ‖v‖ :=
    regularisedBesselLinearTensorPath_norm_le ρ ε hε k T hT g v B hB hg
  have hC : 0 ≤ regularisedBesselTensorConstant ρ ε hε k * B * ‖v‖ :=
    mul_nonneg
      (mul_nonneg (regularisedBesselTensorMap_norm_le ρ ε hε k).1 hB)
      (norm_nonneg v)
  rw [regularisedBesselLinearLocalMap_apply]
  change E (regularisedBesselHeat ((2 * k : ℕ) : ℝ) t.1 t.2.1 b -
    ∫ τ in (0 : ℝ)..T, regularisedBesselShiftedStokesIntegrand k F t.1 τ) = _
  rw [map_sub, regularisedBesselSobolevToL2CLM_apply,
    regularisedBesselHeat_realization,
    ← regularisedBesselSobolevToL2CLM_apply,
    regularisedBesselShiftedStokesIntegral_physical
      k F hFcont _ hFbound hC T t.1 hT]
  congr 1
  apply intervalIntegral.integral_congr
  intro τ _
  by_cases h : 0 < τ ∧ τ < t.1
  · simp only [dite_eq_left h]
    exact congrArg (stokesL2Operator h.1)
      (regularisedBesselLinearTensorPath_physical
        ρ ε hε k T hT g v (t.1 - τ))
  · simp only [dite_eq_right h]

end CKN.Leray

end
