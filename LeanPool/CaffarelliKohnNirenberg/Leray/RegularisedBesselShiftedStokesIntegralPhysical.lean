/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselShiftedStokesPhysical
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselShiftedStokesIntegrability

/-!
# Physical realization of the shifted complete Stokes integral

The complete Sobolev Stokes integral represents the corresponding
complex spatial L² integral.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The physical realization commutes with a shifted complete Sobolev
Stokes integral over a bounded interval. -/
theorem regularisedBesselShiftedStokesIntegral_physical
    (k : ℕ)
    (F : ℝ → BesselPotentialSpace L2Vec3 ComplexTensor3 ((2 * k : ℕ) : ℝ) 2)
    (hF : Continuous F) (C : ℝ) (hFC : ∀ s, ‖F s‖ ≤ C)
    (hC : 0 ≤ C) (T t : ℝ) (hT : 0 ≤ T) :
    regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ) (by positivity)
      (∫ τ in (0 : ℝ)..T,
        regularisedBesselShiftedStokesIntegrand k F t τ) =
      ∫ τ in (0 : ℝ)..T,
        if h : 0 < τ ∧ τ < t then
          stokesL2Operator h.1
            (regularisedTensorBesselSobolevToL2 ((2 * k : ℕ) : ℝ)
              (by positivity) (F (t - τ)))
        else 0 := by
  let E := regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ) (by positivity)
  have hInt : IntervalIntegrable
      (regularisedBesselShiftedStokesIntegrand k F t) volume 0 T :=
    regularisedBesselShiftedStokesIntegrand_intervalIntegrable
      k F hF C hFC hC T t hT
  change E (∫ τ in (0 : ℝ)..T,
      regularisedBesselShiftedStokesIntegrand k F t τ) = _
  calc
    E (∫ τ in (0 : ℝ)..T,
        regularisedBesselShiftedStokesIntegrand k F t τ) =
      ∫ τ in (0 : ℝ)..T,
        E (regularisedBesselShiftedStokesIntegrand k F t τ) :=
          (E.intervalIntegral_comp_comm hInt).symm
    _ = _ := by
      congr 1
      funext τ
      exact regularisedBesselShiftedStokesIntegrand_physical k F t τ

end CKN.Leray

end
