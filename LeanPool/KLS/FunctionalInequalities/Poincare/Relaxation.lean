/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Relaxation.Recovery
public import LeanPool.KLS.FunctionalInequalities.Poincare.L2.Energy

/-!
# Poincaré constants before and after relaxation

These two proved comparisons belong to `lem:legacy-relaxed-poincare-comparison`. The definition
assigns to each concrete test the variance of its `L²` realization and its original finite energy.

The equivalence uses continuity of `L²` variance and the definition of sequential
relaxation. It does not need density, quadraticity, a Markov property, or agreement of raw and
relaxed energy. In particular it includes an empty test type and an infinite optimal constant.

Source: local abstract formulation of Blueprint `thm:legacy-relaxed-holds-equivalence`.
The Euclidean specialization is in `Poincare.SmoothTest.Comparison`; these statements
are not claimed as a separate theorem in the cited KLS literature.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace FunctionalInequalities.Poincare.TestFamily

universe u

variable {α : Type u} [MeasurableSpace α] (μ : ProbabilityMeasure α)
  (P : Energy.PreEnergy (Lp ℝ 2 (μ : Measure α)))

/-- Concrete tests with the variance of their `L²` realizations and their raw finite energy. -/
def ofPreEnergy : TestFamily where
  Test := P.Test
  variance f := L2.variance μ (P.toAmbient f)
  energy := P.energy

/-- A finite constant works on concrete tests exactly when it works on the finite domain
of their sequential relaxation. Source: the local abstract Blueprint bridge described above. -/
theorem holds_ofPreEnergy_iff (C : NNReal) :
    (ofPreEnergy μ P).Holds C ↔ L2Energy.Holds μ P.sequentialRelaxation C := by
  constructor
  · intro h f
    obtain ⟨s, hs⟩ := P.hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt f.2
    have henergy : Tendsto (fun n ↦ P.energy (s.1 n)) atTop
        (𝓝 (P.sequentialRelaxation.finiteValue f)) := by
      simpa only [Function.comp_def, ENNReal.toNNReal_coe, Energy.Functional.finiteValue]
        using (ENNReal.tendsto_toNNReal f.2).comp hs
    exact le_of_tendsto_of_tendsto
      ((L2.continuous_variance μ).tendsto f.1 |>.comp s.2)
      (tendsto_const_nhds.mul henergy) (Eventually.of_forall fun n ↦ h (s.1 n))
  · intro h f
    let x : P.sequentialRelaxation.domain :=
      ⟨P.toAmbient f, P.sequentialRelaxation_finiteAt_toAmbient f⟩
    have henergy : P.sequentialRelaxation.finiteValue x ≤ P.energy f := by
      apply ENNReal.coe_le_coe.mp
      simpa only [Energy.Functional.coe_finiteValue] using
        P.sequentialRelaxation_toAmbient_le f
    exact (h x).trans (mul_le_mul le_rfl henergy zero_le zero_le)

/-- Relaxation preserves the extended optimum, even if no finite constant works.
Source: the fixed-constant equivalence above and the existing optimizer order law. -/
theorem constant_ofPreEnergy_eq :
    (ofPreEnergy μ P).optimalConstant = L2Energy.optimalConstant μ P.sequentialRelaxation := by
  apply ENNReal.eq_of_forall_le_nnreal_iff
  intro C
  rw [← holds_iff_constant_le, ← L2Energy.holds_iff_constant_le, holds_ofPreEnergy_iff]

end FunctionalInequalities.Poincare.TestFamily
