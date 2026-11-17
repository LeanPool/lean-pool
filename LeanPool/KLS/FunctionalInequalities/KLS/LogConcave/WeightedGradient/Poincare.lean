/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.WeightedGradient.Energy
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Poincare
public import LeanPool.KLS.FunctionalInequalities.Poincare.SmoothGradient.Comparison

/-!
# Literature Poincare constants on the actual closed gradient

For a full-dimensional log-concave law, the squared-norm form of the closed unit gradient
is the smooth-gradient relaxation. Its finite Poincare constants are therefore precisely
the finite bounds on the intrinsic literature optimum. No heat estimate is assumed here.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.KLS.LogConcave

open Energy

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

/-- The optimal Poincare constant of the actual closed unit-gradient form is exactly the
intrinsic literature constant, including zero and infinity. -/
theorem closedWeightedOperator_id_constant_eq_literature :
    Poincare.L2Energy.optimalConstant ν
      (PreEnergy.normSqEnergy
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) =
      Poincare.LocalSlope.Intrinsic.optimalConstant ν := by
  rw [hν.closedWeightedOperator_id_energy_eq_smoothGradient m hi]
  exact (Poincare.SmoothGradient.Ambient.constant_eq_intrinsic ν).trans
    hν.intrinsicSmooth_constant_eq_localSlope

/-- A finite upper bound on the literature Poincare optimum is a form-domain gap
for the actual closed unit gradient. -/
theorem closedWeightedOperator_id_gap_of_literature_le (C : NNReal)
    (hC : Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤ (C : ENNReal))
    (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
      (C : ℝ) * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u‖ ^ 2 := by
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let Q := Energy.SmoothGradient.relaxation ν
  have hQ : PreEnergy.normSqEnergy T = Q :=
    hν.closedWeightedOperator_id_energy_eq_smoothGradient m hi
  have hmem : (u : Lp ℝ 2 (ν : Measure V)) ∈ Q.domain := by
    change Q (u : Lp ℝ 2 (ν : Measure V)) ≠ ⊤
    rw [← hQ, PreEnergy.normSqEnergy_of_mem T u]
    exact ENNReal.coe_ne_top
  have hbound : Poincare.SmoothGradient.Ambient.Holds ν C :=
    (Poincare.SmoothGradient.Ambient.holds_iff_constant_le ν C).2 (by
      rw [Poincare.SmoothGradient.Ambient.constant_eq_intrinsic,
        hν.intrinsicSmooth_constant_eq_localSlope]
      exact hC)
  have hform := (Poincare.L2Energy.holds_iff ν Q C).1 hbound ⟨u, hmem⟩
  have hvalue : Q.finiteValue ⟨u, hmem⟩ = ‖T u‖₊ ^ 2 := by
    apply ENNReal.coe_injective
    rw [Energy.Functional.coe_finiteValue]
    calc
      Q (u : Lp ℝ 2 (ν : Measure V)) = PreEnergy.normSqEnergy T u :=
        congrArg (fun F : Energy.Functional (Lp ℝ 2 (ν : Measure V)) => F u.1) hQ.symm
      _ = _ := PreEnergy.normSqEnergy_of_mem T u
  rw [hvalue] at hform
  exact_mod_cast hform

end FunctionalInequalities.KLS.LogConcave
