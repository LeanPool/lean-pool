/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationCZP1LocalGrowth
public import LeanPool.CaffarelliKohnNirenberg.Pressure.CZP1Closer
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SliceVelocityCube
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.ThetaDecayTShape

/-! The source-data input is supplied through
`pressureUTensor_source_data_ae_of_sws` from `SliceVelocityCube.lean`.  That
solution-level package combines the local velocity `L³` slice with the fixed-
time tensor-source estimate, returning all nine `L^{3/2}` components, compact
support, and the matching factor-27 source bound.  This is the normalization
already consumed by the singly centred pressure assembly. -/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Euclidean
open CKN.Core.Step3
noncomputable section

namespace CKN



/-- The exact singly centred pressure input required by Theorem A, from
suitability alone.  Its coefficient is fixed before the solution data. -/
theorem theoremA_hCZ_p1_of_sws (q : ℝ) :
    ∀ (Ω : Set Vec3) (I : Set ℝ)
        (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z : ParabolicPoint} {ρ r : ℝ}, (hρ : 0 < ρ) → 0 < r →
        r ≤ ρ / 2 →
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
        ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
          eLpNorm' (fun w : ParabolicPoint => pressureP1
            (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            p f w.2 w.1) (3 / 2 : ℝ)
            (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
          ENNReal.ofReal (czP1ThetaDecayConstant * (r / ρ)⁻¹ *
            alpha u z ρ * beta u Du z ρ) := by
  intro Ω I u Du p f hsol z ρ r hρ hr hhalf hsub
  have hbase : 0 ≤ max czP1OperatorConstant 0 := le_max_right _ _
  have hoperator : czP1OperatorConstant ≤ max czP1OperatorConstant 0 :=
    le_max_left _ _
  have hC_CZ : 0 ≤ 9 * max czP1OperatorConstant 0 :=
    mul_nonneg (by norm_num) hbase
  have hconst :
      (9 * max czP1OperatorConstant 0) *
        (9 * sobolevPoincareL6Constant.toReal) ≤
        czP1ThetaDecayConstant := by
    unfold czP1ThetaDecayConstant
    exact le_rfl
  have hslice := pressureP1_thetaDecay_hCZ_of_sws_growth
    (max czP1OperatorConstant 0) hbase hoperator hsol hρ hsub
  exact pressureP1_thetaDecay_hCZ_of_global_slice
    czP1ThetaDecayConstant (9 * max czP1OperatorConstant 0)
    hC_CZ hconst hsol hρ hr hhalf hsub hslice

end CKN
