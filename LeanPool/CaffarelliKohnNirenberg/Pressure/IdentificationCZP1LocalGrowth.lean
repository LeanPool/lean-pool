/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.CZP1UnconditionalAssembly
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionGrowthSWS
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34CentredPairingSWS
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34CentredResidual

/-! The solution-level residual-growth estimate removes the explicit Liouville
input from the centred pressure certificate. -/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Euclidean
open CKN.Core.Step3
noncomputable section

namespace CKN



/-- The source-producing theta-decay assembly, with its residual-growth input
replaced by the suitable-solution producer. -/
theorem pressureP1_thetaDecay_hCZ_of_sws_growth
    (C_CZ : ℝ) (hC_CZ : 0 ≤ C_CZ)
    (hoperator : czP1OperatorConstant ≤ C_CZ)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp
          (fun x : Vec3 => pressureP1 (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            p f s x) (ENNReal.ofReal (3 / 2)) volume ∧
        lpNorm
          (fun x : Vec3 => pressureP1 (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            p f s x) (ENNReal.ofReal (3 / 2)) volume ≤
          (9 * C_CZ) *
            (∫ y in vec3Ball z.1 ρ,
              (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
  exact pressureP1_thetaDecay_hCZ_of_sws C_CZ hC_CZ hoperator hsol hρ hsub
    (pressureSecondExtension_residual_growth_ae_of_sws hsol hρ hsub)

end CKN
