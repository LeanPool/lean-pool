/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamSupClauseProvider

/-!
# HomSeamComposition

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The generator-renormalization conclusion

`GeneratorRenormalizationShape d cstar` names the frozen conclusion: the
effective coefficient approximation, moments of the random error envelope,
and the almost-everywhere comparison estimates for Dirichlet solutions.

This module defines that conclusion. The composition with a model-dependent
clause constant is proved in `HomSeamCompositionCcg`, and
the theorem `generator_renormalization_provider_final` in
`HomSeamProviderFinal` constructs the shape for every dimension and positive
`cstar` from the model assumptions.
The clause and energy supply interfaces used by that route are recorded in
`HomSeamSupClauseCcgFree`; the downstream seam data carry the clause constant
as an explicit parameter or existential witness.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

/-! ## 1. The frozen conclusion, named -/

/-- **THE FROZEN `generator_renormalization` CONCLUSION.**

Byte-transcribed from the `FROZEN-STATEMENT` block of
`Algsuperdiff/Frozen/Section4/GeneratorRenormalization.lean` (which is NOT
imported), modulo this file's `open`s. -/
def GeneratorRenormalizationShape (d : ℕ) (cstar : ℝ) : Prop :=
  ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
    ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ m : ℤ, ∃ sigmaBarM : ℝ, 0 < sigmaBarM ∧
        |sigmaBarM -
            Real.sqrt (M.nu ^ (2 : ℕ) +
              cstar * M.gamma⁻¹ * Real.rpow (3 : ℝ) (2 * M.gamma * (m : ℝ)))| ≤
          C * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM ∧
        ∃ EB : Cutoff.CutoffSample d → ℝ,
          (∀ omega, 0 ≤ EB omega) ∧ Measurable EB ∧
          (∀ p : ℝ, 1 ≤ p → p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
            (∫⁻ omega, ENNReal.ofReal (EB omega) ^ p
                ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
              ENNReal.ofReal
                  (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
                    Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p) ∧
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            ∀ L : ℤ, m ≤ L →
              ∀ (u v h : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d) (Kg Kh KhInf : ℝ),
                IsDirichletSolutionOn
                    (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                    (originCube d m) u h g →
                IsDirichletSolutionOn
                    (fun _ => sigmaBarM • (1 : Mat d)) (originCube d m) v h g →
                HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
                HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
                (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
                HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
                (∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
                    Real.rpow (3 : ℝ) (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
                      EB omega *
                        (sigmaBarM⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                          (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))) ∧
                  |volumeAverage (openCubeSet (originCube d m))
                        (fun y => M.nu * vecNormSq (u.grad y)) -
                      volumeAverage (openCubeSet (originCube d m))
                        (fun y => sigmaBarM * vecNormSq (v.grad y))| ≤
                    EB omega *
                      (Real.sqrt sigmaBarM⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                          Real.sqrt sigmaBarM *
                            (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) ^
                        (2 : ℕ)

end

end Algsuperdiff.Section4.Provider.Homogenization
