/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.ClassicalGradient
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.ErrorAtoms
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Disorder.Cstar
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamProviderFinal

/-!
# GeneratorRenormalization

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

/-!
# Generator renormalization — [ABK] Theorem B (`t.homogenization`)

At every scale `m` the coarse-grained generator is a constant multiple
`sigmaBar` of the identity, quantitatively close to
`sqrt (nu^2 + cstar gamma^{-1} 3^{2 gamma m})`, and the disorder solution `u`
is compared with the homogenized solution `v` of the same Dirichlet problem:
a single random error amplitude with Gaussian-type moments controls both the
uniform difference `u - v` and the difference of the two Dirichlet energies.

Proved; reduces to the standard axioms.
-/

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section4.generator_renormalization
    (d : ℕ) (cstar : ℝ) (_hcstar : 0 < cstar) :
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
                ∀ (u v h : HCPolySupport.H1Function
                      (HCPolySupport.openCubeSet (HCPolySupport.originCube d m)))
                  (g : HCPolySupport.Vec d → HCPolySupport.Vec d)
                  (Kg Kh KhInf : ℝ),
                  Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (HCPolySupport.originCube d m) u h g →
                  Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                      (fun _ : HCPolySupport.Vec d => sigmaBarM • (1 : HCPolySupport.Mat d))
                      (HCPolySupport.originCube d m) v h g →
                  Algsuperdiff.Section4.Support.HolderSeminormBoundOn
                      (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                      (1 / 2) Kg g →
                  Algsuperdiff.Section4.Support.HolderSeminormBoundOn
                      (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                      (1 / 2) Kh h.grad →
                  (∀ x ∈ HCPolySupport.openCubeSet (HCPolySupport.originCube d m),
                    ‖h.grad x‖ ≤ KhInf) →
                  Algsuperdiff.Section4.Support.HasGradientOn
                      (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                      h.toFun h.grad →
                  (∀ᵐ x ∂(MeasureTheory.volume.restrict
                        (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))),
                      Real.rpow (3 : ℝ) (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
                        EB omega *
                          (sigmaBarM⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                            (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))) ∧
                    |HCPolySupport.volumeAverage
                          (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                          (fun y => M.nu * HCPolySupport.vecNormSq (u.grad y)) -
                        HCPolySupport.volumeAverage
                          (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                          (fun y => sigmaBarM * HCPolySupport.vecNormSq (v.grad y))| ≤
                      EB omega *
                        (Real.sqrt sigmaBarM⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                            Real.sqrt sigmaBarM *
                              (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) ^
                          (2 : ℕ)
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section4.Provider.Homogenization.generator_renormalization_provider_final
    d cstar _hcstar
