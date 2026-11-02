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
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootProviderFinal

/-!
# AnomalousRegularity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

/-!
# Anomalous regularity — [ABK] Theorem C (`t.regularity`)

For a disorder model of strength `gamma` small enough, and every Hölder
exponent `alpha` below `1 - C sqrt gamma`, there is an almost surely finite
minimal scale `X` with an exponential tail such that, above `X`, every
Dirichlet solution on a triadic cube with `C^{0,1/2}` force `g` and
`C^{1,1/2}` boundary datum `h` satisfies the `C^{0,alpha}` large-scale
excess decay `3^{(1-alpha)(m-n)}` between any two scales `n <= m`.

Proved; reduces to the standard axioms.
-/

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section4.anomalous_regularity
    (d : ℕ) (cstar : ℝ) (_hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - C * Real.sqrt M.gamma →
          ∀ m : ℤ, ∃ X : Cutoff.CutoffSample d → ℕ∞,
            Measurable X ∧
            (∀ N : ℕ,
                (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ X omega} ≤
                  ENNReal.ofReal
                    (C * Real.exp
                      (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C)) / (C * M.gamma)))) ∧
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ L : ℤ, m ≤ L →
                ∀ (u h : HCPolySupport.H1Function
                      (HCPolySupport.openCubeSet (HCPolySupport.originCube d m)))
                  (g : HCPolySupport.Vec d → HCPolySupport.Vec d)
                  (Kg Kh : ℝ),
                  Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (HCPolySupport.originCube d m) u h g →
                  Algsuperdiff.Section4.Support.HolderSeminormBoundOn
                      (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                      (1 / 2) Kg g →
                  Algsuperdiff.Section4.Support.HolderSeminormBoundOn
                      (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                      (1 / 2) Kh h.grad →
                  (∀ y ∈ HCPolySupport.openCubeSet (HCPolySupport.originCube d m),
                    ‖h.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) →
                  Algsuperdiff.Section4.Support.HasGradientOn
                      (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                      h.toFun h.grad →
                  ∀ x : HCPolySupport.Vec d,
                    x ∈ HCPolySupport.openCubeSet (HCPolySupport.originCube d m) →
                    ∀ n : ℤ, n ≤ m → X omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
                      (ENNReal.ofReal (Real.sqrt M.nu) *
                          MeasureTheory.eLpNorm
                            (fun y => Real.sqrt (HCPolySupport.vecNormSq (u.grad y))) 2
                            (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                              (((fun y => x + y) ''
                                  HCPolySupport.openCubeSet (HCPolySupport.originCube d n)) ∩
                                HCPolySupport.openCubeSet (HCPolySupport.originCube d m))) ≤
                        ENNReal.ofReal
                            (C *
                              Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
                          (ENNReal.ofReal (Real.sqrt M.nu) *
                              MeasureTheory.eLpNorm
                                (fun y =>
                                  Real.sqrt (HCPolySupport.vecNormSq (u.grad y))) 2
                                (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                  (HCPolySupport.openCubeSet
                                    (HCPolySupport.originCube d m))) +
                            ENNReal.ofReal
                              (Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg) +
                            ENNReal.ofReal
                              (Real.sqrt (Annealed.sigmaBar M m : ℝ) *
                                Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))) ∧
                      (x ∈ HCPolySupport.openCubeSet (HCPolySupport.originCube d (m - 1)) →
                        ENNReal.ofReal (Real.sqrt M.nu) *
                            MeasureTheory.eLpNorm
                              (fun y => Real.sqrt (HCPolySupport.vecNormSq (u.grad y))) 2
                              (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                (((fun y => x + y) ''
                                    HCPolySupport.openCubeSet
                                      (HCPolySupport.originCube d n)) ∩
                                  HCPolySupport.openCubeSet (HCPolySupport.originCube d m))) ≤
                          ENNReal.ofReal
                              (C *
                                Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
                            (ENNReal.ofReal (Real.sqrt M.nu) *
                                MeasureTheory.eLpNorm
                                  (fun y =>
                                    Real.sqrt (HCPolySupport.vecNormSq (u.grad y))) 2
                                  (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                    (HCPolySupport.openCubeSet
                                      (HCPolySupport.originCube d m))) +
                              ENNReal.ofReal
                                (Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                                    Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg)))
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section4.Provider.Regularity.anomalous_regularity_provider_final
    d cstar _hcstar
