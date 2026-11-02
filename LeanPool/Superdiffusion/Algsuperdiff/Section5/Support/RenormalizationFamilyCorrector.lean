/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section4.GeneratorRenormalization
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.CutoffLimitDatum
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.StoppedMomentsDatum
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.IntrinsicScale

/-!
# RenormalizationFamilyCorrector

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Renormalization families with the corrector clause

This module assembles the scale-indexed effective diffusivities and error variables supplied by
generator renormalization while retaining the corrector estimate for the same witnesses.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

/-- The renormalization families over the scales, with the corrector clause retained for the
same error family whose moments are controlled. -/
theorem exists_renormalizationFamily_corrector (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∃ (sigmaBar : ℤ → ℝ) (EB : ℤ → Cutoff.CutoffSample d → ℝ),
          (∀ m : ℤ, 0 < sigmaBar m) ∧
          (∀ m : ℤ, |sigmaBar m -
              effectiveDiffusivity M.nu cstar M.gamma ((3 : ℝ) ^ m)| ≤
            C * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBar m) ∧
          (∀ m : ℤ, ∀ omega, 0 ≤ EB m omega) ∧
          (∀ m : ℤ, Measurable (EB m)) ∧
          (∀ m : ℤ, ∀ p : ℝ, 1 ≤ p → p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
            (∫⁻ omega, ENNReal.ofReal (EB m omega) ^ p
                ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
              ENNReal.ofReal (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
                Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p) ∧
          ∀ m : ℤ, ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            ∀ L : ℤ, m ≤ L →
              ∀ (u v h : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d) (Kg Kh KhInf : ℝ),
                IsDirichletSolutionOn
                    (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                    (originCube d m) u h g →
                IsDirichletSolutionOn
                    (fun _ : Vec d => sigmaBar m • (1 : Mat d))
                    (originCube d m) v h g →
                HolderSeminormBoundOn (openCubeSet (originCube d m))
                    (1 / 2) Kg g →
                HolderSeminormBoundOn (openCubeSet (originCube d m))
                    (1 / 2) Kh h.grad →
                (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
                HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
                ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
                    Real.rpow 3 (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
                      EB m omega *
                        ((sigmaBar m)⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
                          (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) := by
  obtain ⟨gamma0, C, hgamma0, hC, hmain⟩ :=
    Algsuperdiff.Frozen.Section4.generator_renormalization d cstar hcstar
  refine ⟨gamma0, C, hgamma0, hC, fun M hcs hgamma => ?_⟩
  choose sigmaBar hsigpos hsigbound EB hEBnn hEBmeas hEBmom hdir using
    hmain M hcs hgamma
  refine ⟨sigmaBar, EB, hsigpos, ?_, hEBnn, hEBmeas, hEBmom, ?_⟩
  · intro m
    rw [effectiveDiffusivity_three_zpow]
    exact hsigbound m
  · exact fun m => (hdir m).mono fun omega homega L hL u v h g Kg Kh KhInf hu hv hg hh
      hhInf hhGrad => (homega L hL u v h g Kg Kh KhInf hu hv hg hh hhInf hhGrad).1

end

end Algsuperdiff.Section5.Support
