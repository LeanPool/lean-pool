/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.ShellWindowEnergyCentre
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ShellScalarPriced

/-!
# StepSevenFlushWindowEnergy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The flush-branch window energy, `S`-free.**

At every centre `z ∈ □_m` with the flush-direction overhang at the covering
scale `n+2`, almost surely on the good event at `(n+3, z)`, under the `ε`-pin,
the Step-7 window scalar `√ν‖∇u‖_{(z+□_n)∩□_m}` is priced on the window's own
legs — the oscillation leg, the datum legs and the forcing legs — with NO
normalization scalar.  unit 5 composed with's priced scalar. -/
theorem ae_windowEnergy_flush_S_killed (d : ℕ) [NeZero d] :
    ∃ C A K1 K2 : ℝ, 0 < C ∧ 0 < A ∧ 0 < K1 ∧ 0 ≤ K2 ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m → ∀ z : Vec d,
          z ∈ openCubeSet (originCube d m) →
          ∀ (i : Fin d) (sigma : ℝ), (sigma = 1 ∨ sigma = -1) →
            wellPlacedHalfGap m (n + 2) < sigma * z i →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                  (Support.cgEllipLowerConstant d) (n + 3) z
                  ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
                A * Support.fluxCorrectedErrorRepresentative M L (n + 3)
                    ⟨s / 8, by linarith only [hs]⟩
                    (Cutoff.translateCutoffSample z omega) ≤ s ^ (4 : ℕ) →
                ∀ (u hdat : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                  Support.IsDirichletSolutionOn
                      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (originCube d m) u hdat g →
                  MemLp g 2 (Support.normalizedVolumeMeasureOn
                    (openCubeSet (originCube d m))) →
                  MemLp (Gagliardo.gagliardoKernel s 2 g) 2
                    (Support.normalizedGagliardoMeasureOn
                      (openCubeSet (originCube d m))) →
                  MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
                    (Support.normalizedGagliardoMeasureOn
                      (openCubeSet (originCube d m))) →
                    Real.sqrt (M.nu *
                        normalizedSetAverage (truncatedWindow z m n)
                          (fun y => vecNormSq (u.grad y))) ≤
                      K1 * (Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ)) *
                              Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
                              (eLpNorm (fun y => u.toFun y -
                                  volumeAverage ((((fun y' => z + y') ''
                                      openCubeSet (originCube d (n + 3))) ∩
                                    openCubeSet (originCube d m))) u.toFun) 2
                                (Support.normalizedVolumeMeasureOn
                                  ((((fun y' => z + y') ''
                                      openCubeSet (originCube d (n + 3))) ∩
                                    openCubeSet (originCube d m))))).toReal +
                            Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ)) *
                                Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
                              (K2 *
                                ((eLpNorm (fun y => u.toFun y -
                                      volumeAverage ((((fun y' => z + y') ''
                                          openCubeSet (originCube d (n + 3))) ∩
                                        openCubeSet (originCube d m))) u.toFun) 2
                                    (Support.normalizedVolumeMeasureOn
                                      ((((fun y' => z + y') ''
                                          openCubeSet (originCube d (n + 3))) ∩
                                        openCubeSet
                                          (originCube d m))))).toReal +
                                  (3 : ℝ) ^ n *
                                    ∑ i' : Fin d,
                                      (eLpNorm (fun y => hdat.grad y i') 2
                                        (Support.normalizedVolumeMeasureOn
                                          ((((fun y' => z + y') ''
                                              openCubeSet
                                                (originCube d (n + 3))) ∩
                                            openCubeSet
                                              (originCube d m))))).toReal +
                                  Real.rpow s (-(6 : ℝ)) *
                                      Real.rpow (3 : ℝ) (n : ℝ) *
                                    (eLpNorm hdat.grad 2
                                      (Support.normalizedVolumeMeasureOn
                                        ((((fun y' => z + y') ''
                                            openCubeSet (originCube d (n + 3))) ∩
                                          openCubeSet
                                            (originCube d m))))).toReal +
                                  Real.rpow s (-(6 : ℝ)) *
                                      Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                                    (Support.normalizedGagliardoESeminormOn
                                      ((((fun y' => z + y') ''
                                          openCubeSet (originCube d (n + 3))) ∩
                                        openCubeSet (originCube d m))) s
                                      hdat.grad).toReal +
                                  Real.rpow s (-(7 : ℝ)) *
                                      ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ *
                                      Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                                    (Support.normalizedGagliardoESeminormOn
                                      ((((fun y' => z + y') ''
                                          openCubeSet (originCube d (n + 3))) ∩
                                        openCubeSet (originCube d m))) s
                                      g).toReal)) +
                            Real.rpow s (-(3 : ℝ)) *
                                Real.sqrt (((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹) *
                                Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ)) *
                              (Support.normalizedGagliardoESeminormOn
                                ((((fun y' => z + y') ''
                                    openCubeSet (originCube d (n + 3))) ∩
                                  openCubeSet (originCube d m))) s g).toReal +
                            Real.rpow s (-(2 : ℝ)) *
                                Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ)) *
                                Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ)) *
                              (Support.normalizedGagliardoESeminormOn
                                ((((fun y' => z + y') ''
                                    openCubeSet (originCube d (n + 3))) ∩
                                  openCubeSet (originCube d m))) s
                                hdat.grad).toReal +
                            Real.rpow s (-(2 : ℝ)) *
                                Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ)) *
                              (eLpNorm hdat.grad 2
                                (Support.normalizedVolumeMeasureOn
                                  ((((fun y' => z + y') ''
                                      openCubeSet (originCube d (n + 3))) ∩
                                    openCubeSet (originCube d m))))).toReal) := by
  obtain ⟨Cwe, K1, hCwe, hK1, hwe⟩ := ae_windowEnergy_boundary_le_anchorLegs_atCentre d
  obtain ⟨Csc, A, K2, hCsc, hA, hK2, hsc⟩ :=
    exists_boundaryScalar_le_displayLegs_of_epsPin d
  refine ⟨max Cwe Csc, A, K1, K2, lt_of_lt_of_le hCwe (le_max_left _ _), hA, hK1,
    hK2, ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm z hz i sigma hsigma hover
  have hcs10 : (0 : ℝ) ≤ Disorder.cstar M ^ (10 : ℕ) :=
    pow_nonneg ((Disorder.cstar_characterization M).1).le 10
  have hregWe : M.gamma ≤ Cwe⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    le_trans hregime (mul_le_mul_of_nonneg_right
      (inv_anti₀ hCwe (le_max_left _ _)) hcs10)
  have hregSc : M.gamma ≤ Csc⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    le_trans hregime (mul_le_mul_of_nonneg_right
      (inv_anti₀ hCsc (le_max_right _ _)) hcs10)
  filter_upwards [hwe M s hsrange hregWe hsmall hs L m n hmL hnm z hz,
    hsc M s hsrange hregSc hsmall hs L m n hmL hnm z hz i sigma hsigma hover]
    with omega hWE hSC
  intro hmem hpin u hdat g hdir hgL2 hgW hhW
  exact hWE hmem u hdat g _ hdir hgL2 hgW hhW (hSC hmem hpin u hdat g hdir hgL2 hgW hhW)

end

end Algsuperdiff.Section4.Provider.Regularity
