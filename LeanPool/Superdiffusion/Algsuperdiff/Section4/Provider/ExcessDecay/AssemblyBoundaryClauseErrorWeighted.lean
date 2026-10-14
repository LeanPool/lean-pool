/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.AssemblyComposedErrorWeighted
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ReindexSlot

/-!
# AssemblyBoundaryClauseErrorWeighted

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The error-weighted boundary obligation, modulo the scalar

Nothing here imports the frozen file, and nothing here claims the anchor or any
source node.  It is `AssemblyBoundaryClause`'s script with the flat `∇h` leg
read in its `𝓔`-multiplied form on both sides; that proved module itself is
untouched.

## What is proved

`AssemblyComposedErrorWeighted`'s boundary display, re-cut onto the
error-weighted right-hand side
by the two proved moves — the `σ` gap-3 conversion `σ_{n+3}^{-1} ≤ 4
σ_n^{-1}` (`ReindexSlot`) and the nonnegative in-bracket `∇h`-average
companion, simply added.  **No window move is needed**: the boundary chain
already outputs on `W' = (z+□_{n+3}) ∩ □_m`, the anchor's window itself.

The fourth leg is the error-weighted one, `s^{-6}·𝓔·3^n·‖∇h‖_{L²(W')}`.

## References

* ABK26, `l.harmonic.approximation.good.scales`; the frozen block of
  `Algsuperdiff/Frozen/Section4/HarmonicApproximation.lean` (never imported).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

/-- **The error-weighted boundary obligation at the scalar `S`.**

Everything else is discharged from the proved chain: the boundary Caccioppoli,
the scaled parent-`L²` pricing, the composed datum pricing and the two
Dirichlet-energy legs at the coarse caps, the envelope, the `σ`-frame division
and the `σ` gap-3 conversion.  The frontier condition is never used, so the
display holds at every `z`; the gate binder is carried only to match the frozen
shape. -/
theorem hbdryOfScalarCoarse_errorWeighted (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s,
        ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m →
          ∀ x z : Vec d,
            x ∈ openCubeSet (originCube d m) →
            z ∈ openCubeSet (originCube d m) →
            (fun y => x + y) '' openCubeSet (originCube d n) ⊆
              ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
                openCubeSet (originCube d m) →
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
                  frontier (openCubeSet (originCube d m)) ≠ ∅)) →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                  (Support.cgEllipLowerConstant d) (n + 3) z
                  ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
                ∀ (u h : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                  Support.IsDirichletSolutionOn
                      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (originCube d m) u h g →
                  MemLp g 2 (Support.normalizedVolumeMeasureOn
                    (openCubeSet (originCube d m))) →
                  MemLp (Gagliardo.gagliardoKernel s 2 g) 2
                    (Support.normalizedGagliardoMeasureOn
                      (openCubeSet (originCube d m))) →
                  MemLp (Gagliardo.gagliardoKernel s 2 h.grad) 2
                    (Support.normalizedGagliardoMeasureOn
                      (openCubeSet (originCube d m))) →
                  ∀ S : ℝ,
                  |volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
                      openCubeSet (originCube d (n + 2)))
                      (fun y => u.toFun y - h.toFun y)| ≤ S →
                  ∀ (v : H1Function
                        ((fun y => x + y) '' openCubeSet (originCube d n)))
                    (w : H10Function
                        ((fun y => x + y) '' openCubeSet (originCube d n))),
                    Support.IsWeaklyHarmonicOn
                        ((fun y => x + y) '' openCubeSet (originCube d n)) v →
                    (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                    (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                      (eLpNorm (fun y => u.toFun y - v.toFun y) 2
                          (Support.normalizedVolumeMeasureOn
                            ((fun y => x + y) ''
                              openCubeSet (originCube d n)))).toReal ≤
                        C *
                          (Real.rpow s (-(4 : ℝ)) *
                                Support.fluxCorrectedErrorRepresentative M L (n + 3)
                                  ⟨s / 8, by linarith only [hs]⟩
                                  (Cutoff.translateCutoffSample z omega) *
                                ((eLpNorm
                                    (fun y =>
                                      u.toFun y -
                                        volumeAverage
                                          (((fun y' => z + y') ''
                                              openCubeSet (originCube d (n + 3))) ∩
                                            openCubeSet (originCube d m))
                                          u.toFun)
                                    2
                                    (Support.normalizedVolumeMeasureOn
                                      (((fun y' => z + y') ''
                                          openCubeSet (originCube d (n + 3))) ∩
                                        openCubeSet (originCube d m)))).toReal +
                                  Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
                                    ‖volumeAverageVec
                                        (((fun y' => z + y') ''
                                            openCubeSet (originCube d (n + 2))) ∩
                                          openCubeSet (originCube d m))
                                        h.grad‖) +
                            Real.rpow s (-(7 : ℝ)) * (Annealed.sigmaBar M n : ℝ)⁻¹ *
                                Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                                (Support.normalizedGagliardoESeminormOn
                                  (((fun y' => z + y') ''
                                      openCubeSet (originCube d (n + 3))) ∩
                                    openCubeSet (originCube d m)) s g).toReal +
                            Real.rpow s (-(6 : ℝ)) *
                                Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                                (Support.normalizedGagliardoESeminormOn
                                  (((fun y' => z + y') ''
                                      openCubeSet (originCube d (n + 3))) ∩
                                    openCubeSet (originCube d m)) s h.grad).toReal +
                            Real.rpow s (-(6 : ℝ)) *
                                Support.fluxCorrectedErrorRepresentative M L (n + 3)
                                  ⟨s / 8, by linarith only [hs]⟩
                                  (Cutoff.translateCutoffSample z omega) *
                                Real.rpow (3 : ℝ) (n : ℝ) *
                                (eLpNorm h.grad 2
                                  (Support.normalizedVolumeMeasureOn
                                    (((fun y' => z + y') ''
                                        openCubeSet (originCube d (n + 3))) ∩
                                      openCubeSet (originCube d m)))).toReal) +
                          C *
                            (Real.rpow s (-(4 : ℝ)) *
                              Support.fluxCorrectedErrorRepresentative M L (n + 3)
                                ⟨s / 8, by linarith only [hs]⟩
                                (Cutoff.translateCutoffSample z omega) * S) := by
  classical
  by_cases hd : d = 0
  · refine ⟨1, one_pos, ?_⟩
    intro M
    exact absurd M.shellPrefix.dimension (by omega)
  have : NeZero d := ⟨hd⟩
  obtain ⟨CC, Cfin, hCC, hCfin, hcomp⟩ := exists_boundaryClauseComposed_honest_errorWeighted d
  obtain ⟨CS, hCS, hS⟩ := exists_inv_sigmaBar_add_three_le d
  obtain ⟨C, hCpos, hleC, hleS, hle1, hle4⟩ :=
    exists_clause_absorption_constant (CS := CS) (K := 1) hCC hCfin.le zero_le_one
  simp only [mul_one, one_mul] at hle1 hle4
  refine ⟨C, hCpos, ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm x z hx _hz hgeom _hgate
  have hregimeC : M.gamma ≤ CC⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    hregime.trans (inverse_mul_le_of_constant_le hCC hleC (by positivity))
  have hregimeS : M.gamma ≤ CS⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    hregime.trans (inverse_mul_le_of_constant_le hCS hleS (by positivity))
  have hsigconv := hS M hregimeS n
  filter_upwards [hcomp M s hsrange hregimeC hsmall hs L m n hmL hnm x z hx hgeom]
    with omega hom
  intro hmem u hdat g hsol hgL2 hgW hhW S hmean v w hharm hval hgrad
  have hreal := hom hmem u hdat g S hsol hgL2 hgW hhW hmean v w hharm hval hgrad
  have hErep0 : (0 : ℝ) ≤ Support.fluxCorrectedErrorRepresentative M L (n + 3)
      ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) :=
    Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
  have hS0 : (0 : ℝ) ≤ S := le_trans (abs_nonneg _) hmean
  have hS4 : (0 : ℝ) ≤ Real.rpow s (-(4 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS7 : (0 : ℝ) ≤ Real.rpow s (-(7 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS6 : (0 : ℝ) ≤ Real.rpow s (-(6 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS32 : (0 : ℝ) ≤ Real.rpow s (-(3 / 2 : ℝ)) := Real.rpow_nonneg hs.le _
  have h3n : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (n : ℝ) := Real.rpow_nonneg (by norm_num) _
  have h3sn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hsgn : (0 : ℝ) ≤ ((Annealed.sigmaBar M n : ℝ))⁻¹ :=
    inv_nonneg.mpr (Annealed.sigmaBar M n).2.le
  have hcompanion : (0 : ℝ) ≤ Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
      ‖volumeAverageVec
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
          openCubeSet (originCube d m))) hdat.grad‖ :=
    mul_nonneg (mul_nonneg hS32 h3n) (norm_nonneg _)
  refine hreal.trans (boundary_absorb ?_ ?_ ?_ ?_ ?_ ?_ ?_ hCfin.le hle1 hle4)
  · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hcompanion)
      (mul_nonneg hS4 hErep0)
  · exact mul_nonneg (mul_nonneg hS4 hErep0)
      (add_nonneg ENNReal.toReal_nonneg hcompanion)
  · exact sigma_leg_move hS7 h3sn ENNReal.toReal_nonneg hsigconv
  · exact mul_nonneg (mul_nonneg (mul_nonneg hS7 hsgn) h3sn) ENNReal.toReal_nonneg
  · exact mul_nonneg (mul_nonneg hS6 h3sn) ENNReal.toReal_nonneg
  · exact mul_nonneg (mul_nonneg (mul_nonneg hS6 hErep0) h3n) ENNReal.toReal_nonneg
  · exact mul_nonneg (mul_nonneg hS4 hErep0) hS0


end

end Algsuperdiff.Section4.Provider.ExcessDecay
