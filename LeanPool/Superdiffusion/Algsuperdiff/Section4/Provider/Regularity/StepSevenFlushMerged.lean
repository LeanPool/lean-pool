/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenFlushWindowEnergy
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.ShellEpsPinFloor
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenAeMerge
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.Api

/-!
# StepSevenFlushMerged

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# countable index data

Nothing here imports any of them, nothing here claims an anchor, and nothing
here is a frozen statement.

## The quantifier move

The boundary assembly chooses its scales A the sample (the pigeonhole selection
depends on the bad set), at a lattice centre depending on the root's own `x`,
and its flush direction after the geometry — so one null set must serve every
index at once.  As's merge, the index data are countable (`ℤ`-scales, printed
lattice centres, `Fin d` directions, a sign bit), and `Mathlib`'s `ae_all_iff`
does the whole job.

## References

* Mathlib, `MeasureTheory.ae_all_iff`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The good-event bridge -/

theorem mem_goodEventAtHalf_of_stepThree {M : ABKModel d} {delta : ℝ} {j : ℤ}
    {z : Vec d} {omega : Cutoff.CutoffSample d}
    (hdelta : delta ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hmem : omega ∈ stepThreeGoodEvent M delta j z) :
    omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
      (Support.cgEllipLowerConstant d) j z
      ⟨stepOneS / 8, by have := stepOneS_pos; linarith only [this]⟩ (1 / 2) := by
  have hsub : (⟨stepOneSEighth, stepOneSEighth_pos⟩ : {s : ℝ // 0 < s}) =
      (⟨stepOneS / 8, by have := stepOneS_pos; linarith only [this]⟩ : {s : ℝ // 0 < s}) := by
    refine Subtype.ext ?_
    change stepOneSEighth = stepOneS / 8
    rw [stepOneSEighth_eq, stepOneS]
    norm_num
  have hep := stepOneEp_mem_Ioc hdelta
  have hstep : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
      (Support.cgEllipLowerConstant d) j z
      ⟨stepOneSEighth, stepOneSEighth_pos⟩ (1 / 2) :=
    GoodEvents.goodEventAt_mono_ep M (Support.cgEllipLowerConstant d) j z
      ⟨stepOneSEighth, stepOneSEighth_pos⟩ hep.1.le hep.2 hmem
  rwa [hsub] at hstep

/-! ## 2. The flush conclusion record -/

/-- The uniform solution estimate assembled in the seventh regularity step. -/
def StepSevenFlushBound (M : ABKModel d) (K1 K2 : ℝ) (L m n : ℤ) (z : Vec d)
    (omega : Cutoff.CutoffSample d) : Prop :=
  ∀ (u hdat : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
    Support.IsDirichletSolutionOn
        (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
        (originCube d m) u hdat g →
    MemLp g 2 (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
    MemLp (Gagliardo.gagliardoKernel stepOneS 2 g) 2
      (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
    MemLp (Gagliardo.gagliardoKernel stepOneS 2 hdat.grad) 2
      (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
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
                          openCubeSet (originCube d m))))).toReal +
                    (3 : ℝ) ^ n *
                      ∑ i' : Fin d,
                        (eLpNorm (fun y => hdat.grad y i') 2
                          (Support.normalizedVolumeMeasureOn
                            ((((fun y' => z + y') ''
                                openCubeSet (originCube d (n + 3))) ∩
                              openCubeSet (originCube d m))))).toReal +
                    Real.rpow stepOneS (-(6 : ℝ)) *
                        Real.rpow (3 : ℝ) (n : ℝ) *
                      (eLpNorm hdat.grad 2
                        (Support.normalizedVolumeMeasureOn
                          ((((fun y' => z + y') ''
                              openCubeSet (originCube d (n + 3))) ∩
                            openCubeSet (originCube d m))))).toReal +
                    Real.rpow stepOneS (-(6 : ℝ)) *
                        Real.rpow (3 : ℝ) ((1 + stepOneS) * (n : ℝ)) *
                      (Support.normalizedGagliardoESeminormOn
                        ((((fun y' => z + y') ''
                            openCubeSet (originCube d (n + 3))) ∩
                          openCubeSet (originCube d m))) stepOneS
                        hdat.grad).toReal +
                    Real.rpow stepOneS (-(7 : ℝ)) *
                        ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ *
                        Real.rpow (3 : ℝ) ((1 + stepOneS) * (n : ℝ)) *
                      (Support.normalizedGagliardoESeminormOn
                        ((((fun y' => z + y') ''
                            openCubeSet (originCube d (n + 3))) ∩
                          openCubeSet (originCube d m))) stepOneS g).toReal)) +
              Real.rpow stepOneS (-(3 : ℝ)) *
                  Real.sqrt (((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹) *
                  Real.rpow (3 : ℝ) (stepOneS * (((n + 2 : ℤ)) : ℝ)) *
                (Support.normalizedGagliardoESeminormOn
                  ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                    openCubeSet (originCube d m))) stepOneS g).toReal +
              Real.rpow stepOneS (-(2 : ℝ)) *
                  Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ)) *
                  Real.rpow (3 : ℝ) (stepOneS * (((n + 2 : ℤ)) : ℝ)) *
                (Support.normalizedGagliardoESeminormOn
                  ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                    openCubeSet (originCube d m))) stepOneS hdat.grad).toReal +
              Real.rpow stepOneS (-(2 : ℝ)) *
                  Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ)) *
                (eLpNorm hdat.grad 2
                  (Support.normalizedVolumeMeasureOn
                    ((((fun y' => z + y') ''
                        openCubeSet (originCube d (n + 3))) ∩
                      openCubeSet (originCube d m))))).toReal)

/-! ## 3. The flush window energy, merged -/

theorem ae_stepSevenFlushBound_merged (d : ℕ) [NeZero d] :
    ∃ C A K1 K2 : ℝ, 0 < C ∧ 0 < A ∧ 0 < K1 ∧ 0 ≤ K2 ∧
      ∀ M : ABKModel d, stepOneS ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (stepOneS / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
              (1 / 2) →
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            ∀ (L m n nl : ℤ) (v : Fin d → ℤ) (i : Fin d) (sigma : ℝ),
              (sigma = 1 ∨ sigma = -1) → m ≤ L → n + 3 ≤ m →
              Support.triadicLatticePoint nl v ∈ openCubeSet (originCube d m) →
              wellPlacedHalfGap m (n + 2) <
                sigma * Support.triadicLatticePoint nl v i →
              omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                  (Support.cgEllipLowerConstant d) (n + 3)
                  (Support.triadicLatticePoint nl v)
                  ⟨stepOneS / 8, by have := stepOneS_pos; linarith only [this]⟩ (1 / 2) →
                A * Support.fluxCorrectedErrorRepresentative M L (n + 3)
                    ⟨stepOneS / 8, by have := stepOneS_pos; linarith only [this]⟩
                    (Cutoff.translateCutoffSample
                      (Support.triadicLatticePoint nl v) omega) ≤
                  stepOneS ^ (4 : ℕ) →
                StepSevenFlushBound M K1 K2 L m n
                  (Support.triadicLatticePoint nl v) omega := by
  obtain ⟨C, A, K1, K2, hC, hA, hK1, hK2, hmain⟩ := ae_windowEnergy_flush_S_killed d
  refine ⟨C, A, K1, K2, hC, hA, hK1, hK2, ?_⟩
  intro M hsrange hregime hsmall
  have hpair : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ p : ℤ × ℤ × ℤ × ℤ × (Fin d → ℤ) × (Fin d) × Bool,
        (p.2.1 ≤ p.1 ∧ p.2.2.1 + 3 ≤ p.2.1 ∧
          Support.triadicLatticePoint p.2.2.2.1 p.2.2.2.2.1 ∈
            openCubeSet (originCube d p.2.1) ∧
          wellPlacedHalfGap p.2.1 (p.2.2.1 + 2) <
            (if p.2.2.2.2.2.2 then (1 : ℝ) else -1) *
              Support.triadicLatticePoint p.2.2.2.1 p.2.2.2.2.1
                p.2.2.2.2.2.1) →
        (omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
            (Support.cgEllipLowerConstant d) (p.2.2.1 + 3)
            (Support.triadicLatticePoint p.2.2.2.1 p.2.2.2.2.1)
            ⟨stepOneS / 8, by have := stepOneS_pos; linarith only [this]⟩ (1 / 2) →
          A * Support.fluxCorrectedErrorRepresentative M p.1 (p.2.2.1 + 3)
              ⟨stepOneS / 8, by have := stepOneS_pos; linarith only [this]⟩
              (Cutoff.translateCutoffSample
                (Support.triadicLatticePoint p.2.2.2.1 p.2.2.2.2.1) omega) ≤
            stepOneS ^ (4 : ℕ) →
          StepSevenFlushBound M K1 K2 p.1 p.2.1 p.2.2.1
            (Support.triadicLatticePoint p.2.2.2.1 p.2.2.2.2.1) omega) := by
    refine ae_forall_of_forall_ae_of_countable ?_
    rintro ⟨L, m, n, nl, v, i, b⟩ ⟨hmL, hnm, hz, hover⟩
    have hinst := hmain M stepOneS hsrange hregime hsmall stepOneS_pos L m n hmL
      hnm (Support.triadicLatticePoint nl v) hz i
      (if b then (1 : ℝ) else -1)
      (by cases b <;> simp) hover
    exact hinst.mono fun omega h hmem hpin u hdat g hdir h1 h2 h3 =>
      h hmem hpin u hdat g hdir h1 h2 h3
  refine hpair.mono fun omega h L m n nl v i sigma hsigma hmL hnm hz hover => ?_
  rcases hsigma with hσ | hσ
  · exact fun hmem hpin =>
      h (L, m, n, nl, v, i, true) ⟨hmL, hnm, hz, by simpa [hσ] using hover⟩
        hmem hpin
  · exact fun hmem hpin =>
      h (L, m, n, nl, v, i, false) ⟨hmL, hnm, hz, by simpa [hσ] using hover⟩
        hmem hpin

/-! ## 4. The `ε`-pin, merged -/

theorem ae_shellEpsPin_merged (d : ℕ) :
    ∃ Cann : ℝ, 0 < Cann ∧
      ∀ A : ℝ, 0 < A →
        ∃ Cfl : ℝ, 1 ≤ Cfl ∧
          ∀ M : ABKModel d, M.gamma ≤ Cann⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
            M.gamma ≤ 1 / 256 →
              ∀ (Cedos Citer : ℝ) (k : ℕ), Cfl ≤ Cedos →
                ∀ alpha : ℝ, 0 < alpha → alpha < 1 →
                  M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                      Real.rpow stepOneSEighth (3 / 2 : ℝ) *
                        Disorder.cstar M ^ (2 : ℕ) *
                        stepOneEp
                          (stepOneDelta (stepOneC1 d Cedos 1 Citer k) alpha) →
                    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                      ∀ (j nl : ℤ) (v : Fin d → ℤ),
                        omega ∈ stepThreeGoodEvent M
                            (stepOneDelta (stepOneC1 d Cedos 1 Citer k) alpha) j
                            (Support.triadicLatticePoint nl v) →
                          ∀ L : ℤ, j ≤ L →
                            A * Support.fluxCorrectedErrorRepresentative M L j
                                ⟨stepOneS / 8,
                                  by have := stepOneS_pos; linarith only [this]⟩
                                (Cutoff.translateCutoffSample
                                  (Support.triadicLatticePoint nl v) omega) ≤
                              stepOneS ^ (4 : ℕ) := by
  obtain ⟨Cann, hCann, hmain⟩ := exists_cedosFloor_shellEpsPin d
  refine ⟨Cann, hCann, ?_⟩
  intro A hA
  obtain ⟨Cfl, hCfl, hbody⟩ := hmain A hA
  refine ⟨Cfl, hCfl, ?_⟩
  intro M hregime hgamma Cedos Citer k hfloor alpha halpha0 halpha1 hsmall
  have hsub : (⟨stepOneSEighth, stepOneSEighth_pos⟩ : {s : ℝ // 0 < s}) =
      (⟨stepOneS / 8, by have := stepOneS_pos; linarith only [this]⟩ : {s : ℝ // 0 < s}) := by
    refine Subtype.ext ?_
    change stepOneSEighth = stepOneS / 8
    rw [stepOneSEighth_eq, stepOneS]
    norm_num
  have hpair : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ p : ℤ × ℤ × (Fin d → ℤ), True →
        (omega ∈ stepThreeGoodEvent M
            (stepOneDelta (stepOneC1 d Cedos 1 Citer k) alpha) p.1
            (Support.triadicLatticePoint p.2.1 p.2.2) →
          ∀ L : ℤ, p.1 ≤ L →
            A * Support.fluxCorrectedErrorRepresentative M L p.1
                ⟨stepOneS / 8, by have := stepOneS_pos; linarith only [this]⟩
                (Cutoff.translateCutoffSample
                  (Support.triadicLatticePoint p.2.1 p.2.2) omega) ≤
              stepOneS ^ (4 : ℕ)) := by
    refine ae_forall_of_forall_ae_of_countable
      (Q := fun _ : ℤ × ℤ × (Fin d → ℤ) => True) ?_
    rintro ⟨j, nl, v⟩ -
    have hinst := hbody M hregime hgamma Cedos Citer k hfloor alpha halpha0
      halpha1 hsmall j (Support.triadicLatticePoint nl v)
    rw [hsub] at hinst
    exact hinst
  exact hpair.mono fun omega h j nl v hmem L hL => h (j, nl, v) trivial hmem L hL

end

end Algsuperdiff.Section4.Provider.Regularity
