/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResiduePluginErrorWeighted
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueBudget

/-!
# StitchDisplayLegs

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The scalar leg, priced on the display

## Why the pin is consumed twice

The contract asked the residue at the four `s`-powers `(0, 0, −2, −3
σ⁻¹)`; the composition delivers it at `(0, −6, −6, −7 σ⁻¹)`, the
display's own powers.  That is enough exactly because the pin appears on both
sides of the `S`-loop:

* once inside `ResiduePlugin.exists_flushResidue_le_displayLegs_of_epsPin`,
  where `loop_resolution` closes the `S ↦ R ↦ S` cycle;
* once here, as `p := s^{-4}·𝓔 ≤ 1`, which is what lets the widened residue's
  three tail legs be absorbed back into the display's tail legs
  (`sLeg_of_displayResidue`).

Only the *first* leg keeps the factor `p`, and that is the display's own first
leg.

## References

* ABK26, `l.harmonic.approximation.good.scales`; the frozen block of
  `Algsuperdiff/Section4/Provider/ExcessDecay/ProviderEpsFree.lean` (read for
  the byte-verification, never imported).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

/-- Scalar absorption retaining the error prefactor in the flat leg. -/
theorem sLeg_of_displayResidue_errorWeighted {p CB K X Ln Lh Lg Sm Hn R3n S dR : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hCB0 : 0 ≤ CB) (hK0 : 0 ≤ K)
    (hX0 : 0 ≤ X) (hLn0 : 0 ≤ Ln) (hLh0 : 0 ≤ Lh) (hLg0 : 0 ≤ Lg)
    (hR3n0 : 0 ≤ R3n) (hdR0 : 0 ≤ dR)
    (hSm : Sm ≤ dR * Hn) (hRHn : dR * (p * (R3n * Hn)) ≤ dR * Ln)
    (hS : S ≤ CB * (X + R3n * Sm + K * (X + Ln + Lh + Lg))) :
    p * S ≤ CB * (1 + 2 * K + dR) * (p * X + Ln + Lh + Lg) := by
  have hpS : p * S ≤ p * (CB * (X + R3n * Sm + K * (X + Ln + Lh + Lg))) :=
    mul_le_mul_of_nonneg_left hS hp0
  have hSm' : p * (R3n * Sm) ≤ dR * Ln := by
    have h1 : R3n * Sm ≤ R3n * (dR * Hn) := mul_le_mul_of_nonneg_left hSm hR3n0
    have h2 : p * (R3n * Sm) ≤ p * (R3n * (dR * Hn)) :=
      mul_le_mul_of_nonneg_left h1 hp0
    have h3 : p * (R3n * (dR * Hn)) = dR * (p * (R3n * Hn)) := by ring
    linarith only [h2, h3, hRHn]
  -- the three absorptions
  have hA1 : p * (CB * (R3n * Sm)) ≤ CB * (dR * Ln) := by
    have h := mul_le_mul_of_nonneg_left hSm' hCB0
    linarith only [h]
  have hA2 : p * (CB * (K * (Ln + Lh + Lg))) ≤ CB * K * (Ln + Lh + Lg) := by
    have hnn : 0 ≤ CB * (K * (Ln + Lh + Lg)) :=
      mul_nonneg hCB0 (mul_nonneg hK0 (by linarith only [hLn0, hLh0, hLg0]))
    have h := mul_le_mul_of_nonneg_right hp1 hnn
    linarith only [h]
  have hexp : p * (CB * (X + R3n * Sm + K * (X + Ln + Lh + Lg))) =
      CB * (p * X) + p * (CB * (R3n * Sm)) + CB * K * (p * X) +
        p * (CB * (K * (Ln + Lh + Lg))) := by ring
  rw [hexp] at hpS
  have hpX0 : 0 ≤ p * X := mul_nonneg hp0 hX0
  have q1 : 0 ≤ CB * (p * X) := mul_nonneg hCB0 hpX0
  have q2 : 0 ≤ CB * K * (p * X) := mul_nonneg (mul_nonneg hCB0 hK0) hpX0
  have q3 : 0 ≤ CB * dR * Ln := mul_nonneg (mul_nonneg hCB0 hdR0) hLn0
  have q4 : 0 ≤ CB * K * Ln := mul_nonneg (mul_nonneg hCB0 hK0) hLn0
  have q5 : 0 ≤ CB * K * Lh := mul_nonneg (mul_nonneg hCB0 hK0) hLh0
  have q6 : 0 ≤ CB * K * Lg := mul_nonneg (mul_nonneg hCB0 hK0) hLg0
  have q7 : 0 ≤ CB * dR * Lh := mul_nonneg (mul_nonneg hCB0 hdR0) hLh0
  have q8 : 0 ≤ CB * dR * Lg := mul_nonneg (mul_nonneg hCB0 hdR0) hLg0
  have q9 : 0 ≤ CB * dR * (p * X) := mul_nonneg (mul_nonneg hCB0 hdR0) hpX0
  have q10 : 0 ≤ CB * Ln := mul_nonneg hCB0 hLn0
  have q11 : 0 ≤ CB * Lh := mul_nonneg hCB0 hLh0
  have q12 : 0 ≤ CB * Lg := mul_nonneg hCB0 hLg0
  linarith only [hpS, hA1, hA2, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12]

/-- **The contested arithmetic, in the abstract.**

If the pin gives `A p <= 1` with `A >= 1`, then the widened residue `K (X + Ln
+ Lh + Lg)` -- whose legs already sit at the display's own `s`-powers --
multiplied by `p` and by the scalar control's constant, is dominated by the
display's four legs `p X, Ln, Lh, Lg`.  Nothing here is a norm: `X, Ln, Lh, Lg,
Sm, Hn` are free nonnegative reals. -/
theorem sLeg_of_displayResidue {p CB K X Ln Lh Lg Sm Hn R3n S dR : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hCB0 : 0 ≤ CB) (hK0 : 0 ≤ K)
    (hX0 : 0 ≤ X) (hLn0 : 0 ≤ Ln) (hLh0 : 0 ≤ Lh) (hLg0 : 0 ≤ Lg)
    (hR3n0 : 0 ≤ R3n) (hdR0 : 0 ≤ dR)
    (hSm : Sm ≤ dR * Hn) (hRHn : dR * (R3n * Hn) ≤ dR * Ln)
    (hS : S ≤ CB * (X + R3n * Sm + K * (X + Ln + Lh + Lg))) :
    p * S ≤ CB * (1 + 2 * K + dR) * (p * X + Ln + Lh + Lg) := by
  have hweighted : dR * (p * (R3n * Hn)) ≤ dR * Ln := by
    have h1 := mul_le_mul_of_nonneg_left hRHn hp0
    have h2 := mul_le_mul_of_nonneg_right hp1 (mul_nonneg hdR0 hLn0)
    nlinarith only [h1, h2]
  exact sLeg_of_displayResidue_errorWeighted hp0 hp1 hCB0 hK0 hX0 hLn0 hLh0 hLg0
    hR3n0 hdR0 hSm hweighted hS

/-- Error-weighted scalar assembly, including the shared window and norm preparation. -/
theorem exists_scalarLeg_le_displayLegs_of_epsPin_errorWeighted (d : ℕ) [NeZero d] :
    ∃ C A Cout : ℝ, 0 < C ∧ 0 < A ∧ 0 ≤ Cout ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m → ∀ x z : Vec d,
          x ∈ openCubeSet (originCube d m) →
          z ∈ openCubeSet (originCube d m) →
          ((fun y => x + y) '' openCubeSet (originCube d n) ⊆
            ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
              openCubeSet (originCube d m)) →
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
                  Real.rpow s (-(4 : ℝ)) *
                      Support.fluxCorrectedErrorRepresentative M L (n + 3)
                        ⟨s / 8, by linarith only [hs]⟩
                        (Cutoff.translateCutoffSample z omega) *
                      |volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
                        openCubeSet (originCube d (n + 2)))
                        (fun y => u.toFun y - hdat.toFun y)| ≤
                    Cout *
                      (Real.rpow s (-(4 : ℝ)) *
                          Support.fluxCorrectedErrorRepresentative M L (n + 3)
                            ⟨s / 8, by linarith only [hs]⟩
                            (Cutoff.translateCutoffSample z omega) *
                          (eLpNorm (fun y => u.toFun y -
                              volumeAverage ((((fun y' => z + y') ''
                                  openCubeSet (originCube d (n + 3))) ∩
                                openCubeSet (originCube d m))) u.toFun) 2
                            (Support.normalizedVolumeMeasureOn
                              ((((fun y' => z + y') ''
                                  openCubeSet (originCube d (n + 3))) ∩
                                openCubeSet (originCube d m))))).toReal +
                        Real.rpow s (-(6 : ℝ)) *
                          Support.fluxCorrectedErrorRepresentative M L (n + 3)
                            ⟨s / 8, by linarith only [hs]⟩
                            (Cutoff.translateCutoffSample z omega) *
                          Real.rpow (3 : ℝ) (n : ℝ) *
                          (eLpNorm hdat.grad 2
                            (Support.normalizedVolumeMeasureOn
                              ((((fun y' => z + y') ''
                                  openCubeSet (originCube d (n + 3))) ∩
                                openCubeSet (originCube d m))))).toReal +
                        Real.rpow s (-(6 : ℝ)) *
                          Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                          (Support.normalizedGagliardoESeminormOn
                            ((((fun y' => z + y') ''
                                openCubeSet (originCube d (n + 3))) ∩
                              openCubeSet (originCube d m))) s hdat.grad).toReal +
                        Real.rpow s (-(7 : ℝ)) *
                          ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ *
                          Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                          (Support.normalizedGagliardoESeminormOn
                            ((((fun y' => z + y') ''
                                openCubeSet (originCube d (n + 3))) ∩
                              openCubeSet (originCube d m))) s g).toReal) := by
  classical
  obtain ⟨C1, A0, K0, hC1, hA0, hK0, hplug⟩ :=
    exists_flushResidue_le_displayLegs_of_epsPin_errorWeighted d
  obtain ⟨CB, hCB0, hbud⟩ := exists_scalarControl_of_boundaryBranch_harmonicResidue d
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  refine ⟨C1, A0 + 1, CB * (1 + 2 * K0 + (d : ℝ)), hC1, by positivity,
    by positivity, ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm x z hx hz hgeom i sigma hsigma hover
  have hs1 : s ≤ 1 := hsrange.2
  have hnm2 : n + 2 ≤ m := by omega
  filter_upwards [hplug M s hsrange hregime hsmall hs L m n hmL hnm z hz i sigma
    hsigma hover] with omega hplugw
  intro hmem hpin u hdat g hsol hgL2 hgW hhW
  have hErep0 : (0 : ℝ) ≤ Support.fluxCorrectedErrorRepresentative M L (n + 3)
      ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) :=
    Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
  have hpin0 : A0 * Support.fluxCorrectedErrorRepresentative M L (n + 3)
      ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) ≤
      s ^ (4 : ℕ) :=
    error_pin_of_successor_constant hErep0 hpin
  have hres := hplugw hmem hpin0 u hdat g hsol hgL2 hgW hhW
  have hpcap : (A0 + 1) * Real.rpow s (-(4 : ℝ)) *
      Support.fluxCorrectedErrorRepresentative M L (n + 3)
        ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) ≤ 1 :=
    coarseGrainingResidue_coefficient_le_of_error_small hs (by positivity) hErep0 hpin
  have hscal := hbud hnm2 hx hz hgeom hsigma hover u hdat hsol.1 _ hres
  -- the coordinate sum against the vector norm
  have hW30 : volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m))) ≠ 0 :=
    volume_anchorWindow_ne_zero_of_flushSubCube hnm2 hz i hsigma
  have hvecfin : eLpNorm hdat.grad 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤ :=
    (memLp_normalizedVolumeMeasureOn_of_restrict hW30
      (hdat.grad_memVectorL2.mono_measure
        (Measure.restrict_mono Set.inter_subset_right le_rfl))).eLpNorm_ne_top
  have hsumb : (∑ i' : Fin d,
      (eLpNorm (fun y => hdat.grad y i') 2
        (Support.normalizedVolumeMeasureOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m))))).toReal) ≤
      (d : ℝ) * (eLpNorm hdat.grad 2
        (Support.normalizedVolumeMeasureOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m))))).toReal :=
    sum_coordinate_eLpNorm_toReal_le hvecfin
  have hzr : (3 : ℝ) ^ n = Real.rpow (3 : ℝ) (n : ℝ) := (Real.rpow_intCast 3 n).symm
  rw [hzr] at hscal
  -- the abbreviations
  set Erep : ℝ := Support.fluxCorrectedErrorRepresentative M L (n + 3)
    ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) with hErepdef
  set X : ℝ := (eLpNorm (fun y => u.toFun y -
      volumeAverage ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) u.toFun) 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))).toReal with hXdef
  set Gs : ℝ := (Support.normalizedGagliardoESeminormOn
      ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) s g).toReal with hGsdef
  set Hs : ℝ := (Support.normalizedGagliardoESeminormOn
      ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) s hdat.grad).toReal with hHsdef
  set Hn : ℝ := (eLpNorm hdat.grad 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))).toReal with hHndef
  set Sm : ℝ := ∑ i' : Fin d,
    (eLpNorm (fun y => hdat.grad y i') 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))).toReal with hSmdef
  set sig : ℝ := (Annealed.sigmaBar M (n + 3) : ℝ) with hsigdef
  set S4 : ℝ := Real.rpow s (-(4 : ℝ)) with hS4def
  set S6 : ℝ := Real.rpow s (-(6 : ℝ)) with hS6def
  set S7 : ℝ := Real.rpow s (-(7 : ℝ)) with hS7def
  set Q1s : ℝ := Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) with hQ1sdef
  set R3n : ℝ := Real.rpow (3 : ℝ) ((n : ℝ)) with hR3ndef
  set SV : ℝ := |volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
    openCubeSet (originCube d (n + 2))) (fun y => u.toFun y - hdat.toFun y)| with hSVdef
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hGs0 : 0 ≤ Gs := ENNReal.toReal_nonneg
  have hHs0 : 0 ≤ Hs := ENNReal.toReal_nonneg
  have hHn0 : 0 ≤ Hn := ENNReal.toReal_nonneg
  have hsig : (0 : ℝ) < sig := (Annealed.sigmaBar M (n + 3)).2
  have hsiginv0 : (0 : ℝ) ≤ sig⁻¹ := inv_nonneg.mpr hsig.le
  have hS40 : 0 ≤ S4 := Real.rpow_nonneg hs.le _
  have hS60 : 0 ≤ S6 := Real.rpow_nonneg hs.le _
  have hS70 : 0 ≤ S7 := Real.rpow_nonneg hs.le _
  have hQ1s0 : 0 ≤ Q1s := Real.rpow_nonneg (by norm_num) _
  have hR3n0 : 0 ≤ R3n := Real.rpow_nonneg (by norm_num) _
  have hS46 : S4 ≤ S6 := by
    rw [hS4def, hS6def]
    exact Real.rpow_le_rpow_of_exponent_ge hs hs1 (by norm_num)
  have hErepnn : 0 ≤ Erep := hErep0
  clear_value X Gs Hs Hn Sm Erep sig S4 S6 S7 Q1s R3n SV
  obtain ⟨Ln, hLndef, hLn0⟩ : ∃ t : ℝ, t = S6 * Erep * R3n * Hn ∧ 0 ≤ t :=
    ⟨_, rfl, mul_nonneg (mul_nonneg (mul_nonneg hS60 hErepnn) hR3n0) hHn0⟩
  obtain ⟨Lh, hLhdef, hLh0⟩ : ∃ t : ℝ, t = S6 * Q1s * Hs ∧ 0 ≤ t :=
    ⟨_, rfl, mul_nonneg (mul_nonneg hS60 hQ1s0) hHs0⟩
  obtain ⟨Lg, hLgdef, hLg0⟩ : ∃ t : ℝ, t = S7 * sig⁻¹ * Q1s * Gs ∧ 0 ≤ t :=
    ⟨_, rfl, mul_nonneg (mul_nonneg (mul_nonneg hS70 hsiginv0) hQ1s0) hGs0⟩
  obtain ⟨p, hpdef, hp0⟩ : ∃ t : ℝ, t = S4 * Erep ∧ 0 ≤ t :=
    ⟨_, rfl, mul_nonneg hS40 hErepnn⟩
  rw [← hLndef, ← hLhdef, ← hLgdef] at hscal
  rw [← hLndef, ← hLhdef, ← hLgdef, ← hpdef]
  have hp1 : p ≤ 1 := by
    have h1 : (A0 + 1) * p ≤ 1 := by
      rw [hpdef]
      linarith only [hpcap]
    have hnn : 0 ≤ A0 * p := mul_nonneg hA0.le hp0
    linarith only [h1, hnn, hp0]
  have hRHn : (d : ℝ) * (p * (R3n * Hn)) ≤ (d : ℝ) * Ln := by
    rw [hLndef, hpdef]
    have hRH : (0 : ℝ) ≤ R3n * Hn := mul_nonneg hR3n0 hHn0
    have h1 : S4 * Erep * (R3n * Hn) ≤ S6 * Erep * (R3n * Hn) := by
      calc S4 * Erep * (R3n * Hn) = S4 * (Erep * (R3n * Hn)) := by ring
        _ ≤ S6 * (Erep * (R3n * Hn)) :=
            mul_le_mul_of_nonneg_right hS46 (mul_nonneg hErepnn hRH)
        _ = S6 * Erep * (R3n * Hn) := by ring
    calc (d : ℝ) * (S4 * Erep * (R3n * Hn))
        ≤ (d : ℝ) * (S6 * Erep * (R3n * Hn)) := mul_le_mul_of_nonneg_left h1 hd0
      _ = (d : ℝ) * (S6 * Erep * R3n * Hn) := by ring
  have hmain := sLeg_of_displayResidue_errorWeighted (p := p) (CB := CB) (K := K0) (X := X)
    (Ln := Ln) (Lh := Lh) (Lg := Lg) (Sm := Sm) (Hn := Hn) (R3n := R3n)
    (S := SV) (dR := (d : ℝ)) hp0 hp1 hCB0 hK0 hX0 hLn0 hLh0 hLg0 hR3n0 hd0
    hsumb hRHn hscal
  exact hmain

/-- **The display's boundary leg, produced.**

At the anchor's own binders and under the disclosed pin, the frozen display's
`S`-leg `s^{-4} * E * |avg_{V1}(u - h)|` is dominated by the display's own four
legs at `sigmabar_{n+3}`.  This is the end-to-end statement: the
producer exists once the pin is granted. -/
theorem exists_scalarLeg_le_displayLegs_of_epsPin (d : ℕ) [NeZero d] :
    ∃ C A Cout : ℝ, 0 < C ∧ 0 < A ∧ 0 ≤ Cout ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m → ∀ x z : Vec d,
          x ∈ openCubeSet (originCube d m) →
          z ∈ openCubeSet (originCube d m) →
          ((fun y => x + y) '' openCubeSet (originCube d n) ⊆
            ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
              openCubeSet (originCube d m)) →
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
                  Real.rpow s (-(4 : ℝ)) *
                      Support.fluxCorrectedErrorRepresentative M L (n + 3)
                        ⟨s / 8, by linarith only [hs]⟩
                        (Cutoff.translateCutoffSample z omega) *
                      |volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
                        openCubeSet (originCube d (n + 2)))
                        (fun y => u.toFun y - hdat.toFun y)| ≤
                    Cout *
                      (Real.rpow s (-(4 : ℝ)) *
                          Support.fluxCorrectedErrorRepresentative M L (n + 3)
                            ⟨s / 8, by linarith only [hs]⟩
                            (Cutoff.translateCutoffSample z omega) *
                          (eLpNorm (fun y => u.toFun y -
                              volumeAverage ((((fun y' => z + y') ''
                                  openCubeSet (originCube d (n + 3))) ∩
                                openCubeSet (originCube d m))) u.toFun) 2
                            (Support.normalizedVolumeMeasureOn
                              ((((fun y' => z + y') ''
                                  openCubeSet (originCube d (n + 3))) ∩
                                openCubeSet (originCube d m))))).toReal +
                        Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
                          (eLpNorm hdat.grad 2
                            (Support.normalizedVolumeMeasureOn
                              ((((fun y' => z + y') ''
                                  openCubeSet (originCube d (n + 3))) ∩
                                openCubeSet (originCube d m))))).toReal +
                        Real.rpow s (-(6 : ℝ)) *
                          Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                          (Support.normalizedGagliardoESeminormOn
                            ((((fun y' => z + y') ''
                                openCubeSet (originCube d (n + 3))) ∩
                              openCubeSet (originCube d m))) s hdat.grad).toReal +
                        Real.rpow s (-(7 : ℝ)) *
                          ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ *
                          Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                          (Support.normalizedGagliardoESeminormOn
                            ((((fun y' => z + y') ''
                                openCubeSet (originCube d (n + 3))) ∩
                              openCubeSet (originCube d m))) s g).toReal) := by
  obtain ⟨C, A, Cout, hC, hA, hCout, hweighted⟩ :=
    exists_scalarLeg_le_displayLegs_of_epsPin_errorWeighted d
  refine ⟨C, A + 1, Cout, hC, by positivity, hCout, ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm x z hx hz hgeom i sigma hsigma hover
  filter_upwards [hweighted M s hsrange hregime hsmall hs L m n hmL hnm x z hx hz
    hgeom i sigma hsigma hover] with omega hom
  intro hmem hpin u hdat g hsol hgL2 hgW hhW
  have hE : 0 ≤ Support.fluxCorrectedErrorRepresentative M L (n + 3)
      ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) :=
    Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
  have hE1 : Support.fluxCorrectedErrorRepresentative M L (n + 3)
      ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) ≤ 1 := by
    have hs4 : s ^ (4 : ℕ) ≤ 1 := by
      simpa using pow_le_pow_left₀ hs.le hsrange.2 4
    have hAE := mul_nonneg hA.le hE
    nlinarith only [hpin, hs4, hAE]
  have hres := hom hmem (error_pin_of_successor_constant hE hpin)
    u hdat g hsol hgL2 hgW hhW
  refine hres.trans (mul_le_mul_of_nonneg_left ?_ hCout)
  have hS6 : (0 : ℝ) ≤ Real.rpow s (-(6 : ℝ)) := Real.rpow_nonneg hs.le _
  have h3n : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (n : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hflat := mul_le_mul_of_nonneg_left hE1
    (mul_nonneg (mul_nonneg hS6 h3n)
      (show 0 ≤ (eLpNorm hdat.grad 2
        (Support.normalizedVolumeMeasureOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m))))).toReal from ENNReal.toReal_nonneg))
  refine add_le_add_left (α := ℝ) ?_ _
  refine add_le_add_left (α := ℝ) ?_ _
  refine add_le_add_right (α := ℝ) ?_ _
  convert hflat using 1 <;> ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
