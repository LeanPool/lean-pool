/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationOscillationEndpoint

/-!
# LocalizationOscillationEndpointSixteen

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `e.lower.bound.oscillations` at the interior mesh, one power of `gamma` sharper

`LocalizationOscillationEndpoint` proves the interior-mesh endpoint of
`e.lower.bound.oscillations` at `gamma^{15}`, the manuscript's own exponent.
The transport of that endpoint from the **interior** meso grid to the **full**
mesh costs a boundary remainder, so the interior half has to be delivered with
one power of `gamma` to spare if the *sum* is to stay below `gamma^{15}`.

This module supplies that sharper interior endpoint.  Nothing in the proved
`gamma^{15}` route is edited: the sharpening is a **re-instantiation** of the
same three inputs

* `LocalizationOscillationDisplay.exists_freshShell*_gradient_oscillation_lower_bound_display`,
* `LocalizationEnvelopeWire.exists_freshShell_gridFourthMoment_mesoWindowEnergy_le_wired`,
*
`exists_gamma0_integrable_freshShell*_meshEnergyCell_rpow_four`,

at the *same* explicit threshold
`min gcell (min (1/4) (min genv (min 3^{-(d+3)} (1/(1+Ctot)))))`.

## Where the spare power comes from

`LocalizationOscillationBudget.three_term_budget_le` collapses the display's
three terms to `Ctot gamma^{31}` and then uses `hfinal : Ctot gamma^{16} <= 1`
to land on `gamma^{15}`.  But the threshold that produces `hfinal` is `gamma <=
1/(1 + Ctot)`, which gives `Ctot gamma <= 1` outright; since `gamma <= 1`, it
gives `Ctot gamma^k <= 1` for **every** `k >= 1`, in particular for `k = 15`.
That is the slack the module docstring of the proved endpoint does not use: the
`1/(1+Ctot)` factor in its `min` is one power stronger than the `gamma^{15}`
conclusion needs.

`three_term_budget_le_mul` below is the proved collapse stopped one step
earlier, at `Ctot gamma^{31}`; `three_term_budget_le_sixteen` is the `k = 15`
instance of the last step.  The proved `three_term_budget_le` is the `k = 16`
instance and is untouched.

## What is proved

* `three_term_budget_le_mul` -- the three-term collapse, at `Ctot gamma^{31}`.
* `three_term_budget_le_sixteen` -- its `gamma^{16}` form.
* `exists_gamma0_freshShellDirichlet_meshOscillation_le_gamma_pow_sixteen` and
  its Neumann mirror -- the interior endpoint at `gamma^{16}`.  Statement,
  binders and threshold are those of the proved `..._fifteen` pair, with `15`
  replaced by `16` in the conclusion and nothing else changed.

## Binders

Verbatim those of `LocalizationOscillationEndpoint`: `hd`, the model gate
`M.gamma <= gamma0`, the induction state, the four source gates `0 < h`,
`m - h <= m0`, `h <= 6 cstar gamma^{-1}`, `10^10 gamma^{-1} <= K - m`, the two
direction bounds, the base point `z0`, and the corrector family with the weak
formulation of `e.def.w`.  **No sample-space binder survives**, for the same
reason as there.

## Scope

There is no `sorry`.

## References

* ABK26, `e.lower.bound.oscillations`, `e.recurrence.params`, `e.def.w`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3.Cutoff
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The three-term collapse, stopped one step earlier -/

/-- **The three surviving terms of `e.lower.bound.oscillations`, at
`Ctot gamma^{31}`.**  This is `LocalizationOscillationBudget.three_term_budget_le`
with its last step -- the absorption of `Ctot` into a power of `gamma` --
removed, so that the caller may choose which power to land on.

: purely on the displayed numeric hypotheses; no model, field or measure
occurs. -/
theorem three_term_budget_le_mul {C W Csig sqd Nr G P S Eb gamma Ctot Kn : ℝ}
    (hC : 0 ≤ C) (hW : 0 ≤ W) (hCsig : 0 ≤ Csig) (hsqd : 0 ≤ sqd)
    (hNr0 : 0 ≤ Nr) (hG0 : 0 ≤ G) (_hP0 : 0 ≤ P) (_hS0 : 0 ≤ S) (hEb0 : 0 ≤ Eb)
    (_hKn0 : 0 ≤ Kn) (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1)
    (hG : G ≤ gamma ^ (32 : ℕ)) (hSP : S * P ≤ Csig)
    (hNr : Nr * gamma ≤ Kn) (hEb : Eb ≤ 1)
    (hCtot : C * W + Kn * (C * sqd * Csig) + C * Csig ≤ Ctot) :
    C * (G * W) + C * (Nr * (S * sqd * Eb)) * (G * P) + C * S * (G * P) ≤
      Ctot * gamma ^ (31 : ℕ) := by
  have hg31 : (0 : ℝ) ≤ gamma ^ (31 : ℕ) := pow_nonneg hgamma0.le _
  have hg3231 : gamma ^ (32 : ℕ) ≤ gamma ^ (31 : ℕ) :=
    pow_le_pow_of_le_one hgamma0.le hgamma1 (by norm_num)
  have hG31 : G ≤ gamma ^ (31 : ℕ) := le_trans hG hg3231
  have h1 : C * (G * W) ≤ C * W * gamma ^ (31 : ℕ) := by
    have hstep : G * W ≤ gamma ^ (31 : ℕ) * W := mul_le_mul_of_nonneg_right hG31 hW
    calc C * (G * W) ≤ C * (gamma ^ (31 : ℕ) * W) :=
          mul_le_mul_of_nonneg_left hstep hC
      _ = C * W * gamma ^ (31 : ℕ) := by ring
  have h3 : C * S * (G * P) ≤ C * Csig * gamma ^ (31 : ℕ) := by
    have hle1 : C * G * (S * P) ≤ C * G * Csig :=
      mul_le_mul_of_nonneg_left hSP (mul_nonneg hC hG0)
    have hle2 : C * G * Csig ≤ C * gamma ^ (31 : ℕ) * Csig := by
      have hstep : C * G ≤ C * gamma ^ (31 : ℕ) := mul_le_mul_of_nonneg_left hG31 hC
      exact mul_le_mul_of_nonneg_right hstep hCsig
    calc C * S * (G * P) = C * G * (S * P) := by ring
      _ ≤ C * G * Csig := hle1
      _ ≤ C * gamma ^ (31 : ℕ) * Csig := hle2
      _ = C * Csig * gamma ^ (31 : ℕ) := by ring
  have h2 : C * (Nr * (S * sqd * Eb)) * (G * P) ≤
      Kn * (C * sqd * Csig) * gamma ^ (31 : ℕ) := by
    have hA0 : (0 : ℝ) ≤ C * sqd * Eb := mul_nonneg (mul_nonneg hC hsqd) hEb0
    have hNrG0 : (0 : ℝ) ≤ Nr * G := mul_nonneg hNr0 hG0
    have hstep1 : (C * sqd * Eb) * (Nr * G) * (S * P) ≤
        (C * sqd * Eb) * (Nr * G) * Csig :=
      mul_le_mul_of_nonneg_left hSP (mul_nonneg hA0 hNrG0)
    have hstep2 : C * sqd * Eb ≤ C * sqd := by
      have hCs : (0 : ℝ) ≤ C * sqd := mul_nonneg hC hsqd
      exact mul_le_of_le_one_right hCs hEb
    have hNrGle : Nr * G ≤ Kn * gamma ^ (31 : ℕ) := by
      have hNrG : Nr * G ≤ Nr * gamma ^ (32 : ℕ) := mul_le_mul_of_nonneg_left hG hNr0
      have hstep : Nr * gamma ^ (32 : ℕ) = (Nr * gamma) * gamma ^ (31 : ℕ) := by ring
      have hfin : (Nr * gamma) * gamma ^ (31 : ℕ) ≤ Kn * gamma ^ (31 : ℕ) :=
        mul_le_mul_of_nonneg_right hNr hg31
      linarith [hNrG, hstep.le, hstep.ge, hfin]
    have hp1 : (C * sqd * Eb) * (Nr * G) ≤ (C * sqd) * (Kn * gamma ^ (31 : ℕ)) := by
      have hq1 : (C * sqd * Eb) * (Nr * G) ≤ (C * sqd) * (Nr * G) :=
        mul_le_mul_of_nonneg_right hstep2 hNrG0
      have hq2 : (C * sqd) * (Nr * G) ≤ (C * sqd) * (Kn * gamma ^ (31 : ℕ)) :=
        mul_le_mul_of_nonneg_left hNrGle (mul_nonneg hC hsqd)
      linarith
    calc C * (Nr * (S * sqd * Eb)) * (G * P)
        = (C * sqd * Eb) * (Nr * G) * (S * P) := by ring
      _ ≤ (C * sqd * Eb) * (Nr * G) * Csig := hstep1
      _ ≤ (C * sqd) * (Kn * gamma ^ (31 : ℕ)) * Csig :=
          mul_le_mul_of_nonneg_right hp1 hCsig
      _ = Kn * (C * sqd * Csig) * gamma ^ (31 : ℕ) := by ring
  have hsum : C * (G * W) + C * (Nr * (S * sqd * Eb)) * (G * P) + C * S * (G * P) ≤
      (C * W + Kn * (C * sqd * Csig) + C * Csig) * gamma ^ (31 : ℕ) := by
    have hadd := add_le_add (add_le_add h1 h2) h3
    calc C * (G * W) + C * (Nr * (S * sqd * Eb)) * (G * P) + C * S * (G * P)
        ≤ C * W * gamma ^ (31 : ℕ) + Kn * (C * sqd * Csig) * gamma ^ (31 : ℕ)
          + C * Csig * gamma ^ (31 : ℕ) := hadd
      _ = (C * W + Kn * (C * sqd * Csig) + C * Csig) * gamma ^ (31 : ℕ) := by ring
  have hmid : (C * W + Kn * (C * sqd * Csig) + C * Csig) * gamma ^ (31 : ℕ) ≤
      Ctot * gamma ^ (31 : ℕ) := mul_le_mul_of_nonneg_right hCtot hg31
  linarith [hsum, hmid]

/-- **The `gamma^{16}` form of the three-term collapse.**  Identical to
`LocalizationOscillationBudget.three_term_budget_le` except that the absorption
gate is `Ctot gamma^{15} <= 1` and the conclusion is `gamma^{16}`. -/
theorem three_term_budget_le_sixteen {C W Csig sqd Nr G P S Eb gamma Ctot Kn : ℝ}
    (hC : 0 ≤ C) (hW : 0 ≤ W) (hCsig : 0 ≤ Csig) (hsqd : 0 ≤ sqd)
    (hNr0 : 0 ≤ Nr) (hG0 : 0 ≤ G) (hP0 : 0 ≤ P) (hS0 : 0 ≤ S) (hEb0 : 0 ≤ Eb)
    (hKn0 : 0 ≤ Kn) (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1)
    (hG : G ≤ gamma ^ (32 : ℕ)) (hSP : S * P ≤ Csig)
    (hNr : Nr * gamma ≤ Kn) (hEb : Eb ≤ 1)
    (hCtot : C * W + Kn * (C * sqd * Csig) + C * Csig ≤ Ctot)
    (hfinal : Ctot * gamma ^ (15 : ℕ) ≤ 1) :
    C * (G * W) + C * (Nr * (S * sqd * Eb)) * (G * P) + C * S * (G * P) ≤
      gamma ^ (16 : ℕ) := by
  have hmain := three_term_budget_le_mul hC hW hCsig hsqd hNr0 hG0 hP0 hS0 hEb0 hKn0
    hgamma0 hgamma1 hG hSP hNr hEb hCtot
  have hg16 : (0 : ℝ) ≤ gamma ^ (16 : ℕ) := pow_nonneg hgamma0.le _
  have hlast : Ctot * gamma ^ (31 : ℕ) ≤ gamma ^ (16 : ℕ) := by
    calc Ctot * gamma ^ (31 : ℕ) = (Ctot * gamma ^ (15 : ℕ)) * gamma ^ (16 : ℕ) := by ring
      _ ≤ 1 * gamma ^ (16 : ℕ) := mul_le_mul_of_nonneg_right hfinal hg16
      _ = gamma ^ (16 : ℕ) := one_mul _
  linarith

/-! ## The two sharpened endpoints -/

private theorem localizationOscillationEndpointSixteen_comparisonBounds1 :
    ∀ (d : ℕ) (Cdisp : ℝ) (_ : (0 : ℝ) ≤ Cdisp)
      (_ :
        ∀ (M : ABKModel d) (K n : ℤ) (N : ℕ),
          d + (3 : ℕ) ≤ N →
            ∀ (highScale : ℤ),
              n + (↑N : ℤ) < highScale →
                ∀ (sigmaInv : ℝ),
                  (0 : ℝ) ≤ sigmaInv →
                    ∀ (e z₀ : Vec d) (wD : ShellSeq d → H10Function (openCubeSet (originCube d K))),
                      (∀ (omega : ShellSeq d),
                          IsZeroTraceDirichletRhsWeakSolution (fun (_ : Vec d) => (1 : Matrix (Fin
                            d) (Fin d) ℝ))
                            (openCubeSet (originCube d K)) (wD omega) fun (x : Vec d) =>
                            -Corrector.streamForcing sigmaInv omega (n + (↑N : ℤ)) highScale e x) →
                        ∀ (W : ℝ),
                          (0 : ℝ) ≤ W →
                            (gridFourthMoment (↑M.P : Measure (ℤ → Frozen.Assumptions.ShellField d))
                                  (interiorMesoCubeGrid d K n (n + (↑N : ℤ) - (1 : ℤ)))
                                  fun (R : TriadicCube d) (omega : ℤ →
                                    Frozen.Assumptions.ShellField d) =>
                                  meshEnergyCell (n + (↑N : ℤ)) (wD omega).grad R) ≤
                                W ^ (4 : ℕ) →
                              (∀ R ∈ interiorMesoCubeGrid d K n (n + (↑N : ℤ) - (1 : ℤ)),
                                  Integrable
                                    (fun (omega : ShellSeq d) => meshEnergyCell (n + (↑N : ℤ)) (wD
                                      omega).grad R ^ (4 : ℝ))
                                    (↑M.P : Measure (ℤ → Frozen.Assumptions.ShellField d))) →
                                (gridFourthMomentRoot (↑M.P : Measure (ℤ →
                                  Frozen.Assumptions.ShellField d))
                                      (interiorMesoCubeGrid d K n (n + (↑N : ℤ) - (1 : ℤ)))
                                      fun (R : TriadicCube d) (omega : ℤ →
                                        Frozen.Assumptions.ShellField d) =>
                                      meshOscillationCell n (wD omega).grad R) +
                                    sigmaInv *
                                      ((3 : ℝ) ^ (↑n : ℝ) *
                                        (∫ (omega : ShellSeq d),
                                            shellDerivNormSum (n + (↑N : ℤ)) highScale z₀ omega ^
                                              (4 : ℝ) ∂(↑M.P : Measure (ℤ →
                                                Frozen.Assumptions.ShellField d))) ^
                                          (4 : ℝ)⁻¹) ≤
                                  Cdisp * ((3 : ℝ) ^ (-(↑N : ℝ)) * W) +
                                      Cdisp * ((↑N : ℝ) * (sigmaInv * √(↑d : ℝ) * vecNorm e)) *
                                        ((3 : ℝ) ^ (-(↑N : ℝ)) * (3 : ℝ) ^ (M.gamma * ((↑n : ℝ) +
                                          (↑N : ℝ)))) +
                                    Cdisp * sigmaInv *
                                      ((3 : ℝ) ^ (-(↑N : ℝ)) * (3 : ℝ) ^ (M.gamma * ((↑n : ℝ) +
                                        (↑N : ℝ)))))
      (Chead W0 : ℝ) (_ : W0 = ((3 : ℝ) ^ d * freshShellFourthEnergyConst Chead (1 : ℝ)) ^ (4 :
        ℝ)⁻¹) (Ctot : ℝ)
      (_ :
        Ctot = Cdisp * W0 + (96 : ℝ) * (Cdisp * √(↑d : ℝ) * shellNormalizationConst) + Cdisp *
          shellNormalizationConst)
      (_ : (0 : ℝ) ≤ Ctot) (M : ABKModel d) (m0 : ℤ) (Eind : { E : ℝ // (1 : ℝ) ≤ E })
      (_ : Frozen.Section3.inductionState M m0 Eind) (m K : ℤ) (h : ℕ) (_ : (0 : ℕ) < h) (_ : m -
        (↑h : ℤ) ≤ m0)
      (_ : (↑h : ℝ) ≤ (6 : ℝ) * Disorder.cstar M * M.gamma⁻¹) (e : Vec d) (_ : vecNorm e ≤ (1 :
        ℝ)) (z₀ : Vec d)
      (wD : ShellSeq d → H10Function (openCubeSet (originCube d K)))
      (_ :
        ∀ (omega : ShellSeq d),
          IsZeroTraceDirichletRhsWeakSolution (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
            (openCubeSet (originCube d K)) (wD omega) fun (x : Vec d) =>
            -Corrector.streamForcing (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ omega (m - (↑h
              : ℤ)) m e x)
      (_ : M.gamma ≤ (1 : ℝ) / ((1 : ℝ) + Ctot))
      (_ :
        ∀ (omega : ShellSeq d),
          IntegrableOn (fun (x : Vec d) => vecNormSq ((wD omega).grad x)) (openCubeSet (originCube
            d K)) volume)
      (_ : (0 : ℝ) < M.gamma) (_ : M.gamma ≤ (1 : ℝ)) (nbuf : ℤ) (Ngap : ℕ)
      (_ : Ngap = recurrenceGap recurrenceGapMultiplier M.gamma) (_ : nbuf + (↑Ngap : ℤ) = m - (↑h
        : ℤ))
      (_ : (↑nbuf : ℝ) + (↑Ngap : ℝ) = (↑(m - (↑h : ℤ)) : ℝ)) (_ : d + (3 : ℕ) ≤ Ngap)
      (_ : nbuf + (↑Ngap : ℤ) < m)
      (_ :
        ∀ R ∈ interiorMesoCubeGrid d K nbuf (nbuf + (↑Ngap : ℤ) - (1 : ℤ)),
          Integrable (fun (omega : ShellSeq d) => meshEnergyCell (nbuf + (↑Ngap : ℤ)) (wD
            omega).grad R ^ (4 : ℝ))
            (↑M.P : Measure (ℤ → Frozen.Assumptions.ShellField d)))
      (Aenv : ℝ)
      (_ :
        (gridFourthMoment (↑M.P : Measure (ℤ → Frozen.Assumptions.ShellField d))
            (interiorMesoCubeGrid d K nbuf (nbuf + (↑Ngap : ℤ) - (1 : ℤ)))
            fun (R : TriadicCube d) (omega : ℤ → Frozen.Assumptions.ShellField d) =>
            mesoWindowEnergy (nbuf + (↑Ngap : ℤ)) (wD omega).grad R) ≤
          Aenv)
      (_ : Aenv = (3 : ℝ) ^ d * freshShellFourthEnergyConst Chead (M.gamma ^ (100 : ℕ))) (_ : (0 :
        ℝ) ≤ Aenv)
      (W : ℝ) (_ : W = Aenv ^ (4 : ℝ)⁻¹),
      (gridFourthMomentRoot (↑M.P : Measure (ℤ → Frozen.Assumptions.ShellField d))
            (interiorMesoCubeGrid d K nbuf (nbuf + (↑Ngap : ℤ) - (1 : ℤ)))
            fun (R : TriadicCube d) (omega : ℤ → Frozen.Assumptions.ShellField d) =>
            meshOscillationCell nbuf (wD omega).grad R) +
          (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ *
            ((3 : ℝ) ^ (↑nbuf : ℝ) *
              (∫ (omega : ShellSeq d),
                  shellDerivNormSum (nbuf + (↑Ngap : ℤ)) m z₀ omega ^
                    (4 : ℝ) ∂(↑M.P : Measure (ℤ → Frozen.Assumptions.ShellField d))) ^
                (4 : ℝ)⁻¹) ≤
        M.gamma ^ (16 : ℕ) := by
  intro d Cdisp hCdisp0 hdisp Chead W0 hW0 Ctot hCtot hCtot0 M _ _ hstate m K h hhpos hm0 hcstar e
    he z₀ wD hsol hCgate hsq hgamma0 hgamma1 nbuf Ngap hNgap hsum hsumR hdimN hlt hcellInt Aenv
      henvD hAenv hAenv0 W hW
  have hW0nn : 0 ≤ W := by rw [hW]; exact Real.rpow_nonneg hAenv0 _
  have hWpow : W ^ (4 : ℕ) = Aenv := by
    rw [hW, ← Real.rpow_natCast (Aenv ^ ((4 : ℝ)⁻¹)) 4, ← Real.rpow_mul hAenv0,
      show ((4 : ℝ)⁻¹ * ((4 : ℕ) : ℝ)) = 1 by norm_num]
    exact Real.rpow_one Aenv
  have hcoarse : gridFourthMoment M.P.toMeasure
      (interiorMesoCubeGrid d K nbuf (nbuf + (Ngap : ℤ) - 1))
      (fun R omega => meshEnergyCell (nbuf + (Ngap : ℤ))
        (wD omega).toH1Function.grad R) ≤ W ^ (4 : ℕ) := by
    rw [hWpow]
    exact henvD
  have hsigma0 : (0 : ℝ) ≤ ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ :=
    (inv_pos.2 (Annealed.sigmaBar_characterization M (m - (h : ℤ))).1).le
  have hmain := hdisp M K nbuf Ngap hdimN m hlt
    ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ hsigma0 e z₀ wD
    (by rw [hsum]; exact hsol) W hW0nn hcoarse hcellInt
  have hGle : (3 : ℝ) ^ (-((Ngap : ℕ) : ℝ)) ≤ M.gamma ^ (32 : ℕ) := by
    have hbase := rpow_three_neg_recurrenceGap_le_gamma_pow recurrenceGapMultiplier
      (gamma := M.gamma) hgamma0 hgamma1
    rw [hNgap]
    simpa [recurrenceGapMultiplier] using hbase
  have hNrle : ((Ngap : ℕ) : ℝ) * M.gamma ≤ 96 := by
    have hbase := recurrenceGap_mul_gamma_le recurrenceGapMultiplier
      (gamma := M.gamma) hgamma0 hgamma1
    rw [hNgap]
    calc ((recurrenceGap recurrenceGapMultiplier M.gamma : ℕ) : ℝ) * M.gamma
        ≤ 3 * ((recurrenceGapMultiplier : ℕ) : ℝ) := hbase
      _ = 96 := by norm_num [recurrenceGapMultiplier]
  have hSPle : ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ *
      (3 : ℝ) ^ (M.gamma * (((nbuf : ℤ) : ℝ) + ((Ngap : ℕ) : ℝ))) ≤
        shellNormalizationConst := by
    rw [hsumR]
    exact sigmaBarInv_mul_rpow_gamma_shell_le M hstate hhpos hm0 hcstar
  have hWle : W ≤ W0 := by
    rw [hW, hW0]
    refine Real.rpow_le_rpow hAenv0 ?_ (by norm_num)
    rw [hAenv]
    have hmono : freshShellFourthEnergyConst Chead (M.gamma ^ (100 : ℕ)) ≤
        freshShellFourthEnergyConst Chead 1 := by
      simp only [freshShellFourthEnergyConst]
      have h1 : M.gamma ^ (100 : ℕ) ≤ 1 := pow_le_one₀ hgamma0.le hgamma1
      have h0 : (0 : ℝ) ≤ M.gamma ^ (100 : ℕ) := by positivity
      have hsq : (M.gamma ^ (100 : ℕ)) ^ (2 : ℕ) ≤ (1 : ℝ) ^ (2 : ℕ) :=
        pow_le_pow_left₀ h0 h1 2
      have hcoef : (0 : ℝ) ≤ 32 * Real.exp 1 ^ (2 : ℕ) := by positivity
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq hcoef)
    have h3d : (0 : ℝ) ≤ (3 : ℝ) ^ d := by positivity
    exact mul_le_mul_of_nonneg_left hmono h3d
  have hCtotle : Cdisp * W + 96 * (Cdisp * Real.sqrt (d : ℝ) * shellNormalizationConst)
      + Cdisp * shellNormalizationConst ≤ Ctot := by
    rw [hCtot]
    have : Cdisp * W ≤ Cdisp * W0 := mul_le_mul_of_nonneg_left hWle hCdisp0
    linarith
  have hfinal : Ctot * M.gamma ^ (15 : ℕ) ≤ 1 := by
    have h15 : M.gamma ^ (15 : ℕ) ≤ M.gamma := by
      calc M.gamma ^ (15 : ℕ) ≤ M.gamma ^ (1 : ℕ) :=
            pow_le_pow_of_le_one hgamma0.le hgamma1 (by norm_num)
        _ = M.gamma := pow_one _
    have hCg : Ctot * M.gamma ^ (15 : ℕ) ≤ Ctot * M.gamma :=
      mul_le_mul_of_nonneg_left h15 hCtot0
    have hCg2 : Ctot * M.gamma ≤ Ctot * (1 / (1 + Ctot)) :=
      mul_le_mul_of_nonneg_left hCgate hCtot0
    have hden : (0 : ℝ) < 1 + Ctot := by linarith
    have hlast : Ctot * (1 / (1 + Ctot)) ≤ 1 := by
      rw [mul_one_div, div_le_one hden]
      linarith
    linarith
  have hG0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((Ngap : ℕ) : ℝ)) :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
  have hP0 : (0 : ℝ) ≤
      (3 : ℝ) ^ (M.gamma * (((nbuf : ℤ) : ℝ) + ((Ngap : ℕ) : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
  have hbudget : Cdisp * ((3 : ℝ) ^ (-((Ngap : ℕ) : ℝ)) * W) +
        Cdisp * (((Ngap : ℕ) : ℝ) *
            (((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ * Real.sqrt (d : ℝ) *
              Book.Ch02.vecNorm e)) *
          ((3 : ℝ) ^ (-((Ngap : ℕ) : ℝ)) *
            (3 : ℝ) ^ (M.gamma * (((nbuf : ℤ) : ℝ) + ((Ngap : ℕ) : ℝ)))) +
        Cdisp * ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ *
          ((3 : ℝ) ^ (-((Ngap : ℕ) : ℝ)) *
            (3 : ℝ) ^ (M.gamma * (((nbuf : ℤ) : ℝ) + ((Ngap : ℕ) : ℝ)))) ≤
      M.gamma ^ (16 : ℕ) :=
    three_term_budget_le_sixteen hCdisp0 hW0nn shellNormalizationConst_nonneg
      (Real.sqrt_nonneg _) (Nat.cast_nonneg _) hG0 hP0 hsigma0
      (Book.Ch02.vecNorm_nonneg e) (by norm_num) hgamma0 hgamma1 hGle hSPle hNrle he
      hCtotle hfinal
  have hgoal := le_trans hmain hbudget
  exact hgoal

/-- **`e.lower.bound.oscillations` for the Dirichlet corrector of `e.def.w`, at the
recurrence parameters, below `gamma^{16}`.**

Statement, binders and threshold are those of
`exists_gamma0_freshShellDirichlet_meshOscillation_le_gamma_pow_fifteen`; only
the conclusion's exponent changes. -/
theorem exists_gamma0_freshShellDirichlet_meshOscillation_le_gamma_pow_sixteen
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
        ∀ (m0 : ℤ) (Eind : {E : ℝ // 1 ≤ E}),
          Algsuperdiff.Frozen.Section3.inductionState M m0 Eind →
          ∀ (m K : ℤ) (h : ℕ), 0 < h → m - (h : ℤ) ≤ m0 →
            (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
            (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (K : ℝ) - (m : ℝ) →
            ∀ e e' : Vec d, Book.Ch02.vecNorm e ≤ 1 →
              Book.Ch02.vecNorm e' ≤ 1 →
              ∀ z₀ : Vec d,
                ∀ wD : Cutoff.ShellSeq d → H10Function (openCubeSet (originCube d K)),
                  (∀ omega, IsZeroTraceDirichletRhsWeakSolution
                      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                      (openCubeSet (originCube d K)) (wD omega)
                      (fun x => -Corrector.streamForcing
                        ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ omega
                        (m - (h : ℤ)) m e x)) →
                  gridFourthMomentRoot M.P.toMeasure
                      (interiorMesoCubeGrid d K
                        (recurrenceMesoScale recurrenceGapMultiplier M.gamma m (h : ℤ))
                        (m - (h : ℤ) - 1))
                      (fun R omega => meshOscillationCell
                        (recurrenceMesoScale recurrenceGapMultiplier M.gamma m (h : ℤ))
                        (wD omega).toH1Function.grad R) +
                      ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ *
                        ((3 : ℝ) ^ ((recurrenceMesoScale recurrenceGapMultiplier M.gamma
                            m (h : ℤ) : ℤ) : ℝ) *
                          (∫ omega : Cutoff.ShellSeq d,
                            shellDerivNormSum (m - (h : ℤ)) m z₀ omega ^ (4 : ℝ)
                              ∂M.P.toMeasure) ^ ((4 : ℝ)⁻¹)) ≤
                    M.gamma ^ (16 : ℕ) := by
  classical
  obtain ⟨Cdisp, hCdisp0, hdisp⟩ :=
    exists_freshShellDirichlet_gradient_oscillation_lower_bound_display
      (d := d) (lt_of_lt_of_le (by norm_num) hd)
  obtain ⟨Chead, -, genv, hgenv0, -, henv⟩ :=
    exists_freshShell_gridFourthMoment_mesoWindowEnergy_le_wired d hd
  obtain ⟨gcell, hgcell0, -, hcell⟩ :=
    exists_gamma0_integrable_freshShellDirichlet_meshEnergyCell_rpow_four d hd
  obtain ⟨W0, hW0⟩ : ∃ W0 : ℝ,
      W0 = ((3 : ℝ) ^ d * freshShellFourthEnergyConst Chead 1) ^ ((4 : ℝ)⁻¹) := ⟨_, rfl⟩
  have hbase0 : (0 : ℝ) ≤ (3 : ℝ) ^ d * freshShellFourthEnergyConst Chead 1 :=
    mul_nonneg (by positivity) (freshShellFourthEnergyConst_nonneg _ _)
  have hW00 : 0 ≤ W0 := by rw [hW0]; exact Real.rpow_nonneg hbase0 _
  obtain ⟨Ctot, hCtot⟩ : ∃ Ctot : ℝ,
      Ctot = Cdisp * W0 + 96 * (Cdisp * Real.sqrt (d : ℝ) * shellNormalizationConst)
        + Cdisp * shellNormalizationConst := ⟨_, rfl⟩
  have hCtot0 : 0 ≤ Ctot := by
    have hsq : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
    have hsn : (0 : ℝ) ≤ shellNormalizationConst := shellNormalizationConst_nonneg
    have hb1 : (0 : ℝ) ≤ Cdisp * W0 := mul_nonneg hCdisp0 hW00
    have hb2 : (0 : ℝ) ≤ 96 * (Cdisp * Real.sqrt (d : ℝ) * shellNormalizationConst) :=
      mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hCdisp0 hsq) hsn)
    have hb3 : (0 : ℝ) ≤ Cdisp * shellNormalizationConst := mul_nonneg hCdisp0 hsn
    rw [hCtot]
    linarith
  refine ⟨min gcell
      (min (1 / 4) (min genv (min ((3 : ℝ) ^ (-((d : ℝ) + 3))) (1 / (1 + Ctot))))),
    ?_, le_trans (min_le_right _ _) (min_le_left _ _), ?_⟩
  · refine lt_min hgcell0 (lt_min (by norm_num) (lt_min hgenv0 (lt_min ?_ ?_)))
    · exact Real.rpow_pos_of_pos (by norm_num) _
    · exact div_pos one_pos (by linarith)
  intro M hMgamma m0 Eind hstate m K h hhpos hm0 hcstar hK e e' he he' z₀ wD hsol
  have hgcellle : M.gamma ≤ gcell := le_trans hMgamma (min_le_left _ _)
  have hq : M.gamma ≤ 1 / 4 :=
    le_trans hMgamma (le_trans (min_le_right _ _) (min_le_left _ _))
  have hgenvle : M.gamma ≤ genv :=
    le_trans hMgamma
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hdimgate : M.gamma ≤ (3 : ℝ) ^ (-((d : ℝ) + 3)) :=
    le_trans hMgamma (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hCgate : M.gamma ≤ 1 / (1 + Ctot) :=
    le_trans hMgamma (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  clear hMgamma
  have hgrad : ∀ omega : Cutoff.ShellSeq d,
      MemLp (wD omega).toH1Function.grad (8 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d K)) := fun omega =>
    memLp_eight_grad_freshShellDirichlet hd (originCube d K)
      ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ omega (m - (h : ℤ)) m e
      (wD omega) (hsol omega)
  have hmem : ∀ omega : Cutoff.ShellSeq d,
      MemLp (fun x => Book.Ch02.vecNorm ((wD omega).toH1Function.grad x)) 8
        (normalizedCubeMeasure (originCube d K)) := fun omega =>
    memLp_vecNorm_eight_of_memLp_eight _ (hgrad omega)
  have hcoord : ∀ (omega : Cutoff.ShellSeq d) (k : Fin d),
      IntegrableOn (fun x => ((wD omega).toH1Function.grad x k) ^ 2)
        (openCubeSet (originCube d K)) volume := fun omega k =>
    integrableOn_openCubeSet_coord_sq_of_memLp_eight _ (hgrad omega) k
  have hsq : ∀ omega : Cutoff.ShellSeq d,
      IntegrableOn (fun x => vecNormSq ((wD omega).toH1Function.grad x))
        (openCubeSet (originCube d K)) volume := fun omega =>
    integrableOn_openCubeSet_vecNormSq_of_memLp_eight _ (hgrad omega)
  have hfour : ∀ omega : Cutoff.ShellSeq d,
      IntegrableOn (fun x => vecNormSq ((wD omega).toH1Function.grad x) ^ 2)
        (openCubeSet (originCube d K)) volume := fun omega =>
    integrableOn_openCubeSet_vecNormSq_sq_of_memLp_eight _ (hgrad omega)
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hgamma1 : M.gamma ≤ 1 := le_trans hq (by norm_num)
  obtain ⟨nbuf, hnbuf⟩ : ∃ n : ℤ,
      n = recurrenceMesoScale recurrenceGapMultiplier M.gamma m (h : ℤ) := ⟨_, rfl⟩
  obtain ⟨Ngap, hNgap⟩ : ∃ N : ℕ,
      N = recurrenceGap recurrenceGapMultiplier M.gamma := ⟨_, rfl⟩
  rw [← hnbuf]
  have hsum : nbuf + (Ngap : ℤ) = m - (h : ℤ) := by
    rw [hnbuf, hNgap]
    exact recurrenceMesoScale_add_recurrenceGap _ _ _ _
  have hsumR : ((nbuf : ℤ) : ℝ) + ((Ngap : ℕ) : ℝ) = (((m - (h : ℤ) : ℤ)) : ℝ) := by
    rw [hnbuf, hNgap]
    exact recurrenceMesoScale_add_recurrenceGap_real _ _ _ _
  have hmK : m ≤ K := by
    have hpos : (0 : ℝ) < (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ := by positivity
    have hle : (m : ℝ) ≤ (K : ℝ) := by linarith
    exact_mod_cast hle
  have hKone : (1 : ℝ) ≤ (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ := by
    have hinv : (1 : ℝ) ≤ M.gamma⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hgamma0]
      linarith
    have h10 : (1 : ℝ) ≤ (10 : ℝ) ^ (10 : ℕ) := by norm_num
    exact one_le_mul_of_one_le_of_one_le h10 hinv
  have hmK1 : m ≤ K - 1 := by
    have hle : (m : ℝ) + 1 ≤ (K : ℝ) := by linarith
    have : m + 1 ≤ K := by exact_mod_cast hle
    omega
  have hnNle : nbuf + (Ngap : ℤ) ≤ K - 1 := by omega
  have hnle : nbuf ≤ K - 1 := by omega
  have hdimN : d + 3 ≤ Ngap := by
    rw [hNgap]
    refine dim_add_three_le_recurrenceGap (a := recurrenceGapMultiplier) d hgamma0
      (by norm_num [recurrenceGapMultiplier]) ?_
    have hpow : (0 : ℝ) < (3 : ℝ) ^ ((d : ℝ) + 3) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : M.gamma ≤ ((3 : ℝ) ^ ((d : ℝ) + 3))⁻¹ := by
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
      exact hdimgate
    exact (le_inv_comm₀ hpow hgamma0).mpr h2
  have hlt : nbuf + (Ngap : ℤ) < m := by omega
  have hcellInt : ∀ R ∈ interiorMesoCubeGrid d K nbuf (nbuf + (Ngap : ℤ) - 1),
      Integrable (fun omega : Cutoff.ShellSeq d =>
        meshEnergyCell (nbuf + (Ngap : ℤ))
          (wD omega).toH1Function.grad R ^ (4 : ℝ)) M.P.toMeasure := by
    intro R hR
    exact hcell M hgcellle m0 Eind hstate m K h hhpos hm0 hcstar hK e e' he he' wD hsol
      hmem hcoord hsq hfour (nbuf + (Ngap : ℤ)) R
      (openCubeAtScale_subset_openCubeSet_of_mem_interiorMesoCubeGrid hR)
  obtain ⟨-, -, -, hDleg, -⟩ :=
    henv M hgenvle m0 Eind hstate m K h hhpos hm0 hcstar hK e e' he he'
  have henvD := hDleg nbuf Ngap hnle hnNle wD hsol hmem hcoord hsq hfour
  obtain ⟨Aenv, hAenv⟩ : ∃ A : ℝ,
      A = (3 : ℝ) ^ d * freshShellFourthEnergyConst Chead (M.gamma ^ (100 : ℕ)) := ⟨_, rfl⟩
  rw [← hAenv] at henvD
  have hAenv0 : 0 ≤ Aenv := by
    rw [hAenv]
    exact mul_nonneg (by positivity) (freshShellFourthEnergyConst_nonneg _ _)
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = Aenv ^ ((4 : ℝ)⁻¹) := ⟨_, rfl⟩
  have hgoal :=
    @localizationOscillationEndpointSixteen_comparisonBounds1 (d) (Cdisp) (hCdisp0) (hdisp)
      (Chead) (W0) (hW0) (Ctot) (hCtot) (hCtot0) (M) (m0) (Eind) (hstate) (m) (K) (h) (hhpos)
        (hm0) (hcstar) (e) (he) (z₀) (wD) (hsol) (hCgate) (hsq) (hgamma0) (hgamma1) (nbuf) (Ngap)
          (hNgap) (hsum) (hsumR) (hdimN) (hlt) (hcellInt) (Aenv) (henvD) (hAenv) (hAenv0) (W) (hW)
  rw [hsum] at hgoal
  exact hgoal

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
