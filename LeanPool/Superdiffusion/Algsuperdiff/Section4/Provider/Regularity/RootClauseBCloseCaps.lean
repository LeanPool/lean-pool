/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBCloseSelection
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenLambdaGoodEvent
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenAeMerge

/-!
# RootClauseBCloseCaps

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## 1. The merged clause-(B) record -/

/-- **`ae_stepSevenLambdaCaps` with the scale AND the printed centre inside the
almost-everywhere quantifier.**

One null set serves every scale `k : ℤ` and every printed lattice centre
`Support.triadicLatticePoint n v`; the index set `ℤ × ℤ × (Fin d → ℤ)` is
countable, so this is Mathlib's `ae_all_iff` and nothing more. -/
theorem ae_stepSevenLambdaCaps_merged (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ delta : ℝ, delta ∈ Set.Ioc (0 : ℝ) (1 / 2) →
          8 * M.gamma ≤ stepOneSEighth →
          M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
              Real.rpow stepOneSEighth (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                stepOneEp delta →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ (k n : ℤ) (v : Fin d → ℤ),
                omega ∈ stepThreeGoodEvent M delta k
                    (Support.triadicLatticePoint n v) →
                  ∀ L : ℤ, k ≤ L →
                    StepSevenLambdaCaps (originCube d k)
                      (Support.fluxCorrectedCoeffFamily M L k (originCube d k)
                        (Cutoff.translateCutoffSample
                          (Support.triadicLatticePoint n v) omega))
                      ((Annealed.sigmaBar M k : ℝ))
                      (2 * (d : ℝ) * ((C * stepOneEp delta) ^ 2 + 1)) := by
  obtain ⟨C, hCpos, hC⟩ := ae_stepSevenLambdaCaps d
  refine ⟨C, hCpos, ?_⟩
  intro M hregime delta hdelta hfloor hsmall
  have hpair : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ p : ℤ × ℤ × (Fin d → ℤ), True →
        (omega ∈ stepThreeGoodEvent M delta p.1
            (Support.triadicLatticePoint p.2.1 p.2.2) →
          ∀ L : ℤ, p.1 ≤ L →
            StepSevenLambdaCaps (originCube d p.1)
              (Support.fluxCorrectedCoeffFamily M L p.1 (originCube d p.1)
                (Cutoff.translateCutoffSample
                  (Support.triadicLatticePoint p.2.1 p.2.2) omega))
              ((Annealed.sigmaBar M p.1 : ℝ))
              (2 * (d : ℝ) * ((C * stepOneEp delta) ^ 2 + 1))) :=
    ae_forall_of_forall_ae_of_countable
      (Q := fun _ : ℤ × ℤ × (Fin d → ℤ) => True)
      (fun p _ => hC M hregime delta hdelta hfloor hsmall p.1
        (Support.triadicLatticePoint p.2.1 p.2.2))
  exact hpair.mono fun omega h k n v => h (k, n, v) trivial

/-! ## 2. The clause-(B) record at BOTH selected scales -/

/-- **The two clause-(B) records the chain consumes, produced.**

`RootClauseBCloseSelection`'s joint pigeonhole selects the two good scales `j ≤
k` from the separation `|𝓑| + 7 ≤ m - n`; the merged record then supplies the clause-(B)
data at both.  The `caps` field of the payload sits at `□_k` (the chain's
coarse cube `□_{k_c+1}` at `k_c = k-1`) and `capsCacc` at `□_j` (the
Caccioppoli's cube `□_{n'+1}` at `n' = j-1`). -/
theorem exists_rootClauseBCapsPair {M : ABKModel d} {delta : ℝ} {n m L : ℤ}
    {omega : Cutoff.CutoffSample d} {CB : ℝ}
    (hmerge : ∀ (k n0 : ℤ) (v0 : Fin d → ℤ),
      omega ∈ stepThreeGoodEvent M delta k (Support.triadicLatticePoint n0 v0) →
        ∀ L' : ℤ, k ≤ L' →
          StepSevenLambdaCaps (originCube d k)
            (Support.fluxCorrectedCoeffFamily M L' k (originCube d k)
              (Cutoff.translateCutoffSample
                (Support.triadicLatticePoint n0 v0) omega))
            ((Annealed.sigmaBar M k : ℝ)) CB)
    (hbudget : StepThreeWindowsAndBudget M delta n m omega) {v : Fin d → ℤ}
    (hv : v ∈ Support.latticeCubeSet d n m) (hmL : m ≤ L) :
    ∃ j k : ℤ, n + 4 ≤ j ∧ j ≤ k ∧ k ≤ m - 1 ∧
      j - n ≤ ((stepThreeBadSet M delta n m
        (Support.triadicLatticePoint n v) omega).card : ℤ) + 4 ∧
      m - k ≤ ((stepThreeBadSet M delta n m
        (Support.triadicLatticePoint n v) omega).card : ℤ) + 1 ∧
      StepSevenLambdaCaps (originCube d j)
        (Support.fluxCorrectedCoeffFamily M L j (originCube d j)
          (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v) omega))
        ((Annealed.sigmaBar M j : ℝ)) CB ∧
      StepSevenLambdaCaps (originCube d k)
        (Support.fluxCorrectedCoeffFamily M L k (originCube d k)
          (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v) omega))
        ((Annealed.sigmaBar M k : ℝ)) CB := by
  obtain ⟨j, k, hjlo, hjk, hkhi, hgapLo, hgapHi, hgoodj, hgoodk⟩ :=
    exists_rootClauseBCapScales hbudget hv
  exact ⟨j, k, hjlo, hjk, hkhi, hgapLo, hgapHi,
    hmerge j n v hgoodj L (by omega), hmerge k n v hgoodk L (by omega)⟩

end

end Algsuperdiff.Section4.Provider.Regularity
