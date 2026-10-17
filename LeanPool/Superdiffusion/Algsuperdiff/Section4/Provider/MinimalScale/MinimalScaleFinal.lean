/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.MinimalScale.ZCesaroLeg

/-!
# MinimalScaleFinal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
The outer constant is `2 · max (zTwoConst d) (zOneConst d)`: the `Z^{(2)}`
leg's `d`-only floor and the `Z^{(1)}` leg's, doubled so that each leg's tail
carries half the prefactor.

It does NOT import the anchor.
-/

open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.MinimalScale
open HCPolySupport MeasureTheory
open scoped ENNReal

/-- The frozen minimal-scale-separation statement, proved. -/
theorem Algsuperdiff.Section4.Provider.MinimalScale.minimal_scale_separation_provider
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s delta : ℝ),
        s ∈ Set.Ioc (0 : ℝ) (1 / 4) →
        delta ∈ Set.Ioc (0 : ℝ) (1 / 2) →
        M.gamma ≤
          (C⁻¹) ^ (10 : ℕ) *
            min (Disorder.cstar M ^ (10 : ℕ))
              (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ)) →
        8 * M.gamma ≤ s →
        ∀ m : ℤ, ∀ hs : 0 < s,
          ∃ Z : Cutoff.CutoffSample d → ℕ∞,
            Measurable Z ∧
            (∀ N : ℕ,
                (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ Z omega} ≤
                  ENNReal.ofReal
                    (C *
                      Real.exp
                        (-(((N : ℝ) - 1) * s ^ (9 : ℕ) *
                              Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ)) /
                          (C * M.gamma)))) ∧
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ n : ℤ, n ≤ m → Z omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
                (⨆ z : ↥(Algsuperdiff.Section4.Support.latticeCubeSet d (n - 1) m),
                    ((((m - n).toNat : ℝ≥0∞) + 1)⁻¹ *
                      ∑ k ∈ Finset.Icc n m,
                        Set.indicator
                          (Algsuperdiff.Frozen.Section4.goodEventAt M
                            (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) k
                            (Algsuperdiff.Section4.Support.triadicLatticePoint (n - 1) z)
                            ⟨s, hs⟩ (s * Real.sqrt delta))
                          (fun omega' =>
                            Algsuperdiff.Section4.Support.fluxCorrectedErrorObservableSup M k
                              ⟨s, hs⟩
                              (Cutoff.translateCutoffSample
                                (Algsuperdiff.Section4.Support.triadicLatticePoint (n - 1) z)
                                omega'))
                          omega)) ≤
                  ENNReal.ofReal delta ∧
                (⨆ z : ↥(Algsuperdiff.Section4.Support.latticeCubeSet d (n - 1) m),
                    ((((m - n).toNat : ℝ≥0∞) + 1)⁻¹ *
                      ∑ k ∈ Finset.Icc n m,
                        Set.indicator
                          ((Algsuperdiff.Frozen.Section4.goodEventAt M
                              (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) k
                              (Algsuperdiff.Section4.Support.triadicLatticePoint (n - 1) z)
                              ⟨s, hs⟩ (s * Real.sqrt delta))ᶜ)
                          (fun _ => (1 : ℝ≥0∞)) omega)) ≤
                  ENNReal.ofReal delta
    := by
  refine ⟨2 * max (zTwoConst d) (zOneConst d), ?_, ?_⟩
  · have h1 : (0 : ℝ) < zTwoConst d := zTwoConst_pos d
    have h2 : (0 : ℝ) < max (zTwoConst d) (zOneConst d) :=
      lt_of_lt_of_le h1 (le_max_left _ _)
    linarith only [h2]
  intro M s delta hsr hdr hgam hwin m hs
  have hCtwo : 2 * zTwoConst d ≤ 2 * max (zTwoConst d) (zOneConst d) := by
    have h := le_max_left (zTwoConst d) (zOneConst d)
    linarith only [h]
  have hCone : 2 * zOneConst d ≤ 2 * max (zTwoConst d) (zOneConst d) := by
    have h := le_max_right (zTwoConst d) (zOneConst d)
    linarith only [h]
  exact frozen_body_of_cesaro_tail (2 * max (zTwoConst d) (zOneConst d)) hCtwo M s delta
    hsr hdr hgam hwin m hs
    (fun N =>
      measure_tail_badCesaro_le_half (2 * max (zTwoConst d) (zOneConst d)) hCone M s delta
        hs hsr.2 hdr.1 hdr.2 hgam hwin m N)
