/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.SealPackaging
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.PrefDischarge

/-!
# AnnularFinal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.Annular
open HCPolySupport MeasureTheory
open scoped ENNReal

/-- The frozen annular-decomposition statement, proved. -/
theorem Algsuperdiff.Section4.Provider.Annular.annular_decomposition_provider
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d,
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ s : ℝ, s ∈ Set.Icc (8 * M.gamma) (1 / 4) → ∀ hs : 0 < s, ∀ m : ℤ,
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            (Set.indicator
                (Algsuperdiff.Section4.Support.eventG0 M
                    (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) m ∩
                  Algsuperdiff.Section4.Support.eventG1 M m s
                    (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
                (fun omega' =>
                  Algsuperdiff.Section4.Support.fluxCorrectedErrorObservableSqSup M m
                    ⟨s, hs⟩ omega')
                omega ≤
              ENNReal.ofReal (C * s) *
                  (∑' j : {j : ℤ // j ≤ m}, ∑' n : {n : ℤ // n ≤ j.1 - 1},
                    ENNReal.ofReal
                        (Real.rpow (3 : ℝ) (-s * ((m - n.1 : ℤ) : ℝ))) *
                      ⨆ v : ↥(Algsuperdiff.Section4.Support.latticeAnnulusSet d n.1 j.1
                          (j.1 - 1)),
                        ENNReal.ofReal
                          (Algsuperdiff.Section4.Support.annularErrorObservable M n.1
                              ⟨s, hs⟩
                              (Cutoff.translateCutoffSample
                                (Algsuperdiff.Section4.Support.triadicLatticePoint n.1 v.1)
                                omega) ^ 2)) +
                ENNReal.ofReal
                  (C * (s⁻¹ ^ (3 : ℕ)) * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ)) *
                    M.gamma ^ (2 : ℕ) * |Real.log M.gamma| ^ (4 : ℕ)) +
                ENNReal.ofReal (C * (s⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma) *
                  (∑' k : {k : ℤ // m ≤ k},
                    ENNReal.ofReal
                      (Real.rpow (3 : ℝ) ((2 - M.gamma) * (m : ℝ)) *
                        Algsuperdiff.Section4.Support.shellW1InfGradNorm m
                          (omega.1 k.1))) ^ (2 : ℕ) +
                ENNReal.ofReal (C * (s⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma) *
                  (∑' n : {n : ℤ // n ≤ m},
                    ENNReal.ofReal
                        (Real.rpow (3 : ℝ) (-(1 / 2 : ℝ) * s * ((m - n.1 : ℤ) : ℝ))) *
                      ∑ k ∈ Finset.Icc (n.1 - 1) m,
                        (ENNReal.ofReal
                              (Real.rpow (3 : ℝ) ((2 - M.gamma) * (k : ℝ))) *
                            ⨆ v : ↥(Algsuperdiff.Section4.Support.latticeCubeSet d k m),
                              ENNReal.ofReal
                                (Algsuperdiff.Section4.Support.shellW2InfNormAt
                                  (Algsuperdiff.Section4.Support.triadicLatticePoint k v.1)
                                  k (omega.1 k))) ^ (2 : ℕ))) ∧
              ∀ ep : ℝ, ep ∈ Set.Ioc (0 : ℝ) (1 / 2) →
                M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                  Real.rpow s (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * ep →
                Set.indicator
                    (Algsuperdiff.Frozen.Section4.goodEventAt M
                      (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) m 0 ⟨s, hs⟩ ep)
                    (fun omega' =>
                      Algsuperdiff.Section4.Support.fluxCorrectedErrorObservableSup M m
                        ⟨s, hs⟩ omega')
                    omega ≤
                  ENNReal.ofReal (C * ep)
    :=
  annular_decomposition_of_hpref d fun hd =>
    ⟨4, 1, by norm_num, one_pos, fun M _ m s hs14 _ omega hmem L hL =>
      annularDecompPre_slot_of_mem_annularEvent d hd M
        (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) m s hs14 omega hmem L hL⟩
