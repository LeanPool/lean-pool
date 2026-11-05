/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBWellPlacedFloor
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseABoundaryShellEndpoint

/-!
# RootClauseBWellPlacedEndpoint

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The obligation shape -/

theorem exists_rootDisplayClauseABoundaryC1Ae_wellPlaced (d : ℕ) [NeZero d]
    (hd : d ≠ 0) (cstar Crg : ℝ) (hcstar : 0 < cstar) (hCrg : 0 < Crg) :
    ∃ (Cfl Citer : ℝ) (k : ℕ), 1 ≤ Cfl ∧ 11 ≤ k ∧
      ∀ Cedos : ℝ, Cfl ≤ Cedos →
        ∃ Cest gamma0 : ℝ, 0 ≤ Cest ∧ 0 < gamma0 ∧
          ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
            ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - Crg * Real.sqrt M.gamma →
              RootDisplayClauseABoundaryC1Ae M
                (stepOneC1 d Cedos 1 Citer k) Cest alpha := by
  obtain ⟨Cfl, Citer, Cest, k, hCfl, hCest, hk11, hmain⟩ :=
    rootClauseB_display_wellPlaced_final_floor d hd cstar Crg hcstar hCrg
  refine ⟨Cfl, Citer, k, hCfl, hk11, ?_⟩
  intro Cedos hfloor
  obtain ⟨gamma0, hgamma0, hbody⟩ := hmain Cedos hfloor
  refine ⟨Cest, gamma0, hCest, hgamma0, ?_⟩
  intro M hcs hg alpha ha0 ha m
  filter_upwards [hbody M hcs hg alpha ha0 ha m] with omega hom
  intro n hn hpay L hL u h g Kg Kh hdir hKg hKh hsup hgradh x hx _hout
  exact hom n L hn hL hpay u h g Kg Kh hdir hKg hKh hsup hgradh x hx

/-! ## 2. The endpoint, with no named conditional -/

theorem anomalous_regularity_provider_wellPlaced (d : ℕ) [NeZero d]
    (hd : d ≠ 0) (cstar Crg : ℝ) (hcstar : 0 < cstar) (hCrg : 0 < Crg) :
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
                ∀ (u h : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d) (Kg Kh : ℝ),
                  Support.IsDirichletSolutionOn
                      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (originCube d m) u h g →
                  Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
                      (1 / 2) Kg g →
                  Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
                      (1 / 2) Kh h.grad →
                  (∀ y ∈ openCubeSet (originCube d m),
                    ‖h.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) →
                  Support.HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
                  ∀ x : Vec d, x ∈ openCubeSet (originCube d m) →
                    ∀ n : ℤ, n ≤ m → X omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
                      (ENNReal.ofReal (Real.sqrt M.nu) *
                          eLpNorm
                            (fun y => Real.sqrt (vecNormSq (u.grad y))) 2
                            (Support.normalizedVolumeMeasureOn
                              (((fun y => x + y) '' openCubeSet (originCube d n)) ∩
                                openCubeSet (originCube d m))) ≤
                        ENNReal.ofReal
                            (C * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
                          (ENNReal.ofReal (Real.sqrt M.nu) *
                              eLpNorm
                                (fun y => Real.sqrt (vecNormSq (u.grad y))) 2
                                (Support.normalizedVolumeMeasureOn
                                  (openCubeSet (originCube d m))) +
                            ENNReal.ofReal
                              (Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg) +
                            ENNReal.ofReal
                              (Real.sqrt (Annealed.sigmaBar M m : ℝ) *
                                Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))) ∧
                      (x ∈ openCubeSet (originCube d (m - 1)) →
                        ENNReal.ofReal (Real.sqrt M.nu) *
                            eLpNorm
                              (fun y => Real.sqrt (vecNormSq (u.grad y))) 2
                              (Support.normalizedVolumeMeasureOn
                                (((fun y => x + y) '' openCubeSet (originCube d n)) ∩
                                  openCubeSet (originCube d m))) ≤
                          ENNReal.ofReal
                              (C *
                                Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
                            (ENNReal.ofReal (Real.sqrt M.nu) *
                                eLpNorm
                                  (fun y => Real.sqrt (vecNormSq (u.grad y))) 2
                                  (Support.normalizedVolumeMeasureOn
                                    (openCubeSet (originCube d m))) +
                              ENNReal.ofReal
                                (Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                                    Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg))) := by
  refine anomalous_regularity_provider_of_boundaryClauseAC1Floor d hd cstar Crg hcstar
    hCrg ?_
  intro Citer k _hk11
  obtain ⟨CflW, CiterW, kW, hCflW, hkW11, hprod⟩ :=
    exists_rootDisplayClauseABoundaryC1Ae_wellPlaced d hd cstar Crg hcstar hCrg
  refine ⟨max 1 (max (4 * CiterW * ((kW : ℝ) + 1) / Real.log 3)
      (stepOneC1Delta0 CflW 1 kW)), le_max_left _ _, ?_⟩
  intro Cedos hfloor
  have hCedos1 : (1 : ℝ) ≤ Cedos := le_trans (le_max_left _ _) hfloor
  have hbase : max 2 (2 * (d : ℝ) + 2) ≤ stepOneC1 d Cedos 1 Citer k := by
    rw [stepOneC1]
    exact le_max_left _ _
  have hiter : 4 * CiterW * ((kW : ℝ) + 1) / Real.log 3 ≤
      stepOneC1 d Cedos 1 Citer k :=
    le_stepOneC1_of_le_cedos d hCedos1
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hfloor) Citer k
  have hdelta0 : stepOneC1Delta0 CflW 1 kW ≤ stepOneC1 d Cedos 1 Citer k :=
    le_stepOneC1_of_le_cedos d hCedos1
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hfloor) Citer k
  obtain ⟨CedosW, hCedosW, hEq⟩ :=
    exists_cedos_stepOneC1_eq d CiterW kW hCflW hbase hiter hdelta0
  obtain ⟨CestW, gamma0W, hCestW, hgamma0W, hbody⟩ := hprod CedosW hCedosW
  refine ⟨CestW, gamma0W, Crg, hCestW, hgamma0W, hCrg, ?_⟩
  intro M hcs hg alpha ha0 ha
  have h := hbody M hcs hg alpha ha0 ha
  rw [hEq] at h
  exact h

end

end Algsuperdiff.Section4.Provider.Regularity
