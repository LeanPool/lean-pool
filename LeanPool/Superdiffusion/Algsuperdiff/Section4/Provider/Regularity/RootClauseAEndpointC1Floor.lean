/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseAEndpointC1
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBFloorRecut

/-!
# RootClauseAEndpointC1Floor

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

/-! ## 1. The parametric clause-(B) lane in the `RootDisplayClauseBAe` slot -/

/-- **The parametric clause-(B) endpoint, restated in `RootDisplayClauseBAe`.**

`rootClauseB_display_offGrid_final_floor` with its `∀ n L, n ≤ m → m ≤ L →
payload → …` prefix reordered into the slot's `∀ n, n ≤ m → payload → ∀ L, m ≤
L → …`.  A pure binder move. -/
theorem clauseB_endpoint_as_clauseBAe_floor (d : ℕ) [NeZero d] (hd : d ≠ 0)
    (cstar Crg : ℝ) (hcstar : 0 < cstar) (hCrg : 0 < Crg) :
    ∃ (Cfl Citer Cest : ℝ) (k : ℕ),
      1 ≤ Cfl ∧ 0 ≤ Cest ∧ 11 ≤ k ∧
      ∀ Cedos : ℝ, Cfl ≤ Cedos →
        ∃ gamma0 : ℝ, 0 < gamma0 ∧
          ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
            ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - Crg * Real.sqrt M.gamma →
              RootDisplayClauseBAe M (stepOneC1 d Cedos 1 Citer k) Cest alpha := by
  obtain ⟨Cfl, Citer, Cest, k, h1, h2, h3, hmain⟩ :=
    rootClauseB_display_offGrid_final_floor d hd cstar Crg hcstar hCrg
  refine ⟨Cfl, Citer, Cest, k, h1, h2, h3, ?_⟩
  intro Cedos hfloor
  obtain ⟨gamma0, hgamma0, hbody⟩ := hmain Cedos hfloor
  refine ⟨gamma0, hgamma0, ?_⟩
  intro M hcs hg alpha ha0 ha m
  filter_upwards [hbody M hcs hg alpha ha0 ha m] with omega hom
  intro n hn hpay L hL u hdat g Kg Kh hdir hKg hKh x hx
  exact hom n L hn hL hpay u hdat g Kg Kh hdir hKg hKh x hx

/-! ## 2. The re-cut endpoint -/

/-- **`t.regularity` from clause (B) and the boundary clause (A).**

`anomalous_regularity_provider_of_boundaryClauseAC1` with the ONE named
conditional asked at its own parameters: the boundary producer receives
`(C_iter, k)`, answers with a `C_edos`-floor, and the endpoint runs both lanes
at the max of the two floors, at `C_annp = 1`.  Everything else — the minimal
scale, its measurability and tail, the `γ₀` min-merge, the `α`-range max-merge,
the off-grid transfer — is verbatim.

`hbdry` is a carried mathematical obligation, NOT a source premise: it is the
printed estimate itself at the centres `offGridCentre n x ∉ □_{m-1}`. -/
theorem anomalous_regularity_provider_of_boundaryClauseAC1Floor (d : ℕ) [NeZero d]
    (hd : d ≠ 0) (cstar Crg : ℝ) (hcstar : 0 < cstar) (hCrg : 0 < Crg)
    (hbdry : ∀ (Citer : ℝ) (k : ℕ), 11 ≤ k →
      ∃ CflA : ℝ, 1 ≤ CflA ∧
        ∀ Cedos : ℝ, CflA ≤ Cedos →
          ∃ CestA gamma0A CrgA : ℝ, 0 ≤ CestA ∧ 0 < gamma0A ∧ 0 < CrgA ∧
            ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0A →
              ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - CrgA * Real.sqrt M.gamma →
                RootDisplayClauseABoundaryC1Ae M
                  (stepOneC1 d Cedos 1 Citer k) CestA alpha) :
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
  obtain ⟨CflB, Citer, CestB, k, hCflB, hCestB, hk11, hBfl⟩ :=
    clauseB_endpoint_as_clauseBAe_floor d hd cstar Crg hcstar hCrg
  obtain ⟨CflA, hCflA, hAfl⟩ := hbdry Citer k hk11
  obtain ⟨gamma0B, hgamma0B, hB⟩ := hBfl (max CflB CflA) (le_max_left _ _)
  obtain ⟨CestA, gamma0A, CrgA, hCestA, hgamma0A, hCrgA, hA⟩ :=
    hAfl (max CflB CflA) (le_max_right _ _)
  obtain ⟨gamma0, C0, hg0pos, hC0pos, -, -, -, hpkg⟩ :=
    rootAssembly_aePackage d cstar hcstar (max CflB CflA) Citer 1 k hk11
  have hCest : (0 : ℝ) ≤ max CestB CestA := le_trans hCestB (le_max_left _ _)
  refine ⟨min gamma0 (min gamma0B gamma0A),
    max (max C0 ((3 : ℝ) ^ d * max CestB CestA)) (max Crg CrgA),
    lt_min hg0pos (lt_min hgamma0B hgamma0A),
    lt_of_lt_of_le hCrg (le_trans (le_max_left _ _) (le_max_right _ _)), ?_⟩
  intro M hcs hgamma alpha halpha0 halpha m
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hC0le : C0 ≤ max (max C0 ((3 : ℝ) ^ d * max CestB CestA)) (max Crg CrgA) :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hCestle : (3 : ℝ) ^ d * max CestB CestA ≤
      max (max C0 ((3 : ℝ) ^ d * max CestB CestA)) (max Crg CrgA) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have halphaC0 : alpha ≤ 1 - C0 * Real.sqrt M.gamma :=
    alphaRange_of_mono_const hC0le halpha
  have halphaB : alpha ≤ 1 - Crg * Real.sqrt M.gamma :=
    alphaRange_of_mono_const (le_trans (le_max_left _ _) (le_max_right _ _)) halpha
  have halphaA : alpha ≤ 1 - CrgA * Real.sqrt M.gamma :=
    alphaRange_of_mono_const (le_trans (le_max_right _ _) (le_max_right _ _)) halpha
  obtain ⟨Z, hXmeas, hXtail, hae⟩ :=
    hpkg M hcs (rootGamma0_le_left hgamma) alpha halpha0 halphaC0 m
  refine ⟨minimalScaleX Z k, hXmeas, ?_, ?_⟩
  · intro N
    exact le_trans (hXtail N)
      (minimalScaleTail_ofReal_mono_const hC0pos hC0le hgpos)
  have hBm := ((hB M hcs (rootGamma0_le_left (rootGamma0_le_right hgamma)) alpha halpha0
    halphaB).mono_const (le_max_left CestB CestA)) m
  have hAm := ((hA M hcs (rootGamma0_le_right (rootGamma0_le_right hgamma)) alpha halpha0
    halphaA).mono_const (le_max_right CestB CestA)) m
  filter_upwards [hae, hBm, hAm] with omega hpay hdispB hdispA
  intro L hL u h g Kg Kh hdir hKg hKh hsup hgradh x hx n hn hgate
  have hpayn := hpay n hn hgate
  have hclB := hdispB n hn hpayn L hL u h g Kg Kh hdir hKg hKh x hx
  have hclA : Real.sqrt M.nu *
        Support.normalizedL2On
          (truncatedWindow (offGridCentre n x) m (n + 1))
          (fun y => Real.sqrt (vecNormSq (u.grad y)))
      ≤ max CestB CestA *
          Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
        (Real.sqrt M.nu *
            Support.normalizedL2On (openCubeSet (originCube d m))
              (fun y => Real.sqrt (vecNormSq (u.grad y)))
          + Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
              Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg
          + Real.sqrt (Annealed.sigmaBar M m : ℝ) *
              Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) := by
    by_cases hin : offGridCentre n x ∈ openCubeSet (originCube d (m - 1))
    · have hbase := hclB hin
      have hKh0 : (0 : ℝ) ≤ Kh := holderHalf_const_nonneg hKh
      have h3 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) :=
        Real.rpow_nonneg (by norm_num) _
      have hHleg : (0 : ℝ) ≤ Real.sqrt (Annealed.sigmaBar M m : ℝ) *
          Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh :=
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) h3) hKh0
      have hcoef : (0 : ℝ) ≤
          max CestB CestA * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) :=
        mul_nonneg hCest (Real.rpow_nonneg (by norm_num) _)
      have hstep := mul_le_mul_of_nonneg_left
        (by linarith only [hHleg] :
          Real.sqrt M.nu *
                Support.normalizedL2On (openCubeSet (originCube d m))
                  (fun y => Real.sqrt (vecNormSq (u.grad y)))
              + Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg ≤
            Real.sqrt M.nu *
                Support.normalizedL2On (openCubeSet (originCube d m))
                  (fun y => Real.sqrt (vecNormSq (u.grad y)))
              + Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg
              + Real.sqrt (Annealed.sigmaBar M m : ℝ) *
                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) hcoef
      exact le_trans hbase hstep
    · exact hdispA n hn hpayn L hL u h g Kg Kh hdir hKg hKh hsup hgradh x hx hin
  have hpair := rootEnergyDensityPair_of_realDisplays M.nu
    (fun y => Real.sqrt (vecNormSq (u.grad y))) hx hn hCest
    (memLp_two_sqrt_vecNormSq_grad u) hclA hclB
  have hCle : ((3 : ℝ) ^ d * max CestB CestA) *
      Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) ≤
      max (max C0 ((3 : ℝ) ^ d * max CestB CestA)) (max Crg CrgA) *
        Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) :=
    mul_le_mul_of_nonneg_right hCestle
      (Real.rpow_pos_of_pos (by norm_num) _).le
  have hcoef : ENNReal.ofReal
        (((3 : ℝ) ^ d * max CestB CestA) *
          Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) ≤
      ENNReal.ofReal
        (max (max C0 ((3 : ℝ) ^ d * max CestB CestA)) (max Crg CrgA) *
          Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) :=
    ENNReal.ofReal_le_ofReal hCle
  refine ⟨le_trans hpair.1 (mul_le_mul' hcoef (le_refl _)), fun hxin => ?_⟩
  exact le_trans (hpair.2 hxin) (mul_le_mul' hcoef (le_refl _))

end

end Algsuperdiff.Section4.Provider.Regularity
