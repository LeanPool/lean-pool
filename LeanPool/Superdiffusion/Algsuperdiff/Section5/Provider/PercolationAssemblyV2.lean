/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.PercolationAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.SiteTailsV2
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section4.S5RegularityMomentBoundV2

/-!
# PercolationAssemblyV2

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Chains of good cubes at the successor logarithmic exponents

This module reruns the lattice-path assembly with the successor per-site tail.
The localized-error moment input is supplied internally, while the successor
localized-regularity moment estimate remains one explicit hypothesis.
A second theorem supplies that estimate from the Section 4 statement and so
states the assembly with no hypothesis beyond the model.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open HCPolySupport MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

def siteShiftedTailConstV2 (d : ℕ) (c : ℝ) : ℝ :=
  c / 2 *
    (3 : ℝ) ^ (-(sitePathExponent * (Provider.Percolation.sepShift d : ℝ)))

private theorem siteShiftedTailConstV2_pos (d : ℕ) {c : ℝ} (hc : 0 < c) :
    0 < siteShiftedTailConstV2 d c := by
  rw [siteShiftedTailConstV2]
  exact mul_pos (div_pos hc (by norm_num)) (Real.rpow_pos_of_pos (by norm_num) _)

private theorem siteTailRateSqV2_eq (d : ℕ) (M : ABKModel d) (c ep : ℝ) :
    siteTailRateSqV2 d M c ep =
      siteShiftedTailConstV2 d c * ep ^ 2 * M.gamma⁻¹ *
        |Real.log M.gamma| ^ (-6 : ℤ) := by
  rw [siteTailRateSqV2, siteBadRateSqV2, siteMarkovExponentV2,
    siteShiftedTailConstV2]
  ring

private theorem siteTailRateV2_sq (d : ℕ) (M : ABKModel d) {c ep : ℝ}
    (hc : 0 < c) (hep : 0 < ep) :
    siteTailRateV2 d M c ep ^ 2 = siteTailRateSqV2 d M c ep := by
  rw [siteTailRateV2]
  apply Real.sq_sqrt
  rw [siteTailRateSqV2, siteBadRateSqV2]
  exact mul_nonneg (div_nonneg (siteMarkovExponentV2_pos M hc hep).le (by norm_num))
    (Real.rpow_nonneg (by norm_num) _)

private theorem pathBoundRateV2_eq (d : ℕ) (M : ABKModel d) (c ep cpb : ℝ)
    (hc : 0 < c) (hep : 0 < ep) :
    cpb * (sitePathExponent - 1) ^ 2 * siteTailRateV2 d M c ep ^ 2 *
        (1 / 4 : ℝ) ^ 2 =
      cpb * siteShiftedTailConstV2 d c / 256 * ep ^ 2 * M.gamma⁻¹ *
        |Real.log M.gamma| ^ (-6 : ℤ) := by
  rw [siteTailRateV2_sq d M hc hep, siteTailRateSqV2_eq, sitePathExponent]
  ring

/-- The successor chains-of-good-cubes estimate, conditional only on the
successor localized-regularity moment bound. -/
theorem percolation_GF_v2_provider_of_hmomX
    (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar) (Cinj : ℝ) (hCinj : 0 < Cinj)
    (hmomX : ∃ gamma0 creg Creg : ℝ,
      0 < gamma0 ∧ 0 < creg ∧ 0 < Creg ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ (n : ℤ) (y : Vec d),
        (∫⁻ omega, localizedRegularity M n y omega ^
            (creg * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ))
            ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
          ENNReal.ofReal Creg ^
            (creg * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ))) :
    ∃ gamma0 c C Creg : ℝ, 0 < gamma0 ∧ 0 < c ∧ 0 < C ∧ 0 < Creg ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ ep : ℝ, ep ∈ Set.Icc (C * Real.sqrt M.gamma *
          Real.rpow |Real.log M.gamma| (7 / 2)) (1 / 4) →
      ∀ m : ℤ, ∃ Y : Cutoff.CutoffSample d → ℕ,
        Measurable Y ∧
        (∀ N : ℕ, 1 ≤ N →
          (Cutoff.cutoffSampleLaw M).toMeasure {omega | N ≤ Y omega} ≤
            ENNReal.ofReal (Real.exp (-(c * ep ^ (2 : ℕ) * M.gamma⁻¹ *
              |Real.log M.gamma| ^ (-6 : ℤ) * (3 : ℝ) ^ N)))) ∧
        ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ n : ℤ,
          n ≤ m - (Y omega : ℤ) →
          ∀ (N : ℕ) (x : ℕ → Fin d → ℤ),
            Provider.Percolation.IsLatticePath x N →
            x 0 ∈ Provider.Percolation.cubeAt (m - n).toNat 0 →
            x N ∉ Provider.Percolation.cubeAt ((m - n).toNat + 1) 0 →
            (3 / 4 : ℝ) * (3 : ℝ) ^ (m - n).toNat ≤
              ((qSiteCount M Creg Cinj n ep
                (Algsuperdiff.Section5.Percolation.pathSites N x) omega : ℕ) : ℝ) := by
  obtain ⟨gammaE, CE, hgammaE, hCE, hmomentE⟩ :=
    Algsuperdiff.Frozen.Section4.s5_error_moment_bound d cstar hcstar
  obtain ⟨gammaX, creg, Creg, hgammaX, hcreg, hCreg, hmomentX⟩ := hmomX
  obtain ⟨Cpb, hCpb, cpb, hcpb, hpath⟩ := Percolation.path_bound d
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let gamma0 := min gammaE gammaX
  let cSite := siteTailConstV2 CE creg Cinj
  let Cpath := max Cpb (Real.sqrt (2 * Real.log 2 / cpb))
  let C := siteEpsLowerConstV2 d cSite Cinj Cpath CE
  let c := cpb * siteShiftedTailConstV2 d cSite / 1536
  have hgamma0 : 0 < gamma0 := lt_min hgammaE hgammaX
  have hcSite : 0 < cSite := siteTailConstV2_pos hCE hcreg hCinj
  have hCpath0 : 0 ≤ Cpath := hCpb.le.trans (le_max_left _ _)
  have hC : 0 < C := siteEpsLowerConstV2_pos d hCinj hCE.le
  have hc : 0 < c :=
    div_pos (mul_pos hcpb (siteShiftedTailConstV2_pos d hcSite)) (by norm_num)
  have hCpbLe : Cpb ≤ Cpath := le_max_left _ _
  have hCpathSq : 2 * Real.log 2 / cpb ≤ Cpath ^ 2 := by
    have hnonneg : 0 ≤ 2 * Real.log 2 / cpb :=
      (div_pos (mul_pos (by norm_num) hlog2) hcpb).le
    calc
      2 * Real.log 2 / cpb = Real.sqrt (2 * Real.log 2 / cpb) ^ 2 :=
        (Real.sq_sqrt hnonneg).symm
      _ ≤ Cpath ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2
  refine ⟨gamma0, c, C, Creg, hgamma0, hc, hC, hCreg, ?_⟩
  intro M hcstarM hgammaM ep hep m
  have hmomentEM := hmomentE M hcstarM (hgammaM.trans (min_le_left _ _))
  have hmomentXM := hmomentX M hcstarM (hgammaM.trans (min_le_right _ _))
  have hepPos : 0 < ep := pos_of_epsLowerV2 M hCinj hCE.le hep.1
  have hd2 : 2 ≤ d := M.shellPrefix.dimension
  have hgate : Cpb * (1 / 4 : ℝ)⁻¹ * (sitePathExponent - 1)⁻¹ ≤
      siteTailRateV2 d M cSite ep := by
    have hg := pathBoundGate_le_siteTailRateV2_of_epsLower M hcSite hCinj hCpath0
      hCE.le hep.1
    have hinv : (sitePathExponent - 1 : ℝ)⁻¹ = 4 := by
      rw [sitePathExponent]
      norm_num
    have hfour : ((1 : ℝ) / 4)⁻¹ = 4 := by norm_num
    rw [hinv, hfour] at hg ⊢
    linarith only [hg, hCpbLe]
  have hAgate : 2 * Real.log 2 ≤ cpb * (sitePathExponent - 1) ^ 2 *
      siteTailRateV2 d M cSite ep ^ 2 * (1 / 4 : ℝ) ^ 2 := by
    have hTsq := gateBracket_le_siteTailRateSqV2_of_epsLower M hcSite hCinj hCE.le hep.1
    have hT2 := siteTailRateV2_sq d M hcSite hepPos
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hbig : 256 * Cpath ^ 2 ≤ siteTailRateV2 d M cSite ep ^ 2 := by
      rw [hT2]
      have hexpand : (16 * Cpath) ^ 2 = 256 * Cpath ^ 2 := by ring
      rw [← hexpand]
      linarith only [hTsq, hlog3]
    have hprod : cpb * (256 * Cpath ^ 2) ≤
        cpb * siteTailRateV2 d M cSite ep ^ 2 :=
      mul_le_mul_of_nonneg_left hbig hcpb.le
    have hlow : 2 * Real.log 2 ≤ cpb * Cpath ^ 2 := by
      rw [div_le_iff₀ hcpb] at hCpathSq
      simpa only [mul_comm] using hCpathSq
    have hsq : (sitePathExponent - 1 : ℝ) ^ 2 = 1 / 16 := by
      rw [sitePathExponent]
      norm_num
    rw [hsq]
    have hshape : cpb * (1 / 16 : ℝ) * siteTailRateV2 d M cSite ep ^ 2 *
        (1 / 4 : ℝ) ^ 2 = cpb * siteTailRateV2 d M cSite ep ^ 2 / 256 := by ring
    rw [hshape]
    linarith only [hprod, hlow]
  have hkey : ∀ k : ℕ, (Cutoff.cutoffSampleLaw M).toMeasure
      (lightQPathEvent M Creg Cinj m ep k) ≤
      ENNReal.ofReal (Real.exp (-(cpb * (sitePathExponent - 1) ^ 2 *
        siteTailRateV2 d M cSite ep ^ 2 * (1 / 4 : ℝ) ^ 2 * 3 ^ k))) := by
    intro k
    have hp := hpath (Cutoff.cutoffSampleLaw M).toMeasure
      (shiftedSiteBadEventFive M Creg (siteThresholdConst Cinj) ep (m - (k : ℤ)))
      sitePathExponent (siteTailRateV2 d M cSite ep) (1 / 4) k
      (fun L z => measurableSet_shiftedSiteBadEventFive M Creg
        (siteThresholdConst Cinj) ep (m - (k : ℤ)) L z)
      (sepIndep_shiftedSiteBadEventFive M Creg (siteThresholdConst Cinj) ep
        (m - (k : ℤ)))
      (fun L z => measureReal_shiftedSiteBadEventFive_le_of_epsLower_v2 M hcSite hCE
        hcreg hCreg hCinj (siteTailConstV2_le_error CE creg Cinj)
        (siteTailConstV2_le_range CE creg Cinj)
        (siteTailConstV2_le_regularity CE creg Cinj)
        (siteTailConstV2_le_shell CE creg Cinj) hmomentEM hmomentXM hep
        (m - (k : ℤ)) L z)
      one_lt_sitePathExponent (sitePathExponent_le_dim hd2)
      (one_le_siteTailRateV2_of_epsLower M hcSite hCinj hCE.le hep.1)
      (by norm_num) (by norm_num) hgate
    have hsub := lightQPathEvent_subset M (Creg := Creg) (Cinj := Cinj)
      (C0 := siteThresholdConst Cinj) m k
      (siteThresholdConst_pos hCinj).le hepPos.le
      (le_of_eq (siteThresholdConst_mul_geometric Cinj))
    refine (measure_mono hsub).trans ?_
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
      (Real.exp_pos _).le).2 hp
  have hArw : cpb * (sitePathExponent - 1) ^ 2 * siteTailRateV2 d M cSite ep ^ 2 *
      (1 / 4 : ℝ) ^ 2 =
      cpb * siteShiftedTailConstV2 d cSite / 256 * ep ^ 2 * M.gamma⁻¹ *
        |Real.log M.gamma| ^ (-6 : ℤ) :=
    pathBoundRateV2_eq d M cSite ep cpb hcSite hepPos
  rw [hArw] at hkey hAgate
  have hApos : 0 < cpb * siteShiftedTailConstV2 d cSite / 256 * ep ^ 2 *
      M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) := by
    linarith only [hAgate, hlog2]
  refine ⟨percolationScaleTotal M Creg Cinj m ep,
    measurable_percolationScaleTotal_of_model M Creg Cinj m ep, ?_, ?_⟩
  · intro N hN
    refine (measure_le_percolationScaleTotal_le M Creg Cinj m ep hAgate hkey hN).trans ?_
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    congr 1
    dsimp only [c]
    ring
  · exact percolationScaleTotal_ae_crossing M Creg Cinj m ep
      (ae_mem_eventuallyHeavyPaths M Creg Cinj m ep hApos hkey)

/-- The successor chains-of-good-cubes estimate, with the successor
localized-regularity moment bound supplied. -/
theorem percolation_GF_v2_provider
    (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar) (Cinj : ℝ) (hCinj : 0 < Cinj) :
    ∃ gamma0 c C Creg : ℝ, 0 < gamma0 ∧ 0 < c ∧ 0 < C ∧ 0 < Creg ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ ep : ℝ, ep ∈ Set.Icc (C * Real.sqrt M.gamma *
          Real.rpow |Real.log M.gamma| (7 / 2)) (1 / 4) →
      ∀ m : ℤ, ∃ Y : Cutoff.CutoffSample d → ℕ,
        Measurable Y ∧
        (∀ N : ℕ, 1 ≤ N →
          (Cutoff.cutoffSampleLaw M).toMeasure {omega | N ≤ Y omega} ≤
            ENNReal.ofReal (Real.exp (-(c * ep ^ (2 : ℕ) * M.gamma⁻¹ *
              |Real.log M.gamma| ^ (-6 : ℤ) * (3 : ℝ) ^ N)))) ∧
        ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ n : ℤ,
          n ≤ m - (Y omega : ℤ) →
          ∀ (N : ℕ) (x : ℕ → Fin d → ℤ),
            Provider.Percolation.IsLatticePath x N →
            x 0 ∈ Provider.Percolation.cubeAt (m - n).toNat 0 →
            x N ∉ Provider.Percolation.cubeAt ((m - n).toNat + 1) 0 →
            (3 / 4 : ℝ) * (3 : ℝ) ^ (m - n).toNat ≤
              ((qSiteCount M Creg Cinj n ep
                (Algsuperdiff.Section5.Percolation.pathSites N x) omega : ℕ) : ℝ) :=
  percolation_GF_v2_provider_of_hmomX d cstar hcstar Cinj hCinj
    (Algsuperdiff.Frozen.Section4.s5_regularity_moment_bound_v2 d cstar hcstar)

end

end Algsuperdiff.Section5.Provider
