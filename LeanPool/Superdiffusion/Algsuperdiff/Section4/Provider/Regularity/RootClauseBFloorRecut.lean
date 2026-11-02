/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBFinalAssembly

/-!
# RootClauseBFloorRecut

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. `C₁` is monotone in `C_edos` -/

theorem stepOneC1Delta0_mono_cedos {Cedos Cedos' Cann : ℝ} (hCedos : 0 < Cedos)
    (hCann : 0 < Cann) (hle : Cedos ≤ Cedos') (k : ℕ) :
    stepOneC1Delta0 Cedos Cann k ≤ stepOneC1Delta0 Cedos' Cann k := by
  have hCedos' : (0 : ℝ) < Cedos' := lt_of_lt_of_le hCedos hle
  have hT : (0 : ℝ) < stepOneThreePow k := stepOneThreePow_pos k
  have hs : (0 : ℝ) < stepOneS := by rw [stepOneS]; norm_num
  have hbase : (0 : ℝ) ≤ 2 * Cedos * Cann * stepOneThreePow k :=
    mul_nonneg (mul_nonneg (by linarith only [hCedos]) hCann.le) hT.le
  have hstep : 2 * Cedos * Cann * stepOneThreePow k ≤
      2 * Cedos' * Cann * stepOneThreePow k := by
    have h1 : 2 * Cedos * Cann ≤ 2 * Cedos' * Cann :=
      mul_le_mul_of_nonneg_right (by linarith only [hle]) hCann.le
    exact mul_le_mul_of_nonneg_right h1 hT.le
  have hnum : (2 * Cedos * Cann * stepOneThreePow k) ^ (2 : ℕ) ≤
      (2 * Cedos' * Cann * stepOneThreePow k) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hbase hstep 2
  rw [stepOneC1Delta0_eq hCedos hCann k, stepOneC1Delta0_eq hCedos' hCann k]
  exact div_le_div_of_nonneg_right hnum hs.le

theorem stepOneC1_mono_cedos (d : ℕ) {Cedos Cedos' Cann : ℝ} (hCedos : 0 < Cedos)
    (hCann : 0 < Cann) (hle : Cedos ≤ Cedos') (Citer : ℝ) (k : ℕ) :
    stepOneC1 d Cedos Cann Citer k ≤ stepOneC1 d Cedos' Cann Citer k := by
  rw [stepOneC1, stepOneC1]
  exact max_le_max (le_refl _)
    (max_le_max (le_refl _) (stepOneC1Delta0_mono_cedos hCedos hCann hle k))

/-- **Every floor is cleared by a large enough `C_edos`.**

`C₁ ≥ stepOne C_edos 1 k = 16 C_edos² 3^{k/2} ≥ C_edos` for `C_edos ≥ 1`.  This
is the shape a boundary producer needs: it may answer with a floor on `C_edos`
alone and never mention `C₁`. -/
theorem le_stepOneC1_of_le_cedos (d : ℕ) {F Cedos : ℝ} (h1 : 1 ≤ Cedos) (hF : F ≤ Cedos)
    (Citer : ℝ) (k : ℕ) : F ≤ stepOneC1 d Cedos 1 Citer k := by
  have hCedos : (0 : ℝ) < Cedos := lt_of_lt_of_le (by norm_num) h1
  have hT : (1 : ℝ) ≤ stepOneThreePow k := by
    rw [stepOneThreePow]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hslot : stepOneC1Delta0 Cedos 1 k ≤ stepOneC1 d Cedos 1 Citer k :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have heq : stepOneC1Delta0 Cedos 1 k =
      (2 * Cedos * 1 * stepOneThreePow k) ^ (2 : ℕ) / stepOneS :=
    stepOneC1Delta0_eq hCedos one_pos k
  have hbig : Cedos ≤ (2 * Cedos * 1 * stepOneThreePow k) ^ (2 : ℕ) / stepOneS := by
    have hb : 2 * Cedos ≤ 2 * Cedos * 1 * stepOneThreePow k := by
      have h2 : (0 : ℝ) ≤ 2 * Cedos := by linarith only [hCedos]
      have hstep := mul_le_mul_of_nonneg_left hT h2
      rw [mul_one] at hstep
      calc 2 * Cedos ≤ 2 * Cedos * stepOneThreePow k := hstep
        _ = 2 * Cedos * 1 * stepOneThreePow k := by ring
    have hsq : (2 * Cedos) ^ (2 : ℕ) ≤ (2 * Cedos * 1 * stepOneThreePow k) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by linarith only [hCedos]) hb 2
    have hlow : Cedos ≤ (2 * Cedos) ^ (2 : ℕ) := by
      have hexp : (2 * Cedos) ^ (2 : ℕ) = 4 * Cedos * Cedos := by ring
      rw [hexp]
      have hsq' := mul_le_mul_of_nonneg_left h1 hCedos.le
      rw [mul_one] at hsq'
      linarith only [hsq', h1]
    have hs : stepOneS = 1 / 4 := by rw [stepOneS]
    rw [hs]
    have hdiv : (2 * Cedos * 1 * stepOneThreePow k) ^ (2 : ℕ) / (1 / 4 : ℝ) =
        4 * (2 * Cedos * 1 * stepOneThreePow k) ^ (2 : ℕ) := by ring
    rw [hdiv]
    have hnn : (0 : ℝ) ≤ (2 * Cedos * 1 * stepOneThreePow k) ^ (2 : ℕ) := sq_nonneg _
    linarith only [hlow, hsq, hnn]
  rw [heq] at hslot
  linarith only [hF, hbig, hslot]

/-! ## 2. `hosc` with `C_edos` free above the lane's own floor -/

/-- **'s `exists_rootClauseBOsc`, parametric above its `C_edos` floor.**

Character for character `RootClauseBFinalOsc.exists_rootClauseBOsc`, with the
pinned letter `rootClauseBFundCedos d k` replaced by a `C_edos` above it.  The
only proof change: the Step-6 funding gate is obtained from the pinned floor
and `stepOneC1_mono_cedos`. -/
theorem exists_rootClauseBOsc_floor (d : ℕ) [NeZero d] (hd : d ≠ 0) :
    ∃ (C Cann Citer Cosc Cdel : ℝ) (k : ℕ),
      0 < C ∧ 0 < Cann ∧ 0 ≤ Cosc ∧ 0 ≤ Cdel ∧ 11 ≤ k ∧
      ∀ Cedos : ℝ, rootClauseBFundCedos d C Cann k ≤ Cedos →
      ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap →
        M.gamma < 1 / 2 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma ≤ Cann⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma ≤ 1 / 256 →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (stepOneS / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
              (C⁻¹ * stepOneS ^ (4 : ℕ)) →
        ∀ alpha : ℝ, 0 < alpha → alpha < 1 →
          M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
              Real.rpow stepOneSEighth (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                stepOneEp (stepOneDelta (stepOneC1 d Cedos 1 Citer k) alpha) →
          ∀ m : ℤ, m ≤ m0 →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ (L n : ℤ) (v : Fin d → ℤ), m ≤ L → (14 : ℤ) ≤ m - n →
                v ∈ Support.latticeCubeSet d n m →
                Support.triadicLatticePoint n v ∈
                    openCubeSet (originCube d (m - 1)) →
                  RootWindowPayload M (stepOneC1 d Cedos 1 Citer k) alpha n m omega →
                    ∀ (uglob hdat : H1Function (openCubeSet (originCube d m)))
                      (gsrc : Vec d → Vec d) (Khol Kh : ℝ), 0 ≤ Khol → 0 ≤ Kh →
                      IsDirichletSolutionOn
                          (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                          (originCube d m) uglob hdat gsrc →
                      HolderSeminormBoundOn (openCubeSet (originCube d m))
                          (1 / 2) Khol gsrc →
                      HolderSeminormBoundOn (openCubeSet (originCube d m))
                          (1 / 2) Kh hdat.grad →
                      ∀ n' kc : ℤ, n ≤ n' → n' ≤ kc → kc ≤ m →
                        (3 : ℝ) ^ (-n') *
                            normalizedL2On
                              (truncatedWindow (Support.triadicLatticePoint n v) m n')
                              (fun y => uglob.toFun y -
                                volumeAverage
                                  (truncatedWindow
                                    (Support.triadicLatticePoint n v) m n')
                                  uglob.toFun) ≤
                          Cosc *
                              Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
                              ((3 : ℝ) ^ (-kc) *
                                normalizedL2On
                                  (truncatedWindow
                                    (Support.triadicLatticePoint n v) m kc)
                                  (fun y => uglob.toFun y -
                                    volumeAverage
                                      (truncatedWindow
                                        (Support.triadicLatticePoint n v) m kc)
                                      uglob.toFun)) +
                            Cosc *
                              Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
                              (edFinalDataG M Cdel
                                (Khol * stepFourGagliardoConst d stepOneS) m + 0) := by
  classical
  obtain ⟨C, Cann, hC, hCann, k0, hk0, hres⟩ :=
    edFinal_oscillationHolderBound_interior d hd
  have hk0k : k0 ≤ max k0 11 := le_max_left _ _
  have hk11 : 11 ≤ max k0 11 := le_max_right _ _
  have hk2 : 2 ≤ max k0 11 := le_trans (by norm_num) hk11
  obtain ⟨Cout, Citer, hCout, hCiter, hres'⟩ := hres (max k0 11) hk0k hk2
  have hs0 : (0 : ℝ) < stepOneS := by rw [stepOneS]; norm_num
  have hs2 : stepOneS < 1 / 2 := by rw [stepOneS]; norm_num
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hCoutSq : (0 : ℝ) ≤ Cout * Cout := mul_nonneg hCout.le hCout.le
  refine ⟨C, Cann, Citer, Cout + Cout * Cout,
    edFinalDeltaConst d C (max k0 11) stepOneS, max k0 11, hC, hCann,
    by linarith only [hCout, hCoutSq], edFinalDeltaConst_nonneg d hC.le _ hs0.le,
    hk11, ?_⟩
  intro Cedos hfloor M m0 Ecap hS hgamma hregC hregAnn hg256 hfree alpha halpha0
    halpha1 hsmall m hmm0
  have hCedosPos : (0 : ℝ) < Cedos :=
    lt_of_lt_of_le (rootClauseBFundCedos_pos d C Cann (max k0 11)) hfloor
  have hC1two : (2 : ℝ) ≤ stepOneC1 d Cedos 1 Citer (max k0 11) :=
    two_le_stepOneC1 d _ _ _ _
  have hC1pos : (0 : ℝ) < stepOneC1 d Cedos 1 Citer (max k0 11) := by
    linarith only [hC1two]
  have hdeltamem := stepOneDelta_mem hC1two halpha0 halpha1
  have hgate := edFunding_of_c1_floor d hC.le hCann.le halpha0.le hC1pos
    (le_trans (rootClauseBFundFloor_le_stepOneC1 d hC.le hCann.le Citer (max k0 11))
      (stepOneC1_mono_cedos d (rootClauseBFundCedos_pos d C Cann (max k0 11)) one_pos
        hfloor Citer (max k0 11)))
  have hmerge := ae_forall_of_forall_ae_of_countable
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    (Q := fun p : ℤ × ℤ × (Fin d → ℤ) =>
      m ≤ p.1 ∧ (14 : ℤ) ≤ m - p.2.1 ∧
        p.2.2 ∈ Support.latticeCubeSet d p.2.1 m ∧
        Support.triadicLatticePoint p.2.1 p.2.2 ∈
          openCubeSet (originCube d (m - 1)))
    (fun p hp => hres' M m0 Ecap hS hgamma hregC hregAnn hg256 hfree
      Cedos 1 alpha (le_of_lt halpha1)
      hdeltamem hsmall hgate p.1 m p.2.1 hp.1 hmm0 hp.2.1 p.2.2 hp.2.2.1 hp.2.2.2)
  filter_upwards [hmerge] with omega hom
  intro L n v hL hwin hv hzin hpay uglob hdat gsrc Khol Kh hKhol hKh hsol hgHol hhHol
    n' kc hn' hn'kc hkc
  have hnm : n ≤ m := by omega
  have hbudget := (hpay.2.2.1 v hv).2.2.1
  rw [toNat_sub_cast_real hnm] at hbudget
  obtain ⟨hgL2, hgW⟩ := memLp_pair_of_holderHalf hd1 hKhol hgHol
  have hhW := memLp_two_gagliardoKernel_of_holderHalf hd1 hs0 hs2 hKh hhHol
  obtain ⟨cfam, slope, hmin⟩ :=
    exists_stepThreeWindow_affineMinimizerFamily
      (mem_openCubeSet_of_mem_latticeCubeSet hv) uglob
  exact hom (L, n, v) ⟨hL, hwin, hv, hzin⟩ hpay.1 hbudget uglob hdat gsrc Khol hKhol
    hsol hgL2 hgW hhW hgHol cfam slope hmin n' kc hn' hn'kc hkc

/-! ## 3. Clause (B) with `C_edos` free above the lane's own floor -/

/-- **'s clause-(B) endpoint, parametric above its `C_edos` floor.** -/
theorem rootClauseB_display_offGrid_final_floor (d : ℕ) [NeZero d] (hd : d ≠ 0)
    (cstar Crg : ℝ) (hcstar : 0 < cstar) (hCrg : 0 < Crg) :
    ∃ (Cfl Citer Cest : ℝ) (k : ℕ),
      1 ≤ Cfl ∧ 0 ≤ Cest ∧ 11 ≤ k ∧
      ∀ Cedos : ℝ, Cfl ≤ Cedos →
        ∃ gamma0 : ℝ, 0 < gamma0 ∧
          ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
            ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - Crg * Real.sqrt M.gamma →
              ∀ m : ℤ,
                ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                  ∀ n L : ℤ, n ≤ m → m ≤ L →
                    RootWindowPayload M (stepOneC1 d Cedos 1 Citer k) alpha n m omega →
                      ∀ (u h : H1Function (openCubeSet (originCube d m)))
                        (g : Vec d → Vec d) (Kg Kh : ℝ),
                        Support.IsDirichletSolutionOn
                            (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                            (originCube d m) u h g →
                        Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
                            (1 / 2) Kg g →
                        Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
                            (1 / 2) Kh h.grad →
                        ∀ x : Vec d, x ∈ openCubeSet (originCube d m) →
                          (offGridCentre n x ∈ openCubeSet (originCube d (m - 1)) →
                            Real.sqrt M.nu *
                                Support.normalizedL2On
                                  (truncatedWindow (offGridCentre n x) m (n + 1))
                                  (fun y => Real.sqrt (vecNormSq (u.grad y)))
                              ≤ Cest *
                                  Real.rpow (3 : ℝ)
                                    ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
                                (Real.sqrt M.nu *
                                    Support.normalizedL2On
                                      (openCubeSet (originCube d m))
                                      (fun y => Real.sqrt (vecNormSq (u.grad y))) +
                                  Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                                    Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg)) := by
  classical
  obtain ⟨C, Cann, Citer, Cosc, Cdel, k, hC, hCann, hCosc, hCdel, hk11, hoscprod⟩ :=
    exists_rootClauseBOsc_floor d hd
  obtain ⟨Ccaps, hCcaps, hcapsprod⟩ := ae_stepSevenLambdaCaps_merged d
  obtain ⟨Cind, hCind6, -, hind⟩ :=
    Algsuperdiff.Section4.Provider.GoodEvents.exists_allScalesInductionState_ge d 0
  obtain ⟨Cch, Cc, hCch, hCc, hend⟩ := rootClauseB_display_offGrid_of_windowPayload d
  have hCindpos : (0 : ℝ) < Cind := by linarith only [hCind6]
  have hCmax : (0 : ℝ) < max C Ccaps := lt_of_lt_of_le hC (le_max_left _ _)
  set CBu : ℝ := rootClauseBCapsUniform d Ccaps with hCBuDef
  have hCBu : (0 : ℝ) ≤ CBu := rootClauseBCapsUniform_nonneg d Ccaps
  set CWGu : ℝ := rootClauseBOscWUniform Cdel * stepFourGagliardoConst d stepOneS
    with hCWGuDef
  refine ⟨rootClauseBFundCedos d C Cann k, Citer,
    rootClauseBPrefactor d Cch (rootClauseBCaccUniform Cc CBu) Cosc CBu CBu
      (rootClauseBTopCtr d (rootClauseBDataBConst d)) CWGu
      (rootClauseBDataMConst d CBu),
    k, one_le_rootClauseBFundCedos d C Cann k, ?_, hk11, ?_⟩
  · -- `0 ≤ C_est`
    have hCWGu0 : (0 : ℝ) ≤ CWGu := by
      rw [hCWGuDef]
      exact mul_nonneg (rootClauseBOscWUniform_nonneg hCdel)
        (stepFourGagliardoConst_nonneg d _)
    have hzero := rootClauseBPrefactor_mono_data d (Cch := Cch)
      (Ccacc := rootClauseBCaccUniform Cc CBu) (Cosc := Cosc) (CBc := 0) (CBc' := CBu)
      (CB := 0) (CB' := CBu) (Ctr := rootClauseBTopCtr d (rootClauseBDataBConst d))
      (CWG := 0) (CWG' := CWGu) (CdM := 0) (CdM' := rootClauseBDataMConst d CBu)
      hCch.le (rootClauseBCaccUniform_nonneg Cc CBu) hCosc le_rfl
      (rootClauseBTopCtr_nonneg d _) le_rfl le_rfl hCBu hCBu hCWGu0
      (rootClauseBDataMConst_nonneg d CBu)
    refine le_trans ?_ hzero
    rw [rootClauseBPrefactor]
    have hCg : (0 : ℝ) ≤ rootClauseBCg d (rootClauseBCaccUniform Cc CBu) Cosc 0 :=
      rootClauseBCg_nonneg d (rootClauseBCaccUniform_nonneg Cc CBu) hCosc
    have hX : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
        stepSevenBridgeConst stepSevenCgS *
        (Cch * 64 * (Real.sqrt (32 / 7 * 0) + 32 / 7 * 0)) *
        rootClauseBTopCtr d (rootClauseBDataBConst d) := by
      refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
        (stepSevenEmbeddingConst_nonneg d)) (stepSevenBridgeConst_nonneg _)) ?_)
        (rootClauseBTopCtr_nonneg d _)
      have h0 : (0 : ℝ) ≤ Real.sqrt (32 / 7 * 0) + 32 / 7 * 0 := by
        have hz := Real.sqrt_nonneg ((32 : ℝ) / 7 * 0)
        linarith only [hz]
      exact mul_nonneg (by linarith only [hCch]) h0
    have hL : (0 : ℝ) ≤ rootClauseBCg d (rootClauseBCaccUniform Cc CBu) Cosc 0 *
        Real.sqrt 4 * (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
          stepSevenBridgeConst stepSevenCgS *
          (Cch * 64 * (Real.sqrt (32 / 7 * 0) + 32 / 7 * 0)) *
          rootClauseBTopCtr d (rootClauseBDataBConst d)) :=
      mul_nonneg (mul_nonneg hCg (Real.sqrt_nonneg 4)) hX
    have hR : (0 : ℝ) ≤ rootClauseBCg d (rootClauseBCaccUniform Cc CBu) Cosc 0 *
        (Real.sqrt 4 * 0 + 0) := by
      rw [mul_zero, add_zero, mul_zero]
    linarith only [hL, hR]
  intro Cedos hfloor
  set C1 : ℝ := stepOneC1 d Cedos 1 Citer k with hC1Def
  have hC1two : (2 : ℝ) ≤ C1 := two_le_stepOneC1 d Cedos 1 Citer k
  have hC1pos : (0 : ℝ) < C1 := by linarith only [hC1two]
  obtain ⟨gamma0, hgamma0, hfacts⟩ :=
    exists_rootClauseBGammaFacts d (C := max C Ccaps) (Cann := Cann) (Cind := Cind)
      (C1 := C1) (Crg := Crg) hcstar hCmax hCann hCindpos hC1pos hCrg
  refine ⟨gamma0, hgamma0, ?_⟩
  intro M hcs hgammale alpha halpha0 halpha m
  have hfact := hfacts M hcs hgammale
  have hg0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hsqrtpos : (0 : ℝ) < Crg * Real.sqrt M.gamma :=
    mul_pos hCrg (Real.sqrt_pos.mpr hg0)
  have halpha1 : alpha < 1 := by linarith only [halpha, hsqrtpos]
  have hcs10 : (0 : ℝ) ≤ Disorder.cstar M ^ (10 : ℕ) :=
    pow_nonneg ((Disorder.cstar_characterization M).1).le 10
  have hinvC : (max C Ccaps)⁻¹ ≤ C⁻¹ := inv_anti₀ hC (le_max_left _ _)
  have hinvCaps : (max C Ccaps)⁻¹ ≤ Ccaps⁻¹ := inv_anti₀ hCcaps (le_max_right _ _)
  have hregC : M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    le_trans hfact.regimeC (mul_le_mul_of_nonneg_right hinvC hcs10)
  have hregCaps : M.gamma ≤ Ccaps⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    le_trans hfact.regimeC (mul_le_mul_of_nonneg_right hinvCaps hcs10)
  have hfree : M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
      Real.rpow (stepOneS / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
        (C⁻¹ * stepOneS ^ (4 : ℕ)) := by
    refine le_trans hfact.smallFree (mul_le_mul_of_nonneg_left ?_ ?_)
    · exact mul_le_mul_of_nonneg_right hinvC (pow_nonneg (by rw [stepOneS]; norm_num) 4)
    · exact mul_nonneg (Real.rpow_pos_of_pos (by rw [stepOneS]; norm_num) _).le
        (pow_nonneg ((Disorder.cstar_characterization M).1).le 2)
  have hsmall := hfact.smallEp alpha halpha0 halpha
  obtain ⟨Ecap, -, -, hstate⟩ := hind M hfact.regimeInd
  have hdeltamem := stepOneDelta_mem hC1two halpha0 halpha1
  have haeOsc := hoscprod Cedos hfloor M m Ecap (hstate m) hfact.ltHalf hregC
    hfact.regimeAnn hfact.le256 hfree alpha halpha0 halpha1 hsmall m le_rfl
  have haeCaps := hcapsprod M hregCaps (stepOneDelta C1 alpha) hdeltamem
    hfact.floorEight hsmall
  filter_upwards [haeOsc, haeCaps] with omega hOsc hCap
  intro n L hnm hmL hpay u h g Kg Kh hsol hgHol hhHol x hx hzin
  have hKg : (0 : ℝ) ≤ Kg := holderHalf_const_nonneg hgHol
  have hKh : (0 : ℝ) ≤ Kh := holderHalf_const_nonneg hhHol
  have hv : offGridLatticeIndex n x ∈ Support.latticeCubeSet d n m :=
    offGridLatticeIndex_mem_of_mem_cube n hx
  have hoscfun := hOsc L n (offGridLatticeIndex n x) hmL hpay.2.1 hv hzin hpay u h g
    Kg Kh hKg hKh hsol hgHol hhHol
  set CBraw : ℝ :=
    2 * (d : ℝ) * ((Ccaps * stepOneEp (stepOneDelta C1 alpha)) ^ 2 + 1) with hCBrawDef
  have hCBraw0 : (0 : ℝ) ≤ CBraw := by
    have hsq : (0 : ℝ) ≤ (Ccaps * stepOneEp (stepOneDelta C1 alpha)) ^ 2 := sq_nonneg _
    have hdd : (0 : ℝ) ≤ 2 * (d : ℝ) := by
      have hc : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith only [hc]
    rw [hCBrawDef]
    exact mul_nonneg hdd (by linarith only [hsq])
  have hCBle : CBraw ≤ CBu := by
    rw [hCBrawDef, hCBuDef]
    exact capsConst_le_rootClauseBCapsUniform d hCcaps.le hdeltamem.2
  have hCWGle : edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS ≤ CWGu := by
    rw [hCWGuDef]
    exact mul_le_mul_of_nonneg_right
      (edFinalDataOscW_le_uniform hfact.ltHalf hfact.leQuarter hCdel)
      (stepFourGagliardoConst_nonneg d _)
  have hCWG0 : (0 : ℝ) ≤ edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS :=
    mul_nonneg (edFinalDataOscW_nonneg hfact.ltHalf hCdel)
      (stepFourGagliardoConst_nonneg d _)
  have hstep1 := rootClauseBPrefactor_mono_ccacc d (Cch := Cch)
    (Cosc := Cosc) (CBc := CBraw) (CB := CBraw)
    (Ctr := rootClauseBTopCtr d (rootClauseBDataBConst d))
    (CWG := edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS)
    (CdM := rootClauseBDataMConst d CBraw) hCch.le hCosc hCBraw0
    (rootClauseBTopCtr_nonneg d _) hCWG0 (rootClauseBDataMConst_nonneg d CBraw)
    (rootClauseBCaccUniform_mono Cc hCBraw0 hCBle)
  have hstep2 := rootClauseBPrefactor_mono_data d (Cch := Cch)
    (Ccacc := rootClauseBCaccUniform Cc CBu) (Cosc := Cosc) (CBc := CBraw)
    (CBc' := CBu) (CB := CBraw) (CB' := CBu)
    (Ctr := rootClauseBTopCtr d (rootClauseBDataBConst d))
    (CWG := edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS) (CWG' := CWGu)
    (CdM := rootClauseBDataMConst d CBraw) (CdM' := rootClauseBDataMConst d CBu)
    hCch.le (rootClauseBCaccUniform_nonneg Cc CBu) hCosc hCBraw0
    (rootClauseBTopCtr_nonneg d _) hCWG0 (rootClauseBDataMConst_nonneg d CBraw)
    hCBle hCBle hCWGle (rootClauseBDataMConst_mono d hCBle)
  refine hend M m Ecap (hstate m) hfact.ltHalf L omega u h le_rfl hnm hmL
    (fun k' n0 v0 hgood L' hL' => hCap k' n0 v0 hgood L' hL') hpay hx hzin hsol hgHol
    hKg hCBraw0 hCdel hCosc (two_mul_dim_le_stepOneC1 d Cedos 1 Citer k)
    halpha0.le (le_of_lt halpha1) hoscfun (le_trans hstep1 hstep2) hzin

end

end Algsuperdiff.Section4.Provider.Regularity
