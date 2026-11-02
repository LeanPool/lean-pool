/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.EarlyExitScaleMoments
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.HomogenizationCorrector
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.PthMomentProcessModel
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.QuenchedMomentsComposer
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.StoppedMomentsCubeModel
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.SuperdiffusivityComponentsModel
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SmallGammaRpow

/-!
# SuperdiffusivityProvider

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Assembly of the corrected superdiffusivity estimate

This module assembles the corrected annealed estimates from the model's
renormalization family, confinement-scale lift, stopped-moment identities, and
process-moment removal bounds.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3 Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open DivergenceFormProcess.Form HCPolySupport MarkovProcess MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- A common constant for assembling process, renormalization and cutoff-removal estimates. -/
def providerComponentConstant (d : ℕ) (CS Cren K C4 C6 : ℝ) : ℝ :=
  max (superdiffusivityV2ComponentConstant CS Cren K)
    (max ((d : ℝ) * 10)
      (max (C6 + 2 + 2 * ((d : ℝ) * (1 + 2 * Cren)))
        (max (2 * (4 * (d : ℝ))) (2 * C4))))

/-- Quantitative control of removing the confinement cutoff from the stream process. -/
def HasDisplacementRemovalBounds (d : ℕ) [NeZero d] (cstar : ℝ) : Prop :=
∀ _hdim : 2 ≤ d, ∀ (c : ℝ), 0 < c → c ≤ 1 →
      ∃ gamma4 C4 C6 Kc : ℝ, 0 < gamma4 ∧ gamma4 = 1 / 4 ∧
        0 ≤ C4 ∧ 0 ≤ C6 ∧ 1 ≤ Kc ∧ Kc = 1 ∧
        ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma4 →
        ∀ t : ℝ, 0 < t →
        ∀ (S : ℤ → Cutoff.CutoffSample d → ℝ) (K L delta : ℝ)
          (Y : ℤ → Cutoff.CutoffSample d → ℕ),
          1 ≤ K → Kc ≤ K →
          L = K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t →
          0 < delta → delta ≤ 1 → (∀ i : ℤ, Measurable (Y i)) →
          (∀ (i : ℤ) (omega : Cutoff.CutoffSample d),
            S i omega = displacementScale delta M.gamma (Y i omega)) →
        (∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
          IsConfinementScale (fun n => widenedScale (fun i => S i omega.1) n) L
            (confinementScale S L omega.1)) →
        (∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
          letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
          letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
          let m := confinementScale S L omega.1
          let R : ℝ := (3 : ℝ) ^ m
          let Q := (streamExhaustionTailInput M omega).wholeSpaceProcess
            ((0 : Vec d) : OnePoint (Vec d))
          ∀ k : ℤ, R ≤ (3 : ℝ) ^ k →
            Q.real {eta | (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤
              ‖onePointRetract (0 : Vec d) (eta t.toNNReal)‖} ≤
              Real.exp (-c * ((((3 : ℝ) ^ k) / R) ^ (2 : ℕ)))) →
        (∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
          letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
          letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
          cubeExitProbability M omega (confinementScale S L omega.1) t.toNNReal ≤
            M.gamma ^ (100 : ℕ)) →
        (∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
          letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
          letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
          let m := confinementScale S L omega.1
          vecNormSq ((∫ path, onePointRetract (0 : Vec d) (path t.toNNReal)
              ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                ((0 : Vec d) : OnePoint (Vec d)))) -
            cubeStoppedMean M omega m t.toNNReal) ≤
              C4 * M.gamma ^ (100 : ℕ) * ((3 : ℝ) ^ m) ^ (2 : ℕ)) ∧
        (∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
          letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
          letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
          let m := confinementScale S L omega.1
          abs ((∫ path, vecNormSq (onePointRetract (0 : Vec d) (path t.toNNReal))
              ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                ((0 : Vec d) : OnePoint (Vec d)))) -
            (∫ path, onePointRealExtension (fun z => cubeCutoff d m z * vecNormSq z)
                (path (ContinuousPath.exitTimeTrunc
                  (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (0 : Vec d) m)
                  t.toNNReal path))
              ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                ((0 : Vec d) : OnePoint (Vec d))))) ≤
              C6 * M.gamma ^ (50 : ℕ) * ((3 : ℝ) ^ m) ^ (2 : ℕ))

private theorem componentConstant_le_providerComponentConstant
    (d : ℕ) (CS Cren K C4 C6 : ℝ) :
    superdiffusivityV2ComponentConstant CS Cren K ≤
      providerComponentConstant d CS Cren K C4 C6 :=
  le_max_left _ _

private theorem stoppedSecondCoefficient_le_providerComponentConstant
    (d : ℕ) (CS Cren K C4 C6 : ℝ) :
    (d : ℝ) * 10 ≤ providerComponentConstant d CS Cren K C4 C6 :=
  (le_max_left _ _).trans (le_max_right _ _)

private theorem secondTailCoefficient_le_providerComponentConstant
    (d : ℕ) (CS Cren K C4 C6 : ℝ) :
    C6 + 2 + 2 * ((d : ℝ) * (1 + 2 * Cren)) ≤
      providerComponentConstant d CS Cren K C4 C6 :=
  ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)

private theorem stoppedMeanCoefficient_le_providerComponentConstant
    (d : ℕ) (CS Cren K C4 C6 : ℝ) :
    2 * (4 * (d : ℝ)) ≤ providerComponentConstant d CS Cren K C4 C6 :=
  (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
    (le_max_right _ _)

private theorem meanTailCoefficient_le_providerComponentConstant
    (d : ℕ) (CS Cren K C4 C6 : ℝ) :
    2 * C4 ≤ providerComponentConstant d CS Cren K C4 C6 :=
  (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
    (le_max_right _ _)

private theorem superdiffusivityV2ComponentConstant_mono
    {CS CS' Cren K K' : ℝ} (hCS0 : 0 ≤ CS) (hCren0 : 0 ≤ Cren) (hK0 : 0 ≤ K)
    (hCS : CS ≤ CS') (hK : K ≤ K') :
    superdiffusivityV2ComponentConstant CS Cren K ≤
      superdiffusivityV2ComponentConstant CS' Cren K' := by
  unfold superdiffusivityV2ComponentConstant
  apply max_le_max le_rfl
  apply max_le_max le_rfl
  apply max_le_max
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hCS (by positivity)) hCren0
  · exact mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hCS0 hCS 2) (by positivity)) hK
      hK0 (by positivity)

/-- The corrected superdiffusivity estimate from the paired removal bounds at the one
confinement-scale family returned by the model lift. -/
theorem superdiffusivity_v2_provider_of_removalBounds
    (d : ℕ) [NeZero d] (cstar : ℝ) (hcstar : 0 < cstar)
    (hremoval : HasDisplacementRemovalBounds d cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ t : ℝ, 0 < t →
      ∀ p : ℝ, 1 ≤ p →
        p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) →
        (∫⁻ omega : FullSample d M.gamma,
            (letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
             letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
             ENNReal.ofReal
                |(∫ path, vecNormSq (onePointRetract (0 : Vec d) (path t.toNNReal))
                    ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                        ((0 : Vec d) : OnePoint (Vec d)))) -
                  2 * (d : ℝ) * intrinsicScale M.nu cstar M.gamma t ^ 2| ^ p)
            ∂(fullSampleLaw M).toMeasure) ≤
          ENNReal.ofReal (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
              Real.sqrt M.gamma * |Real.log M.gamma| ^ (4 : ℕ) *
              intrinsicScale M.nu cstar M.gamma t ^ 2) ^ p ∧
        (∫⁻ omega : FullSample d M.gamma,
            (letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
             letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
             ENNReal.ofReal
                (vecNormSq (∫ path, onePointRetract (0 : Vec d) (path t.toNNReal)
                    ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                        ((0 : Vec d) : OnePoint (Vec d))))) ^ p)
            ∂(fullSampleLaw M).toMeasure) ≤
          ENNReal.ofReal (C * (p + |Real.log M.gamma|) * M.gamma *
              |Real.log M.gamma| ^ (7 : ℕ) *
              intrinsicScale M.nu cstar M.gamma t ^ 2) ^ p := by
  classical
  by_cases hmodels : Nonempty (ABKModel d)
  · let M0 : ABKModel d := Classical.choice hmodels
    have hdim : 2 ≤ d := M0.shellPrefix.dimension
    obtain ⟨gammaE, Cscale, CSbar, Kbar, cbar, hgammaE, hCscale, hCSbar, hKbar,
      hcbar, hcbar1, hlift⟩ :=
      measureReal_exitEvent_confinementScale_le_pow_of_threshold
        d hdim cstar hcstar
    obtain ⟨gammaR, Cren, hgammaR, hCren, hren⟩ :=
      exists_renormalizationFamily_corrector d cstar hcstar
    obtain ⟨gamma4, C4, C6, Kc, hgamma4, hgamma4eq, hC4nn, hC6nn, hKc,
      hKceq, hremove⟩ := hremoval hdim cbar hcbar hcbar1
    obtain ⟨gammaS, hgammaS, hsmallS⟩ :=
      exists_sqrt_mul_abs_log_rpow_le (K := Cren) (q := 1) (eps := 1 / 2)
        hCren.le (by norm_num) (by norm_num)
    have hdimCoeff : 0 ≤ (d : ℝ) * (1 + 2 * Cren) := by positivity
    obtain ⟨gammaD, hgammaD, hsmallD⟩ :=
      exists_sqrt_mul_abs_log_rpow_le (K := (d : ℝ) * (1 + 2 * Cren))
        (q := 1) (eps := 1 / 2) hdimCoeff (by norm_num) (by norm_num)
    let gammaBase := min (min (min gammaE gammaR) (min gamma4 gammaS))
      (min gammaD cstar)
    have hgammaBase : 0 < gammaBase := by
      exact lt_min (lt_min (lt_min hgammaE hgammaR) (lt_min hgamma4 hgammaS))
        (lt_min hgammaD hcstar)
    let Ktop := max Kbar (Real.sqrt (2 * (d : ℝ)))
    let Cbody := providerComponentConstant d CSbar Cren Ktop C4 C6
    let C0 := max Cscale Cbody
    have hC0 : 1 ≤ C0 := hCscale.trans (le_max_left _ _)
    apply superdiffusivity_v2_of_components d cstar hcstar gammaBase C0 hgammaBase hC0
    intro M hMstar hMsmall t ht p hp hpRange
    have hME : M.gamma ≤ gammaE :=
      hMsmall.trans (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
    have hMR : M.gamma ≤ gammaR :=
      hMsmall.trans (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
    have hM4 : M.gamma ≤ gamma4 :=
      hMsmall.trans (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hMS : M.gamma ≤ gammaS :=
      hMsmall.trans (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    have hMD : M.gamma ≤ gammaD :=
      hMsmall.trans (le_trans (min_le_right _ _) (min_le_left _ _))
    apply Classical.choice
    let Kmin := max (Real.sqrt (2 * (d : ℝ))) Kc
    obtain ⟨S, K, L, c, CS, pS, hK, hKmin, hc, hc1, hcbarle, hL, hSform,
      hSmeas, hSnn, hCS, hpS, hCSle, hKle, hpSrange, hSmom, hconf, hearly,
      _hdispk, _hdispR, hdispRbar⟩ := hlift M hMstar hME t ht Kmin
    obtain ⟨delta, Y, hdelta, hdelta1, hYmeas, hS⟩ := hSform
    subst L
    have hKcK : Kc ≤ K := (le_max_right _ _).trans hKmin
    have hsqrtK : Real.sqrt (2 * (d : ℝ)) ≤ K := (le_max_left _ _).trans hKmin
    have hKd : 2 * (d : ℝ) ≤ K ^ (2 : ℕ) := by
      have hnonneg : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
      exact (Real.sq_sqrt hnonneg).ge.trans
        (pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrtK 2)
    have hKcTop : Kc ≤ Ktop := by
      rw [hKceq]
      exact hKbar.trans (le_max_left _ _)
    have hKtop : K ≤ Ktop := by
      refine hKle.trans (max_le (le_max_left _ _) ?_)
      exact max_le (le_max_right _ _) hKcTop
    have hCbody : Cbody ≤ C0 := le_max_right _ _
    have hcomponent : superdiffusivityV2ComponentConstant CS Cren K ≤ C0 :=
      (superdiffusivityV2ComponentConstant_mono (zero_le_one.trans hCS) hCren.le
        (zero_le_one.trans hK) hCSle hKtop).trans
        ((componentConstant_le_providerComponentConstant d CSbar Cren Ktop C4 C6).trans
          hCbody)
    have hCscaleC0 : Cscale ≤ C0 := le_max_left _ _
    have hC0pos : 0 < C0 := zero_lt_one.trans_le hC0
    have hCscalepos : 0 < Cscale := zero_lt_one.trans_le hCscale
    have hinv : C0⁻¹ ≤ Cscale⁻¹ :=
      (inv_le_inv₀ hC0pos hCscalepos).2 hCscaleC0
    have hlogpos : 0 < |Real.log M.gamma| := abs_log_gamma_pos M
    have hfactor : 0 ≤ M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) :=
      (mul_pos (inv_pos.mpr M.shellPrefix.gamma_pos) (zpow_pos hlogpos _)).le
    have hpScaled : p ≤ Cscale⁻¹ * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) := by
      refine hpRange.trans ?_
      have hfirst : C0⁻¹ * M.gamma⁻¹ ≤ Cscale⁻¹ * M.gamma⁻¹ :=
        mul_le_mul_of_nonneg_right hinv (inv_nonneg.mpr M.shellPrefix.gamma_pos.le)
      exact mul_le_mul_of_nonneg_right hfirst (zpow_nonneg hlogpos.le _)
    have hpPS : p ≤ pS := hpScaled.trans hpSrange
    let sigmaBar := Classical.choose (hren M hMstar hMR)
    have hfamilyRest := Classical.choose_spec (hren M hMstar hMR)
    let EB := Classical.choose hfamilyRest
    have hfamily := Classical.choose_spec hfamilyRest
    have hsigma : ∀ m : ℤ, 0 < sigmaBar m := hfamily.1
    have hprofile : ∀ m : ℤ, |sigmaBar m -
        effectiveDiffusivity M.nu cstar M.gamma ((3 : ℝ) ^ m)| ≤
          Cren * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBar m := hfamily.2.1
    have hEBnn : ∀ m : ℤ, ∀ omega, 0 ≤ EB m omega := hfamily.2.2.1
    have hEBmeas : ∀ m : ℤ, Measurable (EB m) := hfamily.2.2.2.1
    have hEBmom := hfamily.2.2.2.2.1
    have hdir := hfamily.2.2.2.2.2
    have hsmall : Cren * Real.sqrt M.gamma * |Real.log M.gamma| ≤ 1 / 2 := by
      have hs := hsmallS M.gamma M.shellPrefix.gamma_pos hMS
      have hpow : Real.rpow |Real.log M.gamma| (1 : ℝ) = |Real.log M.gamma| :=
        Real.rpow_one _
      rw [hpow] at hs
      simpa only [mul_assoc] using hs
    have hsmall' : (d : ℝ) * (1 + 2 * Cren) * Real.sqrt M.gamma *
        |Real.log M.gamma| ≤ 1 / 2 := by
      have hs := hsmallD M.gamma M.shellPrefix.gamma_pos hMD
      have hpow : Real.rpow |Real.log M.gamma| (1 : ℝ) = |Real.log M.gamma| :=
        Real.rpow_one _
      rw [hpow] at hs
      simpa only [mul_assoc] using hs
    have hcorrector := ae_renormalizationCorrector_fullSample M hdir
    have hprof := abs_mul_intrinsicScale_sq_sub_mul_le_confinementScale M S sigmaBar
      hcstar ht hK rfl hsigma hCren.le hsmall hprofile hconf
    obtain ⟨h4, h6⟩ := hremove M hMstar hM4 t ht S K _ delta Y hK hKcK rfl
      hdelta hdelta1 hYmeas hS hconf hdispRbar hearly
    have hsecond : ∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
        (letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
         letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
         |(∫ path, vecNormSq (onePointRetract (0 : Vec d) (path t.toNNReal))
              ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                  ((0 : Vec d) : OnePoint (Vec d)))) -
            2 * (d : ℝ) * intrinsicScale M.nu cstar M.gamma t ^ 2|) ≤
          C0 * (EB (confinementScale S
            (K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t)
            omega.1) omega.1 + Real.sqrt M.gamma * |Real.log M.gamma|) *
            ((3 : ℝ) ^ confinementScale S
              (K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t)
              omega.1) ^ 2 := by
      filter_upwards [hcorrector, hconf, hearly, hprof, h6] with omega hrenOmega hconfOmega
        hearlyOmega hprofOmega h6Omega
      exact secondMoment_quenched_of_moments M cstar t C0 omega S EB _
        (cubeCutoff d (confinementScale S _ omega.1))
        (sigmaBar (confinementScale S _ omega.1))
        (cubeExitProbability M omega (confinementScale S _ omega.1) t.toNNReal)
        10 C6 ((d : ℝ) * (1 + 2 * Cren)) ht M.shellPrefix.gamma_le_quarter hC6nn
        hEBnn (cubeExitProbability_nonneg M omega _ _)
        (sq_nonneg ((3 : ℝ) ^ confinementScale S _ omega.1))
        (dim_mul_sigmaBar_mul_le_three_zpow_sq_of_isConfinementScale M.nu_pos hcstar
          M.shellPrefix.gamma_pos M.shellPrefix.gamma_le_quarter ht hK hKd hconfOmega
          (hsigma _) hCren.le hsmall hsmall' (hprofile _))
        (abs_cubeStoppedQuadratic_sub_le M omega _ (hsigma _) (hEBnn _ _) (hrenOmega _) _)
        (measurable_cubeCutoff_mul_quadraticObservable d _)
        (abs_cubeCutoff_mul_quadraticObservable_le d _)
        h6Omega hprofOmega hearlyOmega
        ((stoppedSecondCoefficient_le_providerComponentConstant d CSbar Cren Ktop C4 C6).trans
          hCbody)
        ((secondTailCoefficient_le_providerComponentConstant d CSbar Cren Ktop C4 C6).trans
          hCbody)
    have hmeanSq : ∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
        (letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
         letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
         vecNormSq (∫ path, onePointRetract (0 : Vec d) (path t.toNNReal)
              ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                  ((0 : Vec d) : OnePoint (Vec d))))) ≤
          C0 * (EB (confinementScale S
            (K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t)
            omega.1) omega.1 ^ 2 + M.gamma ^ (80 : ℕ)) *
            ((3 : ℝ) ^ confinementScale S
              (K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t)
              omega.1) ^ 2 := by
      filter_upwards [hcorrector, h4] with omega hrenOmega h4Omega
      exact meanSq_quenched_of_moments M t C0 omega S EB _
        (cubeStoppedMean M omega (confinementScale S _ omega.1) t.toNNReal)
        (4 * (d : ℝ)) C4 M.shellPrefix.gamma_le_quarter
        (sq_nonneg ((3 : ℝ) ^ confinementScale S _ omega.1)) hC4nn
        (vecNormSq_cubeStoppedMean_le M omega _ (hEBnn _ _) (hrenOmega _) _)
        h4Omega
        ((stoppedMeanCoefficient_le_providerComponentConstant d CSbar Cren Ktop C4 C6).trans
          hCbody)
        ((meanTailCoefficient_le_providerComponentConstant d CSbar Cren Ktop C4 C6).trans
          hCbody)
    exact ⟨superdiffusivityV2ComponentsOfQuenched M hcstar ht hp hCS hCren hK hcomponent
      hpRange hSmeas hSnn (hSmom p hp hpPS).1 (hSmom p hp hpPS).2 hEBnn hEBmeas hEBmom
      hsecond hmeanSq⟩
  · refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
    intro M
    exact (hmodels ⟨M⟩).elim

/-- The corrected Theorem A provider at the stream model. -/
theorem superdiffusivity_v2_provider (d : ℕ) [NeZero d] (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ t : ℝ, 0 < t →
      ∀ p : ℝ, 1 ≤ p →
        p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) →
        (∫⁻ omega : FullSample d M.gamma,
            (letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
             letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
             ENNReal.ofReal
                |(∫ path, vecNormSq (onePointRetract (0 : Vec d) (path t.toNNReal))
                    ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                        ((0 : Vec d) : OnePoint (Vec d)))) -
                  2 * (d : ℝ) * intrinsicScale M.nu cstar M.gamma t ^ 2| ^ p)
            ∂(fullSampleLaw M).toMeasure) ≤
          ENNReal.ofReal (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
              Real.sqrt M.gamma * |Real.log M.gamma| ^ (4 : ℕ) *
              intrinsicScale M.nu cstar M.gamma t ^ 2) ^ p ∧
        (∫⁻ omega : FullSample d M.gamma,
            (letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
             letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
             ENNReal.ofReal
                (vecNormSq (∫ path, onePointRetract (0 : Vec d) (path t.toNNReal)
                    ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                        ((0 : Vec d) : OnePoint (Vec d))))) ^ p)
            ∂(fullSampleLaw M).toMeasure) ≤
          ENNReal.ofReal (C * (p + |Real.log M.gamma|) * M.gamma *
              |Real.log M.gamma| ^ (7 : ℕ) *
              intrinsicScale M.nu cstar M.gamma t ^ 2) ^ p := by
  apply superdiffusivity_v2_provider_of_removalBounds d cstar hcstar
  intro hdim c hc hc1
  exact streamProcess_moment_removal_bounds_of_confinement d hdim cstar hcstar c hc hc1

end

end Algsuperdiff.Section5.Provider
