/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section4.GeneratorRenormalization
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.IntrinsicScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.ConfinementScaleRandomMoments
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.RenormalizationFamilyCorrector

/-!
# RenormalizationAtRandomScale

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The renormalization of the generator, read at the random confinement scale

The superdiffusive displacement bounds evaluate the effective diffusivity and
the error random variable of the renormalization theorem at the random
confinement scale.  This file makes that reading available.

The renormalization theorem produces, for each scale separately, an effective
diffusivity and an error random variable.  Assembling them into families indexed
by the scales is one application of choice over the integers, and is the first
result below; the families are stated with the effective diffusivity profile of
the intrinsic-scale file, so that the scale arithmetic applies to them
verbatim.

The remaining results evaluate at the random scale.  The confinement scale is
above the intrinsic scale, so the scale arithmetic applies pointwise at
`3^{m_t}`; and the moments of the error family at the random scale follow from
the uniform-in-scale moment bound together with the level-set decomposition.

The moment bound of the renormalization theorem carries the factor
`γ^{1/2}|log γ|³` and the `p`-dependence `p^{1/2} + |log γ|^{1/2}`, as in the
source; the additive `p`-dependence is the one the proof of that theorem yields
over the whole range of exponents, and it agrees with `p^{1/2}` up to a
constant once `p` is at least of order `|log γ|`.  It is inherited verbatim
here: the bound below reads
`(C(p^{1/2} + |log γ|^{1/2}) γ^{1/2} |log γ|³)^p`.

## References

* ABK26, the renormalization of the generator and the superdiffusive
  displacement bounds of Section 5.4.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## 2. The scale arithmetic at the confinement scale -/

/-- **The scale arithmetic at the confinement scale.**  The confinement scale is
above the intrinsic scale, because the deterministic factor
`K |log γ|^{1/2} R(t)` in its definition is at least `R(t)`; so the comparison
between `R(t)²` and the displacement holds at `3^{m_t}`. -/
theorem abs_intrinsicScale_sq_sub_mul_le_of_isConfinementScale {nu cstar gamma t K : ℝ}
    (hnu : 0 < nu) (hcstar : 0 < cstar) (hgamma : 0 < gamma) (hgamma4 : gamma ≤ 1 / 4)
    (ht : 0 < t) (hK : 1 ≤ K) {Stilde : ℤ → ℝ≥0∞} {m : ℤ}
    (hm : IsConfinementScale Stilde
      (K * Real.sqrt |Real.log gamma| * intrinsicScale nu cstar gamma t) m)
    {sigmaBar C : ℝ} (hsigma : 0 < sigmaBar) (hC : 0 ≤ C)
    (hsmall : C * Real.sqrt gamma * |Real.log gamma| ≤ 1 / 2)
    (hprofile : |sigmaBar - effectiveDiffusivity nu cstar gamma ((3 : ℝ) ^ m)| ≤
      C * Real.sqrt gamma * |Real.log gamma| * sigmaBar) :
    |intrinsicScale nu cstar gamma t ^ (2 : ℕ) - sigmaBar * t| ≤
      (1 + 2 * C) * Real.sqrt gamma * |Real.log gamma| * ((3 : ℝ) ^ m) ^ (2 : ℕ) := by
  have hRpos := intrinsicScale_pos hnu hcstar hgamma ht
  have hlog := one_le_sqrt_abs_log hgamma hgamma4
  have hle : intrinsicScale nu cstar gamma t ≤
      K * Real.sqrt |Real.log gamma| * intrinsicScale nu cstar gamma t := by
    nth_rewrite 1 [← one_mul (intrinsicScale nu cstar gamma t)]
    refine mul_le_mul_of_nonneg_right ?_ hRpos.le
    nlinarith only [hK, hlog]
  exact abs_intrinsicScale_sq_sub_mul_le hnu hcstar hgamma hgamma4 ht
    (le_three_zpow_of_isConfinementScale' hle hm) hsigma hC hsmall hprofile

/-! ## 3. The moments of the confinement scale in terms of the intrinsic scale -/

/-- **The moments of the confinement scale**, in the form in which they are used:
`3^{m_t}` has moments of order `p` bounded by a constant multiple of
`|log γ|^{1/2} R(t)`. -/
theorem lintegral_three_zpow_confinementScale_le {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {S : ℤ → Omega → ℝ}
    (hmeas : ∀ k, Measurable (S k)) (hSnn : ∀ k omega, 0 ≤ S k omega)
    {nu cstar gamma t K : ℝ} (hnu : 0 < nu) (hcstar : 0 < cstar) (hgamma : 0 < gamma)
    (hgamma4 : gamma ≤ 1 / 4) (ht : 0 < t) (hK : 1 ≤ K) {m : Omega → ℤ}
    (hmmeas : Measurable m)
    (hm : ∀ᵐ omega ∂mu, IsConfinementScale (fun n => widenedScale (fun k => S k omega) n)
      (K * Real.sqrt |Real.log gamma| * intrinsicScale nu cstar gamma t) (m omega))
    {C p : ℝ} (hC : 1 ≤ C) (hp : 1 ≤ p)
    (hmom : ∀ k : ℤ, (∫⁻ omega, ENNReal.ofReal (S k omega) ^ (2 * p) ∂mu) ≤
      ENNReal.ofReal C ^ (2 * p)) :
    (∫⁻ omega, ENNReal.ofReal ((3 : ℝ) ^ (m omega)) ^ p ∂mu) ≤
      ENNReal.ofReal (2187 / 2 * C ^ (2 : ℕ) * K * Real.sqrt |Real.log gamma| *
        intrinsicScale nu cstar gamma t) ^ p := by
  have hRpos := intrinsicScale_pos hnu hcstar hgamma ht
  have hlog := one_le_sqrt_abs_log hgamma hgamma4
  have hL : 0 < K * Real.sqrt |Real.log gamma| * intrinsicScale nu cstar gamma t := by
    have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
    have hs0 : (0 : ℝ) < Real.sqrt |Real.log gamma| := lt_of_lt_of_le zero_lt_one hlog
    positivity
  have hmain := lintegral_three_zpow_isConfinementScale_rpow_le mu hmeas hSnn hL hmmeas hm hC hp
    hmom
  refine hmain.trans (le_of_eq ?_)
  congr 2
  ring

/-! ## 4. The moments of the error family at the confinement scale -/

/-- **The moments of the renormalization error at the confinement scale.**  The
moment bound of the renormalization theorem is uniform in the scale, so the
level-set decomposition of the random scale spends it at the exponent `2p` and
returns the same profile at the exponent `p`, with an explicit constant.

The profile is the one the renormalization theorem carries: the factor
`p^{1/2} + |log γ|^{1/2}` and the power `|log γ|³`. -/
theorem lintegral_renormalizationError_confinementScale_le {d : ℕ} (M : ABKModel d)
    {S : ℤ → Cutoff.CutoffSample d → ℝ} (hmeas : ∀ k, Measurable (S k))
    (hSnn : ∀ k omega, 0 ≤ S k omega) {L : ℝ} (hL : 0 < L)
    {m : Cutoff.CutoffSample d → ℤ} (hmmeas : Measurable m)
    (hm : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      IsConfinementScale (fun n => widenedScale (fun k => S k omega) n) L (m omega))
    {CS p : ℝ} (hCS : 1 ≤ CS) (hp : 1 ≤ p)
    (hmom : ∀ k : ℤ,
      (∫⁻ omega, ENNReal.ofReal (S k omega) ^ (2 * p)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal CS ^ (2 * p))
    {EB : ℤ → Cutoff.CutoffSample d → ℝ} (hEBmeas : ∀ n, Measurable (EB n))
    {C : ℝ} (hC : 0 < C)
    (hrange : 2 * p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹)
    (hEBmom : ∀ n : ℤ, ∀ q : ℝ, 1 ≤ q → q ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
      (∫⁻ omega, ENNReal.ofReal (EB n omega) ^ q
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal (C * (Real.sqrt q + Real.sqrt |Real.log M.gamma|) *
          Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ q) :
    (∫⁻ omega, ENNReal.ofReal (EB (m omega) omega) ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (81 / 2 * Real.sqrt 2 * CS * C *
        (Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
        |Real.log M.gamma| ^ (3 : ℕ)) ^ p := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  set D : ℝ := C * (Real.sqrt (2 * p) + Real.sqrt |Real.log M.gamma|) *
    Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ) with hDdef
  have hDnn : 0 ≤ D := by
    rw [hDdef]
    positivity
  have hEBmom' : ∀ n : ℤ, (∫⁻ omega, ENNReal.ofReal (EB n omega) ^ (2 * p)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal D ^ (2 * p) :=
    fun n => hEBmom n (2 * p) (by linarith only [hp]) hrange
  have hmain := lintegral_atConfinementScale_rpow_le (Cutoff.cutoffSampleLaw M).toMeasure
    hmeas hSnn hL hmmeas hm hCS hp hmom hEBmeas hDnn hEBmom'
  refine hmain.trans ?_
  refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hp0.le
  have hsqrt2 : Real.sqrt (2 * p) = Real.sqrt 2 * Real.sqrt p :=
    Real.sqrt_mul (by norm_num) p
  have hone : (1 : ℝ) ≤ Real.sqrt 2 := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
  have hsum : Real.sqrt (2 * p) + Real.sqrt |Real.log M.gamma| ≤
      Real.sqrt 2 * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) := by
    rw [hsqrt2, mul_add]
    have : Real.sqrt |Real.log M.gamma| ≤ Real.sqrt 2 * Real.sqrt |Real.log M.gamma| := by
      nlinarith only [hone, Real.sqrt_nonneg |Real.log M.gamma|]
    linarith only [this]
  have hCSnn : (0 : ℝ) ≤ CS := by linarith only [hCS]
  have hDle : D ≤ Real.sqrt 2 * C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
      Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ) := by
    rw [hDdef]
    have hfac : (0 : ℝ) ≤ C * (Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) := by
      positivity
    nlinarith only [hsum, hfac, hC, Real.sqrt_nonneg M.gamma,
      pow_nonneg (abs_nonneg (Real.log M.gamma)) 3]
  have hconst : (0 : ℝ) ≤ 81 / 2 * CS := by linarith only [hCSnn]
  nlinarith only [hDle, hconst, hDnn]

/-! ## 5. The same moments at the chosen confinement scale -/

/-- **The moments of the chosen confinement scale.**  The hypotheses of the
moment bound already make the chosen scale measurable and almost surely minimal,
so the scale is no longer a binder. -/
theorem lintegral_three_zpow_selectedConfinementScale_le {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    {S : ℤ → Omega → ℝ} (hmeas : ∀ k, Measurable (S k)) (hSnn : ∀ k omega, 0 ≤ S k omega)
    {nu cstar gamma t K : ℝ} (hnu : 0 < nu) (hcstar : 0 < cstar) (hgamma : 0 < gamma)
    (hgamma4 : gamma ≤ 1 / 4) (ht : 0 < t) (hK : 1 ≤ K) {C p : ℝ} (hC : 1 ≤ C) (hp : 1 ≤ p)
    (hmom : ∀ k : ℤ, (∫⁻ omega, ENNReal.ofReal (S k omega) ^ (2 * p) ∂mu) ≤
      ENNReal.ofReal C ^ (2 * p)) :
    (∫⁻ omega, ENNReal.ofReal ((3 : ℝ) ^ (confinementScale S
        (K * Real.sqrt |Real.log gamma| * intrinsicScale nu cstar gamma t) omega)) ^ p ∂mu) ≤
      ENNReal.ofReal (2187 / 2 * C ^ (2 : ℕ) * K * Real.sqrt |Real.log gamma| *
        intrinsicScale nu cstar gamma t) ^ p := by
  have hRpos := intrinsicScale_pos hnu hcstar hgamma ht
  have hlog := one_le_sqrt_abs_log hgamma hgamma4
  have hL : 0 < K * Real.sqrt |Real.log gamma| * intrinsicScale nu cstar gamma t := by
    have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
    have hs0 : (0 : ℝ) < Real.sqrt |Real.log gamma| := lt_of_lt_of_le zero_lt_one hlog
    positivity
  exact lintegral_three_zpow_confinementScale_le mu hmeas hSnn hnu hcstar hgamma hgamma4 ht hK
    (measurable_confinementScale hmeas _)
    (ae_isConfinementScale_confinementScale mu hmeas (by linarith only [hC])
      (by linarith only [hp]) hL hmom) hC hp hmom

/-- **The moments of the renormalization error at the chosen confinement
scale.**  As above, with the error family evaluated at the chosen scale. -/
theorem lintegral_renormalizationError_selectedConfinementScale_le {d : ℕ} (M : ABKModel d)
    {S : ℤ → Cutoff.CutoffSample d → ℝ} (hmeas : ∀ k, Measurable (S k))
    (hSnn : ∀ k omega, 0 ≤ S k omega) {L : ℝ} (hL : 0 < L)
    {CS p : ℝ} (hCS : 1 ≤ CS) (hp : 1 ≤ p)
    (hmom : ∀ k : ℤ,
      (∫⁻ omega, ENNReal.ofReal (S k omega) ^ (2 * p)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal CS ^ (2 * p))
    {EB : ℤ → Cutoff.CutoffSample d → ℝ} (hEBmeas : ∀ n, Measurable (EB n))
    {C : ℝ} (hC : 0 < C)
    (hrange : 2 * p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹)
    (hEBmom : ∀ n : ℤ, ∀ q : ℝ, 1 ≤ q → q ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
      (∫⁻ omega, ENNReal.ofReal (EB n omega) ^ q
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal (C * (Real.sqrt q + Real.sqrt |Real.log M.gamma|) *
          Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ q) :
    (∫⁻ omega, ENNReal.ofReal (EB (confinementScale S L omega) omega) ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (81 / 2 * Real.sqrt 2 * CS * C *
        (Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
        |Real.log M.gamma| ^ (3 : ℕ)) ^ p :=
  lintegral_renormalizationError_confinementScale_le M hmeas hSnn hL
    (measurable_confinementScale hmeas L)
    (ae_isConfinementScale_confinementScale (Cutoff.cutoffSampleLaw M).toMeasure hmeas
      (by linarith only [hCS]) (by linarith only [hp]) hL hmom) hCS hp hmom hEBmeas hC
    hrange hEBmom

end

end Algsuperdiff.Section5.Support
