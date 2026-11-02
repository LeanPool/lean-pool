/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.StreamProcess
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.PthMomentProcessScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.RenormalizationAtRandomScale

/-!
# EarlyExitModel

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The early-exit probability and the diffusivity profile at the confinement scale

The quenched displacement-moment composition reads two of its inputs at the random
confinement scale of one sample: the probability that the process leaves the cube
`□_{m_t}` before time `t`, and the closeness of the running diffusivity to the intrinsic
scale.  Both are supplied here.

The confinement scale is the least scale `n` with `L (1 + S_n) ≤ 3^n`, where the
deterministic factor is `L = K |log γ|^{1/2} R(t)`.  Two consequences of that inequality
are used.  The first is purely deterministic: `3^{m_t}` is at least `K |log γ|^{1/2} R(t)`,
so the two-branch minimum `M(t, m_t)` of the displacement estimate is at least
`K² |log γ|`, and an exponential of `-c M(t, m_t)` is therefore at most `γ^{cK²}`; choosing
`K` with `100 ≤ c K²` turns that into `γ^{100}`.  The second is the scale arithmetic of the
intrinsic-scale comparison, which the profile bound inherits with one factor of the
dimension.

## Main results

* `sq_le_displacementMinScale_of_isConfinementScale` — the deterministic lower bound
  `K² |log γ| ≤ M(t, m_t)` at a confinement scale.
* `exp_neg_mul_displacementMinScale_le_pow_of_isConfinementScale` — the exponential of the
  displacement minimum at a confinement scale is at most `γ^{100}`.
* `ae_isConfinementScale_confinementScale_fullSample` — the chosen confinement scale is
  almost surely a confinement scale, for the law of the full sample.
* `abs_mul_intrinsicScale_sq_sub_mul_le_of_isConfinementScale` and
  `abs_mul_intrinsicScale_sq_sub_mul_le_confinementScale` — the diffusivity profile
  comparison at a confinement scale and at the chosen confinement scale.

## References

* ABK26, the superdiffusive displacement bounds of Section 5.4.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3 Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open DivergenceFormProcess.Form DivergenceFormProcess.StoppedDirichlet
open HCPolySupport MarkovProcess MeasureTheory
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## 1. The displacement minimum at a confinement scale -/

private theorem three_zpow_sq (m : ℤ) : ((3 : ℝ) ^ m) ^ (2 : ℕ) = (3 : ℝ) ^ (2 * m) := by
  rw [← zpow_natCast ((3 : ℝ) ^ m) 2, ← zpow_mul]
  congr 1
  push_cast
  ring

/-- **The displacement minimum is large at a confinement scale.**  The defining inequality
of the confinement scale puts `3^{m_t}` above the deterministic factor `K |log γ|^{1/2}`
times the intrinsic scale, and the intrinsic-scale comparison of the two branches of the
minimum then reads that ratio squared inside `M(t, m_t)`. -/
theorem sq_le_displacementMinScale_of_isConfinementScale
    {nu cstar gamma t K L : ℝ} {Stilde : ℤ → ℝ≥0∞} {m : ℤ}
    (hnu : 0 < nu) (hcstar : 0 < cstar) (hgamma : 0 < gamma) (hgamma4 : gamma ≤ 1 / 4)
    (hgc : gamma ≤ cstar) (ht : 0 < t) (hK : 1 ≤ K)
    (hKL : K * Real.sqrt |Real.log gamma| * intrinsicScale nu cstar gamma t ≤ L)
    (hm : IsConfinementScale Stilde L m) :
    K ^ (2 : ℕ) * |Real.log gamma| ≤ displacementMinScale nu cstar gamma t m := by
  have hgamma1 : gamma < 1 := lt_of_le_of_lt hgamma4 (by norm_num)
  have hR : 0 < intrinsicScale nu cstar gamma t := intrinsicScale_pos hnu hcstar hgamma ht
  have hlog : 1 ≤ Real.sqrt |Real.log gamma| := one_le_sqrt_abs_log hgamma hgamma4
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  have hKlog : 1 ≤ K * Real.sqrt |Real.log gamma| := by nlinarith only [hK, hlog]
  have hLm : L ≤ (3 : ℝ) ^ m := le_three_zpow_of_isConfinementScale' le_rfl hm
  have hprod : K * Real.sqrt |Real.log gamma| * intrinsicScale nu cstar gamma t ≤
      (3 : ℝ) ^ m := hKL.trans hLm
  have hRle : intrinsicScale nu cstar gamma t ≤ (3 : ℝ) ^ m := by
    nlinarith only [hKlog, hR, hprod]
  have hratio : K * Real.sqrt |Real.log gamma| ≤
      (3 : ℝ) ^ m / intrinsicScale nu cstar gamma t := (le_div_iff₀ hR).2 hprod
  have hsq : K ^ (2 : ℕ) * |Real.log gamma| ≤
      ((3 : ℝ) ^ m / intrinsicScale nu cstar gamma t) ^ (2 : ℕ) := by
    have hsqrt : Real.sqrt |Real.log gamma| ^ (2 : ℕ) = |Real.log gamma| :=
      Real.sq_sqrt (abs_nonneg _)
    calc K ^ (2 : ℕ) * |Real.log gamma|
        = (K * Real.sqrt |Real.log gamma|) ^ (2 : ℕ) := by rw [mul_pow, hsqrt]
      _ ≤ ((3 : ℝ) ^ m / intrinsicScale nu cstar gamma t) ^ (2 : ℕ) :=
          pow_le_pow_left₀ (le_trans zero_le_one hKlog) hratio 2
  refine hsq.trans ?_
  have hmin := sq_div_intrinsicScale_le_displacementMinScale hnu hcstar hgamma hgamma1 hgc ht hRle
  rw [displacementMinScale, ← three_zpow_sq]
  exact hmin

/-- **The exponential of the displacement minimum at a confinement scale.**  With
`100 ≤ c K²` the exponential rate `c M(t, m_t)` is at least `100 |log γ|`. -/
theorem exp_neg_mul_displacementMinScale_le_pow_of_isConfinementScale
    {nu cstar gamma t K L c : ℝ} {Stilde : ℤ → ℝ≥0∞} {m : ℤ}
    (hnu : 0 < nu) (hcstar : 0 < cstar) (hgamma : 0 < gamma) (hgamma4 : gamma ≤ 1 / 4)
    (hgc : gamma ≤ cstar) (ht : 0 < t) (hK : 1 ≤ K) (hc : 0 ≤ c)
    (hcK : (100 : ℝ) ≤ c * K ^ (2 : ℕ))
    (hKL : K * Real.sqrt |Real.log gamma| * intrinsicScale nu cstar gamma t ≤ L)
    (hm : IsConfinementScale Stilde L m) :
    Real.exp (-c * displacementMinScale nu cstar gamma t m) ≤ gamma ^ (100 : ℕ) := by
  have hgamma1 : gamma < 1 := lt_of_le_of_lt hgamma4 (by norm_num)
  have hbase := sq_le_displacementMinScale_of_isConfinementScale hnu hcstar hgamma hgamma4
    hgc ht hK hKL hm
  have habs0 : (0 : ℝ) ≤ |Real.log gamma| := abs_nonneg _
  have hstep : (100 : ℝ) * |Real.log gamma| ≤
      c * displacementMinScale nu cstar gamma t m := by
    calc (100 : ℝ) * |Real.log gamma| ≤ (c * K ^ (2 : ℕ)) * |Real.log gamma| :=
          mul_le_mul_of_nonneg_right hcK habs0
      _ = c * (K ^ (2 : ℕ) * |Real.log gamma|) := by ring
      _ ≤ c * displacementMinScale nu cstar gamma t m :=
          mul_le_mul_of_nonneg_left hbase hc
  have habs : |Real.log gamma| = -Real.log gamma :=
    abs_of_neg (Real.log_neg hgamma hgamma1)
  have hpow : gamma ^ (100 : ℕ) = Real.exp (Real.log gamma * 100) := by
    rw [← Real.rpow_natCast gamma 100, Real.rpow_def_of_pos hgamma]
    norm_num
  rw [habs] at hstep
  rw [hpow]
  exact Real.exp_le_exp.2 (by linarith only [hstep])

/-! ## 2. The early-exit probability at the confinement scale -/

omit [NeZero d] in
/-- **The confinement scale is almost surely a confinement scale, for the full sample.**
The law of the full sample pushes forward to the law of the coefficient cutoff sample, so
one uniform moment bound on the displacement scales gives the statement there. -/
theorem ae_isConfinementScale_confinementScale_fullSample (M : ABKModel d)
    {S : ℤ → Cutoff.CutoffSample d → ℝ} (hmeas : ∀ k, Measurable (S k))
    {C p L : ℝ} (hC : 0 ≤ C) (hp : 1 ≤ p) (hL : 0 < L)
    (hmom : ∀ k : ℤ, (∫⁻ omega, ENNReal.ofReal (S k omega) ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal C ^ p) :
    ∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
      IsConfinementScale (fun n => widenedScale (fun k => S k omega.1) n) L
        (confinementScale S L omega.1) := by
  have hcut := ae_isConfinementScale_confinementScale
    (Cutoff.cutoffSampleLaw M).toMeasure hmeas hC hp hL hmom
  rw [← map_fullSampleLaw_val M] at hcut
  exact ae_of_ae_map measurable_subtype_coe.aemeasurable hcut

/-! ## 3. The diffusivity profile at the confinement scale -/

/-- **The profile comparison in the dimensional form.**  The scale arithmetic at the
confinement scale, multiplied by the dimension; the constant is `d (1 + 2C)`, where `C` is
the relative error of the renormalized diffusivity. -/
theorem abs_mul_intrinsicScale_sq_sub_mul_le_of_isConfinementScale (d : ℕ)
    {nu cstar gamma t K : ℝ} (hnu : 0 < nu) (hcstar : 0 < cstar) (hgamma : 0 < gamma)
    (hgamma4 : gamma ≤ 1 / 4) (ht : 0 < t) (hK : 1 ≤ K)
    {Stilde : ℤ → ℝ≥0∞} {m : ℤ}
    (hm : IsConfinementScale Stilde
      (K * Real.sqrt |Real.log gamma| * intrinsicScale nu cstar gamma t) m)
    {sigmaBar C : ℝ} (hsigma : 0 < sigmaBar) (hC : 0 ≤ C)
    (hsmall : C * Real.sqrt gamma * |Real.log gamma| ≤ 1 / 2)
    (hprofile : |sigmaBar - effectiveDiffusivity nu cstar gamma ((3 : ℝ) ^ m)| ≤
      C * Real.sqrt gamma * |Real.log gamma| * sigmaBar) :
    |(d : ℝ) * intrinsicScale nu cstar gamma t ^ 2 - (d : ℝ) * (sigmaBar * t)| ≤
      ((d : ℝ) * (1 + 2 * C)) * Real.sqrt gamma * |Real.log gamma| *
        ((3 : ℝ) ^ m) ^ (2 : ℕ) := by
  have hbase := abs_intrinsicScale_sq_sub_mul_le_of_isConfinementScale hnu hcstar hgamma
    hgamma4 ht hK hm hsigma hC hsmall hprofile
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  calc |(d : ℝ) * intrinsicScale nu cstar gamma t ^ 2 - (d : ℝ) * (sigmaBar * t)|
      = (d : ℝ) * |intrinsicScale nu cstar gamma t ^ (2 : ℕ) - sigmaBar * t| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hd]
    _ ≤ (d : ℝ) * ((1 + 2 * C) * Real.sqrt gamma * |Real.log gamma| *
        ((3 : ℝ) ^ m) ^ (2 : ℕ)) := mul_le_mul_of_nonneg_left hbase hd
    _ = ((d : ℝ) * (1 + 2 * C)) * Real.sqrt gamma * |Real.log gamma| *
        ((3 : ℝ) ^ m) ^ (2 : ℕ) := by ring

omit [NeZero d] in
/-- **The profile comparison at the chosen confinement scale.**  The renormalized
diffusivities of the scales, read at the confinement scale of the sample. -/
theorem abs_mul_intrinsicScale_sq_sub_mul_le_confinementScale (M : ABKModel d)
    {cstar t K L C : ℝ} (S : ℤ → Cutoff.CutoffSample d → ℝ) (sigmaBar : ℤ → ℝ)
    (hcstar : 0 < cstar) (ht : 0 < t) (hK : 1 ≤ K)
    (hL : L = K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t)
    (hsigma : ∀ n : ℤ, 0 < sigmaBar n) (hC : 0 ≤ C)
    (hsmall : C * Real.sqrt M.gamma * |Real.log M.gamma| ≤ 1 / 2)
    (hprofile : ∀ n : ℤ, |sigmaBar n -
        effectiveDiffusivity M.nu cstar M.gamma ((3 : ℝ) ^ n)| ≤
      C * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBar n)
    (hconf : ∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
      IsConfinementScale (fun n => widenedScale (fun k => S k omega.1) n) L
        (confinementScale S L omega.1)) :
    ∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
      |(d : ℝ) * intrinsicScale M.nu cstar M.gamma t ^ 2 -
          (d : ℝ) * (sigmaBar (confinementScale S L omega.1) * t)| ≤
        ((d : ℝ) * (1 + 2 * C)) * Real.sqrt M.gamma * |Real.log M.gamma| *
          ((3 : ℝ) ^ (confinementScale S L omega.1)) ^ (2 : ℕ) := by
  subst hL
  filter_upwards [hconf] with omega hmconf
  exact abs_mul_intrinsicScale_sq_sub_mul_le_of_isConfinementScale d M.nu_pos hcstar
    M.shellPrefix.gamma_pos M.shellPrefix.gamma_le_quarter ht hK hmconf
    (hsigma _) hC hsmall (hprofile _)

end

end Algsuperdiff.Section5.Provider
