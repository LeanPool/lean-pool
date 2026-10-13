/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.MomentBoostedKernel
public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.PsiConcentration.TailKernel

/-!
# MomentBoostedTruncation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Internal truncated-MGF kernel for strengthened moment tails

This file starts the analytic `p > 2` branch needed internally by the exact
`e.kl.bounds.large` provider.  It does not state a source-facing stream bound.
The first lemma keeps the `sigma⁻¹` in the strengthened tail from
`MomentBoostedKernel`, which is what prevents the generic heavy-tail A's
exponential-in-`sigma⁻²` loss.

No declaration, import, or code path from that repository is used.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory ProbabilityTheory
open HCPolySupport HCPolySupport.IndependentSums

noncomputable section

/-- Half of the strengthened tail exponent. -/
noncomputable def momentBoostedKernelCoeff (sigma : ℝ) : ℝ :=
  1 / (4 * sigma)

theorem momentBoostedKernelCoeff_pos {sigma : ℝ} (hsigma : 0 < sigma) :
    0 < momentBoostedKernelCoeff sigma := by
  unfold momentBoostedKernelCoeff
  positivity

/-- A positive MGF tilt below the cutoff is absorbed by the strengthened
one-sided moment tail. -/
theorem momentBoosted_tail_kernel_pointwise
    {sigma l L t : ℝ}
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hl : 0 ≤ l)
    (hlL : l ≤ momentBoostedKernelCoeff sigma * L ^ (sigma - 1))
    (ht : t ∈ Set.Icc 1 L) :
    ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
        Real.exp (-(t ^ sigma / (2 * sigma)))
      ≤ (2 * t + momentBoostedKernelCoeff sigma * t ^ (sigma + 1)) *
          Real.exp (-(momentBoostedKernelCoeff sigma * t ^ sigma)) := by
  let b := momentBoostedKernelCoeff sigma
  have hb : 0 < b := momentBoostedKernelCoeff_pos hsigma
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one (le_trans ht.1 ht.2)
  have hpow_mono : L ^ (sigma - 1) ≤ t ^ (sigma - 1) := by
    exact Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)
      ht_pos (show L ∈ Set.Ioi (0 : ℝ) by exact hL_pos) ht.2
  have hlt : l * t ≤ b * t ^ sigma := by
    calc
      l * t ≤ (b * L ^ (sigma - 1)) * t :=
        mul_le_mul_of_nonneg_right hlL ht_pos.le
      _ ≤ (b * t ^ (sigma - 1)) * t :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow_mono hb.le) ht_pos.le
      _ = b * t ^ sigma := by
        calc
          (b * t ^ (sigma - 1)) * t =
              b * (t ^ (sigma - 1) * t ^ (1 : ℝ)) := by
                rw [Real.rpow_one]
                ring
          _ = b * t ^ sigma := by rw [← Real.rpow_add ht_pos]; ring_nf
  have hpoly :
      2 * t + l * t ^ (2 : ℕ) ≤
        2 * t + b * t ^ (sigma + 1) := by
    have hmul : l * t ^ (2 : ℕ) ≤ b * t ^ (sigma + 1) := by
      calc
        l * t ^ (2 : ℕ) = (l * t) * t := by ring
        _ ≤ (b * t ^ sigma) * t :=
          mul_le_mul_of_nonneg_right hlt ht_pos.le
        _ = b * t ^ (sigma + 1) := by
          calc
            (b * t ^ sigma) * t = b * (t ^ sigma * t ^ (1 : ℝ)) := by
              rw [Real.rpow_one]
              ring
            _ = b * t ^ (sigma + 1) := by rw [← Real.rpow_add ht_pos]
    linarith
  have hexp :
      Real.exp (l * t) * Real.exp (-(t ^ sigma / (2 * sigma))) ≤
        Real.exp (-(b * t ^ sigma)) := by
    have htail_eq : t ^ sigma / (2 * sigma) = 2 * (b * t ^ sigma) := by
      dsimp only [b, momentBoostedKernelCoeff]
      field_simp [ne_of_gt hsigma]
      ring
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    rw [htail_eq]
    linarith
  have hpoly_nonneg : 0 ≤ 2 * t + l * t ^ (2 : ℕ) := by positivity
  calc
    ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
          Real.exp (-(t ^ sigma / (2 * sigma))) =
        (2 * t + l * t ^ (2 : ℕ)) *
          (Real.exp (l * t) * Real.exp (-(t ^ sigma / (2 * sigma)))) := by ring
    _ ≤ (2 * t + l * t ^ (2 : ℕ)) *
          Real.exp (-(b * t ^ sigma)) :=
      mul_le_mul_of_nonneg_left hexp hpoly_nonneg
    _ ≤ (2 * t + b * t ^ (sigma + 1)) *
          Real.exp (-(b * t ^ sigma)) :=
      mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = _ := rfl

/-- The analytic kernel also controls the actual upper-tail integrand of an
observable with strengthened moment tail at unit scale. -/
theorem momentBoosted_tail_integrand_pointwise_of_isBigOWith
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {X : Omega → ℝ} {sigma l L t : ℝ}
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hX : IsBigOWith mu (momentBoostedGammaSigma sigma) X 1)
    (hl : 0 ≤ l)
    (hlL : l ≤ momentBoostedKernelCoeff sigma * L ^ (sigma - 1))
    (ht : t ∈ Set.Icc 1 L) :
    ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
        mu.real {omega | t < X omega}
      ≤ (2 * t + momentBoostedKernelCoeff sigma * t ^ (sigma + 1)) *
          Real.exp (-(momentBoostedKernelCoeff sigma * t ^ sigma)) := by
  have htail :
      mu.real {omega | t < X omega} ≤ Real.exp (-(t ^ sigma / (2 * sigma))) := by
    have h := hX ht.1
    simpa [upperTailEvent] using h
  have hpref_nonneg :
      0 ≤ (2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t) := by
    have : 0 ≤ t := le_trans zero_le_one ht.1
    positivity
  calc
    ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
          mu.real {omega | t < X omega}
        ≤ ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
            Real.exp (-(t ^ sigma / (2 * sigma))) :=
      mul_le_mul_of_nonneg_left htail hpref_nonneg
    _ ≤ _ := momentBoosted_tail_kernel_pointwise hsigma hsigma_one hl hlL ht

/-- An internal one-variable truncated-MGF reduction.  The second-moment and
large-tail inputs are kept separate so that the moment-boosted kernel may
provide the latter without invoking the generic `Gamma_sigma` triangle
constant. -/
theorem mgf_upperTruncation_le_exp_of_secondMoment_and_tail
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {X : Omega → ℝ} {l L C2 K : ℝ}
    (hXm : Measurable X)
    (hXint : Integrable X mu)
    (hXsq : Integrable (fun omega => |X omega| ^ (2 : ℕ)) mu)
    (hXmean : ∫ omega, X omega ∂mu = 0)
    (hsecond : ∫ omega, |X omega| ^ (2 : ℕ) ∂mu ≤ C2)
    (hl : 0 ≤ l) (hl1 : l ≤ 1) (hL : 1 ≤ L)
    (hlarge : ∫ t in Set.Ioc 1 L,
      ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
        mu.real {omega | t ≤ X omega} ∂volume ≤ K) :
    mgf (upperTruncation X L) mu l ≤
      Real.exp (l ^ (2 : ℕ) * (C2 / 2 + Real.exp 1 / 2 + K / 2)) := by
  let tailIntegrand : ℝ → ℝ := fun t =>
    ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
      mu.real {omega | t ≤ X omega}
  have htail_int : IntegrableOn tailIntegrand (Set.Ioc 0 L) volume :=
    integrableOn_integrand_Ioc_tail (μ := mu) (X := X) (l := l) (L := L)
      hl (le_trans zero_le_one hL)
  have htail_split :
      ∫ t in Set.Ioc 0 L, tailIntegrand t ∂volume =
        ∫ t in Set.Ioc 0 1, tailIntegrand t ∂volume +
          ∫ t in Set.Ioc 1 L, tailIntegrand t ∂volume := by
    have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioc 1 L) := by
      refine Set.disjoint_left.2 fun t ht0 ht1 => ?_
      exact not_lt_of_ge ht0.2 ht1.1
    rw [← Set.Ioc_union_Ioc_eq_Ioc zero_le_one hL]
    exact setIntegral_union hdisj measurableSet_Ioc
      (htail_int.mono_set fun _ ht => ⟨ht.1, le_trans ht.2 hL⟩)
      (htail_int.mono_set fun _ ht => ⟨lt_trans zero_lt_one ht.1, ht.2⟩)
  have hsmall :
      ∫ t in Set.Ioc 0 1, tailIntegrand t ∂volume ≤ Real.exp 1 := by
    simpa [tailIntegrand] using
      integral_Ioc_zero_one_tail_le_exp_one (μ := mu) (X := X) (l := l)
        hXm hl hl1
  have htail_total :
      ∫ t in Set.Ioc 0 L, tailIntegrand t ∂volume ≤ Real.exp 1 + K := by
    rw [htail_split]
    exact add_le_add hsmall hlarge
  calc
    mgf (upperTruncation X L) mu l ≤
        Real.exp ((l ^ (2 : ℕ) / 2) *
          (∫ omega, |X omega| ^ (2 : ℕ) ∂mu +
            ∫ t in Set.Ioc 0 L, tailIntegrand t ∂volume)) := by
      simpa [tailIntegrand] using
        mgf_upperTruncation_le_exp_of_integral_abs_sq_add_integral_Ioc_tail_of_integral_eq_zero
          (μ := mu) (X := X) (l := l) (L := L)
          hXm hXint hXsq hXmean hl (le_trans zero_le_one hL)
    _ ≤ Real.exp ((l ^ (2 : ℕ) / 2) * (C2 + (Real.exp 1 + K))) := by
      apply Real.exp_le_exp.2
      exact mul_le_mul_of_nonneg_left
        (add_le_add hsecond htail_total) (by positivity)
    _ = Real.exp (l ^ (2 : ℕ) * (C2 / 2 + Real.exp 1 / 2 + K / 2)) := by
      congr 1
      ring

/-- A positive dilation transfers the standard stretched-exponential
integrability fact to the coefficient occurring in the boosted kernel. -/
private theorem integrableOn_rpow_mul_exp_neg_boostedCoeff
    {sigma q b : ℝ} (hsigma : 0 < sigma) (hq : -1 < q) (hb : 0 < b) :
    IntegrableOn
      (fun t : ℝ => t ^ q * Real.exp (-(b * t ^ sigma)))
      (Set.Ioi 0) volume := by
  let c : ℝ := b ^ (1 / sigma)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hc_pow : c ^ sigma = b := by
    dsimp [c]
    rw [← Real.rpow_mul hb.le]
    field_simp [hsigma.ne']
    exact Real.rpow_one b
  let f : ℝ → ℝ := fun u => u ^ q * Real.exp (-(u ^ sigma))
  have hf : IntegrableOn f (Set.Ioi 0) volume := by
    convert
      integrableOn_rpow_mul_exp_neg_rpow_of_pos
        (σ := sigma) (p := q + 1) hsigma (by linarith : 0 < q + 1) using 1
    ext u
    simp [f]
  have hscaled :
      IntegrableOn (fun t : ℝ => c ^ (-q) * f (c * t)) (Set.Ioi 0) volume :=
    ((integrableOn_Ioi_comp_mul_left_iff f 0 hc).2 (by simpa using hf)).const_mul _
  refine (integrableOn_congr_fun ?_ measurableSet_Ioi).1 hscaled
  intro t ht
  have ht0 : 0 ≤ t := ht.le
  dsimp [f]
  calc
    c ^ (-q) * ((c * t) ^ q * Real.exp (-((c * t) ^ sigma))) =
        (c ^ (-q) * c ^ q) * t ^ q *
          Real.exp (-(c ^ sigma * t ^ sigma)) := by
      rw [Real.mul_rpow hc.le ht0, Real.mul_rpow hc.le ht0]
      ring
    _ = t ^ q * Real.exp (-(b * t ^ sigma)) := by
      rw [← Real.rpow_add hc, show -q + q = 0 by ring,
        Real.rpow_zero, hc_pow]
      ring

/-- The deterministic integral envelope generated by the boosted tail.  It is
an internal analytic constant, not a stream-level estimate. -/
noncomputable def momentBoostedTailKernelConst (sigma : ℝ) : ℝ :=
  2 * (momentBoostedKernelCoeff sigma ^ (-(1 + 1) / sigma) * (1 / sigma) *
      Real.Gamma ((1 + 1) / sigma)) +
    momentBoostedKernelCoeff sigma *
      (momentBoostedKernelCoeff sigma ^ (-((sigma + 1) + 1) / sigma) *
        (1 / sigma) * Real.Gamma (((sigma + 1) + 1) / sigma))

private theorem integrableOn_momentBoosted_tail_kernel
    {sigma : ℝ} (hsigma : 0 < sigma) :
    IntegrableOn
      (fun t : ℝ =>
        (2 * t + momentBoostedKernelCoeff sigma * t ^ (sigma + 1)) *
          Real.exp (-(momentBoostedKernelCoeff sigma * t ^ sigma)))
      (Set.Ioi 0) volume := by
  have hb := momentBoostedKernelCoeff_pos hsigma
  have hlinear :
      IntegrableOn
        (fun t : ℝ => 2 * (t ^ (1 : ℝ) *
          Real.exp (-(momentBoostedKernelCoeff sigma * t ^ sigma))))
        (Set.Ioi 0) volume :=
    (integrableOn_rpow_mul_exp_neg_boostedCoeff
      (sigma := sigma) (q := 1) (b := momentBoostedKernelCoeff sigma)
      hsigma (by norm_num) hb).const_mul 2
  have hhigher :
      IntegrableOn
        (fun t : ℝ => momentBoostedKernelCoeff sigma *
          (t ^ (sigma + 1) *
            Real.exp (-(momentBoostedKernelCoeff sigma * t ^ sigma))))
        (Set.Ioi 0) volume :=
    (integrableOn_rpow_mul_exp_neg_boostedCoeff
      (sigma := sigma) (q := sigma + 1) (b := momentBoostedKernelCoeff sigma)
      hsigma (by linarith) hb).const_mul _
  refine (integrableOn_congr_fun ?_ measurableSet_Ioi).1 (hlinear.add hhigher)
  intro t _
  simp only [Pi.add_apply, Real.rpow_one]
  ring

private theorem integral_momentBoosted_tail_kernel_eq
    {sigma : ℝ} (hsigma : 0 < sigma) :
    ∫ t in Set.Ioi (0 : ℝ),
        (2 * t + momentBoostedKernelCoeff sigma * t ^ (sigma + 1)) *
          Real.exp (-(momentBoostedKernelCoeff sigma * t ^ sigma)) =
      momentBoostedTailKernelConst sigma := by
  have hb := momentBoostedKernelCoeff_pos hsigma
  have hlinear :
      IntegrableOn
        (fun t : ℝ => 2 * t *
          Real.exp (-(momentBoostedKernelCoeff sigma * t ^ sigma)))
        (Set.Ioi 0) volume := by
    refine (integrableOn_congr_fun ?_ measurableSet_Ioi).1
      ((integrableOn_rpow_mul_exp_neg_boostedCoeff
        (sigma := sigma) (q := 1) (b := momentBoostedKernelCoeff sigma)
        hsigma (by norm_num) hb).const_mul 2)
    intro t _
    simp only [Real.rpow_one]
    ring
  have hhigher :
      IntegrableOn
        (fun t : ℝ => momentBoostedKernelCoeff sigma * t ^ (sigma + 1) *
          Real.exp (-(momentBoostedKernelCoeff sigma * t ^ sigma)))
        (Set.Ioi 0) volume := by
    refine (integrableOn_congr_fun ?_ measurableSet_Ioi).1
      ((integrableOn_rpow_mul_exp_neg_boostedCoeff
        (sigma := sigma) (q := sigma + 1) (b := momentBoostedKernelCoeff sigma)
        hsigma (by linarith) hb).const_mul (momentBoostedKernelCoeff sigma))
    intro t _
    ring
  calc
    ∫ t in Set.Ioi (0 : ℝ),
        (2 * t + momentBoostedKernelCoeff sigma * t ^ (sigma + 1)) *
          Real.exp (-(momentBoostedKernelCoeff sigma * t ^ sigma)) =
      (∫ t in Set.Ioi (0 : ℝ),
        2 * t * Real.exp (-(momentBoostedKernelCoeff sigma * t ^ sigma))) +
        ∫ t in Set.Ioi (0 : ℝ),
          momentBoostedKernelCoeff sigma * t ^ (sigma + 1) *
            Real.exp (-(momentBoostedKernelCoeff sigma * t ^ sigma)) := by
          rw [← integral_add hlinear hhigher]
          refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
    _ =
      2 * (∫ t in Set.Ioi (0 : ℝ),
        t ^ (1 : ℝ) *
          Real.exp (-momentBoostedKernelCoeff sigma * t ^ sigma)) +
        momentBoostedKernelCoeff sigma * (∫ t in Set.Ioi (0 : ℝ),
          t ^ (sigma + 1) *
            Real.exp (-momentBoostedKernelCoeff sigma * t ^ sigma)) := by
          congr 1
          · calc
              ∫ t in Set.Ioi (0 : ℝ),
                  2 * t * Real.exp (-(momentBoostedKernelCoeff sigma * t ^ sigma)) =
                ∫ t in Set.Ioi (0 : ℝ),
                  2 * (t ^ (1 : ℝ) *
                    Real.exp (-momentBoostedKernelCoeff sigma * t ^ sigma)) := by
                      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by
                        rw [Real.rpow_one]
                        ring_nf
              _ = _ := by rw [integral_const_mul]
          · calc
              ∫ t in Set.Ioi (0 : ℝ),
                  momentBoostedKernelCoeff sigma * t ^ (sigma + 1) *
                    Real.exp (-(momentBoostedKernelCoeff sigma * t ^ sigma)) =
                ∫ t in Set.Ioi (0 : ℝ),
                  momentBoostedKernelCoeff sigma *
                    (t ^ (sigma + 1) *
                      Real.exp (-momentBoostedKernelCoeff sigma * t ^ sigma)) := by
                      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring_nf
              _ = _ := by rw [integral_const_mul]
    _ = momentBoostedTailKernelConst sigma := by
      rw [integral_rpow_mul_exp_neg_mul_rpow
        (p := sigma) (q := 1) (b := momentBoostedKernelCoeff sigma)
        hsigma (by norm_num) hb,
        integral_rpow_mul_exp_neg_mul_rpow
          (p := sigma) (q := sigma + 1) (b := momentBoostedKernelCoeff sigma)
          hsigma (by linarith) hb]
      rfl

private theorem momentBoostedTailKernelConst_eq
    {sigma : ℝ} (hsigma : 0 < sigma) :
    momentBoostedTailKernelConst sigma =
      momentBoostedKernelCoeff sigma ^ (-(2 / sigma)) *
        (1 + 1 / sigma) * Real.Gamma (2 / sigma + 1) := by
  let b := momentBoostedKernelCoeff sigma
  have hb : 0 < b := by
    simpa [b] using momentBoostedKernelCoeff_pos hsigma
  have hpow :
      b ^ (-((sigma + 1) + 1) / sigma) =
        b⁻¹ * b ^ (-(2 / sigma)) := by
    have hexp : -((sigma + 1) + 1) / sigma = -1 + -(2 / sigma) := by
      field_simp [hsigma.ne']
      ring
    have hnegone : b ^ (-1 : ℝ) = b⁻¹ := by
      rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_one]
    rw [hexp, Real.rpow_add hb, hnegone]
  have hgamma :
      Real.Gamma (2 / sigma + 1) =
        (2 / sigma) * Real.Gamma (2 / sigma) := by
    rw [Real.Gamma_add_one (by positivity : 2 / sigma ≠ 0)]
  change
    2 * (b ^ (-(1 + 1) / sigma) * (1 / sigma) *
        Real.Gamma ((1 + 1) / sigma)) +
      b * (b ^ (-((sigma + 1) + 1) / sigma) * (1 / sigma) *
        Real.Gamma (((sigma + 1) + 1) / sigma)) =
      b ^ (-(2 / sigma)) * (1 + 1 / sigma) *
        Real.Gamma (2 / sigma + 1)
  rw [show (1 + 1) / sigma = 2 / sigma by ring,
    show -(1 + 1) / sigma = -(2 / sigma) by ring,
    show ((sigma + 1) + 1) / sigma = 2 / sigma + 1 by
      field_simp [hsigma.ne']
      ring,
    hpow]
  calc
    2 * (b ^ (-(2 / sigma)) * (1 / sigma) *
        Real.Gamma (2 / sigma)) +
      b * (b⁻¹ * b ^ (-(2 / sigma)) * (1 / sigma) *
        Real.Gamma (2 / sigma + 1)) =
      b ^ (-(2 / sigma)) * ((2 / sigma) * Real.Gamma (2 / sigma)) +
        b ^ (-(2 / sigma)) * (1 / sigma) *
          Real.Gamma (2 / sigma + 1) := by
            field_simp [hb.ne', hsigma.ne']
    _ = b ^ (-(2 / sigma)) * Real.Gamma (2 / sigma + 1) +
        b ^ (-(2 / sigma)) * (1 / sigma) *
          Real.Gamma (2 / sigma + 1) := by rw [← hgamma]
    _ = _ := by ring

/-- The boosted tail kernel has a fixed-base envelope.  Crucially, the
coefficient `1 / (4 sigma)` cancels the `sigma⁻¹` in the Gamma integral before
the elementary exponential factors are estimated. -/
theorem momentBoostedTailKernelConst_le_fixedBase
    {sigma : ℝ} (hsigma : 0 < sigma) (hsigma_one : sigma < 1) :
    momentBoostedTailKernelConst sigma ≤ (48 : ℝ) ^ (2 / sigma) := by
  let b := momentBoostedKernelCoeff sigma
  have hb : 0 < b := by
    simpa [b] using momentBoostedKernelCoeff_pos hsigma
  have hinv : b⁻¹ = 4 * sigma := by
    dsimp [b, momentBoostedKernelCoeff]
    field_simp [hsigma.ne']
  have ha_pos : 0 < 2 / sigma := by positivity
  have ha_nonneg : 0 ≤ 2 / sigma := ha_pos.le
  have hfactor_pos : 0 < 1 + 1 / sigma := by positivity
  have hgamma :
      Real.Gamma (2 / sigma + 1) ≤
        2 * ((2 * (2 / sigma)) / Real.exp 1) ^ (2 / sigma) := by
    exact gamma_add_one_le_two_mul_rpow_div_exp (r := 2 / sigma) ha_pos
  have hcombine :
      b ^ (-(2 / sigma)) *
          (2 * ((2 * (2 / sigma)) / Real.exp 1) ^ (2 / sigma)) =
        2 * (16 / Real.exp 1) ^ (2 / sigma) := by
    have hbase : (2 * (2 / sigma)) / Real.exp 1 =
        4 / (sigma * Real.exp 1) := by
      field_simp [hsigma.ne']
      ring
    rw [Real.rpow_neg_eq_inv_rpow, hinv, hbase]
    calc
      (4 * sigma) ^ (2 / sigma) *
          (2 * (4 / (sigma * Real.exp 1)) ^ (2 / sigma)) =
        2 * ((4 * sigma) ^ (2 / sigma) *
          (4 / (sigma * Real.exp 1)) ^ (2 / sigma)) := by ring
      _ = 2 * ((4 * sigma) * (4 / (sigma * Real.exp 1))) ^ (2 / sigma) := by
        rw [← Real.mul_rpow (by positivity) (by positivity)]
      _ = 2 * (16 / Real.exp 1) ^ (2 / sigma) := by
        congr 2
        field_simp [hsigma.ne']
        norm_num
  have hone_inv : 1 ≤ 1 / sigma := by
    simpa [one_div] using (one_le_inv₀ hsigma).2 hsigma_one.le
  have htwo_exp : 2 ≤ Real.exp (1 / sigma) := by
    exact (lt_of_lt_of_le
      (lt_trans (by norm_num) Real.exp_one_gt_d9)
      (Real.exp_le_exp.2 hone_inv)).le
  have hfactor_exp : 1 + 1 / sigma ≤ Real.exp (1 / sigma) :=
    by simpa [add_comm] using Real.add_one_le_exp (1 / sigma)
  have hscalar : 2 * (1 + 1 / sigma) ≤ Real.exp (2 / sigma) := by
    calc
      2 * (1 + 1 / sigma) ≤ Real.exp (1 / sigma) * Real.exp (1 / sigma) :=
        mul_le_mul htwo_exp hfactor_exp hfactor_pos.le (Real.exp_pos _).le
      _ = Real.exp (2 / sigma) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hratio : 16 / Real.exp 1 ≤ (16 : ℝ) := by
    rw [div_le_iff₀ (Real.exp_pos 1)]
    nlinarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)]
  have hpower :
      (16 / Real.exp 1) ^ (2 / sigma) ≤ 16 ^ (2 / sigma) :=
    Real.rpow_le_rpow (by positivity) hratio ha_nonneg
  have hexp_rpow : Real.exp (2 / sigma) =
      (Real.exp 1) ^ (2 / sigma) := by
    rw [Real.exp_one_rpow]
  have he_le_three : Real.exp 1 ≤ (3 : ℝ) :=
    Real.exp_one_lt_d9.le.trans (by norm_num)
  calc
    momentBoostedTailKernelConst sigma =
        b ^ (-(2 / sigma)) * (1 + 1 / sigma) *
          Real.Gamma (2 / sigma + 1) := by
            simpa [b] using momentBoostedTailKernelConst_eq hsigma
    _ ≤ b ^ (-(2 / sigma)) * (1 + 1 / sigma) *
        (2 * ((2 * (2 / sigma)) / Real.exp 1) ^ (2 / sigma)) := by
          calc
            b ^ (-(2 / sigma)) * (1 + 1 / sigma) *
                Real.Gamma (2 / sigma + 1) =
              b ^ (-(2 / sigma)) *
                ((1 + 1 / sigma) * Real.Gamma (2 / sigma + 1)) := by ring
            _ ≤ b ^ (-(2 / sigma)) *
                ((1 + 1 / sigma) *
                  (2 * ((2 * (2 / sigma)) / Real.exp 1) ^ (2 / sigma))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hgamma hfactor_pos.le)
                (Real.rpow_nonneg hb.le _)
            _ = _ := by ring
    _ = (1 + 1 / sigma) *
        (b ^ (-(2 / sigma)) *
          (2 * ((2 * (2 / sigma)) / Real.exp 1) ^ (2 / sigma))) := by ring
    _ = (1 + 1 / sigma) * (2 * (16 / Real.exp 1) ^ (2 / sigma)) := by
      rw [hcombine]
    _ = (2 * (1 + 1 / sigma)) * (16 / Real.exp 1) ^ (2 / sigma) := by ring
    _ ≤ Real.exp (2 / sigma) * (16 / Real.exp 1) ^ (2 / sigma) :=
      mul_le_mul_of_nonneg_right hscalar (Real.rpow_nonneg (by positivity) _)
    _ ≤ Real.exp (2 / sigma) * 16 ^ (2 / sigma) :=
      mul_le_mul_of_nonneg_left hpower (Real.exp_pos _).le
    _ = (16 * Real.exp 1) ^ (2 / sigma) := by
      rw [hexp_rpow, mul_comm (Real.exp 1 ^ (2 / sigma)),
        ← Real.mul_rpow (by positivity) (Real.exp_pos _).le]
    _ ≤ (16 * 3) ^ (2 / sigma) := by
      exact Real.rpow_le_rpow (by positivity)
        (mul_le_mul_of_nonneg_left he_le_three (by norm_num)) ha_nonneg
    _ = (48 : ℝ) ^ (2 / sigma) := by norm_num

/-- The strengthened upper tail supplies the large-interval input to the
truncated-MGF estimate with a fixed base, uniformly in `sigma ∈ (0,1)`. -/
theorem integral_Ioc_one_L_tail_le_momentBoosted_fixedBase
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {X : Omega → ℝ} {sigma l L : ℝ}
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hX : IsBigOWith mu (momentBoostedGammaSigma sigma) X 1)
    (hl : 0 ≤ l) (hL : 1 ≤ L)
    (hlL : l ≤ momentBoostedKernelCoeff sigma * L ^ (sigma - 1)) :
    ∫ t in Set.Ioc 1 L,
        ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
          mu.real {omega | t ≤ X omega} ∂volume ≤
      (48 : ℝ) ^ (2 / sigma) := by
  let f : ℝ → ℝ := fun t =>
    ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
      mu.real {omega | t ≤ X omega}
  let g : ℝ → ℝ := fun t =>
    (2 * t + momentBoostedKernelCoeff sigma * t ^ (sigma + 1)) *
      Real.exp (-(momentBoostedKernelCoeff sigma * t ^ sigma))
  have htail_eq :
      (fun t : ℝ => mu.real {omega | t ≤ X omega})
          =ᵐ[volume.restrict (Set.Ioc 1 L)]
        fun t => mu.real {omega | t < X omega} := by
    refine (MeasureTheory.meas_le_ae_eq_meas_lt
      mu (volume.restrict (Set.Ioc 1 L)) X).mono ?_
    intro t ht
    exact congrArg ENNReal.toReal ht
  have hf : IntegrableOn f (Set.Ioc 1 L) volume :=
    (integrableOn_integrand_Ioc_tail (μ := mu) (X := X) (l := l) (L := L)
      hl (le_trans zero_le_one hL)).mono_set (by
        intro t ht
        exact ⟨lt_trans zero_lt_one ht.1, ht.2⟩)
  have hg_Ioi : IntegrableOn g (Set.Ioi 0) volume := by
    simpa [g] using integrableOn_momentBoosted_tail_kernel hsigma
  have hg : IntegrableOn g (Set.Ioc 1 L) volume :=
    hg_Ioi.mono_set (by
      intro t ht
      exact lt_trans zero_lt_one ht.1)
  have hbound : ∀ᵐ t ∂volume.restrict (Set.Ioc 1 L), f t ≤ g t := by
    filter_upwards [htail_eq, self_mem_ae_restrict measurableSet_Ioc]
      with t htail ht
    have ht_mem : t ∈ Set.Icc 1 L := ⟨ht.1.le, ht.2⟩
    change
      ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
          mu.real {omega | t ≤ X omega} ≤ g t
    rw [htail]
    simpa [g] using
      momentBoosted_tail_integrand_pointwise_of_isBigOWith
        hsigma hsigma_one hX hl hlL ht_mem
  have hmono :
      ∫ t in Set.Ioc 1 L, f t ∂volume ≤
        ∫ t in Set.Ioc 1 L, g t ∂volume :=
    setIntegral_mono_on_ae hf hg measurableSet_Ioc
      ((ae_restrict_iff' measurableSet_Ioc).1 hbound)
  have hg_nonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] g := by
    refine (ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun t ht => ?_)
    dsimp [g]
    exact mul_nonneg
      (add_nonneg (mul_nonneg (by norm_num) ht.le)
        (mul_nonneg (momentBoostedKernelCoeff_pos hsigma).le
          (Real.rpow_nonneg ht.le _)))
      (Real.exp_nonneg _)
  calc
    ∫ t in Set.Ioc 1 L,
        ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
          mu.real {omega | t ≤ X omega} ∂volume =
      ∫ t in Set.Ioc 1 L, f t ∂volume := rfl
    _ ≤ ∫ t in Set.Ioc 1 L, g t ∂volume := hmono
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), g t ∂volume :=
      setIntegral_mono_set hg_Ioi hg_nonneg (by
        exact (show Set.Ioc (1 : ℝ) L ⊆ Set.Ioi 0 by
          intro t ht
          exact lt_trans zero_lt_one ht.1).eventuallyLE)
    _ = momentBoostedTailKernelConst sigma := by
      simpa [g] using integral_momentBoosted_tail_kernel_eq hsigma
    _ ≤ (48 : ℝ) ^ (2 / sigma) :=
      momentBoostedTailKernelConst_le_fixedBase hsigma hsigma_one

end

end Algsuperdiff.Section3.Provider.Stream
