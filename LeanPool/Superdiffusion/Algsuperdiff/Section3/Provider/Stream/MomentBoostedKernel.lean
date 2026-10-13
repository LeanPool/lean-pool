/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementLp

/-!
# MomentBoostedKernel

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Internal moment-boosted tail kernel for stream-increment masses

This module is internal probability infrastructure for the proof of
`e.kl.bounds.large` (ABK26).  It is not a source-facing replacement for that
node and does not state a large-cube conclusion.

The usual conversion from `Gamma_sigma` moment growth to a weak-tail witness
throws away the factor `sigma⁻¹` available when the Markov exponent is chosen
to be `t^sigma`.  Retaining that factor gives the one-sided tail

`exp (t^sigma / (2 sigma))⁻¹`.

For `sigma = 2 / p`, its scale is a fixed base to the power `p / 2`, rather
than the forbidden `p^12` inflation from the generic `Gamma_sigma` triangle
route.  The later finite-range colored truncated-MGF argument consumes both
the strengthened tail and the genuine centered second-moment estimate proved
here.

No frozen declaration is imported.

References:

* ABK26 and Proposition `p.concentration`.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- The strengthened one-sided tail naturally supplied by all-real
`Gamma_sigma` moment growth.  It is an internal kernel, not the source's
`Gamma_sigma` tail function. -/
noncomputable def momentBoostedGammaSigma (sigma : ℝ) : ℝ → ℝ :=
  fun t => Real.exp (t ^ sigma / (2 * sigma))

@[simp] theorem momentBoostedGammaSigma_inv (sigma t : ℝ) :
    (momentBoostedGammaSigma sigma t)⁻¹ =
      Real.exp (-(t ^ sigma / (2 * sigma))) := by
  simp [momentBoostedGammaSigma, Real.exp_neg]

/-- A strengthened kernel tail controls the ordinary `Gamma_sigma` tail at a
fixed factor-four enlargement whenever `0 < sigma ≤ 1`.  This conversion is
used only for the bounded partition-window branch; the finite-family route
retains the sharper kernel until after coloring. -/
theorem isBigOWith_gammaSigma_of_momentBoostedGammaSigma
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {X : Omega → ℝ} {A sigma : ℝ}
    (hsigma : 0 < sigma) (hsigma_one : sigma ≤ 1)
    (h : IndependentSums.IsBigOWith mu (momentBoostedGammaSigma sigma) X A) :
    IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) X (4 * A) := by
  rw [IndependentSums.isBigOWith_gammaSigma_iff]
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hfactor : 2 * sigma ≤ (4 : ℝ) ^ sigma := by
    by_cases hhalf : sigma ≤ (1 : ℝ) / 2
    · calc
        2 * sigma ≤ 1 := by linarith
        _ ≤ (4 : ℝ) ^ sigma :=
          Real.one_le_rpow (by norm_num) hsigma.le
    · have hhalf' : (1 : ℝ) / 2 ≤ sigma := le_of_not_ge hhalf
      calc
        2 * sigma ≤ 2 := by linarith
        _ = (4 : ℝ) ^ ((1 : ℝ) / 2) := by
          rw [← Real.sqrt_eq_rpow]
          rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num,
            Real.sqrt_sq_eq_abs]
          norm_num
        _ ≤ (4 : ℝ) ^ sigma :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hhalf'
  have hpow : t ^ sigma ≤ (4 * t) ^ sigma / (2 * sigma) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hsigma)).2
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) ht0.le]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg ht0.le _)
  calc
    mu.real (IndependentSums.upperTailEvent X ((4 * A) * t)) =
        mu.real (IndependentSums.upperTailEvent X (A * (4 * t))) := by ring_nf
    _ ≤ Real.exp (-((4 * t) ^ sigma / (2 * sigma))) := by
      simpa only [momentBoostedGammaSigma_inv] using h (by nlinarith)
    _ ≤ Real.exp (-(t ^ sigma)) :=
      Real.exp_le_exp.2 (neg_le_neg hpow)

/-- All-real `Gamma_sigma` moment growth gives the strengthened one-sided
tail at scale `2^(1/sigma) M`. -/
theorem isBigOWith_momentBoostedGammaSigma_of_momentGrowth
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {Y : Omega → ℝ} {M sigma : ℝ}
    (hsigma : 0 < sigma) (hM : 0 < M) (hY_nonneg : ∀ omega, 0 ≤ Y omega)
    (hY : IndependentSums.HasGammaMomentGrowthWith mu sigma Y M) :
    IndependentSums.IsBigOWith mu (momentBoostedGammaSigma sigma) Y
      ((2 : ℝ) ^ sigma⁻¹ * M) := by
  intro t ht
  let r : ℝ := t ^ sigma
  have hr_one : 1 ≤ r := by
    dsimp only [r]
    exact Real.one_le_rpow ht hsigma.le
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr_one
  obtain ⟨hr_int, hr_bound⟩ := hY hr_one
  have hscale_pos : 0 < ((2 : ℝ) ^ sigma⁻¹ * M) * t := by positivity
  have hYpow_nonneg : 0 ≤ᵐ[mu] fun omega => Y omega ^ r :=
    Filter.Eventually.of_forall fun omega => Real.rpow_nonneg (hY_nonneg omega) _
  have hr_int' : Integrable (fun omega => Y omega ^ r) mu := by
    simpa only [abs_of_nonneg (hY_nonneg _)] using hr_int
  have hr_bound' :
      ∫ omega, Y omega ^ r ∂mu ≤ (M * r ^ sigma⁻¹) ^ r := by
    simpa only [abs_of_nonneg (hY_nonneg _)] using hr_bound
  have hsubset :
      IndependentSums.upperTailEvent Y (((2 : ℝ) ^ sigma⁻¹ * M) * t) ⊆
        {omega | ((((2 : ℝ) ^ sigma⁻¹ * M) * t) ^ r) ≤ Y omega ^ r} := by
    intro omega homega
    exact le_of_lt ((Real.rpow_lt_rpow_iff hscale_pos.le
      (hY_nonneg omega) hr_pos).2 homega)
  have hmarkov :=
    mul_meas_ge_le_integral_of_nonneg (μ := mu) (f := fun omega => Y omega ^ r)
      hYpow_nonneg hr_int' ((((2 : ℝ) ^ sigma⁻¹ * M) * t) ^ r)
  have htail_aux :
      mu.real {omega | ((((2 : ℝ) ^ sigma⁻¹ * M) * t) ^ r) ≤ Y omega ^ r} ≤
        ((M * r ^ sigma⁻¹) ^ r) /
          ((((2 : ℝ) ^ sigma⁻¹ * M) * t) ^ r) := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hscale_pos _)]
    simpa [mul_comm] using hmarkov.trans hr_bound'
  have hr_root : r ^ sigma⁻¹ = t := by
    dsimp only [r]
    calc
      (t ^ sigma) ^ sigma⁻¹ = t ^ (sigma * sigma⁻¹) := by
        rw [← Real.rpow_mul (le_trans zero_le_one ht)]
      _ = t := by rw [mul_inv_cancel₀ hsigma.ne', Real.rpow_one]
  have hMt_pos : 0 < M * t := by positivity
  have htwo_pow_pos : 0 < (2 : ℝ) ^ sigma⁻¹ := Real.rpow_pos_of_pos (by norm_num) _
  have hratio :
      ((M * r ^ sigma⁻¹) ^ r) /
          ((((2 : ℝ) ^ sigma⁻¹ * M) * t) ^ r) =
        Real.exp (-(Real.log 2 / sigma) * r) := by
    rw [hr_root]
    have hden : (((2 : ℝ) ^ sigma⁻¹ * M) * t) =
        (2 : ℝ) ^ sigma⁻¹ * (M * t) := by ring
    rw [hden, Real.mul_rpow htwo_pow_pos.le hMt_pos.le]
    rw [div_eq_mul_inv, mul_inv_rev]
    rw [← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hMt_pos _).ne', one_mul]
    rw [← Real.rpow_neg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ sigma⁻¹)]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    field_simp [hsigma.ne']
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hexp :
      Real.exp (-(Real.log 2 / sigma) * r) ≤
        Real.exp (-(r / (2 * sigma))) := by
    apply Real.exp_le_exp.2
    have hdiv : (1 / 2 : ℝ) / sigma ≤ Real.log 2 / sigma :=
      div_le_div_of_nonneg_right hlog hsigma.le
    have hmul := mul_le_mul_of_nonneg_right hdiv hr_pos.le
    have heq : (1 / 2 / sigma) * r = r / (2 * sigma) := by ring
    rw [heq] at hmul
    simpa only [neg_mul] using neg_le_neg hmul
  calc
    mu.real (IndependentSums.upperTailEvent Y (((2 : ℝ) ^ sigma⁻¹ * M) * t))
        ≤ mu.real {omega | ((((2 : ℝ) ^ sigma⁻¹ * M) * t) ^ r) ≤ Y omega ^ r} :=
          measureReal_mono hsubset
    _ ≤ ((M * r ^ sigma⁻¹) ^ r) /
          ((((2 : ℝ) ^ sigma⁻¹ * M) * t) ^ r) := htail_aux
    _ = Real.exp (-(Real.log 2 / sigma) * r) := hratio
    _ ≤ Real.exp (-(r / (2 * sigma))) := hexp
    _ = (momentBoostedGammaSigma sigma t)⁻¹ := by
      rw [momentBoostedGammaSigma_inv]

/-- The local scale for the later moment-boosted finite-range argument. -/
def streamIncrementLpMomentBoostScale (M : ABKModel d) (p : ℝ) (n m : ℤ) : ℝ :=
  (2 : ℝ) ^ (p / 2) *
    ((IndependentSums.gammaMomentConst 2 * streamPointScale M n m) ^ p *
      p ^ (p / 2))

theorem streamIncrementLpMomentBoostScale_pos (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p)
    {n m : ℤ} (hnm : n < m) : 0 < streamIncrementLpMomentBoostScale M p n m := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  rw [streamIncrementLpMomentBoostScale]
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (mul_pos
      (Real.rpow_pos_of_pos
        (mul_pos (IndependentSums.gammaMomentConst_pos (by norm_num))
          (streamPointScale_pos M hnm)) _)
      (Real.rpow_pos_of_pos hp0 _))

/-- The actual local stream-increment mass has the strengthened centered
one-sided tail, uniformly in the observation scale `l`. -/
theorem isBigOWith_centered_streamIncrementLpMass_momentBoosted
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) {n m : ℤ} (hnm : n < m) (l : ℤ) :
    IndependentSums.IsBigOWith M.P.toMeasure (momentBoostedGammaSigma (2 / p))
      (fun omega => streamIncrementLpMass p l n m omega -
        ∫ omega', streamIncrementLpMass p l n m omega' ∂M.P.toMeasure)
      (streamIncrementLpMomentBoostScale M p n m) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hsigma : 0 < 2 / p := by positivity
  have hbase := isBigOWith_momentBoostedGammaSigma_of_momentGrowth
    (mu := M.P.toMeasure) (Y := streamIncrementLpMass p l n m)
    (M := (IndependentSums.gammaMomentConst 2 * streamPointScale M n m) ^ p *
      p ^ (p / 2)) (sigma := 2 / p) hsigma ?_ (fun omega =>
        streamIncrementLpMass_nonneg p l n m omega)
      (hasGammaMomentGrowthWith_streamIncrementLpMass M hp hnm l)
  · have hmean : 0 ≤ ∫ omega, streamIncrementLpMass p l n m omega ∂M.P.toMeasure :=
      integral_nonneg fun omega => streamIncrementLpMass_nonneg p l n m omega
    have hle : ∀ omega : Cutoff.ShellSeq d, streamIncrementLpMass p l n m omega -
        ∫ omega', streamIncrementLpMass p l n m omega' ∂M.P.toMeasure ≤
        streamIncrementLpMass p l n m omega := by
      intro omega
      linarith
    have hscale : (2 : ℝ) ^ (2 / p)⁻¹ *
        ((IndependentSums.gammaMomentConst 2 * streamPointScale M n m) ^ p *
          p ^ (p / 2)) = streamIncrementLpMomentBoostScale M p n m := by
      rw [streamIncrementLpMomentBoostScale]
      congr 2
      field_simp
    rw [hscale] at hbase
    exact hbase.of_le hle
  · exact mul_pos (Real.rpow_pos_of_pos
      (mul_pos (IndependentSums.gammaMomentConst_pos (by norm_num))
        (streamPointScale_pos M hnm)) _) (Real.rpow_pos_of_pos hp0 _)

/-- The same local mass has a genuine centered second-moment scale.  This is
the variance input to the finite-range truncated-MGF proof, not an extra
premise of the source-facing large-cube statement. -/
theorem integrable_and_integral_centered_streamIncrementLpMass_sq_le
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) {n m : ℤ} (hnm : n < m) (l : ℤ) :
    Integrable (fun omega => (streamIncrementLpMass p l n m omega -
      ∫ omega', streamIncrementLpMass p l n m omega' ∂M.P.toMeasure) ^ (2 : ℕ))
      M.P.toMeasure ∧
      ∫ omega, (streamIncrementLpMass p l n m omega -
        ∫ omega', streamIncrementLpMass p l n m omega' ∂M.P.toMeasure) ^ (2 : ℕ)
          ∂M.P.toMeasure ≤ (streamIncrementLpMomentBoostScale M p n m) ^ (2 : ℕ) := by
  let X : Cutoff.ShellSeq d → ℝ := streamIncrementLpMass p l n m
  let V : ℝ := streamIncrementLpMomentBoostScale M p n m
  have hXint : Integrable X M.P.toMeasure := by
    simpa only [X] using integrable_streamIncrementLpMass M hp hnm l
  have hXmeas : AEStronglyMeasurable X M.P.toMeasure := hXint.aestronglyMeasurable
  have hmoment := hasGammaMomentGrowthWith_streamIncrementLpMass M hp hnm l
  have htwo := hmoment (show (1 : ℝ) ≤ 2 by norm_num)
  have habs : (fun omega => |X omega| ^ (2 : ℝ)) = fun omega => X omega ^ (2 : ℕ) := by
    funext omega
    rw [abs_of_nonneg (by simpa only [X] using streamIncrementLpMass_nonneg p l n m omega)]
    rw [Real.rpow_two]
  have hXsq : Integrable (fun omega => X omega ^ (2 : ℕ)) M.P.toMeasure := by
    rw [← habs]
    exact htwo.1
  have hrawSq : ∫ omega, X omega ^ (2 : ℕ) ∂M.P.toMeasure ≤ V ^ (2 : ℕ) := by
    have hsigma : ((2 : ℝ) / p)⁻¹ = p / 2 := by
      have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
      field_simp
    rw [← habs]
    have hscaleSq :
        (((IndependentSums.gammaMomentConst 2 * streamPointScale M n m) ^ p *
          p ^ (p / 2)) * 2 ^ ((2 : ℝ) / p)⁻¹) ^ (2 : ℝ) = V ^ (2 : ℕ) := by
      dsimp only [V]
      rw [hsigma, streamIncrementLpMomentBoostScale, Real.rpow_two]
      ring
    exact htwo.2.trans_eq hscaleSq
  have hXmem : MemLp X 2 M.P.toMeasure :=
    (memLp_two_iff_integrable_sq hXmeas).mpr hXsq
  let Z : Cutoff.ShellSeq d → ℝ := fun omega => X omega - ∫ omega', X omega' ∂M.P.toMeasure
  have hZint : Integrable (fun omega => Z omega ^ (2 : ℕ)) M.P.toMeasure :=
    (hXmem.sub (memLp_const _)).integrable_sq
  refine ⟨?_, ?_⟩
  · simpa only [X, Z] using hZint
  · calc
      ∫ omega, (streamIncrementLpMass p l n m omega -
          ∫ omega', streamIncrementLpMass p l n m omega' ∂M.P.toMeasure) ^ (2 : ℕ)
          ∂M.P.toMeasure = ProbabilityTheory.variance X M.P.toMeasure := by
            symm
            simpa only [X] using ProbabilityTheory.variance_eq_integral hXmeas.aemeasurable
      _ ≤ ∫ omega, X omega ^ (2 : ℕ) ∂M.P.toMeasure :=
        ProbabilityTheory.variance_le_expectation_sq hXmeas
      _ ≤ V ^ (2 : ℕ) := hrawSq

end

end Algsuperdiff.Section3.Provider.Stream
