/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeRenormalizedMeasurability
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeRenormalizedFamily
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangePoweredGauge
public import LeanPool.HighContrastHomogenization.Provider.Quenched.CoupledMixingScaleDecay

/-!
# High-contrast homogenization: Provider.Quenched.RenormalizedRadiusGauge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# A gauge for the normalized renormalization radius

The shifted triadic tail of the renormalization radius is converted here into
an ordinary source-tail estimate.  Below the buffer scale the gauge is one;
above it the powered finite-range gauge is read in buffer units.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory IndependentSums

noncomputable section

variable {d : Nat}

/-- The source gauge of the renormalization radius after division by its base
triadic scale. -/
@[expose]
def renormalizedRadiusGauge (d : Nat) (mu : Real) (b : Nat) : Real -> Real :=
  fun t => if t < (3 : Real) ^ (b + 1) then 1
    else frPoweredGauge d mu (t / (3 : Real) ^ (b + 1))

/-- A growth witness for `renormalizedRadiusGauge`. -/
@[expose]
def renormalizedRadiusGrowthWitness (d : Nat) (mu : Real) (b : Nat) : Real :=
  (3 : Real) ^ (b + 1) * frPoweredGrowthWitness d mu

theorem admissiblePsi_renormalizedRadiusGauge (d : Nat) {mu : Real}
    (hmu : 0 < mu) (b : Nat) :
    AdmissiblePsi (renormalizedRadiusGauge d mu b) := by
  let c : Real := (3 : Real) ^ (b + 1)
  have hc : 0 < c := by positivity
  have hraw := admissiblePsi_frPoweredGauge d hmu
  constructor
  · intro s hs t ht hst
    simp only [Set.mem_Ici] at hs ht
    by_cases hsc : s < (3 : Real) ^ (b + 1)
    · by_cases htc : t < (3 : Real) ^ (b + 1)
      · simp only [renormalizedRadiusGauge, ite_eq_left hsc, ite_eq_left htc]
        exact le_rfl
      · simp only [renormalizedRadiusGauge, ite_eq_left hsc, ite_eq_right htc]
        exact hraw.2 (div_nonneg ht hc.le)
    · have htc : ¬ t < (3 : Real) ^ (b + 1) :=
        fun h => hsc (lt_of_le_of_lt hst h)
      simp only [renormalizedRadiusGauge, ite_eq_right hsc, ite_eq_right htc]
      exact hraw.1 (div_nonneg hs hc.le) (div_nonneg ht hc.le)
        (div_le_div_of_nonneg_right hst hc.le)
  · intro t ht
    simp only [renormalizedRadiusGauge]
    split_ifs
    · exact le_rfl
    · exact (admissiblePsi_frPoweredGauge d hmu).2 (div_nonneg ht (by positivity))

theorem one_lt_renormalizedRadiusGrowthWitness (d : Nat) {mu : Real}
    (hmu : 0 < mu) (b : Nat) :
    1 < renormalizedRadiusGrowthWitness d mu b := by
  have hc : (1 : Real) <= (3 : Real) ^ (b + 1) := one_le_pow₀ (by norm_num)
  have hK : (3 : Real) <= frPoweredGrowthWitness d mu :=
    three_le_frPoweredGrowthWitness d hmu
  rw [renormalizedRadiusGrowthWitness]
  nlinarith only [hc, hK]

theorem hasPsiGrowth_renormalizedRadiusGauge (d : Nat) {mu : Real}
    (hmu : 0 < mu) (b : Nat) :
    HasPsiGrowth (renormalizedRadiusGauge d mu b)
      (renormalizedRadiusGrowthWitness d mu b) := by
  intro t ht
  let c : Real := (3 : Real) ^ (b + 1)
  let K : Real := frPoweredGrowthWitness d mu
  have hc : 1 <= c := one_le_pow₀ (by norm_num)
  have hK : 3 <= K := three_le_frPoweredGrowthWitness d hmu
  have hct : c <= c * K * t := by
    have hKt : 1 <= K * t := by nlinarith only [hK, ht]
    simpa only [mul_one, mul_assoc] using
      (mul_le_mul_of_nonneg_left hKt (zero_le_one.trans hc))
  have hnot : ¬ (c * K * t < c) := not_lt_of_ge hct
  rw [renormalizedRadiusGrowthWitness]
  simp only [renormalizedRadiusGauge]
  rw [ite_eq_right hnot]
  have harg : c * K * t / c = K * t := by field_simp [ne_of_gt (zero_lt_one.trans_le hc)]
  rw [harg]
  by_cases htc : t < c
  · rw [ite_eq_left htc]
    have hraw := hasPsiGrowth_frPoweredGauge d hmu ht
    have hrawone : 1 <= frPoweredGauge d mu t :=
      (admissiblePsi_frPoweredGauge d hmu).2 (zero_le_one.trans ht)
    exact (mul_le_mul_of_nonneg_left hrawone (zero_le_one.trans ht)).trans hraw
  · rw [ite_eq_right htc]
    have hdiv : t / c <= t := div_le_self (zero_le_one.trans ht) hc
    have hmono := (admissiblePsi_frPoweredGauge d hmu).1
      (div_nonneg (zero_le_one.trans ht) (zero_le_one.trans hc))
      (zero_le_one.trans ht) hdiv
    exact (mul_le_mul_of_nonneg_left hmono (zero_le_one.trans ht)).trans
      (hasPsiGrowth_frPoweredGauge d hmu ht)

private theorem buffer_le_ceiling {t : Real} {b : Nat}
    (ht : (3 : Real) ^ (b + 1) <= t) :
    b + 1 <= triadicCeilingIndex t := by
  have htone : 1 <= t := (one_le_pow₀ (by norm_num : (1 : Real) <= 3)).trans ht
  have hceil := le_pow_triadicCeilingIndex htone
  have hp : (3 : Nat) ^ (b + 1) <= 3 ^ triadicCeilingIndex t := by
    exact_mod_cast ht.trans hceil
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 3)).mp hp

private theorem lower_ceiling_power {t : Real} (ht : 1 <= t) (hthree : 3 <= t) :
    (3 : Real) ^ (triadicCeilingIndex t - 1) <= t := by
  have hu := pow_triadicCeilingIndex_le_three_mul ht
  have hNpos : 1 <= triadicCeilingIndex t := by
    have hthree' : (3 : Real) ^ (0 + 1) <= t := by simpa using hthree
    simpa only [Nat.zero_add] using (buffer_le_ceiling (b := 0) hthree')
  have hsplit : (3 : Real) ^ triadicCeilingIndex t =
      3 * (3 : Real) ^ (triadicCeilingIndex t - 1) := by
    rw [show triadicCeilingIndex t = 1 + (triadicCeilingIndex t - 1) by omega, pow_add]
    norm_num
  rw [hsplit] at hu
  nlinarith only [hu]

/-- The normalized renormalization radius has an ordinary source tail at the
buffered powered finite-range gauge. -/
theorem measureReal_normalized_renormRadius_gt_le
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {S : CoeffSpace d -> Real} {Ahat : BlockMat d}
    {gamma nu mu rho delta Gain : Real} {n l0 h b : Nat}
    (hAhat : Book.Ch02.BlockPosDef Ahat) (hGain : 0 < Gain) (hdelta : 0 <= delta)
    (hmu : mu = nu - gamma) (hmupos : 0 < mu) (hgn : gamma <= nu)
    (hrg : gamma <= rho)
    (hl0 : 1 <= renormBase gamma nu mu delta Gain l0 h)
    (hthr : Real.log 2 <= frGaugeConst d *
      renormBase gamma nu mu delta Gain l0 h ^ 2 *
        ((3 : Real) ^ (2 * mu) - 1))
    (hcell : HasCellRenormalization P S Ahat gamma nu Gain n l0 h)
    (hb1 : 1 <= b) (hh1 : 1 <= h)
    (hbuf : Real.log (2 * renormCellCount d h) <=
      frGaugeConst d * ((3 : Real) ^ (2 * mu * (b : Real)) - 1)) :
    forall t : Real, 0 < t ->
      P.real (upperTailEvent
        (fun a => renormRadius S Ahat delta rho h n a / (3 : Real) ^ n) t) <=
          (renormalizedRadiusGauge d mu b t)⁻¹ := by
  intro t ht
  let c : Real := (3 : Real) ^ (b + 1)
  have hc : 0 < c := by positivity
  by_cases htc : t < c
  · rw [renormalizedRadiusGauge, ite_eq_left htc, inv_one]
    exact measureReal_le_one
  · have hct : c <= t := le_of_not_gt htc
    have htone : 1 <= t := (one_le_pow₀ (by norm_num : (1 : Real) <= 3)).trans hct
    let N : Nat := triadicCeilingIndex t
    have hbN : b + 1 <= N := by
      simpa only [N, c] using buffer_le_ceiling hct
    let q : Nat := N - (b + 1)
    have hqb : q + b = N - 1 := by simp only [q]; omega
    have hthree : (3 : Real) <= t := by
      have hbpow : (3 : Real) <= c := by
        calc
          (3 : Real) = (3 : Real) ^ (1 : Nat) := by norm_num
          _ <= (3 : Real) ^ (b + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
          _ = c := rfl
      exact hbpow.trans hct
    have hlower : (3 : Real) ^ (q + b) <= t := by
      rw [hqb]
      exact lower_ceiling_power htone hthree
    have hupper : t / c <= (3 : Real) ^ q := by
      have htN := le_pow_triadicCeilingIndex htone
      have hsplit : (3 : Real) ^ N = c * (3 : Real) ^ q := by
        rw [show N = (b + 1) + q by simp only [q]; omega, pow_add]
      rw [hsplit] at htN
      exact (div_le_iff₀ hc).2 (by simpa only [mul_comm] using htN)
    have hsub : upperTailEvent
        (fun a => renormRadius S Ahat delta rho h n a / (3 : Real) ^ n) t <=
        {a : CoeffSpace d | (3 : Real) ^ (n + q + b) <
          renormRadius S Ahat delta rho h n a} := by
      intro a ha
      simp only [upperTailEvent, Set.mem_ofPred_eq] at ha ⊢
      have hnpos : 0 < (3 : Real) ^ n := by positivity
      have hmul := (lt_div_iff₀ hnpos).mp ha
      have hpow : (3 : Real) ^ (n + q + b) =
          (3 : Real) ^ n * (3 : Real) ^ (q + b) := by
        rw [show n + q + b = n + (q + b) by omega, pow_add]
      rw [hpow]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hlower hnpos.le)
        (by simpa only [mul_comm] using hmul)
    have htail := measureReal_renormRadius_gt_le hAhat hGain hdelta hmu hmupos
      hgn hrg hl0 hthr hcell hb1 hh1 hbuf q
    have hpowmono : (t / c) ^ (2 * mu) <=
        ((3 : Real) ^ q) ^ (2 * mu) :=
      Real.rpow_le_rpow (div_nonneg ht.le hc.le) hupper (by linarith only [hmupos])
    have hexp : Real.exp (-(frGaugeConst d *
        (3 : Real) ^ (2 * mu * (q : Real)))) <=
        (frPoweredGauge d mu (t / c))⁻¹ := by
      rw [frPoweredGauge, ← Real.exp_neg]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) <= 3)] at hpowmono
      exact (Real.exp_le_exp.2 (neg_le_neg <|
        mul_le_mul_of_nonneg_left (by simpa only [mul_comm] using hpowmono)
          (frGaugeConst_pos d).le))
    rw [renormalizedRadiusGauge, ite_eq_right htc]
    exact (measureReal_mono hsub).trans (htail.trans hexp)

/-- The supremum defining the renormalization scale is finite almost surely.
This closes the exceptional `top` branch that is deliberately erased by
`ENNReal.toReal` in the real-valued radius. -/
theorem ae_renormScale_ne_top
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {S : CoeffSpace d -> Real} {Ahat : BlockMat d}
    {gamma nu mu rho delta Gain : Real} {n l0 h : Nat}
    (hAhat : Book.Ch02.BlockPosDef Ahat) (hGain : 0 < Gain) (hdelta : 0 <= delta)
    (hmu : mu = nu - gamma) (hmupos : 0 < mu) (hgn : gamma <= nu)
    (hrg : gamma <= rho)
    (hl0 : 1 <= renormBase gamma nu mu delta Gain l0 h)
    (hthr : Real.log 2 <= frGaugeConst d *
      renormBase gamma nu mu delta Gain l0 h ^ 2 *
        ((3 : Real) ^ (2 * mu) - 1))
    (hcell : HasCellRenormalization P S Ahat gamma nu Gain n l0 h) :
    ∀ᵐ a ∂P, renormScale S Ahat delta rho h n a ≠ ⊤ := by
  let B : Real := renormBase gamma nu mu delta Gain l0 h
  let A : Real := frGaugeConst d * B ^ 2 * (3 : Real) ^ (2 * mu)
  let C : Real := 2 * renormCellCount d h
  let f : Nat -> Real := fun q => C *
    Real.exp (-(A * (3 : Real) ^ (2 * mu * (q : Real))))
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hl0
  have hApos : 0 < A := by
    exact mul_pos (mul_pos (frGaugeConst_pos d) (sq_pos_of_pos hBpos)) (by positivity)
  have h2mu : 0 < 2 * mu := by linarith only [hmupos]
  have hfsum : Summable f := by
    exact (summable_exp_neg_triadic hApos h2mu).mul_left C
  have hfle : forall q : Nat,
      P.real {a : CoeffSpace d | renormScale S Ahat delta rho h n a = ⊤} <= f q := by
    intro q
    have hsub : {a : CoeffSpace d | renormScale S Ahat delta rho h n a = ⊤} <=
        {a : CoeffSpace d | ENNReal.ofReal ((3 : Real) ^ ((n + q : Nat) : Int)) <
          renormScale S Ahat delta rho h n a} := by
      intro a ha
      simp only [Set.mem_ofPred_eq] at ha ⊢
      rw [ha]
      exact ENNReal.ofReal_lt_top
    have htail := measureReal_renormScale_gt_le hAhat hGain hdelta hmu hmupos
      hgn hrg hl0 hthr hcell (N := ((n + q : Nat) : Int)) (by omega)
    refine (measureReal_mono hsub).trans (htail.trans_eq ?_)
    have hexponent :
        (3 : Real) ^ (2 * mu * ((((n + q : Nat) : Int) : Real) + 1 - (n : Real))) =
          (3 : Real) ^ (2 * mu) * (3 : Real) ^ (2 * mu * (q : Real)) := by
      rw [← Real.rpow_add (by norm_num : (0 : Real) < 3)]
      congr 1
      push_cast
      ring
    simp only [f, C, A, B]
    rw [hexponent]
    ring_nf
  have hlim : _root_.Filter.Tendsto f _root_.Filter.atTop (nhds 0) := hfsum.tendsto_atTop_zero
  have hzero : P.real {a : CoeffSpace d |
      renormScale S Ahat delta rho h n a = ⊤} = 0 := by
    apply le_antisymm
    · exact ge_of_tendsto' hlim hfle
    · exact measureReal_nonneg
  rw [MeasureTheory.ae_iff]
  have hset : {a : CoeffSpace d | ¬ renormScale S Ahat delta rho h n a ≠ ⊤} =
      {a : CoeffSpace d | renormScale S Ahat delta rho h n a = ⊤} := by
    ext a
    simp only [Set.mem_ofPred_eq, not_not]
  rw [hset]
  exact (measureReal_eq_zero_iff).mp hzero

end

end Quenched
end HighContrast
end HCPolySupport
