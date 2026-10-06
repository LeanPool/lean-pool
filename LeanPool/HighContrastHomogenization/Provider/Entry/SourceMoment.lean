/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Frozen.CoarseEllipticityDagger
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# High-contrast homogenization: Provider.Entry.SourceMoment

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The source moment of the random-source data

The comparison between adapted and Euclidean cubes measures its error in units
of the reference block with the source gauge
`Γ_{g,S}(j) = (1-g)^{-1}(1 + K_{Ψ_S}^2 3^{-j})^g` as coefficient, and the one
place the law of the source scale enters its proof is the moment of the source
scale,

`E[S] ≤ 2K_{Ψ_S}^2`.

This file proves it, and the integrability of the source scale that comes with
it, from the random-source data alone.

Iterating the gauge growth of `e.source.tail` twice against
`Ψ_S ≥ 1` gives `Ψ_S(σ) ≥ σ^2K_{Ψ_S}^{-3}` for `σ ≥ K_{Ψ_S}^2`, so the tail is
quadratic there.  The layer-cake integral of the tail then splits at
`K_{Ψ_S}^2`: below it the tail is bounded by one and contributes the length
`K_{Ψ_S}^2`, above it the quadratic tail integrates to `K_{Ψ_S}`, and
`K_{Ψ_S} ≤ K_{Ψ_S}^2` since the witness exceeds one.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Entry

open MeasureTheory Set

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The source moment -/

/-- **The gauge is at least quadratic above the square of its witness.**
Iterating the growth inequality of `e.source.tail` twice, at the
arguments `σK_{Ψ_S}^{-2}` and `σK_{Ψ_S}^{-1}`, and using `Ψ_S ≥ 1`. -/
theorem sq_div_le_gauge {Ψ : ℝ → ℝ} {K : ℝ} (hK : 1 < K)
    (hadm : IndependentSums.AdmissiblePsi Ψ)
    (hgrow : IndependentSums.HasPsiGrowth Ψ K) {σ : ℝ} (hσ : K ^ 2 ≤ σ) :
    σ ^ 2 / K ^ 3 ≤ Ψ σ := by
  have hK0 : (0 : ℝ) < K := lt_trans zero_lt_one hK
  have hK2 : (0 : ℝ) < K ^ 2 := by positivity
  set τ : ℝ := σ / K ^ 2 with hτdef
  have hτ1 : 1 ≤ τ := by
    rw [hτdef, le_div_iff₀ hK2]
    linarith only [hσ]
  have hτ0 : (0 : ℝ) ≤ τ := le_trans zero_le_one hτ1
  have hKτ1 : 1 ≤ K * τ := by nlinarith only [hK, hτ1]
  have h1 : τ * Ψ τ ≤ Ψ (K * τ) := hgrow hτ1
  have h2 : (K * τ) * Ψ (K * τ) ≤ Ψ (K * (K * τ)) := hgrow hKτ1
  have hΨτ : 1 ≤ Ψ τ := hadm.2 hτ0
  have hKτ0 : (0 : ℝ) ≤ K * τ := by positivity
  have h3 : τ ≤ Ψ (K * τ) := le_trans (by nlinarith only [hΨτ, hτ0]) h1
  have h4 : K * τ * τ ≤ K * τ * Ψ (K * τ) := mul_le_mul_of_nonneg_left h3 hKτ0
  have hstep : K * τ ^ 2 ≤ Ψ (K * (K * τ)) := by
    have hrw : K * τ ^ 2 = K * τ * τ := by ring
    rw [hrw]
    exact le_trans h4 h2
  have hσeq : K * (K * τ) = σ := by rw [hτdef]; field_simp
  have hval : K * τ ^ 2 = σ ^ 2 / K ^ 3 := by rw [hτdef]; field_simp
  rw [hσeq, hval] at hstep
  exact hstep

/-- **The quadratic tail of the source scale** above the square of the gauge
witness, from `e.source.tail` and the quadratic lower bound on
the gauge. -/
theorem measureReal_tail_le {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) {σ : ℝ}
    (hσ : K ^ 2 ≤ σ) :
    P.real {a | σ < S a} ≤ K ^ 3 * σ ^ (-2 : ℝ) := by
  have hK : 1 < K := hdag.one_lt_growthWitness
  have hK0 : (0 : ℝ) < K := lt_trans zero_lt_one hK
  have hK2 : (0 : ℝ) < K ^ 2 := by positivity
  have hσ0 : (0 : ℝ) < σ := lt_of_lt_of_le hK2 hσ
  have hlow : σ ^ 2 / K ^ 3 ≤ Ψ σ :=
    sq_div_le_gauge hK hdag.gauge_admissible hdag.gauge_growth hσ
  have hpos : (0 : ℝ) < σ ^ 2 / K ^ 3 := by positivity
  have htail := hdag.source_tail σ hσ0
  have hinv : (Ψ σ)⁻¹ ≤ K ^ 3 * σ ^ (-2 : ℝ) := by
    have h1 : (Ψ σ)⁻¹ ≤ (σ ^ 2 / K ^ 3)⁻¹ := by
      have := one_div_le_one_div_of_le hpos hlow
      rwa [one_div, one_div] at this
    have h2 : (σ ^ 2 / K ^ 3)⁻¹ = K ^ 3 * σ ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hσ0.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      field_simp
    rw [← h2]
    exact h1
  exact le_trans htail hinv

/-- The layer-cake bound behind the source moment: the split of
`∫_0^∞ P[S > σ]dσ` at `K_{Ψ_S}^2`. -/
theorem lintegral_source_le {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) :
    ∫⁻ a, ENNReal.ofReal (S a) ∂P ≤ ENNReal.ofReal (K ^ 2 + K) := by
  have hK : 1 < K := hdag.one_lt_growthWitness
  have hK0 : (0 : ℝ) < K := lt_trans zero_lt_one hK
  have hK2 : (0 : ℝ) < K ^ 2 := by positivity
  have hSm : Measurable S := hdag.source_measurable
  have hS0 : ∀ a, 0 ≤ S a := hdag.source_nonneg
  have hlayer : ∫⁻ a, ENNReal.ofReal (S a) ∂P =
      ∫⁻ t in Ioi (0 : ℝ), P {a | t < S a} :=
    lintegral_eq_lintegral_meas_lt P (Filter.Eventually.of_forall hS0)
      hSm.aemeasurable
  have hsplit : ∫⁻ t in Ioi (0 : ℝ), P {a | t < S a} =
      (∫⁻ t in Ioc (0 : ℝ) (K ^ 2), P {a | t < S a}) +
        ∫⁻ t in Ioi (K ^ 2), P {a | t < S a} := by
    rw [← Ioc_union_Ioi_eq_Ioi hK2.le]
    exact lintegral_union measurableSet_Ioi
      (disjoint_left.2 fun t ht0 ht1 => not_lt_of_ge ht0.2 ht1)
  have hlow : (∫⁻ t in Ioc (0 : ℝ) (K ^ 2), P {a | t < S a}) ≤
      ENNReal.ofReal (K ^ 2) := by
    calc (∫⁻ t in Ioc (0 : ℝ) (K ^ 2), P {a | t < S a})
        ≤ ∫⁻ _ in Ioc (0 : ℝ) (K ^ 2), (1 : ENNReal) :=
          lintegral_mono fun _ => prob_le_one
      _ = volume (Ioc (0 : ℝ) (K ^ 2)) := by simp
      _ = ENNReal.ofReal (K ^ 2) := by rw [Real.volume_Ioc, sub_zero]
  have hmajm : IntegrableOn (fun t : ℝ => K ^ 3 * t ^ (-2 : ℝ)) (Ioi (K ^ 2)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hK2).const_mul _
  have hmajint : ∫ t in Ioi (K ^ 2), K ^ 3 * t ^ (-2 : ℝ) = K := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hK2]
    have hrw : (K ^ 2 : ℝ) ^ ((-2 : ℝ) + 1) = (K ^ 2)⁻¹ := by
      norm_num
      rw [Real.rpow_neg_one]
    rw [hrw]
    field_simp
    ring
  have hhigh : (∫⁻ t in Ioi (K ^ 2), P {a | t < S a}) ≤ ENNReal.ofReal K := by
    have hstep : (∫⁻ t in Ioi (K ^ 2), P {a | t < S a}) ≤
        ∫⁻ t in Ioi (K ^ 2), ENNReal.ofReal (K ^ 3 * t ^ (-2 : ℝ)) := by
      refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
      rw [← ENNReal.ofReal_toReal (measure_ne_top P {a | t < S a})]
      exact ENNReal.ofReal_le_ofReal (measureReal_tail_le hdag (le_of_lt ht))
    refine hstep.trans (le_of_eq ?_)
    rw [← ofReal_integral_eq_lintegral_ofReal hmajm
      ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun t ht => by
          have ht0 : (0 : ℝ) < t := lt_trans hK2 ht
          positivity)), hmajint]
  rw [hlayer, hsplit, ENNReal.ofReal_add (by positivity) hK0.le]
  exact add_le_add hlow hhigh

/-- The source scale is integrable: its quadratic tail is. -/
theorem integrable_source {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) : Integrable S P := by
  refine ⟨hdag.source_measurable.aestronglyMeasurable, ?_⟩
  have hnorm : ∫⁻ a, ‖S a‖ₑ ∂P = ∫⁻ a, ENNReal.ofReal (S a) ∂P :=
    lintegral_congr fun a => by
      rw [← ofReal_norm, Real.norm_eq_abs,
        abs_of_nonneg (hdag.source_nonneg a)]
  rw [HasFiniteIntegral, hnorm]
  exact lt_of_le_of_lt (lintegral_source_le hdag) ENNReal.ofReal_lt_top

/-- **The source moment**: `E[S] ≤ 2K_{Ψ_S}^2`. -/
theorem integral_source_le {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) :
    ∫ a, S a ∂P ≤ 2 * K ^ 2 := by
  have hK : 1 < K := hdag.one_lt_growthWitness
  have hint : ∫ a, S a ∂P = (∫⁻ a, ENNReal.ofReal (S a) ∂P).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall hdag.source_nonneg)
      hdag.source_measurable.aestronglyMeasurable
  have htoreal : (∫⁻ a, ENNReal.ofReal (S a) ∂P).toReal ≤ K ^ 2 + K := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (lintegral_source_le hdag)
    rwa [ENNReal.toReal_ofReal (by positivity)] at h
  have hKK : K ≤ K ^ 2 := by nlinarith only [hK]
  rw [hint]
  linarith only [htoreal, hKK]

end

end Entry
end HighContrast
end HCPolySupport
