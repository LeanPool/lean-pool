/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Frozen.CoarseEllipticityDagger
public import LeanPool.HighContrastHomogenization.Setup.BlockAlgebra
public import LeanPool.HighContrastHomogenization.Setup.LocalSigmaFields
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockMatrixProperties
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.CoarseBounds
public import LeanPool.HighContrastHomogenization.Setup.Response
public import LeanPool.HighContrastHomogenization.Entry.Geometry.StandardCell
public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.PsiCalculus
public import LeanPool.HighContrastHomogenization.Setup.CoefficientSpace
public import LeanPool.HighContrastHomogenization.Entry.Multiscale.SelectionExponentBounds
public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.WeakOrlicz
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import LeanPool.HighContrastHomogenization.Setup.SourceObjects

/-!
# High-contrast homogenization: Entry.Source.GaugeMoments

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Source moments from the gauge tail

HC Lemma C.1 (Steps 1–4) supplies the
printed route. We use CG's proved growth/doubling calculus, Mathlib's layer cake,
and an integrable power-tail envelope to obtain the paper's `C(p) * K^C(p)` consequence
(`l.source.whitney`). The coefficient here is deliberately nonsharp;
HC's sharper coefficient and its sequence triangle inequality are not asserted.

Finiteness is proved in the nonnegative extended integral before deriving `MemLp`
and the real moment bound. The constant precedes every law, gauge and source.
The final consumer uses exactly the same `Q` and `p = 2*(d+Q)`. No new definition
or global measurability assumption on the gauge is introduced.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Source

open MeasureTheory Set Filter

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Layer cake for a nonnegative source, before any finiteness assumption.
The pinned Mathlib theorem is `MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul`
in `Mathlib.Analysis.SpecialFunctions.Pow.Integral`. -/
theorem source_lintegral_layercake (μ : Measure Ω) (S : Ω → ℝ)
    (hS : Measurable S) (hS0 : ∀ ω, 0 ≤ S ω) {p : ℝ} (hp : 0 < p) :
    (∫⁻ ω, ENNReal.ofReal (S ω ^ p) ∂μ) = ENNReal.ofReal p *
      ∫⁻ t in Set.Ioi (0 : ℝ), μ (IndependentSums.upperTailEvent S t) *
        ENNReal.ofReal (t ^ (p - 1)) := by
  exact lintegral_rpow_eq_lintegral_meas_lt_mul μ
    (Filter.Eventually.of_forall hS0) hS.aemeasurable hp

theorem two_le_twoGrowthWitness (K : ℝ) : 2 ≤ growthBar K := by
  exact le_max_left 2 K

theorem one_lt_twoGrowthWitness (K : ℝ) : 1 < growthBar K := by
  exact lt_of_lt_of_le one_lt_two (two_le_twoGrowthWitness K)

theorem le_twoGrowthWitness_of_one_lt {K : ℝ} (_hK : 1 < K) :
    K ≤ growthBar K := by
  exact le_max_right 2 K

theorem hasPsiGrowth_twoGrowthWitness_of_growth
    {Ψ : ℝ → ℝ} {K : ℝ}
    (hAdmissible : IndependentSums.AdmissiblePsi Ψ) (hK : 1 < K)
    (hGrowth : IndependentSums.HasPsiGrowth Ψ K) :
    IndependentSums.HasPsiGrowth Ψ (growthBar K) := by
  intro t ht
  have ht_nonneg : 0 ≤ t := le_trans zero_le_one ht
  have hK_nonneg : 0 ≤ K := le_trans zero_le_one hK.le
  have htwoK_nonneg : 0 ≤ growthBar K := by
    exact le_trans (by norm_num : (0 : ℝ) ≤ 2) (two_le_twoGrowthWitness K)
  have harg_le : K * t ≤ growthBar K * t := by
    exact mul_le_mul_of_nonneg_right (le_twoGrowthWitness_of_one_lt hK) ht_nonneg
  have hmono :
      Ψ (K * t) ≤ Ψ (growthBar K * t) :=
    hAdmissible.1 (mul_nonneg hK_nonneg ht_nonneg)
      (mul_nonneg htwoK_nonneg ht_nonneg) harg_le
  exact (hGrowth ht).trans hmono

/-- HC C.1 growth gives a global power-tail envelope above one, also for `1 < K < 2`. -/
theorem gauge_inverse_rpow_bound {Ψ : ℝ → ℝ} {K q t : ℝ}
    (hΨ : IndependentSums.AdmissiblePsi Ψ) (hK : 1 < K)
    (hg : IndependentSums.HasPsiGrowth Ψ K) (hq : 2 ≤ q) (ht : 1 ≤ t) :
    (Ψ t)⁻¹ ≤ growthBar K ^ (3 * q ^ (2 : ℕ)) * t ^ (-q) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hΨ0 : 0 < Ψ t := zero_lt_one.trans_le (hΨ.2 ht0.le)
  have hdouble := IndependentSums.admissiblePsi_doubling
    (two_le_twoGrowthWitness K) (hasPsiGrowth_twoGrowthWitness_of_growth hΨ hK hg)
    hΨ hq (le_refl (1 : ℝ)) ht
  simp only [one_mul] at hdouble
  have hpoly : t ^ q ≤ growthBar K ^ (3 * q ^ (2 : ℕ)) * Ψ t :=
    hdouble.trans (mul_le_mul_of_nonneg_left
      (div_le_self hΨ0.le (hΨ.2 zero_le_one)) (Real.rpow_nonneg (zero_lt_one.trans
        (one_lt_twoGrowthWitness K)).le _))
  rw [Real.rpow_neg ht0.le, ← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos ht0 q)).2
  rw [inv_mul_eq_div]
  exact (div_le_iff₀ hΨ0).2 hpoly

/-- A power tail one order above the moment gives a finite layer-cake integral.
The elementary bound on `(0,1]` costs a factor `p`; no sharp HC coefficient is asserted. -/
theorem source_lintegral_moment_le_of_power_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → ℝ) (hS : Measurable S) (hS0 : ∀ ω, 0 ≤ S ω)
    {p A : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A)
    (htail : ∀ t : ℝ, 1 ≤ t →
      μ.real (IndependentSums.upperTailEvent S t) ≤ A * t ^ (-(p + 1))) :
    (∫⁻ ω, ENNReal.ofReal (S ω ^ p) ∂μ) ≤ ENNReal.ofReal (p * (1 + A)) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hlo : (∫⁻ t in Ioc (0 : ℝ) 1,
      μ (IndependentSums.upperTailEvent S t) * ENNReal.ofReal (t ^ (p - 1))) ≤ 1 := by
    calc
      _ ≤ ∫⁻ _t in Ioc (0 : ℝ) 1, (1 : ENNReal) := by
        apply setLIntegral_mono' measurableSet_Ioc
        intro t ht
        refine (mul_le_of_le_one_left zero_le prob_le_one).trans ?_
        exact (ENNReal.ofReal_le_one).2
          (Real.rpow_le_one ht.1.le ht.2 (sub_nonneg.mpr hp))
      _ = 1 := by simp
  have hmodel : (∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (A * t ^ (-2 : ℝ))) =
      ENNReal.ofReal A := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one).const_mul A)
      (by
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        exact mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans ht).le _)),
      integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one]
    norm_num
  have hhi : (∫⁻ t in Ioi (1 : ℝ),
      μ (IndependentSums.upperTailEvent S t) * ENNReal.ofReal (t ^ (p - 1))) ≤
      ENNReal.ofReal A := by
    rw [← hmodel]
    apply setLIntegral_mono' measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [← ofReal_measureReal (μ := μ), ← ENNReal.ofReal_mul measureReal_nonneg]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (A * t ^ (-(p + 1))) * t ^ (p - 1) :=
        mul_le_mul_of_nonneg_right (htail t ht.le) (Real.rpow_nonneg ht0.le _)
      _ = A * t ^ (-2 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add ht0]
        congr 2
        ring
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi 1 := by
    ext t
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro ht
      by_cases ht1 : t ≤ 1
      · exact Or.inl ⟨ht, ht1⟩
      · exact Or.inr (lt_of_not_ge ht1)
    · rintro (⟨ht, _⟩ | ht)
      · exact ht
      · exact zero_lt_one.trans ht
  rw [source_lintegral_layercake μ S hS hS0 hp0]
  calc
    _ ≤ ENNReal.ofReal p * (1 + ENNReal.ofReal A) := by
      apply mul_le_mul_right
      rw [hsplit]
      exact (lintegral_union_le _ _ _).trans (add_le_add hlo hhi)
    _ = ENNReal.ofReal (p * (1 + A)) := by
      rw [ENNReal.ofReal_mul hp0.le, ENNReal.ofReal_add zero_le_one hA, ENNReal.ofReal_one]

/-- HC C.1's tail-to-moment consequence, with a deliberately nonsharp explicit coefficient.
The bound is proved in the nonnegative extended integral before asserting either integrability
or membership in `L^p`. No measurability of the gauge on negative arguments is needed. -/
theorem source_moment_bound_of_gauge_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Ψ : ℝ → ℝ) (K : ℝ) (S : Ω → ℝ) {p : ℝ} (hp : 1 ≤ p)
    (hΨ : IndependentSums.AdmissiblePsi Ψ) (hK : 1 < K)
    (hg : IndependentSums.HasPsiGrowth Ψ K) (hS : Measurable S)
    (hS0 : ∀ ω, 0 ≤ S ω)
    (htail : ∀ t : ℝ, 0 < t →
      μ.real (IndependentSums.upperTailEvent S t) ≤ (Ψ t)⁻¹) :
    MemLp S (ENNReal.ofReal p) μ ∧ Integrable (fun ω => S ω ^ p) μ ∧
      (∫ ω, S ω ^ p ∂μ) ≤
        p * (1 + growthBar K ^ (3 * (p + 1) ^ (2 : ℕ))) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hbound := source_lintegral_moment_le_of_power_tail μ S hS hS0 hp
    (Real.rpow_nonneg (zero_lt_one.trans (one_lt_twoGrowthWitness K)).le
      (3 * (p + 1) ^ (2 : ℕ))) (fun t ht =>
        (htail t (zero_lt_one.trans_le ht)).trans
          (gauge_inverse_rpow_bound hΨ hK hg (by linarith only [hp] : 2 ≤ p + 1) ht))
  have hn : 0 ≤ᵐ[μ] (fun ω => S ω ^ p) :=
    Eventually.of_forall (fun ω => Real.rpow_nonneg (hS0 ω) p)
  have hi : Integrable (fun ω => S ω ^ p) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (hS.pow_const p).aestronglyMeasurable hn).1
      (ne_of_lt (hbound.trans_lt ENNReal.ofReal_lt_top))
  have hlp : MemLp S (ENNReal.ofReal p) μ := by
    apply (integrable_norm_rpow_iff hS.aestronglyMeasurable
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top).1
    simpa only [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs,
      abs_of_nonneg (hS0 _)] using hi
  refine ⟨hlp, hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hn hi.aestronglyMeasurable]
  exact (ENNReal.toReal_le_toReal (ne_of_lt (hbound.trans_lt ENNReal.ofReal_lt_top))
    ENNReal.ofReal_ne_top).2 hbound |>.trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg hp0.le (add_nonneg zero_le_one
        (Real.rpow_nonneg (zero_lt_one.trans (one_lt_twoGrowthWitness K)).le _))))

/-- The moment endpoint of the proof of `e.source.adapted.bound`, with the constant
chosen before the probability space, gauge, growth witness and source. One possible
constant is
`C = p * (1 + 2 ^ a) + a + 1`, where `a = 3 * (p + 1)^2`.
The fixed enlargement `max 2 K ≤ 2 K` is absorbed explicitly, so the endpoint retains `K > 1`. -/
theorem source_moment_bound (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure μ]
        (Ψ : ℝ → ℝ) (K : ℝ) (S : Ω → ℝ),
        IndependentSums.AdmissiblePsi Ψ → 1 < K →
        IndependentSums.HasPsiGrowth Ψ K → Measurable S →
        (∀ ω, 0 ≤ S ω) →
        (∀ t : ℝ, 0 < t →
          μ.real (IndependentSums.upperTailEvent S t) ≤ (Ψ t)⁻¹) →
        MeasureTheory.MemLp S (ENNReal.ofReal p) μ ∧
        MeasureTheory.Integrable (fun ω => S ω ^ p) μ ∧
        (∫ ω, S ω ^ p ∂μ) ≤ C * K ^ C := by
  let a : ℝ := 3 * (p + 1) ^ (2 : ℕ)
  let C : ℝ := p * (1 + (2 : ℝ) ^ a) + a + 1
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ _ Ψ K S hΨ hK hg hS hS0 htail
  obtain ⟨hlp, hi, hbound⟩ :=
    source_moment_bound_of_gauge_tail μ Ψ K S hp hΨ hK hg hS hS0 htail
  refine ⟨hlp, hi, hbound.trans ?_⟩
  have hK0 : 0 < K := zero_lt_one.trans hK
  have htwo : growthBar K ≤ 2 * K := by
    apply max_le <;> linarith only [hK, hK0]
  have hpow : growthBar K ^ a ≤ (2 : ℝ) ^ a * K ^ a := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hK0.le]
    exact Real.rpow_le_rpow (zero_lt_one.trans (one_lt_twoGrowthWitness K)).le htwo ha
  have hKa : 1 ≤ K ^ a := Real.one_le_rpow hK.le ha
  have hCa : a ≤ C := by
    dsimp [C]
    have hprod : 0 < p * (1 + (2 : ℝ) ^ a) := mul_pos hp0 (by positivity)
    linarith only [hprod]
  have hcoeff : p * (1 + (2 : ℝ) ^ a) ≤ C := by
    dsimp [C]
    linarith only [ha]
  calc
    p * (1 + growthBar K ^ a) ≤ p * (1 + (2 : ℝ) ^ a * K ^ a) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hpow) hp0.le
    _ ≤ (p * (1 + (2 : ℝ) ^ a)) * K ^ a := by
      calc
        p * (1 + (2 : ℝ) ^ a * K ^ a)
            ≤ p * (K ^ a + (2 : ℝ) ^ a * K ^ a) :=
          mul_le_mul_of_nonneg_left (add_le_add hKa le_rfl) hp0.le
        _ = (p * (1 + (2 : ℝ) ^ a)) * K ^ a := by ring
    _ ≤ C * K ^ a := mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ ≤ C * K ^ C := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hK.le hCa) hC.le

/-- The moment estimate specialized to precisely the dagger fields and probability.
The constant still depends only on the moment order. -/
theorem CoarseEllipticityDagger.source_moment_bound (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {d : ℕ} (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
      (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
      CoarseEllipticityDagger P γ E Ψ K S →
      MemLp S (ENNReal.ofReal p) P ∧ Integrable (fun a => S a ^ p) P ∧
        (∫ a, S a ^ p ∂P) ≤ C * K ^ C := by
  obtain ⟨C, hC, hmoment⟩ := Source.source_moment_bound p hp
  refine ⟨C, hC, ?_⟩
  intro d P _ γ E Ψ K S hdag
  exact hmoment P Ψ K S hdag.gauge_admissible hdag.one_lt_growthWitness
    hdag.gauge_growth hdag.source_measurable hdag.source_nonneg hdag.source_tail

/-- The source-moment endpoint: `p = 2*(d+Q)`, with explicit geometric-tail
margins `d+Q`. Substitution in `source_moment_bound` fixes `C` from `d, γ` alone.
Neither stationarity, independence, an integrability premise nor ellipticity constants enter. -/
theorem source_selection_moment_bound (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      1 ≤ Multiscale.sourceMomentExponent d γ ∧
      (d : ℝ) + (bigQ d γ : ℝ) ≤
        (Multiscale.sourceMomentExponent d γ : ℝ) - (d : ℝ) ∧
      (d : ℝ) + (bigQ d γ : ℝ) ≤
        (Multiscale.sourceMomentExponent d γ : ℝ) - (bigQ d γ : ℝ) * γ ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        CoarseEllipticityDagger P γ E Ψ K S →
        MemLp S (ENNReal.ofReal (Multiscale.sourceMomentExponent d γ : ℝ)) P ∧
        Integrable (fun a => S a ^ (Multiscale.sourceMomentExponent d γ : ℝ)) P ∧
        (∫ a, S a ^ (Multiscale.sourceMomentExponent d γ : ℝ) ∂P) ≤ C * K ^ C := by
  have hp := Multiscale.sourceMomentExponent_ge_one d hd γ hγ
  have hpR : 1 ≤ (Multiscale.sourceMomentExponent d γ : ℝ) := by exact_mod_cast hp
  obtain ⟨C, hC, hmoment⟩ := CoarseEllipticityDagger.source_moment_bound _ hpR
  obtain ⟨hdmargin, hγmargin⟩ := Multiscale.sourceMomentExponent_tail_margins d hd γ hγ
  exact ⟨C, hC, hp, hdmargin, hγmargin, fun P _ E Ψ K S hdag =>
    hmoment P γ E Ψ K S hdag⟩

variable {d : ℕ} {P : Measure (CoeffSpace d)} {γ : ℝ} {E : BlockMat d}
  {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}

end HCPolySupport.HighContrast.Source
