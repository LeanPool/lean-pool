/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.OAI.Analysis.KLS.Model
public import LeanPool.KLS.FunctionalInequalities.KLS.Statement
public import LeanPool.KLS.FunctionalInequalities.KLS.Isotropic
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Borel
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Poincare
public import LeanPool.KLS.FunctionalInequalities.Probability.BrunnMinkowski
public import LeanPool.KLS.FunctionalInequalities.Poincare.SmoothTest.WeakLimit

/-!
# From the covariance-normalized KLS conjecture to the OpenAI statement

The target is the unchanged `OAI.LeanBlast.KLS.KLSStatement` from openai/math
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Its density need only be measurable,
nonnegative and log-concave on its positive support. No upper semicontinuity or
extra moment hypotheses are imposed. The proof converts these assumptions to the
library's compact-set log-concavity and isotropy, then applies the covariance bound
to smooth compactly supported tests. It does not import a proof of KLS.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open OAI.LeanBlast.KLS
open scoped ContDiff RealInnerProductSpace

namespace KLSOpenAI

variable {n : ℕ} {ρ : Space n → ℝ}

private theorem density_rpow (hρ : IsLogConcaveDensity ρ) (x y : Space n) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    ρ x ^ t * ρ y ^ (1 - t) ≤ ρ (t • x + (1 - t) • y) := by
  have ht : 0 < 1 - t := by linarith
  by_cases hx : 0 < ρ x
  · by_cases hy : 0 < ρ y
    · have hz : 0 < ρ (t • x + (1 - t) • y) :=
        hρ.log_concave.1 hx hy ht0.le ht.le (by ring)
      apply (Real.log_le_log_iff
        (mul_pos (Real.rpow_pos_of_pos hx t) (Real.rpow_pos_of_pos hy (1 - t))) hz).mp
      rw [Real.log_mul (Real.rpow_pos_of_pos hx t).ne'
        (Real.rpow_pos_of_pos hy (1 - t)).ne', Real.log_rpow hx, Real.log_rpow hy]
      exact hρ.log_concave.2 hx hy ht0.le ht.le (by ring)
    · have hy0 : ρ y = 0 := le_antisymm (le_of_not_gt hy) (hρ.nonnegative y)
      rw [hy0, Real.zero_rpow ht.ne', mul_zero]
      exact hρ.nonnegative _
  · have hx0 : ρ x = 0 := le_antisymm (le_of_not_gt hx) (hρ.nonnegative x)
    rw [hx0, Real.zero_rpow ht0.ne', zero_mul]
    exact hρ.nonnegative _

/-- An OpenAI log-concave probability density gives a compact-set log-concave law.
Prékopa–Leindler applies directly; upper semicontinuity of the density is unnecessary. -/
theorem logConcave (hρ : IsLogConcaveDensity ρ) :
    FunctionalInequalities.KLS.LogConcave
      (⟨densityMeasure ρ, hρ.probability⟩ : ProbabilityMeasure (Space n)) := by
  intro K L hK hL t ht0 ht1
  set S := {z : Space n | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y}
  have hS : IsCompact S := FunctionalInequalities.KLS.isCompact_combination hK hL t
  have hmass (A : Set (Space n)) (hA : MeasurableSet A) :
      densityMeasure ρ A = ∫⁻ x, ENNReal.ofReal (A.indicator ρ x) := by
    have hind : (fun x => ENNReal.ofReal (A.indicator ρ x)) =
        A.indicator (fun x => ENNReal.ofReal (ρ x)) := by
      funext x
      by_cases hx : x ∈ A <;> simp [hx]
    rw [hind, lintegral_indicator hA, densityMeasure, withDensity_apply _ hA]
  change densityMeasure ρ K ^ t * densityMeasure ρ L ^ (1 - t) ≤ densityMeasure ρ S
  rw [hmass K hK.measurableSet, hmass L hL.measurableSet, hmass S hS.measurableSet]
  refine FunctionalInequalities.Analysis.prekopaLeindler
    (hρ.measurable.indicator hK.measurableSet) (hρ.measurable.indicator hL.measurableSet)
    (hρ.measurable.indicator hS.measurableSet)
    (fun x => Set.indicator_nonneg (fun y _ => hρ.nonnegative y) x)
    (fun x => Set.indicator_nonneg (fun y _ => hρ.nonnegative y) x) ht0 ht1 ?_
  intro x y
  by_cases hx : x ∈ K
  · by_cases hy : y ∈ L
    · have hz : t • x + (1 - t) • y ∈ S := ⟨x, hx, y, hy, rfl⟩
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hz]
      exact density_rpow hρ x y ht0 ht1
    · rw [Set.indicator_of_notMem hy, Real.zero_rpow (by linarith : 1 - t ≠ 0), mul_zero]
      exact Set.indicator_nonneg (fun z _ => hρ.nonnegative z) _
  · rw [Set.indicator_of_notMem hx, Real.zero_rpow ht0.ne', zero_mul]
    exact Set.indicator_nonneg (fun z _ => hρ.nonnegative z) _

/-- Coordinate isotropy in the OpenAI model implies the library's vector/covariance isotropy. -/
theorem isotropic (hρ : IsLogConcaveDensity ρ) (hi : IsIsotropic (densityMeasure ρ)) :
    FunctionalInequalities.KLS.Isotropic
      (⟨densityMeasure ρ, hρ.probability⟩ : ProbabilityMeasure (Space n)) := by
  let μ : ProbabilityMeasure (Space n) := ⟨densityMeasure ρ, hρ.probability⟩
  have h2 : MemLp id 2 (μ : Measure (Space n)) := by
    apply memLp_piLp_iff.mpr
    intro i
    apply (memLp_two_iff_integrable_sq
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.aestronglyMeasurable).mpr
    change Integrable (fun x : Space n => x i ^ 2) (densityMeasure ρ)
    simpa only [pow_two] using hi.integrable_product i i
  have hmean : (∫ x, x ∂(μ : Measure (Space n))) = 0 := by
    ext i
    have h := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm (h2.integrable (by norm_num))
    change (∫ x : Space n, x i ∂densityMeasure ρ) =
      (∫ x : Space n, x ∂densityMeasure ρ) i at h
    change (∫ x : Space n, x ∂densityMeasure ρ) i = 0
    rw [← h, hi.mean_zero]
  apply FunctionalInequalities.KLS.isotropic_of_moments μ h2 hmean
  intro u v
  have hinner (a b : Space n) : inner ℝ a b = ∑ i, a i * b i := by
    simp [PiLp.inner_apply, mul_comm]
  have hint (i j : Fin n) :
      Integrable (fun x : Space n => (u i * x i) * (v j * x j)) (μ : Measure (Space n)) := by
    have heq : (fun x : Space n => (u i * x i) * (v j * x j)) =
        (fun x => (u i * v j) * (x i * x j)) := by funext x; ring
    rw [heq]
    exact (hi.integrable_product i j).const_mul (u i * v j)
  simp_rw [hinner, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  calc
    (∑ j, ∫ x, (u i * x i) * (v j * x j) ∂(μ : Measure (Space n))) =
        ∑ j, (u i * v j) * (if i = j then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      have heq : (fun x : Space n => (u i * x i) * (v j * x j)) =
          (fun x => (u i * v j) * (x i * x j)) := by funext x; ring
      rw [heq, integral_const_mul]
      change (u i * v j) * (∫ x, x i * x j ∂densityMeasure ρ) = _
      rw [hi.second_moment]
    _ = u i * v i := by simp

/-- At an OpenAI isotropic log-concave density, a covariance-normalized local-slope bound
`C_P^lit(μ) ≤ C ‖Cov μ‖` gives the smooth compactly supported Poincaré bound with the same
constant: the covariance is the identity, whose operator norm is at most one. Every dimension,
including zero, is allowed. -/
theorem smoothTest_holds_of_localSlope_le_covariance (hρ : IsLogConcaveDensity ρ)
    (hi : IsIsotropic (densityMeasure ρ)) {C : NNReal}
    (hC : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.optimalConstant
        (⟨densityMeasure ρ, hρ.probability⟩ : ProbabilityMeasure (Space n)) ≤
      (C : ENNReal) * ENNReal.ofReal
        ‖FunctionalInequalities.Covariance.operator (densityMeasure ρ)‖) :
    FunctionalInequalities.Poincare.SmoothTest.Holds (densityMeasure ρ) (C : ℝ) := by
  let μ : ProbabilityMeasure (Space n) := ⟨densityMeasure ρ, hρ.probability⟩
  have hcov : FunctionalInequalities.Covariance.operator (densityMeasure ρ) =
      ContinuousLinearMap.id ℝ (Space n) := (isotropic hρ hi).covariance_identity
  have hlit : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.optimalConstant μ ≤
    (C : ENNReal) := by
    refine hC.trans (mul_le_of_le_one_right zero_le ?_)
    rw [hcov]
    exact ENNReal.ofReal_le_one.mpr ContinuousLinearMap.norm_id_le
  apply (FunctionalInequalities.Poincare.SmoothTest.holds_iff_ambient μ C).mpr
  apply (FunctionalInequalities.Poincare.SmoothGradient.Ambient.holds_iff_constant_le μ C).mpr
  rw [← FunctionalInequalities.Poincare.SmoothTest.constant_eq_ambient μ,
    (logConcave hρ).smoothTest_constant_eq_localSlope]
  exact hlit

/-- The covariance-normalized KLS conjecture implies exactly the pinned OpenAI statement.
One positive real constant is chosen before every dimension, density and test function. -/
theorem of_conjecture (hKLS : FunctionalInequalities.KLS.Conjecture) : KLSStatement := by
  obtain ⟨C, hC⟩ := hKLS
  refine ⟨(C : ℝ) + 1, by positivity, ?_⟩
  intro n _ ρ hρ hi f hf
  let μ : ProbabilityMeasure (Space n) := ⟨densityMeasure ρ, hρ.probability⟩
  have hsmooth := smoothTest_holds_of_localSlope_le_covariance hρ hi
    (hC n μ (logConcave hρ) (isotropic hρ hi).memLp_two)
  have : IsProbabilityMeasure (densityMeasure ρ) := hρ.probability
  have hadm := FunctionalInequalities.Poincare.SmoothTest.Admissible.of_contDiff_hasCompactSupport
    (μ := densityMeasure ρ) hf.1 hf.2
  have hvariance := hsmooth.variance_le hadm
  rw [ProbabilityTheory.variance_eq_integral hadm.memLp_two.aemeasurable] at hvariance
  change variance (densityMeasure ρ) f ≤ ((C : ℝ) + 1) * dirichletEnergy (densityMeasure ρ) f
  change variance (densityMeasure ρ) f ≤ (C : ℝ) * dirichletEnergy (densityMeasure ρ) f
    at hvariance
  exact hvariance.trans (mul_le_mul_of_nonneg_right (by linarith)
    (integral_nonneg fun x => sq_nonneg ‖gradient f x‖))

end KLSOpenAI
