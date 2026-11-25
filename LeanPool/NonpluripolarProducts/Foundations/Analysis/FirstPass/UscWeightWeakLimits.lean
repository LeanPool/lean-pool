/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.UscLipschitzMajorants
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Upper semicontinuous weights and weak measure limits

The local Bedford–Taylor argument uses finite mass on each compact set and
a common compact set containing the support of the nonnegative test function.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.FirstPass

variable {X : Type*} [MeasurableSpace X]

private theorem integrable_mul_of_compact_bounds
    [TopologicalSpace X] [OpensMeasurableSpace X] [T2Space X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {K : Set X} (hK : IsCompact K) {a b : X → ℝ} {A B : ℝ}
    (ha : Measurable a) (hb : Measurable b) (haK : Function.support a ⊆ K)
    (hA : 0 ≤ A) (habound : ∀ x, |a x| ≤ A)
    (hbbound : ∀ x ∈ K, |b x| ≤ B) :
    Integrable (fun x => a x * b x) μ := by
  rw [← integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_left a b).trans haK)]
  refine IntegrableOn.of_bound hK.measure_lt_top
    (ha.mul hb).aestronglyMeasurable (A * B) ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hxK
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (habound x) (hbbound x hxK) (abs_nonneg _) hA

/-- Compactly supported local form of upper-semicontinuous-weight domination.

The ambient metric space may be noncompact and the positive measures may have
infinite total mass.  It is enough that they are finite on compact sets.  The
sequence is only required to be uniformly bounded on one nonempty compact set
`K` containing the support of the chosen nonnegative test function.  Weak
convergence is correspondingly tested only against continuous compactly
supported functions.

This is the scalar test-function inequality expressing that any weak limit of
the weighted measures is at most `fLim * μ`. -/
theorem uscWeight_weakLimit_integral_le_of_hasCompactSupport
    [PseudoMetricSpace X] [T2Space X] [BorelSpace X]
    (μs : ℕ → Measure X) (μ : Measure X)
    [∀ k, IsFiniteMeasureOnCompacts (μs k)] [IsFiniteMeasureOnCompacts μ]
    (K : Set X) (hK : IsCompact K) (hKne : K.Nonempty)
    (f : ℕ → X → ℝ) (fLim φ : X → ℝ) (Lφ C : ℝ)
    (hfusc : ∀ k, UpperSemicontinuous (f k))
    (hfanti : ∀ x ∈ K, Antitone (fun k => f k x))
    (hflim : ∀ x ∈ K, Tendsto (fun k => f k x) atTop (𝓝 (fLim x)))
    (hfbound : ∀ k x, x ∈ K → |f k x| ≤ C)
    (hφcont : Continuous φ) (hφcompact : HasCompactSupport φ)
    (hφK : Function.support φ ⊆ K) (hφnonneg : ∀ x, 0 ≤ φ x)
    (hμweak : ∀ g : X → ℝ, Continuous g → HasCompactSupport g →
      Tendsto (fun k => ∫ x, g x ∂(μs k)) atTop (𝓝 (∫ x, g x ∂μ)))
    (hweighted : Tendsto (fun k => ∫ x, φ x * f k x ∂(μs k))
      atTop (𝓝 Lφ)) :
    Lφ ≤ ∫ x, φ x * fLim x ∂μ := by
  obtain ⟨A, hAupper⟩ := hφcompact.exists_bound_of_continuous hφcont
  have hA : 0 ≤ A := by
    obtain ⟨x, hxK⟩ := hKne
    exact (abs_nonneg (φ x)).trans (by simpa [Real.norm_eq_abs] using hAupper x)
  have hφbound : ∀ x, |φ x| ≤ A := by
    simpa only [Real.norm_eq_abs] using hAupper
  have hKmeas : MeasurableSet K := hK.measurableSet
  have hzero (x : X) (hxK : x ∉ K) : φ x = 0 := by
    by_contra hx
    exact hxK (hφK hx)
  have hbound_integrable :
      Integrable (K.indicator (fun _ : X => A * C)) μ :=
    (integrableOn_const hK.measure_ne_top).integrable_indicator hKmeas
  have hmain (k₀ : ℕ) : Lφ ≤ ∫ x, φ x * f k₀ x ∂μ := by
    have hmajorant_le_C (m : ℕ) (x : X) :
        uscLipschitzMajorant K (f k₀) (m : ℝ) x ≤ C := by
      calc
        uscLipschitzMajorant K (f k₀) (m : ℝ) x
            ≤ uscLipschitzMajorant K (f k₀) 0 x :=
          uscLipschitzMajorant_antitone hK hKne
            ((hfusc k₀).upperSemicontinuousOn K) (by norm_num)
            (Nat.cast_nonneg _) x
        _ ≤ C := by
          unfold uscLipschitzMajorant
          apply csSup_le (hKne.image _)
          rintro _ ⟨y, hyK, rfl⟩
          simpa using
            (le_trans (le_abs_self (f k₀ y)) (hfbound k₀ y hyK))
    have hmajorant_ge_neg_C (m : ℕ) (x : X) (hxK : x ∈ K) :
        -C ≤ uscLipschitzMajorant K (f k₀) (m : ℝ) x :=
      (neg_le_of_abs_le (hfbound k₀ x hxK)).trans
        (le_uscLipschitzMajorant hK
          ((hfusc k₀).upperSemicontinuousOn K) (Nat.cast_nonneg _) hxK)
    have hmajorant_abs (m : ℕ) (x : X) (hxK : x ∈ K) :
        |uscLipschitzMajorant K (f k₀) (m : ℝ) x| ≤ C :=
      abs_le.2 ⟨hmajorant_ge_neg_C m x hxK, hmajorant_le_C m x⟩
    have hL_le_majorant (m : ℕ) :
        Lφ ≤ ∫ x, φ x * uscLipschitzMajorant K (f k₀) (m : ℝ) x ∂μ := by
      have hmajorant_cont := continuous_uscLipschitzMajorant hK hKne
        ((hfusc k₀).upperSemicontinuousOn K) (Nat.cast_nonneg m)
      have hright := hμweak
        (fun x => φ x * uscLipschitzMajorant K (f k₀) (m : ℝ) x)
        (hφcont.mul hmajorant_cont) hφcompact.mul_right
      exact tendsto_le_of_eventuallyLE hweighted hright
        (eventually_atTop.2 ⟨k₀, fun k hk => by
          have hleftInt : Integrable (fun x => φ x * f k x) (μs k) :=
            integrable_mul_of_compact_bounds hK hφcont.measurable
              (hfusc k).measurable hφK hA hφbound (hfbound k)
          have hrightInt : Integrable
              (fun x => φ x * uscLipschitzMajorant K (f k₀) (m : ℝ) x)
              (μs k) :=
            integrable_mul_of_compact_bounds hK hφcont.measurable
              hmajorant_cont.measurable hφK hA hφbound (hmajorant_abs m)
          apply integral_mono hleftInt hrightInt
          intro x
          by_cases hxK : x ∈ K
          · exact mul_le_mul_of_nonneg_left
              ((hfanti x hxK hk).trans
                (le_uscLipschitzMajorant hK
                  ((hfusc k₀).upperSemicontinuousOn K)
                  (Nat.cast_nonneg _) hxK))
              (hφnonneg x)
          · simp [hzero x hxK]⟩)
    have hmajorant_integrals : Tendsto
        (fun m : ℕ => ∫ x, φ x *
          uscLipschitzMajorant K (f k₀) (m : ℝ) x ∂μ)
        atTop (𝓝 (∫ x, φ x * f k₀ x ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence
        (K.indicator (fun _ : X => A * C))
      · intro m
        exact (hφcont.mul
          (continuous_uscLipschitzMajorant hK hKne
            ((hfusc k₀).upperSemicontinuousOn K)
            (Nat.cast_nonneg m))).measurable.aestronglyMeasurable
      · exact hbound_integrable
      · intro m
        filter_upwards with x
        by_cases hxK : x ∈ K
        · rw [indicator_of_mem hxK, Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hφbound x) (hmajorant_abs m x hxK)
            (abs_nonneg _) hA
        · simp [hxK, hzero x hxK]
      · filter_upwards with x
        by_cases hxK : x ∈ K
        · exact tendsto_const_nhds.mul
            (tendsto_uscLipschitzMajorant_nat hK hKne
              ((hfusc k₀).upperSemicontinuousOn K) hxK)
        · simp [hzero x hxK]
    exact ge_of_tendsto' hmajorant_integrals hL_le_majorant
  have hfinal : Tendsto (fun k => ∫ x, φ x * f k x ∂μ)
      atTop (𝓝 (∫ x, φ x * fLim x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (K.indicator (fun _ : X => A * C))
    · intro k
      exact (hφcont.measurable.mul (hfusc k).measurable).aestronglyMeasurable
    · exact hbound_integrable
    · intro k
      filter_upwards with x
      by_cases hxK : x ∈ K
      · rw [indicator_of_mem hxK, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hφbound x) (hfbound k x hxK) (abs_nonneg _) hA
      · simp [hxK, hzero x hxK]
    · filter_upwards with x
      by_cases hxK : x ∈ K
      · exact tendsto_const_nhds.mul (hflim x hxK)
      · simp [hzero x hxK]
  exact ge_of_tendsto' hfinal hmain

/-- Uniform compactly supported test-order form of USC-weight domination.

Here `ν` records the weak limit functional of the weighted measures on all
continuous compactly supported tests.  The conclusion gives its order against
the expected weighted limit on every nonnegative such test.  Local uniform
boundedness of the weights is used only on a compact set containing the
support of the test currently under consideration. -/
theorem uscWeight_weakLimit_test_integral_le
    [PseudoMetricSpace X] [T2Space X] [BorelSpace X] [Nonempty X]
    (μs : ℕ → Measure X) (μ : Measure X)
    [∀ k, IsFiniteMeasureOnCompacts (μs k)] [IsFiniteMeasureOnCompacts μ]
    (f : ℕ → X → ℝ) (fLim : X → ℝ) (ν : (X → ℝ) → ℝ)
    (hfusc : ∀ k, UpperSemicontinuous (f k))
    (hfanti : ∀ x, Antitone (fun k => f k x))
    (hflim : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (fLim x)))
    (hfbound : ∀ K : Set X, IsCompact K →
      ∃ C : ℝ, ∀ k x, x ∈ K → |f k x| ≤ C)
    (hμweak : ∀ g : X → ℝ, Continuous g → HasCompactSupport g →
      Tendsto (fun k => ∫ x, g x ∂(μs k)) atTop (𝓝 (∫ x, g x ∂μ)))
    (hweighted : ∀ φ : X → ℝ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun k => ∫ x, φ x * f k x ∂(μs k)) atTop (𝓝 (ν φ))) :
    ∀ φ : X → ℝ, Continuous φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → ν φ ≤ ∫ x, φ x * fLim x ∂μ := by
  intro φ hφcont hφcompact hφnonneg
  let K : Set X := tsupport φ ∪ {Classical.choice inferInstance}
  have hK : IsCompact K := hφcompact.union isCompact_singleton
  have hKne : K.Nonempty :=
    ⟨Classical.choice inferInstance, by simp [K]⟩
  have hφK : Function.support φ ⊆ K := by
    intro x hx
    exact Or.inl ((subset_tsupport φ) hx)
  obtain ⟨C, hC⟩ := hfbound K hK
  exact uscWeight_weakLimit_integral_le_of_hasCompactSupport
    μs μ K hK hKne f fLim φ (ν φ) C hfusc
    (fun x _ => hfanti x) (fun x _ => hflim x) hC hφcont hφcompact hφK
    hφnonneg hμweak (hweighted φ hφcont hφcompact)

end SGPT.Foundations.Analysis.FirstPass
