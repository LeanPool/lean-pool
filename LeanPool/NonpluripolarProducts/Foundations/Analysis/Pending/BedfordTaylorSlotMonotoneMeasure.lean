/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorSlotMonotone

/-!
# Comparing measures by nonnegative tests

`Pending.BedfordTaylorExistence.restrict_eq_of_testFunction_integral_eq` turns
equality of test integrals into equality of restrictions. Slot monotonicity of
the Bedford–Taylor limits is an *inequality* of test integrals, so it needs the
one-sided companion: two measures finite on the compact subsets of an open set
`U`, one of whose test integrals dominates the other's for every nonnegative
continuous test supported in `U`, are ordered on every compact subset of `U`.

The proof is the usual Urysohn argument. A compact `K ⊆ U` is squeezed into an
open `V` with compact closure in `U`; a continuous function equal to `1` on `K`,
to `0` off `V`, and with values in `[0,1]`, bounds the indicator of `K` from
above and the indicator of `V` from below. Outer regularity of the finite
measure `ν` restricted to a relatively compact neighborhood then lets `V`
shrink to `K`.
-/

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- A continuous function bounded by `1` and vanishing off a set of finite
measure is integrable. -/
private theorem integrable_of_le_one_of_support_subset {ρ : Measure (ComplexModel n)}
    {f : ComplexModel n → ℝ} (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z) (hf1 : ∀ z, f z ≤ 1)
    {S : Set (ComplexModel n)} (hS : MeasurableSet S) (hSf : ρ S < ⊤)
    (hsupp : ∀ z ∉ S, f z = 0) : Integrable f ρ := by
  have hind : Integrable (S.indicator (1 : ComplexModel n → ℝ)) ρ :=
    (integrable_indicator_iff hS).mpr (integrableOn_const hSf.ne)
  refine hind.mono' hf.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ S
  · simpa [Set.indicator_of_mem hz, Real.norm_eq_abs, abs_of_nonneg (hf0 z)] using hf1 z
  · simp [Set.indicator_of_notMem hz, hsupp z hz]

/-- **Measure comparison from nonnegative tests.** If every nonnegative
continuous test supported in `U` integrates no more against `μ` than against
`ν`, and both measures are finite on the compact subsets of `U`, then
`μ K ≤ ν K` for every compact `K ⊆ U`. -/
theorem measure_le_of_testFunction_integral_le {U : Opens (ComplexModel n)}
    {μ ν : Measure (ComplexModel n)} (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hνf : ∀ K, IsCompact K → K ⊆ U → ν K < ⊤)
    (h : ∀ φ : ComplexModel n → ℝ, Continuous φ → HasCompactSupport φ →
      tsupport φ ⊆ (U : Set (ComplexModel n)) → (∀ z, 0 ≤ φ z) →
      ∫ z, φ z ∂μ ≤ ∫ z, φ z ∂ν)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKU : K ⊆ (U : Set (ComplexModel n))) :
    μ K ≤ ν K := by
  classical
  obtain ⟨W, hWo, hKW, hWU, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK U.isOpen hKU
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hμK : μ K < ⊤ := hμf K hK hKU
  -- Every open `V` between `K` and `W` already dominates `μ K`.
  have key : ∀ V : Set (ComplexModel n), IsOpen V → K ⊆ V → V ⊆ W → μ K ≤ ν V := by
    intro V hVo hKV hVW
    have hclV : closure V ⊆ (U : Set (ComplexModel n)) := (closure_mono hVW).trans hWU
    have hcV : IsCompact (closure V) := hWc.of_isClosed_subset isClosed_closure (closure_mono hVW)
    have hνclV : ν (closure V) < ⊤ := hνf _ hcV hclV
    have hμclV : μ (closure V) < ⊤ := hμf _ hcV hclV
    have hνV : ν V < ⊤ := lt_of_le_of_lt (measure_mono subset_closure) hνclV
    obtain ⟨f, hf1, hf0, hfc, hf01⟩ :=
      exists_continuous_one_zero_of_isCompact hK hVo.isClosed_compl
        (disjoint_compl_right_iff_subset.mpr hKV)
    set g : ComplexModel n → ℝ := ⇑f with hg
    have hgcont : Continuous g := f.continuous
    have hgnn : ∀ z, 0 ≤ g z := fun z => (hf01 z).1
    have hgle : ∀ z, g z ≤ 1 := fun z => (hf01 z).2
    have hgsupp : ∀ z ∉ V, g z = 0 := fun z hz => hf0 hz
    have hgtsupp : tsupport g ⊆ (U : Set (ComplexModel n)) := by
      refine subset_trans (closure_mono ?_) hclV
      intro z hz
      by_contra hzV
      exact hz (hgsupp z hzV)
    have hgsupp' : ∀ z ∉ closure V, g z = 0 := fun z hz =>
      hgsupp z fun hzV => hz (subset_closure hzV)
    have hintμ : Integrable g μ := integrable_of_le_one_of_support_subset hgcont hgnn hgle
      hcV.measurableSet hμclV hgsupp'
    have hintν : Integrable g ν := integrable_of_le_one_of_support_subset hgcont hgnn hgle
      hcV.measurableSet hνclV hgsupp'
    have hindKμ : Integrable (K.indicator (1 : ComplexModel n → ℝ)) μ :=
      (integrable_indicator_iff hKm).mpr (integrableOn_const hμK.ne)
    have hindVν : Integrable (V.indicator (1 : ComplexModel n → ℝ)) ν :=
      (integrable_indicator_iff hVo.measurableSet).mpr (integrableOn_const hνV.ne)
    have h1 : (μ K).toReal ≤ ∫ z, g z ∂μ := by
      rw [show (μ K).toReal = ∫ z, K.indicator (1 : ComplexModel n → ℝ) z ∂μ from
        (integral_indicator_one hKm).symm]
      refine integral_mono hindKμ hintμ fun z => ?_
      by_cases hz : z ∈ K
      · simp only [Set.indicator_of_mem hz, Pi.one_apply]
        exact le_of_eq (hf1 hz).symm
      · simpa [Set.indicator_of_notMem hz] using hgnn z
    have h2 : (∫ z, g z ∂ν) ≤ (ν V).toReal := by
      rw [show (ν V).toReal = ∫ z, V.indicator (1 : ComplexModel n → ℝ) z ∂ν from
        (integral_indicator_one hVo.measurableSet).symm]
      refine integral_mono hintν hindVν fun z => ?_
      by_cases hz : z ∈ V
      · simpa [Set.indicator_of_mem hz] using hgle z
      · simp [Set.indicator_of_notMem hz, hgsupp z hz]
    have hreal : (μ K).toReal ≤ (ν V).toReal :=
      h1.trans ((h g hgcont hfc hgtsupp hgnn).trans h2)
    exact (ENNReal.toReal_le_toReal hμK.ne hνV.ne).mp hreal
  -- Shrink `V` to `K` using outer regularity of the finite measure `ν.restrict W`.
  have hfinν : IsFiniteMeasure (ν.restrict W) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono subset_closure) (hνf _ hWc hWU)
  have hrestrictK : ν.restrict W K = ν K := by
    rw [Measure.restrict_apply hKm, inter_eq_self_of_subset_left hKW]
  rw [← hrestrictK, Set.measure_eq_iInf_isOpen K (ν.restrict W)]
  refine le_iInf₂ fun V hKV => le_iInf fun hVo => ?_
  rw [Measure.restrict_apply hVo.measurableSet]
  exact key (V ∩ W) (hVo.inter hWo) (subset_inter hKV hKW) inter_subset_right

/-- **Slot monotonicity of the bounded mixed products, as measures.** Adding a
smooth positive semidefinite function in one slot does not decrease the mixed
Bedford–Taylor limit on any compact subset of the domain. -/
theorem IsBTLimit.measure_le_add_smoothPsd {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {μ ν : Measure (ComplexModel n)} (hμ : IsBTLimit Ω u μ)
    (i₀ : Fin n) {s : ComplexModel n → ℝ} (hs : IsSmoothPsdOn Ω s)
    (hν : IsBTLimit Ω (Function.update u i₀ fun z => u i₀ z + s z) ν)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ (Ω : Set (ComplexModel n))) :
    μ K ≤ ν K :=
  measure_le_of_testFunction_integral_le hμ.2.1 hν.2.1
    (fun _ hφ hφc hφΩ hφ0 => hμ.integral_le_add_smoothPsd i₀ hs hν hφ hφc hφΩ hφ0) hK hKΩ

end SGPT.Foundations.Analysis.Pending.BedfordTaylor
