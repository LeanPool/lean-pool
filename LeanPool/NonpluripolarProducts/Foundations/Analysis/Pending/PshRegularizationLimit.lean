/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PshRegularizationData
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.DeficitIntegrability
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PositiveDistributionMeasure
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PlurisubharmonicLimits
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.BallSubmean

/-!
# Pending limit of decreasing smooth PSH approximations

This file proves the limit theorem needed by the first-pass representative
construction. It remains in the Pending layer because its downstream
regularization and gluing dependencies are not yet all discharged.

Source: Demailly, Complex Analytic and Differential Geometry, I.4.20 and I.5.8.

The intended representative is `u x = ⨅ n, (f n x : EReal)`. The common-domain
disc criterion passes to this decreasing limit. Almost-everywhere finiteness
and local integrability must be derived from weak convergence, not assumed.
For each compact `K ⊆ Ω`, choose a nonnegative smooth test function `χ` which
is at least one on `K`, and choose `C` above `f 0` on `tsupport χ`. The weighted
deficits `χ * (C - f n)` increase, and their integrals have a finite limit by
weak convergence against `χ`. Monotone convergence therefore gives finite
deficit integrals on `K`, hence a.e. finiteness and local L1 of the limit.
Dominated convergence on compact test supports then identifies its regular
distribution with `T`.

No connectedness or preassigned nontriviality is required. The cutoff argument
is local on an arbitrary open domain and prevents a component from collapsing
identically to negative infinity while still converging weakly to a real-valued
distribution. Negative-infinity values on null sets remain allowed.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

omit [IsScalarTower ℝ ℂ E] in
/-- On every compact subset of the approximation domain, weak convergence
against a positive cutoff bounds the total deficit of the pointwise infimum. -/
private theorem compact_limit_deficit
    (μ : Measure E) [μ.IsAddHaarMeasure] {Ω : Opens E}
    {T : 𝓓'(Ω, ℝ)} {f : ℕ → E → ℝ}
    (hf : IsDecreasingSmoothPshApproximation μ T f)
    {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ,
      (∀ x ∈ K, (⨅ n, (f n x : EReal)) ≤ (C : EReal)) ∧
      ∫⁻ x in K, ((C : EReal) - (⨅ n, (f n x : EReal))).toENNReal ∂μ < ⊤ := by
  obtain ⟨χ, hχnonneg, hχK⟩ :=
    SGPT.Foundations.Analysis.exists_nonneg_testFunction_one_le_on_compact hK hKΩ
  obtain ⟨C, hC⟩ := χ.hasCompactSupport.exists_bound_of_continuousOn
    (hf.1 0).continuous.continuousOn
  let g : ℕ → E → ℝ := fun n x => χ x * (C - f n x)
  have hg_cont (n : ℕ) : Continuous (g n) :=
    χ.continuous.mul (continuous_const.sub (hf.1 n).continuous)
  have hg_supp (n : ℕ) : HasCompactSupport (g n) :=
    χ.hasCompactSupport.mul_right
  have hg_int (n : ℕ) : Integrable (g n) μ :=
    (hg_cont n).integrable_of_hasCompactSupport (hg_supp n)
  have hC0 : ∀ x ∈ tsupport χ, f 0 x ≤ C := by
    intro x hx
    exact (le_abs_self (f 0 x)).trans (by simpa [Real.norm_eq_abs] using hC x hx)
  have hg_nonneg (n : ℕ) (x : E) : 0 ≤ g n x := by
    by_cases hx : x ∈ tsupport χ
    · exact mul_nonneg (hχnonneg x)
        (sub_nonneg.mpr ((hf.2.2.1 x (χ.tsupport_subset hx) (Nat.zero_le n)).trans (hC0 x hx)))
    · simp [g, image_eq_zero_of_notMem_tsupport hx]
  have hg_mono : Monotone g := by
    intro m n hmn x
    by_cases hx : x ∈ tsupport χ
    · exact mul_le_mul_of_nonneg_left
        (sub_le_sub_left (hf.2.2.1 x (χ.tsupport_subset hx) hmn) C)
        (hχnonneg x)
    · simp [g, image_eq_zero_of_notMem_tsupport hx]
  have hχ_int : Integrable (fun x : E => χ x) μ :=
    χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport
  have hχf_int (n : ℕ) : Integrable (fun x : E => χ x * f n x) μ :=
    (χ.continuous.mul (hf.1 n).continuous).integrable_of_hasCompactSupport
      χ.hasCompactSupport.mul_right
  have hg_integral (n : ℕ) :
      ∫ x, g n x ∂μ = C * ∫ x, χ x ∂μ - ∫ x, χ x * f n x ∂μ := by
    rw [show g n = fun x => C * χ x - χ x * f n x by
      funext x
      simp only [g]
      ring]
    rw [integral_sub (hχ_int.const_mul C) (hχf_int n), integral_const_mul]
  have hg_tendsto : Tendsto (fun n => ∫ x, g n x ∂μ) atTop
      (𝓝 (C * ∫ x, χ x ∂μ - T χ)) := by
    convert tendsto_const_nhds.sub (hf.2.2.2 χ) using 1
    ext n
    exact hg_integral n
  have hg_integral_mono : Monotone (fun n => ∫ x, g n x ∂μ) := by
    intro m n hmn
    exact integral_mono (hg_int m) (hg_int n) (hg_mono hmn)
  have hg_integral_le (n : ℕ) :
      ∫ x, g n x ∂μ ≤ C * ∫ x, χ x ∂μ - T χ :=
    hg_integral_mono.ge_of_tendsto hg_tendsto n
  let G : ℕ → E → ℝ≥0∞ := fun n x => ENNReal.ofReal (g n x)
  have hG_meas (n : ℕ) : Measurable (G n) :=
    (hg_cont n).measurable.ennreal_ofReal
  have hG_mono : Monotone G := by
    intro m n hmn x
    exact ENNReal.ofReal_le_ofReal (hg_mono hmn x)
  have hG_integral (n : ℕ) :
      ∫⁻ x, G n x ∂μ = ENNReal.ofReal (∫ x, g n x ∂μ) := by
    symm
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hg_int n)
      (Eventually.of_forall (hg_nonneg n))
  have hG_sup_lt : ∫⁻ x, ⨆ n, G n x ∂μ < ⊤ := by
    rw [lintegral_iSup hG_meas hG_mono]
    refine lt_of_le_of_lt (iSup_le fun n => ?_)
      (ENNReal.ofReal_lt_top :
        ENNReal.ofReal (C * ∫ x, χ x ∂μ - T χ) < ⊤)
    rw [hG_integral n]
    exact ENNReal.ofReal_le_ofReal (hg_integral_le n)
  refine ⟨C, ?_, (setLIntegral_mono' hK.measurableSet ?_).trans_lt
    ((setLIntegral_le_lintegral K _).trans_lt hG_sup_lt)⟩
  · intro x hx
    refine (iInf_le (fun n => (f n x : EReal)) 0).trans ?_
    exact EReal.coe_le_coe_iff.mpr (hC0 x
      (subset_tsupport χ (ne_of_gt (zero_lt_one.trans_le (hχK x hx)))))
  intro x hx
  rw [SGPT.Foundations.Analysis.finiteDeficit_iInf]
  gcongr with n
  apply ENNReal.ofReal_le_ofReal
  have hdef : 0 ≤ C - f n x := sub_nonneg.mpr
    ((hf.2.2.1 x (hKΩ hx) (Nat.zero_le n)).trans (hC0 x ?_))
  · exact le_mul_of_one_le_left hdef (hχK x hx)
  · exact subset_tsupport χ (ne_of_gt ((zero_lt_one.trans_le (hχK x hx))))

omit [IsScalarTower ℝ ℂ E] in
/-- A decreasing sequence of actual smooth disc-PSH functions which converges
weakly to a distribution produces a genuine PSH representative.
Almost-everywhere finiteness and local L1 are conclusions, including when the
open domain is disconnected. -/
theorem exists_pshRepresentative_of_decreasing_approximation
    (μ : Measure E) [μ.IsAddHaarMeasure] {Ω : Opens E}
    {T : 𝓓'(Ω, ℝ)} {f : ℕ → E → ℝ}
    (hf : IsDecreasingSmoothPshApproximation μ T f) :
    ∃ u : E → EReal, IsPshRepresentative μ T u := by
  let u : E → EReal := fun x => ⨅ n, (f n x : EReal)
  have huD : DiscPshOn u Ω :=
    DiscPshOn.iInf_of_antitone (fun n => hf.2.1 n) (fun x hx => by
      intro m n hmn
      exact EReal.coe_le_coe_iff.mpr (hf.2.2.1 x hx hmn))
  have huP : PlurisubharmonicOn u Ω := huD.plurisubharmonicOn Ω.isOpen
  have hcompact (K : Set E) (hKΩ : K ⊆ Ω) (hK : IsCompact K) :
      (∀ᵐ x ∂μ.restrict K, u x ≠ ⊤ ∧ u x ≠ ⊥) ∧
        IntegrableOn (fun x => (u x).toReal) K μ ∧
        ((fun x => ((u x).toReal : EReal)) =ᶠ[ae (μ.restrict K)] u) := by
    obtain ⟨C, hCu, hCI⟩ := compact_limit_deficit μ hf hK hKΩ
    exact ae_finite_and_integrableOn_of_lintegral_deficit_lt_top hK.measure_lt_top
      (by filter_upwards [ae_restrict_mem hK.measurableSet] with x hx using hCu x hx)
      (huD.aemeasurable_deficit_restrict hK.measurableSet hKΩ C μ) hCI
  have huL : LocallyIntegrableOn (fun x => (u x).toReal) Ω μ := by
    rw [locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed]
    intro K hKΩ hK
    exact (hcompact K hKΩ hK).2.1
  let _ : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  obtain ⟨K, hKcompact, hKcover⟩ := SigmaCompactSpace.exists_compact_covering (X := Ω)
  let L : ℕ → Set E := fun n => Subtype.val '' K n
  have hLcompact (n : ℕ) : IsCompact (L n) :=
    (hKcompact n).image continuous_subtype_val
  have hLΩ (n : ℕ) : L n ⊆ Ω := by
    rintro x ⟨y, -, rfl⟩
    exact y.property
  have hLcover : ⋃ n, L n = (Ω : Set E) := by
    apply Subset.antisymm
    · rw [iUnion_subset_iff]
      exact hLΩ
    · intro x hx
      have hy : (⟨x, hx⟩ : Ω) ∈ ⋃ n, K n := by
        rw [hKcover]
        exact mem_univ _
      obtain ⟨n, hn⟩ := mem_iUnion.mp hy
      exact mem_iUnion_of_mem n ⟨⟨x, hx⟩, hn, rfl⟩
  have huFinite : ∀ᵐ x ∂μ.restrict Ω, u x ≠ ⊤ ∧ u x ≠ ⊥ := by
    rw [← hLcover, ae_restrict_iUnion_iff]
    intro n
    exact (hcompact (L n) (hLΩ n) (hLcompact n)).1
  refine ⟨u, huP, huFinite, huL, ?_⟩
  ext φ
  rw [regularDistribution_apply]
  have hfnL (n : ℕ) : LocallyIntegrableOn (f n) Ω μ :=
    (hf.1 n).continuous.locallyIntegrable.locallyIntegrableOn Ω
  have hφfn (n : ℕ) : Integrable (fun x => φ x * f n x) μ := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) (hfnL n) φ
  have hφu : Integrable (fun x => φ x * (u x).toReal) μ := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) huL φ
  let bound : E → ℝ := fun x => |φ x * f 0 x| + |φ x * (u x).toReal|
  have hbound_int : Integrable bound μ := by
    exact (hφfn 0).abs.add hφu.abs
  have hbound_inside : ∀ᵐ x ∂μ.restrict Ω,
      ∀ n, ‖φ x * f n x‖ ≤ bound x := by
    filter_upwards [huFinite, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
    intro n
    have hu_le : (u x).toReal ≤ f n x :=
      EReal.toReal_le_toReal (iInf_le (fun m => (f m x : EReal)) n)
        hx.2 (EReal.coe_ne_top (f n x))
    have hfn_le : f n x ≤ f 0 x := hf.2.2.1 x hxΩ (Nat.zero_le n)
    have habs : |f n x| ≤ |f 0 x| + |(u x).toReal| := by
      rw [abs_le]
      constructor
      · calc
          -(|f 0 x| + |(u x).toReal|) ≤ -|(u x).toReal| := by
            linarith [abs_nonneg (f 0 x)]
          _ ≤ (u x).toReal := by
            simpa only [abs_neg, neg_neg] using
              neg_le_neg (le_abs_self (-(u x).toReal))
          _ ≤ f n x := hu_le
      · calc
          f n x ≤ f 0 x := hfn_le
          _ ≤ |f 0 x| := le_abs_self _
          _ ≤ |f 0 x| + |(u x).toReal| := le_add_of_nonneg_right (abs_nonneg _)
    simpa only [bound, Real.norm_eq_abs, abs_mul, mul_add] using
      mul_le_mul_of_nonneg_left habs (abs_nonneg (φ x))
  have hφzero (x : E) (hx : x ∉ (Ω : Set E)) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => hx (φ.tsupport_subset h)
  have hbound_outside : ∀ᵐ x ∂μ.restrict (Ω : Set E)ᶜ,
      ∀ n, ‖φ x * f n x‖ ≤ bound x := by
    refine ae_restrict_of_forall_mem Ω.isOpen.measurableSet.compl fun x hx n => ?_
    simp [hφzero x hx, bound]
  have hbound : ∀ n, ∀ᵐ x ∂μ, ‖φ x * f n x‖ ≤ bound x := by
    have hall := ae_of_ae_restrict_of_ae_restrict_compl (Ω : Set E)
      hbound_inside hbound_outside
    exact fun n => hall.mono fun x hx => hx n
  have hlim_inside : ∀ᵐ x ∂μ.restrict Ω,
      Tendsto (fun n => φ x * f n x) atTop (𝓝 (φ x * (u x).toReal)) := by
    filter_upwards [huFinite, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
    apply tendsto_const_nhds.mul
    have he : Tendsto (fun n => (f n x : EReal)) atTop (𝓝 (u x)) := by
      exact tendsto_atTop_iInf (fun m n hmn =>
        EReal.coe_le_coe_iff.mpr (hf.2.2.1 x hxΩ hmn))
    change Tendsto (fun n => ((f n x : EReal)).toReal) atTop (𝓝 (u x).toReal)
    exact (EReal.tendsto_toReal hx.1 hx.2).comp he
  have hlim_outside : ∀ᵐ x ∂μ.restrict (Ω : Set E)ᶜ,
      Tendsto (fun n => φ x * f n x) atTop (𝓝 (φ x * (u x).toReal)) := by
    refine ae_restrict_of_forall_mem Ω.isOpen.measurableSet.compl fun x hx => ?_
    simp [hφzero x hx]
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun n => φ x * f n x) atTop (𝓝 (φ x * (u x).toReal)) :=
    ae_of_ae_restrict_of_ae_restrict_compl (Ω : Set E) hlim_inside hlim_outside
  have hintegral : Tendsto (fun n => ∫ x, φ x * f n x ∂μ) atTop
      (𝓝 (∫ x, φ x * (u x).toReal ∂μ)) :=
    tendsto_integral_of_dominated_convergence bound
      (fun n => (hφfn n).aestronglyMeasurable) hbound_int hbound hlim
  exact tendsto_nhds_unique (hf.2.2.2 φ) hintegral

end SGPT.Foundations.Analysis.Pending
