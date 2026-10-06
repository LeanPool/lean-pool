/-
Copyright (c) 2026 FormalizingGMT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalizingGMT contributors
-/
module

public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Densities obtained from singular integrals

This file develops density results for measures using Vitali families associated to locally
doubling measures and singular-integral estimates.
-/

@[expose] public section

open MeasureTheory Measure Metric Filter Set Topology
open scoped NNReal ENNReal MeasureTheory

noncomputable section

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- A Radon measure is a regular Borel measure. -/
def IsRadon {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) : Prop :=
  μ.Regular

/-! ## Vitali family from doubling measure -/

/-- Construction of a VitaliFamily from a uniformly locally doubling measure,
using the Vitali covering theorem. -/
def doublingVitaliFamily
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [IsUnifLocDoublingMeasure μ] :
    VitaliFamily μ :=
  Vitali.vitaliFamily μ (IsUnifLocDoublingMeasure.scalingConstantOf μ 3) (fun x => by
    have hR := IsUnifLocDoublingMeasure.scalingScaleOf_pos μ (3 : ℝ)
    apply Filter.Eventually.frequently
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds hR] with r hr hr'
    exact IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul μ
      (show (3 : ℝ) ∈ Ioc 0 3 from ⟨by norm_num, le_refl _⟩) (le_of_lt hr))

/-! ## Theorem 2.10: Hausdorff measure and integrals over balls -/

/-- The s-dimensional density limsup of the integral of `‖f‖` over balls. -/
def integralDensityLimsup (μ : Measure X) (f : X → ℝ) (s : ℝ) (x : X) : ℝ≥0∞ :=
  Filter.limsup
    (fun r => (∫⁻ y in closedBall x r, ‖f y‖ₑ ∂μ) / ENNReal.ofReal (r ^ s))
    (𝓝[>] (0 : ℝ))

/-- The set `Λ_s` where the density limsup is positive. -/
def integralDensitySet (μ : Measure X) (f : X → ℝ) (s : ℝ) : Set X :=
  {x | 0 < integralDensityLimsup μ f s x}

/-- For closed balls of sufficiently small radius, the ball belongs to the
Vitali family's `setsAt`. -/
lemma closedBall_mem_doublingVitali_setsAt
    {μ : Measure X} [IsLocallyFiniteMeasure μ] [IsUnifLocDoublingMeasure μ]
    (x : X) {r : ℝ} (hr : 0 < r)
    (hrS : r ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ 3) :
    closedBall x r ∈ (doublingVitaliFamily μ).setsAt x := by
  refine ⟨Metric.isClosed_closedBall, ?_, ?_⟩
  · exact ⟨ x, mem_interior_iff_mem_nhds.mpr ( Metric.closedBall_mem_nhds _ hr ) ⟩
  · refine ⟨r, Set.Subset.rfl, ?_⟩
    convert IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul μ
      (show (3 : ℝ) ∈ Set.Ioc 0 3 by norm_num) hrS using 1

/-- The VitaliFamily filter at x receives the function r ↦ closedBall x r. -/
lemma tendsto_closedBall_doublingVitali_filterAt
    {μ : Measure X} [IsLocallyFiniteMeasure μ] [IsUnifLocDoublingMeasure μ]
    (x : X) :
    Tendsto (closedBall x) (𝓝[>] (0 : ℝ)) ((doublingVitaliFamily μ).filterAt x) := by
  refine Filter.tendsto_inf.mpr ⟨?_, ?_⟩
  · rw [ Filter.tendsto_smallSets_iff ]
    intro t ht;
    rcases Metric.mem_nhds_iff.1 ht with ⟨ ε, εpos, hε ⟩
    filter_upwards [Ioo_mem_nhdsGT εpos] with r hr using
      Set.Subset.trans (closedBall_subset_ball hr.2) hε
  · simp +decide only [tendsto_principal];
    filter_upwards [Ioo_mem_nhdsGT
      (show 0 < IsUnifLocDoublingMeasure.scalingScaleOf μ 3 from
        IsUnifLocDoublingMeasure.scalingScaleOf_pos μ 3)] with r hr using
      closedBall_mem_doublingVitali_setsAt x hr.1 hr.2.le

/-- For a.e. x, the integral density limsup equals zero. -/
lemma ae_integralDensityLimsup_eq_zero
    {μ : Measure X} [IsLocallyFiniteMeasure μ] [IsUnifLocDoublingMeasure μ]
    (_hμ : IsRadon μ)
    {f : X → ℝ} (hf : LocallyIntegrable f μ)
    {s : ℝ} (_hs : 0 ≤ s)
    (hdim : ∀ᵐ x ∂μ,
      Tendsto (fun r => μ (closedBall x r) / ENNReal.ofReal (r ^ s))
        (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ᵐ x ∂μ, integralDensityLimsup μ f s x = 0 := by
  have := @VitaliFamily.ae_tendsto_lintegral_enorm_sub_div X
  specialize this ( doublingVitaliFamily μ ) hf
  have h_le : ∀ᵐ x ∂μ, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (∫⁻ y in closedBall x r, ‖f y‖ₑ ∂μ) ≤
        (‖f x‖ₑ + 1) * μ (closedBall x r) := by
    filter_upwards [ this ] with x hx
    have h_le : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        (∫⁻ y in closedBall x r, ‖f y - f x‖ₑ ∂μ) ≤ μ (closedBall x r) := by
      have h_le : ∀ᶠ r in 𝓝[>] (0 : ℝ),
          (∫⁻ y in closedBall x r, ‖f y - f x‖ₑ ∂μ) / μ (closedBall x r) ≤ 1 := by
        have := hx.comp ( tendsto_closedBall_doublingVitali_filterAt x )
        filter_upwards [this.eventually (ge_mem_nhds zero_lt_one)] with r hr using by
          simpa using hr
      filter_upwards [ h_le, self_mem_nhdsWithin ] with r hr hr'
      rw [ ENNReal.div_le_iff_le_mul ] at hr <;> aesop
    filter_upwards [ h_le, self_mem_nhdsWithin ] with r hr hr'
    have h_le : ∫⁻ y in closedBall x r, ‖f y‖ₑ ∂μ ≤
        ∫⁻ y in closedBall x r, (‖f y - f x‖ₑ + ‖f x‖ₑ) ∂μ := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_closedBall] with y hy using by
        simpa using enorm_add_le (f y - f x) (f x)
    rw [MeasureTheory.lintegral_add_right'] at h_le
    · have hconst : (∫⁻ _y in closedBall x r, ‖f x‖ₑ ∂μ) =
          ‖f x‖ₑ * μ (closedBall x r) := by simp
      refine h_le.trans ?_
      rw [hconst]
      calc
        (∫⁻ y in closedBall x r, ‖f y - f x‖ₑ ∂μ) +
            ‖f x‖ₑ * μ (closedBall x r) ≤
            μ (closedBall x r) + ‖f x‖ₑ * μ (closedBall x r) :=
          add_le_add_left hr _
        _ = (‖f x‖ₑ + 1) * μ (closedBall x r) := by
          rw [add_mul, one_mul, add_comm]
    · fun_prop
  filter_upwards [ hdim, h_le ] with x hx₁ hx₂
  have h_le : ∀ᶠ r in 𝓝[>] (0 : ℝ),
  (∫⁻ y in closedBall x r, ‖f y‖ₑ ∂μ) / ENNReal.ofReal (r ^ s) ≤ (‖f x‖ₑ + 1) * (μ (closedBall x r)
  / ENNReal.ofReal (r ^ s)) := by
    filter_upwards [ hx₂ ] with r hr
    rw [ mul_div ]
    gcongr;
  have h_le : Filter.Tendsto
      (fun r => (‖f x‖ₑ + 1) * (μ (closedBall x r) / ENNReal.ofReal (r ^ s)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert ENNReal.Tendsto.const_mul hx₁ _ using 1 <;> norm_num;
  exact Filter.Tendsto.limsup_eq
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_le
      (Filter.eventually_of_mem ‹_› fun _r _hr => zero_le)
      (Filter.eventually_of_mem ‹_› fun _r hr => hr))

/-- The base measure μ of the density set is zero. -/
lemma measure_integralDensitySet_eq_zero
    {μ : Measure X} [IsLocallyFiniteMeasure μ] [IsUnifLocDoublingMeasure μ]
    (hμ : IsRadon μ)
    {f : X → ℝ} (hf : LocallyIntegrable f μ)
    {s : ℝ} (hs : 0 ≤ s)
    (hdim : ∀ᵐ x ∂μ,
      Tendsto (fun r => μ (closedBall x r) / ENNReal.ofReal (r ^ s))
        (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    μ (integralDensitySet μ f s) = 0 := by
  convert MeasureTheory.measure_mono_null _ ( ae_integralDensityLimsup_eq_zero hμ hf hs hdim );
  exact fun x hx => ne_of_gt hx

lemma measure_integralDensitySetAbove_eq_zero
    {μ : Measure X} [IsLocallyFiniteMeasure μ] [IsUnifLocDoublingMeasure μ]
    (hμ : IsRadon μ)
    {f : X → ℝ} (hf : LocallyIntegrable f μ)
    {s : ℝ} (hs : 0 ≤ s)
    (hdim : ∀ᵐ x ∂μ,
      Tendsto (fun r => μ (closedBall x r) / ENNReal.ofReal (r ^ s))
        (𝓝[>] (0 : ℝ)) (𝓝 0))
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    μ {x | ε < integralDensityLimsup μ f s x} = 0 := by
  refine MeasureTheory.measure_mono_null ?_
    (measure_integralDensitySet_eq_zero hμ hf hs hdim)
  exact fun x hx => lt_trans hε hx

omit [SecondCountableTopology X] [BorelSpace X] in
lemma exists_open_supset_small_integral
    {μ : Measure X}
    (hμ : IsRadon μ)
    {S : Set X} (hS : μ S = 0)
    {g : X → ℝ≥0∞} (hg : ∫⁻ x, g x ∂μ ≠ ⊤)
    {σ : ℝ≥0∞} (hσ : 0 < σ) :
    ∃ U : Set X, IsOpen U ∧ S ⊆ U ∧ ∫⁻ x in U, g x ∂μ < σ := by
  obtain ⟨U_n, hU_n_open, hU_n_cont, hU_n_zero⟩ :
      ∃ U_n : ℕ → Set X, (∀ n, IsOpen (U_n n)) ∧ (∀ n, S ⊆ U_n n) ∧
        Filter.Tendsto (fun n => μ (U_n n)) Filter.atTop (nhds 0) := by
    have h_outer_regular : ∀ ε > 0, ∃ U : Set X, IsOpen U ∧ S ⊆ U ∧ μ U < ε := by
      intro ε hε
      have := hμ.outerRegular
      contrapose! this
      refine ⟨MeasureTheory.toMeasurable μ S,
        MeasureTheory.measurableSet_toMeasurable _ _, ε, ?_, ?_⟩
      · rw [ MeasureTheory.measure_toMeasurable ] ; aesop
      · exact fun U hU hU' => this U hU' ( hU.trans' ( subset_toMeasurable _ _ ) )
    choose U hU using h_outer_regular
    let U_n : ℕ → Set X := fun n => U (1 / 2 ^ n) (by simp +decide)
    refine ⟨U_n, ?_, ?_, ?_⟩
    · intro n
      simpa only [U_n] using (hU (1 / 2 ^ n) (by simp +decide)).1
    · intro n
      simpa only [U_n] using (hU (1 / 2 ^ n) (by simp +decide)).2.1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun n => zero_le) (fun n => by
        simpa only [U_n] using (hU (1 / 2 ^ n) (by simp +decide)).2.2.le)
    · norm_num [ ENNReal.inv_pow ]
  have h_integral_zero : Filter.Tendsto (fun n => ∫⁻ x in U_n n, g x ∂μ) Filter.atTop (nhds 0) := by
    apply_rules [ tendsto_setLIntegral_zero ]
  exact Filter.Eventually.exists (h_integral_zero.eventually (gt_mem_nhds hσ)) |>
    fun ⟨n, hn⟩ => ⟨U_n n, hU_n_open n, hU_n_cont n, hn⟩

/-
If S can be covered by countable families with diameters and costs tending to 0,
then its Hausdorff measure is 0.
-/
omit [SecondCountableTopology X] in
lemma hausdorff_measure_eq_zero_of_coverings
    {S : Set X} {s : ℝ}
    (h : ∀ n : ℕ, ∃ (ι : Type _) (_ : Countable ι) (E : ι → Set X),
      S ⊆ ⋃ i, E i ∧
      (∀ i, Metric.ediam (E i) ≤ ENNReal.ofReal (1 / (↑n + 1))) ∧
      ∑' i, Metric.ediam (E i) ^ s ≤ ENNReal.ofReal (1 / (↑n + 1))) :
    μH[s] S = 0 := by
  apply le_antisymm
  · have h_liminf : Filter.liminf (fun n : ℕ => ∑' i : Classical.choose (h n),
        Metric.ediam (Classical.choose_spec (h n) |>.2.choose i) ^ s) Filter.atTop ≤ 0 := by
      refine Filter.Tendsto.liminf_eq ?_ |> le_of_eq
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat)
        (fun n => zero_le) fun n => Classical.choose_spec (h n) |>.2.choose_spec.2.2
    refine le_trans ?_ h_liminf
    let _ (n : ℕ) : Countable (Classical.choose (h n)) :=
      Classical.choose_spec (h n) |>.1
    exact hausdorffMeasure_le_liminf_tsum s S
      (fun n : ℕ => ENNReal.ofReal (1 / (n + 1)))
      (by simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat)
      (fun n i => Classical.choose_spec (h n) |>.2.choose i)
      (Filter.Eventually.of_forall fun n i =>
        Classical.choose_spec (h n) |>.2.choose_spec.2.1 i)
      (Filter.Eventually.of_forall fun n =>
        Classical.choose_spec (h n) |>.2.choose_spec.1)
  · exact zero_le

omit [SecondCountableTopology X] [BorelSpace X] in
lemma choose_radii_in_open_set
    {μ : Measure X}
    {S U : Set X} (hU : IsOpen U) (hSU : S ⊆ U)
    {g : X → ℝ≥0∞}
    {s : ℝ}
    {ε : ℝ≥0∞}
    {δ : ℝ} (hδ : 0 < δ)
    (hcover : ∀ x ∈ S, ∀ δ' > (0 : ℝ), ∃ r : ℝ, 0 < r ∧ r < δ' ∧
      ε * ENNReal.ofReal (r ^ s) < ∫⁻ y in closedBall x r, g y ∂μ) :
    ∃ rad : X → ℝ, (∀ x ∈ S, 0 < rad x ∧ rad x < δ ∧
      closedBall x (rad x) ⊆ U ∧
      ε * ENNReal.ofReal (rad x ^ s) < ∫⁻ y in closedBall x (rad x), g y ∂μ) := by
  choose! rad hrad using hcover
  have h_rad : ∀ x ∈ S, ∃ r > 0, r < δ ∧ closedBall x r ⊆ U ∧
      ε * ENNReal.ofReal (r ^ s) < ∫⁻ y in closedBall x r, g y ∂μ := by
    intro x hx
    obtain ⟨d, hd_pos, hd_ball⟩ : ∃ d > 0, closedBall x d ⊆ U := by
      exact Metric.nhds_basis_closedBall.mem_iff.mp ( hU.mem_nhds ( hSU hx ) )
    have hr := hrad x hx _ (lt_min hδ hd_pos)
    exact ⟨rad x (Min.min δ d), hr.1,
      hr.2.1.trans_le (min_le_left _ _),
      Set.Subset.trans
        (Metric.closedBall_subset_closedBall
          (hr.2.1.le.trans (min_le_right _ _))) hd_ball,
      hr.2.2⟩
  choose! rad hrad using h_rad
  exact ⟨ rad, hrad ⟩

omit [MeasurableSpace X] [BorelSpace X] in
lemma vitali_countable_covering
    {S : Set X}
    {rad : X → ℝ} (hrad : ∀ x ∈ S, 0 < rad x)
    {R : ℝ} (hR : ∀ x ∈ S, rad x ≤ R) :
    ∃ u : Set X, u ⊆ S ∧ u.Countable ∧
      u.PairwiseDisjoint (fun x => closedBall x (rad x)) ∧
      S ⊆ ⋃ x ∈ u, closedBall x (4 * rad x) := by
  obtain ⟨u, hu⟩ : ∃ (u : Set X), u ⊆ S ∧
      (u.PairwiseDisjoint (fun x => closedBall x (rad x))) ∧
      ∀ x ∈ S, ∃ b ∈ u, closedBall x (rad x) ⊆ closedBall b (4 * rad b) := by
    simpa only [id_eq] using
      (Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
        S id rad R hR 4 (by norm_num))
  refine ⟨u, hu.1, ?_, hu.2.1, ?_⟩
  · have h_interior : ∀ x ∈ u, (interior (closedBall x (rad x))).Nonempty := by
      exact fun x hx => ⟨x, mem_interior_iff_mem_nhds.mpr
        (Metric.closedBall_mem_nhds _ (hrad x (hu.1 hx)))⟩
    exact hu.2.1.countable_of_nonempty_interior h_interior
  · exact fun x hx => by
      rcases hu.2.2 x hx with ⟨b, hb, h⟩
      exact Set.mem_iUnion₂.2
        ⟨b, hb, h (Metric.mem_closedBall_self (le_of_lt (hrad x hx)))⟩

omit [SecondCountableTopology X] in
lemma tsum_lintegral_le_of_pairwise_disjoint
    {μ : Measure X}
    {u : Set X} (hu_count : u.Countable)
    {rad : X → ℝ}
    (hpd : u.PairwiseDisjoint (fun x => closedBall x (rad x)))
    {U : Set X} (hBU : ∀ x ∈ u, closedBall x (rad x) ⊆ U)
    {g : X → ℝ≥0∞} :
    ∑' (x : u), ∫⁻ y in closedBall (↑x) (rad ↑x), g y ∂μ ≤ ∫⁻ y in U, g y ∂μ := by
  have h_integrals_subadd : ∀ (s : Set X), MeasurableSet s → s ⊆ U →
      ∫⁻ y in s, g y ∂μ ≤ ∫⁻ y in U, g y ∂μ := by
    exact fun s hs hsU => MeasureTheory.lintegral_mono_set hsU
  have h_integrals_subadd : ∫⁻ y in ⋃ x ∈ u, closedBall x (rad x), g y ∂μ ≤ ∫⁻ y in U, g y ∂μ := by
    apply h_integrals_subadd
    · exact MeasurableSet.biUnion hu_count fun x hx => measurableSet_closedBall
    · exact Set.iUnion₂_subset fun x hx => hBU x hx
  refine le_trans ?_ h_integrals_subadd
  rw [ MeasureTheory.lintegral_biUnion ]
  · exact hu_count
  · exact fun x hx => measurableSet_closedBall
  · exact hpd

/-
Helper: ediam of a closed ball is at most 2r.
-/
omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma ediam_closedBall_le_two_mul (x : X) {r : ℝ} :
    Metric.ediam (closedBall x r) ≤ ENNReal.ofReal (2 * r) :=
  Metric.ediam_le_of_forall_dist_le fun y hy z hz =>
    (dist_triangle_right _ _ _).trans <| by
      linarith [Metric.mem_closedBall.1 hy, Metric.mem_closedBall.1 hz]

/-
The diameter bound: ediam(closedBall z (4*r)) ≤ ofReal(1/(n+1))
when r < 1/(8*(n+1)).
-/
omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma ediam_four_ball_le {x : X} {r : ℝ} {n : ℕ}
    (hr : r < 1 / (8 * (↑n + 1))) :
    Metric.ediam (closedBall x (4 * r)) ≤ ENNReal.ofReal (1 / (↑n + 1)) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h_real : 2 * (4 * r) ≤ 1 / ((n : ℝ) + 1) := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 8 * ((n : ℝ) + 1))] at hr
    rw [le_div_iff₀ hn]
    linarith
  exact (ediam_closedBall_le_two_mul (x := x)).trans (ENNReal.ofReal_le_ofReal h_real)

/-
The rpow bound: ediam(closedBall z (4*r))^s ≤ ofReal(8^s) * ofReal(r^s).
-/
omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma ediam_four_ball_rpow_le {x : X} {r : ℝ} (hr : 0 < r)
    {s : ℝ} (hs : 0 ≤ s) :
    Metric.ediam (closedBall x (4 * r)) ^ s ≤
      ENNReal.ofReal (8 ^ s) * ENNReal.ofReal (r ^ s) := by
  have h1 : Metric.ediam (closedBall x (4 * r)) ≤ ENNReal.ofReal (8 * r) := by
    have := ediam_closedBall_le_two_mul (x := x) (r := 4 * r)
    rwa [show (2 : ℝ) * (4 * r) = 8 * r from by ring] at this
  calc Metric.ediam (closedBall x (4 * r)) ^ s
      ≤ ENNReal.ofReal (8 * r) ^ s := ENNReal.rpow_le_rpow h1 hs
    _ = ENNReal.ofReal ((8 * r) ^ s) := ENNReal.ofReal_rpow_of_pos (by positivity)
    _ = ENNReal.ofReal (8 ^ s * r ^ s) := by rw [Real.mul_rpow (by norm_num) hr.le]
    _ = ENNReal.ofReal (8 ^ s) * ENNReal.ofReal (r ^ s) := ENNReal.ofReal_mul (by positivity)

/-
If S has measure zero and is covered by balls where the integral exceeds
ε times the radius to the power s, then H^s(S) = 0.
This is the core Vitali covering argument.
-/
lemma hausdorff_measure_zero_of_ball_integral_bound
    {μ : Measure X}
    {S : Set X} (hS : μ S = 0) (hμR : IsRadon μ)
    {g : X → ℝ≥0∞} (hg : ∫⁻ x, g x ∂μ ≠ ⊤)
    {s : ℝ} (hs : 0 ≤ s)
    {ε : ℝ≥0∞} (hε : 0 < ε)
    (hcover : ∀ x ∈ S, ∀ δ > (0 : ℝ), ∃ r : ℝ, 0 < r ∧ r < δ ∧
      ε * ENNReal.ofReal (r ^ s) < ∫⁻ y in closedBall x r, g y ∂μ) :
    μH[s] S = 0 := by
  apply hausdorff_measure_eq_zero_of_coverings
  intro n
  set C := ENNReal.ofReal (8 ^ s)
  -- Choose integral threshold small enough: ε / ((C + 1) * (n + 1))
  -- so that C/ε * threshold ≤ 1/(n+1)
  have h_threshold_pos : (0 : ℝ≥0∞) < ε / ((C + 1) * (↑n + 1)) := by
    apply ENNReal.div_pos (ne_of_gt hε)
    exact ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩)
      (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩)
  obtain ⟨U, hU_open, hSU_n, hU_int⟩ :=
    exists_open_supset_small_integral hμR hS hg h_threshold_pos
  -- Choose radii
  obtain ⟨rad, hrad⟩ := choose_radii_in_open_set hU_open hSU_n
    (show (0 : ℝ) < 1 / (8 * (↑n + 1)) by positivity) hcover
  -- Vitali covering extraction
  obtain ⟨u, hu_sub, hu_count, hu_disj, hu_cov⟩ := vitali_countable_covering
    (fun x hx => (hrad x hx).1) (fun x hx => le_of_lt (hrad x hx).2.1)
  refine ⟨↑u, hu_count.to_subtype, fun z => closedBall (↑z) (4 * rad ↑z), ?_, ?_, ?_⟩
  -- Coverage
  · intro x hx
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (hu_cov hx)
    exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hxz⟩
  -- Diameter bound
  · intro ⟨z, hz⟩
    exact ediam_four_ball_le (hrad z (hu_sub hz)).2.1
  -- Cost bound
  · have h_sum_le_integral :
        ∑' i : u, ∫⁻ y in closedBall (i : X) (rad i), g y ∂μ ≤
          ∫⁻ y in U, g y ∂μ := by
      apply_rules [ tsum_lintegral_le_of_pairwise_disjoint ]
      exact fun x hx => hrad x ( hu_sub hx ) |>.2.2.1
    have h_sum_le_integral : ∑' i : u, ENNReal.ofReal (rad i ^ s) < 1 / ((C + 1) * (n + 1)) := by
      have h_sum_le_integral :
          ε * ∑' i : u, ENNReal.ofReal (rad i ^ s) <
            ε / ((C + 1) * (n + 1)) := by
        rw [ ← ENNReal.tsum_mul_left ]
        exact lt_of_le_of_lt
          (ENNReal.tsum_le_tsum fun i => le_of_lt (hrad i (hu_sub i.2) |>.2.2.2))
          (lt_of_le_of_lt h_sum_le_integral hU_int)
      contrapose! h_sum_le_integral
      simpa only [div_eq_mul_inv, one_div, one_mul,
        ENNReal.inv_mul_cancel
          (by aesop : (C + 1) * (n + 1 : ENNReal) ≠ 0)
          (by aesop : (C + 1) * (n + 1 : ENNReal) ≠ ⊤)] using
        mul_le_mul_right h_sum_le_integral ε
    have h_sum_le_integral :
        ∑' i : u, Metric.ediam (closedBall (i : X) (4 * rad i)) ^ s
          ≤ C * ∑' i : u, ENNReal.ofReal (rad i ^ s) := by
      rw [← ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum fun i =>
        ediam_four_ball_rpow_le (show (0 : ℝ) < rad i from (hrad i (hu_sub i.2)).1) hs
    refine le_trans h_sum_le_integral ?_
    refine le_trans (mul_le_mul_right (le_of_lt ‹_›) _) ?_
    rw [ mul_one_div, ENNReal.div_le_iff_le_mul ] <;> norm_num
    · rw [ mul_left_comm, ENNReal.ofReal_inv_of_pos ]
      · rw [ ENNReal.ofReal_add ] <;> norm_num
        rw [ ENNReal.inv_mul_cancel ] <;> norm_num
      · exact_mod_cast Nat.succ_pos n
    · exact Or.inl (ENNReal.mul_ne_top
        (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩)
        (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, ENNReal.one_ne_top⟩))

/-
Core Vitali covering argument for integrable functions.
-/
lemma hausdorff_integralDensitySetAbove_zero_of_integrable
    {μ : Measure X} [IsLocallyFiniteMeasure μ] [IsUnifLocDoublingMeasure μ]
    (hμ : IsRadon μ)
    {f : X → ℝ} (hf_int : Integrable f μ) (hf_loc : LocallyIntegrable f μ)
    {s : ℝ} (hs : 0 ≤ s)
    (hdim : ∀ᵐ x ∂μ,
      Tendsto (fun r => μ (closedBall x r) / ENNReal.ofReal (r ^ s))
        (𝓝[>] (0 : ℝ)) (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    μH[s] {x | ε < integralDensityLimsup μ f s x} = 0 := by
  apply hausdorff_measure_zero_of_ball_integral_bound
    (measure_integralDensitySetAbove_eq_zero hμ hf_loc hs hdim ε hε) hμ
    (ne_of_lt hf_int.2) hs hε
  intro x hx δ hδ
  have hfreq : ∃ᶠ r in 𝓝[>] (0 : ℝ),
      ε < (∫⁻ y in closedBall x r, ‖f y‖ₑ ∂μ) / ENNReal.ofReal (r ^ s) := by
    apply Filter.frequently_lt_of_lt_limsup _ hx
    exact isCoboundedUnder_le_of_le _ (fun _ => OrderBot.bot_le _)
  obtain ⟨r, ⟨hrε, hr⟩⟩ := (hfreq.and_eventually (Ioo_mem_nhdsGT hδ)).exists
  refine ⟨r, hr.1, hr.2, ?_⟩
  have h1 := ENNReal.mul_lt_of_lt_div hrε
  exact h1

lemma hausdorff_measure_integralDensitySetAbove_zero
    {μ : Measure X} [IsLocallyFiniteMeasure μ] [IsUnifLocDoublingMeasure μ]
    (hμ : IsRadon μ)
    {f : X → ℝ} (hf : LocallyIntegrable f μ)
    {s : ℝ} (hs : 0 ≤ s)
    (hdim : ∀ᵐ x ∂μ,
      Tendsto (fun r => μ (closedBall x r) / ENNReal.ofReal (r ^ s))
        (𝓝[>] (0 : ℝ)) (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    μH[s] {x | ε < integralDensityLimsup μ f s x} = 0 := by
  obtain ⟨U, hU⟩ : ∃ U : ℕ → Set X, (∀ n, IsOpen (U n)) ∧
      (∀ n, MeasureTheory.IntegrableOn f (U n) μ) ∧ ⋃ n, U n = Set.univ := by
    have h_loc_int : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        MeasureTheory.IntegrableOn f U μ := by
      intro x
      rcases hf x with ⟨ U, hU, hU' ⟩
      exact ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.mpr hU,
        hU'.mono_set interior_subset⟩
    choose U hU using h_loc_int
    obtain ⟨T, hT_count, hT_cover⟩ :=
      TopologicalSpace.isOpen_iUnion_countable (fun x => U x) fun x => (hU x).1
    have h_cover : ⋃ x, U x = Set.univ := by
      apply Set.eq_univ_of_forall
      exact fun x => Set.mem_iUnion.mpr ⟨x, (hU x).2.1⟩
    rcases T.eq_empty_or_nonempty with hT_empty | hT_nonempty
    · have h_empty_univ : (∅ : Set X) = Set.univ := by
        calc
          ∅ = ⋃ i ∈ T, U i := by simp [hT_empty]
          _ = ⋃ i, U i := hT_cover
          _ = Set.univ := h_cover
      exact ⟨fun _ => ∅, fun _ => isOpen_empty,
        fun _ => by simp only [MeasureTheory.integrableOn_empty], by simpa using h_empty_univ⟩
    · obtain ⟨f, hf⟩ := hT_count.exists_eq_range hT_nonempty
      refine ⟨fun n => U (f n), fun n => (hU _).1, fun n => (hU _).2.2, ?_⟩
      apply Set.eq_univ_of_forall
      intro x
      have hx : x ∈ ⋃ i ∈ T, U i := by
        rw [hT_cover, h_cover]
        exact Set.mem_univ x
      rcases Set.mem_iUnion₂.mp hx with ⟨i, hi, hxi⟩
      rw [hf] at hi
      rcases hi with ⟨n, rfl⟩
      exact Set.mem_iUnion.mpr ⟨n, hxi⟩
  have h_zero_measure : ∀ n, μH[s] ({x | ε < integralDensityLimsup μ f s x} ∩ U n) = 0 := by
    intro n
    have h_integrable : IntegrableOn f (U n) μ := hU.right.left n
    have h_indicator : ∀ x ∈ U n, ∀ᶠ r in 𝓝[>] 0,
        ∫⁻ y in closedBall x r, ‖f y‖ₑ ∂μ =
          ∫⁻ y in closedBall x r, ‖(U n).indicator f y‖ₑ ∂μ := by
      intro x hx
      obtain ⟨r, hr_pos, hr_ball⟩ : ∃ r > 0, Metric.closedBall x r ⊆ U n := by
        exact Metric.nhds_basis_closedBall.mem_iff.mp ( hU.1 n |> IsOpen.mem_nhds <| hx )
      filter_upwards [ Ioo_mem_nhdsGT hr_pos ] with r hr
      rw [ MeasureTheory.setLIntegral_congr_fun ]
      · exact measurableSet_closedBall
      · intro y hy
        simp +decide [Set.indicator_of_mem (hr_ball <| Metric.mem_closedBall.mpr <|
          le_trans (Metric.mem_closedBall.mp hy) hr.2.le)]
    have h_indicator2 : ∀ x ∈ U n,
        integralDensityLimsup μ f s x =
          integralDensityLimsup μ (U n |>.indicator f) s x := by
      intro x hx
      simp only [integralDensityLimsup]
      rw [ Filter.limsup_congr ( by filter_upwards [ h_indicator x hx ] with r hr; rw [ hr ] ) ];
    have h_zero_measure : μH[s] {x | ε < integralDensityLimsup μ (U n |>.indicator f) s x} = 0 := by
      apply_rules [ hausdorff_integralDensitySetAbove_zero_of_integrable ]
      · rw [ integrable_indicator_iff ( hU.1 n |> IsOpen.measurableSet ) ] ; aesop
      · intro x
        have := hf x
        obtain ⟨ t, ht₁, ht₂ ⟩ := this
        refine ⟨t, ht₁, ?_⟩
        apply ht₂.indicator
        exact hU.1 n |> IsOpen.measurableSet
    exact MeasureTheory.measure_mono_null ( fun x hx => by aesop ) h_zero_measure
  rw [show {x | ε < integralDensityLimsup μ f s x} =
      ⋃ n, {x | ε < integralDensityLimsup μ f s x} ∩ U n by
    ext x
    replace hU := Set.ext_iff.mp hU.2.2 x
    aesop]
  exact MeasureTheory.measure_iUnion_null fun n => h_zero_measure n

/--
**Theorem 2.10** (Hausdorff measure and integrals over balls).

For `f` locally integrable w.r.t. a uniformly locally doubling Radon measure `μ` on a metric space,
and `s ≥ 0` such that `μ(B(x,r))/r^s → 0` as `r → 0+` for μ-a.e. `x`,
the set `{x : limsup_{r→0+} (∫_{B(x,r)} ‖f‖ dμ) / r^s > 0}` has `H^s`-measure zero.
-/
theorem integralDensitySet_hausdorffMeasure_zero_of_ae_zero_sDensity
    {μ : Measure X} [IsLocallyFiniteMeasure μ] [IsUnifLocDoublingMeasure μ]
    (hμ : IsRadon μ)
    {f : X → ℝ} (hf : LocallyIntegrable f μ)
    {s : ℝ} (hs : 0 ≤ s)
    (hdim : ∀ᵐ x ∂μ,
      Tendsto (fun r => μ (closedBall x r) / ENNReal.ofReal (r ^ s))
        (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    μH[s] (integralDensitySet μ f s) = 0 := by
  have h_zero_hausdorff_measure : ∀ (ε : ℝ≥0∞), 0 < ε →
      μH[s] {x | ε < integralDensityLimsup μ f s x} = 0 := by
    exact fun ε a => hausdorff_measure_integralDensitySetAbove_zero hμ hf hs hdim a
  refine MeasureTheory.measure_mono_null ?_
    (MeasureTheory.measure_iUnion_null fun n : ℕ =>
      h_zero_hausdorff_measure (1 / (n + 1)) (by simp +decide))
  intro x hx
  simp_all +decide only [one_div, mem_iUnion, mem_ofPred_eq]
  rcases ENNReal.exists_inv_nat_lt hx.ne' with ⟨ n, hn ⟩
  exact ⟨ n, lt_of_le_of_lt ( by gcongr ; norm_num ) hn ⟩

end
