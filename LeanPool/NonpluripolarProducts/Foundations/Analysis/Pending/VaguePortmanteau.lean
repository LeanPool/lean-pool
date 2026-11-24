/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Portmanteau inequalities for vague convergence on an open set

Let `Ω` be an open subset of a proper metric space and let `μ_j`, `μ` be positive
Borel measures which are finite on the compact subsets of `Ω` and satisfy
`∫ χ dμ_j → ∫ χ dμ` for every continuous `χ` with compact support in `Ω`
(vague convergence on `Ω`; the measures may have infinite mass near `∂Ω`).

* **Open sets.** For every open `O ⊆ Ω`, `μ O ≤ liminf_j μ_j O`.  Exhaust `O` by an
  increasing sequence of compact sets `K_m`; by Urysohn's lemma there is a continuous
  `0 ≤ φ_m ≤ 1` with compact support in `O` and `φ_m = 1` on `K_m`, whence
  `μ K_m ≤ ∫ φ_m dμ = lim_j ∫ φ_m dμ_j ≤ liminf_j μ_j O`.
* **Upper semicontinuous weights.** For `χ ≥ 0` continuous with compact support in `Ω`
  and `f` upper semicontinuous and bounded on `supp χ`,
  `limsup_j ∫ χ f dμ_j ≤ ∫ χ f dμ`.  The inf-convolutions
  `g_m(x) = sup_{y ∈ supp χ} (f(y) - m·d(x, y))` are continuous, bounded, lie above `f`
  and decrease to `f` on `supp χ`; hence `∫ χ f dμ_j ≤ ∫ χ g_m dμ_j → ∫ χ g_m dμ`, and
  `∫ χ g_m dμ → ∫ χ f dμ` by dominated convergence.

The open-set inequality is first proved in a form involving only lower integrals
of nonnegative tests, which needs no finiteness hypothesis at all.

These are the measure-theoretic inputs of the lower semicontinuity of
non-pluripolar Monge–Ampère measures along increasing sequences (Darvas–Di
Nezza–Lu, Theorem 2.6; Xia, SGPT, Theorem 2.4.2) and of the increasing
Bedford–Taylor convergence theorem (Błocki, *The complex Monge–Ampère operator
in pluripotential theory*, Theorem 2.2.5).
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.VaguePortmanteau

variable {X : Type*} [PseudoMetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]

omit [ProperSpace X] in
/-- A continuous compactly supported function with support in a set on whose
compact subsets the measure is finite is integrable. -/
theorem integrable_of_tsupport_subset {Ω : Set X} {μ : Measure X}
    (hμ : ∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤) {φ : X → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) : Integrable φ μ := by
  obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuous hφ
  rw [← integrableOn_iff_integrable_of_support_subset (subset_tsupport φ)]
  exact Measure.integrableOn_of_bounded (M := M) (hμ _ hφc hφΩ).ne
    hφ.aestronglyMeasurable (Eventually.of_forall hM)

omit [MeasurableSpace X] [BorelSpace X] in
/-- An open set of a proper metric space is the union of an increasing sequence of
compact closed sets. -/
theorem _root_.IsOpen.exists_monotone_isCompact_iUnion_eq {O : Set X} (hO : IsOpen O) :
    ∃ K : ℕ → Set X, (∀ m, IsCompact (K m)) ∧ (∀ m, IsClosed (K m)) ∧ (∀ m, K m ⊆ O) ∧
      Monotone K ∧ ⋃ m, K m = O := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact ⟨fun _ => ∅, fun _ => isCompact_empty, fun _ => isClosed_empty,
      fun _ => empty_subset _, fun _ _ _ => le_rfl, by simp [eq_empty_of_isEmpty O]⟩
  obtain ⟨F, hFc, hFO, hFU, hFmono⟩ := hO.exists_iUnion_isClosed
  refine ⟨fun m => F m ∩ closedBall x₀ m, fun m => ?_, fun m => (hFc m).inter isClosed_closedBall,
    fun m => inter_subset_left.trans (hFO m),
    fun m l hml => inter_subset_inter (hFmono hml)
      (closedBall_subset_closedBall (by exact_mod_cast hml)), ?_⟩
  · exact (isCompact_closedBall x₀ m).inter_left (hFc m)
  · apply Subset.antisymm
    · exact iUnion_subset fun m => inter_subset_left.trans (hFO m)
    · intro z hz
      rw [← hFU] at hz
      obtain ⟨a, ha⟩ := mem_iUnion.mp hz
      obtain ⟨b, hb⟩ := exists_nat_ge (dist z x₀)
      refine mem_iUnion.mpr ⟨max a b, hFmono (le_max_left a b) ha, ?_⟩
      exact mem_closedBall.mpr (hb.trans (by exact_mod_cast le_max_right a b))

/-- **Open-set portmanteau, lower-integral form.** If for every continuous
compactly supported test `0 ≤ φ ≤ 1` with support in the open set `O` the lower
integral against `μ` is at most the lower limit of those against `μ_j`, then
`μ O ≤ liminf μ_j O`.  No finiteness of the measures is needed. -/
theorem measure_le_liminf_of_le_liminf_lintegral {μs : ℕ → Measure X} {μ : Measure X}
    {O : Set X} (hO : IsOpen O)
    (h : ∀ φ : X → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∀ x, φ x ∈ Icc (0 : ℝ) 1) →
      ∫⁻ x, ENNReal.ofReal (φ x) ∂μ ≤
        liminf (fun j => ∫⁻ x, ENNReal.ofReal (φ x) ∂(μs j)) atTop) :
    μ O ≤ liminf (fun j => μs j O) atTop := by
  obtain ⟨K, hKc, hKcl, hKO, hKmono, hKU⟩ := hO.exists_monotone_isCompact_iUnion_eq
  rw [← hKU, hKmono.measure_iUnion, hKU]
  refine iSup_le fun m => ?_
  obtain ⟨f, hf1, hfc, hfO, hf01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen (hKc m) hO (hKO m)
  have hle1 : ∀ ν : Measure X, ∫⁻ x, ENNReal.ofReal (f x) ∂ν ≤ ν O := by
    intro ν
    rw [← lintegral_indicator_one hO.measurableSet]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ O
    · rw [indicator_of_mem hx]
      simpa using (hf01 x).2
    · rw [indicator_of_notMem hx]
      have : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hfO h))
      simp [this]
  have hK : μ (K m) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
    rw [← lintegral_indicator_one (hKcl m).measurableSet]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ K m
    · rw [indicator_of_mem hx, hf1 hx]
      simp
    · rw [indicator_of_notMem hx]
      exact bot_le
  refine hK.trans ((h f f.continuous hfc hfO hf01).trans ?_)
  exact liminf_le_liminf (Eventually.of_forall fun j => hle1 (μs j))

/-- **Open-set portmanteau.** Let the measures be finite on compact subsets of `Ω`
and converge vaguely on `Ω`.  Then `μ O ≤ liminf μ_j O` for every open `O ⊆ Ω`. -/
theorem measure_le_liminf_of_tendsto_integral {μs : ℕ → Measure X} {μ : Measure X}
    {Ω O : Set X} (hO : IsOpen O) (hOΩ : O ⊆ Ω)
    (hμs : ∀ j K, IsCompact K → K ⊆ Ω → μs j K < ⊤)
    (hμ : ∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤)
    (hconv : ∀ φ : X → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      Tendsto (fun j => ∫ x, φ x ∂(μs j)) atTop (𝓝 (∫ x, φ x ∂μ))) :
    μ O ≤ liminf (fun j => μs j O) atTop := by
  refine measure_le_liminf_of_le_liminf_lintegral hO fun φ hφ hφc hφO hφ01 => ?_
  have hφΩ := hφO.trans hOΩ
  have heq : ∀ ν : Measure X, (∀ K, IsCompact K → K ⊆ Ω → ν K < ⊤) →
      ∫⁻ x, ENNReal.ofReal (φ x) ∂ν = ENNReal.ofReal (∫ x, φ x ∂ν) := fun ν hν =>
    (ofReal_integral_eq_lintegral_ofReal (integrable_of_tsupport_subset hν hφ hφc hφΩ)
      (Eventually.of_forall fun x => (hφ01 x).1)).symm
  have ht := (ENNReal.continuous_ofReal.tendsto _).comp (hconv φ hφ hφc hφΩ)
  rw [heq μ hμ]
  simp_rw [heq _ (hμs _)]
  exact ht.liminf_eq.ge

omit [ProperSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- **Lipschitz regularization of an upper semicontinuous function.** A function which
is upper semicontinuous and bounded by `C` on a set `S` is, on `S`, the decreasing
pointwise limit of continuous functions `g_m ≥ f` bounded by `C` on `S`; one takes the
inf-convolutions `g_m(x) = sup_{y ∈ S} (f(y) - m·d(x, y))`. -/
theorem exists_continuous_antitone_tendsto_of_upperSemicontinuousOn {S : Set X}
    {f : X → ℝ} {C : ℝ} (hf : UpperSemicontinuousOn f S) (hfb : ∀ x ∈ S, |f x| ≤ C) :
    ∃ g : ℕ → X → ℝ, (∀ m, Continuous (g m)) ∧ (∀ m, ∀ x ∈ S, f x ≤ g m x) ∧
      (∀ m, ∀ x ∈ S, |g m x| ≤ C) ∧ (∀ x ∈ S, Antitone fun m => g m x) ∧
      (∀ x ∈ S, Tendsto (fun m => g m x) atTop (𝓝 (f x))) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ _ => 0, fun _ => continuous_const, fun _ _ h => h.elim,
      fun _ _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim⟩
  have : Nonempty S := hne.to_subtype
  set g : ℕ → X → ℝ := fun m x => ⨆ y : S, (f y - m * dist x y) with hg
  have hbdd : ∀ (m : ℕ) (x : X), BddAbove (range fun y : S => f y - m * dist x y) := by
    intro m x
    refine ⟨C, ?_⟩
    rintro _ ⟨y, rfl⟩
    have h1 := (abs_le.mp (hfb y y.2)).2
    have h2 : 0 ≤ (m : ℝ) * dist x y := by positivity
    linarith
  have hle : ∀ (m : ℕ) (x : X) (y : S), f y - m * dist x y ≤ g m x := fun m x y =>
    le_ciSup (hbdd m x) y
  have hupper : ∀ m x, g m x ≤ C := fun m x => ciSup_le fun y => by
    have h1 := (abs_le.mp (hfb y y.2)).2
    have h2 : 0 ≤ (m : ℝ) * dist x y := by positivity
    linarith
  have hlow : ∀ m, ∀ x ∈ S, f x ≤ g m x := fun m x hx => by
    simpa using hle m x ⟨x, hx⟩
  refine ⟨g, fun m => ?_, hlow, fun m x hx => abs_le.mpr ⟨?_, hupper m x⟩, fun x _ m l hml => ?_,
    fun x hx => ?_⟩
  · have hlip : LipschitzWith (m : NNReal) (g m) := by
      refine LipschitzWith.of_le_add_mul _ fun x x' => ?_
      refine ciSup_le fun y => ?_
      have htri := dist_triangle x' x y
      have := hle m x' y
      push_cast
      rw [dist_comm x' x] at htri
      nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    exact hlip.continuous
  · linarith [(abs_le.mp (hfb x hx)).1, hlow m x hx]
  · exact ciSup_mono (hbdd m x) fun y => by
      have : (m : ℝ) * dist x y ≤ l * dist x y :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hml) dist_nonneg
      linarith
  · refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun m =>
      lt_of_lt_of_le ha (hlow m x hx), fun b hb => ?_⟩
    obtain ⟨b', hb', hb'b⟩ := exists_between hb
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp (hf x hx b' hb')
    obtain ⟨M, hM⟩ := exists_nat_ge ((C - b') / δ)
    filter_upwards [eventually_ge_atTop M] with m hm
    refine lt_of_le_of_lt (ciSup_le fun y => ?_) hb'b
    by_cases hy : dist (y : X) x < δ
    · have : f y < b' := hball ⟨mem_ball.mpr hy, y.2⟩
      have h2 : 0 ≤ (m : ℝ) * dist x y := by positivity
      linarith
    · have hδy : δ ≤ dist x y := by rw [dist_comm]; exact not_lt.mp hy
      have h1 := (abs_le.mp (hfb y y.2)).2
      have hmM : (C - b') / δ ≤ m := hM.trans (by exact_mod_cast hm)
      have h3 : C - b' ≤ m * δ := by rwa [div_le_iff₀ hδ] at hmM
      have h4 : (m : ℝ) * δ ≤ m * dist x y :=
        mul_le_mul_of_nonneg_left hδy (Nat.cast_nonneg m)
      linarith

omit [ProperSpace X] in
/-- **Upper semicontinuous weights.** Let the measures be finite on compact subsets of
`Ω` and converge vaguely on `Ω`, let `χ ≥ 0` be continuous with compact support in
`Ω`, and let `f` be upper semicontinuous and bounded on the support of `χ`.  Then
`∫ χ f dμ_j ≤ ∫ χ f dμ + ε` for all large `j`, i.e. `limsup_j ∫ χ f dμ_j ≤ ∫ χ f dμ`. -/
theorem eventually_integral_mul_le_of_upperSemicontinuousOn {μs : ℕ → Measure X}
    {μ : Measure X} {Ω : Set X}
    (hμs : ∀ j K, IsCompact K → K ⊆ Ω → μs j K < ⊤)
    (hμ : ∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤)
    (hconv : ∀ φ : X → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      Tendsto (fun j => ∫ x, φ x ∂(μs j)) atTop (𝓝 (∫ x, φ x ∂μ)))
    {χ f : X → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ x, 0 ≤ χ x) (hf : UpperSemicontinuousOn f (tsupport χ)) {C : ℝ}
    (hfb : ∀ x ∈ tsupport χ, |f x| ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∫ x, χ x * f x ∂(μs j) ≤ ∫ x, χ x * f x ∂μ + ε := by
  obtain ⟨g, hgc, hfg, hgb, -, hglim⟩ :=
    exists_continuous_antitone_tendsto_of_upperSemicontinuousOn hf hfb
  have hzero : ∀ x, x ∉ tsupport χ → χ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport hx
  have hptlim : ∀ x, Tendsto (fun m => χ x * g m x) atTop (𝓝 (χ x * f x)) := by
    intro x
    by_cases hx : x ∈ tsupport χ
    · exact (hglim x hx).const_mul _
    · simp [hzero x hx]
  obtain ⟨M, hM⟩ := hχc.exists_bound_of_continuous hχ
  have hbound : ∀ (h : X → ℝ), (∀ x ∈ tsupport χ, |h x| ≤ C) → ∀ x, ‖χ x * h x‖ ≤ C * |χ x| := by
    intro h hh x
    by_cases hx : x ∈ tsupport χ
    · rw [Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hh x hx) (abs_nonneg _)
    · simp [hzero x hx]
  have hmeas : ∀ ν : Measure X, AEStronglyMeasurable (fun x => χ x * f x) ν := fun ν =>
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun m => (hχ.mul (hgc m)).aestronglyMeasurable) (Eventually.of_forall hptlim)
  have hint : ∀ ν : Measure X, (∀ K, IsCompact K → K ⊆ Ω → ν K < ⊤) → ∀ h : X → ℝ,
      AEStronglyMeasurable (fun x => χ x * h x) ν → (∀ x ∈ tsupport χ, |h x| ≤ C) →
      Integrable (fun x => χ x * h x) ν := by
    intro ν hν h hhm hh
    have hχi : Integrable (fun x => C * |χ x|) ν :=
      (integrable_of_tsupport_subset hν hχ hχc hχΩ).abs.const_mul C
    exact hχi.mono' hhm (Eventually.of_forall (hbound h hh))
  have hlimμ : Tendsto (fun m => ∫ x, χ x * g m x ∂μ) atTop (𝓝 (∫ x, χ x * f x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => C * |χ x|)
      (fun m => (hχ.mul (hgc m)).aestronglyMeasurable)
      ((integrable_of_tsupport_subset hμ hχ hχc hχΩ).abs.const_mul C)
      (fun m => Eventually.of_forall (hbound _ (hgb m)))
      (Eventually.of_forall hptlim)
  obtain ⟨m, hm⟩ := ((tendsto_order.1 hlimμ).2 (∫ x, χ x * f x ∂μ + ε / 2)
    (by linarith)).exists
  have hsupp : tsupport (fun x => χ x * g m x) ⊆ Ω := (tsupport_mul_subset_left).trans hχΩ
  have hcj := hconv (fun x => χ x * g m x) (hχ.mul (hgc m)) hχc.mul_right hsupp
  filter_upwards [(tendsto_order.1 hcj).2 (∫ x, χ x * g m x ∂μ + ε / 2) (by linarith)]
    with j hj
  have hmono : ∫ x, χ x * f x ∂(μs j) ≤ ∫ x, χ x * g m x ∂(μs j) := by
    refine integral_mono (hint _ (hμs j) f (hmeas _) hfb)
      (hint _ (hμs j) (g m) (hχ.mul (hgc m)).aestronglyMeasurable (hgb m)) fun x => ?_
    by_cases hx : x ∈ tsupport χ
    · exact mul_le_mul_of_nonneg_left (hfg m x hx) (hχ0 x)
    · simp [hzero x hx]
  linarith

end SGPT.Foundations.Analysis.Pending.VaguePortmanteau
