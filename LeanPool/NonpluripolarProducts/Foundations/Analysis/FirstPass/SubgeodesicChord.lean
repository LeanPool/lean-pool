/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ERealChordUSC
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PshRealConvexity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PotentialL1AESubsequence

/-!
# The endpoint chord bound for strip subgeodesics

This file supplies the analytic assembly behind the pointwise endpoint chord
bound.  It first records the two affine restrictions of the strip PSH
function, together with local measurability and almost-everywhere finiteness
interfaces that do not depend on any `Pending` pole-set theorem.
-/

@[expose] public section

open Filter MeasureTheory Set Metric TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

/-- A relatively upper-semicontinuous `EReal`-valued function on an open set
is almost-everywhere measurable for the measure restricted to that set. -/
theorem UpperSemicontinuousOn.aemeasurable_restrict_of_isOpen
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} {f : X → EReal} {U : Set X}
    (hf : UpperSemicontinuousOn f U) (hU : IsOpen U) :
    AEMeasurable f (μ.restrict U) := by
  classical
  let g : X → EReal := fun x => if x ∈ U then f x else ⊤
  have hg : UpperSemicontinuous g := by
    intro x c hxc
    by_cases hx : x ∈ U
    · have hfc : f x < c := by simpa [g, hx] using hxc
      have hlocal := hf x hx c hfc
      rw [hU.nhdsWithin_eq hx] at hlocal
      filter_upwards [hlocal, hU.mem_nhds hx] with y hy hyU
      simpa [g, hyU] using hy
    · simp [g, hx] at hxc
  apply hg.measurable.aemeasurable.congr
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  simp [g, hx]

/-- Local nondegeneracy on the manifold produces a non-pole point in every
nonempty open subset of a chart target. -/
theorem LocallyNondegenerate.exists_chart_ne_bot
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M]
    {u : M → EReal} (hu : LocallyNondegenerate u)
    (e : ComplexChart n M) {O : Set (ComplexModel n)}
    (hO : IsOpen O) (hOe : O ⊆ e.val.target) {z : ComplexModel n}
    (hz : z ∈ O) :
    ∃ y ∈ O, chartFunction u e y ≠ ⊥ := by
  let V : Set M := e.val.source ∩ e.val ⁻¹' O
  have hV : IsOpen V := e.val.isOpen_inter_preimage hO
  have hz_target : z ∈ e.val.target := hOe hz
  have hzV : e.val.symm z ∈ V := by
    refine ⟨e.val.symm.map_source hz_target, ?_⟩
    change e.val (e.val.symm z) ∈ O
    rw [e.val.right_inv hz_target]
    exact hz
  obtain ⟨y, hyV, hy⟩ := hu (e.val.symm z) V hV hzV
  refine ⟨e.val y, hyV.2, ?_⟩
  simpa [chartFunction, e.val.left_inv hyV.1] using hy

/-- If a chart representative becomes PSH after adding a finite smooth
correction, local nondegeneracy implies that the raw representative is finite
almost everywhere on every preconnected compact set containing a nonempty
open subset. -/
theorem ae_finite_chartFunction_of_psh_add
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M]
    {u : M → EReal} (hu : LocallyNondegenerate u)
    (e : ComplexChart n M) {W K O : Set (ComplexModel n)}
    {ρ : ComplexModel n → ℝ}
    (hpsh : PlurisubharmonicOn
      (fun y => chartFunction u e y + (ρ y : EReal)) W)
    (hKW : K ⊆ W) (hK : IsPreconnected K)
    (hO : IsOpen O) (hOK : O ⊆ K) (hOe : O ⊆ e.val.target)
    {z : ComplexModel n} (hz : z ∈ O) :
    ∀ᵐ y ∂volume.restrict K,
      chartFunction u e y ≠ ⊤ ∧ chartFunction u e y ≠ ⊥ := by
  obtain ⟨y, hyO, hybot⟩ := hu.exists_chart_ne_bot e hO hOe hz
  have hcorrbot : chartFunction u e y + (ρ y : EReal) ≠ ⊥ := by
    rw [EReal.add_ne_bot_iff]
    exact ⟨hybot, EReal.coe_ne_bot _⟩
  have hfinite := (hpsh.mono hKW).ae_finite volume hK
    ⟨y, hOK hyO, hcorrbot⟩
  filter_upwards [hfinite] with q hq
  constructor
  · exact (EReal.add_ne_top_iff_ne_top_left
      (EReal.coe_ne_bot (ρ q)) (EReal.coe_ne_top (ρ q))).mp hq.1
  · exact (EReal.add_ne_bot_iff.mp hq.2).1

/-- A genuine global quasi-PSH potential is finite almost everywhere in every
chart target.  This local proof uses only its PSH germ decomposition and local
nondegeneracy; no global pluripolar-set theorem is required. -/
theorem IsGlobalQuasiPshPotential.ae_finite_chart
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M]
    {u : M → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u)
    (e : ComplexChart n M) :
    ∀ᵐ y ∂volume.restrict e.val.target,
      chartFunction u e y ≠ ⊤ ∧ chartFunction u e y ≠ ⊥ := by
  apply ae_restrict_of_open_neighborhood_ae
  intro z hz
  obtain ⟨p, h, hp, _, heq⟩ := hu.1 e z hz
  obtain ⟨D, hD, hzD, hdisc⟩ := hp
  have hnbhd : {y | y ∈ D ∧ y ∈ e.val.target ∧
      chartFunction u e y = p y + (h y : EReal)} ∈ 𝓝 z := by
    filter_upwards [hD.mem_nhds hzD, e.val.open_target.mem_nhds hz, heq]
      with y hyD hye hyEq
    exact ⟨hyD, hye, hyEq⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnbhd
  let W : Set (ComplexModel n) := ball z ε
  let K : Set (ComplexModel n) := closedBall z (ε / 2)
  have hKW : K ⊆ W := by
    exact closedBall_subset_ball (half_lt_self hε)
  have hWD : W ⊆ D := fun y hy => (hεsub hy).1
  have hWe : W ⊆ e.val.target := fun y hy => (hεsub hy).2.1
  have hcorr : EqOn (fun y => chartFunction u e y + ((-h y : ℝ) : EReal)) p W := by
    intro y hy
    change chartFunction u e y + ((-h y : ℝ) : EReal) = p y
    rw [(hεsub hy).2.2, add_assoc, ← EReal.coe_add]
    simp
  have hcorr_psh : PlurisubharmonicOn
      (fun y => chartFunction u e y + ((-h y : ℝ) : EReal)) W :=
    ((hdisc.mono hWD).congr fun y hy => (hcorr hy).symm).plurisubharmonicOn
      isOpen_ball
  have hfiniteK : ∀ᵐ y ∂volume.restrict K,
      chartFunction u e y ≠ ⊤ ∧ chartFunction u e y ≠ ⊥ :=
    ae_finite_chartFunction_of_psh_add hu.2 e hcorr_psh hKW
      (convex_closedBall z (ε / 2)).isPreconnected isOpen_ball ball_subset_closedBall
      (fun y hy => hWe (hKW (ball_subset_closedBall hy)))
      (show z ∈ ball z (ε / 2) by simpa using half_pos hε)
  refine ⟨ball z (ε / 2), isOpen_ball,
    (show z ∈ ball z (ε / 2) by simpa using half_pos hε), ?_⟩
  exact ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hfiniteK

/-- Chart representatives of global quasi-PSH potentials are measurable for
volume restricted to any subset of the chart target. -/
theorem IsGlobalQuasiPshPotential.aemeasurable_chart_restrict
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M]
    {u : M → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u)
    (e : ComplexChart n M) {K : Set (ComplexModel n)}
    (hK : K ⊆ e.val.target) :
    AEMeasurable (chartFunction u e) (volume.restrict K) :=
  AEMeasurable.mono_set hK
    (UpperSemicontinuousOn.aemeasurable_restrict_of_isOpen
      (hu.1 e).upperSemicontinuousOn e.val.open_target)

/-- Choose paired interior times approaching the left and right endpoints,
with the fixed middle time strictly between every pair. -/
theorem exists_paired_endpoint_sequences {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ a b : ℕ → ℝ,
      (∀ k, a k ∈ Ioo (0 : ℝ) t) ∧
      (∀ k, b k ∈ Ioo t 1) ∧
      Tendsto a atTop (𝓝[>] (0 : ℝ)) ∧
      Tendsto b atTop (𝓝[<] (1 : ℝ)) := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, Tendsto a atTop (𝓝[>] (0 : ℝ)) :=
    exists_seq_tendsto (𝓝[>] (0 : ℝ))
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝[<] (1 : ℝ)) :=
    exists_seq_tendsto (𝓝[<] (1 : ℝ))
  have hgood : ∀ᶠ k : ℕ in atTop,
      a k ∈ Ioo (0 : ℝ) t ∧ b k ∈ Ioo t 1 :=
    (ha.eventually (Ioo_mem_nhdsGT ht.1)).and
      (hb.eventually (Ioo_mem_nhdsLT ht.2))
  rw [eventually_atTop] at hgood
  obtain ⟨N, hN⟩ := hgood
  refine ⟨fun k => a (k + N), fun k => b (k + N), ?_, ?_,
    ha.comp (tendsto_add_atTop_nat N), hb.comp (tendsto_add_atTop_nat N)⟩
  · intro k
    exact (hN (k + N) (by omega)).1
  · intro k
    exact (hN (k + N) (by omega)).2

/-- The affine chords through moving endpoints converge to the normalized
chord through the limiting endpoint values. -/
theorem tendsto_affineChord_of_endpoint_limits
    {a b A B : ℕ → ℝ} {A₀ B₁ t : ℝ}
    (ha : Tendsto a atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 1))
    (hA : Tendsto A atTop (𝓝 A₀)) (hB : Tendsto B atTop (𝓝 B₁)) :
    Tendsto
      (fun k => A k + (t - a k) * (B k - A k) / (b k - a k))
      atTop (𝓝 ((1 - t) * A₀ + t * B₁)) := by
  have hden : Tendsto (fun k => b k - a k) atTop (𝓝 (1 - 0)) := hb.sub ha
  have hslope : Tendsto (fun k => (B k - A k) / (b k - a k))
      atTop (𝓝 ((B₁ - A₀) / (1 - 0))) :=
    (hB.sub hA).div hden (by norm_num)
  have htlim : Tendsto (fun _ : ℕ => t) atTop (𝓝 t) := tendsto_const_nhds
  have hlim := hA.add ((htlim.sub ha).mul hslope)
  convert hlim using 1
  · funext k
    ring
  · ring_nf

/-- Inequalities below every moving affine chord pass to the limiting
normalized chord. -/
theorem le_normalizedChord_of_le_affineChords
    {a b A B : ℕ → ℝ} {A₀ B₁ t c : ℝ}
    (ha : Tendsto a atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 1))
    (hA : Tendsto A atTop (𝓝 A₀)) (hB : Tendsto B atTop (𝓝 B₁))
    (hle : ∀ k, c ≤ A k + (t - a k) * (B k - A k) / (b k - a k)) :
    c ≤ (1 - t) * A₀ + t * B₁ :=
  ge_of_tendsto (tendsto_affineChord_of_endpoint_limits ha hb hA hB)
    (Eventually.of_forall hle)

/-- A PSH function of one complex variable that only depends on the real
coordinate lies below the endpoint chord when finite interior samples tend
to two finite endpoint values. -/
theorem PlurisubharmonicOn.le_eRealChord_of_endpoint_sequences
    {v : ℝ → EReal} {a b : ℕ → ℝ} {u₀ u₁ : EReal} {t : ℝ}
    (hv : PlurisubharmonicOn (fun τ : ℂ => v τ.re)
      (Complex.re ⁻¹' Ioo (0 : ℝ) 1))
    (_ht : t ∈ Ioo (0 : ℝ) 1)
    (ha_mem : ∀ k, a k ∈ Ioo (0 : ℝ) t)
    (hb_mem : ∀ k, b k ∈ Ioo t 1)
    (ha : Tendsto a atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 1))
    (hva : Tendsto (fun k => v (a k)) atTop (𝓝 u₀))
    (hvb : Tendsto (fun k => v (b k)) atTop (𝓝 u₁))
    (hfinite_a : ∀ k, v (a k) ≠ ⊤ ∧ v (a k) ≠ ⊥)
    (hfinite_t : v t ≠ ⊤ ∧ v t ≠ ⊥)
    (hfinite_b : ∀ k, v (b k) ≠ ⊤ ∧ v (b k) ≠ ⊥)
    (hfinite₀ : u₀ ≠ ⊤ ∧ u₀ ≠ ⊥)
    (hfinite₁ : u₁ ≠ ⊤ ∧ u₁ ≠ ⊥) :
    v t ≤ eRealChord u₀ u₁ t := by
  have hA : Tendsto (fun k => (v (a k)).toReal) atTop (𝓝 u₀.toReal) :=
    (EReal.tendsto_toReal hfinite₀.1 hfinite₀.2).comp hva
  have hB : Tendsto (fun k => (v (b k)).toReal) atTop (𝓝 u₁.toReal) :=
    (EReal.tendsto_toReal hfinite₁.1 hfinite₁.2).comp hvb
  have hreal : (v t).toReal ≤
      (1 - t) * u₀.toReal + t * u₁.toReal :=
    le_normalizedChord_of_le_affineChords ha hb hA hB fun k =>
      hv.comp_re_toReal_le_affine_chord (ha_mem k).2 (hb_mem k).1
        (fun y hy => ⟨(ha_mem k).1.trans_le hy.1, hy.2.trans_lt (hb_mem k).2⟩)
        (hfinite_a k).1 (hfinite_a k).2 hfinite_t.1 hfinite_t.2
        (hfinite_b k).1 (hfinite_b k).2
  calc
    v t = ((v t).toReal : EReal) :=
      (EReal.coe_toReal hfinite_t.1 hfinite_t.2).symm
    _ ≤ (((1 - t) * u₀.toReal + t * u₁.toReal : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.mpr hreal
    _ = eRealChord u₀ u₁ t := by
      rw [eRealChord, ← EReal.coe_toReal hfinite₀.1 hfinite₀.2,
        ← EReal.coe_toReal hfinite₁.1 hfinite₁.2]
      norm_cast

/-- Adding the same finite constant to both finite endpoints translates their
extended-real chord by that constant. -/
theorem eRealChord_add_coe_right {a b : EReal} (r t : ℝ)
    (ha : a ≠ ⊤ ∧ a ≠ ⊥) (hb : b ≠ ⊤ ∧ b ≠ ⊥) :
    eRealChord (a + (r : EReal)) (b + (r : EReal)) t =
      eRealChord a b t + (r : EReal) := by
  rw [← EReal.coe_toReal ha.1 ha.2, ← EReal.coe_toReal hb.1 hb.2]
  norm_cast
  simp only [eRealChord]
  norm_cast
  ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- Restrict the strip PSH function to a horizontal complex-affine spatial
slice. -/
theorem PlurisubharmonicOn.subgeodesic_spatial_slice
    {curve : ℝ → M → EReal} {e : ComplexChart n M}
    {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hpsh : PlurisubharmonicOn (subgeodesicChartFunction curve e ρ)
      (geodesicChartDomain W))
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    PlurisubharmonicOn
      (fun z => chartFunction (curve s) e z + (ρ z : EReal)) W := by
  let L : ComplexModel n →L[ℂ] ComplexModel n × ℂ :=
    ContinuousLinearMap.inl ℂ (ComplexModel n) ℂ
  let a : ComplexModel n × ℂ := (0, (s : ℂ))
  have hpull := hpsh.comp_affine L a
  have hmono : W ⊆ (fun z => a + L z) ⁻¹' geodesicChartDomain W := by
    intro z hz
    change a + L z ∈ geodesicChartDomain W
    simpa [a, L] using ⟨hz, hs.1, hs.2⟩
  simpa [a, L] using hpull.mono hmono

omit [IsComplexManifold n M] in
/-- Restrict the strip PSH function to the complex-time line over one fixed
chart point. -/
theorem PlurisubharmonicOn.subgeodesic_time_line
    {curve : ℝ → M → EReal} {e : ComplexChart n M}
    {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hpsh : PlurisubharmonicOn (subgeodesicChartFunction curve e ρ)
      (geodesicChartDomain W))
    {z : ComplexModel n} (hz : z ∈ W) :
    PlurisubharmonicOn
      (fun τ : ℂ => chartFunction (curve τ.re) e z + (ρ z : EReal))
      complexTimeStrip := by
  let L : ℂ →L[ℂ] ComplexModel n × ℂ :=
    ContinuousLinearMap.inr ℂ (ComplexModel n) ℂ
  let a : ComplexModel n × ℂ := (z, 0)
  have hpull := hpsh.comp_affine L a
  have hmono : complexTimeStrip ⊆
      (fun τ => a + L τ) ⁻¹' geodesicChartDomain W := by
    intro τ hτ
    change a + L τ ∈ geodesicChartDomain W
    simpa [a, L] using ⟨hz, hτ⟩
  simpa [a, L] using hpull.mono hmono

namespace IsSubgeodesicFrom

variable {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
  {u₀ u₁ : M → EReal}

/-- Every interior slice of a strip subgeodesic lies below the extended-real
chord joining its prescribed `L¹` endpoint values. -/
theorem le_eRealChord
    (h : IsSubgeodesicFrom θ curve u₀ u₁)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : M) :
    curve t x ≤ eRealChord (u₀ x) (u₁ x) t := by
  let e : ComplexChart n M := complexChartAt (n := n) x
  let z : ComplexModel n := e.val x
  have hxsource : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : z ∈ e.val.target := e.val.map_source hxsource
  obtain ⟨W, ρ, hzW, hρ, hstrip⟩ := h.interior.complexified_psh e hz
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hρ.1 z hzW
  let O : Set (ComplexModel n) := ball z (ε / 2)
  let K : Set (ComplexModel n) := closedBall z (ε / 2)
  have hKW : K ⊆ W :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεW
  have hOW : O ⊆ W := ball_subset_closedBall.trans hKW
  have hKtarget : K ⊆ e.val.target := hKW.trans hρ.2.1
  have hOtarget : O ⊆ e.val.target := hOW.trans hρ.2.1
  have hzO : z ∈ O := by
    simpa [O] using half_pos hε
  obtain ⟨a, b, ha_mem, hb_mem, ha, hb⟩ :=
    exists_paired_endpoint_sequences ht
  have ha_int (k : ℕ) : a k ∈ Ioo (0 : ℝ) 1 :=
    ⟨(ha_mem k).1, (ha_mem k).2.trans ht.2⟩
  have hb_int (k : ℕ) : b k ∈ Ioo (0 : ℝ) 1 :=
    ⟨ht.1.trans (hb_mem k).1, (hb_mem k).2⟩
  have hL₀ : Tendsto
      (fun k => chartL1EDistance (curve (a k)) u₀ e K)
      atTop (𝓝 0) :=
    (h.tendsto_left e K (by simpa [K] using isCompact_closedBall z (ε / 2))
      hKtarget).comp ha
  have hL₁ : Tendsto
      (fun k => chartL1EDistance (curve (b k)) u₁ e K)
      atTop (𝓝 0) :=
    (h.tendsto_right e K (by simpa [K] using isCompact_closedBall z (ε / 2))
      hKtarget).comp hb
  have hfiniteK (v : M → EReal)
      (hv : IsGlobalQuasiPshPotential (n := n) v) :
      ∀ᵐ q ∂volume.restrict K,
        chartFunction v e q ≠ ⊤ ∧ chartFunction v e q ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hKtarget (hv.ae_finite_chart e)
  obtain ⟨ns, hns, hconv⟩ :=
    chartL1EDistance_exists_common_strictMono_tendsto_ae_eReal e K
      (fun k => (h.interior.thetaPshPotential (ha_int k)).quasiPshPotential
        |>.aemeasurable_chart_restrict e hKtarget)
      (h.left_endpoint.quasiPshPotential.aemeasurable_chart_restrict e hKtarget)
      (fun k => (h.interior.thetaPshPotential (hb_int k)).quasiPshPotential
        |>.aemeasurable_chart_restrict e hKtarget)
      (h.right_endpoint.quasiPshPotential.aemeasurable_chart_restrict e hKtarget)
      (fun k => hfiniteK (curve (a k))
        (h.interior.thetaPshPotential (ha_int k)).quasiPshPotential)
      (hfiniteK u₀ h.left_endpoint.quasiPshPotential)
      (fun k => hfiniteK (curve (b k))
        (h.interior.thetaPshPotential (hb_int k)).quasiPshPotential)
      (hfiniteK u₁ h.right_endpoint.quasiPshPotential) hL₀ hL₁
  have hfinite_a : ∀ᵐ q ∂volume.restrict K, ∀ k,
      chartFunction (curve (a (ns k))) e q ≠ ⊤ ∧
        chartFunction (curve (a (ns k))) e q ≠ ⊥ :=
    ae_all_iff.mpr fun k => hfiniteK (curve (a (ns k)))
      (h.interior.thetaPshPotential (ha_int (ns k))).quasiPshPotential
  have hfinite_b : ∀ᵐ q ∂volume.restrict K, ∀ k,
      chartFunction (curve (b (ns k))) e q ≠ ⊤ ∧
        chartFunction (curve (b (ns k))) e q ≠ ⊥ :=
    ae_all_iff.mpr fun k => hfiniteK (curve (b (ns k)))
      (h.interior.thetaPshPotential (hb_int (ns k))).quasiPshPotential
  have hfinite_t := hfiniteK (curve t)
    (h.interior.thetaPshPotential ht).quasiPshPotential
  have hfinite₀ := hfiniteK u₀ h.left_endpoint.quasiPshPotential
  have hfinite₁ := hfiniteK u₁ h.right_endpoint.quasiPshPotential
  have ha0 : Tendsto (fun k => a (ns k)) atTop (𝓝 0) :=
    (ha.comp hns.tendsto_atTop).mono_right inf_le_left
  have hb1 : Tendsto (fun k => b (ns k)) atTop (𝓝 1) :=
    (hb.comp hns.tendsto_atTop).mono_right inf_le_left
  have haeK : ∀ᵐ q ∂volume.restrict K,
      chartFunction (curve t) e q + (ρ q : EReal) ≤
        eRealChord (chartFunction u₀ e q) (chartFunction u₁ e q) t +
          (ρ q : EReal) := by
    filter_upwards [ae_restrict_mem (isClosed_closedBall.measurableSet), hconv,
      hfinite_a, hfinite_t, hfinite_b, hfinite₀, hfinite₁]
      with q hqK hqconv hqfina hqfint hqfinb hqfin₀ hqfin₁
    have hcorrFinite {c : EReal} (hc : c ≠ ⊤ ∧ c ≠ ⊥) :
        c + (ρ q : EReal) ≠ ⊤ ∧ c + (ρ q : EReal) ≠ ⊥ := by
      constructor
      · exact (EReal.add_ne_top_iff_ne_top_left
          (EReal.coe_ne_bot (ρ q)) (EReal.coe_ne_top (ρ q))).mpr hc.1
      · rw [EReal.add_ne_bot_iff]
        exact ⟨hc.2, EReal.coe_ne_bot (ρ q)⟩
    have hconv₀ : Tendsto
        (fun k => chartFunction (curve (a (ns k))) e q + (ρ q : EReal))
        atTop (𝓝 (chartFunction u₀ e q + (ρ q : EReal))) := by
      exact (EReal.continuousAt_add (Or.inl hqfin₀.1)
          (Or.inr (EReal.coe_ne_top (ρ q)))).tendsto.comp
        (hqconv.1.prodMk_nhds tendsto_const_nhds)
    have hconv₁ : Tendsto
        (fun k => chartFunction (curve (b (ns k))) e q + (ρ q : EReal))
        atTop (𝓝 (chartFunction u₁ e q + (ρ q : EReal))) := by
      exact (EReal.continuousAt_add (Or.inl hqfin₁.1)
          (Or.inr (EReal.coe_ne_top (ρ q)))).tendsto.comp
        (hqconv.2.prodMk_nhds tendsto_const_nhds)
    have htime := PlurisubharmonicOn.subgeodesic_time_line hstrip (hKW hqK)
    change PlurisubharmonicOn
      (fun τ : ℂ => chartFunction (curve τ.re) e q + (ρ q : EReal))
      (Complex.re ⁻¹' Ioo (0 : ℝ) 1) at htime
    have hcorrected :=
      PlurisubharmonicOn.le_eRealChord_of_endpoint_sequences
      (v := fun s => chartFunction (curve s) e q + (ρ q : EReal))
      (a := fun k => a (ns k)) (b := fun k => b (ns k))
      (u₀ := chartFunction u₀ e q + (ρ q : EReal))
      (u₁ := chartFunction u₁ e q + (ρ q : EReal)) htime ht
      (fun k => ha_mem (ns k)) (fun k => hb_mem (ns k)) ha0 hb1
      hconv₀ hconv₁ (fun k => hcorrFinite (hqfina k))
      (hcorrFinite hqfint) (fun k => hcorrFinite (hqfinb k))
      (hcorrFinite hqfin₀) (hcorrFinite hqfin₁)
    rw [eRealChord_add_coe_right (ρ q) t hqfin₀ hqfin₁] at hcorrected
    exact hcorrected
  have haeO : ∀ᵐ q ∂volume.restrict O,
      chartFunction (curve t) e q + (ρ q : EReal) ≤
        eRealChord (chartFunction u₀ e q) (chartFunction u₁ e q) t +
          (ρ q : EReal) :=
    ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall haeK
  have hcenter : PlurisubharmonicOn
      (fun q => chartFunction (curve t) e q + (ρ q : EReal)) O :=
    (PlurisubharmonicOn.subgeodesic_spatial_slice hstrip ht).mono hOW
  have hρusc : UpperSemicontinuousOn (fun q => (ρ q : EReal)) O := by
    intro q hq
    exact (continuous_coe_real_ereal.continuousAt.comp
      ((hρ.2.2.1 q (hOW hq)).contDiffAt (hρ.1.mem_nhds (hOW hq))).continuousAt)
      |>.upperSemicontinuousAt.upperSemicontinuousWithinAt O
  have hchordusc := (h.upperSemicontinuousOn_chart_eRealChord e ht.1.le ht.2.le).mono
    hOtarget
  have htarget : UpperSemicontinuousOn
      (fun q => eRealChord (chartFunction u₀ e q) (chartFunction u₁ e q) t +
        (ρ q : EReal)) O :=
    upperSemicontinuousOn_eReal_add hchordusc hρusc
      (fun q hq => by
        change (((1 - t : ℝ) : EReal) * chartFunction u₀ e q +
          (t : EReal) * chartFunction u₁ e q) ≠ ⊤
        exact EReal.add_ne_top
          (eReal_const_mul_ne_top (sub_nonneg.mpr ht.2.le)
            ((h.left_endpoint.1.quasiPlurisubharmonic e q (hOtarget hq)).ne_top))
          (eReal_const_mul_ne_top ht.1.le
            ((h.right_endpoint.1.quasiPlurisubharmonic e q (hOtarget hq)).ne_top)))
      (fun q _ => EReal.coe_ne_top (ρ q))
  have hzle := hcenter.le_of_ae_le isOpen_ball htarget volume haeO z hzO
  have hzraw : chartFunction (curve t) e z ≤
      eRealChord (chartFunction u₀ e z) (chartFunction u₁ e z) t :=
    (EReal.addLECancellable_coe (ρ z)).add_le_add_iff_right.mp hzle
  simpa [e, z, chartFunction, e.val.left_inv hxsource] using hzraw

end IsSubgeodesicFrom

end

end SGPT.Foundations.Analysis.FirstPass
