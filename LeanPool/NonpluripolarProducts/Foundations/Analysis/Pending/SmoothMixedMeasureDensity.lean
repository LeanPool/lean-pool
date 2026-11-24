/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.TopDegreeDensity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ProductTestForms
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.FullSpacePatchMeasure
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SmoothDDCHessianPositivity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalPotentials

/-!
# The global mixed measure of smooth semipositive forms has the smooth density

Let `θ₁, …, θₙ` be smooth closed semipositive real `(1,1)`-forms on a compact complex manifold
`M` of dimension `n` (equivalently, `0` is `θᵢ`-psh,
    `LocalPotentials.thetaPlurisubharmonic_zero_iff`).
Their global mixed non-pluripolar measure with the potentials `0`,
`GlobalNonPluripolar.globalMixedMeasure θ 0`, is the smooth measure `θ₁ ∧ ⋯ ∧ θₙ`: in every
chart `e`, for every measurable set `S` of the chart target,

`globalMixedMeasure θ 0 (e⁻¹ S) = ∫_S D(z) dλ(z)`,  `D(z) = actualMixedTopDensity (θᵢ(z))ᵢ`,

the density of the genuine exterior product of the coefficients in the standard orientation
(`globalMixedMeasure_image_eq_lintegral`).  By `MixedCoordinateDensity` this density is
`Re C(H₁, …, Hₙ) / πⁿ` with `Hᵢ` the normalized Hermitian matrices of the `θᵢ`, the matrix form
in which `ConcentrationEigenvalueBound` (TN.4, step B3) is stated.

*Proof.*  Near a point of the target each `θᵢ` has a smooth local potential `ρᵢ` (`ddᶜρᵢ = θᵢ`)
which is psh; the patch whose corrections are the `ρᵢ` identifies the global measure on
inverse images of a small ball with the smooth mixed Monge--Ampère measure of `(ρᵢ)`
(`FullSpacePatchMeasure.globalMixedMeasure_coordinate_inverse_image_eq_smoothMixedMeasure`), whose
density is `D` (`actualMixedTopDensity_smoothDDC`).  An arbitrary measurable piece is a disjoint
countable union of pieces inside such balls (second countability).

The map form `restrict_image_eq_map` and the change of variables
`setLIntegral_image_eq` follow; they are the interface used by the smooth currents
`[M] ∧ γ₁ ∧ ⋯ ∧ γ_p` of `Pending.SmoothCurrentTraceMeasure` and by the measure lower bound of
TN.4 step B3 (agreed on I-0831).

## Main results

* `isSemipositiveOneOne_coeff` — pointwise semipositivity of a form with psh potential `0`.
* `exists_ball_globalMixedMeasure_image_eq` — the identity on subsets of a small ball.
* `globalMixedMeasure_image_eq_lintegral` — the identity on every measurable subset of a chart.
* `restrict_image_eq_map`, `setLIntegral_image_eq` — the map form and the change of variables.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped ENNReal Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.SmoothMixedMeasureDensity

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
  FirstPass.GlobalPotentialPatches FirstPass.MixedNonPluripolar
open GlobalNonPluripolar StronglyPositiveForms TopDegreeDensity

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A closed form with psh potential `0` is pointwise a semipositive real `(1,1)`-form. -/
theorem isSemipositiveOneOne_coeff {θ : ClosedRealOneOneForm n M}
    (hθ : ThetaPlurisubharmonic θ.val (fun _ => 0)) {e : ComplexChart n M} {z : ComplexModel n}
    (hz : z ∈ e.val.target) : IsSemipositiveOneOne (θ.val.coeff e z) :=
  ⟨θ.2.2 e z hz, (LocalPotentials.thetaPlurisubharmonic_zero_iff θ).mp hθ e z hz⟩

/-- The density of the mixed product of the coefficients of a family of forms in a chart. -/
def chartDensity (θ : Fin n → ClosedRealOneOneForm n M) (e : ComplexChart n M)
    (z : ComplexModel n) : ℝ≥0∞ :=
  ENNReal.ofReal (actualMixedTopDensity fun i => (θ i).val.coeff e z)

/-- Products of two-forms depend continuously on the factors. -/
theorem continuous_wedgeProd :
    ∀ q : ℕ, Continuous (fun A : Fin q → RealForm n 2 => wedgeProd q A)
  | 0 => continuous_const
  | q + 1 => by
    have h1 : Continuous (fun A : Fin (q + 1) → RealForm n 2 => wedgeProd q fun i => A i.castSucc)
      :=
      (continuous_wedgeProd q).comp (continuous_pi fun i => continuous_apply _)
    have h2 : Continuous (fun A : Fin (q + 1) → RealForm n 2 => A (Fin.last q)) :=
      continuous_apply _
    have h3 : Continuous (fun A : Fin (q + 1) → RealForm n 2 =>
        ProductTestForms.wedgeCLM n (2 * q) (wedgeProd q fun i => A i.castSucc) (A (Fin.last q)))
          :=
      ((ProductTestForms.wedgeCLM n (2 * q)).continuous.comp h1).clm_apply h2
    refine h3.congr fun A => ?_
    rw [ProductTestForms.wedgeCLM_apply, wedgeProd_succ]

/-- The mixed top density depends continuously on the forms. -/
theorem continuous_actualMixedTopDensity :
    Continuous (fun A : Fin n → RealForm n 2 => actualMixedTopDensity A) := by
  have h : (fun A : Fin n → RealForm n 2 => actualMixedTopDensity A) =
      fun A => topDensity (wedgeProd n A) := funext fun A => (topDensity_wedgeProd A).symm
  rw [h]
  exact continuous_topDensity.comp (continuous_wedgeProd n)

theorem continuousOn_chartDensity (θ : Fin n → ClosedRealOneOneForm n M) (e : ComplexChart n M) :
    ContinuousOn (chartDensity θ e) e.val.target := by
  have hcoeff : ContinuousOn (fun z => fun i => (θ i).val.coeff e z) e.val.target :=
    continuousOn_pi.mpr fun i => ((θ i).val.smooth e).continuousOn
  exact ENNReal.continuous_ofReal.comp_continuousOn
    (continuous_actualMixedTopDensity.comp_continuousOn hcoeff)

/-- A map continuous on a measurable set pulls measurable sets back to measurable sets inside
it. -/
theorem measurableSet_inter_preimage_of_continuousOn {α β : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [TopologicalSpace β] [MeasurableSpace β]
    [BorelSpace β] {f : α → β} {s : Set α} (hs : MeasurableSet s) (hf : ContinuousOn f s)
    {A : Set β} (hA : MeasurableSet A) : MeasurableSet (s ∩ f ⁻¹' A) := by
  have hres : Measurable (s.domRestrict f) := hf.domRestrict.measurable
  have hset : s ∩ f ⁻¹' A = Subtype.val '' (s.domRestrict f ⁻¹' A) := by
    ext z
    constructor
    · rintro ⟨hz, hzA⟩
      exact ⟨⟨z, hz⟩, hzA, rfl⟩
    · rintro ⟨⟨z, hz⟩, hzA, rfl⟩
      exact ⟨hz, hzA⟩
  rw [hset]
  exact (MeasurableEmbedding.subtype_coe hs).measurableSet_image.2 (hres hA)

omit [IsComplexManifold n M] in
theorem measurableSet_chartSymm_image [MeasurableSpace M] [BorelSpace M] (e : ComplexChart n M)
    {A : Set (ComplexModel n)} (hA : MeasurableSet A) (hAt : A ⊆ e.val.target) :
    MeasurableSet (e.val.symm '' A) := by
  rw [e.val.symm_image_eq_source_inter_preimage hAt]
  exact measurableSet_inter_preimage_of_continuousOn e.val.open_source.measurableSet
    e.val.continuousOn hA

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **The identity on a small ball.**  Around every point of a chart target there is a ball on
whose measurable subsets the global mixed measure of `θ` with potentials `0` is the smooth
measure with density `actualMixedTopDensity (θᵢ(z))ᵢ`. -/
theorem exists_ball_globalMixedMeasure_image_eq {θ : Fin n → ClosedRealOneOneForm n M}
    (hθ : ∀ i, ThetaPlurisubharmonic (θ i).val (fun _ => 0)) (e : ComplexChart n M)
    {z₀ : ComplexModel n} (hz₀ : z₀ ∈ e.val.target) :
    ∃ r : ℝ, 0 < r ∧ ball z₀ r ⊆ e.val.target ∧ ∀ K : Set (ComplexModel n), MeasurableSet K →
      K ⊆ ball z₀ r →
        globalMixedMeasure θ (fun _ _ => 0) hθ (e.val.symm '' K) =
          ∫⁻ z in K, chartDensity θ e z := by
  classical
  choose W ρ hzW hρ hpsh using fun i => hθ i e z₀ hz₀
  set D : Opens (ComplexModel n) :=
    ⟨e.val.target ∩ ⋂ i, W i, e.val.open_target.inter (isOpen_iInter_of_finite fun i => (hρ i).1)⟩
    with hD
  have hDW : ∀ i, (D : Set (ComplexModel n)) ⊆ W i := fun i _ hy => mem_iInter.mp hy.2 i
  have hz₀D : z₀ ∈ D := ⟨hz₀, mem_iInter.mpr hzW⟩
  let Q : Patch θ (fun _ _ => 0) :=
    { chart := e
      domain := D
      domain_le_target := inter_subset_left
      potential := ρ
      localPotential := fun i => (hρ i).mono D.isOpen (hDW i)
      plurisubharmonic := fun i => (hpsh i).mono (hDW i) }
  have hcorr : ∀ i y, Q.corrected i y = ((ρ i y : ℝ) : EReal) := fun i y => by
    simp [Patch.corrected, Q, chartFunction]
  -- a neighbourhood where every `ρ i` stays above `ρ i z₀ - 1`
  have hcont : ∀ i, ContinuousAt (ρ i) z₀ := fun i =>
    (hρ i).2.2.1.continuousOn.continuousAt ((hρ i).1.mem_nhds (hzW i))
  have hlow : ∀ i, {y | ρ i z₀ - 1 < ρ i y} ∈ 𝓝 z₀ := fun i =>
    (hcont i).eventually (lt_mem_nhds (by linarith))
  have hnhds : (D : Set (ComplexModel n)) ∩ ⋂ i, {y | ρ i z₀ - 1 < ρ i y} ∈ 𝓝 z₀ :=
    inter_mem (D.isOpen.mem_nhds hz₀D) (iInter_mem.mpr hlow)
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp hnhds
  set B : Opens (ComplexModel n) := ⟨ball z₀ r, isOpen_ball⟩ with hB
  have hBD : B ≤ Q.domain := fun y hy => (hball (ball_subset_closedBall hy)).1
  have hBrel : RelativelyCompactIn B Q.domain := by
    refine ⟨(isCompact_closedBall _ _).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall, fun y hy => ?_⟩
    exact (hball (closure_ball_subset_closedBall hy)).1
  obtain ⟨k, hk⟩ := exists_nat_gt (∑ i, |ρ i z₀| + 1)
  have hBk : (B : Set (ComplexModel n)) ⊆ commonStrictLocus Q.domain Q.corrected k := by
    intro y hy
    refine ⟨hBD hy, fun i => ?_⟩
    rw [hcorr]
    have h1 : ρ i z₀ - 1 < ρ i y := mem_iInter.mp (hball (ball_subset_closedBall hy)).2 i
    have h2 : |ρ i z₀| ≤ ∑ j, |ρ j z₀| :=
      Finset.single_le_sum (f := fun j => |ρ j z₀|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have h3 := neg_abs_le (ρ i z₀)
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  have hfun : (fun i z => (Q.corrected i z).toReal) = ρ := by
    funext i z
    rw [hcorr, EReal.toReal_coe]
  have hρB : ∀ i, ContDiffOn ℝ ∞ (ρ i) B := fun i =>
    (hρ i).2.2.1.mono fun y hy => hDW i (hBD hy)
  have hρ2 : ∀ i, ∀ y ∈ B, ContDiffAt ℝ 2 (ρ i) y := fun i y hy =>
    ((hρB i y hy).contDiffAt (B.isOpen.mem_nhds hy)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hddc : ∀ i, ∀ y ∈ B, smoothDDC (ρ i) y = (θ i).val.coeff e y := fun i y hy =>
    (hρ i).2.2.2 (hDW i (hBD hy))
  have htarget : ∀ y ∈ B, y ∈ e.val.target := fun y hy => (hBD hy).1
  have hsemi : ∀ i, ∀ y ∈ B, IsSemipositiveOneOne (smoothDDC (ρ i) y) := fun i y hy => by
    rw [hddc i y hy]
    exact isSemipositiveOneOne_coeff (hθ i) (htarget y hy)
  have hdens : ∀ y ∈ B, mixedDensity ρ y = actualMixedTopDensity fun i => (θ i).val.coeff e y :=
    fun y hy => by
      rw [← actualMixedTopDensity_smoothDDC fun i => hρ2 i y hy]
      congr 1
      funext i
      exact hddc i y hy
  have hsm : IsSmoothMixedPshOn B (fun i z => (Q.corrected i z).toReal) := by
    rw [hfun]
    refine ⟨fun i => ⟨hρB i, ?_, fun y hy =>
      SmoothDDCHessianPositivity.complexHessian_posSemidef_of_coefficientSemipositive
        (hρ2 i y hy) (hsemi i y hy).2⟩, fun y hy => ?_⟩
    · have := (hpsh i).mono fun y hy => hDW i (hBD hy)
      simpa [chartFunction] using this
    · rw [hdens y hy]
      exact actualMixedTopDensity_nonneg fun i =>
        isSemipositiveOneOne_coeff (hθ i) (htarget y hy)
  refine ⟨r, hr, fun y hy => htarget y hy, fun K hK hKB => ?_⟩
  rw [FullSpacePatchMeasure.globalMixedMeasure_coordinate_inverse_image_eq_smoothMixedMeasure
    hθ Q B hBD k hBrel hBk hsm hKB]
  rw [smoothMixedMeasure, withDensity_apply _ hK, Measure.restrict_restrict hK,
    show K ∩ (B : Set (ComplexModel n)) = K from inter_eq_left.mpr hKB]
  refine setLIntegral_congr_fun hK fun z hz => ?_
  simp only [chartDensity]
  congr 1
  rw [hfun]
  exact hdens z (hKB hz)

/-- **The global mixed measure of smooth semipositive forms is the smooth measure**: for every
chart `e` and every measurable subset `S` of its target,
`globalMixedMeasure θ 0 (e⁻¹ S) = ∫_S actualMixedTopDensity (θᵢ(z))ᵢ dλ`. -/
theorem globalMixedMeasure_image_eq_lintegral {θ : Fin n → ClosedRealOneOneForm n M}
    (hθ : ∀ i, ThetaPlurisubharmonic (θ i).val (fun _ => 0)) (e : ComplexChart n M)
    {S : Set (ComplexModel n)} (hS : MeasurableSet S) (hSe : S ⊆ e.val.target) :
    globalMixedMeasure θ (fun _ _ => 0) hθ (e.val.symm '' S) =
      ∫⁻ z in S, chartDensity θ e z := by
  classical
  set mu : Measure M := globalMixedMeasure θ (fun _ _ => 0) hθ with hmu
  have hlocal : ∀ x : S, ∃ r : ℝ, 0 < r ∧ ∀ K : Set (ComplexModel n), MeasurableSet K →
      K ⊆ ball (x : ComplexModel n) r →
        mu (e.val.symm '' K) = ∫⁻ z in K, chartDensity θ e z := by
    rintro ⟨x, hx⟩
    obtain ⟨r, hr, -, hkey⟩ := exists_ball_globalMixedMeasure_image_eq hθ e (hSe hx)
    exact ⟨r, hr, hkey⟩
  choose r hrpos hkey using hlocal
  rcases Set.eq_empty_or_nonempty S with rfl | hSne
  · rw [Set.image_empty, measure_empty, Measure.restrict_empty, lintegral_zero_measure]
  obtain ⟨T, hTcount, hTunion⟩ :=
    TopologicalSpace.isOpen_iUnion_countable (fun x : S => ball (x : ComplexModel n) (r x))
      fun x => isOpen_ball
  have hcover : S ⊆ ⋃ x ∈ T, ball ((x : S) : ComplexModel n) (r x) := by
    intro w hw
    rw [hTunion]
    exact mem_iUnion.mpr ⟨⟨w, hw⟩, mem_ball_self (hrpos ⟨w, hw⟩)⟩
  have hTne : T.Nonempty := by
    obtain ⟨w, hw⟩ := hSne
    obtain ⟨x, hxT, -⟩ := mem_iUnion₂.mp (hcover hw)
    exact ⟨x, hxT⟩
  obtain ⟨f, hf⟩ := hTcount.exists_eq_range hTne
  set A : ℕ → Set (ComplexModel n) :=
    fun k => S ∩ ball ((f k : S) : ComplexModel n) (r (f k)) with hA
  have hAmeas : ∀ k, MeasurableSet (A k) := fun k => hS.inter measurableSet_ball
  have hAunion : (⋃ k, A k) = S := by
    apply Subset.antisymm (iUnion_subset fun k => inter_subset_left)
    intro w hw
    obtain ⟨x, hxT, hxb⟩ := mem_iUnion₂.mp (hcover hw)
    rw [hf] at hxT
    obtain ⟨k, rfl⟩ := hxT
    exact mem_iUnion.mpr ⟨k, hw, hxb⟩
  set Dj : ℕ → Set (ComplexModel n) := disjointed A with hDj
  have hDmeas : ∀ k, MeasurableSet (Dj k) := MeasurableSet.disjointed hAmeas
  have hDdisj : Pairwise (Function.onFun Disjoint Dj) := disjoint_disjointed A
  have hDunion : (⋃ k, Dj k) = S := by rw [hDj, iUnion_disjointed, hAunion]
  have hDball : ∀ k, Dj k ⊆ ball ((f k : S) : ComplexModel n) (r (f k)) := fun k =>
    (disjointed_le A k).trans inter_subset_right
  have hDS : ∀ k, Dj k ⊆ S := fun k => (disjointed_le A k).trans inter_subset_left
  have hpiece : ∀ k, mu (e.val.symm '' Dj k) = ∫⁻ z in Dj k, chartDensity θ e z := fun k =>
    hkey (f k) (Dj k) (hDmeas k) (hDball k)
  have hinj : InjOn e.val.symm e.val.target := e.val.symm.injOn
  have himagedisj : Pairwise (Function.onFun Disjoint fun k => e.val.symm '' Dj k) := by
    intro i j hij
    have hinter := hinj.image_inter ((hDS i).trans hSe) ((hDS j).trans hSe)
    change Disjoint (e.val.symm '' Dj i) (e.val.symm '' Dj j)
    rw [Set.disjoint_iff_inter_eq_empty, ← hinter,
      Set.disjoint_iff_inter_eq_empty.mp (hDdisj hij), Set.image_empty]
  have himagemeas : ∀ k, MeasurableSet (e.val.symm '' Dj k) := fun k =>
    measurableSet_chartSymm_image e (hDmeas k) ((hDS k).trans hSe)
  calc
    mu (e.val.symm '' S) = mu (⋃ k, e.val.symm '' Dj k) := by rw [← Set.image_iUnion, hDunion]
    _ = ∑' k, mu (e.val.symm '' Dj k) := measure_iUnion himagedisj himagemeas
    _ = ∑' k, ∫⁻ z in Dj k, chartDensity θ e z := tsum_congr hpiece
    _ = ∫⁻ z in ⋃ k, Dj k, chartDensity θ e z := (lintegral_iUnion hDmeas hDdisj _).symm
    _ = ∫⁻ z in S, chartDensity θ e z := by rw [hDunion]

/-- **The map form**: restricted to the inverse image of a measurable piece of a chart, the
global mixed measure of smooth semipositive forms is the push-forward of the smooth measure
`D dλ` on the piece by the inverse chart. -/
theorem restrict_image_eq_map {θ : Fin n → ClosedRealOneOneForm n M}
    (hθ : ∀ i, ThetaPlurisubharmonic (θ i).val (fun _ => 0)) (e : ComplexChart n M)
    {K : Set (ComplexModel n)} (hK : MeasurableSet K) (hKe : K ⊆ e.val.target) :
    (globalMixedMeasure θ (fun _ _ => 0) hθ).restrict (e.val.symm '' K) =
      Measure.map e.val.symm ((volume.restrict K).withDensity (chartDensity θ e)) := by
  have hae : AEMeasurable e.val.symm ((volume.restrict K).withDensity (chartDensity θ e)) :=
    ((e.val.continuousOn_symm.mono hKe).aemeasurable hK).mono_ac
      (withDensity_absolutelyContinuous _ _)
  ext A hA
  rw [Measure.restrict_apply hA, Measure.map_apply_of_aemeasurable hae hA,
    withDensity_apply' _ _]
  have hpre : MeasurableSet (K ∩ e.val.symm ⁻¹' A) := by
    have h := measurableSet_inter_preimage_of_continuousOn e.val.open_target.measurableSet
      e.val.continuousOn_symm hA
    have : K ∩ e.val.symm ⁻¹' A = K ∩ (e.val.target ∩ e.val.symm ⁻¹' A) := by
      rw [← inter_assoc, inter_eq_left.mpr hKe]
    rw [this]
    exact hK.inter h
  have himage : A ∩ e.val.symm '' K = e.val.symm '' (K ∩ e.val.symm ⁻¹' A) := by
    rw [image_inter_preimage, inter_comm]
  rw [himage, globalMixedMeasure_image_eq_lintegral hθ e hpre (inter_subset_left.trans hKe),
    Measure.restrict_restrict' hK, inter_comm]

/-- **Change of variables** for the global mixed measure of smooth semipositive forms on the
inverse image of a measurable piece of a chart. -/
theorem setLIntegral_image_eq {θ : Fin n → ClosedRealOneOneForm n M}
    (hθ : ∀ i, ThetaPlurisubharmonic (θ i).val (fun _ => 0)) (e : ComplexChart n M)
    {K : Set (ComplexModel n)} (hK : MeasurableSet K) (hKe : K ⊆ e.val.target)
    {g : M → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in e.val.symm '' K, g x ∂(globalMixedMeasure θ (fun _ _ => 0) hθ) =
      ∫⁻ z in K, chartDensity θ e z * g (e.val.symm z) := by
  have hae : AEMeasurable e.val.symm ((volume.restrict K).withDensity (chartDensity θ e)) :=
    ((e.val.continuousOn_symm.mono hKe).aemeasurable hK).mono_ac
      (withDensity_absolutelyContinuous _ _)
  rw [restrict_image_eq_map hθ e hK hKe, lintegral_map' hg.aemeasurable hae]
  have hd : AEMeasurable (chartDensity θ e) (volume.restrict K) :=
    ((continuousOn_chartDensity θ e).mono hKe).aemeasurable hK
  have hgs : AEMeasurable (fun z => g (e.val.symm z)) (volume.restrict K) :=
    hg.comp_aemeasurable ((e.val.continuousOn_symm.mono hKe).aemeasurable hK)
  rw [lintegral_withDensity_eq_lintegral_mul₀ hd hgs]
  rfl

end SGPT.Foundations.Analysis.Pending.SmoothMixedMeasureDensity
