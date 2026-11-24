/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ThetaCapacityChartLocal
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorDecreasingLimit
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.VaguePortmanteau

/-!
# The diagonal measure along a decreasing sequence: the open-set portmanteau

[Xia's envelope concentration proof](https://github.com/MingchenXia/SGPT/blob/4390e77497d699ac3a4f878b97c34fc867513add/author/chapter_npp.tex#L769-L796)
passes to a limit against weights converging in capacity. This module gives a
related unweighted result on open sets inside a bounded chart. The
Bedford–Taylor convergence theorem for decreasing sequences is the input, which the
workspace has in the model (`Pending.BedfordTaylorDecreasingLimit`) but not for
the global non-pluripolar measure.  This module supplies the half the proof
actually uses, on one slot chart:

  `theta^n_w (O) <= liminf_k theta^n_{u_k} (O)`

for `O` open inside the slot-chart source and `u_k` decreasing to `w`, all
bounded there.  Nothing is assumed away from that chart, so the statement is
applicable on relatively compact subsets off the non-Kähler locus when
the bounds follow from [the local bound for the reference potential](https://github.com/MingchenXia/SGPT/blob/4390e77497d699ac3a4f878b97c34fc867513add/author/chapter_npp.tex#L448-L455).

The proof is a translation.  `ThetaCapacityChartLocal.exists_isBTLimit_of_boundedOn`
identifies the restriction of the global measure to the slot-chart source with
the pushforward of the canonical Bedford--Taylor measure of the corrected chart
potential; `BedfordTaylorDecreasingLimit.tendsto_integral_of_antitone_isBTLimit`
gives vague convergence of those coordinate measures on the coordinate domain;
and `VaguePortmanteau.measure_le_liminf_of_tendsto_integral` turns vague
convergence into the open-set inequality.  The coordinate image of an open
subset of the source is an open subset of the domain, which is what lets the
last step be applied to the image of `O`.
-/

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.DiagonalMeasureDecreasingPortmanteau

open FirstPass FirstPass.PositiveClasses FirstPass.GlobalPotentialPatches
open FirstPass.MongeAmpere
open GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.GlobalSlotStokes
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.ThetaCapacityChart
open SGPT.Foundations.Analysis.Pending.ThetaCapacityChartLocal

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-! ### Reading the slot chart -/

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- A point of the coordinate domain pulls back into the slot-chart source. -/
theorem symm_mem_source {theta : ClosedRealOneOneForm n M} {e : ComplexChart n M}
    {D : Opens (ComplexModel n)} {hD : (D : Set (ComplexModel n)) ⊆ e.val.target}
    {rho : ComplexModel n → ℝ} {hrho : IsSmoothLocalPotential theta.val e D rho}
    {z : ComplexModel n} (hz : z ∈ (D : Set (ComplexModel n))) :
    e.val.symm z ∈ ((diagSlotChart theta e D hD rho hrho).source : Set M) := by
  refine ⟨e.val.map_target (hD hz), ?_⟩
  change e.val (e.val.symm z) ∈ (D : Set (ComplexModel n))
  rwa [e.val.right_inv (hD hz)]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The chart bounds of a potential bounded on the slot-chart source. -/
theorem boundedOn_domain_of_boundedOn_source {theta : ClosedRealOneOneForm n M}
    {e : ComplexChart n M} {D : Opens (ComplexModel n)}
    {hD : (D : Set (ComplexModel n)) ⊆ e.val.target} {rho : ComplexModel n → ℝ}
    {hrho : IsSmoothLocalPotential theta.val e D rho} {u : M → EReal} {c d : ℝ}
    (hb : ∀ x ∈ ((diagSlotChart theta e D hD rho hrho).source : Set M),
      (c : EReal) ≤ u x ∧ u x ≤ (d : EReal)) :
    ∀ z ∈ (D : Set (ComplexModel n)),
      (c : EReal) ≤ u (e.val.symm z) ∧ u (e.val.symm z) ≤ (d : EReal) := by
  intro z hz
  exact hb _ (symm_mem_source (hrho := hrho) hz)

/-- **The global diagonal measure of a subset of the slot-chart source is the
canonical Bedford--Taylor measure of the corrected chart potential, evaluated on
the coordinate image.**  This is the identification inside
`ThetaCapacityChartLocal.diagonalPotentialMeasure_le_relCapacity_of_boundedOn`,
isolated so that it can be used with a test other than the relative capacity. -/
theorem diagonalPotentialMeasure_eq_canonical {theta : ClosedRealOneOneForm n M}
    {e : ComplexChart n M} {D : Opens (ComplexModel n)}
    {hD : (D : Set (ComplexModel n)) ⊆ e.val.target} {rho : ComplexModel n → ℝ}
    {hrho : IsSmoothLocalPotential theta.val e D rho} {u : M → EReal}
    (hu : IsThetaPshPotential theta.val u)
    (hb : IsBoundedPotentialOn u ((diagSlotChart theta e D hD rho hrho).source : Set M))
    (hg : IsLocallyBoundedPshOn D (correctedChartReal u e rho))
    {E : Set M} (hE : E ⊆ ((diagSlotChart theta e D hD rho hrho).source : Set M)) :
    diagonalPotentialMeasure theta u hu E =
      canonicalBedfordTaylorMeasure D (correctedChartReal u e rho) hg (e.val '' E) := by
  classical
  set J := diagSlotChart theta e D hD rho hrho with hJ
  obtain ⟨mu, hmuBT, hmueq⟩ :=
    exists_isBTLimit_of_boundedOn J (u := fun _ => u) (fun _ => hu.1) (fun _ => hb)
  have hfam : (fun (i : Fin n) (z : ComplexModel n) =>
      (u (J.chart.val.symm z)).toReal + J.potential i z) =
        fun _ => correctedChartReal u e rho := rfl
  rw [hfam] at hmuBT
  have hmu : mu = canonicalBedfordTaylorMeasure D (correctedChartReal u e rho) hg :=
    hmuBT.unique (isBTLimit_canonicalBedfordTaylorMeasure hg)
  have hrestr : diagonalPotentialMeasure theta u hu E =
      ((diagonalPotentialMeasure theta u hu).restrict (J.source : Set M)) E := by
    rw [Measure.restrict_apply' J.source.isOpen.measurableSet,
      inter_eq_self_of_subset_left hE]
  rw [hrestr]
  change ((globalMixedMeasure (fun _ : Fin n => theta) (fun _ => u)
    (fun _ => hu.1)).restrict (J.source : Set M)) E = _
  have hsrc : E ⊆ ((J.patch (fun _ => u) (fun _ => hu.1)).source : Set M) := hE
  rw [hmueq, Patch.pushMeasure_apply_image, inter_eq_self_of_subset_left hsrc, hmu]
  rfl

/-! ### The open-set portmanteau on a slot chart -/

/-- **`theta^n` is lower semicontinuous along a decreasing sequence, on the open
subsets of a slot chart where the potentials are bounded.**

`u_k` decreases pointwise to `w`, all of them bounded on the slot-chart source;
then for every open `O` inside that source,

  `theta^n_w (O) <= liminf_k theta^n_{u_k} (O)`.

This is the chartwise portmanteau consequence of Bedford–Taylor
decreasing convergence ([Błocki, Theorem 2.1.5](https://gamma.im.uj.edu.pl/~blocki/publ/ln/wykl.pdf#page=36)). The
boundedness hypotheses identify the global non-pluripolar measures with their
local Bedford–Taylor representatives. The open-set inequality is unweighted. -/
theorem diagonalPotentialMeasure_le_liminf_of_antitone {theta : ClosedRealOneOneForm n M}
    {e : ComplexChart n M} {D : Opens (ComplexModel n)}
    {hD : (D : Set (ComplexModel n)) ⊆ e.val.target} {rho : ComplexModel n → ℝ}
    {hrho : IsSmoothLocalPotential theta.val e D rho}
    {u : ℕ → M → EReal} {w : M → EReal}
    (hu : ∀ k, IsThetaPshPotential theta.val (u k))
    (hw : IsThetaPshPotential theta.val w)
    (hub : ∀ k, IsBoundedPotentialOn (u k)
      ((diagSlotChart theta e D hD rho hrho).source : Set M))
    (hwb : IsBoundedPotentialOn w
      ((diagSlotChart theta e D hD rho hrho).source : Set M))
    {L : ℝ} (hL : ∀ z ∈ (D : Set (ComplexModel n)), |rho z| ≤ L)
    (hanti : ∀ x, Antitone fun k => u k x)
    (hlim : ∀ x, Tendsto (fun k => u k x) atTop (𝓝 (w x)))
    {O : Set M} (hO : IsOpen O)
    (hOsub : O ⊆ ((diagSlotChart theta e D hD rho hrho).source : Set M)) :
    diagonalPotentialMeasure theta w hw O ≤
      liminf (fun k => diagonalPotentialMeasure theta (u k) (hu k) O) atTop := by
  classical
  set J := diagSlotChart theta e D hD rho hrho with hJ
  -- the corrected chart potentials
  set g : ℕ → ComplexModel n → ℝ := fun k => correctedChartReal (u k) e rho with hg_def
  set v : ComplexModel n → ℝ := correctedChartReal w e rho with hv_def
  have hgk : ∀ k, IsLocallyBoundedPshOn D (g k) := by
    intro k
    obtain ⟨c, d, hcd⟩ := hub k
    exact correctedChartReal_isLocallyBoundedPshOn_of_boundedOn (hu k).1 hrho
      (boundedOn_domain_of_boundedOn_source (hrho := hrho) hcd) hL
  have hv : IsLocallyBoundedPshOn D v := by
    obtain ⟨c, d, hcd⟩ := hwb
    exact correctedChartReal_isLocallyBoundedPshOn_of_boundedOn hw.1 hrho
      (boundedOn_domain_of_boundedOn_source (hrho := hrho) hcd) hL
  -- the corrected chart potentials decrease to the limit one
  have hfin : ∀ (k : ℕ), ∀ z ∈ (D : Set (ComplexModel n)),
      ((u k (e.val.symm z)).toReal : EReal) = u k (e.val.symm z) := by
    intro k z hz
    exact EReal.coe_toReal ((hub k).ne_top (symm_mem_source (hrho := hrho) hz))
      ((hub k).ne_bot (symm_mem_source (hrho := hrho) hz))
  have hantig : ∀ z ∈ (D : Set (ComplexModel n)), Antitone fun k => g k z := by
    intro z hz j k hjk
    have h : u k (e.val.symm z) ≤ u j (e.val.symm z) := hanti (e.val.symm z) hjk
    rw [← hfin k z hz, ← hfin j z hz, EReal.coe_le_coe_iff] at h
    change g k z ≤ g j z
    simp only [hg_def, correctedChartReal]
    linarith
  have hlimg : ∀ z ∈ (D : Set (ComplexModel n)),
      Tendsto (fun k => g k z) atTop (𝓝 (v z)) := by
    intro z hz
    have hreal : Tendsto (fun k => (u k (e.val.symm z)).toReal) atTop
        (𝓝 ((w (e.val.symm z)).toReal)) :=
      (EReal.tendsto_toReal (hwb.ne_top (symm_mem_source (hrho := hrho) hz))
        (hwb.ne_bot (symm_mem_source (hrho := hrho) hz))).comp (hlim (e.val.symm z))
    exact hreal.add tendsto_const_nhds
  -- vague convergence of the coordinate measures on the coordinate domain
  set muk : ℕ → Measure (ComplexModel n) :=
    fun k => canonicalBedfordTaylorMeasure D (g k) (hgk k) with hmuk_def
  set nu : Measure (ComplexModel n) := canonicalBedfordTaylorMeasure D v hv with hnu_def
  have hBTk : ∀ k, IsBTLimit D (fun _ => g k) (muk k) := fun k =>
    isBTLimit_canonicalBedfordTaylorMeasure (hgk k)
  have hBT : IsBTLimit D (fun _ => v) nu := isBTLimit_canonicalBedfordTaylorMeasure hv
  have hconv : ∀ φ : ComplexModel n → ℝ, Continuous φ → HasCompactSupport φ →
      tsupport φ ⊆ (D : Set (ComplexModel n)) →
      Tendsto (fun k => ∫ z, φ z ∂(muk k)) atTop (𝓝 (∫ z, φ z ∂nu)) := by
    intro φ hφ hφc hφD
    exact tendsto_integral_of_antitone_isBTLimit hgk hv hantig hlimg hBTk hBT hφ hφc hφD
  -- the coordinate image of `O` is open and contained in the coordinate domain
  have hOsrc : O ⊆ e.val.source := fun x hx => (hOsub hx).1
  have hOopen : IsOpen (e.val '' O) := e.val.isOpen_image_of_subset_source hO hOsrc
  have hOD : e.val '' O ⊆ (D : Set (ComplexModel n)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hOsub hx).2
  -- portmanteau in the chart
  have hport : nu (e.val '' O) ≤ liminf (fun k => muk k (e.val '' O)) atTop :=
    VaguePortmanteau.measure_le_liminf_of_tendsto_integral hOopen hOD
      (fun k K hK hKD => (hBTk k).2.1 K hK hKD) (fun K hK hKD => hBT.2.1 K hK hKD) hconv
  rw [diagonalPotentialMeasure_eq_canonical hw hwb hv hOsub]
  refine hport.trans (liminf_le_liminf (Eventually.of_forall fun k => ?_))
  rw [diagonalPotentialMeasure_eq_canonical (hu k) (hub k) (hgk k) hOsub]

end

end SGPT.Foundations.Analysis.Pending.DiagonalMeasureDecreasingPortmanteau
