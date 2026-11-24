/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BoundedGlobalProduct

/-!
# The local Bedford--Taylor model of the global product, from a bound on ONE patch

`Pending.BoundedGlobalProduct` identifies the glued non-pluripolar measure
`globalMixedMeasure` with an honest Bedford--Taylor measure on each patch, but
only for a tuple of potentials that is bounded on **all** of `M`
(`IsBoundedPotential`).  The same hypothesis is what
`Pending.GlobalSlotStokes.SlotChart.exists_isBTLimit` asks for.  That global
bound is the obstruction recorded in I-0282: Xia's own reference potential
`V_theta` is unbounded below as soon as `nK({theta})` is nonempty, which is the
only case Nakamaye's theorem is about.

The bound does not have to be global.  `globalMixedMeasure` is *defined* patch
by patch through `mixedTruncationLimitMeasure` on a chart domain
(`GlobalNonPluripolar.globalMixedMeasure_restrict_patch`, which assumes
nothing), and
`MixedNonPluripolar.mixedTruncationLimitMeasure_eq_canonical_of_eqOn`
identifies that truncation limit with the bounded mixed Bedford--Taylor measure
from data on the chart domain alone.  So a bound on the **source of a single
patch** already puts the global measure in honest Bedford--Taylor form there.

This is what Xia's Lemma 2.4.3 (`xia-sgpt:page-0079`) needs: its datum
`P_theta(f)` is locally bounded on `X \ nK({theta})` by Lemma 2.4.1, never on
`X`, and (2.21) is a statement about the measure on an open subset of that
complement.  The bound is *used* only through the local model, so the I-0282
architecture objection applies to the capacity half of the Section 2.3 stack,
not to the measure half.

Nothing in this module is new analysis: it is the bounded patch argument of
`Pending.BoundedGlobalProduct` with `IsBoundedPotential` replaced by
`IsBoundedPotentialOn _ P.source` throughout.  The one genuinely new lemma is
the congruence `plurisubharmonicOn_congr` for `PlurisubharmonicOn` on an open
set, which was missing: plurisubharmonicity of a germ at a point of an open set
only reads values on that set, so `DiscPshOn.congr` transports it.
-/

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis

/-! ### Congruence of plurisubharmonicity on an open set -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Plurisubharmonicity on an open set only depends on the values there.**
The germ at a point of `U` may be tested on `V ∩ U`, and `DiscPshOn.congr`
transports the disc criterion across an `EqOn`. -/
theorem plurisubharmonicOn_congr {u w : E → EReal} {U : Set E} (hU : IsOpen U)
    (hu : PlurisubharmonicOn u U) (heq : EqOn u w U) : PlurisubharmonicOn w U := by
  intro x hx
  obtain ⟨V, hVopen, hxV, hV⟩ := hu x hx
  exact ⟨V ∩ U, hVopen.inter hU, ⟨hxV, hx⟩,
    (hV.mono inter_subset_left).congr (heq.mono inter_subset_right)⟩

end SGPT.Foundations.Analysis

namespace SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
open FirstPass.GlobalPotentialPatches
open MixedMongeAmpere MixedNonPluripolar GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}

/-- A two-sided real bound for an extended-real potential **on a subset** of
`M`.  Unlike `BoundedGlobalProduct.IsBoundedPotential` this is not a global
hypothesis: it is exactly what one gets by shrinking a chart inside an open set
on which the potential is locally bounded. -/
def IsBoundedPotentialOn (v : M → EReal) (S : Set M) : Prop :=
  ∃ a b : ℝ, ∀ x ∈ S, (a : EReal) ≤ v x ∧ v x ≤ (b : EReal)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem IsBoundedPotentialOn.of_isBoundedPotential {v : M → EReal}
    (hv : IsBoundedPotential v) (S : Set M) : IsBoundedPotentialOn v S := by
  obtain ⟨a, b, hab⟩ := hv
  exact ⟨a, b, fun x _ => hab x⟩

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem IsBoundedPotentialOn.mono {v : M → EReal} {S T : Set M}
    (hv : IsBoundedPotentialOn v T) (hST : S ⊆ T) : IsBoundedPotentialOn v S := by
  obtain ⟨a, b, hab⟩ := hv
  exact ⟨a, b, fun x hx => hab x (hST hx)⟩

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem IsBoundedPotentialOn.ne_bot {v : M → EReal} {S : Set M}
    (hv : IsBoundedPotentialOn v S) {x : M} (hx : x ∈ S) : v x ≠ ⊥ := by
  obtain ⟨a, _, hab⟩ := hv
  exact ne_of_gt ((EReal.bot_lt_coe a).trans_le (hab x hx).1)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem IsBoundedPotentialOn.ne_top {v : M → EReal} {S : Set M}
    (hv : IsBoundedPotentialOn v S) {x : M} (hx : x ∈ S) : v x ≠ ⊤ := by
  obtain ⟨_, b, hab⟩ := hv
  exact ne_of_lt ((hab x hx).2.trans_lt (EReal.coe_lt_top b))

/-! ### The corrected potential of a patch bounded on its own source -/

section Patch

variable {i : Fin n} {P : Patch θ u}

theorem correctedReal_eq_of_boundedOn (hb : IsBoundedPotentialOn (u i) P.source)
    {z : ComplexModel n} (hz : z ∈ P.domain) :
    correctedReal P i z = (u i (P.chart.val.symm z)).toReal + P.potential i z := by
  have hmem : P.chart.val.symm z ∈ P.source := P.map_target hz
  have hsplit : P.corrected i z =
      (((u i (P.chart.val.symm z)).toReal + P.potential i z : ℝ) : EReal) := by
    change (u i (P.chart.val.symm z)) + ((P.potential i z : ℝ) : EReal) = _
    rw [EReal.coe_add, EReal.coe_toReal (hb.ne_top hmem) (hb.ne_bot hmem)]
  change (P.corrected i z).toReal = _
  rw [hsplit, EReal.toReal_coe]

theorem coe_correctedReal_of_boundedOn (hb : IsBoundedPotentialOn (u i) P.source)
    {z : ComplexModel n} (hz : z ∈ P.domain) :
    ((correctedReal P i z : ℝ) : EReal) = P.corrected i z := by
  have hmem : P.chart.val.symm z ∈ P.source := P.map_target hz
  rw [correctedReal_eq_of_boundedOn hb hz]
  change _ = (u i (P.chart.val.symm z)) + ((P.potential i z : ℝ) : EReal)
  rw [EReal.coe_add, EReal.coe_toReal (hb.ne_top hmem) (hb.ne_bot hmem)]

/-- **The corrected potential of a patch bounded on its own source is real
locally bounded PSH on the chart domain.**  This is
`BoundedGlobalProduct.correctedReal_isLocallyBoundedPshOn` with the global
bound replaced by a bound on `P.source`: every point at which the bound is used
is `P.chart.val.symm w` for some `w` in the chart domain, hence lies in
`P.source`. -/
theorem correctedReal_isLocallyBoundedPshOn_of_boundedOn
    (hb : IsBoundedPotentialOn (u i) P.source) :
    IsLocallyBoundedPshOn P.domain (correctedReal P i) := by
  obtain ⟨a, b, hab⟩ := hb
  have hb' : IsBoundedPotentialOn (u i) P.source := ⟨a, b, hab⟩
  refine ⟨?_, ?_⟩
  · refine plurisubharmonicOn_congr P.domain.isOpen (P.plurisubharmonic i) ?_
    intro z hz
    exact (coe_correctedReal_of_boundedOn hb' hz).symm
  · intro z hz
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (P.domain.isOpen.mem_nhds hz)
    have hclosed : closedBall z (r / 2) ⊆ (P.domain : Set (ComplexModel n)) :=
      (closedBall_subset_ball (by linarith)).trans hball
    obtain ⟨C, hC⟩ := (isCompact_closedBall z (r / 2)).exists_bound_of_continuousOn
      (((P.localPotential i).2.2.1.continuousOn).mono hclosed)
    refine ⟨⟨ball z (r / 2), isOpen_ball⟩, mem_ball_self (by linarith),
      ball_subset_closedBall.trans hclosed, max |a| |b| + C, ?_⟩
    intro w hw
    have hwdom : w ∈ (P.domain : Set (ComplexModel n)) :=
      hclosed (ball_subset_closedBall hw)
    have hwsrc : P.chart.val.symm w ∈ P.source := P.map_target hwdom
    have hwC : |P.potential i w| ≤ C := by
      simpa [Real.norm_eq_abs] using hC w (ball_subset_closedBall hw)
    set s : ℝ := (u i (P.chart.val.symm w)).toReal with hs_def
    have hcoe : ((s : ℝ) : EReal) = u i (P.chart.val.symm w) :=
      EReal.coe_toReal (hb'.ne_top hwsrc) (hb'.ne_bot hwsrc)
    have hsa : a ≤ s := EReal.coe_le_coe_iff.mp (hcoe ▸ (hab _ hwsrc).1)
    have hsb : s ≤ b := EReal.coe_le_coe_iff.mp (hcoe ▸ (hab _ hwsrc).2)
    have habs : |s| ≤ max |a| |b| := by
      refine abs_le.mpr ⟨?_, hsb.trans ((le_abs_self b).trans (le_max_right _ _))⟩
      exact (neg_le_neg (le_max_left |a| |b|)).trans ((neg_abs_le a).trans hsa)
    calc |correctedReal P i w| = |s + P.potential i w| := by
          rw [correctedReal_eq_of_boundedOn hb' hwdom]
      _ ≤ |s| + |P.potential i w| := abs_add_le _ _
      _ ≤ max |a| |b| + C := add_le_add habs hwC

end Patch

theorem correctedReal_isLocallyBoundedMixedPshOn_of_boundedOn (P : Patch θ u)
    (hb : ∀ i, IsBoundedPotentialOn (u i) P.source) :
    IsLocallyBoundedMixedPshOn P.domain (correctedReal P) :=
  fun i => correctedReal_isLocallyBoundedPshOn_of_boundedOn (hb i)

/-- **The coordinate truncation limit of a patch bounded on its own source is
its bounded mixed Bedford--Taylor measure.**  No truncation survives in the
limit, exactly as in the globally bounded case. -/
theorem mixedTruncationLimitMeasure_corrected_of_boundedOn (P : Patch θ u)
    (hb : ∀ i, IsBoundedPotentialOn (u i) P.source) :
    mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic =
      canonicalMixedBedfordTaylorMeasure P.domain (correctedReal P)
        (correctedReal_isLocallyBoundedMixedPshOn_of_boundedOn P hb) :=
  mixedTruncationLimitMeasure_eq_canonical_of_eqOn
    (correctedReal_isLocallyBoundedMixedPshOn_of_boundedOn P hb) P.plurisubharmonic
    (fun i _ hz => (coe_correctedReal_of_boundedOn (hb i) hz).symm)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **The local Bedford--Taylor model of the global non-pluripolar measure,
from a bound on one patch only.**  Compare
`BoundedGlobalProduct.globalMixedMeasure_restrict_patch_eq_canonical`, which
asks for a bound on all of `M`. -/
theorem globalMixedMeasure_restrict_patch_eq_canonical_of_boundedOn
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (P : Patch θ u)
    (hb : ∀ i, IsBoundedPotentialOn (u i) P.source) :
    (globalMixedMeasure θ u hu).restrict (P.source : Set M) =
      P.pushMeasure (canonicalMixedBedfordTaylorMeasure P.domain (correctedReal P)
        (correctedReal_isLocallyBoundedMixedPshOn_of_boundedOn P hb)) := by
  rw [globalMixedMeasure_restrict_patch hu P]
  exact congrArg P.pushMeasure (mixedTruncationLimitMeasure_corrected_of_boundedOn P hb)

end

end SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
