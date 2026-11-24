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

The bounded-patch statement is suited to [Xia's balayage lemma](https://github.com/MingchenXia/SGPT/blob/4390e77497d699ac3a4f878b97c34fc867513add/author/chapter_npp.tex#L662-L688).
That argument uses [the local bound for the reference potential](https://github.com/MingchenXia/SGPT/blob/4390e77497d699ac3a4f878b97c34fc867513add/author/chapter_npp.tex#L448-L455)
to bound the envelope locally off the non-Kähler locus.

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
  exact correctedReal_isLocallyBoundedPshOn_of_bounds P fun w hw =>
    hab (P.chart.val.symm w) (P.map_target hw)

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
