/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalNonPluripolar

/-!
# The global mixed product of bounded potentials

For a tuple of globally bounded `θ_i`-PSH potentials the corrected potential of
every patch is a real locally bounded PSH function, so the coordinate
truncation limit is the bounded mixed Bedford–Taylor measure and the BEGZ
uniform compact-mass condition holds unconditionally: no Kähler background, no
Stokes theorem and no global regularization is involved.

Consequently the glued measure `globalMixedMeasure` is locally finite for
bounded potentials, and has finite total mass on a compact manifold. This is
the construction half of `gnpp:bounded-global-mass`; the identification of
that mass with `∫ η₁ ∧ ⋯ ∧ η_n` is a separate integration-by-parts argument
and is not asserted here.
-/

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped ENNReal Topology ContDiff

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

namespace SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
open FirstPass.GlobalPotentialPatches
open MixedMongeAmpere MixedNonPluripolar GlobalNonPluripolar

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}

/-- A two-sided real bound for an extended-real potential. No continuity and no
regularity is required, and the bound is global on `M`. -/
def IsBoundedPotential (v : M → EReal) : Prop :=
  ∃ a b : ℝ, ∀ x, (a : EReal) ≤ v x ∧ v x ≤ (b : EReal)

omit [TopologicalSpace M] in
theorem IsBoundedPotential.ne_bot {v : M → EReal} (hv : IsBoundedPotential v) (x : M) :
    v x ≠ ⊥ := by
  obtain ⟨a, _, hab⟩ := hv
  exact ne_of_gt ((EReal.bot_lt_coe a).trans_le (hab x).1)

omit [TopologicalSpace M] in
theorem IsBoundedPotential.ne_top {v : M → EReal} (hv : IsBoundedPotential v) (x : M) :
    v x ≠ ⊤ := by
  obtain ⟨_, b, hab⟩ := hv
  exact ne_of_lt ((hab x).2.trans_lt (EReal.coe_lt_top b))

/-- The real value of a corrected patch potential. For a bounded potential it
is the honest real function whose `EReal` coercion is the corrected potential. -/
def correctedReal (P : Patch θ u) (i : Fin n) (z : ComplexModel n) : ℝ :=
  (P.corrected i z).toReal

theorem correctedReal_eq {i : Fin n} (hb : IsBoundedPotential (u i)) (P : Patch θ u)
    (z : ComplexModel n) :
    correctedReal P i z = (u i (P.chart.val.symm z)).toReal + P.potential i z := by
  have hsplit : P.corrected i z =
      (((u i (P.chart.val.symm z)).toReal + P.potential i z : ℝ) : EReal) := by
    change (u i (P.chart.val.symm z)) + ((P.potential i z : ℝ) : EReal) = _
    rw [EReal.coe_add, EReal.coe_toReal (hb.ne_top _) (hb.ne_bot _)]
  change (P.corrected i z).toReal = _
  rw [hsplit, EReal.toReal_coe]

theorem coe_correctedReal {i : Fin n} (hb : IsBoundedPotential (u i)) (P : Patch θ u)
    (z : ComplexModel n) : ((correctedReal P i z : ℝ) : EReal) = P.corrected i z := by
  rw [correctedReal_eq hb P z]
  change _ = (u i (P.chart.val.symm z)) + ((P.potential i z : ℝ) : EReal)
  rw [EReal.coe_add, EReal.coe_toReal (hb.ne_top _) (hb.ne_bot _)]

/-- Bounds on the chart values of a patch potential suffice for local boundedness. -/
theorem correctedReal_isLocallyBoundedPshOn_of_bounds {i : Fin n} (P : Patch θ u)
    {a b : ℝ} (hab : ∀ w ∈ P.domain,
      (a : EReal) ≤ u i (P.chart.val.symm w) ∧ u i (P.chart.val.symm w) ≤ (b : EReal)) :
    IsLocallyBoundedPshOn P.domain (correctedReal P i) := by
  have hcoe (w : ComplexModel n) (hw : w ∈ P.domain) :
      ((u i (P.chart.val.symm w)).toReal : EReal) = u i (P.chart.val.symm w) :=
    EReal.coe_toReal (ne_of_lt ((hab w hw).2.trans_lt (EReal.coe_lt_top b)))
      (ne_of_gt ((EReal.bot_lt_coe a).trans_le (hab w hw).1))
  have hsplit (w : ComplexModel n) (hw : w ∈ P.domain) :
      P.corrected i w =
        (((u i (P.chart.val.symm w)).toReal + P.potential i w : ℝ) : EReal) := by
    change u i (P.chart.val.symm w) + (P.potential i w : EReal) = _
    rw [EReal.coe_add, hcoe w hw]
  have hreal (w : ComplexModel n) (hw : w ∈ P.domain) :
      correctedReal P i w = (u i (P.chart.val.symm w)).toReal + P.potential i w := by
    rw [correctedReal, hsplit w hw, EReal.toReal_coe]
  refine ⟨?_, ?_⟩
  · refine plurisubharmonicOn_congr P.domain.isOpen (P.plurisubharmonic i) ?_
    intro z hz
    change P.corrected i z = ((correctedReal P i z : ℝ) : EReal)
    rw [hreal z hz]
    exact hsplit z hz
  · intro z hz
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (P.domain.isOpen.mem_nhds hz)
    have hclosed : closedBall z (r / 2) ⊆ (P.domain : Set (ComplexModel n)) :=
      (closedBall_subset_ball (by linarith)).trans hball
    obtain ⟨C, hC⟩ := (isCompact_closedBall z (r / 2)).exists_bound_of_continuousOn
      (((P.localPotential i).2.2.1.continuousOn).mono hclosed)
    refine ⟨⟨ball z (r / 2), isOpen_ball⟩, mem_ball_self (by linarith),
      ball_subset_closedBall.trans hclosed, max |a| |b| + C, ?_⟩
    intro w hw
    have hwdom := hclosed (ball_subset_closedBall hw)
    have hwC : |P.potential i w| ≤ C := by
      simpa [Real.norm_eq_abs] using hC w (ball_subset_closedBall hw)
    set s : ℝ := (u i (P.chart.val.symm w)).toReal
    have hsa : a ≤ s := EReal.coe_le_coe_iff.mp (hcoe w hwdom ▸ (hab w hwdom).1)
    have hsb : s ≤ b := EReal.coe_le_coe_iff.mp (hcoe w hwdom ▸ (hab w hwdom).2)
    have habs : |s| ≤ max |a| |b| := by
      refine abs_le.mpr ⟨?_, hsb.trans ((le_abs_self b).trans (le_max_right _ _))⟩
      exact (neg_le_neg (le_max_left |a| |b|)).trans ((neg_abs_le a).trans hsa)
    rw [hreal w hwdom]
    exact (abs_add_le _ _).trans (add_le_add habs hwC)

/-- **The corrected potential of a bounded tuple is real locally bounded PSH.**
Plurisubharmonicity is the patch's own hypothesis; the local bound combines the
global bound on `u i` with the smoothness of the local potential of `θ i`. -/
theorem correctedReal_isLocallyBoundedPshOn {i : Fin n} (hb : IsBoundedPotential (u i))
    (P : Patch θ u) : IsLocallyBoundedPshOn P.domain (correctedReal P i) := by
  obtain ⟨a, b, hab⟩ := hb
  exact correctedReal_isLocallyBoundedPshOn_of_bounds P fun w _ => hab (P.chart.val.symm w)

theorem correctedReal_isLocallyBoundedMixedPshOn (hb : ∀ i, IsBoundedPotential (u i))
    (P : Patch θ u) : IsLocallyBoundedMixedPshOn P.domain (correctedReal P) :=
  fun i => correctedReal_isLocallyBoundedPshOn (hb i) P

/-- **The coordinate limit measure of a bounded patch is its bounded mixed
Bedford–Taylor measure.** No truncation survives in the limit. -/
theorem mixedTruncationLimitMeasure_corrected (hb : ∀ i, IsBoundedPotential (u i))
    (P : Patch θ u) :
    mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic =
      canonicalMixedBedfordTaylorMeasure P.domain (correctedReal P)
        (correctedReal_isLocallyBoundedMixedPshOn hb P) :=
  mixedTruncationLimitMeasure_eq_canonical_of_eqOn
    (correctedReal_isLocallyBoundedMixedPshOn hb P) P.plurisubharmonic
    (fun i _ _ => (coe_correctedReal (hb i) P _).symm)

/-- **The BEGZ patch mass condition holds unconditionally for bounded
potentials.** The compact Kähler theorem is not used. -/
theorem hasPatchTruncationMass_of_bounded (hb : ∀ i, IsBoundedPotential (u i)) :
    HasPatchTruncationMass θ u := fun P =>
  hasUniformCompactMixedTruncationMass_of_eqOn
    (correctedReal_isLocallyBoundedMixedPshOn hb P) P.plurisubharmonic
    (fun i _ _ => (coe_correctedReal (hb i) P _).symm)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The glued global measure of a bounded tuple identifies, on each patch, with
the transported bounded mixed Bedford–Taylor measure. -/
theorem globalMixedMeasure_restrict_patch_eq_canonical
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (hb : ∀ i, IsBoundedPotential (u i))
    (P : Patch θ u) :
    (globalMixedMeasure θ u hu).restrict (P.source : Set M) =
      P.pushMeasure (canonicalMixedBedfordTaylorMeasure P.domain (correctedReal P)
        (correctedReal_isLocallyBoundedMixedPshOn hb P)) := by
  rw [globalMixedMeasure_restrict_patch hu P]
  exact congrArg P.pushMeasure (mixedTruncationLimitMeasure_corrected hb P)

/-- **The global bounded mixed product is locally finite**, with no Kähler
background: the patch mass condition is the bounded one. -/
theorem globalMixedMeasure_isLocallyFiniteMeasure_of_bounded
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (hb : ∀ i, IsBoundedPotential (u i)) :
    IsLocallyFiniteMeasure (globalMixedMeasure θ u hu) :=
  globalMixedMeasure_isLocallyFiniteMeasure_of_patchMass hu
    (hasPatchTruncationMass_of_bounded hb)

/-- **The global bounded mixed product has finite total mass** on a compact
complex manifold. -/
theorem globalMixedMeasure_isFiniteMeasure_of_bounded
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (hb : ∀ i, IsBoundedPotential (u i)) :
    IsFiniteMeasure (globalMixedMeasure θ u hu) :=
  globalMixedMeasure_isFiniteMeasure_of_patchMass hu (hasPatchTruncationMass_of_bounded hb)

theorem globalMixedMeasure_apply_lt_top_of_bounded
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (hb : ∀ i, IsBoundedPotential (u i))
    (S : Set M) : globalMixedMeasure θ u hu S < ⊤ :=
  globalMixedMeasure_apply_lt_top_of_patchMass hu (hasPatchTruncationMass_of_bounded hb) S

end

end SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
