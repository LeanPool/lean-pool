/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalSlotStokes
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedTruncationMaxLocality

/-!
# Plurifine locality of the maximum for global mixed measures

For raw `θ`-PSH tuples `u` and `w` whose slotwise maximum is again `θ`-PSH, the
global mixed non-pluripolar measure of `max (u i) (w i)` agrees with that of `u`
on the set `{x | ∀ i, w i x < u i x}`.

On a patch of `u`, the same chart, coordinate domain and smooth potentials form a
patch of the maximum, whose corrected potentials are the slotwise maxima of the
corrected potentials of `u` and `w`; the local statement is
`MixedNonPluripolar.mixedTruncationLimitMeasure_restrict_max_eq`. Adding a real
potential does not change strict inequalities, so the coordinate set is the
chart image of the global one. Patches cover `M`.
-/

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.GlobalMaxLocality

open FirstPass FirstPass.GlobalPotentialPatches FirstPass.PositiveClasses
open MixedNonPluripolar GlobalNonPluripolar BoundedGlobalProduct GlobalSlotStokes

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  {θ : Fin n → ClosedRealOneOneForm n M}

/-- The patch of the maximum carried by a patch of `u`. -/
def maxPatch {u w : Fin n → M → EReal} (P : Patch θ u)
    (hmax : ∀ i, ThetaPlurisubharmonic (θ i).val (fun x => max (u i x) (w i x))) :
    Patch θ (fun i x => max (u i x) (w i x)) where
  chart := P.chart
  domain := P.domain
  domain_le_target := P.domain_le_target
  potential := P.potential
  localPotential := P.localPotential
  plurisubharmonic i :=
    BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn (hmax i) P.chart
      (P.localPotential i)

omit [CompactSpace M] in
theorem measurableSet_forall_lt {u w : Fin n → M → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (hw : ∀ i, ThetaPlurisubharmonic (θ i).val (w i)) :
    MeasurableSet {x | ∀ i, w i x < u i x} := by
  have : {x | ∀ i, w i x < u i x} = ⋂ i, {x | w i x < u i x} := by ext; simp
  rw [this]
  exact MeasurableSet.iInter fun i =>
    measurableSet_lt (hw i).quasiPlurisubharmonic.upperSemicontinuous.measurable
      (hu i).quasiPlurisubharmonic.upperSemicontinuous.measurable

/-- **Plurifine locality of the maximum.** The global mixed measure of the
slotwise maximum agrees with that of `u` where every obstacle lies strictly below
its slot. -/
theorem globalMixedMeasure_restrict_max_eq {u w : Fin n → M → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (hw : ∀ i, ThetaPlurisubharmonic (θ i).val (w i))
    (hmax : ∀ i, ThetaPlurisubharmonic (θ i).val (fun x => max (u i x) (w i x))) :
    (globalMixedMeasure θ (fun i x => max (u i x) (w i x)) hmax).restrict
        {x | ∀ i, w i x < u i x} =
      (globalMixedMeasure θ u hu).restrict {x | ∀ i, w i x < u i x} := by
  set S := {x | ∀ i, w i x < u i x} with hS
  have hSm : MeasurableSet S := measurableSet_forall_lt hu hw
  refine measure_eq_of_restrict_eq_of_openCover (fun P : Patch θ u => (P.source : Set M))
    (fun P => P.source.isOpen) (exists_patch_containing hu) fun P => ?_
  rw [Measure.restrict_comm P.source.isOpen.measurableSet,
    Measure.restrict_comm P.source.isOpen.measurableSet,
    globalMixedMeasure_restrict_patch hu P,
    show (P.source : Set M) = ((maxPatch P hmax).source : Set M) from rfl,
    globalMixedMeasure_restrict_patch hmax (maxPatch P hmax)]
  set Q := maxPatch P hmax
  have hwc (i : Fin n) : PlurisubharmonicOn
      (fun z => chartFunction (w i) P.chart z + (P.potential i z : EReal)) P.domain :=
    BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn (hw i) P.chart
      (P.localPotential i)
  have hmaxc : ∀ i, PlurisubharmonicOn (fun z => max (P.corrected i z)
      (chartFunction (w i) P.chart z + (P.potential i z : EReal))) P.domain := fun i =>
    (P.plurisubharmonic i).max (hwc i)
  have hQ : mixedTruncationLimitMeasure Q.domain Q.corrected Q.plurisubharmonic =
      mixedTruncationLimitMeasure P.domain (fun i z => max (P.corrected i z)
        (chartFunction (w i) P.chart z + (P.potential i z : EReal))) hmaxc := by
    apply mixedTruncationLimitMeasure_congr
    intro i z _
    simp only [Q, maxPatch, Patch.corrected, chartFunction]
    exact (max_add_add_right _ _ _).symm
  have hloc := mixedTruncationLimitMeasure_restrict_max_eq (u := P.corrected)
    P.plurisubharmonic hwc hmaxc
  ext t ht
  rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
  change Q.pushMeasure _ (t ∩ S) = P.pushMeasure _ (t ∩ S)
  rw [Q.pushMeasure_apply, P.pushMeasure_apply, hQ]
  change mixedTruncationLimitMeasure P.domain _ hmaxc
      ((P.domain : Set (ComplexModel n)) ∩ P.chart.val.symm ⁻¹' (t ∩ S)) = _
  set A := (P.domain : Set (ComplexModel n)) ∩ P.chart.val.symm ⁻¹' (t ∩ S)
  have hA : A ⊆ {z | z ∈ P.domain ∧ ∀ i,
      chartFunction (w i) P.chart z + (P.potential i z : EReal) < P.corrected i z} := by
    rintro z ⟨hz, -, hzS⟩
    exact ⟨hz, fun i => EReal.add_lt_add_right_coe (hzS i) _⟩
  rw [← Measure.restrict_eq_self _ hA, hloc, Measure.restrict_eq_self _ hA]

end

end SGPT.Foundations.Analysis.Pending.GlobalMaxLocality
