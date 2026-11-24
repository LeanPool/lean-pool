/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalMaxLocality
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalNonPluripolarKahler

/-!
# One-slot locality and the comparison principle for global mixed measures

Fix a tuple `x` of raw `θ`-PSH potentials and a slot `i₀`, and write `μ(c)` for the
global mixed measure of the tuple with `c` in slot `i₀`.

* Pole sets carry no mass: `μ {p | u i p = ⊥} = 0` for every slot, by construction
  of the coordinate truncation limits.
* **Slot locality of the maximum**: `μ(max a c) = μ(a)` on `{c < a}`.
* **Comparison principle**: if all bounded values of slot `i₀` give the same total
  mass, then `μ(d) {c < d} ≤ μ(c) {c ≤ d}` for bounded `c`, `d`. Indeed
  `μ(max c d)` restricts to `μ(d)` on `{c < d}` and to `μ(c)` on `{d < c}`, and all
  three total masses agree.
-/

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.GlobalSlotComparison

open FirstPass FirstPass.GlobalPotentialPatches FirstPass.PositiveClasses
open MixedNonPluripolar GlobalNonPluripolar BoundedGlobalProduct GlobalSlotStokes
open GlobalMaxLocality UniformBoundedGlobalMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  {θ : Fin n → ClosedRealOneOneForm n M}

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The constant `⊥` is raw `θ`-PSH for every background. -/
theorem thetaPlurisubharmonic_bot (a : SmoothRealForm n M 2)
    (ha : HasSmoothLocalPotentials a) : ThetaPlurisubharmonic a (fun _ => (⊥ : EReal)) := by
  intro e z hz
  obtain ⟨W, ρ, hzW, hρ⟩ := ha e z hz
  refine ⟨W, ρ, hzW, hρ, fun y _ => ?_⟩
  simpa [chartFunction] using plurisubharmonicAt_const (⊥ : EReal) (by simp) y

/-- **Pole sets are null** for the global mixed measure. -/
theorem globalMixedMeasure_pole_null {u : Fin n → M → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (i : Fin n) :
    globalMixedMeasure θ u hu {p | u i p = ⊥} = 0 := by
  set E := {p | u i p = ⊥} with hE
  have hEm : MeasurableSet E :=
    measurableSet_eq_fun (hu i).quasiPlurisubharmonic.upperSemicontinuous.measurable
      measurable_const
  have hzero : (globalMixedMeasure θ u hu).restrict E = 0 := by
    refine measure_eq_of_restrict_eq_of_openCover (fun P : Patch θ u => (P.source : Set M))
      (fun P => P.source.isOpen) (exists_patch_containing hu) fun P => ?_
    rw [Measure.restrict_comm P.source.isOpen.measurableSet,
      globalMixedMeasure_restrict_patch hu P, Measure.restrict_zero]
    ext t ht
    rw [Measure.restrict_apply ht, FunLike.coe_zero, Pi.zero_apply, patchMeasure,
      P.pushMeasure_apply]
    apply measure_mono_null _ (mixedTruncationLimitMeasure_poleSet P.plurisubharmonic)
    rintro z ⟨-, -, hz⟩
    exact ⟨i, by simp [chartFunction, show u i _ = ⊥ from hz]⟩
  have := congrArg (fun ν : Measure M => ν univ) hzero
  simpa [Measure.restrict_apply MeasurableSet.univ] using this

/-- **Slot locality of the maximum.** -/
theorem globalMixedMeasure_update_max_restrict (x : Fin n → M → EReal) (i₀ : Fin n)
    {a c : M → EReal}
    (hxa : ∀ i, ThetaPlurisubharmonic (θ i).val (Function.update x i₀ a i))
    (hc : ThetaPlurisubharmonic (θ i₀).val c)
    (hxm : ∀ i, ThetaPlurisubharmonic (θ i).val
      (Function.update x i₀ (fun p => max (a p) (c p)) i)) :
    (globalMixedMeasure θ (Function.update x i₀ (fun p => max (a p) (c p))) hxm).restrict
        {p | c p < a p} =
      (globalMixedMeasure θ (Function.update x i₀ a) hxa).restrict {p | c p < a p} := by
  classical
  set w : Fin n → M → EReal := Function.update (fun _ _ => ⊥) i₀ c with hw
  have hwpsh : ∀ i, ThetaPlurisubharmonic (θ i).val (w i) := by
    intro i
    by_cases h : i = i₀
    · subst h; simpa [hw] using hc
    · simpa [hw, Function.update_of_ne h] using
        thetaPlurisubharmonic_bot _ (hxa i).hasSmoothLocalPotentials
  have htuple : (fun i p => max (Function.update x i₀ a i p) (w i p)) =
      Function.update x i₀ (fun p => max (a p) (c p)) := by
    funext i p
    by_cases h : i = i₀
    · subst h; simp [hw]
    · simp [hw, Function.update_of_ne h]
  have hloc := globalMixedMeasure_restrict_max_eq hxa hwpsh
    (fun i => BoundedGlobalProduct.ThetaPlurisubharmonic.max (hxa i) (hwpsh i))
  rw [globalMixedMeasure_congr_tuple htuple _ hxm] at hloc
  set S' := {p | ∀ i, w i p < Function.update x i₀ a i p} with hS'
  have hS'sub : S' ⊆ {p | c p < a p} := fun p hp => by simpa [hw] using hp i₀
  have hdiff : {p | c p < a p} \ S' ⊆ ⋃ i, {p | i ≠ i₀ ∧ x i p = ⊥} := by
    rintro p ⟨hp, hpS⟩
    simp only [hS', mem_ofPred_eq, not_forall] at hpS
    obtain ⟨i, hi⟩ := hpS
    refine mem_iUnion.mpr ⟨i, ?_⟩
    by_cases h : i = i₀
    · subst h; exact absurd (by simpa [hw] using hp) hi
    · exact ⟨h, by simpa [hw, Function.update_of_ne h] using hi⟩
  have hae (y : M → EReal)
      (hy : ∀ i, ThetaPlurisubharmonic (θ i).val (Function.update x i₀ y i)) :
      {p | c p < a p} =ᵐ[globalMixedMeasure θ (Function.update x i₀ y) hy] S' := by
    refine (ae_eq_set.mpr ⟨measure_mono_null hdiff (measure_iUnion_null fun i => ?_), ?_⟩)
    · by_cases h : i = i₀
      · simp [h]
      · refine measure_mono_null (fun p hp => ?_) (globalMixedMeasure_pole_null hy i)
        simpa [Function.update_of_ne h] using hp.2
    · rw [sdiff_eq_empty.mpr hS'sub, measure_empty]
  rw [Measure.restrict_congr_set (hae _ hxm), Measure.restrict_congr_set (hae _ hxa), hloc]

omit [CompactSpace M] in
theorem ThetaPlurisubharmonic.measurable {a : SmoothRealForm n M 2} {u : M → EReal}
    (hu : ThetaPlurisubharmonic a u) : Measurable u :=
  hu.quasiPlurisubharmonic.upperSemicontinuous.measurable

/-- **Comparison principle in one slot.** If the maximum `max c d` in slot `i₀`
has the same total mass as `c`, then `μ(d) {c < d} ≤ μ(c) {c ≤ d}`, provided
these masses are finite. -/
theorem globalMixedMeasure_comparison (omega : KahlerBackground n M)
    (x : Fin n → M → EReal) (i₀ : Fin n) {c d : M → EReal}
    (hxc : ∀ i, ThetaPlurisubharmonic (θ i).val (Function.update x i₀ c i))
    (hxd : ∀ i, ThetaPlurisubharmonic (θ i).val (Function.update x i₀ d i))
    (hxm : ∀ i, ThetaPlurisubharmonic (θ i).val
      (Function.update x i₀ (fun p => max (c p) (d p)) i))
    (hmass : globalMixedMeasure θ (Function.update x i₀ (fun p => max (c p) (d p))) hxm univ =
      globalMixedMeasure θ (Function.update x i₀ c) hxc univ) :
    globalMixedMeasure θ (Function.update x i₀ d) hxd {p | c p < d p} ≤
      globalMixedMeasure θ (Function.update x i₀ c) hxc {p | c p ≤ d p} := by
  classical
  have hc : ThetaPlurisubharmonic (θ i₀).val c := by simpa using hxc i₀
  have hd : ThetaPlurisubharmonic (θ i₀).val d := by simpa using hxd i₀
  have hm1 : MeasurableSet {p | c p < d p} :=
    measurableSet_lt (ThetaPlurisubharmonic.measurable hc) (ThetaPlurisubharmonic.measurable hd)
  have hm2 : MeasurableSet {p | d p < c p} :=
    measurableSet_lt (ThetaPlurisubharmonic.measurable hd) (ThetaPlurisubharmonic.measurable hc)
  set μm := globalMixedMeasure θ (Function.update x i₀ (fun p => max (c p) (d p))) hxm
  set μc := globalMixedMeasure θ (Function.update x i₀ c) hxc
  set μd := globalMixedMeasure θ (Function.update x i₀ d) hxd
  have htuple : Function.update x i₀ (fun p => max (d p) (c p)) =
      Function.update x i₀ (fun p => max (c p) (d p)) := by
    simp_rw [max_comm]
  have hxm' : ∀ i, ThetaPlurisubharmonic (θ i).val
      (Function.update x i₀ (fun p => max (d p) (c p)) i) := htuple ▸ hxm
  have e1 : μm {p | c p < d p} = μd {p | c p < d p} := by
    have h := globalMixedMeasure_update_max_restrict x i₀ hxd hc hxm'
    rw [globalMixedMeasure_congr_tuple htuple hxm' hxm] at h
    simpa [Measure.restrict_apply MeasurableSet.univ] using
      congrArg (fun ν : Measure M => ν univ) h
  have e2 : μm {p | d p < c p} = μc {p | d p < c p} := by
    have h := globalMixedMeasure_update_max_restrict x i₀ hxc hd hxm
    simpa [Measure.restrict_apply MeasurableSet.univ] using
      congrArg (fun ν : Measure M => ν univ) h
  have hdisj : Disjoint {p | c p < d p} {p | d p < c p} :=
    disjoint_left.mpr fun p (h1 : c p < d p) (h2 : d p < c p) => lt_asymm h1 h2
  have hle : μd {p | c p < d p} + μc {p | d p < c p} ≤
      μc {p | c p ≤ d p} + μc {p | d p < c p} := by
    calc μd {p | c p < d p} + μc {p | d p < c p}
        = μm ({p | c p < d p} ∪ {p | d p < c p}) := by
          rw [measure_union hdisj hm2, e1, e2]
      _ ≤ μm univ := measure_mono (subset_univ _)
      _ = μc univ := hmass
      _ = μc {p | c p ≤ d p} + μc {p | d p < c p} := by
          rw [← measure_union _ hm2, ← ofPred_or]
          · congr 1; ext p; simp [le_or_gt]
          · exact disjoint_left.mpr fun p (h1 : c p ≤ d p) (h2 : d p < c p) => not_lt.mpr h1 h2
  exact (ENNReal.add_le_add_iff_right
    (globalMixedMeasure_apply_lt_top omega hxc _).ne).mp hle

end

end SGPT.Foundations.Analysis.Pending.GlobalSlotComparison
