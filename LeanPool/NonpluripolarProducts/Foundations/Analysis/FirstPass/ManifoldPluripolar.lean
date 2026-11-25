/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalPotentials
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PluripolarSets

/-!
# Pluripolar exceptional sets on complex manifolds

Every atlas chart must have actual local nontrivial PSH witnesses for the
coordinate exceptional set. This is not a measure-zero definition. We make
quasi-everywhere predicates and equality available without assuming that a
non-pluripolar product exists. Local Haar nullity is proved separately; a
global measure is only said not to charge these sets when it really has that
property. Finite-union closure and the quasi-PSH pole-set theorem remain in
Pending, and are not imported here.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.FirstPass

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

/-- The portion of a subset visible in a chart, with the target retained. -/
noncomputable def pluripolarChartSet (S : Set M) (e : ComplexChart n M) : Set (ComplexModel n) :=
  e.val.target ∩ e.val.symm ⁻¹' S

/-- Local PSH pole witnesses in every holomorphic atlas chart. -/
def ManifoldLocallyPluripolar (S : Set M) : Prop :=
  ∀ e : ComplexChart n M,
    LocallyPluripolarOn (pluripolarChartSet S e) e.val.target

variable [IsComplexManifold n M]

omit [IsComplexManifold n M] in
theorem ManifoldLocallyPluripolar.mono {S T : Set M}
    (hS : ManifoldLocallyPluripolar (n := n) S) (hTS : T ⊆ S) :
    ManifoldLocallyPluripolar (n := n) T := by
  intro e
  exact (hS e).mono_set (fun _ hz => ⟨hz.1, hTS hz.2⟩)

private theorem model_locallyPluripolarOn_empty (n : ℕ) (U : Set (ComplexModel n)) :
    LocallyPluripolarOn (∅ : Set (ComplexModel n)) U := by
  intro x _
  refine ⟨univ, (fun _ => ((0 : ℝ) : EReal)), isOpen_univ, mem_univ x,
    isPreconnected_univ, ?_, ?_, ?_⟩
  · exact fun z _ => plurisubharmonicAt_const 0 (EReal.coe_ne_top 0) z
  · exact ⟨0, mem_univ 0, EReal.coe_ne_bot 0⟩
  · exact fun _ _ hy => False.elim hy

omit [IsComplexManifold n M] in
theorem manifoldLocallyPluripolar_empty :
    ManifoldLocallyPluripolar (n := n) (∅ : Set M) := by
  intro e
  simpa only [pluripolarChartSet, preimage_empty, inter_empty] using
    model_locallyPluripolarOn_empty n e.val.target

/-- A property holds quasi-everywhere if its actual failure set is pluripolar. -/
def QuasiEverywhere (P : M → Prop) : Prop :=
  ManifoldLocallyPluripolar (n := n) {x | ¬ P x}

omit [IsComplexManifold n M] in
theorem QuasiEverywhere.mono {P Q : M → Prop}
    (hP : QuasiEverywhere (n := n) P) (hPQ : ∀ x, P x → Q x) :
    QuasiEverywhere (n := n) Q := by
  apply ManifoldLocallyPluripolar.mono hP
  intro x hx hPx
  exact hx (hPQ x hPx)

omit [IsComplexManifold n M] in
theorem quasiEverywhere_of_forall {P : M → Prop} (hP : ∀ x, P x) :
    QuasiEverywhere (n := n) P := by
  apply manifoldLocallyPluripolar_empty.mono
  intro x hx
  exact False.elim (hx (hP x))

/-- Quasi-everywhere equality keeps exceptional sets rather than identifying
all almost-everywhere representatives for an arbitrary measure. -/
def QuasiEverywhereEq {Y : Type*} (f g : M → Y) : Prop :=
  QuasiEverywhere (n := n) (fun x => f x = g x)

omit [IsComplexManifold n M] in
theorem QuasiEverywhereEq.refl {Y : Type*} (f : M → Y) :
    QuasiEverywhereEq (n := n) f f := quasiEverywhere_of_forall (fun _ => rfl)

omit [IsComplexManifold n M] in
theorem QuasiEverywhereEq.symm {Y : Type*} {f g : M → Y}
    (h : QuasiEverywhereEq (n := n) f g) : QuasiEverywhereEq (n := n) g f :=
  h.mono (fun _ hx => hx.symm)

omit [IsComplexManifold n M] in
theorem QuasiEverywhereEq.comp {Y Z : Type*} {f g : M → Y}
    (h : QuasiEverywhereEq (n := n) f g) (F : Y → Z) :
    QuasiEverywhereEq (n := n) (F ∘ f) (F ∘ g) :=
  h.mono (fun _ hx => congrArg F hx)

omit [IsComplexManifold n M] in
/-- Every coordinate exceptional set has Haar outer measure zero. There is
no measurability assumption on the exceptional set. -/
theorem ManifoldLocallyPluripolar.chart_measure_eq_zero {S : Set M}
    (hS : ManifoldLocallyPluripolar (n := n) S) (e : ComplexChart n M)
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure] :
    μ (pluripolarChartSet S e) = 0 := by
  have hsub : pluripolarChartSet S e ⊆ e.val.target := fun _ hz => hz.1
  simpa only [inter_eq_left.mpr hsub] using
    (hS e).measure_inter_eq_zero e.val.open_target μ

omit [IsComplexManifold n M] in
/-- A quasi-everywhere predicate holds Haar-almost-everywhere in each chart. -/
theorem QuasiEverywhere.ae_in_chart {P : M → Prop}
    (hP : QuasiEverywhere (n := n) P) (e : ComplexChart n M)
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure] :
    ∀ᵐ z ∂μ.restrict e.val.target, P (e.val.symm z) := by
  filter_upwards [(hP e).ae_notMem μ, ae_restrict_mem e.val.open_target.measurableSet]
    with z hz hzt
  exact not_not.mp (fun hn => hz ⟨hzt, hn⟩)

section Measures

variable [MeasurableSpace M]

/-- The actual noncharging property of a global measure; no product is
constructed or assumed by this definition. -/
def DoesNotChargeManifoldPluripolar (μ : Measure M) : Prop :=
  ∀ S : Set M, ManifoldLocallyPluripolar (n := n) S → μ S = 0

omit [IsComplexManifold n M] in
theorem DoesNotChargeManifoldPluripolar.ae_of_quasiEverywhere
    {μ : Measure M} (hμ : DoesNotChargeManifoldPluripolar (n := n) μ)
    {P : M → Prop} (hP : QuasiEverywhere (n := n) P) : ∀ᵐ x ∂μ, P x :=
  ae_iff.mpr (hμ _ hP)

omit [IsComplexManifold n M] in
theorem DoesNotChargeManifoldPluripolar.ae_eq_of_quasiEverywhereEq
    {μ : Measure M} (hμ : DoesNotChargeManifoldPluripolar (n := n) μ)
    {Y : Type*} {f g : M → Y} (hfg : QuasiEverywhereEq (n := n) f g) : f =ᵐ[μ] g :=
  hμ.ae_of_quasiEverywhere hfg

end Measures

end SGPT.Foundations.Analysis.FirstPass
