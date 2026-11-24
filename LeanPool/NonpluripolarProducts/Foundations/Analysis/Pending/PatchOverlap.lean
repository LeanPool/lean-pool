/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.NonPluripolarHolomorphic
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalPotentialPatches
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicMaps
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalPatchMeasures

/-!
# Overlap compatibility of coordinate non-pluripolar measures

For two local-potential patches `P` and `Q` the chart transition is a
biholomorphism between the coordinate images of the common source. The two
corrected potentials differ, after transport, by the difference of the smooth
local potentials, whose `ddᶜ` vanishes by the transformation law of the
background forms. Gauge invariance and holomorphic covariance of the mixed
truncation limit then identify the two coordinate measures on the overlap.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.PatchOverlap

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere FirstPass.MixedNonPluripolar
open FirstPass.GlobalPotentialPatches FirstPass.HolomorphicMaps
open MixedNonPluripolar BedfordTaylor

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}

variable (P Q : Patch θ u)

/-- The coordinate image in `P` of the common source. -/
def overlapDomain : Opens (ComplexModel n) :=
  ⟨(P.domain : Set (ComplexModel n)) ∩ P.chart.val.symm ⁻¹' Q.source,
    (P.chart.val.continuousOn_symm.mono P.domain_le_target).isOpen_inter_preimage
      P.domain.isOpen Q.source.isOpen⟩

/-- The transition from `P`-coordinates to `Q`-coordinates. -/
def transition : ComplexModel n → ComplexModel n := fun z ↦ Q.chart.val (P.chart.val.symm z)

theorem mem_overlapDomain {z : ComplexModel n} :
    z ∈ overlapDomain P Q ↔ z ∈ P.domain ∧ P.chart.val.symm z ∈ Q.source := Iff.rfl

theorem overlapDomain_le : overlapDomain P Q ≤ P.domain := fun _ hz ↦ hz.1

theorem transition_eq_chartTransition (z : ComplexModel n) :
    transition P Q z = chartTransition P.chart Q.chart z := rfl

theorem mem_chartTransition_source {z : ComplexModel n} (hz : z ∈ overlapDomain P Q) :
    z ∈ (chartTransition P.chart Q.chart).source := by
  exact ⟨P.domain_le_target hz.1, Q.source_subset hz.2⟩

theorem isBiholomorphicPair :
    IsBiholomorphicPair (overlapDomain P Q) (overlapDomain Q P) (transition P Q)
      (transition Q P) where
  holo := fun z hz ↦ (chartTransition_contDiffAt P.chart Q.chart
    (mem_chartTransition_source P Q hz)).contDiffWithinAt
  holo_inv := fun z hz ↦ (chartTransition_contDiffAt Q.chart P.chart
    (mem_chartTransition_source Q P hz)).contDiffWithinAt
  mapsTo := fun z hz ↦ by
    refine ⟨Q.map_source hz.2, ?_⟩
    change Q.chart.val.symm (Q.chart.val (P.chart.val.symm z)) ∈ P.source
    rw [Q.chart.val.left_inv (Q.source_subset hz.2)]
    exact P.map_target hz.1
  mapsTo_inv := fun w hw ↦ by
    refine ⟨P.map_source hw.2, ?_⟩
    change P.chart.val.symm (P.chart.val (Q.chart.val.symm w)) ∈ Q.source
    rw [P.chart.val.left_inv (P.source_subset hw.2)]
    exact Q.map_target hw.1
  left_inv := fun z hz ↦ by
    change P.chart.val (Q.chart.val.symm (Q.chart.val (P.chart.val.symm z))) = z
    rw [Q.chart.val.left_inv (Q.source_subset hz.2),
      P.chart.val.right_inv (P.domain_le_target hz.1)]
  right_inv := fun w hw ↦ by
    change Q.chart.val (P.chart.val.symm (P.chart.val (Q.chart.val.symm w))) = w
    rw [P.chart.val.left_inv (P.source_subset hw.2),
      Q.chart.val.right_inv (Q.domain_le_target hw.1)]

theorem transition_mapsTo_domain :
    MapsTo (transition P Q) (overlapDomain P Q) Q.domain := fun _ hz ↦
  ((isBiholomorphicPair P Q).mapsTo hz).1

/-- The transported difference of the local potentials has vanishing `ddᶜ`. -/
theorem isSmoothPluriharmonicOn_potential_sub (i : Fin n) :
    IsSmoothPluriharmonicOn (overlapDomain P Q)
      (fun z ↦ Q.potential i (transition P Q z) - P.potential i z) := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  set A := overlapDomain P Q
  have hτ : ContDiffOn ℂ ∞ (transition P Q) A := (isBiholomorphicPair P Q).holo
  have hτm := transition_mapsTo_domain P Q
  have hq : ContDiffOn ℝ ∞ (Q.potential i) Q.domain := (Q.localPotential i).2.2.1
  have hp : ContDiffOn ℝ ∞ (P.potential i) A :=
    (P.localPotential i).2.2.1.mono (overlapDomain_le P Q)
  have hqτ : ContDiffOn ℝ ∞ (fun z ↦ Q.potential i (transition P Q z)) A :=
    hq.comp (hτ.restrict_scalars ℝ) hτm
  refine ⟨hqτ.sub hp, fun z hz ↦ ?_⟩
  have hqτ2 : ContDiffAt ℝ 2 (fun z ↦ Q.potential i (transition P Q z)) z :=
    ((hqτ z hz).contDiffAt (A.isOpen.mem_nhds hz)).of_le h2
  have hp2 : ContDiffAt ℝ 2 (P.potential i) z := ((hp z hz).contDiffAt (A.isOpen.mem_nhds
    hz)).of_le h2
  have hDDC : smoothDDC (fun x ↦ Q.potential i (transition P Q x)) z =
      smoothDDC (P.potential i) z := by
    rw [HolomorphicDDC.smoothDDC_comp A.isOpen Q.domain.isOpen hτ hq hτm hz]
    ext v
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      (Q.localPotential i).2.2.2 (hτm hz), (P.localPotential i).2.2.2 hz.1]
    exact ((θ i).val.compatible P.chart Q.chart z (mem_chartTransition_source P Q hz) v).symm
  have hH : complexHessian (fun x ↦ Q.potential i (transition P Q x)) z =
      complexHessian (P.potential i) z := by
    rw [← normalizedHermitianMatrix_smoothDDC hqτ2, ← normalizedHermitianMatrix_smoothDDC hp2,
      hDDC]
  have hfun : (fun x ↦ Q.potential i (transition P Q x) - P.potential i x) =
      (fun x ↦ Q.potential i (transition P Q x)) + (-1 : ℝ) • P.potential i := by
    funext x; simp [sub_eq_add_neg]
  have hsm : ContDiffAt ℝ 2 ((-1 : ℝ) • P.potential i) z := hp2.const_smul (-1 : ℝ)
  rw [hfun, complexHessian_add hqτ2 hsm, complexHessian_smul hp2, hH]
  simp

theorem corrected_add_potential_sub (i : Fin n) {z : ComplexModel n} (hz : z ∈ overlapDomain P Q) :
    P.corrected i z + ((Q.potential i (transition P Q z) - P.potential i z : ℝ) : EReal) =
      Q.corrected i (transition P Q z) := by
  have hsymm : Q.chart.val.symm (transition P Q z) = P.chart.val.symm z :=
    Q.chart.val.left_inv (Q.source_subset hz.2)
  simp only [Patch.corrected, chartFunction, hsymm]
  rw [add_assoc, ← EReal.coe_add, add_sub_cancel]

theorem plurisubharmonicOn_corrected_comp (i : Fin n) :
    PlurisubharmonicOn (fun z ↦ Q.corrected i (transition P Q z)) (overlapDomain P Q) :=
  HolomorphicPullback.plurisubharmonicOn_comp_holomorphic (overlapDomain P Q).isOpen
    ((isBiholomorphicPair P Q).holo.differentiableOn (by simp))
    (isBiholomorphicPair P Q).mapsTo
    ((Q.plurisubharmonic i).mono (overlapDomain_le Q P))

/-- **Coordinate overlap compatibility.** -/
theorem mixedTruncationLimitMeasure_overlap :
    (mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic).restrict
        (overlapDomain P Q) =
      ((mixedTruncationLimitMeasure Q.domain Q.corrected Q.plurisubharmonic).restrict
        (overlapDomain Q P)).map (transition Q P) := by
  set A := overlapDomain P Q
  set B := overlapDomain Q P
  have hPA : ∀ i, PlurisubharmonicOn (P.corrected i) A := fun i ↦
    (P.plurisubharmonic i).mono (overlapDomain_le P Q)
  have hQB : ∀ i, PlurisubharmonicOn (Q.corrected i) B := fun i ↦
    (Q.plurisubharmonic i).mono (overlapDomain_le Q P)
  have heq (i : Fin n) : EqOn (fun z ↦ P.corrected i z +
      ((Q.potential i (transition P Q z) - P.potential i z : ℝ) : EReal))
      (fun z ↦ Q.corrected i (transition P Q z)) A := fun z hz ↦
    corrected_add_potential_sub P Q i hz
  have hvh : ∀ i, PlurisubharmonicOn (fun z ↦ P.corrected i z +
      ((Q.potential i (transition P Q z) - P.potential i z : ℝ) : EReal)) A := fun i z hz ↦
    (plurisubharmonicOn_corrected_comp P Q i z hz).congr
      (Filter.eventually_of_mem (A.isOpen.mem_nhds hz) fun y hy ↦ (heq i hy).symm)
  have hgauge := mixedTruncationLimitMeasure_add_pluriharmonic hPA
    (isSmoothPluriharmonicOn_potential_sub P Q) hvh
  have hcongr := mixedTruncationLimitMeasure_open_locality (Ω := A) le_rfl hvh
    (plurisubharmonicOn_corrected_comp P Q) heq
  have hself : (mixedTruncationLimitMeasure A _ hvh).restrict (A : Set (ComplexModel n)) =
      mixedTruncationLimitMeasure A _ hvh :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (mixedTruncationLimitMeasure_compl hvh))
  have hcov := mixedTruncationLimitMeasure_comp_biholomorphic (isBiholomorphicPair P Q) hQB
    (plurisubharmonicOn_corrected_comp P Q)
  have hrP := mixedTruncationLimitMeasure_restrict_open (u := P.corrected) (overlapDomain_le P Q)
    P.plurisubharmonic
  have hrQ := mixedTruncationLimitMeasure_restrict_open (u := Q.corrected) (overlapDomain_le Q P)
    Q.plurisubharmonic
  rw [hrP, ← hgauge, ← hself, hcongr, hcov, ← hrQ,
    Measure.restrict_restrict B.isOpen.measurableSet, inter_self]

section Manifold

variable [MeasurableSpace M] [BorelSpace M]

omit [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem measurableSet_inter_preimage {A : Opens (ComplexModel n)} {f : ComplexModel n → M}
    (hf : ContinuousOn f A) {s : Set M} (hs : MeasurableSet s) :
    MeasurableSet ((A : Set (ComplexModel n)) ∩ f ⁻¹' s) := by
  have hemb := MeasurableEmbedding.subtype_coe A.isOpen.measurableSet
  have hmeas : Measurable ((A : Set (ComplexModel n)).domRestrict f) :=
    (continuousOn_iff_continuous_domRestrict.mp hf).measurable
  have h := hemb.measurableSet_image.2 (hmeas hs)
  convert h using 1
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_image, Subtype.exists, exists_and_right,
    exists_eq_right]
  tauto

/-- **Transport of coordinate overlap compatibility to the manifold.** -/
theorem pushMeasure_restrict_inter_eq {μ ν : Measure (ComplexModel n)}
    (h : μ.restrict (overlapDomain P Q) =
      (ν.restrict (overlapDomain Q P)).map (transition Q P)) :
    (P.pushMeasure μ).restrict ((P.source : Set M) ∩ Q.source) =
      (Q.pushMeasure ν).restrict ((P.source : Set M) ∩ Q.source) := by
  ext s hs
  have hO : MeasurableSet ((P.source : Set M) ∩ Q.source) :=
    P.source.isOpen.measurableSet.inter Q.source.isOpen.measurableSet
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs, Patch.pushMeasure_apply,
    Patch.pushMeasure_apply]
  set A := overlapDomain P Q
  set B := overlapDomain Q P
  have hpairs := isBiholomorphicPair P Q
  have hPcont : ContinuousOn P.chart.val.symm A :=
    P.chart.val.continuousOn_symm.mono fun z hz ↦ P.domain_le_target hz.1
  set t := (A : Set (ComplexModel n)) ∩ P.chart.val.symm ⁻¹' s
  have ht : MeasurableSet t := measurableSet_inter_preimage hPcont hs
  have hLt : (P.domain : Set (ComplexModel n)) ∩ P.chart.val.symm ⁻¹' (s ∩ (P.source ∩ Q.source)) =
      t := by
    ext z
    simp only [t, A, mem_inter_iff, mem_preimage, overlapDomain, Opens.mem_mk, SetLike.mem_coe]
    constructor
    · rintro ⟨hz, hs', -, hQ⟩
      exact ⟨⟨hz, hQ⟩, hs'⟩
    · rintro ⟨⟨hz, hQ⟩, hs'⟩
      exact ⟨hz, hs', P.map_target hz, hQ⟩
  have hσm : AEMeasurable (transition Q P) (ν.restrict B) :=
    hpairs.holo_inv.continuousOn.aemeasurable B.isOpen.measurableSet
  have hRt : transition Q P ⁻¹' t ∩ B =
      (Q.domain : Set (ComplexModel n)) ∩ Q.chart.val.symm ⁻¹' (s ∩ (P.source ∩ Q.source)) := by
    ext w
    simp only [t, A, B, mem_inter_iff, mem_preimage, overlapDomain, Opens.mem_mk,
      SetLike.mem_coe]
    constructor
    · rintro ⟨⟨-, hs'⟩, hw, hP⟩
      have hback : P.chart.val.symm (transition Q P w) = Q.chart.val.symm w :=
        P.chart.val.left_inv (P.source_subset hP)
      rw [hback] at hs'
      exact ⟨hw, hs', hP, Q.map_target hw⟩
    · rintro ⟨hw, hs', hP, -⟩
      have hback : P.chart.val.symm (transition Q P w) = Q.chart.val.symm w :=
        P.chart.val.left_inv (P.source_subset hP)
      exact ⟨⟨hpairs.mapsTo_inv ⟨hw, hP⟩, by rw [hback]; exact hs'⟩, hw, hP⟩
  rw [hLt, ← hRt, ← Measure.restrict_apply' B.isOpen.measurableSet,
    ← Measure.map_apply_of_aemeasurable hσm ht, ← h,
    Measure.restrict_apply' A.isOpen.measurableSet, inter_eq_left.2 inter_subset_left]

end Manifold

end SGPT.Foundations.Analysis.Pending.PatchOverlap
