/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalSlotStokes
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BoundedGlobalTruncation
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedTruncationSlotLinear

/-!
# One-slot positive linearity of global mixed measures

Let `θ i₀ = s • α + r • β` with `s, r > 0`. For raw quasi-PSH tuples that differ
only in slot `i₀`, where the slots are `a`, `b` and `s a + r b`, the global mixed
non-pluripolar measure of the combined tuple is
`s • (a-tuple measure) + r • (b-tuple measure)`, provided the pole set of `a` is
not charged by the `b`-tuple measure and symmetrically.

Locally, a chart domain carrying smooth potentials `ρ j` of `θ j` (`j ≠ i₀`) and
`gα`, `gβ` of `α`, `β` gives patches of all three tuples with the same chart and
domain; the potential of `θ i₀` is `s gα + r gβ`. The corrected tuples are exactly
those of `MixedNonPluripolar.mixedTruncationLimitMeasure_update_add_smul`. Such
common chart data cover the manifold, and all three measures are evaluated
through the same inverse chart.
-/

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.GlobalSlotLinear

open FirstPass FirstPass.GlobalPotentialPatches FirstPass.PositiveClasses
open MixedNonPluripolar GlobalNonPluripolar BoundedGlobalProduct GlobalSlotStokes

noncomputable section

/-- Positive linear combinations commute with adding real corrections, including
the pole value `⊥` and the value `⊤`. -/
theorem ereal_linear_add_coe {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (x y : EReal) (g h : ℝ) :
    (s : EReal) * x + (r : EReal) * y + ((s * g + r * h : ℝ) : EReal) =
      (s : EReal) * (x + g) + (r : EReal) * (y + h) := by
  induction x using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos hs]
  | top =>
    induction y using EReal.rec with
    | bot => simp [EReal.coe_mul_bot_of_pos hr, EReal.coe_mul_top_of_pos hs]
    | top =>
      simp only [EReal.coe_mul_top_of_pos hr, EReal.coe_mul_top_of_pos hs, EReal.top_add_coe,
        EReal.top_add_top]
    | coe y =>
      simp only [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_mul_top_of_pos hs,
        EReal.top_add_coe]
  | coe x =>
    induction y using EReal.rec with
    | bot => simp [EReal.coe_mul_bot_of_pos hr]
    | top =>
      rw [EReal.top_add_coe, EReal.coe_mul_top_of_pos hr, EReal.add_top_of_ne_bot,
        EReal.add_top_of_ne_bot, EReal.top_add_coe]
      · exact EReal.coe_ne_bot _
      · exact EReal.coe_ne_bot _
    | coe y =>
      rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
        ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul,
        ← EReal.coe_add]
      congr 1
      ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Potentials of `θ i` on a common domain, together with a raw `θ`-PSH tuple,
give a patch. -/
def patchOfPotentials {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (e : ComplexChart n M)
    (D : Opens (ComplexModel n)) (hD : (D : Set (ComplexModel n)) ⊆ e.val.target)
    (ρ : Fin n → ComplexModel n → ℝ)
    (hρ : ∀ i, IsSmoothLocalPotential (θ i).val e D (ρ i)) : Patch θ u where
  chart := e
  domain := D
  domain_le_target := hD
  potential := ρ
  localPotential := hρ
  plurisubharmonic i :=
    BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn (hu i) e (hρ i)

/-- Common chart data for the three tuples: potentials of `θ j` for `j ≠ i₀` and
potentials of `α` and `β`. -/
structure SlotData (θ : Fin n → ClosedRealOneOneForm n M) (i₀ : Fin n)
    (α β : ClosedRealOneOneForm n M) where
  /-- The chart for comparing the three tuples. -/
  chart : ComplexChart n M
  /-- The common domain of the coordinate potentials. -/
  domain : Opens (ComplexModel n)
  domain_le_target : (domain : Set (ComplexModel n)) ⊆ chart.val.target
  /-- The background potentials at slots other than the selected one. -/
  potential : Fin n → ComplexModel n → ℝ
  localPotential : ∀ i, i ≠ i₀ →
    IsSmoothLocalPotential (θ i).val chart domain (potential i)
  /-- The local potential of the first form at the selected slot. -/
  potα : ComplexModel n → ℝ
  /-- The local potential of the second form at the selected slot. -/
  potβ : ComplexModel n → ℝ
  localα : IsSmoothLocalPotential α.val chart domain potα
  localβ : IsSmoothLocalPotential β.val chart domain potβ

namespace SlotData

variable {θ : Fin n → ClosedRealOneOneForm n M} {i₀ : Fin n} {α β : ClosedRealOneOneForm n M}

/-- The manifold neighborhood of the common coordinate domain. -/
def source (D : SlotData θ i₀ α β) : Set M :=
  D.chart.val.source ∩ D.chart.val ⁻¹' D.domain

theorem isOpen_source (D : SlotData θ i₀ α β) : IsOpen D.source :=
  D.chart.val.isOpen_inter_preimage D.domain.isOpen

theorem localPotential_update (D : SlotData θ i₀ α β) {γ : ClosedRealOneOneForm n M}
    {g : ComplexModel n → ℝ} (hg : IsSmoothLocalPotential γ.val D.chart D.domain g)
    (i : Fin n) :
    IsSmoothLocalPotential (Function.update θ i₀ γ i).val D.chart D.domain
      (Function.update D.potential i₀ g i) := by
  by_cases hi : i = i₀
  · subst hi
    simpa only [Function.update_self] using hg
  · simpa only [Function.update_of_ne hi] using D.localPotential i hi

theorem localPotential_combined (D : SlotData θ i₀ α β) {s r : ℝ}
    (hθ : θ i₀ = s • α + r • β) :
    IsSmoothLocalPotential (θ i₀).val D.chart D.domain
      (fun z => s * D.potα z + r * D.potβ z) := by
  have hU := D.localα.1
  have hsα : ContDiffOn ℝ ∞ (fun z => s • D.potα z) D.domain := D.localα.2.2.1.const_smul s
  have hrβ : ContDiffOn ℝ ∞ (fun z => r • D.potβ z) D.domain := D.localβ.2.2.1.const_smul r
  refine ⟨hU, D.localα.2.1, hsα.add hrβ, ?_⟩
  intro z hz
  change smoothDDC (fun y => s • D.potα y + r • D.potβ y) z = _
  rw [smoothDDC_add hU hsα hrβ hz, smoothDDC_smul hU D.localα.2.2.1 s hz,
    smoothDDC_smul hU D.localβ.2.2.1 r hz, D.localα.2.2.2 hz, D.localβ.2.2.2 hz, hθ,
    ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ClosedRealOneOneForm.coeff_smul]

theorem localPotential_update_combined (D : SlotData θ i₀ α β) {s r : ℝ}
    (hθ : θ i₀ = s • α + r • β) (i : Fin n) :
    IsSmoothLocalPotential (θ i).val D.chart D.domain
      (Function.update D.potential i₀ (fun z => s * D.potα z + r * D.potβ z) i) := by
  by_cases hi : i = i₀
  · subst hi
    simpa only [Function.update_self] using D.localPotential_combined hθ
  · simpa only [Function.update_of_ne hi] using D.localPotential i hi

/-- Common chart data exist around every point. -/
theorem exists_mem_source {x : Fin n → M → EReal} {a b : M → EReal}
    (ha : ∀ i, ThetaPlurisubharmonic (Function.update θ i₀ α i).val
      (Function.update x i₀ a i))
    (hb : ∀ i, ThetaPlurisubharmonic (Function.update θ i₀ β i).val
      (Function.update x i₀ b i))
    (p : M) : ∃ D : SlotData θ i₀ α β, p ∈ D.source := by
  let e := complexChartAt (n := n) p
  have hp : p ∈ e.val.source := mem_complexChartAt_source p
  obtain ⟨Pa, hPa, hza⟩ := exists_patch_in_chart ha e (e.val.map_source hp)
  obtain ⟨Pb, hPb, hzb⟩ := exists_patch_in_chart hb e (e.val.map_source hp)
  let V : Opens (ComplexModel n) := Pa.domain ⊓ Pb.domain
  have hVa : (V : Set (ComplexModel n)) ⊆ Pa.domain := inter_subset_left
  have hVb : (V : Set (ComplexModel n)) ⊆ Pb.domain := inter_subset_right
  have hla (i : Fin n) : IsSmoothLocalPotential (Function.update θ i₀ α i).val e V
      (Pa.potential i) := by
    have := (Pa.localPotential i).mono V.isOpen hVa
    rwa [hPa] at this
  have hlb (i : Fin n) : IsSmoothLocalPotential (Function.update θ i₀ β i).val e V
      (Pb.potential i) := by
    have := (Pb.localPotential i).mono V.isOpen hVb
    rwa [hPb] at this
  refine ⟨{
    chart := e
    domain := V
    domain_le_target := fun z hz => hPa ▸ Pa.domain_le_target (hVa hz)
    potential := Pa.potential
    localPotential := fun i hi => by simpa only [Function.update_of_ne hi] using hla i
    potα := Pa.potential i₀
    potβ := Pb.potential i₀
    localα := by simpa only [Function.update_self] using hla i₀
    localβ := by simpa only [Function.update_self] using hlb i₀ }, hp, ?_⟩
  exact ⟨hza, hzb⟩

end SlotData

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **One-slot positive linearity of global mixed measures.** -/
theorem globalMixedMeasure_update_add_smul {θ : Fin n → ClosedRealOneOneForm n M}
    (i₀ : Fin n) {α β : ClosedRealOneOneForm n M} {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hθ : θ i₀ = s • α + r • β) {x : Fin n → M → EReal} {a b : M → EReal}
    (hc : ∀ i, ThetaPlurisubharmonic (θ i).val
      (Function.update x i₀ (fun p => (s : EReal) * a p + (r : EReal) * b p) i))
    (ha : ∀ i, ThetaPlurisubharmonic (Function.update θ i₀ α i).val
      (Function.update x i₀ a i))
    (hb : ∀ i, ThetaPlurisubharmonic (Function.update θ i₀ β i).val
      (Function.update x i₀ b i))
    (hpa : globalMixedMeasure (Function.update θ i₀ β) (Function.update x i₀ b) hb
      {p | a p = ⊥} = 0)
    (hpb : globalMixedMeasure (Function.update θ i₀ α) (Function.update x i₀ a) ha
      {p | b p = ⊥} = 0) :
    globalMixedMeasure θ
        (Function.update x i₀ (fun p => (s : EReal) * a p + (r : EReal) * b p)) hc =
      ENNReal.ofReal s •
          globalMixedMeasure (Function.update θ i₀ α) (Function.update x i₀ a) ha +
        ENNReal.ofReal r •
          globalMixedMeasure (Function.update θ i₀ β) (Function.update x i₀ b) hb := by
  refine measure_eq_of_restrict_eq_of_openCover (fun D : SlotData θ i₀ α β => D.source)
    (fun D => D.isOpen_source) (SlotData.exists_mem_source ha hb) fun D => ?_
  set Pa := patchOfPotentials ha D.chart D.domain D.domain_le_target
    (Function.update D.potential i₀ D.potα) (D.localPotential_update D.localα)
  set Pb := patchOfPotentials hb D.chart D.domain D.domain_le_target
    (Function.update D.potential i₀ D.potβ) (D.localPotential_update D.localβ)
  set Pc := patchOfPotentials hc D.chart D.domain D.domain_le_target
    (Function.update D.potential i₀ (fun z => s * D.potα z + r * D.potβ z))
    (D.localPotential_update_combined hθ)
  have eqa : (globalMixedMeasure _ _ ha).restrict D.source = patchMeasure Pa :=
    globalMixedMeasure_restrict_patch ha Pa
  have eqb : (globalMixedMeasure _ _ hb).restrict D.source = patchMeasure Pb :=
    globalMixedMeasure_restrict_patch hb Pb
  have eqc : (globalMixedMeasure _ _ hc).restrict D.source = patchMeasure Pc :=
    globalMixedMeasure_restrict_patch hc Pc
  rw [Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul, eqa, eqb, eqc]
  -- The local identity.
  set Ω := D.domain
  set a' := Pa.corrected i₀
  set b' := Pb.corrected i₀
  have hua : Function.update Pa.corrected i₀ a' = Pa.corrected := Function.update_eq_self _ _
  have hub : Function.update Pa.corrected i₀ b' = Pb.corrected := by
    funext i z
    by_cases hi : i = i₀
    · subst hi
      rw [Function.update_self]
    · rw [Function.update_of_ne hi]
      simp only [Pa, Pb, patchOfPotentials, Patch.corrected, Function.update_of_ne hi]
  have huc : Function.update Pa.corrected i₀ (fun z => (s : EReal) * a' z + (r : EReal) * b' z) =
      Pc.corrected := by
    funext i z
    by_cases hi : i = i₀
    · subst hi
      rw [Function.update_self]
      simp only [a', b', Pa, Pb, Pc, patchOfPotentials, Patch.corrected, chartFunction,
        Function.update_self]
      exact (ereal_linear_add_coe hs hr _ _ _ _).symm
    · rw [Function.update_of_ne hi]
      simp only [Pa, Pc, patchOfPotentials, Patch.corrected, Function.update_of_ne hi]
  have hla : ∀ i, PlurisubharmonicOn (Function.update Pa.corrected i₀ a' i) Ω := by
    rw [hua]; exact Pa.plurisubharmonic
  have hlb : ∀ i, PlurisubharmonicOn (Function.update Pa.corrected i₀ b' i) Ω := by
    rw [hub]; exact Pb.plurisubharmonic
  have hlc : ∀ i, PlurisubharmonicOn (Function.update Pa.corrected i₀
      (fun z => (s : EReal) * a' z + (r : EReal) * b' z) i) Ω := by
    rw [huc]; exact Pc.plurisubharmonic
  have hμa : mixedTruncationLimitMeasure Ω _ hla =
      mixedTruncationLimitMeasure Pa.domain Pa.corrected Pa.plurisubharmonic :=
    mixedTruncationLimitMeasure_congr _ _ fun i z _ => by rw [hua]
  have hμb : mixedTruncationLimitMeasure Ω _ hlb =
      mixedTruncationLimitMeasure Pb.domain Pb.corrected Pb.plurisubharmonic :=
    mixedTruncationLimitMeasure_congr _ _ fun i z _ => by rw [hub]
  have hμc : mixedTruncationLimitMeasure Ω _ hlc =
      mixedTruncationLimitMeasure Pc.domain Pc.corrected Pc.plurisubharmonic :=
    mixedTruncationLimitMeasure_congr _ _ fun i z _ => by rw [huc]
  -- Local pole hypotheses from the global ones.
  have hpole {γ : ClosedRealOneOneForm n M} {w : M → EReal}
      {P : Patch (Function.update θ i₀ γ) (Function.update x i₀ w)}
      (hw : ∀ i, ThetaPlurisubharmonic (Function.update θ i₀ γ i).val
        (Function.update x i₀ w i)) (hPe : P.chart = D.chart)
      {c : M → EReal} {cor : ComplexModel n → EReal}
      (hcor : ∀ z, cor z = ⊥ → c (D.chart.val.symm z) = ⊥)
      (hglob : globalMixedMeasure _ _ hw {p | c p = ⊥} = 0) :
      mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic
        {z | cor z = ⊥} = 0 := by
    have hP := globalMixedMeasure_restrict_patch hw P
    have h1 : patchMeasure P {p | c p = ⊥} = 0 := by
      rw [← hP]
      exact le_antisymm ((Measure.restrict_apply_le _ _).trans hglob.le) bot_le
    rw [patchMeasure, Patch.pushMeasure_apply] at h1
    refine measure_mono_null (t := ((P.domain : Set (ComplexModel n)) ∩
      P.chart.val.symm ⁻¹' {p | c p = ⊥}) ∪ (P.domain : Set (ComplexModel n))ᶜ) ?_
      (measure_union_null h1 (mixedTruncationLimitMeasure_compl _))
    intro z hz
    by_cases hzΩ : z ∈ (P.domain : Set (ComplexModel n))
    · exact Or.inl ⟨hzΩ, by rw [hPe]; exact hcor z hz⟩
    · exact Or.inr hzΩ
  have hpa' : mixedTruncationLimitMeasure Ω _ hlb {z | a' z = ⊥} = 0 := by
    rw [hμb]
    refine hpole hb rfl (fun z hz => ?_) hpa
    simpa [a', Pa, patchOfPotentials, Patch.corrected, chartFunction] using hz
  have hpb' : mixedTruncationLimitMeasure Ω _ hla {z | b' z = ⊥} = 0 := by
    rw [hμa]
    refine hpole ha rfl (fun z hz => ?_) hpb
    simpa [b', Pb, patchOfPotentials, Patch.corrected, chartFunction] using hz
  have hloc := mixedTruncationLimitMeasure_update_add_smul i₀ hs hr hlc hla hlb hpa' hpb'
  rw [hμa, hμb, hμc] at hloc
  ext t ht
  rw [add_apply, smul_apply, smul_apply, patchMeasure, patchMeasure,
    patchMeasure, Patch.pushMeasure_apply, Patch.pushMeasure_apply, Patch.pushMeasure_apply,
    hloc, add_apply, smul_apply, smul_apply]
  rfl

end

end SGPT.Foundations.Analysis.Pending.GlobalSlotLinear
