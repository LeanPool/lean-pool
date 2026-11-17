/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import Mathlib.Probability.Independence.Basic

/-!
# Independence along a measure-preserving map

If `h : α → β` is measure preserving from `μa` to `μb`, then independence transports
backwards along `h`: independent sub-σ-algebras of `β` have independent comaps in `α`,
and independent random variables on `β` stay independent after pre-composition with `h`.

## Main statements

* `indep_comap_of_measurePreserving` — for two sub-σ-algebras;
* `indepFun_comp_of_measurePreserving` — for a pair of random variables;
* `iIndepFun_comp_of_measurePreserving` — for a family of random variables.
-/

@[expose] public section

open MeasureTheory

namespace LevyStochCalc.Probability

variable {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
  {μa : Measure α} {μb : Measure β} {h : α → β}

/-- Independence of two sub-σ-algebras of `β` transports to their comaps in `α`
along a measure-preserving map `h : α → β`. -/
theorem indep_comap_of_measurePreserving (hmp : MeasurePreserving h μa μb)
    {m₁ m₂ : MeasurableSpace β} (hm₁ : m₁ ≤ mβ) (hm₂ : m₂ ≤ mβ)
    (hindep : ProbabilityTheory.Indep m₁ m₂ μb) :
    ProbabilityTheory.Indep (m₁.comap h) (m₂.comap h) μa := by
  have h_aux : ∀ s : Set β, @MeasurableSet β mβ s → μa (h ⁻¹' s) = μb s := fun s hs =>
    @MeasurePreserving.measure_preimage α β mα mβ μa μb h hmp s
      (@MeasurableSet.nullMeasurableSet β mβ μb s hs)
  rw [ProbabilityTheory.Indep_iff]
  rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
  have hu' : @MeasurableSet β mβ u := hm₁ _ hu
  have hv' : @MeasurableSet β mβ v := hm₂ _ hv
  rw [show h ⁻¹' u ∩ h ⁻¹' v = h ⁻¹' (u ∩ v) from rfl,
    h_aux _ (@MeasurableSet.inter β mβ _ _ hu' hv'), h_aux _ hu', h_aux _ hv']
  exact (ProbabilityTheory.Indep_iff _ _ _).1 hindep u v hu hv

/-- `IndepFun` is preserved by pre-composition with a measure-preserving map. -/
theorem indepFun_comp_of_measurePreserving {γ δ : Type*} [MeasurableSpace γ]
    [MeasurableSpace δ] {f : β → γ} {g : β → δ} (hf : Measurable f) (hg : Measurable g)
    (hindep : ProbabilityTheory.IndepFun f g μb) (hmp : MeasurePreserving h μa μb) :
    ProbabilityTheory.IndepFun (f ∘ h) (g ∘ h) μa := by
  rw [ProbabilityTheory.IndepFun_iff]
  rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  have hfs : MeasurableSet (f ⁻¹' s) := hf hs
  have hgt : MeasurableSet (g ⁻¹' t) := hg ht
  change μa (h ⁻¹' (f ⁻¹' s) ∩ h ⁻¹' (g ⁻¹' t))
    = μa (h ⁻¹' (f ⁻¹' s)) * μa (h ⁻¹' (g ⁻¹' t))
  rw [← Set.preimage_inter, hmp.measure_preimage (hfs.inter hgt).nullMeasurableSet,
    hmp.measure_preimage hfs.nullMeasurableSet, hmp.measure_preimage hgt.nullMeasurableSet]
  exact (ProbabilityTheory.IndepFun_iff _ _ _).1 hindep _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩

/-- `iIndepFun` is preserved by pre-composition with a measure-preserving map. -/
theorem iIndepFun_comp_of_measurePreserving {ι : Type*} {γ : ι → Type*}
    [∀ i, MeasurableSpace (γ i)] {f : ∀ i, β → γ i} (hf : ∀ i, Measurable (f i))
    (hindep : ProbabilityTheory.iIndepFun f μb) (hmp : MeasurePreserving h μa μb) :
    ProbabilityTheory.iIndepFun (fun i => f i ∘ h) μa := by
  have hindep' := ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.1 hindep
  refine ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.2 ?_
  intro S sets h_sets
  have h_meas : ∀ i ∈ S, MeasurableSet (f i ⁻¹' sets i) := fun i hi => hf i (h_sets i hi)
  have h_inter : MeasurableSet (⋂ i ∈ S, f i ⁻¹' sets i) :=
    MeasurableSet.biInter S.countable_toSet h_meas
  have h_pre : ⋂ i ∈ S, (f i ∘ h) ⁻¹' sets i = h ⁻¹' ⋂ i ∈ S, f i ⁻¹' sets i := by
    simp only [Set.preimage_iInter]
    rfl
  rw [h_pre, hmp.measure_preimage h_inter.nullMeasurableSet]
  have h_each : ∀ i ∈ S, μa ((f i ∘ h) ⁻¹' sets i) = μb (f i ⁻¹' sets i) := fun i hi =>
    hmp.measure_preimage (h_meas i hi).nullMeasurableSet
  rw [Finset.prod_congr rfl h_each]
  exact hindep' S h_sets

end LevyStochCalc.Probability
