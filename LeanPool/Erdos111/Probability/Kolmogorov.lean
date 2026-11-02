/-
Copyright (c) 2026 Jacob Parish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Parish
-/

module

public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
public import Mathlib.MeasureTheory.OuterMeasure.OfAddContent

/-!
# Kolmogorov extension for Boolean coordinates

A consistent family of probability laws on the finite coordinate sets of `ι → Bool`
has a projective limit, for an arbitrary index type `ι`. The cylinders of `ι → Bool`
are compact and clopen, so the content of the family is σ-additive on the cylinder
algebra, and Carathéodory's construction extends it.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace Erdos111

/-- A measurable cylinder of `ι → Bool` is closed in the product topology. -/
theorem isClosed_of_mem_measurableCylinders {ι : Type*} {s : Set (ι → Bool)}
    (hs : s ∈ measurableCylinders (fun _ : ι => Bool)) : IsClosed s := by
  obtain ⟨J, S, -, rfl⟩ := (mem_measurableCylinders s).1 hs
  exact (isClosed_discrete S).preimage (continuous_pi fun i => continuous_apply _)

/-- Kolmogorov extension for Boolean coordinates. -/
theorem exists_isProjectiveLimit_bool {ι : Type*}
    (P : ∀ J : Finset ι, Measure (J → Bool)) [∀ J, IsProbabilityMeasure (P J)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : ι => Bool) P) :
    ∃ μ : Measure (ι → Bool), IsProbabilityMeasure μ ∧
      IsProjectiveLimit (α := fun _ : ι => Bool) μ P := by
  -- the content vanishes along decreasing cylinders with empty intersection
  have h_tendsto : ∀ ⦃s : ℕ → Set (ι → Bool)⦄,
      (∀ n, s n ∈ measurableCylinders (fun _ : ι => Bool)) → Antitone s → (⋂ n, s n) = ∅ →
        Tendsto (fun n => projectiveFamilyContent hP (s n)) atTop (𝓝 0) := by
    intro s hs hanti hinter
    obtain ⟨N, hN⟩ : ∃ N, s N = ∅ := by
      by_contra! h
      have := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed s
        (fun n => hanti (Nat.le_succ n)) h
        (isClosed_of_mem_measurableCylinders (hs 0)).isCompact
        (fun n => isClosed_of_mem_measurableCylinders (hs n))
      rw [hinter] at this
      exact Set.not_nonempty_empty this
    refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
    have : s n = ∅ := Set.subset_empty_iff.1 (hN ▸ hanti hn)
    rw [this, addContent_empty]
  have hσ : (projectiveFamilyContent hP).IsSigmaSubadditive := by
    refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
      isSetRing_measurableCylinders (fun f hf hf_Union hf' => ?_)
    exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
      (projectiveFamilyContent hP) (fun s hs => projectiveFamilyContent_ne_top _)
      h_tendsto hf hf_Union hf'
  let μ := (projectiveFamilyContent hP).measure isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.ge hσ
  have hμ : IsProjectiveLimit (α := fun _ : ι => Bool) μ P := by
    intro I
    ext s hs
    rw [Measure.map_apply (Finset.measurable_restrict I) hs, AddContent.measure_eq,
      ← cylinder, projectiveFamilyContent_cylinder hP hs]
    · exact generateFrom_measurableCylinders.symm
    · exact cylinder_mem_measurableCylinders _ _ hs
  refine ⟨μ, ⟨?_⟩, hμ⟩
  rw [← Set.preimage_univ (f := (∅ : Finset ι).restrict),
    ← Measure.map_apply (Finset.measurable_restrict _) .univ, hμ, measure_univ]

end Erdos111
