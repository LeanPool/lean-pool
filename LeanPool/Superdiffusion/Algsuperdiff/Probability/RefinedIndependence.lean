/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Probability.Independence.Basic

/-!
# RefinedIndependence

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Aggregate independence from independent pairs

The two local views of each shell may be dependent on the same shell, but are
independent at the prescribed spatial separation.  This file is the purely
measure-theoretic step which combines those within-shell independences with
mutual independence across shells.  It has no coefficient-field semantics.
-/

namespace Algsuperdiff.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- Split each index into its left and right local sigma-field. -/
def refinedSigma {ι : Type*} (a b : ι → MeasurableSpace Ω) :
    ι × Bool → MeasurableSpace Ω :=
  fun p => cond p.2 (b p.1) (a p.1)

private theorem meas_biInter_fiber [IsProbabilityMeasure μ] {ι : Type*}
    {a b : ι → MeasurableSpace Ω} (i : ι) (hab : Indep (a i) (b i) μ)
    {F : Finset (ι × Bool)} (hF : ∀ p ∈ F, p.1 = i) {g : ι × Bool → Set Ω}
    (hg : ∀ p ∈ F, MeasurableSet[refinedSigma a b p] (g p)) :
    μ (⋂ p ∈ F, g p) = ∏ p ∈ F, μ (g p) := by
  classical
  have hFsub : F ⊆ ({(i, false), (i, true)} : Finset (ι × Bool)) := by
    intro p hp
    obtain ⟨p1, p2⟩ := p
    have hp1 : p1 = i := hF _ hp
    subst hp1
    cases p2 <;> simp
  by_cases hu : (i, false) ∈ F <;> by_cases hv : (i, true) ∈ F
  · have hFeq : F = ({(i, false), (i, true)} : Finset (ι × Bool)) := by
      apply Finset.Subset.antisymm hFsub
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with h | h <;> subst h <;> assumption
    subst hFeq
    have hne : (i, false) ≠ (i, true) := by simp
    rw [Finset.prod_insert (Finset.notMem_singleton.mpr hne), Finset.prod_singleton,
      Finset.set_biInter_insert, Finset.set_biInter_singleton]
    have h1 : MeasurableSet[a i] (g (i, false)) := hg (i, false) hu
    have h2 : MeasurableSet[b i] (g (i, true)) := hg (i, true) hv
    exact (Indep_iff (a i) (b i) μ).1 hab _ _ h1 h2
  · have hFeq : F = ({(i, false)} : Finset (ι × Bool)) := by
      apply Finset.Subset.antisymm _ (by simpa using hu)
      intro p hp
      have hsub := hFsub hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsub ⊢
      rcases hsub with h | h
      · exact h
      · exact absurd (h ▸ hp) hv
    subst hFeq
    simp
  · have hFeq : F = ({(i, true)} : Finset (ι × Bool)) := by
      apply Finset.Subset.antisymm _ (by simpa using hv)
      intro p hp
      have hsub := hFsub hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsub ⊢
      rcases hsub with h | h
      · exact absurd (h ▸ hp) hu
      · exact h
    subst hFeq
    simp
  · have hFeq : F = (∅ : Finset (ι × Bool)) := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      have hsub := hFsub hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsub
      rcases hsub with h | h
      · exact hu (h ▸ hp)
      · exact hv (h ▸ hp)
    subst hFeq
    simp

/-- The Boolean refinement of independently-paired sigma-fields is mutually
independent. -/
theorem iIndep_refinedSigma [IsProbabilityMeasure μ] {ι : Type*}
    {κ a b : ι → MeasurableSpace Ω} (hκ : iIndep κ μ)
    (ha : ∀ i, a i ≤ κ i) (hb : ∀ i, b i ≤ κ i)
    (hab : ∀ i, Indep (a i) (b i) μ) :
    iIndep (refinedSigma a b) μ := by
  classical
  rw [iIndep_iff]
  intro S' g hg
  have hnκ : ∀ p : ι × Bool, refinedSigma a b p ≤ κ p.1 := by
    rintro ⟨i, c⟩
    cases c
    · simpa using! ha i
    · simpa using! hb i
  set L := S'.image Prod.fst with hL
  set fib : ι → Finset (ι × Bool) := fun i => S'.filter (fun q => q.1 = i) with hfib
  have hInter : (⋂ p ∈ S', g p) = ⋂ i ∈ L, ⋂ p ∈ fib i, g p := by
    ext x
    simp only [Set.mem_iInter, hfib, Finset.mem_filter, hL, Finset.mem_image]
    constructor
    · intro h i _ p hp
      exact h p hp.1
    · intro h p hp
      exact h p.1 ⟨p, hp, rfl⟩ p ⟨hp, rfl⟩
  have hGmeas : ∀ i ∈ L, MeasurableSet[κ i] (⋂ p ∈ fib i, g p) := by
    intro i _
    refine @Finset.measurableSet_biInter _ _ (κ i) _ _ (fun p hp => ?_)
    have hpi : p.1 = i := (Finset.mem_filter.1 hp).2
    have hmeas := (hnκ p) _ (hg p (Finset.mem_filter.1 hp).1)
    rwa [hpi] at hmeas
  have hfiber : ∀ i ∈ L, μ (⋂ p ∈ fib i, g p) = ∏ p ∈ fib i, μ (g p) := by
    intro i _
    refine meas_biInter_fiber i (hab i) (fun p hp => (Finset.mem_filter.1 hp).2) ?_
    intro p hp
    exact hg p (Finset.mem_filter.1 hp).1
  rw [hInter, hκ.meas_biInter hGmeas]
  rw [Finset.prod_congr rfl hfiber]
  have hmaps : ∀ p ∈ S', Prod.fst p ∈ L := fun p hp =>
    hL ▸ Finset.mem_image_of_mem Prod.fst hp
  exact Finset.prod_fiberwise_of_maps_to hmaps (fun p => μ (g p))

/-- Aggregate the two local sigma-fields from independent shell coordinates.
This is the exact countable `iSup` theorem used by the cutoff range proof. -/
theorem indep_iSup_of_indep_of_iIndep [IsProbabilityMeasure μ] {ι : Type*}
    {κ a b : ι → MeasurableSpace Ω} (hκ : iIndep κ μ) (hle : ∀ i, κ i ≤ mΩ)
    (ha : ∀ i, a i ≤ κ i) (hb : ∀ i, b i ≤ κ i)
    (hab : ∀ i, Indep (a i) (b i) μ) :
    Indep (⨆ i, a i) (⨆ i, b i) μ := by
  classical
  have hind : iIndep (refinedSigma a b) μ := iIndep_refinedSigma hκ ha hb hab
  have hnle : ∀ p : ι × Bool, refinedSigma a b p ≤ mΩ := by
    rintro ⟨i, c⟩
    cases c
    · exact le_trans (by simpa using! ha i) (hle i)
    · exact le_trans (by simpa using! hb i) (hle i)
  have hdisj : Disjoint ({p : ι × Bool | p.2 = false}) ({p : ι × Bool | p.2 = true}) := by
    rw [Set.disjoint_left]
    rintro ⟨i, c⟩ hs ht
    simp only [Set.mem_ofPred_eq] at hs ht
    rw [hs] at ht
    exact absurd ht (by decide)
  have hmain := indep_iSup_of_disjoint hnle hind hdisj
  have hSa : (⨆ p ∈ ({p : ι × Bool | p.2 = false}), refinedSigma a b p) = ⨆ i, a i := by
    apply le_antisymm
    · refine iSup₂_le ?_
      rintro ⟨i, c⟩ (hc : c = false)
      subst hc
      exact le_iSup a i
    · refine iSup_le fun i => ?_
      exact le_iSup₂_of_le (i, false) rfl le_rfl
  have hSb : (⨆ p ∈ ({p : ι × Bool | p.2 = true}), refinedSigma a b p) = ⨆ i, b i := by
    apply le_antisymm
    · refine iSup₂_le ?_
      rintro ⟨i, c⟩ (hc : c = true)
      subst hc
      exact le_iSup b i
    · refine iSup_le fun i => ?_
      exact le_iSup₂_of_le (i, true) rfl le_rfl
  rwa [hSa, hSb] at hmain

end Algsuperdiff.Probability
