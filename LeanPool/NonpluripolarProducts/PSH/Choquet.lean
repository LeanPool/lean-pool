/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.PSH.VariableAtlas
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ChoquetRegularization

/-!
# Source Choquet lemma with original family indices

Reuse the genuine countable-basis envelope producer from the main branch.
Derive global second countability from the source's exact countable-component
assumption and its convention of a countable basis on every component.
-/

@[expose] public section

namespace SGPT.PSH

open Set Filter Metric
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology

variable {X : Type*} [TopologicalSpace X]

/-- A countable set of actual original indices, without injectivity of the
family map. This purely topological result also permits arbitrary functions. -/
theorem exists_countable_indices_uscSup_eq [SecondCountableTopology X]
    {I : Type*} [Nonempty I] (v : I → X → EReal) :
    ∃ J : Set I, J.Countable ∧ J.Nonempty ∧
      uscSup (fun j : J ↦ v j) = uscSup v := by
  classical
  obtain ⟨s, hs, heq⟩ := SGPT.Foundations.Analysis.Pending.exists_seq_uscRegularization_iSup_eq
    (Set.range_nonempty v)
  choose a ha using hs
  let J : Set I := Set.range a
  have hsup : (fun x ↦ ⨆ j : J, v j x) = fun x ↦ ⨆ n, s n x := by
    funext x
    apply le_antisymm
    · refine iSup_le fun j ↦ ?_
      obtain ⟨n, hn⟩ := j.property
      exact (by simpa only [← hn, ha n] using (le_iSup (fun n ↦ s n x) n))
    · refine iSup_le fun n ↦ ?_
      have h := le_iSup (fun j : J ↦ v j x) (⟨a n, Set.mem_range_self n⟩ : J)
      simpa only [ha n] using h
  refine ⟨J, Set.countable_range a, Set.range_nonempty a, ?_⟩
  unfold uscSup
  rw [hsup]
  have hsfn : (⨆ k, s k) = fun x ↦ ⨆ k, s k x := by
    funext x
    exact iSup_apply
  rw [hsfn] at heq
  simpa only [sSup_range_eq] using heq

namespace VariableComplexAtlas

variable (A : VariableComplexAtlas X)

include A

/-- Actual coordinate balls show every original connected component is open;
no connectedness conclusion is part of the atlas data. -/
theorem isOpen_component (x : X) : IsOpen (connectedComponent x) := by
  apply isOpen_iff_mem_nhds.mpr
  intro y hy
  obtain ⟨i, hi⟩ := A.cover y
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (A.chart i).open_target
    (A.chart i y) ((A.chart i).map_source hi)
  let V := (A.chart i).symm '' ball (A.chart i y) r
  have hV : IsOpen V := (A.chart i).isOpen_image_symm_of_subset_target isOpen_ball hball
  have hyV : y ∈ V := ⟨A.chart i y, mem_ball_self hr, (A.chart i).left_inv hi⟩
  have hc : IsConnected V := (isConnected_ball hr).image _
    ((A.chart i).continuousOn_symm.mono hball)
  have hsub : V ⊆ connectedComponent x := by
    rw [connectedComponent_eq hy]
    exact hc.subset_connectedComponent hyV
  exact Filter.mem_of_superset (hV.mem_nhds hyV) hsub

/-- The exact countable-component source assumption and the book's countable
basis convention imply the global topology used by the existing producer. -/
theorem secondCountableTopology_of_countable_components
    (hcount : (Set.range (connectedComponent : X → Set X)).Countable)
    (hbases : ∀ x : X, SecondCountableTopology (connectedComponent x)) :
    SecondCountableTopology X := by
  classical
  let C := Set.range (connectedComponent : X → Set X)
  have : Countable C := hcount.to_subtype
  let representative : C → X := fun c ↦ c.property.choose
  have hrep (c : C) : connectedComponent (representative c) = c.val := c.property.choose_spec
  have : ∀ c : C, SecondCountableTopology (c.val) := fun c ↦ by
    rw [← hrep c]
    exact hbases (representative c)
  apply TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := fun c : C ↦ c.val)
  · intro c
    rw [← hrep c]
    exact A.isOpen_component (representative c)
  · apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨⟨connectedComponent x, Set.mem_range_self x⟩, mem_connectedComponent⟩

/-- SGPT `prop:Choquet`: actual countable indices and exact original
components. The producer validly requires no PSH or boundedness premise. -/
theorem exists_countable_indices_uscSup_eq_of_countable_components
    (hcount : (Set.range (connectedComponent : X → Set X)).Countable)
    (hbases : ∀ x : X, SecondCountableTopology (connectedComponent x))
    {I : Type*} [Nonempty I] (v : I → X → EReal) :
    ∃ J : Set I, J.Countable ∧ J.Nonempty ∧
      uscSup (fun j : J ↦ v j) = uscSup v := by
  let := A.secondCountableTopology_of_countable_components hcount hbases
  exact exists_countable_indices_uscSup_eq v

end VariableComplexAtlas
end SGPT.PSH
