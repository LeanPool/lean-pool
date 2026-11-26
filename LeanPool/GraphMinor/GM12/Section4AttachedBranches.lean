/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM12.Section4BranchUnions
import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# Attaching disjoint path pieces to branches

XII (4.4), page 252, defines each clique branch by adding its
assigned shortened paths to the connected subdrawing. Form these
finite unions explicitly. Every path piece meets its own branch
and avoids all other branches. Different path pieces are disjoint.
These facts give both connectivity and pairwise disjointness of
the enlarged branches.
-/

public section

namespace GraphMinor.GM12

open Set Hypergraph GM10

/-- A finite union of subhypergraphs remains a subhypergraph. -/
theorem biUnion_le_of_each_le
    {α β ι : Type*} {G : Hypergraph α β} (B : ι → Hypergraph α β) (F : Finset ι)
    (hB : ∀ i ∈ F, B i ≤ G) : Hypergraph.biUnion F B ≤ G := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact (hB i hi).vertexSet_subset hxi
  · intro e he
    obtain ⟨i, hi, hei⟩ := mem_iUnion₂.mp he
    exact (hB i hi).edgeSet_subset hei
  · intro e he
    obtain ⟨i, hi, hei⟩ := mem_iUnion₂.mp he
    ext x
    constructor
    · intro hix
      exact ⟨i, hi, (inc_iff_of_le (hB i hi) hei).mpr hix⟩
    · rintro ⟨j, hj, hjx⟩
      exact (inc_iff_of_le (hB j hj) ((B j).edge_mem_of_inc hjx)).mp hjx

/-- Add disjoint connected pieces to their assigned nonempty
connected branches, as in XII (4.4), page 252. -/
theorem exists_branches_with_attached_pieces
    {α β ι κ : Type*} [Finite ι] {G : Hypergraph α β}
    (A : κ → Hypergraph α β) (B : ι → Hypergraph α β) (owner : ι → κ)
    (hA : ∀ v, A v ≤ G ∧ (A v).vertexSet.Nonempty ∧ IsConnectedSub (A v))
    (hAA : ∀ v w, v ≠ w → Disjoint (A v).vertexSet (A w).vertexSet)
    (hB : ∀ i, B i ≤ G ∧ IsConnectedSub (B i))
    (hBB : ∀ i j, i ≠ j → Disjoint (B i).vertexSet (B j).vertexSet)
    (hmeet : ∀ i, ((A (owner i)).vertexSet ∩ (B i).vertexSet).Nonempty)
    (hcross : ∀ i v, v ≠ owner i → Disjoint (B i).vertexSet (A v).vertexSet) :
    ∃ C : κ → Hypergraph α β,
      (∀ v, C v ≤ G ∧ (C v).vertexSet.Nonempty ∧ IsConnectedSub (C v)) ∧
      (∀ v w, v ≠ w → Disjoint (C v).vertexSet (C w).vertexSet) ∧
      (∀ v, A v ≤ C v) ∧ ∀ i, B i ≤ C (owner i) := by
  classical
  let indexFintype := Fintype.ofFinite ι
  let F : κ → Finset ι := fun v => Finset.univ.filter (fun i => owner i = v)
  let C : κ → Hypergraph α β := fun v => A v ∪ Hypergraph.biUnion (F v) B
  have hF : ∀ i v, i ∈ F v ↔ owner i = v := by intro i v; simp [F]
  have hCle : ∀ v, C v ≤ G := fun v =>
    union_le (hA v).1 (biUnion_le_of_each_le B (F v) (fun i _ => (hB i).1))
  have hAC : ∀ v, A v ≤ C v := fun v =>
    le_union_left (hA v).1 (biUnion_le_of_each_le B (F v) (fun i _ => (hB i).1))
  have hBC : ∀ i, B i ≤ C (owner i) := by
    intro i
    apply (le_iff_of_le (hB i).1 (hCle (owner i))).mpr
    exact ⟨fun x hx => Or.inr (mem_iUnion₂.mpr ⟨i, (hF i _).mpr rfl, hx⟩),
      fun e he => Or.inr (mem_iUnion₂.mpr ⟨i, (hF i _).mpr rfl, he⟩)⟩
  refine ⟨C, ?_, ?_, hAC, hBC⟩
  · intro v
    refine ⟨hCle v, (hA v).2.1.mono (hAC v).vertexSet_subset, ?_⟩
    apply isConnectedSub_union_biUnion (A v) B (F v) (hA v).2.1 (hA v).2.2
      (fun i _ => (hB i).2)
    intro i hi
    have hown := (hF i v).mp hi
    exact hown ▸ hmeet i
  · intro v w hvw
    apply Set.disjoint_left.mpr
    intro x hxv hxw
    rcases hxv with hxA | hxB <;> rcases hxw with hyA | hyB
    · exact Set.disjoint_left.mp (hAA v w hvw) hxA hyA
    · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hyB
      have hjw := (hF j w).mp hj
      exact Set.disjoint_left.mp (hcross j v (fun h => hvw (h.trans hjw))) hxj hxA
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxB
      have hiv := (hF i v).mp hi
      exact Set.disjoint_left.mp (hcross i w (fun h => hvw (h.trans hiv).symm)) hxi hyA
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxB
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hyB
      have hiv := (hF i v).mp hi
      have hjw := (hF j w).mp hj
      have hij : i ≠ j := fun h => hvw (hiv.symm.trans (h ▸ hjw))
      exact Set.disjoint_left.mp (hBB i j hij) hxi hxj

end GraphMinor.GM12
