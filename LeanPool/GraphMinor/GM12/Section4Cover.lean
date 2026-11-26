/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Minimal

/-!
# Chains in a finite closed cover

In Graph Minors XII, proof of (4.1), page 248, the circuit insides cover the
path. Connectedness of the path gives a chain of overlapping insides from
one endpoint to the other. This file proves the finite closed-cover part of
that argument. It does not identify the drawing's path with its cover.
-/

public section

namespace GraphMinor.GM12

open Set

/-- Sets in a finite closed cover of a connected set can be joined by a chain
of intersections when they both meet the connected set. This is the chain
existence step used in XII (4.1), page 248. -/
theorem intersection_chain_of_finite_closed_cover {α ι : Type*}
    [TopologicalSpace α] [Finite ι] (C : ι → Set α) (hclosed : ∀ i, IsClosed (C i))
    {P : Set α} (hP : IsPreconnected P) (hcover : P ⊆ ⋃ i, C i)
    {i j : ι} (hi : (P ∩ C i).Nonempty) (hj : (P ∩ C j).Nonempty) :
    Relation.ReflTransGen (fun k l => (C k ∩ C l).Nonempty) i j := by
  classical
  let reach : ι → Prop := Relation.ReflTransGen (fun k l => (C k ∩ C l).Nonempty) i
  let U : Set α := ⋃ k : {k // reach k}, C k.val
  let V : Set α := ⋃ k : {k // ¬ reach k}, C k.val
  have hU : IsClosed U := isClosed_iUnion_of_finite (fun k => hclosed k.val)
  have hV : IsClosed V := isClosed_iUnion_of_finite (fun k => hclosed k.val)
  have hUV : P ⊆ U ∪ V := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcover hx)
    by_cases hr : reach k
    · exact Or.inl (mem_iUnion.mpr ⟨⟨k, hr⟩, hk⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨k, hr⟩, hk⟩)
  have hiU : (P ∩ U).Nonempty := by
    obtain ⟨x, hxP, hx⟩ := hi
    exact ⟨x, hxP, mem_iUnion.mpr ⟨⟨i, .refl⟩, hx⟩⟩
  by_contra hnot
  have hjV : (P ∩ V).Nonempty := by
    obtain ⟨x, hxP, hx⟩ := hj
    exact ⟨x, hxP, mem_iUnion.mpr ⟨⟨j, hnot⟩, hx⟩⟩
  obtain ⟨x, _, hxU, hxV⟩ :=
    isPreconnected_closed_iff.mp hP U V hU hV hUV hiU hjV
  obtain ⟨k, hk⟩ := mem_iUnion.mp hxU
  obtain ⟨l, hl⟩ := mem_iUnion.mp hxV
  exact l.property (k.property.tail ⟨x, hk, hl⟩)

/-- Every member of a finite family is included in a maximal member. In
XII (4.1), this lets the circuit cover be chosen without proper inclusions. -/
theorem exists_maximal_cover_member {α ι : Type*} [Finite ι]
    (C : ι → Set α) (i : ι) :
    ∃ j, C i ⊆ C j ∧ ∀ k, C j ⊆ C k → C k ⊆ C j := by
  let Z : Set (Set α) := {X | X ∈ Set.range C ∧ C i ⊆ X}
  have hfin : Z.Finite := (Set.finite_range C).subset (fun _ h => h.1)
  obtain ⟨X, hX, hmax⟩ := hfin.exists_maximal ⟨C i, ⟨⟨i, rfl⟩, subset_rfl⟩⟩
  obtain ⟨j, rfl⟩ := hX.1
  exact ⟨j, hX.2, fun k hk => hmax ⟨⟨k, rfl⟩, hX.2.trans hk⟩ hk⟩

end GraphMinor.GM12
