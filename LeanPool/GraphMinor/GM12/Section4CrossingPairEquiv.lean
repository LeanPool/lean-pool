/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert

/-!
# The bijection between edges and crossing pairs

In XII (4.5), page 253, the edges of the subdivided source fall
into crossing pairs. Give each crossing its two incident edges.
Every edge has exactly one crossing, so two crossings cannot
supply the same edge. Conversely each edge is supplied by the
two-edge pair at its unique crossing. This gives the actual
bijection used to index the external paths by source edges.
-/

public section

namespace GraphMinor.GM12

open Set

/-- Edges with one crossing each are in bijection with the two
positions at every crossing. The map sends the two positions
to the two incident edges, as used to reindex the external
paths in XII (4.5), page 253. -/
theorem exists_crossing_pair_equiv {X T E : Type*}
    (x : T → X) (hinj : Function.Injective x) (P : E → Set X) (left right : T → E)
    (hne : ∀ i, left i ≠ right i)
    (hpair : ∀ i, x i ∈ P (left i) ∩ P (right i))
    (honly : ∀ i e, x i ∈ P e → e = left i ∨ e = right i)
    (hsingle : ∀ e, ∃ i, P e ∩ range x = {x i}) :
    ∃ σ : T × Bool ≃ E, ∀ i, σ (i, false) = left i ∧ σ (i, true) = right i := by
  classical
  let f : T × Bool → E := fun q => if q.2 then right q.1 else left q.1
  have hxf : ∀ q, x q.1 ∈ P (f q) := by
    rintro ⟨i, b⟩
    cases b
    · exact (hpair i).1
    · exact (hpair i).2
  have hfi : Function.Injective f := by
    rintro ⟨i, b⟩ ⟨j, c⟩ heq
    obtain ⟨k, hk⟩ := hsingle (f (i, b))
    have hix : x i = x k := mem_singleton_iff.mp (hk.subset ⟨hxf (i, b), mem_range_self i⟩)
    have hjP : x j ∈ P (f (i, b)) := heq.symm ▸ hxf (j, c)
    have hjx : x j = x k := mem_singleton_iff.mp (hk.subset ⟨hjP, mem_range_self j⟩)
    have hij : i = j := hinj (hix.trans hjx.symm)
    subst j
    have hbc : b = c := by
      cases b <;> cases c
      · rfl
      · exact False.elim (hne i heq)
      · exact False.elim (hne i heq.symm)
      · rfl
    subst c
    rfl
  have hfs : Function.Surjective f := by
    intro e
    obtain ⟨i, hi⟩ := hsingle e
    have hxe : x i ∈ P e := (hi.symm.subset (mem_singleton _)).1
    rcases honly i e hxe with he | he
    · exact ⟨(i, false), he.symm⟩
    · exact ⟨(i, true), he.symm⟩
  exact ⟨Equiv.ofBijective f ⟨hfi, hfs⟩, fun _ => ⟨rfl, rfl⟩⟩

end GraphMinor.GM12
