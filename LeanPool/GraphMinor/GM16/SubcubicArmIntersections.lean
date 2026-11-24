/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.ModelBranchCentres

/-!
# Intersections between arms for distinct minor edges

In XVI (4.2), page 54, arms in different branch sets are disjoint.
Two arms in the same branch set come from different neighbours when
the model edges differ. They therefore meet only at the branch centre.
This proves that the paths replacing different minor edges can meet
only at branch centres.
-/

public section
namespace GraphMinor.GM16
open Set Graph SimpleGraph
universe u v w

/-- Arms belonging to different source edges can meet only at a branch
centre. This is the intersection check in XVI (4.2)'s subdivision step. -/
theorem arm_intersection_subset_centres
    {α : Type u} {β : Type v} {ν : Type w}
    {H : SimpleGraph ν} {G : Graph α β} {ηv : ν → Set α} {ηe : Sym2 ν → β}
    (h : IsMinorModel (Graph.ofSimpleGraph H) G ηv ηe)
    (c : ν → α) (arm : ∀ v, H.neighborSet v → Graph α β)
    (hSub : ∀ v i, V(arm v i) ⊆ ηv v)
    (hInter : ∀ v i j, i ≠ j → V(arm v i) ∩ V(arm v j) = {c v})
    {a b d e : ν} (hab : H.Adj a b) (hde : H.Adj d e)
    (hNe : s(a, b) ≠ s(d, e)) :
    V(arm a ⟨b,hab⟩) ∩ V(arm d ⟨e,hde⟩) ⊆ range c := by
  intro x hx
  by_cases had : a = d
  · subst d
    have hbe : b ≠ e := fun heq => hNe (heq ▸ rfl)
    have hIdx : (⟨b,hab⟩ : H.neighborSet a) ≠ ⟨e,hde⟩ :=
      fun heq => hbe (congrArg Subtype.val heq)
    have hxc : x = c a := by
      have hx' := hx
      rw [hInter a _ _ hIdx] at hx'
      exact hx'
    exact ⟨a, hxc.symm⟩
  · have hd := h.vertex_disjoint a (mem_univ _) d (mem_univ _) had
    exact ((disjoint_left.mp hd) (hSub a _ hx.1) (hSub d _ hx.2)).elim

end GraphMinor.GM16
