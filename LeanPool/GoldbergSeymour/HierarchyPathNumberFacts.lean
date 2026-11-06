/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyPathNumber

/-!
# Path-number obstruction at the terminal edge

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input generating phi : PartialEdgeColoring E k}
    {tree : TreeSequence G e0} {ett : ExtendedTashkinovTree G k e0 input tree generating}
    {base : HierarchyBase ett phi}

/-- A full path number prevents the last edge from joining the final two tree vertices. -/
theorem TashkinovHierarchy.lastEdgeNotIncidentPenultimate
    (H : TashkinovHierarchy ett base)
    (full : HierarchyPathNumber H =
      tree.length - (HierarchyStarredStage H (Fin.last H.dividerCount)).length)
    (tail : 2 ≤ tree.length - (HierarchyStarredStage H (Fin.last H.dividerCount)).length)
    (last : Fin tree.length) (penultimate terminal : Fin (tree.length + 1))
    (lastPosition : last.val + 1 = tree.length)
    (penultimatePosition : penultimate.val + 1 = tree.length)
    (terminalPosition : terminal.val = tree.length) :
    ¬Incident G (tree.vertex penultimate) (tree.edge last) := by
  classical
  intro incident
  obtain ⟨i, attaches⟩ := tree.attaches last
  let old : Fin (tree.length + 1) :=
    i.castLT (Nat.lt_trans i.isLt (Nat.succ_lt_succ last.isLt))
  have terminalEqual : last.succ = terminal := Fin.ext (by simp; omega)
  have members : tree.vertex penultimate = tree.vertex last.succ ∨
      tree.vertex penultimate = tree.vertex old := by
    simpa only [Incident, attaches, Sym2.mem_iff] using incident
  rcases members with equal | equal
  · have indices := congrArg Fin.val (tree.vertex_injective equal)
    simp only [Fin.val_succ] at indices
    omega
  have ends : G.ends (tree.edge last) =
      s(tree.vertex penultimate, tree.vertex terminal) := by
    change G.ends (tree.edge last) = s(tree.vertex last.succ, tree.vertex old) at attaches
    rw [terminalEqual, ← equal] at attaches
    exact attaches.trans Sym2.eq_swap
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  let length := tree.length - A.length
  let candidates := (Finset.Icc 1 length).filter fun j =>
    ∀ r : Fin tree.length, A.length + j ≤ r.val →
      G.ends (tree.edge r) = s(tree.vertex r.castSucc, tree.vertex r.succ)
  have tailBound : 2 ≤ length := tail
  have stageBound : A.length ≤ tree.length := by omega
  have member : length - 1 ∈ candidates := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    intro r bound
    have indexEqual : r = last := Fin.ext (by have := r.isLt; dsimp [length] at bound; omega)
    subst r
    have penultimateEqual : last.castSucc = penultimate := Fin.ext (by simp; omega)
    simpa only [penultimateEqual, terminalEqual] using ends
  have nonempty : candidates.Nonempty := ⟨length - 1, member⟩
  have minimum := Finset.min'_le candidates (length - 1) member
  have pathNumber : HierarchyPathNumber H = candidates.min' nonempty := by
    change (if h : candidates.Nonempty then candidates.min' h else length) = _
    rw [dite_eq_left nonempty]
  have equal : length = candidates.min' nonempty := full.symm.trans pathNumber
  omega

end GoldbergSeymour

end
