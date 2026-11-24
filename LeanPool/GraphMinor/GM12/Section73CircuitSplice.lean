/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73CircuitWalks

/-!
# Joining the old circuit through the radial star

In XII (7.3), Claim (1), page 262, the two replaced spokes have
either the same old middle vertex or different old middle vertices.
In the first case two edges close the retained path. In the second
case four edges close it through the deleted vertex. The middle
vertices and the deleted vertex lie outside the retained path, so
both constructions give simple closed walks.
-/

public section

namespace GraphMinor.GM12

open Set Surface Graph

/-- The four-edge splice in XII (7.3), Claim (1), page 262,
closes the retained path into a simple closed walk. All its edges
belong to the path or the four specified spokes. -/
theorem exists_simpleClosed_four_edge_splice
    {α β : Type*} {G : Graph α β} {x y v p q : α} {a b c d : β}
    (ha : G.IsLink a v p) (hb : G.IsLink b p x)
    (hc : G.IsLink c y q) (hd : G.IsLink d q v)
    (P : GraphWalk G x y) (hP : P.IsSimple)
    (hp : p ∉ P.support) (hq : q ∉ P.support) (hv : v ∉ P.support)
    (hpq : p ≠ q) (hpv : p ≠ v) (hqv : q ≠ v) :
    ∃ W : GraphWalk G v v, W.IsSimpleClosed ∧ W.length = P.length + 4 ∧
      W.edges = a :: b :: (P.edges ++ [c, d]) ∧
      W.support = v :: p :: (P.support ++ [q, v]) := by
  let Q : GraphWalk G p q := .cons hb (P.append (.cons hc (.nil hc.right_mem)))
  have hQsupport : Q.support = p :: (P.support ++ [q]) := by
    dsimp only [Q]
    rw [GraphWalk.support_cons, GraphWalk.support_append]
    rfl
  have hQsimple : Q.IsSimple := by
    change Q.support.Nodup
    rw [hQsupport]
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_append.mpr ⟨hP, by simp, ?_⟩⟩
    · intro hpm
      rcases List.mem_append.mp hpm with hpm | hpm
      · exact hp hpm
      · exact hpq (List.mem_singleton.mp hpm)
    · intro z hz w hw hzw
      have hwq : w = q := List.mem_singleton.mp hw
      exact hq (hzw.trans hwq ▸ hz)
  have hvQ : v ∉ Q.support := by
    rw [hQsupport]
    intro hvm
    rcases List.mem_cons.mp hvm with hvp | hvm
    · exact hpv hvp.symm
    · rcases List.mem_append.mp hvm with hvm | hvm
      · exact hv hvm
      · exact hqv (List.mem_singleton.mp hvm).symm
  have had : a ≠ d := by
    intro had
    have ha' : G.IsLink d v p := had ▸ ha
    exact hpq (ha'.right_unique hd.symm)
  let W : GraphWalk G v v := .cons ha (Q.append (.cons hd (.nil hd.right_mem)))
  refine ⟨W, isSimpleClosed_close_path ha hd Q hQsimple hvQ had, ?_, ?_, ?_⟩
  · dsimp only [W, Q]
    rw [GraphWalk.length_cons, GraphWalk.length_append, GraphWalk.length_cons,
      GraphWalk.length_append]
    simp only [GraphWalk.length_cons, GraphWalk.length_nil]
  · dsimp only [W, Q]
    rw [GraphWalk.edges_cons, GraphWalk.edges_append, GraphWalk.edges_cons,
      GraphWalk.edges_append]
    simp only [GraphWalk.edges_cons, GraphWalk.edges_nil, List.append_assoc, List.cons_append]
    rfl
  · dsimp only [W]
    rw [GraphWalk.support_cons, GraphWalk.support_append, hQsupport]
    simp only [GraphWalk.support_cons, GraphWalk.support_nil, List.tail_cons,
      List.cons_append, List.append_assoc]
    rfl

end GraphMinor.GM12
