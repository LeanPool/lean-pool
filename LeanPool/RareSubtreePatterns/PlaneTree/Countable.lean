/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.PlaneTree.Basic

/-!
# Countability of finite plane trees and the discrete measurable structure

Finite plane trees form a countable type, through an injective code into the natural
numbers. They carry the discrete σ-algebra, so every set of trees is measurable.
Their laws are therefore ordinary probability measures determined by point masses.

The discrete `MeasurableSpace PlaneTree` instance and the outdegree sequence `degSeq` are
defined in `PoissonDeclumping.Statements.Defs` (shared verbatim with `Challenge.lean`).
-/

@[expose] public section

namespace PoissonDeclumping.PlaneTree

/-- Injective numerical code of a plane tree: encode the list of child codes. -/
def code : PlaneTree → ℕ
  | .node ts => Encodable.encode (ts.attach.map fun U => code U.1)
termination_by T => sizeOf T
decreasing_by
  have h := List.sizeOf_lt_of_mem U.2
  simp only [PlaneTree.node.sizeOf_spec]
  omega

theorem code_node (ts : List PlaneTree) :
    code (node ts) = Encodable.encode (ts.map code) := by
  rw [code]
  simp

private theorem list_eq_of_map_code_eq {ts us : List PlaneTree}
    (ih : ∀ V ∈ ts, ∀ W, code V = code W → V = W)
    (h : ts.map code = us.map code) : ts = us := by
  induction ts generalizing us with
  | nil =>
    cases us with
    | nil => rfl
    | cons u us => simp at h
  | cons t ts ihl =>
    cases us with
    | nil => simp at h
    | cons u us =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [ih t (by simp) u h1, ihl (fun V hV => ih V (by simp [hV])) h2]

theorem code_injective : Function.Injective code := by
  intro T
  induction T using induction_children with
  | step T ih =>
    intro U h
    cases T with
    | node ts =>
      cases U with
      | node us =>
        rw [code_node, code_node] at h
        have hl := Encodable.encode_injective h
        congr 1
        exact list_eq_of_map_code_eq (fun V hV W hW => ih V hV hW) hl

instance : Countable PlaneTree := code_injective.countable

instance : DiscreteMeasurableSpace PlaneTree := ⟨fun _ => trivial⟩

theorem degSeq_node (ts : List PlaneTree) :
    (node ts).degSeq = ts.length :: ts.flatMap degSeq := by
  simp only [degSeq, fringeTrees_node, List.map_cons, List.map_flatMap, rootDegree_node]
  rfl

theorem length_degSeq (T : PlaneTree) : T.degSeq.length = T.vertexCount := by
  simp [degSeq, vertexCount]

end PoissonDeclumping.PlaneTree
