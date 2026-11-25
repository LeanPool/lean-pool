/-
Copyright (c) 2026 Md Thoriqul Islam Thonmay and Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Md Thoriqul Islam Thonmay, Gregory Morse
-/

-- Modified for Lean Pool.

module

public import LeanPool.DynamicMcs.Definitions
public import LeanPool.DynamicMcs.GreedySearch

/-!
# Executable maximum-cardinality search

The greedy search uses Boolean adjacency rows and chooses the least index when
neighbor counts tie. A single-edge update changes the two symmetric entries.
-/

@[expose] public section

namespace DynamicMcs

namespace Exec

variable {n : ℕ}

/-- Row lookup: `atRow row v` is the v-th entry of the row, `false` if out of
range (loopless/well-shaped matrices keep this total). -/
def atRow : List Bool → ℕ → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: rest, k+1 => atRow rest k

/-- `getAdj a u v`: is edge (u,v) present in the undirected adjacency `a`? -/
def getAdj (a : Adj n) (u v : ℕ) : Bool :=
  match a[u]? with
  | none => false
  | some row => atRow row v

/-- Number of chosen neighbors of `w`. -/
def cardC (a : Adj n) (chosen : List ℕ) (w : ℕ) : ℕ :=
  (chosen.filter (fun v => getAdj a v w)).length

/-- MCS pick: among remaining vertices, the one with maximum cardinality,
tie-broken by smallest vertex id. -/
def bestPick (a : Adj n) (chosen : List ℕ) (rem : List ℕ) : ℕ :=
  rem.foldl (fun best v =>
    let cb := cardC a chosen best
    let cv := cardC a chosen v
    if cv > cb ∨ (cv = cb ∧ v < best) then v else best)
    (rem.headD 0)

/-- One MCS step: state is (chosen-in-reverse, remaining). -/
def mcsStep (a : Adj n) (st : List ℕ × List ℕ) : List ℕ × List ℕ :=
  let (chosen, rem) := st
  match rem with
  | [] => st
  | _ => let v := bestPick a chosen rem; (v :: chosen, rem.erase v)

/-- Computable MCS ordering of `a` (ties broken by smallest id). -/
def mcsOrder (a : Adj n) : List ℕ :=
  let n := a.length
  let st := ((List.range n).foldl (fun s _ => mcsStep a s) ([], List.range n))
  st.1.reverse

/-- Flip undirected edge (u,v): set symmetric entries to `present`. -/
def setEdge (n : ℕ) (a : Adj n) (u v : ℕ) (present : Bool) : Adj n :=
  List.mapIdx (fun i row =>
    List.mapIdx (fun j b =>
      if i = u ∧ j = v ∨ i = v ∧ j = u then present else b) row) a

/-- Insert edge. -/
def insertEdge (n : ℕ) (a : Adj n) (u v : ℕ) : Adj n := setEdge n a u v true
/-- Delete edge. -/
def deleteEdge (n : ℕ) (a : Adj n) (u v : ℕ) : Adj n := setEdge n a u v false

/-- Build the abstract UGraph from an executable adjacency matrix, when the
matrix is symmetric, loop-free, and square of size n. -/
def toUGraph (a : Adj n) (hsymm : ∀ u v : ℕ, getAdj a u v = getAdj a v u)
    (hloop : ∀ u : ℕ, getAdj a u u = false) : Greedy.UGraph n :=
  { adj := fun x y => getAdj a x.val y.val = true
    symm := by
      intro x y h
      rwa [hsymm x.val y.val] at h
    loopless := by
      intro x h
      have hx : getAdj a x.val x.val = false := hloop x.val
      simp [hx] at h }

end Exec
end DynamicMcs
