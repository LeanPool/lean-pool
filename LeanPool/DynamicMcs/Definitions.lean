/-
Copyright (c) 2026 Md Thoriqul Islam Thonmay and Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Md Thoriqul Islam Thonmay, Gregory Morse
-/

-- Modified for Lean Pool.

module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.TakeDrop

/-!
# Specifications and executable updates for maximum-cardinality search

The abstract orderings support both least-index and arbitrary tie breaks.
The executable updates probe an existing ordering and rebuild its invalid suffix.
-/

@[expose] public section

-- BEGIN DEFS
noncomputable section

namespace DynamicMcs

/-- Vertices of an `n`-vertex undirected graph. -/
abbrev Vert (n : ℕ) := Fin n

/-- A finite undirected, loop-free graph on the vertices `Fin n`. -/
structure UGraph (n : ℕ) where
  /-- Adjacency of a pair of vertices. -/
  adj : Vert n → Vert n → Prop
  symm : ∀ {x y : Vert n}, adj x y → adj y x
  loopless : ∀ (x : Vert n), ¬ adj x x

namespace UGraph

variable {n : ℕ}

/-- Cardinality of `w` measured against the already-chosen set `chosen`,
i.e. the number of neighbors of `w` lying in `chosen`. -/
def neigh (G : UGraph n) (chosen : Finset (Vert n)) (w : Vert n) : ℕ := by
  classical
  exact chosen.card - (chosen.filter (fun x => ¬ G.adj w x)).card

/-- `w` is the canonical MCS step after `chosen`: `w` is unchosen, its
cardinality is maximal among the unchosen vertices, and it is the least-index
vertex achieving that maximum. -/
def IsMCSNext (G : UGraph n) (chosen : Finset (Vert n)) (w : Vert n) : Prop :=
  w ∈ (Finset.univ : Finset (Vert n)) \ chosen ∧
  (∀ x : Vert n, x ∈ (Finset.univ : Finset (Vert n)) \ chosen →
    G.neigh chosen x ≤ G.neigh chosen w) ∧
  (∀ x : Vert n, x ∈ (Finset.univ : Finset (Vert n)) \ chosen →
    G.neigh chosen x = G.neigh chosen w → w ≤ x)

/-- `order` is the canonical MCS ordering of `G`: it lists every vertex once
and each position holds the canonical MCS step after the earlier positions. -/
def IsMCSOrdering (G : UGraph n) (order : List (Vert n)) : Prop :=
  order.Nodup ∧ order.length = n ∧
  ∀ (i : ℕ) (hi : i < order.length),
    IsMCSNext G (order.take i).toFinset (order.get ⟨i, hi⟩)

/-- `w` is *an* MCS step after `chosen` under arbitrary tie-breaking. -/
def IsMCSNextAny (G : UGraph n) (chosen : Finset (Vert n)) (w : Vert n) : Prop :=
  w ∈ (Finset.univ : Finset (Vert n)) \ chosen ∧
  ∀ x : Vert n, x ∈ (Finset.univ : Finset (Vert n)) \ chosen →
    G.neigh chosen x ≤ G.neigh chosen w

/-- `order` is an MCS ordering of `G` under arbitrary tie-breaking. -/
def IsMCSOrderingAny (G : UGraph n) (order : List (Vert n)) : Prop :=
  order.Nodup ∧ order.length = n ∧
  ∀ (i : ℕ) (hi : i < order.length),
    IsMCSNextAny G (order.take i).toFinset (order.get ⟨i, hi⟩)

/-- `P` is a *common MCS prefix* of `G` and `G'`: a duplicate-free partial
ordering every one of whose steps is a legal MCS pick in *both* graphs. These
are the sets the greedy construction of a common ordering visits. -/
def IsCommonPrefix (G G' : UGraph n) (P : List (Vert n)) : Prop :=
  P.Nodup ∧ ∀ i (hi : i < P.length),
    IsMCSNextAny G (P.take i).toFinset (P.get ⟨i, hi⟩) ∧
    IsMCSNextAny G' (P.take i).toFinset (P.get ⟨i, hi⟩)

/-- `G'` differs from `G` only by flipping the undirected edge `{u, v}`. -/
def FlipOf (G G' : UGraph n) (u v : Vert n) : Prop :=
  u ≠ v ∧
  ∀ (x y : Vert n),
    G'.adj x y = G.adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)

/-- `G'` is `G` with the edges of `F` added. -/
def AddsEdges (G F G' : UGraph n) : Prop :=
  ∀ x y : Vert n, G'.adj x y ↔ G.adj x y ∨ F.adj x y

/-- Every vertex has at most one `F`-neighbor. -/
def IsMatching (F : UGraph n) : Prop :=
  ∀ x y z : Vert n, F.adj x y → F.adj x z → y = z

/-- The unchosen vertices of maximum cardinality exist whenever some vertex is
unchosen. -/
theorem maxUnchosen_nonempty (G : UGraph n) (chosen : Finset (Vert n))
    (h : chosen ≠ (Finset.univ : Finset (Vert n))) :
    (((Finset.univ : Finset (Vert n)) \ chosen).filter (fun x =>
      G.neigh chosen x =
          ((Finset.univ : Finset (Vert n)) \ chosen).sup (G.neigh chosen))).Nonempty := by
  have hU : ((Finset.univ : Finset (Vert n)) \ chosen).Nonempty :=
    Finset.sdiff_nonempty.2 (fun hs => h (Finset.univ_subset_iff.1 hs))
  obtain ⟨w, hw, hsup⟩ := Finset.exists_mem_eq_sup _ hU (G.neigh chosen)
  exact ⟨w, Finset.mem_filter.2 ⟨hw, hsup.symm⟩⟩

/-- The canonical MCS pick: the least-index unchosen vertex of maximum
cardinality. -/
def mcsPick (G : UGraph n) (chosen : Finset (Vert n))
    (h : chosen ≠ (Finset.univ : Finset (Vert n))) : Vert n :=
  (((Finset.univ : Finset (Vert n)) \ chosen).filter (fun x =>
    G.neigh chosen x = ((Finset.univ : Finset (Vert n)) \ chosen).sup (G.neigh chosen))).min'
    (maxUnchosen_nonempty G chosen h)

/-- The canonical pick is a canonical MCS step. -/
theorem mcsPick_isMCSNext (G : UGraph n) (chosen : Finset (Vert n))
    (h : chosen ≠ (Finset.univ : Finset (Vert n))) :
    IsMCSNext G chosen (mcsPick G chosen h) := by
  have hmem := Finset.min'_mem _ (maxUnchosen_nonempty G chosen h)
  rw [Finset.mem_filter] at hmem
  refine ⟨hmem.1, fun x hx => hmem.2 ▸ Finset.le_sup hx, fun x hx hx' => ?_⟩
  exact Finset.min'_le _ x (Finset.mem_filter.2 ⟨hx, hx'.trans hmem.2⟩)

/-- The canonical pick, carried with its legality proof. -/
def greedyPick (G : UGraph n) (chosen : Finset (Vert n))
    (h : chosen ≠ (Finset.univ : Finset (Vert n))) : { w : Vert n // IsMCSNext G chosen w } :=
  ⟨mcsPick G chosen h, mcsPick_isMCSNext G chosen h⟩

/-- Repeatedly extend `chosen` with the canonical pick, one step per unit of
`k`; the invariant `chosen.card + k = n` certifies that `k` steps suffice. -/
def mcsLoop (G : UGraph n) (chosen : Finset (Vert n)) (k : ℕ)
    (hk : chosen.card + k = n) : List (Vert n) :=
  match k with
  | 0 => []
  | km + 1 =>
      have hchosen : chosen ≠ (Finset.univ : Finset (Vert n)) := by
        intro hc
        have hcard : chosen.card = n := by simp [hc]
        omega
      let p := (greedyPick G chosen hchosen).1
      have hp : p ∉ chosen := by
        exact (Finset.mem_sdiff.mp (greedyPick G chosen hchosen).2.1).2
      have hins : (insert p chosen).card = chosen.card + 1 := by
        exact Finset.card_insert_of_notMem hp
      p :: mcsLoop G (insert p chosen) km (by omega)
termination_by k
decreasing_by
  simp_wf

/-- Canonical MCS continuation of the chosen set `chosen`. -/
def mcsRemainder (G : UGraph n) (chosen : Finset (Vert n)) : List (Vert n) :=
  mcsLoop G chosen (n - chosen.card) (by
    have hcard : chosen.card ≤ n := by
      simpa using (Finset.card_le_univ chosen)
    omega)

/-- Keep the prefix `pref` and recompute the rest canonically (regreedy). -/
def greedySuffix (G : UGraph n) (pref : List (Vert n)) : List (Vert n) :=
  pref ++ mcsRemainder G pref.toFinset

/-- Position (in `order`) of the earlier of the endpoints `u` and `v`. -/
def earlierPos (order : List (Vert n)) (u v : Vert n) : ℕ :=
  min (List.idxOf u order) (List.idxOf v order)

/-- Position (in `order`) of the later of the endpoints `u` and `v`. -/
def laterPos (order : List (Vert n)) (u v : Vert n) : ℕ :=
  max (List.idxOf u order) (List.idxOf v order)

/-- The endpoint placed later in `order`. -/
def laterVert (order : List (Vert n)) (u v : Vert n) : Vert n :=
  if List.idxOf u order ≤ List.idxOf v order then v else u

open Classical in
/-- Boolean negation of a proposition (classical). -/
def isFalse (P : Prop) : Bool :=
  if P then false else true

open Classical in
/-- Scan the list `xs` (whose head sits at position `k` of `order`) and return
the first position whose old choice is not the canonical MCS step on `H`. -/
def firstBreakAux (H : UGraph n) (order : List (Vert n)) :
    ℕ → List (Vert n) → Option ℕ
  | _, [] => none
  | k, x :: xs =>
      if IsMCSNext H (order.take k).toFinset x then firstBreakAux H order (k + 1) xs
      else some k

/-- The first breaking position at or after `k0`, scanning to the end. -/
def firstBreak (H : UGraph n) (order : List (Vert n)) (k0 : ℕ) : Option ℕ :=
  firstBreakAux H order k0 (order.drop k0)

/-- The first breaking position inside the window `[k0, k1]`; the scan
examines only the positions `k0, …, k1`. -/
def firstBreakWindow (H : UGraph n) (order : List (Vert n)) (k0 k1 : ℕ) : Option ℕ :=
  firstBreakAux H order k0 ((order.drop k0).take (k1 + 1 - k0))

/-- The deletion probe: the later endpoint is no longer the canonical step at
its own position. -/
def deletionBreaks (H : UGraph n) (order : List (Vert n)) (u v : Vert n) : Bool :=
  isFalse (IsMCSNext H (order.take (laterPos order u v)).toFinset (laterVert order u v))

/-- Initialisation: the canonical MCS ordering from scratch. -/
def initOrder (H : UGraph n) : List (Vert n) :=
  greedySuffix H []

/-- Insertion update: probe the window `[earlierPos + 1, laterPos]` for the
first break and regreedy from it; keep `order` if the window survives. -/
def insertUpdate (H : UGraph n) (order : List (Vert n)) (u v : Vert n) : List (Vert n) :=
  let k := Option.getD (firstBreakWindow H order (earlierPos order u v + 1)
    (laterPos order u v)) order.length
  greedySuffix H (order.take k)

/-- Deletion update: probe the single position `laterPos`; regreedy from it
only if the probe fires. -/
def deleteUpdate (H : UGraph n) (order : List (Vert n)) (u v : Vert n) : List (Vert n) :=
  if deletionBreaks H order u v then
    greedySuffix H (order.take (laterPos order u v))
  else
    order

/-- The graph on `Fin n` whose edges are the listed pairs (both directions,
loops dropped).  Used to state concrete counterexamples. -/
def ofEdges (n : ℕ) (E : List (ℕ × ℕ)) : UGraph n :=
  { adj := fun x y => x ≠ y ∧ ((x.val, y.val) ∈ E ∨ (y.val, x.val) ∈ E)
    symm := by
      intro x y h
      exact ⟨fun hxy => h.1 hxy.symm, h.2.symm⟩
    loopless := by
      intro x h
      exact h.1 rfl }

end UGraph

open UGraph

variable {n : ℕ}

/-! ## Executable model (boolean adjacency matrix, vertex ids in `ℕ`) -/

/-- A concrete adjacency matrix: rows of booleans. -/
abbrev Adj := List (List Bool)

/-- Row lookup, `false` out of range. -/
def atRow : List Bool → ℕ → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: rest, k+1 => atRow rest k

/-- `getAdj a u v`: is the edge `(u, v)` present in `a`? -/
def getAdj (a : Adj) (u v : ℕ) : Bool :=
  match a[u]? with
  | none => false
  | some row => atRow row v

/-- Number of chosen neighbors of `w`. -/
def cardC (a : Adj) (chosen : List ℕ) (w : ℕ) : ℕ :=
  (chosen.filter (fun v => getAdj a v w)).length

/-- Prefer the greater count, breaking ties by the smaller vertex index. -/
def better (a : Adj) (chosen : List ℕ) (best candidate : ℕ) : ℕ :=
  let bestCount := cardC a chosen best
  let candidateCount := cardC a chosen candidate
  if candidateCount > bestCount ∨ (candidateCount = bestCount ∧ candidate < best) then
    candidate
  else
    best

/-- Canonical MCS pick among `rem`: maximum cardinality, smallest id on ties. -/
def bestPick (a : Adj) (chosen : List ℕ) (rem : List ℕ) : ℕ :=
  rem.foldl (better a chosen) (rem.headD 0)

/-- One MCS step on the state `(chosen in reverse, remaining)`. -/
def mcsStep (a : Adj) (st : List ℕ × List ℕ) : List ℕ × List ℕ :=
  let (chosen, rem) := st
  match rem with
  | [] => st
  | _ => let v := bestPick a chosen rem; (v :: chosen, rem.erase v)

/-- Set the undirected entry `(u, v)` to `present`. -/
def setEdge (a : Adj) (u v : ℕ) (present : Bool) : Adj :=
  List.mapIdx (fun i row =>
    List.mapIdx (fun j b =>
      if i = u ∧ j = v ∨ i = v ∧ j = u then present else b) row) a

/-- Insert the edge `(u, v)`. -/
def insertEdge (a : Adj) (u v : ℕ) : Adj := setEdge a u v true

/-- Delete the edge `(u, v)`. -/
def deleteEdge (a : Adj) (u v : ℕ) : Adj := setEdge a u v false

/-- The matrix is square of size `n`. -/
def WellShaped (n : ℕ) (a : Adj) : Prop :=
  a.length = n ∧ ∀ x : ℕ, x < n → ∃ row : List Bool, a[x]? = some row ∧ row.length = n

/-- The abstract graph denoted by a symmetric loop-free matrix. -/
def toUGraph (a : Adj) (hsymm : ∀ u v : ℕ, getAdj a u v = getAdj a v u)
    (hloop : ∀ u : ℕ, getAdj a u u = false) : UGraph n :=
  { adj := fun x y => getAdj a x.val y.val = true
    symm := by
      intro x y h
      rwa [hsymm x.val y.val] at h
    loopless := by
      intro x h
      have hx : getAdj a x.val x.val = false := hloop x.val
      simp [hx] at h }

/-! ## Executable dynamic updates -/

/-- The unchosen vertex ids, in increasing order. -/
def remOf (n : ℕ) (chosen : List ℕ) : List ℕ :=
  (List.range n).filter (fun v => decide (v ∉ chosen))

/-- The canonical MCS pick after the chosen prefix `chosen`. -/
def pickAt (a : Adj) (chosen : List ℕ) : ℕ :=
  bestPick a chosen (remOf a.length chosen)

/-- Run the specified number of greedy steps from a prefix and its remaining vertices. -/
def mcsFinish (a : Adj) (steps : ℕ) (state : List ℕ × List ℕ) : List ℕ :=
  ((List.range steps).foldl (fun state _ => mcsStep a state) state).1.reverse

/-- Keep the prefix `pref` and recompute the rest of the canonical ordering. -/
def regreedy (a : Adj) (pref : List ℕ) : List ℕ :=
  mcsFinish a (a.length - pref.length) (pref.reverse, remOf a.length pref)

/-- Canonical MCS ordering of `a`, computed from scratch. -/
def mcsOrder (a : Adj) : List ℕ :=
  mcsFinish a a.length ([], List.range a.length)

/-- Executable probe: the first position (starting at `k`) whose old choice
differs from the canonical pick after the preceding prefix of `order`. -/
def execFirstBreak (a : Adj) (order : List ℕ) : ℕ → List ℕ → Option ℕ
  | _, [] => none
  | k, x :: xs => if pickAt a (order.take k) = x then execFirstBreak a order (k + 1) xs else some k

/-- Position of the earlier endpoint in `order`. -/
def execEarlierPos (order : List ℕ) (u v : ℕ) : ℕ :=
  min (order.idxOf u) (order.idxOf v)

/-- Position of the later endpoint in `order`. -/
def execLaterPos (order : List ℕ) (u v : ℕ) : ℕ :=
  max (order.idxOf u) (order.idxOf v)

/-- The endpoint placed later in `order`. -/
def execLaterVert (order : List ℕ) (u v : ℕ) : ℕ :=
  if order.idxOf u ≤ order.idxOf v then v else u

/-- The old choices at the positions `earlierPos + 1, …, laterPos`, which are
the only positions an insertion probe examines. -/
def insertWindow (order : List ℕ) (u v : ℕ) : List ℕ :=
  (order.drop (execEarlierPos order u v + 1)).take
    (execLaterPos order u v - execEarlierPos order u v)

/-- Insertion probe on the post-insertion matrix `a`. -/
def insertProbe (a : Adj) (order : List ℕ) (u v : ℕ) : Option ℕ :=
  execFirstBreak a order (execEarlierPos order u v + 1) (insertWindow order u v)

/-- Executable insertion update on the post-insertion matrix `a`: probe the
window, regreedy from the first break, keep `order` if nothing breaks. -/
def execInsertUpdate (a : Adj) (order : List ℕ) (u v : ℕ) : List ℕ :=
  match insertProbe a order u v with
  | none => order
  | some k => regreedy a (order.take k)

/-- Executable deletion update on the post-deletion matrix `a`: probe the
single position `laterPos`, regreedy from it if the probe fires. -/
def execDeleteUpdate (a : Adj) (order : List ℕ) (u v : ℕ) : List ℕ :=
  if pickAt a (order.take (execLaterPos order u v)) = execLaterVert order u v then order
  else regreedy a (order.take (execLaterPos order u v))

/-! ## Operational cost (unit-cost query model)

Each call of `pickAt` in a probe and each MCS step of a regreedy costs one
unit.  The instrumented functions below follow the control flow of the
executable updates exactly and additionally return the number of units spent.
-/

/-- One MCS step, returning `1` if a vertex was picked. -/
def mcsStepC (a : Adj) (st : List ℕ × List ℕ) : (List ℕ × List ℕ) × ℕ :=
  match st.2 with
  | [] => (st, 0)
  | _ => (mcsStep a st, 1)

/-- Instrumented `regreedy`. -/
def regreedyC (a : Adj) (pref : List ℕ) : List ℕ × ℕ :=
  let r := (List.range (a.length - pref.length)).foldl
    (fun s _ => let t := mcsStepC a s.1; (t.1, s.2 + t.2))
    ((pref.reverse, remOf a.length pref), 0)
  (r.1.1.reverse, r.2)

/-- Instrumented `execFirstBreak`. -/
def execFirstBreakC (a : Adj) (order : List ℕ) : ℕ → List ℕ → Option ℕ × ℕ
  | _, [] => (none, 0)
  | k, x :: xs =>
      if pickAt a (order.take k) = x then
        let r := execFirstBreakC a order (k + 1) xs
        (r.1, r.2 + 1)
      else (some k, 1)

/-- Instrumented `insertProbe`. -/
def insertProbeC (a : Adj) (order : List ℕ) (u v : ℕ) : Option ℕ × ℕ :=
  execFirstBreakC a order (execEarlierPos order u v + 1) (insertWindow order u v)

/-- Instrumented `execInsertUpdate`. -/
def execInsertUpdateC (a : Adj) (order : List ℕ) (u v : ℕ) : List ℕ × ℕ :=
  let p := insertProbeC a order u v
  match p.1 with
  | none => (order, p.2)
  | some k => let r := regreedyC a (order.take k); (r.1, p.2 + r.2)

/-- Instrumented `execDeleteUpdate`. -/
def execDeleteUpdateC (a : Adj) (order : List ℕ) (u v : ℕ) : List ℕ × ℕ :=
  if pickAt a (order.take (execLaterPos order u v)) = execLaterVert order u v then (order, 1)
  else let r := regreedyC a (order.take (execLaterPos order u v)); (r.1, 1 + r.2)

end DynamicMcs
-- END DEFS
