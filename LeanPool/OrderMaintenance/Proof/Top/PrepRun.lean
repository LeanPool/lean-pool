/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.ArrayLemmas
public import LeanPool.OrderMaintenance.Proof.Top.PresStart
public import LeanPool.OrderMaintenance.Proof.Cost.Fresh


/-!
# M5: the deferred construction of the initial chain (runs of `initStep`)
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-! ### Arrays as total maps -/

/-- The new chain node of height `pr.h`, before it is linked from below. -/
def chainNew (P : Params) (pr : Prep) (n : Node) : Node :=
  { n with
    children := [pr.below], table := [(pr.below, 1 <<< (P.beta - 1))],
    weight := 1, first := pr.chunk, last := pr.chunk }

/-- The prep record after building height `pr.h` as node `v`. -/
def prepNext (P : Params) (pr : Prep) (v : Nat) : Prep :=
  { pr with
    h := pr.h + 1, below := v, path := pr.path.setX pr.h v,
    tag := pr.tag ||| ((1 <<< (P.beta - 1)) <<< ((pr.h - 1) * P.beta)) }

/-- A middle step: node `v = |nodes|` of height `pr.h ≥ 2`. -/
theorem initStep_mid (s : Core) (pr : Prep) (hp : s.prep = some pr) (h1 : pr.h ≠ 1) (hH : pr.h ≤ s.P.H) :
    initStep.run s = .ok false { s with
      nodes := ((s.nodes.push { height := pr.h }).modify s.nodes.size (chainNew s.P pr)).modify pr.below
        (fun n => { n with inTables := [s.nodes.size], livePar := s.nodes.size }),
      prep := some (prepNext s.P pr s.nodes.size) } := by
  unfold initStep
  simp [hp, h1, hH, newNode, setInTables, prepNext]
  rfl

/-- The first step: reset, then node `1` of height `1` above chunk `pr.chunk`. -/
theorem initStep_first (s : Core) (pr : Prep) (hp : s.prep = some pr) (h1 : pr.h = 1) (hH : 1 ≤ s.P.H) :
    initStep.run s = .ok false { s with
      nodes := (#[default].push { height := 1 }).modify 1 (chainNew s.P pr), path := #[],
      cin := ((#[] : Array (List Nat)).setX pr.chunk []).setX pr.chunk [1],
      lpar := (#[] : Array Nat).setX pr.chunk 1,
      prep := some (prepNext s.P pr 1) } := by
  unfold initStep
  simp [hp, h1, hH, newNode, setInTables, prepNext, resetTop, setLpar]
  rfl

/-- The last step: store the path and the tag. -/
theorem initStep_last (s : Core) (pr : Prep) (hp : s.prep = some pr) (h1 : pr.h ≠ 1) (hH : s.P.H < pr.h) :
    initStep.run s = .ok true { s with
      path := s.path.setX pr.chunk pr.path, C := s.C.modify pr.chunk (fun C => { C with tag := pr.tag }),
      prep := none } := by
  unfold initStep
  simp [hp, h1, show ¬(pr.h ≤ s.P.H) by omega, setPath]
  rfl

end OrderMaintenance.Proof.Top
