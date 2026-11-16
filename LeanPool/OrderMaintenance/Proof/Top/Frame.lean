/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.Struct


/-!
# M5: frames

`SameTree s s'`: `s'` differs from `s` at most in the range pointers (`first`, `last`) and the
stored weights of nodes, in paths and in tags. The live tree, the tables, the weights and
  everything computed from them
are then the same (`SameTree.*`), and so are the parts of the invariant that read only those.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
structure SameTree (s s' : TS) : Prop where
  P : s'.P = s.P
  size : s'.nodes.size = s.nodes.size
  cin : s'.cin = s.cin
  lpar : s'.lpar = s.lpar
  node : ∀ u, nd s' u = { nd s u with first := (nd s' u).first, last := (nd s' u).last, weight
    := (nd s' u).weight }

namespace SameTree

variable {s s' : TS} (h : SameTree s s')
include h

theorem height (u : Nat) : (nd s' u).height = (nd s u).height := by rw [h.node u]
theorem livePar (u : Nat) : (nd s' u).livePar = (nd s u).livePar := by rw [h.node u]
theorem children (u : Nat) : (nd s' u).children = (nd s u).children := by rw [h.node u]
theorem table (u : Nat) : (nd s' u).table = (nd s u).table := by rw [h.node u]
theorem inTables (u : Nat) : (nd s' u).inTables = (nd s u).inTables := by rw [h.node u]
theorem draining (u : Nat) : (nd s' u).draining = (nd s u).draining := by rw [h.node u]
theorem t1 (u : Nat) : (nd s' u).t1 = (nd s u).t1 := by rw [h.node u]
theorem t2 (u : Nat) : (nd s' u).t2 = (nd s u).t2 := by rw [h.node u]
theorem side (u : Nat) : (nd s' u).side = (nd s u).side := by rw [h.node u]
theorem overflowOf (u : Nat) : (nd s' u).overflowOf = (nd s u).overflowOf := by rw [h.node u]
theorem alive (u : Nat) : (nd s' u).alive = (nd s u).alive := by rw [h.node u]

theorem ht (u : Nat) : ht s' u = ht s u := h.height u
theorem isN (u : Nat) : isN s' u ↔ isN s u := by unfold Top.isN; rw [h.size, h.alive]
theorem liveN (u : Nat) : liveN s' u ↔ liveN s u := by unfold Top.liveN; rw [h.isN, h.draining]
theorem ghostN (u : Nat) : ghostN s' u ↔ ghostN s u := by unfold Top.ghostN; rw [h.isN, h.draining]
theorem lpr (c : Nat) : lpr s' c = lpr s c := by unfold Top.lpr; rw [h.lpar]
theorem cinT (c : Nat) : cinT s' c = cinT s c := by unfold Top.cinT; rw [h.cin]
theorem order (u : Nat) : order s' u = order s u := by unfold Top.order Node.order; rw [h.table]
theorem labs (u : Nat) : labs s' u = labs s u := by unfold Top.labs; rw [h.table]
theorem lab (u e : Nat) : lab s' u e = lab s u e := by unfold Top.lab Node.lab?; rw [h.table]
theorem lab? (u e : Nat) : (nd s' u).lab? e = (nd s u).lab? e := by unfold Node.lab?; rw [h.table]
theorem srcOf (u : Nat) : srcOf s' u = srcOf s u := h.overflowOf u
theorem tabs (k e : Nat) : tabs s' k e = tabs s k e := by
  unfold Top.tabs; rw [h.cinT, h.inTables]
theorem par (k e : Nat) : par s' k e = par s k e := by
  unfold Top.par; rw [h.lpr, h.draining, h.t1, h.livePar, h.livePar]
theorem anc (c : Nat) : ∀ k, anc s' c k = anc s c k
  | 0 => rfl
  | 1 => h.lpr c
  | k + 2 => by
    change (nd s' (Top.anc s' c (k + 1))).livePar = (nd s (Top.anc s c (k + 1))).livePar
    rw [anc c (k + 1), h.livePar]
theorem tw (cl : List Nat) (u : Nat) : tw s' cl u = tw s cl u := by
  unfold Top.tw; simp only [h.ht, h.anc]
theorem ew (cl : List Nat) (u : Nat) : ew s' cl u = ew s cl u := by
  unfold Top.ew; rw [h.draining, h.t1, h.t2, h.tw, h.tw, h.tw]
theorem fundOf (cl : List Nat) (u : Nat) (hw : (nd s' u).weight = (nd s u).weight) :
    fundOf s' cl u = fundOf s cl u := by
  unfold Top.fundOf; rw [h.ew, hw]
theorem growth (cl : List Nat) (X : Nat) : growth s' cl X = growth s cl X := by
  unfold Top.growth
  simp only [h.order, h.liveN, h.tw, h.ht, h.P]
theorem oldLive (X : Nat) : oldLive s' X = oldLive s X := by
  unfold Top.oldLive; simp only [h.order, h.liveN]
theorem upChain : ∀ f v, Top.upChain s' f v = Top.upChain s f v
  | 0, _ => rfl
  | f + 1, v => by
    unfold Top.upChain; rw [h.livePar, upChain f]

end SameTree

theorem SameTree.refl (s : TS) : SameTree s s := ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩

end OrderMaintenance.Proof.Top
