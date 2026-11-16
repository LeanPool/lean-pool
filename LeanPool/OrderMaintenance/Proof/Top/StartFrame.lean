/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.StartCtx


/-!
# M5: the top structure after `startDrain`, as views of the one before

`v1 = N`, `v2 = N + 1` (`N` the node count) are the new targets of `v`.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
theorem nd_ts (X : Core) (u : Nat) : nd (ts X) u = X.nodes.getX u := rfl

/-- What the views of the state after `startDrain` need. -/
structure SDHyps (s : Core) (v : Nat) (side : List (Nat × Side)) : Prop where
  hv : v < s.nodes.size
  hL : (nd (ts s) v).livePar < s.nodes.size
  hLv : (nd (ts s) v).livePar ≠ v
  tnd : (nd (ts s) v).inTables.Nodup
  tlt : ∀ T ∈ (nd (ts s) v).inTables, T < s.nodes.size
  ln : (sLeft (wiC s v) v side).Nodup
  rn : (sRight (wiC s v) v side).Nodup
  c1n : (sCh1 (wiC s v) v side).Nodup
  c2n : (sCh2 (wiC s v) v side).Nodup
  ent : ht (ts s) v - 1 ≠ 0 → ∀ e ∈ sEntries (wiC s v) v, e < s.nodes.size
  kid : ht (ts s) v ≠ 1 → ∀ e ∈ (nd (ts s) v).children, e < s.nodes.size

namespace SDHyps

variable {s : Core} {v : Nat} {side : List (Nat × Side)} (H : SDHyps s v side)
include H

local notation "N" => s.nodes.size
local notation "S'" => ts (sdS (wiC s v) v side)

omit H in
theorem wsize : (wiC s v).nodes.size = s.nodes.size := by simp [wiC]

theorem t_nd : ((wiC s v).nodes.getX v).inTables.Nodup := by
  rw [show ((wiC s v).nodes.getX v).inTables = (nd (ts s) v).inTables from (wiC_sameTree s
    v).inTables v]
  exact H.tnd
theorem t_lt : ∀ T ∈ ((wiC s v).nodes.getX v).inTables, T < (wiC s v).nodes.size := by
  rw [show ((wiC s v).nodes.getX v).inTables = (nd (ts s) v).inTables from (wiC_sameTree s
    v).inTables v,
    SDHyps.wsize]
  exact H.tlt
theorem t_hv : v < (wiC s v).nodes.size := by rw [SDHyps.wsize]; exact H.hv
theorem t_hL : ((wiC s v).nodes.getX v).livePar < (wiC s v).nodes.size := by
  rw [show ((wiC s v).nodes.getX v).livePar = (nd (ts s) v).livePar from (wiC_sameTree s
    v).livePar v,
    SDHyps.wsize]
  exact H.hL

theorem height (u : Nat) : (nd S' u).height = if u = N ∨ u = N + 1 then ht (ts s) v else ht (ts
  s) u := by
  rw [nd_ts, sdS_height H.ln H.rn H.t_nd H.t_lt, SDHyps.wsize, sd_h_eq]
  split
  · rfl
  · exact (wiC_sameTree s v).height u

section wfields
variable (u : Nat)
omit H in
theorem w_height : ((wiC s v).nodes.getX u).height = (nd (ts s) u).height := (wiC_sameTree s
  v).height u
omit H in
theorem w_alive : ((wiC s v).nodes.getX u).alive = (nd (ts s) u).alive := (wiC_sameTree s v).alive u
omit H in
theorem w_first : ((wiC s v).nodes.getX u).first = (nd (ts s) u).first := wiC_first s v u
omit H in
theorem w_last : ((wiC s v).nodes.getX u).last = (nd (ts s) u).last := wiC_last s v u
theorem w_weight : ((wiC s v).nodes.getX u).weight =
    if u = v then (nd (ts s) u).weight + 2 else (nd (ts s) u).weight := wiC_weight s v u H.hv
omit H in
theorem w_overflowOf : ((wiC s v).nodes.getX u).overflowOf = (nd (ts s) u).overflowOf :=
  (wiC_sameTree s v).overflowOf u
omit H in
theorem w_draining : ((wiC s v).nodes.getX u).draining = (nd (ts s) u).draining := (wiC_sameTree
  s v).draining u
omit H in
theorem w_t1 : ((wiC s v).nodes.getX u).t1 = (nd (ts s) u).t1 := (wiC_sameTree s v).t1 u
omit H in
theorem w_t2 : ((wiC s v).nodes.getX u).t2 = (nd (ts s) u).t2 := (wiC_sameTree s v).t2 u
omit H in
theorem w_side : ((wiC s v).nodes.getX u).side = (nd (ts s) u).side := (wiC_sameTree s v).side u
omit H in
theorem w_table : ((wiC s v).nodes.getX u).table = (nd (ts s) u).table := (wiC_sameTree s v).table u
omit H in
theorem w_inTables : ((wiC s v).nodes.getX u).inTables = (nd (ts s) u).inTables := (wiC_sameTree
  s v).inTables u
omit H in
theorem w_livePar : ((wiC s v).nodes.getX u).livePar = (nd (ts s) u).livePar := (wiC_sameTree s
  v).livePar u
omit H in
theorem w_children : ((wiC s v).nodes.getX u).children = (nd (ts s) u).children := (wiC_sameTree
  s v).children u
omit H in
theorem w_sideAround : sideAround ((wiC s v).nodes.getX u) v N (N + 1) = sideAround (nd (ts s)
  u) v N (N + 1) := by
  unfold sideAround; rw [SDHyps.w_draining, SDHyps.w_side]
end wfields

theorem alive (u : Nat) : (nd S' u).alive = if u = N ∨ u = N + 1 then true else (nd (ts s)
  u).alive := by
  rw [nd_ts, sdS_alive H.ln H.rn H.t_nd H.t_lt, SDHyps.wsize, SDHyps.w_alive]

theorem first (u : Nat) : (nd S' u).first = if u = N ∨ u = N + 1 then NIL else (nd (ts s)
  u).first := by
  rw [nd_ts, sdS_first H.ln H.rn H.t_nd H.t_lt, SDHyps.wsize, SDHyps.w_first]

theorem last (u : Nat) : (nd S' u).last = if u = N ∨ u = N + 1 then NIL else (nd (ts s) u).last
  := by
  rw [nd_ts, sdS_last H.ln H.rn H.t_nd H.t_lt, SDHyps.wsize, SDHyps.w_last]

theorem weight (u : Nat) : (nd S' u).weight =
    if u = N then ((sCh1 (wiC s v) v side).map (sWt (wiC s v) v)).sum
    else if u = N + 1 then ((sCh2 (wiC s v) v side).map (sWt (wiC s v) v)).sum
    else if u = v then (nd (ts s) u).weight + 2 else (nd (ts s) u).weight := by
  rw [nd_ts, sdS_weight H.ln H.rn H.t_nd H.t_lt H.t_hv H.t_hL, SDHyps.wsize, H.w_weight]

theorem overflowOf (u : Nat) : (nd S' u).overflowOf =
    if u = N ∨ u = N + 1 then v else (nd (ts s) u).overflowOf := by
  rw [nd_ts, sdS_overflowOf H.ln H.rn H.t_nd H.t_lt H.t_hv H.t_hL, SDHyps.wsize,
    SDHyps.w_overflowOf]
  by_cases h1 : u = N
  · rw [ite_eq_left h1, ite_eq_left (Or.inl h1)]
  · by_cases h2 : u = N + 1
    · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left (Or.inr h2)]
    · rw [ite_eq_right h1, ite_eq_right h2,
      ite_eq_right (show ¬(u = N ∨ u = N + 1) from fun h => h.elim h1 h2)]

theorem draining (u : Nat) : (nd S' u).draining =
    if u = v then true else if u = N ∨ u = N + 1 then false else (nd (ts s) u).draining := by
  rw [nd_ts, sdS_draining H.ln H.rn H.c1n H.c2n H.t_nd H.t_lt H.t_hv, SDHyps.wsize,
    SDHyps.w_draining]

theorem t1 (u : Nat) : (nd S' u).t1 = if u = v then N else if u = N ∨ u = N + 1 then NIL else
  (nd (ts s) u).t1 := by
  rw [nd_ts, sdS_t1 H.ln H.rn H.c1n H.c2n H.t_nd H.t_lt H.t_hv, SDHyps.wsize, SDHyps.w_t1]

theorem t2 (u : Nat) : (nd S' u).t2 =
    if u = v then N + 1 else if u = N ∨ u = N + 1 then NIL else (nd (ts s) u).t2 := by
  rw [nd_ts, sdS_t2 H.ln H.rn H.c1n H.c2n H.t_nd H.t_lt H.t_hv, SDHyps.wsize, SDHyps.w_t2]

theorem sides (u : Nat) : (nd S' u).side =
    if u = v then side else if u = N ∨ u = N + 1 then []
    else if u ∈ (nd (ts s) v).inTables then sideAround (nd (ts s) u) v N (N + 1) else (nd (ts s)
      u).side := by
  rw [nd_ts, sdS_side H.ln H.rn H.c1n H.c2n H.t_nd H.t_lt H.t_hv, SDHyps.wsize,
    SDHyps.w_inTables, SDHyps.w_side,
    SDHyps.w_sideAround]

theorem table (u : Nat) : (nd S' u).table =
    if u = N then evenTable s.P.beta (sLeft (wiC s v) v side)
    else if u = N + 1 then evenTable s.P.beta (sRight (wiC s v) v side)
    else if u ∈ (nd (ts s) v).inTables then
      aroundT (nd (ts s) u).table v N (N + 1) (roomL s.P.beta (nd (ts s) u).table v true)
        (roomL s.P.beta (nd (ts s) u).table v false)
    else (nd (ts s) u).table := by
  rw [nd_ts, sdS_table H.ln H.rn H.t_nd H.t_lt H.t_hv H.t_hL, SDHyps.wsize]
  simp only [sF, SDHyps.w_table, SDHyps.w_inTables]
  rfl

theorem inTables (u : Nat) : (nd S' u).inTables =
    if u = N ∨ u = N + 1 then (nd (ts s) v).inTables
    else (nd (ts s) u).inTables ++ (if ht (ts s) v - 1 ≠ 0 ∧ u ∈ sLeft (wiC s v) v side then [N]
      else []) ++
      (if ht (ts s) v - 1 ≠ 0 ∧ u ∈ sRight (wiC s v) v side then [N + 1] else []) := by
  rw [nd_ts, sdS_inTables H.ln H.rn H.t_nd H.t_lt
    (by rw [sd_h_eq, SDHyps.wsize]; exact H.ent), SDHyps.wsize, SDHyps.w_inTables,
      SDHyps.w_inTables, sd_h_eq]

theorem children (u : Nat) : (nd S' u).children =
    if u = v then [] else if u = N then sCh1 (wiC s v) v side else if u = N + 1 then sCh2 (wiC s
      v) v side
    else if u = (nd (ts s) v).livePar then
      (nd (ts s) (nd (ts s) v).livePar).children.replace1 v [N, N + 1]
    else (nd (ts s) u).children := by
  rw [nd_ts, sdS_children H.ln H.rn H.c1n H.c2n H.t_nd H.t_lt H.t_hv H.t_hL
    (by rw [SDHyps.w_livePar]; exact H.hLv), SDHyps.wsize, SDHyps.w_livePar, SDHyps.w_children,
      SDHyps.w_children]

theorem livePar (u : Nat) : (nd S' u).livePar =
    if u = v then NIL else if u = N ∨ u = N + 1 then (nd (ts s) v).livePar
    else if ht (ts s) v ≠ 1 ∧ u ∈ sCh2 (wiC s v) v side then N + 1
    else if ht (ts s) v ≠ 1 ∧ u ∈ sCh1 (wiC s v) v side then N
    else (nd (ts s) u).livePar := by
  rw [nd_ts, sdS_livePar H.ln H.rn H.c1n H.c2n H.t_nd H.t_lt H.t_hv H.t_hL
    (by rw [sd_h_eq, sd_kids_eq, SDHyps.wsize]; exact H.kid), SDHyps.wsize, SDHyps.w_livePar,
      SDHyps.w_livePar, sd_h_eq]

theorem cin (c : Nat) : cinT S' c =
    if ht (ts s) v - 1 = 0 then
      (if c ∈ sRight (wiC s v) v side then
        (if c ∈ sLeft (wiC s v) v side then cinT (ts s) c ++ [N] else cinT (ts s) c) ++ [N + 1]
      else (if c ∈ sLeft (wiC s v) v side then cinT (ts s) c ++ [N] else cinT (ts s) c))
    else cinT (ts s) c := by
  unfold cinT; rw [ts_cin, sdS_cin H.ln H.rn, SDHyps.wsize, sd_h_eq]; rfl

omit H in
theorem lpar (c : Nat) : lpr S' c =
    if ht (ts s) v = 1 then
      (if c ∈ sCh2 (wiC s v) v side then N + 1 else if c ∈ sCh1 (wiC s v) v side then N else lpr
        (ts s) c)
    else lpr (ts s) c := by
  unfold lpr; rw [ts_lpar, sdS_lpar, SDHyps.wsize, sd_h_eq]; rfl

omit H in
theorem P : (ts (sdS (wiC s v) v side)).P = s.P := by
  rw [ts_P]; exact (sdS_rest (t := wiC s v) (v := v) (side := side)).2.1
omit H in
theorem path : (ts (sdS (wiC s v) v side)).path = s.path := by
  rw [ts_path]; exact (sdS_rest (t := wiC s v) (v := v) (side := side)).1
theorem size : (ts (sdS (wiC s v) v side)).nodes.size = N + 2 := by
  rw [ts_nodes, sdS_size H.ln H.rn, SDHyps.wsize]
omit H in
theorem tag (c : Nat) : (ts (sdS (wiC s v) v side)).tag c = (ts s).tag c := by
  rw [ts_tag, ts_tag, (sdS_rest (t := wiC s v) (v := v) (side := side)).2.2]; rfl

end SDHyps

end OrderMaintenance.Proof.Top
