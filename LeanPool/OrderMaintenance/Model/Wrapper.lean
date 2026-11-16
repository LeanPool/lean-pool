/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Model.Core
public import LeanPool.OrderMaintenance.Spec


/-!
# Level F: the full structure (`prototype/wrapper.py`)

Deletion by tombstones and growth by incremental global rebuilding on top of the insert-only
core. `cur` answers all queries. When `cur` is half full, or too few of its elements are live,
a fresh core `nxt` is prepared and then filled in the background, `K_B` steps per operation.

Handles are the insertion counter, so the `k`-th insertion returns handle `k`, exactly the
element names of `OrderMaintenance.Spec`.

The parameters of a new core are given by a function `mk : Nat → Params` of the capacity.
-/


@[expose] public section

namespace OrderMaintenance.Model

/-- The minimum initial core capacity, equal to 64. -/
def minimumCapacity : Nat := 64

/-- The external handle interface with incremental copying into a replacement core. -/
structure OrderMaintenance where
  /-- Current core answering external operations. -/
  cur : Core
  /-- Handle → element index in `cur` (0: absent). -/
  curIdx : Array Nat := #[]
  /-- Replacement core being prepared and filled, if rebuilding. -/
  nxt : Option Core := none
  /-- External handle to element index in the replacement core. -/
  nxtIdx : Array Nat := #[]
  /-- Next current-core element to copy during rebuilding. -/
  cursor : Nat := NIL
  /-- Copying starts only once `nxt` is fully prepared. -/
  cursorSet : Bool := false
  /-- Number of live external handles. -/
  live : Nat := 0
  /-- Next fresh external handle. -/
  nextHandle : Nat := 0
  /-- Number of completed wrapper rebuilds. -/
  rebuilds : Nat := 0
  /-- Copying budget per external operation. -/
  KB : Nat
  deriving Inhabited

/-- Wrapper computations that report an error instead of returning a partially updated wrapper. -/
abbrev WM := Except Err

/-- Run a core computation and return its result and state on success. -/
def runCore {α : Type} (c : Core) (act : CM α) : WM (α × Core) :=
  match act.run c with
  | .ok a s => .ok (a, s)
  | .error e _ => .error e

/-- Run a core action on `cur`. The core is moved out of `om` first, so that its arrays stay
unshared and are updated in place by compiled code. -/
def OrderMaintenance.onCur {α : Type} (om : OrderMaintenance) (act : CM α) : WM (α ×
  OrderMaintenance) := do
  let cur := om.cur
  let om := { om with cur := default }
  let (a, cur) ← runCore cur act
  return (a, { om with cur := cur })

/-- Construct a core with the supplied parameters, optionally deferring top-tree preparation. -/
def newCore (P : Params) (lazy : Bool) : WM Core :=
  Prod.snd <$> runCore { P := P } (initCore lazy)

/-- Construct the empty external interface with a prepared initial core. -/
def OrderMaintenance.init (mk : Nat → Params) (KB : Nat) : WM OrderMaintenance := do
  return { cur := ← newCore (mk minimumCapacity) false, KB := KB }

/-- Capacity of the next core (`docs/PROOF.md` §2.7, Lemma W). -/
def OrderMaintenance.nextCapacity (om : OrderMaintenance) : Nat :=
  let prep := om.cur.P.L + 2
  let mirrored := (om.cur.count + prep) / (om.KB - 1) + 1
  4 * max (om.live + mirrored) 16

/-- Copy one element of `cur` at the cursor into `nxt`, if it is live. -/
def copyAtCursor (om : OrderMaintenance) (nxt : Core) : WM (OrderMaintenance × Core) := do
  let e := om.cur.E.getX om.cursor
  if e.live then
    let (y, n') ← runCore nxt (insertAfter nxt.tail e.h)
    return ({ om with nxtIdx := om.nxtIdx.setX e.h y, cursor := e.next }, n')
  else
    return ({ om with cursor := e.next }, nxt)

/-- `nxt` replaces `cur`. -/
def OrderMaintenance.swap (om : OrderMaintenance) (nxt : Core) : OrderMaintenance :=
  { om with cur := nxt, curIdx := om.nxtIdx, nxt := none, nxtIdx := #[] }

/-- The rebuild loop, with `budget` steps left: each iteration spends one unit, except the one
that sets the cursor (`fuel` bounds the iterations). -/
def rebuildLoop (om : OrderMaintenance) (nxt : Core) : Nat → Nat → WM OrderMaintenance
  | 0, _ => return { om with nxt := some nxt }
  | fuel + 1, budget =>
    if budget = 0 then return { om with nxt := some nxt }
    else if !om.cursorSet then do
      let (ready, n') ← runCore nxt prepareStep
      if ready then
        rebuildLoop { om with cursor := (om.cur.E.getX om.cur.head).next, cursorSet := true } n'
          fuel budget
      else rebuildLoop om n' fuel (budget - 1)
    else if om.cursor = NIL then return om.swap nxt
    else do
      let (om', n') ← copyAtCursor om nxt
      if om'.cursor = NIL then return om'.swap n'
      else rebuildLoop om' n' fuel (budget - 1)

/-- The rebuild's share of one operation: exactly `K_B` steps (`wrapper.py` `_rebuild_step`). -/
def OrderMaintenance.rebuildStep (mk : Nat → Params) (om : OrderMaintenance) : WM
  OrderMaintenance := do
  match om.nxt with
  | none =>
    let N := om.cur.P.N
    if om.cur.count ≥ N / 2 || (N > minimumCapacity && om.live < N / 8) then
      let nxt ← newCore (mk om.nextCapacity) true
      return { om with nxt := some nxt, nxtIdx := #[], cursorSet := false,
                       rebuilds := om.rebuilds + 1 }
    return om
  | some nxt0 => rebuildLoop { om with nxt := none } nxt0 (om.KB + 1) om.KB

/-- Mirror an insertion into `nxt`, if its anchor is already copied. -/
def OrderMaintenance.mirrorInsert (om : OrderMaintenance) (hx : Option Nat) (hy : Nat) : WM
  OrderMaintenance :=
  match om.nxt with
  | none => return om
  | some nxt =>
    let copied := match hx with
      | none => true
      | some x => om.nxtIdx.getX x != 0
    if om.cursorSet && copied then do
      let om := { om with nxt := none }
      let xn := match hx with
        | none => nxt.head
        | some x => om.nxtIdx.getX x
      let (y', n') ← runCore nxt (insertAfter xn hy)
      return { om with nxt := some n', nxtIdx := om.nxtIdx.setX hy y' }
    else return om

/-- Mirror a deletion into `nxt`, if the element is already copied. -/
def OrderMaintenance.mirrorDelete (om : OrderMaintenance) (x : Nat) : WM OrderMaintenance :=
  match om.nxt with
  | none => return om
  | some nxt =>
    let xn := om.nxtIdx.getX x
    if xn != 0 then do
      let om := { om with nxt := none }
      let (_, n') ← runCore nxt (markDead xn)
      return { om with nxt := some n', nxtIdx := om.nxtIdx.setX x 0 }
    else return om

/-- Allocate a fresh handle and insert it at the front or after a live handle. -/
def OrderMaintenance.insert (mk : Nat → Params) (om : OrderMaintenance) (hx : Option Nat) :
  WM (Nat × OrderMaintenance) := do
  let hy := om.nextHandle
  let xi := match hx with
    | none => om.cur.head
    | some x => om.curIdx.getX x
  let (y, om) ← om.onCur (insertAfter xi hy)
  let om ← { om with nextHandle := hy + 1, curIdx := om.curIdx.setX hy y }.mirrorInsert hx hy
  return (hy, ← { om with live := om.live + 1 }.rebuildStep mk)

/-- Delete a live handle and mirror the deletion into a replacement core. -/
def OrderMaintenance.delete (mk : Nat → Params) (om : OrderMaintenance) (x : Nat) : WM
  OrderMaintenance := do
  let (_, om) ← om.onCur (markDead (om.curIdx.getX x))
  let om ← { om with curIdx := om.curIdx.setX x 0 }.mirrorDelete x
  { om with live := om.live - 1 }.rebuildStep mk

/-- Compare two live external handles using the current core’s order labels. -/
def OrderMaintenance.order (om : OrderMaintenance) (x y : Nat) : WM Bool :=
  Prod.fst <$> runCore om.cur (OrderMaintenance.Model.order (om.curIdx.getX x) (om.curIdx.getX y))

/-- One operation of the specification's interface. The `k`-th insertion returns handle `k`,
which is the specification's name for the new element. -/
def OrderMaintenance.apply (mk : Nat → Params) (om : OrderMaintenance) :
  _root_.OrderMaintenance.Spec.Op → WM (_root_.OrderMaintenance.Spec.Ans × OrderMaintenance)
  | .insertFirst => do
    let (_, om) ← om.insert mk none
    return (.inserted, om)
  | .insertAfter x => do
    let (_, om) ← om.insert mk (some x)
    return (.inserted, om)
  | .delete x => do
    let om ← om.delete mk x
    return (.deleted, om)
  | .order x y => do
    let b ← om.order x y
    return (.bool b, om)

/-- The answers to a sequence of operations. -/
def OrderMaintenance.runOps (mk : Nat → Params) : OrderMaintenance → List
  _root_.OrderMaintenance.Spec.Op → WM (List _root_.OrderMaintenance.Spec.Ans)
  | _, [] => pure []
  | om, op :: ops => do
    let (a, om) ← om.apply mk op
    let as ← OrderMaintenance.runOps mk om ops
    return a :: as

end OrderMaintenance.Model
