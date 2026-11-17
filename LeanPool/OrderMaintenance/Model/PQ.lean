/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Model.State


/-!
# Level F: the bucket priority queue (`prototype/pq.py`)

Quiet chunks with size `> theta`, in buckets indexed by size. A bucket is a doubly linked list
of chunks (`pqHead`, `pqNext`, `pqPrev`), pushed and popped at its head, so `pop_max` takes the
most recently added chunk of the largest bucket. Non-empty buckets form a sorted doubly linked
list (`nbNext`, `nbPrev`, `pqLo`, `pqHi`). Bucket and chunk "none" is 0: sizes in the queue
exceed `theta ≥ 1`.
-/


@[expose] public section

namespace OrderMaintenance.Model

/-- Test whether the priority queue has any nonempty bucket. -/
def pqEmpty : CM Bool := return (← get).pqHi == 0

/-- Make empty bucket `s` non-empty, right after non-empty bucket `p` (0: new minimum). -/
def pqLinkAfter (s p : Nat) : CM Unit := do
  let st ← get
  let n := if p == 0 then st.pqLo else st.nbNext.getX p
  if p == 0 then modify fun st => { st with pqLo := s }
  else modify fun st => { st with nbNext := st.nbNext.setX p s }
  modify fun st => { st with nbPrev := st.nbPrev.setX s p, nbNext := st.nbNext.setX s n }
  if n != 0 then modify fun st => { st with nbPrev := st.nbPrev.setX n s }
  else modify fun st => { st with pqHi := s }

/-- Push a chunk into a bucket, linking the bucket after its predecessor if it was empty. -/
def pqAdd (c s p : Nat) : CM Unit := do
  let st ← get
  let hd := st.pqHead.getX s
  if hd != NIL then
    -- push c at the head of bucket s
    modify fun st => { st with
      pqNext := st.pqNext.setX c hd, pqPrev := (st.pqPrev.setX hd c).setX c NIL,
      pqHead := st.pqHead.setX s c }
  else
    modify fun st => { st with
      pqNext := st.pqNext.setX c NIL, pqPrev := st.pqPrev.setX c NIL,
      pqHead := st.pqHead.setX s c }
    pqLinkAfter s p
  modify fun st => { st with pqWhere := st.pqWhere.setX c s }

/-- Remove a queued chunk and unlink its bucket if the bucket becomes empty. -/
def pqDel (c : Nat) : CM Unit := do
  let st ← get
  let s := st.pqWhere.getX c
  if s == 0 then guard "pq: delete of an absent chunk"
  modify fun st => { st with pqWhere := st.pqWhere.setX c 0 }
  let nx := st.pqNext.getX c
  let pv := st.pqPrev.getX c
  if pv != NIL then modify fun st => { st with pqNext := st.pqNext.setX pv nx }
  else modify fun st => { st with pqHead := st.pqHead.setX s nx }
  if nx != NIL then modify fun st => { st with pqPrev := st.pqPrev.setX nx pv }
  if (← get).pqHead.getX s == NIL then
    -- bucket s became empty: unlink it
    let st ← get
    let p := st.nbPrev.getX s
    let n := st.nbNext.getX s
    modify fun st => { st with nbPrev := st.nbPrev.setX s 0, nbNext := st.nbNext.setX s 0 }
    if p != 0 then modify fun st => { st with nbNext := st.nbNext.setX p n }
    else modify fun st => { st with pqLo := n }
    if n != 0 then modify fun st => { st with nbPrev := st.nbPrev.setX n p }
    else modify fun st => { st with pqHi := p }

/-- Insert `c` at bucket `s`, scanning downward for the predecessor bucket (the slow path; it is
never taken when `s = theta + 1`). -/
def pqInsertScan (c s : Nat) : CM Unit := do
  let st ← get
  let th := st.P.theta
  let mut p := s - 1
  for _ in List.range (s) do
    if p > th && st.pqHead.getX p == NIL then
      p := p - 1
    else break
  pqAdd c s (if p > th then p else 0)

/-- The size of quiet chunk `c` changed from `old` to `new`. -/
def pqAdjust (c old new : Nat) : CM Unit := do
  let th := (← getP).theta
  if old ≤ th && th < new then pqInsertScan c new
  else if new ≤ th && th < old then pqDel c
  else if old > th && new > th then
    let st ← get
    if new == old + 1 then
      -- the bucket of `old` has more than one chunk iff c is not alone in it
      let alone := st.pqHead.getX old == c && st.pqNext.getX c == NIL
      let p := if alone then st.nbPrev.getX old else old
      pqDel c
      pqAdd c new p
    else if new + 1 == old then
      let p := st.nbPrev.getX old
      pqDel c
      pqAdd c new p
    else
      pqDel c
      pqInsertScan c new

/-- Queue a chunk exactly when its size exceeds the quiet-chunk threshold. -/
def pqEnterIfAbove (c : Nat) : CM Unit := do
  let s := (← getC c).size
  if s > (← getP).theta then pqInsertScan c s

/-- Remove and return the head chunk of the largest nonempty bucket. -/
def pqPopMax : CM Nat := do
  let st ← get
  let c := st.pqHead.getX st.pqHi
  if c == NIL then guard "pq: pop from an empty queue"
  pqDel c
  return c

end OrderMaintenance.Model
