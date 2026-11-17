/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.TopFrame
public import LeanPool.OrderMaintenance.Proof.Cost.CDrive


/-!
# Reservation: splitting a popped chunk

`splitChunkStart x` allocates two chunks `y`, `z`, links them around `x`, starts the top
structure's insertion job (`insertAround`) and marks the family. Given that the job starts (the top
structure's contract, proved with the top-structure lemmas), the result is described field by
field.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- The family's bookkeeping after the job `job` started. -/
def markState (t : Core) (x y z : Nat) (job : Job) : Core :=
  let t1 := { t with C := t.C.modify x fun C => { C with st := .splitting, l := y, r := z } }
  let t2 := { t1 with C := t1.C.modify y fun C => { C with st := .overflow, src := x } }
  let t3 := { t2 with C := t2.C.modify z fun C => { C with st := .overflow, src := x } }
  { t3 with resJob := some job }

theorem markSplit_run (t : Core) (x y z : Nat) (job : Job) :
    (markSplit x y z job).run t = .ok () (markState t x y z job) := rfl

theorem splitChunkStart_ok {s : Core} {x : Nat} {job : Job} {s2 : Core}
    (hx : x ≠ NIL) (hxs : x < s.C.size)
    (hj : (insertAround x s.C.size (s.C.size + 1)).run
      (linkChunkPair (push2 s) x s.C.size (s.C.size + 1)) = .ok job s2) :
    (splitChunkStart x).run s = .ok () (markState s2 x s.C.size (s.C.size + 1) job) := by
  unfold splitChunkStart
  simp only [run_get_bind, run_require_bind]
  rw [ite_eq_left (by simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]; exact ⟨hx, hxs⟩)]
  simp only [run_newChunk_bind, run_modify_bind, Array.size_push]
  have hps : ({ ({ s with C := s.C.push {} } : Core) with C := (s.C.push {}).push {} } : Core) =
      push2 s := rfl
  rw [hps, run_bind, hj]
  rfl

end OrderMaintenance.Proof
