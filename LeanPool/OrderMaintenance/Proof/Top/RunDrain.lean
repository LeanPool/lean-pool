/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.Struct


/-!
# M5: running a sweep step

`drainStep v` on a ghost `v` with a non-empty range, when its lookups succeed and its tag passes
the guard, moves one chunk to a target: `drainStep_move`. With an empty range it finishes the
drain (`finishDrain`).
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
section reads
variable {β : Type} (s : Core)

@[simp] theorem run_getN_bind (i : Nat) (k : Node → CM β) :
    (getN i >>= k).run s = (k (s.nodes.getX i)).run s := rfl
@[simp] theorem run_getPath_bind (c : Nat) (k : Array Nat → CM β) :
    (getPath c >>= k).run s = (k (s.path.getX c)).run s := rfl
@[simp] theorem run_getLpar_bind (c : Nat) (k : Nat → CM β) :
    (getLpar c >>= k).run s = (k (s.lpar.getX c)).run s := rfl
@[simp] theorem run_modN_bind (i : Nat) (f : Node → Node) (k : PUnit → CM β) :
    (modN i f >>= k).run s = (k ⟨⟩).run { s with nodes := s.nodes.modify i f } := rfl
@[simp] theorem run_modN (i : Nat) (f : Node → Node) :
    (modN i f).run s = .ok ⟨⟩ { s with nodes := s.nodes.modify i f } := rfl
@[simp] theorem run_setPathAt_bind (c j v : Nat) (k : PUnit → CM β) :
    (setPathAt c j v >>= k).run s =
      (k ⟨⟩).run { s with path := s.path.setX c ((s.path.getX c).setX j v) } := rfl
@[simp] theorem run_modC_bind (i : Nat) (f : Chunk → Chunk) (k : PUnit → CM β) :
    (modC i f >>= k).run s = (k ⟨⟩).run { s with C := s.C.modify i f } := rfl

@[simp] theorem run_guard_bind {α : Type} (msg : String) (k : α → CM β) :
    (OrderMaintenance.Model.guard msg >>= k).run s = .error (.guard msg) s := rfl
@[simp] theorem run_belowOf_bind (h y : Nat) (k : Nat → CM β) :
    (belowOf h y >>= k).run s =
      (k (if h == 1 then y else (s.path.getX y).getX (h - 1))).run s := by
  unfold belowOf
  by_cases h1 : h = 1
  · simp [h1]
  · simp only [h1, beq_iff_eq, ite_false]; rfl

end reads

theorem guardTag_ok {s : Core} {c t : Nat} (h : TagOK s c t) : (guardTag c t).run s = .ok () s := by
  unfold guardTag
  obtain ⟨h1, h2⟩ := h
  simp only [cP, cN, cT] at h1 h2
  by_cases hp : (s.C.getX c).prev = NIL <;> by_cases hn : (s.C.getX c).next = NIL <;>
    simp_all [ Nat.not_le.mpr]

theorem guardedSetTag_bind {β : Type} {s : Core} {c t : Nat} (h : TagOK s c t) (k : PUnit → CM β) :
    (guardedSetTag c t >>= k).run s = (k ⟨⟩).run { s with C := s.C.modify c fun C => { C with tag := t } } := by
  unfold guardedSetTag
  rw [bind_assoc, run_bind, guardTag_ok h]
  rfl

/-! ### The sweep step's choices -/

section pick
variable (s : Core) (v : Nat)

/-- The entry below chunk `y` in ghost `v`'s table. -/
def belowY (y : Nat) : Nat :=
  if (s.nodes.getX v).height == 1 then y else (s.path.getX y).getX ((s.nodes.getX v).height - 1)

/-- The sweep moves the first chunk of the range left, or else the last one right. -/
def goesLeft : Prop := lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).first) = some .left

instance : Decidable (goesLeft s v) := by unfold goesLeft; infer_instance

/-- The chunk moved. -/
def dsY : Nat := if goesLeft s v then (s.nodes.getX v).first else (s.nodes.getX v).last
/-- Its target. -/
def dsT : Nat := if goesLeft s v then (s.nodes.getX v).t1 else (s.nodes.getX v).t2

/-- The new tag of the moved chunk (fields `h`, `h+1` replaced). -/
def dsTag (pt tb pv vb : Nat) : Nat :=
  let h := (s.nodes.getX v).height
  let b := s.P.beta
  (s.C.getX (dsY s v)).tag - ((pv <<< (h * b)) ||| (vb <<< ((h - 1) * b))) +
    ((pt <<< (h * b)) ||| (tb <<< ((h - 1) * b)))

/-- The state after the sweep step. -/
def dsS (tag : Nat) : Core :=
  let V := s.nodes.getX v
  let h := V.height
  let y := dsY s v
  let t := dsT s v
  let T := s.nodes.getX t
  let cy := s.C.getX y
  let s1 := { s with C := s.C.modify y fun C => { C with tag := tag } }
  let s2 := { s1 with path := s1.path.setX y ((s1.path.getX y).setX h t) }
  let s3 := if V.first == V.last then { s2 with nodes := s2.nodes.modify v fun n => { n with first := NIL, last := NIL } }
    else if goesLeft s v then { s2 with nodes := s2.nodes.modify v fun n => { n with first := cy.next } }
    else { s2 with nodes := s2.nodes.modify v fun n => { n with last := cy.prev } }
  if goesLeft s v then
    let s4 := if T.first == NIL then { s3 with nodes := s3.nodes.modify t fun n => { n with first := y } } else s3
    { s4 with nodes := s4.nodes.modify t fun n => { n with last := y } }
  else
    let s4 := if T.last == NIL then { s3 with nodes := s3.nodes.modify t fun n => { n with last := y } } else s3
    { s4 with nodes := s4.nodes.modify t fun n => { n with first := y } }

end pick

/-- **A sweep step that moves a chunk.** -/
theorem drainStep_move {s : Core} {v : Nat} (hal : (s.nodes.getX v).alive = true)
    (hf : (s.nodes.getX v).first ≠ NIL)
    (hside : goesLeft s v ∨
      lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).first) = some .right ∧
      lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).last) = some .right)
    (hsz : (s.nodes.getX v).height + 1 < (s.path.getX (dsY s v)).size)
    {pt tb pv vb : Nat}
    (hpt : (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1))).lab? (dsT s v) = some pt)
    (htb : (s.nodes.getX (dsT s v)).lab? (belowY s v (dsY s v)) = some tb)
    (hpv : (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1))).lab? v = some pv)
    (hvb : (s.nodes.getX v).lab? (belowY s v (dsY s v)) = some vb)
    (hold : (pv <<< ((s.nodes.getX v).height * s.P.beta)) |||
        (vb <<< (((s.nodes.getX v).height - 1) * s.P.beta)) ≤ (s.C.getX (dsY s v)).tag)
    (hok : TagOK s (dsY s v) (dsTag s v pt tb pv vb)) :
    (drainStep v).run s = .ok true (dsS s v (dsTag s v pt tb pv vb)) := by
  unfold drainStep
  simp only [run_getP_bind, run_getN_bind, hal, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [ite_eq_right (by simpa using hf)]
  simp only [run_belowOf_bind]
  by_cases hl : goesLeft s v
  · have hy : dsY s v = (s.nodes.getX v).first := by simp [dsY, hl]
    have ht : dsT s v = (s.nodes.getX v).t1 := by simp [dsT, hl]
    have hl' := hl
    unfold goesLeft belowY at hl'
    unfold belowY at htb hvb
    rw [hy] at hsz hpt hpv hold hok htb hvb
    rw [ht] at hpt htb
    rw [hl']
    simp only [run_pure_bind, beq_self_eq_true, ite_true, run_getN_bind, run_getPath_bind,
      ite_eq_right (Nat.not_le.mpr hsz), hpt, htb, hpv, hvb, run_getC_bind, ite_eq_right (Nat.not_lt.mpr hold)]
    simp only [dsTag, hy] at hok
    rw [guardedSetTag_bind hok]
    simp only [run_setPathAt_bind, dsS, dsY, dsT, ite_eq_left hl, dsTag]
    split <;> split <;> simp_all
  · have hr := hside.resolve_left hl
    have hy : dsY s v = (s.nodes.getX v).last := by simp [dsY, hl]
    have ht : dsT s v = (s.nodes.getX v).t2 := by simp [dsT, hl]
    obtain ⟨hr1, hr2⟩ := hr
    unfold belowY at hr1 hr2 htb hvb
    rw [hy] at hsz hpt hpv hold hok htb hvb
    rw [ht] at hpt htb
    rw [hr1]
    simp only [run_pure_bind, show (Side.right == Side.left) = false from rfl, Bool.false_eq_true,
      ite_false, run_belowOf_bind, hr2, bne_self_eq_false, run_getN_bind, run_getPath_bind,
      ite_eq_right (Nat.not_le.mpr hsz), hpt, htb, hpv, hvb, run_getC_bind, ite_eq_right (Nat.not_lt.mpr hold)]
    simp only [dsTag, hy] at hok
    rw [guardedSetTag_bind hok]
    simp only [run_setPathAt_bind, dsS, dsY, dsT, ite_eq_right hl, dsTag]
    split <;> split <;> simp_all

end OrderMaintenance.Proof.Top
