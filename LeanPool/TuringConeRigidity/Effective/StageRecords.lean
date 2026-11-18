/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/StageRecords.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.FiniteInjurySchedule
public import LeanPool.TuringConeRigidity.Effective.UniformOracle

/-!
# Stage Records
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.StageRecords
open Encodable UniformOracle FiniteInjurySchedule

/-- Iterate a natural-number state transition with the parameter and stage explicitly paired
into its input. -/
def recur (z : ℕ → ℕ) (f : ℕ → ℕ) (a : ℕ) : ℕ → ℕ
  | 0 => z a
  | n+1 => f (Nat.pair a (Nat.pair n (recur z f a n)))

theorem recur_recursive {O : Set (ℕ →. ℕ)} {z f : ℕ → ℕ}
    (hz : Nat.RecursiveIn O (fun a => Part.some (z a)))
    (hf : Nat.RecursiveIn O (fun a => Part.some (f a))) :
    Nat.RecursiveIn O (fun v => Part.some (recur z f (Nat.unpair v).1 (Nat.unpair v).2)) := by
  apply (Nat.RecursiveIn.prec hz hf).of_eq
  intro v
  generalize hv : Nat.unpair v = p
  obtain ⟨a,n⟩ := p
  simp only [Part.bind_eq_bind]
  clear hv
  induction n with
  | zero => rfl
  | succ n ih => simp only [ih,Part.bind_some,recur]

/-- Decode a finite priority record, using the empty list for an invalid code. -/
def record (n : ℕ) : List ℕ := (decode n).getD []
theorem record_primrec : Primrec record := Primrec.option_getD.comp Primrec.decode (Primrec.const
  [])

/-- The finite set of priorities occurring in the decoded record. -/
def members (n : ℕ) : Finset ℕ := (record n).toFinset

theorem mem_primrec : PrimrecRel (fun n i => i ∈ record n) := by
  have h := Primrec.nat_lt.comp (Primrec.list_idxOf.comp Primrec.snd (record_primrec.comp
    Primrec.fst))
    (Primrec.list_length.comp (record_primrec.comp Primrec.fst))
  exact h.of_eq (fun p => List.idxOf_lt_length_iff)

/-- The least priority absent from the decoded visited record. -/
noncomputable def nextVisit (n : ℕ) : ℕ := visit (members n)

theorem nextVisit_recursive {O : Set (ℕ →. ℕ)} :
    Nat.RecursiveIn O (fun n => Part.some (nextVisit n)) := by
  classical
  have h : Primrec (fun v : ℕ => if (Nat.unpair v).2 ∈ record (Nat.unpair v).1 then 1 else 0) :=
    Primrec.ite (mem_primrec.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp
      Primrec.unpair))
      (Primrec.const 1) (Primrec.const 0)
  apply (Nat.RecursiveIn.rfind (total_primrec h)).of_eq_tot
  intro n
  apply Nat.mem_rfind.mpr
  constructor
  · have hn : nextVisit n ∉ record n := by simpa [members,nextVisit] using visit_missing (members n)
    simp [hn]
  · intro i hi
    have hi' : i ∈ record n := by simpa [members] using before_visit (members n) hi
    simp [hi']

/-- Mark a positive-coded action done and retain only smaller prior completions. -/
def doneUpdate (n a : ℕ) : ℕ :=
  if a = 0 then n else encode ((a-1) :: (record n).filter (fun i => i < a-1))

/-- Insert a priority into the encoded visited record. -/
def seenInsert (n t : ℕ) : ℕ := encode (t :: record n)
/-- After a positive-coded action, retain only visited priorities at or below the acting
priority. -/
def seenReset (n a : ℕ) : ℕ :=
  if a = 0 then n else encode ((record n).filter (fun i => i < a))

/-- Decode an action code, with zero meaning no action. -/
def action (n : ℕ) : Option ℕ := if n = 0 then none else some (n-1)
/-- Encode an optional priority, reserving zero for no action. -/
def actionCode : Option ℕ → ℕ | none => 0 | some n => n+1

@[simp] theorem action_actionCode (a : Option ℕ) : action (actionCode a) = a := by
  cases a <;> simp [action,actionCode]

theorem filter_primrec : Primrec (fun p : ℕ × ℕ => (record p.1).filter (fun i => i < p.2)) := by
  have h := Primrec.listFilterMap (record_primrec.comp Primrec.fst)
    (Primrec.ite (Primrec.nat_lt.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂
  exact h.of_eq (fun p => by
    induction record p.1 with
    | nil => rfl
    | cons i l ih => by_cases hi : i < p.2 <;> simp [hi,ih])

theorem doneUpdate_primrec : Primrec₂ doneUpdate := by
  have ht : Primrec (fun p : ℕ × ℕ => p.2-1) := Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) Primrec.fst
    (Primrec.encode.comp (Primrec.list_cons.comp ht (filter_primrec.comp (Primrec.fst.pair ht))))

theorem seenInsert_primrec : Primrec₂ seenInsert := Primrec.encode.comp
  (Primrec.list_cons.comp Primrec.snd (record_primrec.comp Primrec.fst))

theorem seenReset_primrec : Primrec₂ seenReset := Primrec.ite
  (Primrec.eq.comp Primrec.snd (Primrec.const 0)) Primrec.fst (Primrec.encode.comp filter_primrec)

@[simp] theorem members_seenInsert (n t : ℕ) : members (seenInsert n t) = insert t (members n) := by
  simp [members,seenInsert,record]

theorem members_doneUpdate (n a : ℕ) : members (doneUpdate n a) = FiniteInjury.update (members n)
  (action a) := by
  by_cases ha : a = 0
  · simp [doneUpdate,ha,action,FiniteInjury.update]
  · ext i
    simp [doneUpdate,ha,action,FiniteInjury.update,members,record]

theorem members_seenReset (n a : ℕ) : members (seenReset n a) = reset (members n) (action a) := by
  by_cases ha : a = 0
  · simp [seenReset,ha,action,reset]
  · ext i
    simp only [seenReset,ite_eq_right ha,action,reset,members,record,encodek,Option.getD_some,
      List.mem_toFinset,List.mem_filter,decide_eq_true_eq,Finset.mem_filter]
    constructor
    · rintro ⟨hm,hi⟩; exact ⟨hm,by omega⟩
    · rintro ⟨hm,hi⟩; exact ⟨hm,by omega⟩

end TuringRigidity.StageRecords

end OAI
