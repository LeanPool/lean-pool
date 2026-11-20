/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Extracted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/StageComputability.lean.
The coded construction is shared over procedure computability and the existing state interface.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.CommonIdeal
public import LeanPool.TuringConeRigidity.Effective.StageEngineScan

/-!
# Shared coded finite-injury construction
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.StageEngineComputability
open Encodable UniformOracle EncodedForcing CodingForcing FiniteInjury StageRecords
open StageEngineScan
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S : Type} (I : StageEngine.StateInterface S) (C : StageEngine.Procedures)
  {O : Oracle}
  (hpair : Nat.RecursiveIn {oracleFunction O} (fun v => Part.some (C.pairProcedure v)))
  (hopen : Nat.RecursiveIn {oracleFunction O} (fun v => Part.some (C.openProcedure v)))

/-- Decode a priority state from its condition and finite priority records. -/
def state (v : ℕ) : S :=
  I.make (condition (Nat.unpair v).1) (members (Nat.unpair (Nat.unpair v).2).1)
    (members (Nat.unpair (Nat.unpair v).2).2)

/-- Compute the generic extension for the next unvisited requirement in the coded state. -/
def generic (v : ℕ) : ℕ := C.openProcedure
  (Nat.pair (nextVisit (Nat.unpair (Nat.unpair v).2).2) (Nat.unpair v).1)

/-- Canonicalize the condition code at its current active level. -/
def canonical (p : ℕ) : ℕ := levelCode p (active p)
theorem canonical_eq (p : ℕ) : canonical p = code (condition p) := rfl

/-- Compute the generic extension after canonicalizing the coded condition. -/
def genericCanonical (v : ℕ) : ℕ := C.openProcedure
  (Nat.pair (nextVisit (Nat.unpair (Nat.unpair v).2).2) (canonical (Nat.unpair v).1))

include hopen in
theorem generic_recursive :
    Nat.RecursiveIn {oracleFunction O} (fun v => Part.some (genericCanonical C
      v)) := by
  have hn := total_comp (nextVisit_recursive (O := {oracleFunction O}))
    (total_primrec (r.comp r))
  have hp := total_primrec (O := {oracleFunction O}) ((levelCode_primrec.comp
    Primrec.id active_primrec).comp f)
  have hh := total_comp hopen (total_pair hn hp)
  exact hh.of_eq (fun v => rfl)

theorem generic_eq (v : ℕ) :
    condition (genericCanonical C v) = StageEngine.generic I C (state I v) := by
  simp only [genericCanonical, canonical_eq, StageEngine.generic, state,
    I.seen_make, I.condition_make, nextVisit]

/-- Scan the coded priority state for an action at the given stage. -/
def stageAction (s v : ℕ) : ℕ :=
  scan C (genericCanonical C v) (Nat.unpair (Nat.unpair v).2).1 s

include hpair hopen in
theorem stageAction_recursive :
    Nat.RecursiveIn {oracleFunction O} (fun z =>
      Part.some (stageAction C (Nat.unpair z).1 (Nat.unpair z).2)) := by
  have hg := total_comp (generic_recursive C hopen) (total_primrec r)
  have hh := total_comp (scan_recursive C hpair) (total_pair (total_pair hg (total_primrec (f.comp
    (r.comp r)))) (total_primrec f))
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem stageAction_eq (s v : ℕ) :
    action (stageAction C s v) = StageEngine.stageAction I C s (state I v) := by
  rw [stageAction, scan_eq, action_actionCode, generic_eq I C]
  simp only [StageEngine.stageAction, state, I.done_make]

/-- Select either the generic coded condition or its chosen priority candidate. -/
def stageWord (z : ℕ) : ℕ :=
  let s := (Nat.unpair z).1
  let v := (Nat.unpair z).2
  let a := stageAction C s v
  let g := genericCanonical C v
  if a = 0 then g else candidate C (Nat.pair (a-1) g)

include hpair hopen in
theorem stageWord_recursive :
    Nat.RecursiveIn {oracleFunction O} (fun z => Part.some (stageWord C z)) := by
  have ha := stageAction_recursive C hpair hopen
  have hg := total_comp (generic_recursive C hopen) (total_primrec r)
  have hc := total_comp (candidate_recursive C hpair) (total_pair
    (total_comp (total_primrec (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))) ha) hg)
  have hpost := Primrec.ite (Primrec.eq.comp f (Primrec.const 0)) (f.comp r) (r.comp r)
  have hh := total_comp (total_primrec hpost) (total_pair ha (total_pair hg hc))
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem stageWord_eq (s v : ℕ) :
    condition (stageWord C (Nat.pair s v)) = StageEngine.stageWord I C s (state I v) := by
  have he := stageAction_eq I C s v
  unfold stageWord
  simp only [Nat.unpair_pair]
  by_cases ha : stageAction C s v = 0
  · have hn : StageEngine.stageAction I C s (state I v) = none := by
      simpa only [StageRecords.action, ite_eq_left ha] using he.symm
    simp [ha,StageEngine.stageWord,hn,generic_eq I C]
  · have hn : StageEngine.stageAction I C s (state I v) = some (stageAction C s v-1) := by
      simpa only [StageRecords.action,ite_eq_right ha] using he.symm
    simp [ha,StageEngine.stageWord,hn,candidate_eq,generic_eq I C]

/-- Append false to both words and set the next active stage. -/
def grow (p s : ℕ) : ℕ := Nat.pair (encode (left p ++ [false]))
  (Nat.pair (encode (right p ++ [false])) (s+1))

theorem grow_primrec : Primrec₂ grow := Primrec₂.natPair.comp
  (Primrec.encode.comp (Primrec.list_append.comp (left_primrec.comp Primrec.fst) (Primrec.const
    [false])))
  (Primrec₂.natPair.comp
    (Primrec.encode.comp (Primrec.list_append.comp (right_primrec.comp Primrec.fst) (Primrec.const
      [false])))
    (Primrec.succ.comp Primrec.snd))

@[simp] theorem condition_grow (p s : ℕ) :
    condition (grow p s) = atLevel (append (condition p) [false]) (s+1) := condition_code (atLevel
      (append (condition p) [false]) (s+1))

/-- Advance the coded priority state and update its completed and visited records. -/
def advance (z : ℕ) : ℕ :=
  let s := (Nat.unpair z).1
  let v := (Nat.unpair z).2
  let d := (Nat.unpair (Nat.unpair v).2).1
  let seen := (Nat.unpair (Nat.unpair v).2).2
  let a := stageAction C s v
  Nat.pair (grow (stageWord C z) s)
    (Nat.pair (doneUpdate d a) (seenReset (seenInsert seen (nextVisit seen)) a))

include hpair hopen in
theorem advance_recursive :
    Nat.RecursiveIn {oracleFunction O} (fun z => Part.some (advance C z)) := by
  have ha := stageAction_recursive C hpair hopen
  have hw := total_comp (total_primrec (grow_primrec.comp f r))
    (total_pair (stageWord_recursive C hpair hopen) (total_primrec f))
  have hd := total_comp (total_primrec (doneUpdate_primrec.comp f r))
    (total_pair (total_primrec (f.comp (r.comp r))) ha)
  have hs := total_primrec (O := {oracleFunction O}) (r.comp (r.comp r))
  have hn := total_comp nextVisit_recursive hs
  have hi := total_comp (total_primrec (seenInsert_primrec.comp f r)) (total_pair hs hn)
  have hreset := total_comp (total_primrec (seenReset_primrec.comp f r)) (total_pair hi ha)
  have hh := total_pair hw (total_pair hd hreset)
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem advance_eq (s v : ℕ) :
    state I (advance C (Nat.pair s v)) = StageEngine.advance I C s (state I v) := by
  unfold advance
  simp only [state, Nat.unpair_pair, condition_grow, stageWord_eq I C,
    members_doneUpdate, members_seenReset, members_seenInsert, stageAction_eq I C]
  simp only [StageEngine.advance, I.done_make, I.seen_make, nextVisit]

/-- The coded empty priority state. -/
def initial : ℕ := Nat.pair (code ⟨[],[],rfl,0⟩) (Nat.pair (encode ([] : List ℕ)) (encode ([] :
  List ℕ)))

/-- Iterate the coded priority-state transition from the empty state. -/
def construction : ℕ → ℕ :=
  recur (fun _ => initial) (fun v => advance C (Nat.unpair v).2) 0

include hpair hopen in
theorem construction_recursive :
    Nat.RecursiveIn {oracleFunction O} (fun s => Part.some (construction C s))
      := by
  have h := recur_recursive (total_primrec (Primrec.const initial))
    (total_comp (advance_recursive C hpair hopen) (total_primrec r))
  have hh := total_comp h (total_primrec (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id))
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem construction_eq (s : ℕ) :
    state I (construction C s) = StageEngine.construction I C s := by
  induction s with
  | zero => simp
    [construction,recur,initial,state,condition_code,members,record,StageEngine.construction]
  | succ s ih =>
    change state I (advance C (Nat.unpair (Nat.pair 0 (Nat.pair s (construction C s)))).2) = _
    rw [Nat.unpair_pair,advance_eq,ih]
    rfl

include hpair hopen in
theorem conditions_recursive :
    Nat.RecursiveIn {oracleFunction O}
      (fun s => Part.some (code (StageEngine.conditions I C s))) := by
  have h := total_comp (total_primrec ((levelCode_primrec.comp Primrec.id active_primrec).comp f))
    (construction_recursive C hpair hopen)
  apply h.of_eq
  intro s
  change Part.some (code (condition (Nat.unpair (construction C s)).1)) = _
  have he := congrArg I.condition (construction_eq I C s)
  simp only [state, I.condition_make] at he
  exact congrArg (fun p => Part.some (EncodedForcing.code p)) he

include hpair hopen in
theorem limits_recursive :
    Reduces (join (leftLimit (StageEngine.conditions I C)) (rightLimit (StageEngine.conditions
      I C)))
      O := by
  have hs := total_comp (conditions_recursive I C hpair hopen) (total_primrec (Primrec.succ.comp
    Primrec.nat_div2))
  have hbit : Primrec (fun v : ℕ => CommonIdeal.bit
      ((bif (Nat.unpair v).2.bodd then right (Nat.unpair v).1 else left (Nat.unpair v).1).getD
        (Nat.unpair v).2.div2 false)) := (Primrec.dom_bool CommonIdeal.bit).comp
    ((Primrec.list_getD false).comp
      (Primrec.cond (Primrec.nat_bodd.comp r) (right_primrec.comp f) (left_primrec.comp f))
      (Primrec.nat_div2.comp r))
  have h := total_comp (total_primrec hbit) (total_pair hs (total_primrec Primrec.id))
  apply RecursiveIn.iff_nat.mpr
  have hl (p : Condition) : left (code p) = p.left := congrArg Condition.left (condition_code p)
  have hr (p : Condition) : right (code p) = p.right := congrArg Condition.right (condition_code p)
  exact h.of_eq (fun n => by
    simp only [Nat.unpair_pair]
    cases hb : n.bodd <;> simp [oracleFunction,join,hb,leftLimit,rightLimit,CommonIdeal.bit,
      hl,hr,Nat.div2_val])

end
end TuringRigidity.StageEngineComputability

end OAI
