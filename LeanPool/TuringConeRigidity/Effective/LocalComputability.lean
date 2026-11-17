/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/LocalComputability.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.LocalScan

/-!
# Local Computability
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.LocalComputability
open Encodable UniformOracle EncodedForcing CodingForcing FiniteInjury StageRecords
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Decode a local-stage state from its condition and two finite priority records. -/
def state (v : ℕ) : LocalStage.State :=
  ⟨condition (Nat.unpair v).1,members (Nat.unpair (Nat.unpair v).2).1,members (Nat.unpair
    (Nat.unpair v).2).2⟩

/-- Compute the local generic extension for the next unvisited requirement. -/
def generic (D : LocalInputs.Data) (v : ℕ) : ℕ := LocalStage.openProcedure D
  (Nat.pair (nextVisit (Nat.unpair (Nat.unpair v).2).2) (Nat.unpair v).1)

theorem open_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun v => Part.some (LocalStage.openProcedure D v))
      :=
  D.open_recursive

/-- Canonicalize a local condition code at its current active level. -/
def canonical (p : ℕ) : ℕ := levelCode p (active p)
theorem canonical_eq (p : ℕ) : canonical p = code (condition p) := rfl

/-- Compute the local open extension from the canonical condition and next unvisited
requirement. -/
def genericCanonical (D : LocalInputs.Data) (v : ℕ) : ℕ := LocalStage.openProcedure D
  (Nat.pair (nextVisit (Nat.unpair (Nat.unpair v).2).2) (canonical (Nat.unpair v).1))

theorem generic_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun v => Part.some (genericCanonical D v)) := by
  have hn := total_comp (nextVisit_recursive (O := {oracleFunction (D.bound)})) (total_primrec
    (r.comp r))
  have hp := total_primrec (O := {oracleFunction (D.bound)}) ((levelCode_primrec.comp Primrec.id
    active_primrec).comp f)
  have hh := total_comp (open_recursive D) (total_pair hn hp)
  exact hh.of_eq (fun v => rfl)

@[simp] theorem generic_eq (D : LocalInputs.Data) (v : ℕ) :
    condition (genericCanonical D v) = LocalStage.generic D (state v) := rfl

/-- Scan the coded local state for an eligible action at the given stage. -/
def stageAction (D : LocalInputs.Data) (s v : ℕ) : ℕ :=
  scan D (genericCanonical D v) (Nat.unpair (Nat.unpair v).2).1 s

theorem stageAction_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun z =>
      Part.some (stageAction D (Nat.unpair z).1 (Nat.unpair z).2)) := by
  have hg := total_comp (generic_recursive D) (total_primrec r)
  have hh := total_comp (scan_recursive D) (total_pair (total_pair hg (total_primrec (f.comp
    (r.comp r)))) (total_primrec f))
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

@[simp] theorem stageAction_eq (D : LocalInputs.Data) (s v : ℕ) :
    action (stageAction D s v) = LocalStage.stageAction D s (state v) := by
  rw [stageAction,scan_eq,action_actionCode,generic_eq]
  rfl

/-- Select the generic condition or the local candidate named by the stage action. -/
def stageWord (D : LocalInputs.Data) (z : ℕ) : ℕ :=
  let s := (Nat.unpair z).1
  let v := (Nat.unpair z).2
  let a := stageAction D s v
  let g := genericCanonical D v
  if a = 0 then g else candidate D (Nat.pair (a-1) g)

theorem stageWord_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun z => Part.some (stageWord D z)) := by
  have ha := stageAction_recursive D
  have hg := total_comp (generic_recursive D) (total_primrec r)
  have hc := total_comp (candidate_recursive D) (total_pair
    (total_comp (total_primrec (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))) ha) hg)
  have hpost := Primrec.ite (Primrec.eq.comp f (Primrec.const 0)) (f.comp r) (r.comp r)
  have hh := total_comp (total_primrec hpost) (total_pair ha (total_pair hg hc))
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem stageWord_eq (D : LocalInputs.Data) (s v : ℕ) :
    condition (stageWord D (Nat.pair s v)) = LocalStage.stageWord D s (state v) := by
  have he := stageAction_eq D s v
  unfold stageWord
  simp only [Nat.unpair_pair]
  by_cases ha : stageAction D s v = 0
  · have hn : LocalStage.stageAction D s (state v) = none := by
      simpa only [StageRecords.action, ite_eq_left ha] using he.symm
    simp [ha,LocalStage.stageWord,hn,generic_eq]
  · have hn : LocalStage.stageAction D s (state v) = some (stageAction D s v-1) := by
      simpa only [StageRecords.action,ite_eq_right ha] using he.symm
    simp [ha,LocalStage.stageWord,hn,candidate_eq,generic_eq]

/-- Append one false bit to both local words and set the next active stage. -/
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

/-- Advance the coded local state and update its completed and visited priority records. -/
def advance (D : LocalInputs.Data) (z : ℕ) : ℕ :=
  let s := (Nat.unpair z).1
  let v := (Nat.unpair z).2
  let d := (Nat.unpair (Nat.unpair v).2).1
  let seen := (Nat.unpair (Nat.unpair v).2).2
  let a := stageAction D s v
  Nat.pair (grow (stageWord D z) s)
    (Nat.pair (doneUpdate d a) (seenReset (seenInsert seen (nextVisit seen)) a))

theorem advance_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun z => Part.some (advance D z)) := by
  have ha := stageAction_recursive D
  have hw := total_comp (total_primrec (grow_primrec.comp f r))
    (total_pair (stageWord_recursive D) (total_primrec f))
  have hd := total_comp (total_primrec (doneUpdate_primrec.comp f r))
    (total_pair (total_primrec (f.comp (r.comp r))) ha)
  have hs := total_primrec (O := {oracleFunction (D.bound)}) (r.comp (r.comp r))
  have hn := total_comp nextVisit_recursive hs
  have hi := total_comp (total_primrec (seenInsert_primrec.comp f r)) (total_pair hs hn)
  have hreset := total_comp (total_primrec (seenReset_primrec.comp f r)) (total_pair hi ha)
  have hh := total_pair hw (total_pair hd hreset)
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem advance_eq (D : LocalInputs.Data) (s v : ℕ) :
    state (advance D (Nat.pair s v)) = LocalStage.advance D s (state v) := by
  unfold state advance
  simp only [Nat.unpair_pair,condition_grow,stageWord_eq,members_doneUpdate,
    members_seenReset,members_seenInsert,stageAction_eq]
  rfl

/-- The coded empty local state. -/
def initial : ℕ := Nat.pair (code ⟨[],[],rfl,0⟩) (Nat.pair (encode ([] : List ℕ)) (encode ([] :
  List ℕ)))

/-- Iterate the coded local-state transition from the empty initial state. -/
def construction (D : LocalInputs.Data) : ℕ → ℕ :=
  recur (fun _ => initial) (fun v => advance D (Nat.unpair v).2) 0

theorem construction_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun s => Part.some (construction D s)) := by
  have h := recur_recursive (total_primrec (Primrec.const initial))
    (total_comp (advance_recursive D) (total_primrec r))
  have hh := total_comp h (total_primrec (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id))
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem construction_eq (D : LocalInputs.Data) (s : ℕ) :
    state (construction D s) = LocalStage.construction D s := by
  induction s with
  | zero => simp
    [construction,recur,initial,state,condition_code,members,record,LocalStage.construction]
  | succ s ih =>
    change state (advance D (Nat.unpair (Nat.pair 0 (Nat.pair s (construction D s)))).2) = _
    rw [Nat.unpair_pair,advance_eq,ih]
    rfl

theorem conditions_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)}
      (fun s => Part.some (code (LocalStage.conditions D s))) := by
  have h := total_comp (total_primrec ((levelCode_primrec.comp Primrec.id active_primrec).comp f))
    (construction_recursive D)
  apply h.of_eq
  intro s
  change Part.some (code (state (construction D s)).condition) = _
  rw [construction_eq]
  rfl

theorem limits_recursive (D : LocalInputs.Data) :
    Reduces (join (leftLimit (LocalStage.conditions D)) (rightLimit (LocalStage.conditions D)))
      (D.bound) := by
  have hs := total_comp (conditions_recursive D) (total_primrec (Primrec.succ.comp
    Primrec.nat_div2))
  have hbit : Primrec (fun v : ℕ => CommonIdeal.bit
      ((bif (Nat.unpair v).2.bodd then right (Nat.unpair v).1 else left (Nat.unpair v).1).getD
        (Nat.unpair v).2.div2 false)) := CommonIdeal.bit_primrec.comp
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
end TuringRigidity.LocalComputability

end OAI
