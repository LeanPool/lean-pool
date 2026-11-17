/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/GuardedComputability.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.GuardedScan

/-!
# Guarded Computability
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.GuardedComputability
open Encodable UniformOracle EncodedForcing CodingForcing FiniteInjury StageRecords
noncomputable section
attribute [local instance] Classical.propDecidable

def state (v : ℕ) : GuardedStage.State :=
  ⟨condition (Nat.unpair v).1,members (Nat.unpair (Nat.unpair v).2).1,members (Nat.unpair
    (Nat.unpair v).2).2⟩

def generic (A : Oracle) (v : ℕ) : ℕ := GuardedStage.openProcedure A
  (Nat.pair (nextVisit (Nat.unpair (Nat.unpair v).2).2) (Nat.unpair v).1)

theorem open_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun v => Part.some
      (GuardedStage.openProcedure A v)) :=
  (Classical.choose_spec (EffectiveForcing.uniform_open_decision A A (reduces_refl A))).1

def canonical (p : ℕ) : ℕ := levelCode p (active p)
theorem canonical_eq (p : ℕ) : canonical p = code (condition p) := rfl

def genericCanonical (A : Oracle) (v : ℕ) : ℕ := GuardedStage.openProcedure A
  (Nat.pair (nextVisit (Nat.unpair (Nat.unpair v).2).2) (canonical (Nat.unpair v).1))

theorem generic_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun v => Part.some (genericCanonical A
      v)) := by
  have hn := total_comp (nextVisit_recursive (O := {oracleFunction (OracleJump.jump A)}))
    (total_primrec (r.comp r))
  have hp := total_primrec (O := {oracleFunction (OracleJump.jump A)}) ((levelCode_primrec.comp
    Primrec.id active_primrec).comp f)
  have hh := total_comp (open_recursive A) (total_pair hn hp)
  exact hh.of_eq (fun v => rfl)

@[simp] theorem generic_eq (A : Oracle) (v : ℕ) :
    condition (genericCanonical A v) = GuardedStage.generic A (state v) := rfl

def stageAction (A : Oracle) (s v : ℕ) : ℕ :=
  scan A (genericCanonical A v) (Nat.unpair (Nat.unpair v).2).1 s

theorem stageAction_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun z =>
      Part.some (stageAction A (Nat.unpair z).1 (Nat.unpair z).2)) := by
  have hg := total_comp (generic_recursive A) (total_primrec r)
  have hh := total_comp (scan_recursive A) (total_pair (total_pair hg (total_primrec (f.comp
    (r.comp r)))) (total_primrec f))
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

@[simp] theorem stageAction_eq (A : Oracle) (s v : ℕ) :
    action (stageAction A s v) = GuardedStage.stageAction A s (state v) := by
  rw [stageAction,scan_eq,action_actionCode,generic_eq]
  rfl

def stageWord (A : Oracle) (z : ℕ) : ℕ :=
  let s := (Nat.unpair z).1
  let v := (Nat.unpair z).2
  let a := stageAction A s v
  let g := genericCanonical A v
  if a = 0 then g else candidate A (Nat.pair (a-1) g)

theorem stageWord_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun z => Part.some (stageWord A z)) := by
  have ha := stageAction_recursive A
  have hg := total_comp (generic_recursive A) (total_primrec r)
  have hc := total_comp (candidate_recursive A) (total_pair
    (total_comp (total_primrec (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))) ha) hg)
  have hpost := Primrec.ite (Primrec.eq.comp f (Primrec.const 0)) (f.comp r) (r.comp r)
  have hh := total_comp (total_primrec hpost) (total_pair ha (total_pair hg hc))
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem stageWord_eq (A : Oracle) (s v : ℕ) :
    condition (stageWord A (Nat.pair s v)) = GuardedStage.stageWord A s (state v) := by
  have he := stageAction_eq A s v
  unfold stageWord
  simp only [Nat.unpair_pair]
  by_cases ha : stageAction A s v = 0
  · have hn : GuardedStage.stageAction A s (state v) = none := by
      simpa only [StageRecords.action, ite_eq_left ha] using he.symm
    simp [ha,GuardedStage.stageWord,hn,generic_eq]
  · have hn : GuardedStage.stageAction A s (state v) = some (stageAction A s v-1) := by
      simpa only [StageRecords.action,ite_eq_right ha] using he.symm
    simp [ha,GuardedStage.stageWord,hn,candidate_eq,generic_eq]

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

def advance (A : Oracle) (z : ℕ) : ℕ :=
  let s := (Nat.unpair z).1
  let v := (Nat.unpair z).2
  let d := (Nat.unpair (Nat.unpair v).2).1
  let seen := (Nat.unpair (Nat.unpair v).2).2
  let a := stageAction A s v
  Nat.pair (grow (stageWord A z) s)
    (Nat.pair (doneUpdate d a) (seenReset (seenInsert seen (nextVisit seen)) a))

theorem advance_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun z => Part.some (advance A z)) := by
  have ha := stageAction_recursive A
  have hw := total_comp (total_primrec (grow_primrec.comp f r))
    (total_pair (stageWord_recursive A) (total_primrec f))
  have hd := total_comp (total_primrec (doneUpdate_primrec.comp f r))
    (total_pair (total_primrec (f.comp (r.comp r))) ha)
  have hs := total_primrec (O := {oracleFunction (OracleJump.jump A)}) (r.comp (r.comp r))
  have hn := total_comp nextVisit_recursive hs
  have hi := total_comp (total_primrec (seenInsert_primrec.comp f r)) (total_pair hs hn)
  have hreset := total_comp (total_primrec (seenReset_primrec.comp f r)) (total_pair hi ha)
  have hh := total_pair hw (total_pair hd hreset)
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem advance_eq (A : Oracle) (s v : ℕ) :
    state (advance A (Nat.pair s v)) = GuardedStage.advance A s (state v) := by
  unfold state advance
  simp only [Nat.unpair_pair,condition_grow,stageWord_eq,members_doneUpdate,
    members_seenReset,members_seenInsert,stageAction_eq]
  rfl

def initial : ℕ := Nat.pair (code ⟨[],[],rfl,0⟩) (Nat.pair (encode ([] : List ℕ)) (encode ([] :
  List ℕ)))

def construction (A : Oracle) : ℕ → ℕ :=
  recur (fun _ => initial) (fun v => advance A (Nat.unpair v).2) 0

theorem construction_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun s => Part.some (construction A s))
      := by
  have h := recur_recursive (total_primrec (Primrec.const initial))
    (total_comp (advance_recursive A) (total_primrec r))
  have hh := total_comp h (total_primrec (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id))
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem construction_eq (A : Oracle) (s : ℕ) :
    state (construction A s) = GuardedStage.construction A s := by
  induction s with
  | zero => simp
    [construction,recur,initial,state,condition_code,members,record,GuardedStage.construction]
  | succ s ih =>
    change state (advance A (Nat.unpair (Nat.pair 0 (Nat.pair s (construction A s)))).2) = _
    rw [Nat.unpair_pair,advance_eq,ih]
    rfl

theorem conditions_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)}
      (fun s => Part.some (code (GuardedStage.conditions A s))) := by
  have h := total_comp (total_primrec ((levelCode_primrec.comp Primrec.id active_primrec).comp f))
    (construction_recursive A)
  apply h.of_eq
  intro s
  change Part.some (code (state (construction A s)).condition) = _
  rw [construction_eq]
  rfl

theorem limits_recursive (A : Oracle) :
    Reduces (join (leftLimit (GuardedStage.conditions A)) (rightLimit (GuardedStage.conditions A)))
      (OracleJump.jump A) := by
  have hs := total_comp (conditions_recursive A) (total_primrec (Primrec.succ.comp
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
end TuringRigidity.GuardedComputability

end OAI
