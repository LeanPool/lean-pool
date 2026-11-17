/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/GuardedScan.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.StageRecords
public import LeanPool.TuringConeRigidity.Effective.GuardedStage

/-!
# Guarded Scan
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.GuardedComputability
open Encodable UniformOracle EncodedForcing CodingForcing FiniteInjury StageRecords
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Primitive-recursive first projection of a natural-number pair code. -/
abbrev f := Primrec.fst.comp Primrec.unpair
/-- Primitive-recursive second projection of a natural-number pair code. -/
abbrev r := Primrec.snd.comp Primrec.unpair

/-- Re-encode a condition's two words with the specified active level. -/
def levelCode (p t : ℕ) : ℕ := Nat.pair (encode (left p)) (Nat.pair (encode (right p)) t)

theorem levelCode_primrec : Primrec₂ levelCode := Primrec₂.natPair.comp
  (Primrec.encode.comp (left_primrec.comp Primrec.fst))
  (Primrec₂.natPair.comp (Primrec.encode.comp (right_primrec.comp Primrec.fst)) Primrec.snd)

theorem levelCode_eq (p t : ℕ) : levelCode p t = code (atLevel (condition p) t) := rfl

@[simp] theorem condition_levelCode (p t : ℕ) : condition (levelCode p t) = atLevel (condition p)
  t :=
  condition_code (atLevel (condition p) t)

/-- Compute and normalize the guarded candidate at the priority encoded in `v`. -/
def candidate (A : Oracle) (v : ℕ) : ℕ :=
  levelCode (GuardedStage.pairProcedure A (Nat.pair (Nat.unpair v).1
    (levelCode (Nat.unpair v).2 (Nat.unpair v).1))) (Nat.unpair v).1

theorem candidate_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun v => Part.some (candidate A v)) := by
  have h := total_comp (GuardedStage.pairProcedure_recursive A)
    (total_primrec (Primrec₂.natPair.comp f (levelCode_primrec.comp r f)))
  have hh := total_comp (total_primrec (levelCode_primrec.comp f r)) (total_pair h (total_primrec
    f))
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

@[simp] theorem candidate_eq (A : Oracle) (t p : ℕ) :
    condition (candidate A (Nat.pair t p)) = GuardedStage.candidate A t (condition p) := by
  simp only [candidate,Nat.unpair_pair,levelCode_eq,GuardedStage.candidate,condition_code]

/-- Keep the first unfinished candidate that changes a condition word during the scan. -/
def scanStep (A : Oracle) (v : ℕ) : ℕ :=
  let p := (Nat.unpair (Nat.unpair v).1).1
  let d := (Nat.unpair (Nat.unpair v).1).2
  let t := (Nat.unpair (Nat.unpair v).2).1
  let prev := (Nat.unpair (Nat.unpair v).2).2
  let c := candidate A (Nat.pair t p)
  if prev = 0 ∧ t ∉ record d ∧ (left c ≠ left p ∨ right c ≠ right p) then t+1 else prev

theorem scanStep_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun v => Part.some (scanStep A v)) := by
  have hc := total_comp (candidate_recursive A)
    (total_primrec (Primrec₂.natPair.comp (f.comp r) (f.comp f)))
  let v := f
  let c := r
  let p := f.comp (f.comp v)
  let d := r.comp (f.comp v)
  let t := f.comp (r.comp v)
  let prev := r.comp (r.comp v)
  have hm := (mem_primrec.comp d t).not
  have hl := (Primrec.eq.comp (left_primrec.comp c) (left_primrec.comp p)).not
  have hr := (Primrec.eq.comp (right_primrec.comp c) (right_primrec.comp p)).not
  have hpost := Primrec.ite ((Primrec.eq.comp prev (Primrec.const 0)).and (hm.and (hl.or hr)))
    (Primrec.succ.comp t) prev
  have hh := total_comp (total_primrec hpost) (total_pair (total_primrec Primrec.id) hc)
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

/-- Iterate the guarded candidate scan through the first `n` priorities. -/
def scan (A : Oracle) (p d n : ℕ) : ℕ := recur (fun _ => 0) (scanStep A) (Nat.pair p d) n

theorem scan_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun v =>
      Part.some (scan A (Nat.unpair (Nat.unpair v).1).1 (Nat.unpair (Nat.unpair v).1).2
        (Nat.unpair v).2)) := by
  simpa only [scan,Nat.pair_unpair] using recur_recursive (total_primrec (Primrec.const 0))
    (scanStep_recursive A)

theorem source_scan_succ (A : Oracle) (p : Condition) (d : Finset ℕ) (t n : ℕ) :
    GuardedStage.scan A p d t (n+1) =
      match GuardedStage.scan A p d t n with
      | some i => some i
      | none => if t+n ∉ d ∧ GuardedStage.Changes A (t+n) p then some (t+n) else none := by
  induction n generalizing t with
  | zero => simp [GuardedStage.scan]
  | succ n ih =>
    change (if t ∉ d ∧ GuardedStage.Changes A t p then some t else GuardedStage.scan A p d (t+1)
      (n+1)) =
      match (if t ∉ d ∧ GuardedStage.Changes A t p then some t else GuardedStage.scan A p d (t+1)
        n) with
      | some i => some i
      | none => if t+(n+1) ∉ d ∧ GuardedStage.Changes A (t+(n+1)) p then some (t+(n+1)) else none
    by_cases ht : t ∉ d ∧ GuardedStage.Changes A t p
    · simp only [ite_eq_left ht]
    · simpa only [ite_eq_right ht,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (t+1)

theorem scan_eq (A : Oracle) (p d n : ℕ) :
    scan A p d n = actionCode (GuardedStage.scan A (condition p) (members d) 0 n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [source_scan_succ]
    change scanStep A (Nat.pair (Nat.pair p d) (Nat.pair n (scan A p d n))) = _
    simp only [scanStep,Nat.unpair_pair,ih,Nat.zero_add]
    have hc : left (candidate A (Nat.pair n p)) ≠ left p ∨
        right (candidate A (Nat.pair n p)) ≠ right p ↔ GuardedStage.Changes A n (condition p) := by
      change (condition (candidate A (Nat.pair n p))).left ≠ (condition p).left ∨
        (condition (candidate A (Nat.pair n p))).right ≠ (condition p).right ↔ _
      rw [candidate_eq]
      rfl
    cases he : GuardedStage.scan A (condition p) (members d) 0 n with
    | none =>
      by_cases hn : n ∉ record d ∧ GuardedStage.Changes A n (condition p)
      · simp_all only [actionCode,members,List.mem_toFinset,true_and]; simp
      · simp_all only [actionCode,members,List.mem_toFinset,true_and]; simp
    | some i => simp [actionCode]

end
end TuringRigidity.GuardedComputability

end OAI
