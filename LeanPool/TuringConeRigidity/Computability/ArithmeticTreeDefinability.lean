/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticTreeDefinability.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticWitnessTree

/-!
# Arithmetic Tree Definability
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic Encodable
noncomputable section
attribute [local instance] Classical.propDecidable

theorem Term.approx_primrec (t : Term) :
    Primrec (fun p : List ℕ × ℕ => t.approx (listApprox p.1) p.2) := by
  induction t with
  | input => exact Primrec.option_some.comp Primrec.snd
  | const n => exact Primrec.const (some n)
  | prim g hg t ih =>
    exact Primrec.option_bind ih (Primrec.option_some.comp (hg.comp Primrec.snd))
  | pair t u ih ik =>
    exact Primrec.option_bind ih (Primrec.option_bind (ik.comp Primrec.fst)
      (Primrec.option_some.comp (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)))
  | witness t ih =>
    exact Primrec.option_bind ih
      (Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)

private theorem option_neg_iff (a : Option Bool) (b : Bool) :
    (a.bind (fun c => some (!c)) = some b) ↔ a = some (!b) := by
  cases a with
  | none => simp
  | some a => cases a <;> cases b <;> decide

private theorem option_and_true (a b : Option Bool) :
    (a.bind (fun c => b.bind (fun d => some (c && d))) = some true) ↔
      a = some true ∧ b = some true := by
  cases a with
  | none => simp
  | some a => cases b with
    | none => simp
    | some b => cases a <;> cases b <;> decide

private theorem option_and_false (a b : Option Bool) :
    (a.bind (fun c => b.bind (fun d => some (c && d))) = some false) ↔
      (a = some false ∧ b = some false) ∨
      (a = some false ∧ b = some true) ∨ (a = some true ∧ b = some false) := by
  cases a with
  | none => simp
  | some a => cases b with
    | none => simp
    | some b => cases a <;> cases b <;> decide

theorem Test.approx_arith (t : Test) {s : ℕ → List ℕ} (hs : Primrec s)
    {v : ℕ → ℕ} (hv : Primrec v) (b : Bool) :
    Arith (fun O k => t.approx O (listApprox (s k)) (v k) = some b) := by
  induction t generalizing s v b with
  | pure P hP t =>
    have hp : Primrec (fun k : ℕ => (t.approx (listApprox (s k)) (v k)).bind
        (fun a => some (decide (P a)))) := Primrec.option_bind ((t.approx_primrec).comp (hs.pair
          hv))
      (Primrec.option_some.comp (hP.decide.comp Primrec.snd))
    exact .pure _ (Primrec.eq.comp hp (Primrec.const (some b)))
  | query i t =>
    have ht := (t.approx_primrec).comp ((hs.comp left_primrec).pair (hv.comp left_primrec))
    have hh : Arith (fun _ k => t.approx (listApprox (s (left k))) (v (left k)) = some (right k)) :=
      .pure _ (Primrec.eq.comp ht (Primrec.option_some.comp right_primrec))
    have hq : Arith (fun O k => O i (right k) = b) := by
      cases b with
      | true => exact (Arith.query i).comp _ right_primrec
      | false =>
        exact ((Arith.query i).comp _ right_primrec).neg.congr
          (fun O k => by cases O i (right k) <;> simp)
    exact (hh.and hq).ex.congr (fun O k => by
      simp only [left,right,Nat.unpair_pair,Test.approx,Option.bind_eq_some_iff,Option.some.injEq])
  | neg t ih =>
    exact (ih hs hv (!b)).congr (fun O k => (option_neg_iff _ b).symm)
  | and t u ih ik =>
    cases b with
    | true =>
      exact ((ih hs hv true).and (ik hs hv true)).congr
        (fun O k => (option_and_true _ _).symm)
    | false =>
      exact (((ih hs hv false).and (ik hs hv false)).or
        (((ih hs hv false).and (ik hs hv true)).or ((ih hs hv true).and (ik hs hv false)))).congr
        (fun O k => (option_and_false _ _).symm)

theorem Test.accepts_arith (t : Test) {s : ℕ → List ℕ} (hs : Primrec s)
    {v : ℕ → ℕ} (hv : Primrec v) : Arith (fun O k => t.accepts O (v k) (s k)) := by
  have hlen : Arith (fun _ k => right k < (s (left k)).length) :=
    .pure _ (Primrec.nat_lt.comp right_primrec (Primrec.list_length.comp (hs.comp left_primrec)))
  have ht := t.approx_arith (hs.comp left_primrec)
    (Primrec₂.natPair.comp (hv.comp left_primrec) right_primrec) false
  exact (hlen.imp ht.neg).all.congr (fun O k => by
    simp only [Test.accepts,left,right,Nat.unpair_pair])

/-- Decode a finite witness-tree node, using the empty list for an invalid code. -/
def decodeNode (n : ℕ) : List ℕ := (decode (α := List ℕ) n).getD []

theorem decodeNode_primrec : Primrec decodeNode :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

@[simp] theorem decodeNode_encode (s : List ℕ) : decodeNode (encode s) = s := by
  simp [decodeNode]

/-- An oracle coding the finite nodes accepted by the arithmetic test. -/
def Test.nodeCode (t : Test) (O : Oracles) (v : ℕ) : Oracle :=
  fun n => decide (t.accepts O v (decodeNode n))

theorem Test.nodeCode_arith (t : Test) (v : ℕ) :
    Arith (fun O n => t.nodeCode O v n = true) :=
  (t.accepts_arith decodeNode_primrec (Primrec.const v)).congr (fun _ _ => by simp [Test.nodeCode])

end
end TuringRigidity.ArithmeticTree

end OAI
