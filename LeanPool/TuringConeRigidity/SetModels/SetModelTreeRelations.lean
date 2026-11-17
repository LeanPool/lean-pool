/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelTreeRelations.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelArithmeticTree
public import LeanPool.TuringConeRigidity.Syntax.SetRankCertificate

/-!
# Set Model Tree Relations
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic BoundedSetTheory TransitiveNameModel SetModelReals SetModelSyntax
open SetModelArithmetic SetModelFunctions SetModelSequences Encodable
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

def Test.canonicalNode (t : Test) (O : Oracles) (v n : ℕ) : Prop :=
  encode (decodeNode n) = n ∧ t.accepts O v (decodeNode n)

def Test.edgePredicate (t : Test) (O : Oracles) (v n m : ℕ) : Prop :=
  t.canonicalNode O v n ∧ t.canonicalNode O v m ∧ ∃ a, decodeNode n = decodeNode m ++ [a]

theorem Test.canonical_arith (t : Test) (v : ℕ) : Arith (fun O n => t.canonicalNode O v n) :=
  (Arith.pure _ (Primrec.eq.comp (Primrec.encode.comp decodeNode_primrec) Primrec.id)).and
    (t.accepts_arith decodeNode_primrec (Primrec.const v))

theorem Test.edge_arith (t : Test) (v : ℕ) :
    Arith (fun O n => t.edgePredicate O v (left n) (right n)) := by
  have hc := ((t.canonical_arith v).comp _ left_primrec).and
    ((t.canonical_arith v).comp _ right_primrec)
  have he : Arith (fun _ n =>
      decodeNode (left (left n)) = decodeNode (right (left n)) ++ [right n]) :=
    .pure _ (Primrec.eq.comp (decodeNode_primrec.comp (left_primrec.comp left_primrec))
      (Primrec.list_concat.comp (decodeNode_primrec.comp (right_primrec.comp left_primrec))
        right_primrec))
  exact (hc.and he.ex).congr (fun _ _ => by
    simp only [Test.edgePredicate, left, right, Nat.unpair_pair, and_assoc])

def relationSet (A : Oracle) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ realSet A, ZFSet.pair z x ∈ pairingSet) pairNumbers

theorem relationSet_pair (A : Oracle) (n m : ℕ) :
    ZFSet.pair (natSet.{u} n) (natSet m) ∈ relationSet A ↔ A (Nat.pair n m) = true := by
  simp only [relationSet,ZFSet.mem_sep,natPair_mem,true_and]
  constructor
  · rintro ⟨x,hx,hp⟩
    obtain ⟨k,rfl⟩ := (mem_omega _).mp (realSet_subset A hx)
    have hk := (pairingSet_code n m k).mp hp
    simpa only [hk,nat_mem_realSet] using hx
  · intro hA
    exact ⟨natSet (Nat.pair n m),(nat_mem_realSet _ _).mpr hA,
      (pairingSet_code n m _).mpr rfl⟩

theorem relationSet_mem {M : ZFSet.{u}} (C : Context M) {A : Oracle} (hA : A ∈ reals M) :
    relationSet A ∈ M := by
  let φ : Formula := .existsMem 1 (.pairMem 1 0 3)
  let e := cons (realSet A) (fun _ => pairingSet.{u})
  have he : ∀ i, e i ∈ M := by
    intro i
    cases i with
    | zero => exact hA
    | succ i => exact C.pairing_mem
  have h := sep_mem M C.transitive C.separation φ e he C.pairNumbers_mem
  have heq : ZFSet.sep (fun z => φ.Eval (cons z e)) pairNumbers = relationSet A := by
    apply ZFSet.ext
    intro z
    simp only [relationSet,ZFSet.mem_sep,φ,e,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ]
  exact heq ▸ h

theorem Test.internal_relations {M : ZFSet.{u}} (C : Context M) (t : Test)
    (O : Oracles) (hO : ∀ i, O i ∈ reals M) (v : ℕ) :
    ∃ d ∈ M, ∃ r ∈ M,
      (∀ n, natSet n ∈ d ↔ t.canonicalNode O v n) ∧
      (∀ n m, ZFSet.pair (natSet n) (natSet m) ∈ r ↔ t.edgePredicate O v n m) := by
  let A : Oracle := fun n => decide (t.canonicalNode O v n)
  let B : Oracle := fun n => decide (t.edgePredicate O v (left n) (right n))
  have hA : A ∈ reals M := arithmetic_comprehension C (t.canonical_arith v) O hO A
    (fun n => by simp [A])
  have hB : B ∈ reals M := arithmetic_comprehension C (t.edge_arith v) O hO B
    (fun n => by simp [B])
  refine ⟨realSet A,hA,relationSet B,relationSet_mem C hB,?_,?_⟩
  · intro n
    simp [A]
  · intro n m
    simp [relationSet_pair,B,left,right]

theorem Test.internal_tree {M : ZFSet.{u}} (C : Context M) (t : Test)
    (O : Oracles) (hO : ∀ i, O i ∈ reals M) (v : ℕ) :
    ∃ d ∈ M, ∃ r ∈ M,
      (∀ x : t.tree O v, natSet (encode x.val) ∈ d) ∧
      (∀ x y : t.tree O v, ZFSet.pair (natSet (encode x.val)) (natSet (encode y.val)) ∈ r ↔
        t.Child O v x y) := by
  obtain ⟨d,hd,r,hr,hD,hR⟩ := t.internal_relations C O hO v
  refine ⟨d,hd,r,hr,fun x => (hD _).mpr ?_,fun x y => ?_⟩
  · exact ⟨by simp, by simpa only [decodeNode_encode] using (show t.accepts O v x.val from
      x.property)⟩
  · rw [hR]
    have hx : t.canonicalNode O v (encode x.val) := ⟨by simp,by
      simpa only [decodeNode_encode] using (show t.accepts O v x.val from x.property)⟩
    have hy : t.canonicalNode O v (encode y.val) := ⟨by simp,by
      simpa only [decodeNode_encode] using (show t.accepts O v y.val from y.property)⟩
    simp only [Test.edgePredicate,hx,hy,true_and,decodeNode_encode,Test.Child]

end
end TuringRigidity.ArithmeticTree

end OAI
