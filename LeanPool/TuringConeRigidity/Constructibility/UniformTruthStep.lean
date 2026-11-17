/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformTruthStep.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.TupleLookupAdequacy
public import LeanPool.TuringConeRigidity.Syntax.SatisfactionRecursion

/-!
# Uniform Truth Step
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions SetModelReals
universe u

variable {M : ZFSet.{u}}

/-- One recursive truth clause for a coded full set-theoretic formula and tuple. -/
def SetTruthStep (A G T S c t : ZFSet.{u}) : Prop :=
  (∃ i ∈ ZFSet.omega, ∃ j ∈ ZFSet.omega, ∃ x ∈ A, ∃ y ∈ A,
    BinaryGraph (fun i j => binary 0 (atom i) (atom j)) i j c ∧
      TupleLookup G t i x ∧ TupleLookup G t j y ∧ x = y) ∨
  (∃ i ∈ ZFSet.omega, ∃ j ∈ ZFSet.omega, ∃ x ∈ A, ∃ y ∈ A,
    BinaryGraph (fun i j => binary 1 (atom i) (atom j)) i j c ∧
      TupleLookup G t i x ∧ TupleLookup G t j y ∧ x ∈ y) ∨
  (∃ i ∈ ZFSet.omega, ∃ j ∈ ZFSet.omega,
    BinaryGraph (binary 2) i j c ∧ ZFSet.pair i t ∈ S ∧ ZFSet.pair j t ∈ S) ∨
  (∃ i ∈ ZFSet.omega, UnaryGraph (unary 3) i c ∧ ¬ ZFSet.pair i t ∈ S) ∨
  (∃ i ∈ ZFSet.omega, UnaryGraph (unary 4) i c ∧
    ∃ x ∈ A, ∃ s ∈ T, TuplePrefix A G t x s ∧ ZFSet.pair i s ∈ S)

theorem setTruthStep_definable (C : Context M) {G : ZFSet.{u}}
    (hG : G ∈ M) (a T S c t : ℕ) :
    Definable M (fun e => SetTruthStep (e a) G (e T) (e S) (e c) (e t)) := by
  have ha (tag : ℕ) (hr : Definable M (fun e => e 1 = e 0)) :=
    (((((binaryGraph_definable C _ (atomic_primrec tag) 3 2 (c+4)).and
      ((tupleLookup_definable C hG (t+4) 3 1).and
        ((tupleLookup_definable C hG (t+4) 2 0).and hr))).existsMem (a+3)).existsMem
          (a+2)).existsParam
          C.omega_mem).existsParam C.omega_mem
  have he := ha 0 (equal_definable C 1 0)
  have hm := (((((binaryGraph_definable C _ (atomic_primrec 1) 3 2 (c+4)).and
    ((tupleLookup_definable C hG (t+4) 3 1).and
      ((tupleLookup_definable C hG (t+4) 2 0).and (member_definable C 1 0)))).existsMem
        (a+3)).existsMem
        (a+2)).existsParam C.omega_mem).existsParam C.omega_mem
  have hc := (((binaryGraph_definable C _ (binary_primrec 2) 1 0 (c+2)).and
    ((defPairMem C 1 (t+2) (S+2)).and (defPairMem C 0 (t+2) (S+2)))).existsParam
      C.omega_mem).existsParam C.omega_mem
  have hn := ((unaryGraph_definable C _ (unary_primrec 3) 0 (c+1)).and
    (defPairMem C 0 (t+1) (S+1)).neg).existsParam C.omega_mem
  have hbody := (((tuplePrefix_definable C hG (a+3) (t+3) 1 0).and
    (defPairMem C 2 0 (S+3))).existsMem (T+2)).existsMem (a+1)
  have hx := ((unaryGraph_definable C _ (unary_primrec 4) 0 (c+1)).and hbody).existsParam
    C.omega_mem
  exact defOr he (defOr hm (defOr hc (defOr hn hx)))

theorem setTruthStep_encode (A G S : ZFSet.{u})
    (hG : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleGraph v ∈ G)
    (p : SentenceForm) {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A)
    (hb : p.bound ≤ n) :
    SetTruthStep A G (tupleSpace A) S (natSet (Encodable.encode p)) (tupleCode v) ↔
      truthStep A S v p := by
  unfold SetTruthStep
  simp_rw [omega_exists]
  simp only [BinaryGraph,UnaryGraph,natSet_injective.eq_iff]
  cases p with
  | equal i j =>
    have hi : i < n := by simp only [SentenceForm.bound] at hb; omega
    have hj : j < n := by simp only [SentenceForm.bound] at hb; omega
    simp [encode_equal,binary,unary,cell,atom,Nat.pair_eq_pair,
      tupleLookup_nat G v (hG n v hv),hi,hj,truthStep,eq_comm,
      show tupleEnv v j ∈ A from by simpa [tupleEnv,hj] using hv ⟨j,hj⟩]
  | member i j =>
    have hi : i < n := by simp only [SentenceForm.bound] at hb; omega
    have hj : j < n := by simp only [SentenceForm.bound] at hb; omega
    simp [encode_member,binary,unary,cell,atom,Nat.pair_eq_pair,
      tupleLookup_nat G v (hG n v hv),hi,hj,truthStep,
      show tupleEnv v i ∈ A from by simpa [tupleEnv,hi] using hv ⟨i,hi⟩,
      show tupleEnv v j ∈ A from by simpa [tupleEnv,hj] using hv ⟨j,hj⟩]
  | conj p q =>
    simp [encode_conj,binary,unary,cell,atom,Nat.pair_eq_pair,truthStep,accepts]
  | neg p =>
    simp [encode_neg,binary,unary,cell,atom,Nat.pair_eq_pair,truthStep,accepts]
  | ex p =>
    simp only [↓existsAndEq, encode_ex, unary, cell, atom, binary, Nat.pair_eq_pair,
      Nat.add_right_cancel_iff, OfNat.ofNat_ne_zero, and_false, Nat.right_eq_add,
      Nat.add_eq_zero_iff, one_ne_zero, false_and, and_self, and_true, exists_const,
      OfNat.ofNat_ne_one, Nat.reduceEqDiff, Nat.succ_ne_self, true_and, exists_eq_left', false_or]
    apply exists_congr; intro x
    apply and_congr_right; intro hx
    simp only [tuplePrefix_spec A G hG v hv x _ hx]
    change (∃ s ∈ tupleSpace A, s = tupleCode (Fin.cases x v) ∧
      ZFSet.pair (natSet (Encodable.encode p)) s ∈ S) ↔ _
    constructor
    · rintro ⟨s,_,rfl,hs⟩; exact hs
    · intro hs
      let w : Fin (n+1) → ZFSet.{u} := Fin.cases (motive := fun _ => ZFSet.{u}) x v
      have hw : ∀ i : Fin (n+1), w i ∈ A := fun i => Fin.cases hx hv i
      have ht : tupleCode w ∈ tupleSpace A := (mem_tupleSpace A (tupleCode w)).mpr ⟨n+1,w,hw,rfl⟩
      exact ⟨tupleCode w,ht,rfl,hs⟩

end TuringRigidity.RelativeConstructible

end OAI
