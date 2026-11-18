/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelArithmeticSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelPrimrec
public import LeanPool.TuringConeRigidity.Syntax.BoundedDefinability
public import LeanPool.TuringConeRigidity.Computability.UniformArithmetic

/-!
# Set Model Arithmetic Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelSyntax
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelArithmetic SetModelFunctions
open BoundedDefinability UniformArithmetic Encodable
universe u
noncomputable section

variable {M : ZFSet.{u}}

/-- Shift all non-input variable slots past a block of `k` reserved slots. -/
def skipInput (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => i+k+1

@[simp] theorem skipInput_zero (k : ℕ) : skipInput k 0 = 0 := rfl
@[simp] theorem skipInput_succ (k i : ℕ) : skipInput k (i+1) = i+k+1 := rfl

/-- The predicate `P` is definable in the model through its set-coded oracle parameters. -/
def ArithmeticDefinition (M : ZFSet.{u}) (P : Predicate) : Prop :=
  ∃ Q : (ℕ → ZFSet.{u}) → Prop, Definable M Q ∧
    ∀ e n, e 0 = natSet n →
      (Q e ↔ P (fun i => oracleOf (e (i+1))) n)

/-- The two natural set inputs are paired and their numerical pairing value is `z`. -/
def PairCode (x y z : ZFSet.{u}) : Prop :=
  ZFSet.pair x y ∈ pairNumbers ∧ ZFSet.pair (ZFSet.pair x y) z ∈ pairingSet

theorem pairCode_definable (C : Context M) (i j k : ℕ) :
    Definable M (fun e => PairCode (e i) (e j) (e k)) := by
  refine ⟨tripleFormula (2*i) (2*j) (2*k) 1 3,
    cons pairingSet (fun _ => pairNumbers),?_,?_⟩
  · intro n
    cases n with
    | zero => exact C.pairing_mem
    | succ n => exact C.pairNumbers_mem
  · intro e
    simp only [eval_tripleFormula,mix_even,PairCode]
    rfl

@[simp] theorem pairCode_nat (i j k : ℕ) :
    PairCode (natSet.{u} i) (natSet j) (natSet k) ↔ k = Nat.pair i j := by
  simp only [PairCode,natPair_mem,true_and,pairing_code]

theorem pure_definition (C : Context M) (P : ℕ → Prop) (hP : PrimrecPred P) :
    ArithmeticDefinition M (fun _ n => P n) := by
  obtain ⟨d,hd⟩ := hP
  let : DecidablePred P := d
  obtain ⟨g,hg,hgc⟩ := primrec_graph C (Primrec.encode.comp hd)
  let Q := fun e : ℕ → ZFSet.{u} => ∃ x ∈ ZFSet.omega,
    x = natSet 1 ∧ ZFSet.pair (e 0) x ∈ g
  have hQ : Definable M Q :=
    ((equal_param (C.nat_mem 1) 0).and (pairMem_param hg 1 0)).existsParam C.omega_mem
  refine ⟨Q,hQ,?_⟩
  intro e n hn
  simp only [Q,hn,omega_exists]
  constructor
  · rintro ⟨k,hk,hgk⟩
    have hk' : k=1 := natSet_injective hk
    have hh := (hgc n k).mp hgk
    rw [hk'] at hh
    by_contra h
    simp [h] at hh
  · intro h
    exact ⟨1,rfl,(hgc n 1).mpr (by simp [h])⟩

theorem query_definition (C : Context M) (i : ℕ) :
    ArithmeticDefinition M (fun O n => O i n = true) := by
  refine ⟨fun e => e 0 ∈ e (i+1),member_definable C 0 (i+1),?_⟩
  intro e n hn
  simp [hn,oracleOf]

theorem ArithmeticDefinition.neg {P : Predicate} (h : ArithmeticDefinition M P) :
    ArithmeticDefinition M (fun O n => ¬ P O n) := by
  obtain ⟨Q,hQ,hc⟩ := h
  exact ⟨fun e => ¬ Q e,hQ.neg,fun e n hn => not_congr (hc e n hn)⟩

theorem ArithmeticDefinition.and {P R : Predicate}
    (hP : ArithmeticDefinition M P) (hR : ArithmeticDefinition M R) :
    ArithmeticDefinition M (fun O n => P O n ∧ R O n) := by
  obtain ⟨Q,hQ,hc⟩ := hP
  obtain ⟨S,hS,hs⟩ := hR
  exact ⟨fun e => Q e ∧ S e,hQ.and hS,fun e n hn => and_congr (hc e n hn) (hs e n hn)⟩

theorem ArithmeticDefinition.comp (C : Context M) {P : Predicate}
    (h : ArithmeticDefinition M P) {f : ℕ → ℕ} (hf : Primrec f) :
    ArithmeticDefinition M (fun O n => P O (f n)) := by
  obtain ⟨Q,hQ,hc⟩ := h
  obtain ⟨g,hg,hgc⟩ := primrec_graph C hf
  let R := fun e : ℕ → ZFSet.{u} => ∃ x ∈ ZFSet.omega,
    ZFSet.pair (e 0) x ∈ g ∧ Q (cons x e ∘ skipInput 1)
  have hR : Definable M R :=
    ((pairMem_param hg 1 0).and (hQ.subst (skipInput 1))).existsParam C.omega_mem
  refine ⟨R,hR,?_⟩
  intro e n hn
  simp only [R,omega_exists,hn,hgc]
  constructor
  · rintro ⟨k,rfl,hk⟩
    exact (hc (cons (natSet (f n)) e ∘ skipInput 1) (f n) rfl).mp hk
  · intro hh
    exact ⟨f n,rfl,(hc (cons (natSet (f n)) e ∘ skipInput 1) (f n) rfl).mpr hh⟩

theorem ArithmeticDefinition.ex (C : Context M) {P : Predicate}
    (h : ArithmeticDefinition M P) :
    ArithmeticDefinition M (fun O n => ∃ k, P O (Nat.pair n k)) := by
  obtain ⟨Q,hQ,hc⟩ := h
  let R := fun e : ℕ → ZFSet.{u} => ∃ x ∈ ZFSet.omega, ∃ y ∈ ZFSet.omega,
    PairCode (e 0) x y ∧ Q (cons y (cons x e) ∘ skipInput 2)
  have hR : Definable M R :=
    (((pairCode_definable C 2 1 0).and (hQ.subst (skipInput 2))).existsParam
      C.omega_mem).existsParam C.omega_mem
  refine ⟨R,hR,?_⟩
  intro e n hn
  simp only [R,hn]
  simp_rw [omega_exists]
  simp only [pairCode_nat]
  constructor
  · rintro ⟨k,l,rfl,hl⟩
    exact ⟨k,(hc (cons (natSet (Nat.pair n k)) (cons (natSet k) e) ∘ skipInput 2) (Nat.pair n k)
      rfl).mp hl⟩
  · rintro ⟨k,hk⟩
    exact ⟨k,Nat.pair n k,rfl,(hc (cons (natSet (Nat.pair n k)) (cons (natSet k) e) ∘ skipInput 2)
      (Nat.pair n k) rfl).mpr hk⟩

theorem arith_definition (C : Context M) {P : Predicate} (h : Arith P) :
    ArithmeticDefinition M P := by
  induction h with
  | pure P hP => exact pure_definition C P hP
  | query i => exact query_definition C i
  | neg h ih => exact ih.neg
  | and h k ih ik => exact ih.and ik
  | ex h ih => exact ih.ex C
  | comp f h hf ih => exact ih.comp C hf

end
end TuringRigidity.SetModelSyntax

end OAI
