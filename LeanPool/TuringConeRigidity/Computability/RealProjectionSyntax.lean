/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/RealProjectionSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.ConstructionInputData
public import LeanPool.TuringConeRigidity.SetModels.SetModelJoin

/-!
# Real Projection Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic SetModelReals
universe u

/-- The natural-number index obtained by following a finite sequence of binary real
projections. -/
def bitIndex : List Bool → ℕ → ℕ
  | [], n => n
  | b::bs, n => 2 * bitIndex bs n + if b then 1 else 0

/-- The binary projection path selecting the `i`th component of an oracle. -/
def partBits : ℕ → List Bool
  | 0 => [false]
  | i+1 => true :: partBits i

/-- Concatenate the component-selection paths along a finite sequence of indices. -/
def pathBits : List ℕ → List Bool
  | [] => []
  | i::is => partBits i ++ pathBits is

theorem bitIndex_append (a b : List Bool) (n : ℕ) :
    bitIndex (a++b) n = bitIndex a (bitIndex b n) := by
  induction a with
  | nil => rfl
  | cons c a ih => simp only [List.cons_append,bitIndex,ih]

theorem realPart_bits (P : Oracle) (i n : ℕ) :
    realPart P i n = P (bitIndex (partBits i) n) := by
  induction i generalizing P with
  | zero => simp [realPart,partBits,bitIndex]
  | succ i ih => exact ih (fun k => P (2*k+1))

theorem pathReal_bits (P : Oracle) (path : List ℕ) (n : ℕ) :
    pathReal P path n = P (bitIndex (pathBits path) n) := by
  induction path generalizing P with
  | nil => rfl
  | cons i is ih => rw [pathReal,ih,realPart_bits,pathBits,bitIndex_append]

/-- Bounded formula for one doubling step, adding one when the selected bit is true. -/
def bitStep (b : Bool) (w a d x y : ℕ) : Formula :=
  if b then .existsMem w (.conj (tripleFormula (x+1) (x+1) 0 (a+1) (d+1))
    (.successor (y+1) 0)) else tripleFormula x x y a d

theorem bitStep_spec (b : Bool) (w a d x y : ℕ) (e : ℕ → ZFSet.{u})
    (hw : e w = ZFSet.omega) (ha : e a = additionSet) (hd : e d = pairNumbers)
    (n m : ℕ) (hx : e x = natSet n) (hy : e y = natSet m) :
    (bitStep b w a d x y).Eval e ↔ m = 2*n + if b then 1 else 0 := by
  cases b
  · simp [bitStep,eval_tripleFormula,hx,hy,ha,hd,addition_code,two_mul]
  · simp only [bitStep,ite_true,Formula.Eval,eval_tripleFormula,Formula.eval_successor,
      cons_zero,cons_succ,hw,hx,hy,ha,hd]
    rw [omega_exists]
    simp only [natPair_mem,true_and,addition_code,natSet_successor_eq]
    constructor
    · rintro ⟨k,hk,hm⟩; omega
    · intro hm; exact ⟨n+n,rfl,by omega⟩

/-- Bounded formula computing the natural index associated with a binary projection path. -/
def bitIndexFormula : List Bool → ℕ → ℕ → ℕ → ℕ → ℕ → Formula
  | [], _, _, _, x, y => .equal y x
  | b::bs, w, a, d, x, y => .existsMem w
      (.conj (bitIndexFormula bs (w+1) (a+1) (d+1) (x+1) 0)
        (bitStep b (w+1) (a+1) (d+1) 0 (y+1)))

theorem bitIndexFormula_spec (bs : List Bool) (w a d x y : ℕ) (e : ℕ → ZFSet.{u})
    (hw : e w = ZFSet.omega) (ha : e a = additionSet) (hd : e d = pairNumbers)
    (n m : ℕ) (hx : e x = natSet n) (hy : e y = natSet m) :
    (bitIndexFormula bs w a d x y).Eval e ↔ m = bitIndex bs n := by
  induction bs generalizing w a d x y e m with
  | nil => simp [bitIndexFormula,Formula.Eval,hx,hy,bitIndex,natSet_injective.eq_iff]
  | cons b bs ih =>
    simp only [bitIndexFormula,Formula.Eval,hw]
    rw [omega_exists]
    have hb (k : ℕ) := bitStep_spec b (w+1) (a+1) (d+1) 0 (y+1)
      (cons (natSet k) e) hw ha hd k m rfl hy
    have hi (k : ℕ) := ih (w+1) (a+1) (d+1) (x+1) 0 (cons (natSet k) e)
      hw ha hd k hx rfl
    simp only [hi,hb,exists_eq_left,bitIndex]

/-- Bounded formula expressing membership in a binary projection of an oracle code. -/
def projectionMember (bs : List Bool) (w a d P x : ℕ) : Formula :=
  .conj (.member x w) (.existsMem w
    (.conj (bitIndexFormula bs (w+1) (a+1) (d+1) (x+1) 0) (.member 0 (P+1))))

theorem projectionMember_spec (bs : List Bool) (w a d P x : ℕ)
    (e : ℕ → ZFSet.{u}) (hw : e w = ZFSet.omega) (ha : e a = additionSet)
    (hd : e d = pairNumbers) (Q : Oracle) (hP : e P = realCode Q) :
    (projectionMember bs w a d P x).Eval e ↔ e x ∈ realCode (fun n => Q (bitIndex bs n)) := by
  simp only [projectionMember,Formula.Eval,hw,cons_zero,cons_succ,hP]
  constructor
  · rintro ⟨hx,k,hk,hrel,hQ⟩
    obtain ⟨n,hn⟩ := (mem_omega (e x)).mp hx
    obtain ⟨m,rfl⟩ := (mem_omega k).mp hk
    have hm := (bitIndexFormula_spec bs (w+1) (a+1) (d+1) (x+1) 0
      (cons (natSet m) e) hw ha hd n m hn rfl).mp hrel
    rw [hn,natSet_mem_realCode]
    simpa [hm] using (natSet_mem_realCode Q m).mp hQ
  · intro hx
    obtain ⟨n,hn⟩ := (mem_omega (e x)).mp (realCode_subset _ hx)
    have hnQ : Q (bitIndex bs n) = true := (natSet_mem_realCode _ n).mp (hn ▸ hx)
    refine ⟨hn.symm ▸ (mem_omega _).mpr ⟨n,rfl⟩,natSet (bitIndex bs n),
      (mem_omega _).mpr ⟨_,rfl⟩,?_,(natSet_mem_realCode Q _).mpr hnQ⟩
    exact (bitIndexFormula_spec bs (w+1) (a+1) (d+1) (x+1) 0
      (cons (natSet (bitIndex bs n)) e) hw ha hd n _ hn rfl).mpr rfl

/-- Full set-theoretic formula defining the oracle projection selected by the binary path. -/
noncomputable def projectionFormula (bs : List Bool) (out w a d P : ℕ) : SentenceForm :=
  SentenceForm.all (SentenceForm.iff (.member 0 (out+1))
    (fromBounded (projectionMember bs (w+1) (a+1) (d+1) (P+1) 0)))

theorem projectionFormula_spec (M : ZFSet.{u}) (hM : Transitive M)
    (bs : List Bool) (out w a d P : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (hw : e w = ZFSet.omega) (ha : e a = additionSet) (hd : e d = pairNumbers)
    (Q : Oracle) (hP : e P = realCode Q) :
    (projectionFormula bs out w a d P).Sat (M : Set ZFSet) e ↔
      e out = realCode (fun n => Q (bitIndex bs n)) := by
  have hs (x : ZFSet.{u}) (hx : x ∈ M) :
      (fromBounded (projectionMember bs (w+1) (a+1) (d+1) (P+1) 0)).Sat
        (M : Set ZFSet) (cons x e) ↔ x ∈ realCode (fun n => Q (bitIndex bs n)) := by
    rw [bounded_sat,Formula.absolute _ M hM _
      (by
        intro i
        cases i
        · exact hx
        · exact he _)]
    exact projectionMember_spec bs (w+1) (a+1) (d+1) (P+1) 0 (cons x e) hw ha hd Q hP
  simp only [projectionFormula,SentenceForm.sat_all,SentenceForm.sat_iff,
    SentenceForm.Sat,cons_zero,cons_succ]
  constructor
  · intro h
    apply ZFSet.ext; intro x
    constructor
    · intro hx
      have hxM := hM _ (he out) _ hx
      exact (hs x hxM).mp ((h x hxM).mp hx)
    · intro hx
      have hxM := hM _ (hw ▸ he w) _ (realCode_subset _ hx)
      exact (h x hxM).mpr ((hs x hxM).mpr hx)
  · intro h x hx; rw [h]; exact (hs x hx).symm

end TuringRigidity.RelativeConstructible

end OAI
