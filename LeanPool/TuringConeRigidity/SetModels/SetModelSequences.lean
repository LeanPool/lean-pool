/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelSequences.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelRecursion

/-!
# Set Model Sequences
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelSequences
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
universe u
noncomputable section

/-- The set-coded graph of a sequence of oracle real sets. -/
def sequenceSet (F : ℕ → Oracle) : ZFSet.{u} :=
  ZFSet.range (fun n : ℕ => ZFSet.pair (natSet n) (realSet (F n)))

theorem mem_sequenceSet (F : ℕ → Oracle) (z : ZFSet.{u}) :
    z ∈ sequenceSet F ↔ ∃ n, z = ZFSet.pair (natSet n) (realSet (F n)) := by
  rw [sequenceSet,ZFSet.mem_range]
  exact exists_congr (fun n => eq_comm)

@[simp] theorem pair_mem_sequenceSet (F : ℕ → Oracle) (n : ℕ) (x : ZFSet.{u}) :
    ZFSet.pair (natSet n) x ∈ sequenceSet F ↔ x = realSet (F n) := by
  rw [mem_sequenceSet]
  constructor
  · rintro ⟨m,he⟩
    obtain ⟨hn,hx⟩ := ZFSet.pair_inj.mp he
    exact natSet_injective hn ▸ hx
  · intro h
    exact ⟨n,by rw [h]⟩

/-- Bounded formula describing one slice of a paired oracle sequence. -/
def sliceFormula : Formula :=
  .existsMem 1 (.existsMem 3 (.existsMem 7
    (.conj (.orderedPair 3 2 1) (.conj (.orderedPair 0 2 6) (.pairMem 0 1 7)))))

theorem eval_sliceFormula (z r a q d : ZFSet.{u}) :
    sliceFormula.Eval (cons z (cons ZFSet.omega (cons r (cons a (cons q (fun _ => d)))))) ↔
    ∃ n : ℕ, ∃ b ∈ r, ∃ t ∈ d,
      z = ZFSet.pair (natSet n) b ∧ t = ZFSet.pair (natSet n) a ∧ ZFSet.pair t b ∈ q := by
  simp only [sliceFormula,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ]
  rw [omega_exists]

theorem sequence_mem_of_iteration (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M)
    {r : ZFSet.{u}} (hr : r ∈ M) (F : ZFSet.{u} → ZFSet.{u})
    (hF : ∀ x ∈ r, F x ∈ r) (hq : iterationSet r F ∈ M)
    {A : Oracle} (hA : realSet A ∈ r) (B : ℕ → Oracle)
    (hB : ∀ n, F^[n] (realSet A) = realSet (B n)) : sequenceSet B ∈ M := by
  have hω := omega_mem M hM hS hI
  let d := ZFSet.prod ZFSet.omega r
  have hd : d ∈ M := product_mem M hM hP hU hPow hS hω hr
  have ha := hM r hr _ hA
  let e := cons ZFSet.omega (cons r (cons (realSet A) (cons (iterationSet r F) (fun _ => d))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|i <;> simp only [e,cons_zero,cons_succ]
    · exact hω
    · exact hr
    · exact ha
    · exact hq
    · exact hd
  have hs := sep_mem M hM hS sliceFormula e he hd
  have eq : ZFSet.sep (fun z => sliceFormula.Eval (cons z e)) d = sequenceSet B := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep,mem_sequenceSet,
      show sliceFormula.Eval (cons z e) ↔ _ from eval_sliceFormula z r (realSet A) (iterationSet r
        F) d]
    constructor
    · rintro ⟨_,n,b,hb,t,ht,hz,htA,hqt⟩
      obtain ⟨m,x,hx,hpair⟩ := (mem_iterationSet F hF _).mp hqt
      obtain ⟨hfirst,hsecond⟩ := ZFSet.pair_inj.mp hpair
      rw [htA] at hfirst
      obtain ⟨hn,hxA⟩ := ZFSet.pair_inj.mp hfirst
      have hnm := natSet_injective hn
      refine ⟨n,?_⟩
      rw [hz,hsecond,←hxA,←hnm,hB]
    · rintro ⟨n,rfl⟩
      have hb : realSet (B n) ∈ r := hB n ▸ iterate_mem F hF hA n
      have hn : natSet.{u} n ∈ ZFSet.omega := (mem_omega _).mpr ⟨n,rfl⟩
      refine ⟨ZFSet.pair_mem_prod.mpr ⟨hn,hb⟩,n,_,hb,_,
        ZFSet.pair_mem_prod.mpr ⟨hn,hA⟩,rfl,rfl,?_⟩
      exact (mem_iterationSet F hF _).mpr ⟨n,realSet A,hA,by rw [hB]⟩
  exact eq ▸ hs

/-- The natural-number pairs in `p` agree exactly with the natural pairing function. -/
def PairingCode (p : ZFSet.{u}) : Prop := ∀ n k m : ℕ,
  ZFSet.pair (ZFSet.pair (natSet n) (natSet k)) (natSet m) ∈ p ↔ m = Nat.pair n k

/-- Bounded formula describing the flattening of a set-coded oracle sequence. -/
def flattenFormula : Formula :=
  .existsMem 1 (.existsMem 2 (.existsMem 7 (.existsMem 5
    (.conj (.orderedPair 1 3 2) (.conj (.pairMem 1 4 8)
      (.conj (.pairMem 3 0 7) (.member 2 0)))))))

theorem eval_flattenFormula (m : ℕ) (r q p d : ZFSet.{u}) :
    flattenFormula.Eval (cons (natSet m) (cons ZFSet.omega
      (cons r (cons q (cons p (fun _ => d)))))) ↔
    ∃ n k : ℕ, ∃ t ∈ d, ∃ b ∈ r,
      t = ZFSet.pair (natSet n) (natSet k) ∧ ZFSet.pair t (natSet m) ∈ p ∧
      ZFSet.pair (natSet n) b ∈ q ∧ natSet k ∈ b := by
  simp only [flattenFormula,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ]
  rw [omega_exists]
  apply exists_congr
  intro n
  rw [omega_exists]

theorem flatten_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M)
    {r p : ZFSet.{u}} (hr : r ∈ M)
    (hrdef : ∀ x, x ∈ r ↔ ∃ A ∈ reals M, x = realSet A)
    (hp : p ∈ M) (hpdef : PairingCode p) (F : ℕ → Oracle)
    (hF : ∀ n, F n ∈ reals M) (hq : sequenceSet F ∈ M) :
    (fun v => F (Nat.unpair v).1 (Nat.unpair v).2) ∈ reals M := by
  have hω := omega_mem M hM hS hI
  let d := ZFSet.prod ZFSet.omega ZFSet.omega
  have hd : d ∈ M := product_mem M hM hP hU hPow hS hω hω
  let e := cons ZFSet.omega (cons r (cons (sequenceSet F) (cons p (fun _ => d))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|i <;> simp only [e,cons_zero,cons_succ]
    · exact hω
    · exact hr
    · exact hq
    · exact hp
    · exact hd
  apply real_comprehension M hM hS hI _ flattenFormula e he
  intro m
  rw [show flattenFormula.Eval (cons (natSet m) e) ↔ _ from eval_flattenFormula m r (sequenceSet
    F) p d]
  constructor
  · rintro ⟨n,k,t,ht,b,hb,htnk,hpm,hqb,hkb⟩
    rw [htnk] at hpm
    have hm := (hpdef n k m).mp hpm
    have hbF := (pair_mem_sequenceSet F n b).mp hqb
    rw [hbF] at hkb
    simpa only [hm,Nat.unpair_pair] using (nat_mem_realSet _ _).mp hkb
  · intro hm
    let n := (Nat.unpair m).1
    let k := (Nat.unpair m).2
    have hn : natSet.{u} n ∈ ZFSet.omega := (mem_omega _).mpr ⟨n,rfl⟩
    have hk : natSet.{u} k ∈ ZFSet.omega := (mem_omega _).mpr ⟨k,rfl⟩
    refine ⟨n,k,_,ZFSet.pair_mem_prod.mpr ⟨hn,hk⟩,_,
      (hrdef _).mpr ⟨F n,hF n,rfl⟩,rfl,?_,(pair_mem_sequenceSet F n _).mpr rfl,?_⟩
    · exact (hpdef n k m).mpr (Nat.pair_unpair m).symm
    · exact (nat_mem_realSet _ _).mpr hm

end
end TuringRigidity.SetModelSequences

end OAI
