/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalSatisfactionSlice.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.FiniteGraphSatisfaction

/-!
# Internal Satisfaction Slice
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem natSet_subset_iff (k n : ℕ) : natSet.{u} k ⊆ natSet n ↔ k ≤ n := by
  constructor
  · intro h
    by_contra hn
    have hk : n < k := by omega
    have hn' := (natSet_mem_natSet n n).mp (h ((natSet_mem_natSet n k).mpr hk))
    omega
  · intro h x hx
    obtain ⟨i,hi,rfl⟩ := (mem_natSet k x).mp hx
    exact (natSet_mem_natSet i n).mpr (by omega)

theorem satisfactionSet_record (A : ZFSet.{u}) (p : SentenceForm)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) :
    ZFSet.pair (natSet (Encodable.encode p)) (tupleCode v) ∈ satisfactionSet A ↔
      p.bound ≤ n ∧ p.Sat (A : Set ZFSet) (tupleEnv v) := by
  constructor
  · intro h
    obtain ⟨⟨⟨m,q,w⟩,hqm,hq⟩,he⟩ := ZFSet.mem_range.mp h
    obtain ⟨hp,ht⟩ := ZFSet.pair_inj.mp he
    have hqp : q = p := Encodable.encode_injective (natSet_injective hp)
    subst q
    have hmn : m = n := tupleCode_length _ _ ht
    subst m
    have hwv := tupleCode_injective n ht
    rw [hwv] at hq
    exact ⟨hqm,hq⟩
  · rintro ⟨hb,hs⟩
    exact (satisfactionSet_spec A p v hv hb).mpr hs

noncomputable def truthSlice (A : ZFSet.{u}) (p : SentenceForm) : ZFSet.{u} :=
  (tupleSpace A).sep (fun t => ZFSet.pair (natSet (Encodable.encode p)) t ∈ satisfactionSet A)

theorem truthSlice_record (A : ZFSet.{u}) (p : SentenceForm)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) :
    tupleCode v ∈ truthSlice A p ↔ p.bound ≤ n ∧ p.Sat (A : Set ZFSet) (tupleEnv v) := by
  rw [truthSlice,ZFSet.mem_sep,satisfactionSet_record A p v hv]
  exact and_iff_right ((mem_tupleSpace A _).mpr ⟨n,v,hv,rfl⟩)

def tupleTruth (p : SentenceForm) (o A Q b t : ℕ) (idx : ℕ → ℕ) : Formula :=
  .existsMem o (.existsMem (Q+1)
    (.conj (.orderedPair (t+2) 1 0)
      (.conj (.subset (b+2) 1) (graphTruth p (A+2) 0 (fun i => idx i+2)))))

theorem tupleTruth_spec (p : SentenceForm) (o A Q b t : ℕ) (idx : ℕ → ℕ)
    (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega) (hb : e b = natSet p.bound)
    (hi : ∀ i, i < p.bound → e (idx i) = natSet i)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ e A)
    (ht : e t = tupleCode v) (hQ : tupleGraph v ∈ e Q) :
    (tupleTruth p o A Q b t idx).Eval e ↔
      p.bound ≤ n ∧ p.Sat (e A : Set ZFSet) (tupleEnv v) := by
  simp only [tupleTruth,Formula.Eval,Formula.eval_orderedPair,Formula.eval_subset,
    cons_zero,cons_succ]
  constructor
  · rintro ⟨m,_,g,_,hp,hsub,htruth⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp (ht.symm.trans hp)
    have hbn : p.bound ≤ n := natSet_subset_iff p.bound n |>.mp (hb ▸ hsub)
    exact ⟨hbn,(graphTruth_spec p (A+2) 0 (fun i => idx i+2)
      (cons (tupleGraph v) (cons (natSet n) e)) v hv hbn rfl hi).mp htruth⟩
  · rintro ⟨hbn,htruth⟩
    refine ⟨natSet n,ho ▸ (mem_omega _).mpr ⟨n,rfl⟩,tupleGraph v,hQ,ht,?_,?_⟩
    · rw [hb]; exact (natSet_subset_iff p.bound n).mpr hbn
    · exact (graphTruth_spec p (A+2) 0 (fun i => idx i+2)
        (cons (tupleGraph v) (cons (natSet n) e)) v hv hbn rfl hi).mpr htruth

theorem truthSlice_mem (M A : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (p : SentenceForm) : truthSlice A p ∈ M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  have hn (n : ℕ) : natSet.{u} n ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
  obtain ⟨Q,hQM,hQdef⟩ := internal_power M hM hT.powerSet
    (product_mem M hM hT.pairing hT.union hT.powerSet hS hω hA)
  have hQ {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) : tupleGraph v ∈ Q := by
    apply (hQdef _).mpr
    refine ⟨tupleGraph_mem M hM hT.pairing hT.union hω v (fun i => hM A hA _ (hv i)),?_⟩
    intro z hz
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz
    exact ZFSet.mem_prod.mpr ⟨_,(mem_omega _).mpr ⟨i.val,rfl⟩,_,hv i,rfl⟩
  let e := cons ZFSet.omega (cons A (cons Q (cons (natSet p.bound) natSet)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    · exact hω
    · exact hA
    · exact hQM
    · exact hn _
    · exact hn _
  let φ := tupleTruth p 1 2 3 4 0 (fun i => i+5)
  have hs := sep_mem M hM hS φ e he (tupleSpace_mem M A hM hT hA)
  have heq : (tupleSpace A).sep (fun t => φ.Eval (cons t e)) = truthSlice A p := by
    apply ZFSet.ext; intro t
    rw [truthSlice,ZFSet.mem_sep,ZFSet.mem_sep]
    apply and_congr_right; intro ht
    obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp ht
    exact (tupleTruth_spec p 1 2 3 4 0 (fun i => i+5) (cons (tupleCode v) e)
      rfl rfl (fun _ _ => rfl) v hv rfl (hQ v hv)).trans (satisfactionSet_record A p v hv).symm
  exact heq ▸ hs

end TuringRigidity.RelativeConstructible

end OAI
