/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/FiniteSumGraph.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.TrimmedSumGraph

/-!
# Finite Sum Graph
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalCoding
universe u

theorem sum_graph_spec_with_internal_nodes (A : ZFSet.{u}) (hA : Transitive A) (a b : Ordinal.{u})
  (hω : ZFSet.omega.{u} ∈ A)
    (ha : a.toZFSet ∈ A) (hb : b.toZFSet ∈ A)
    (h0 : (∅ : ZFSet.{u}) ∈ A) (h1 : ({∅} : ZFSet.{u}) ∈ A)
    (hlocal : ∀ t < b, (a + t).toZFSet ∈ A ∧ SumCertificates (A) a t)
    (hnodes : sumDomain a.toZFSet b.toZFSet ⊆ A)
    (z : ZFSet.{u}) (hz : z ∈ A) :
    trimmedSumGraphSentence.Sat (A : Set ZFSet)
      (cons z (cons a.toZFSet (cons b.toZFSet (cons ∅ (fun _ => {∅}))))) ↔
        ∃ x ∈ sumDomain a.toZFSet b.toZFSet, z = ZFSet.pair x (sumValue a x) := by
  let e := cons z (cons a.toZFSet (cons b.toZFSet (cons ∅ (fun _ => {∅}))))
  have he (i : ℕ) : e i ∈ A := by
    rcases i with _ | _ | _ | _ | i
    · exact hz
    · exact ha
    · exact hb
    · exact h0
    · exact h1
  rw [trimmedSumGraphSentence_semantics A hA e he]
  constructor
  · rintro ⟨t,ht,x,hx,y,hy,hleft|⟨hright,hq⟩⟩
    · obtain ⟨hta,hxdef,hzdef,hydef⟩ := hleft
      change x = leftNode t at hxdef
      refine ⟨x,(mem_sumDomain _ _ _).mpr (Or.inl ⟨t,hta,hxdef⟩),?_⟩
      change z = ZFSet.pair x y at hzdef
      rw [hzdef,hydef,hxdef,sumValue_left]
    · obtain ⟨htb,hxdef,hzdef⟩ := hright
      change t ∈ b.toZFSet at htb
      obtain ⟨t,htb,rfl⟩ := Ordinal.mem_toZFSet_iff.mp htb
      have htb := Ordinal.toZFSet_mem_toZFSet_iff.mp htb
      have hE : ∀ i, cons y (cons x (cons t.toZFSet e)) i ∈ A := by
        intro i
        rcases i with _ | _ | _ | i
        · exact hy
        · exact hx
        · exact ht
        · exact he i
      have hydef := codeSumAt_sound A hA 0 4 2 _ hE a t rfl rfl hq
      change x = rightNode t.toZFSet at hxdef
      refine ⟨x,(mem_sumDomain _ _ _).mpr (Or.inr
        ⟨t.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr htb,hxdef⟩),?_⟩
      change z = ZFSet.pair x y at hzdef
      change y = (a+t).toZFSet at hydef
      rw [hzdef,hydef,hxdef,sumValue_right,Ordinal.rank_toZFSet]
  · rintro ⟨x,hx,hzdef⟩
    rcases (mem_sumDomain _ _ _).mp hx with ⟨t,ht,rfl⟩|⟨t,ht,rfl⟩
    · have htA := hA _ ha _ ht
      have hxA := hnodes ((mem_sumDomain _ _ _).mpr (Or.inl ⟨t,ht,rfl⟩))
      refine ⟨t,htA,_,hxA,t,htA,Or.inl ⟨ht,rfl,?_,rfl⟩⟩
      rw [sumValue_left] at hzdef
      simpa only [e,cons_zero,leftNode] using hzdef
    · obtain ⟨t,ht,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
      have ht := Ordinal.toZFSet_mem_toZFSet_iff.mp ht
      have htA := hA _ hb _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr ht)
      have hxA := hnodes ((mem_sumDomain _ _ _).mpr (Or.inr
        ⟨t.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr ht,rfl⟩))
      obtain ⟨hy,hq⟩ := hlocal t ht
      let E := cons (a+t).toZFSet (cons (rightNode t.toZFSet) (cons t.toZFSet e))
      have hE (i : ℕ) : E i ∈ A := by
        rcases i with _ | _ | _ | i
        · exact hy
        · exact hxA
        · exact htA
        · exact he i
      refine ⟨t.toZFSet,htA,_,hxA,(a+t).toZFSet,hy,Or.inr
        ⟨⟨Ordinal.toZFSet_mem_toZFSet_iff.mpr ht,rfl,?_⟩,?_⟩⟩
      · rw [sumValue_right,Ordinal.rank_toZFSet] at hzdef
        simpa only [e,cons_zero,rightNode] using hzdef
      · exact codeSumAt_of_certificates A hA hω 0 4 2 E hE a t rfl rfl hq rfl

end TuringRigidity.OrdinalArithmetic

end OAI
