/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/TrimmedSumGraph.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.TrimmedSumDomains
public import LeanPool.TuringConeRigidity.OrdinalCodes.TrimmedPresentation
public import LeanPool.TuringConeRigidity.OrdinalCodes.CodeOperationCertificates

/-!
# Trimmed Sum Graph
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalCoding
universe u

/-- A full formula describing the collapse graph for the trimmed tagged ordinal-sum
presentation. -/
noncomputable def trimmedSumGraphSentence : SentenceForm := .ex (.ex (.ex
  (.disj (fromBounded (.conj (.member 2 4) (.conj (.orderedPair 1 6 2)
    (.conj (.orderedPair 3 1 0) (.equal 0 2)))))
    (.conj (fromBounded (.conj (.member 2 5) (.conj (.orderedPair 1 7 2)
      (.orderedPair 3 1 0)))) (codeSumAt 0 4 2)))))

theorem trimmedSumGraphSentence_semantics (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) :
    trimmedSumGraphSentence.Sat (A : Set ZFSet) e ↔
      ∃ t ∈ A, ∃ x ∈ A, ∃ y ∈ A,
        (t ∈ e 1 ∧ x = ZFSet.pair (e 3) t ∧ e 0 = ZFSet.pair x y ∧ y = t) ∨
        ((t ∈ e 2 ∧ x = ZFSet.pair (e 4) t ∧ e 0 = ZFSet.pair x y) ∧
          (codeSumAt 0 4 2).Sat (A : Set ZFSet) (cons y (cons x (cons t e)))) := by
  change (∃ t ∈ A, ∃ x ∈ A, ∃ y ∈ A, _) ↔ _
  apply exists_congr; intro t; apply and_congr_right; intro ht
  apply exists_congr; intro x; apply and_congr_right; intro hx
  apply exists_congr; intro y; apply and_congr_right; intro hy
  have hE : ∀ i, cons y (cons x (cons t e)) i ∈ A := by
    intro i
    rcases i with _ | _ | _ | i
    · exact hy
    · exact hx
    · exact ht
    · exact he i
  rw [SentenceForm.sat_disj,SentenceForm.Sat]
  simp only [bounded_sat,Formula.absolute _ A hA _ hE,Formula.Eval,
    Formula.eval_orderedPair,cons_zero,cons_succ]

theorem trimmedSumGraphSentence_spec (R : ZFSet.{u}) (γ a b : Ordinal.{u})
    (hγ : Order.IsSuccLimit γ) (hω : ZFSet.omega.{u} ∈ level R γ)
    (ha : a.toZFSet ∈ level R γ) (hb : b.toZFSet ∈ level R γ)
    (h0 : (∅ : ZFSet.{u}) ∈ level R γ) (h1 : ({∅} : ZFSet.{u}) ∈ level R γ)
    (hlocal : ∀ t < b, (a + t).toZFSet ∈ level R γ ∧ SumCertificates (level R γ) a t)
    (z : ZFSet.{u}) (hz : z ∈ level R γ) :
    trimmedSumGraphSentence.Sat (level R γ : Set ZFSet)
      (cons z (cons a.toZFSet (cons b.toZFSet (cons ∅ (fun _ => {∅}))))) ↔
        ∃ x ∈ sumDomain a.toZFSet b.toZFSet, z = ZFSet.pair x (sumValue a x) := by
  let A := level R γ
  let e := cons z (cons a.toZFSet (cons b.toZFSet (cons ∅ (fun _ => {∅}))))
  have he (i : ℕ) : e i ∈ A := by
    rcases i with _ | _ | _ | _ | i
    · exact hz
    · exact ha
    · exact hb
    · exact h0
    · exact h1
  rw [trimmedSumGraphSentence_semantics A (level_transitive R γ) e he]
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
      have hydef := codeSumAt_sound A (level_transitive R γ) 0 4 2 _ hE a t rfl rfl hq
      change x = rightNode t.toZFSet at hxdef
      refine ⟨x,(mem_sumDomain _ _ _).mpr (Or.inr
        ⟨t.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr htb,hxdef⟩),?_⟩
      change z = ZFSet.pair x y at hzdef
      change y = (a+t).toZFSet at hydef
      rw [hzdef,hydef,hxdef,sumValue_right,Ordinal.rank_toZFSet]
  · rintro ⟨x,hx,hzdef⟩
    rcases (mem_sumDomain _ _ _).mp hx with ⟨t,ht,rfl⟩|⟨t,ht,rfl⟩
    · have htA := level_transitive R γ _ ha _ ht
      have hxA := orderedPair_mem_level_limit R γ hγ h0 htA
      refine ⟨t,htA,_,hxA,t,htA,Or.inl ⟨ht,rfl,?_,rfl⟩⟩
      rw [sumValue_left] at hzdef
      simpa only [e,cons_zero,leftNode] using hzdef
    · obtain ⟨t,ht,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
      have ht := Ordinal.toZFSet_mem_toZFSet_iff.mp ht
      have htA := level_transitive R γ _ hb _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr ht)
      have hxA := orderedPair_mem_level_limit R γ hγ h1 htA
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
      · exact codeSumAt_of_certificates A (level_transitive R γ) hω 0 4 2 E hE a t rfl rfl hq rfl

theorem sum_certificates_at_limit_successor (R : ZFSet.{u}) (γ a b : Ordinal.{u})
    (hγ : Order.IsSuccLimit γ) (hω : ZFSet.omega.{u} ∈ level R γ)
    (ha : a.toZFSet ∈ level R γ) (hb : b.toZFSet ∈ level R γ)
    (h0 : (∅ : ZFSet.{u}) ∈ level R γ) (h1 : ({∅} : ZFSet.{u}) ∈ level R γ)
    (hlocal : ∀ t < b, (a + t).toZFSet ∈ level R γ ∧ SumCertificates (level R γ) a t) :
    SumCertificates (level R (γ+1)) a b := by
  refine ⟨sum_domain_at_limit_successor R γ hγ ha hb h0 h1,
    sum_relation_at_limit_successor R γ hγ ha hb h0 h1,?_⟩
  apply presentation_graph_at_limit_successor R γ hγ _ _ (a+b) (sumValue a)
    (sum_domain_subset_limit R γ hγ ha hb h0 h1) ?_
    (sumValue_mem a b) (sumValue_surjective a b) (sumValue_relation a b)
    trimmedSumGraphSentence (cons a.toZFSet (cons b.toZFSet (cons ∅ (fun _ => {∅}))))
    (fun i => by
      rcases i with _|_|_|i
      · exact ha
      · exact hb
      · exact h0
      · exact h1)
  · exact trimmedSumGraphSentence_spec R γ a b hγ hω ha hb h0 h1 hlocal
  · intro x hx
    rcases (mem_sumDomain _ _ _).mp hx with ⟨t,ht,rfl⟩|⟨t,ht,rfl⟩
    · simpa only [sumValue_left] using level_transitive R γ _ ha _ ht
    · obtain ⟨t,ht,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
      have ht := Ordinal.toZFSet_mem_toZFSet_iff.mp ht
      simpa only [sumValue_right,Ordinal.rank_toZFSet] using (hlocal t ht).1

end TuringRigidity.OrdinalArithmetic

end OAI
